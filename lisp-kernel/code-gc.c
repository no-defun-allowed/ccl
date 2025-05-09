/* We have a few requirements for GCing code:
 * 1. We can have ambiguous roots to code vectors, because CALL (no
 * longer) tags return addresses any particular way. It follows that
 * we cannot (always) move code vectors.
 * 2. We would like for code in images to be maximally compacted,
 * and for bootstrapping to see just a bump-allocated area like any
 * other.
 * 3. Return addresses are inherently interior pointers and we don't
 * want to require RECOVER-FN-FROM-RIP/LEA-decoding shenanigans to
 * recover the starts of code vectors.
 *
 * In support of #1 and #3 we will use a non-moving GC/segregated-fits
 * allocator whilst Lisp is running (and thus producing ambiguous
 * roots). In support of #2 we will treat the prefix of the code area
 * (which we loaded from the image) as an immortal bump-allocated
 * area, and then we will perform a mark-compact just before saving
 * an image (when there are no ambiguous roots).
 */

/* But for now, we just have one bump-allocated space which we
 * only ever mark-compact just before saving an image. */

#include "lisp.h"
#include "gc.h"
#include "area.h"

bitvector code_mark_ref_bits;

void init_code_area(area *a) {
  /* see map_initial_markbits */
  natural
    prefix_dnodes = area_dnode(a->low, pure_space_limit),
    ndnodes = area_dnode(a->high, a->low),
    prefix_size = (prefix_dnodes+7)>>3,
    markbits_size = (ndnodes+7)>>3,
    n = align_to_power_of_2(markbits_size,log2_page_size);

  code_mark_ref_bits = (bitvector)(((BytePtr)global_mark_ref_bits)+prefix_size);
  CommitMemory(code_mark_ref_bits,n);
}

LispObj allocate_in_code_area(natural bytes) {
  natural bytes_needed = align_to_power_of_2(8 + bytes, 4);
  char *last = code_area->active;
  if (code_area->active + bytes_needed > code_area->high)
    Bug(NULL, "Out of code area");
  code_area->active += bytes_needed;
  *(LispObj*)last = make_header(subtag_u8_vector, bytes);
  return (LispObj)last | fulltag_misc;
}
