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
 * only ever mark-compacted just before saving an image. */

#include "lisp.h"
#include "gc.h"
#include "area.h"
#include "bits.h"

static bitvector code_mark_ref_bits;
/* We are only going to have 2GB of code, so we might as well use
 * a smaller type for caching where to relocate to. */
static unsigned int *code_relocations;
code_gc_kind code_collection_kind = code_gc_in_place;

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
  
  natural relocation_bytes = sizeof(unsigned int) * ndnodes >> bitmap_shift;
  code_relocations = ReserveMemory(relocation_bytes);
  if (!code_relocations) Bug(NULL, "Couldn't allocate code area relocation table");
  CommitMemory(code_relocations, relocation_bytes);
}

LispObj allocate_in_code_area(natural bytes) {
  natural bytes_needed = align_to_power_of_2(node_size + bytes, dnode_shift);
  char *last = code_area->active;
  if (code_area->active + bytes_needed > code_area->high)
    Bug(NULL, "Out of code area");
  code_area->active += bytes_needed;
  *(LispObj*)last = make_header(subtag_u8_vector, bytes);
  return (LispObj)last | fulltag_misc;
}

/* The mark-sweep algorithm is bog-standard, mark-compact uses the
 * same Compressor-esque algorithm used in the dynamic area. */

void mark_code_vector(LispObj obj, Boolean precise) {
  natural dnode = area_dnode(obj, code_area->low);
  switch (code_collection_kind) {
  case code_gc_in_place:
    set_bit(code_mark_ref_bits, dnode);
    break;
  case code_gc_compacting: {
    /* We get ambiguous roots from stacks and registers which won't exist
     * after saving the application. */
    if (!precise)
      return;
    /* See rmark and mark_root */
    natural
      header = *((natural*)ptr_from_lispobj(untag(obj))),
      subtag = header_subtag(header),
      element_count = header_element_count(header),
      total_size_in_bytes = node_size + element_count,
      total_size_in_dwords = (total_size_in_bytes+(dnode_size-1))>>dnode_shift;
    set_n_bits(code_mark_ref_bits, dnode, total_size_in_dwords);
  }
  }
}

/* The compacting GC */

LispObj code_forwarding_address(LispObj obj) {
  if (code_collection_kind == code_gc_in_place)
    return obj;
  /* See dnode_forwarding_address */
  unsigned int
    dnode = area_dnode(obj, code_area->low),
    pagelet = dnode >> bitmap_shift,
    nbits = dnode & bitmap_shift_count_mask,
    offset = code_relocations[pagelet],
    shift = nbits_in_word - nbits;
  if (nbits)
    offset += __builtin_popcountl(code_mark_ref_bits[pagelet] >> shift);
  return (LispObj)code_area->low + dnode_size * offset + fulltag_of(obj);
}


static void scan_readonly_area() {
  /* We end up with most functions being moved to the read-only area
   * after purification. These functions alsok eep code vectors live. */
  LispObj *start = (LispObj *)(readonly_area->low), *end = (LispObj *)(readonly_area->active);
  while (start < end) {
    LispObj w0;
    int fulltag;
    w0 = *start;
    fulltag = fulltag_of(w0);
    if (immheader_tag_p(fulltag)) {
      start = (LispObj *)skip_over_ivector((natural)start, w0);
    } else {
      if (in_code_area(w0) && is_node_fulltag(fulltag))
        mark_code_vector(w0, true);
      start++;
    }
  }
  if (start > end) {
    Bug(NULL, "Overran area bounds in scan_readonly_area");
  }
}

static void relocate_readonly_area() {
  natural size = readonly_area->high - readonly_area->low;
  UnProtectMemory(readonly_area->low, size);
  LispObj *start = (LispObj *)(readonly_area->low), *end = (LispObj *)(readonly_area->active);
  while (start < end) {
    LispObj w0;
    int fulltag;
    w0 = *start;
    fulltag = fulltag_of(w0);
    if (immheader_tag_p(fulltag)) {
      start = (LispObj *)skip_over_ivector((natural)start, w0);
    } else {
      if (in_code_area(w0) && is_node_fulltag(fulltag))
        *start = code_forwarding_address(w0);
      start++;
    }
  }
  if (start > end) {
    Bug(NULL, "Overran area bounds in scan_readonly_area");
  }
  ProtectMemory(readonly_area->low, size);
}


static natural previous_dnodes;
static char *next_active;

static void calculate_code_relocation() {
  /* See calculate_relocation */
  unsigned int
    npagelets = (area_dnode(code_area->active, code_area->low)+(nbits_in_word-1))>>bitmap_shift,
    bits_counted = 0;
  for (unsigned int i = 0; i < npagelets; i++) {
    code_relocations[i] = bits_counted;
    bits_counted += __builtin_popcountl(code_mark_ref_bits[i]);
  }
  next_active = code_area->low + dnode_size * bits_counted;
}

static void move_code_area() {
  natural dnode = 0, end_dnode = area_dnode(code_area->active, code_area->low);
  LispObj last_dest = 0, last_src = 0;
  while (dnode < end_dnode) {
    natural *bitsp, bits, bitidx;
    set_bitidx_vars(code_mark_ref_bits, dnode, bitsp, bits, bitidx);
    if (!bits) {
      /* Get to the next word of the bitmap */
      dnode += nbits_in_word - bitidx;
    } else {
      natural nextbit = count_leading_zeros(bits);
      dnode += nextbit - bitidx;
      bitidx = nextbit;

      LispObj src = (LispObj)code_area->low + dnode_size * dnode;
      LispObj dest = code_forwarding_address(src);
      LispObj header = header_of(src);
      if (header_subtag(header) != subtag_u8_vector)
        Bug(NULL, LISP " (header " LISP ") does not point to a code vector", src, header);
      if (dest <= last_dest)
        Bug(NULL, LISP " wasn't relocated to after " LISP " at " LISP, src, last_src, last_dest);
      natural size = node_size + header_element_count(header);
      memmove(ptr_from_lispobj(dest), ptr_from_lispobj(src), size);
      dnode += (size + (dnode_size - 1)) >> dnode_shift;
      last_dest = dest; last_src = src;
    }
  }
}

void compact_code_area() {
  previous_dnodes = area_dnode(code_area->active, code_area->low);
  if (code_collection_kind == code_gc_compacting) {
    scan_readonly_area();
    calculate_code_relocation();
    move_code_area();
    relocate_readonly_area();
  }
}

void sweep_code_area() {
  if (code_collection_kind == code_gc_in_place) {
    next_active = code_area->active;
  }
  zero_bits(code_mark_ref_bits, previous_dnodes);
  code_area->active = next_active;
}
