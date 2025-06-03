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

#include "lisp.h"
#include "gc.h"
#include "area.h"
#include "bits.h"

#define LOG2_BLOCK_SIZE 15
#define BLOCK_SIZE (1 << LOG2_BLOCK_SIZE)
/* Objects which were in the image are immortal and aren't block-aligned.
 * We don't allocate into immortal block. */
#define IMMORTAL_CLASS -1
/* Objects larger than a block are large and are handled specially. */
#define LARGE_CLASS -2
/* Smaller size classes are computed by ceil(lb(size)). */
#define LARGEST_SMALL_CLASS LOG2_BLOCK_SIZE
#define FREE_CLASS 0

struct free_list;
struct free_list {
  struct free_list *next;
};
struct block {
  unsigned char size_class;
  unsigned int large_size;      /* pages of a large object */
  struct free_list *free_list;
};
typedef unsigned int block_index;

static struct block *block_table;
static unsigned int used_blocks;
static unsigned int total_blocks;
#define LARGE_ALLOCATOR_STATE (LOG2_BLOCK_SIZE + 0)
#define FREE_ALLOCATOR_STATE (LOG2_BLOCK_SIZE + 1)
#define ALLOCATION_STATES (LOG2_BLOCK_SIZE + 2)
static unsigned int block_allocator_state[ALLOCATION_STATES];

static bitvector code_mark_ref_bits;
/* We are only going to have 2GB of code, so we might as well use
 * a smaller type for caching where to relocate to. */
static unsigned int *code_relocations;
code_gc_kind code_collection_kind = code_gc_in_place;

void init_code_area(area *a) {
  /* First the mark bits. */
  /* see map_initial_markbits */
  natural
    prefix_dnodes = area_dnode(a->low, pure_space_limit),
    ndnodes = area_dnode(a->high, a->low),
    prefix_size = (prefix_dnodes+7)>>3,
    markbits_size = (ndnodes+7)>>3,
    n = align_to_power_of_2(markbits_size,log2_page_size);

  code_mark_ref_bits = (bitvector)(((BytePtr)global_mark_ref_bits)+prefix_size);
  CommitMemory(code_mark_ref_bits,n);

  /* Then the relocation table for compacting GC. */
  natural relocation_bytes = sizeof(unsigned int) * ndnodes >> bitmap_shift;
  code_relocations = ReserveMemory(relocation_bytes);
  if (!code_relocations) Bug(NULL, "Couldn't allocate code area relocation table");
  CommitMemory(code_relocations, relocation_bytes);

  /* Then the block table for non-moving allocation. */
  total_blocks = ((a->high - a->low) + (BLOCK_SIZE - 1)) / BLOCK_SIZE;
  int immortal_blocks = ((a->active - a->low) + (BLOCK_SIZE - 1)) / BLOCK_SIZE;
  block_table = calloc(total_blocks, sizeof(struct block));
  if (!block_table) Bug(NULL, "Couldn't allocate code block table for %d blocks", total_blocks);
  for (int i = 0; i < immortal_blocks; i++)
    block_table[i].size_class = IMMORTAL_CLASS;
  used_blocks = immortal_blocks;
}

/* Allocation */
static char *block_address(block_index index) {
  return code_area->low + index * BLOCK_SIZE;
}
static unsigned int lispobj_block(LispObj obj) {
  if (!in_code_area(obj))
    Bug(NULL, "lispobj_block argument should be in the code area");
  return (obj - (LispObj)code_area->low) / BLOCK_SIZE;
}

static void init_small_block(block_index index, unsigned char size_class) {
  if (size_class == FREE_CLASS || size_class > LARGEST_SMALL_CLASS)
    Bug(NULL, "init_small_block requires a small class");
  if (block_table[index].size_class != FREE_CLASS)
    Bug(NULL, "init_small_block requires a free page");
  int stride = 1 << size_class;
  block_table[index].free_list = (struct free_list*)block_address(index);
  block_table[index].size_class = size_class;
  char *limit = block_address(index + 1);
  for (char *addr = block_address(index);
       addr < limit;
       addr += stride) {
    struct free_list *node = (struct free_list*)addr;
    node->next = (struct free_list*)((addr + stride >= limit) ? NULL : addr + stride);
  }
  if (index >= used_blocks) used_blocks = index + 1;
}

static LispObj *allocate_from_small_block(block_index index) {
  if (!block_table[index].free_list)
    Bug(NULL, "allocate_from_small_block on page with no free objects");
  LispObj *o = (LispObj*)block_table[index].free_list;
  block_table[index].free_list = block_table[index].free_list->next;
  return o;
}

LispObj *allocate_small_object(unsigned char size_class) {
  for (block_index index = block_allocator_state[size_class]; index < used_blocks; index++) {
    if (block_table[index].size_class == size_class && block_table[index].free_list) {
      block_allocator_state[size_class] = index;
      return allocate_from_small_block(index);
    }
  }
  for (block_index index = block_allocator_state[FREE_ALLOCATOR_STATE]; index < total_blocks; index++) {
    if (block_table[index].size_class == FREE_CLASS) {
      init_small_block(index, size_class);
      block_allocator_state[size_class] = index;
      block_allocator_state[FREE_ALLOCATOR_STATE] = index + 1;
      return allocate_from_small_block(index);
    }
  }
  Bug(NULL, "Out of code area");
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

static Boolean is_object_live(LispObj obj) {
  /* Objects on the free list will have a pointer instead of a u8 header,
   * and this pointer is at least word-aligned, so it will not look like a u8
   * header. */
  return header_subtag(header_of(obj)) == subtag_u8_vector;
}

/* The mark-sweep algorithm is bog-standard using a mark bitmap; though
 * code vectors don't have any references and thus we never trace from
 * code vectors. */

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

/* The compacting GC, which is the same Compressor-esque algorithm used
 * for the dynamic area. */

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
  /* Might as well check we're forwarding something live */
  LispObj addr = (LispObj)code_area->low + dnode_size * offset + fulltag_of(obj);
  if (!ref_bit(code_mark_ref_bits, dnode))
    Bug(NULL, LISP " doesn't point to a live code vector", addr);
  return addr;
}


static void scan_additional_area(area *a) {
  /* We end up with most functions being moved to the read-only area
   * after purification. These functions also keep code vectors live. */
  LispObj *start = (LispObj*)a->low, *end = (LispObj*)a->active;
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

static void relocate_additional_area(area *a) {
  LispObj *start = (LispObj *)a->low, *end = (LispObj *)a->active;
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
    Bug(NULL, "Overran area bounds in relocate_additional_area");
  }
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
    /* Why isn't there a good way to find this area? */
    area static_area = {.low = static_space_start, .active = static_space_active};
    scan_additional_area(&static_area);
    scan_additional_area(readonly_area);
    /* GC expects to have memoised the relevant references from the
     * managed-static area, but we do not update the refbits. */
    scan_additional_area(managed_static_area);

    calculate_code_relocation();
    move_code_area();

    natural size = readonly_area->high - readonly_area->low;
    UnProtectMemory(readonly_area->low, size);
    relocate_additional_area(readonly_area);
    relocate_additional_area(managed_static_area);
    ProtectMemory(readonly_area->low, size);
  }
}

void sweep_code_area() {
  if (code_collection_kind == code_gc_in_place) {
    next_active = code_area->active;
  }
  zero_bits(code_mark_ref_bits, previous_dnodes);
  code_area->active = next_active;
  for (unsigned int i; i < ALLOCATION_STATES; i++)
    block_allocator_state[i] = 0;
}

Boolean in_code_area(LispObj where) {
  char *p = (char*)where;
  return code_area->low <= p && p < code_area->active;
}
