#include "lisp.h"
#include "area.h"
#include "gc.h"

/* GDB declarations */

typedef enum
{
  JIT_NOACTION = 0,
  JIT_REGISTER_FN,
  JIT_UNREGISTER_FN
} jit_actions_t;

struct jit_code_entry
{
  struct jit_code_entry *next_entry;
  struct jit_code_entry *prev_entry;
  const char *symfile_addr;
  uint64_t symfile_size;
};

struct jit_descriptor
{
  uint32_t version;
  /* This type should be jit_actions_t, but we use uint32_t
     to be explicit about the bitwidth.  */
  uint32_t action_flag;
  struct jit_code_entry *relevant_entry;
  struct jit_code_entry *first_entry;
};

struct jit_descriptor __jit_debug_descriptor = { 1, 0, 0, 0 };

void __attribute__((noinline)) __jit_debug_register_code() {
  asm volatile("" ::"r"(&__jit_debug_descriptor));
}

/* Now the actual code */

struct buffer {
  char *start;
  natural pos;
  natural end;
};

static struct buffer buffer_init() {
  natural size = 1 << 16;
  char *start = malloc(size);
  if (!start) Bug(NULL, "malloc failed");
  return (struct buffer){ start, 0, size };
}

static void buffer_emit(struct buffer* b, natural n, const char *data) {
  if (b->pos + n > b->end) {
    natural new_end = b->end * 2;
    b->start = realloc(b->start, new_end);
    if (!b->start) Bug(NULL, "realloc failed");
    b->end = new_end;
  }
  memcpy(b->start + b->pos, data, n);
  b->pos += n;
}

static void print_area_symbols_to_buffer(area *a, struct buffer *b)
{
  if (!a) return;
  LispObj *start = (LispObj *)(a->low), *end = (LispObj *)(a->active);
  /* Our symbol table format is start and end bounds of each function,
   * then the symbol name as a zero-terminated string. */
  while (start < end) {
    LispObj w0;
    int fulltag;
    w0 = *start;
    fulltag = fulltag_of(w0);
    if (immheader_tag_p(fulltag)) {
      start = (LispObj *)skip_over_ivector((natural)start, w0);
    } else {
      if (header_subtag(w0) == subtag_function) {
        natural elements = header_element_count(w0);
        LispObj lfbits = start[elements], name = start[elements - 1];
        LispObj code = start[1], len = header_element_count(header_of(code));
        LispObj end = untag(code) + node_size + len;
        char *str;
        char buffer[128];
        if ((lfbits & lfbits_noname_mask) == 0) {
          extern char *print_lisp_object(LispObj);
          str = print_lisp_object(name);
        } else {
          snprintf(buffer, 128, "lambda_%lx", start);
          str = buffer;
        }
        buffer_emit(b, sizeof(LispObj), (char*)&code);
        buffer_emit(b, sizeof(LispObj), (char*)&end);
        buffer_emit(b, strlen(str) + 1, str);
      }
      start += 2;
    }
  }
  if (start > end) {
    Bug(NULL, "Overran area bounds in print_all_symbols");
  }
}

static void commit_buffer(struct buffer *b)
{
  if (b->pos) {
    /* Now write in the entry */
    struct jit_code_entry *entry = malloc(sizeof(struct jit_code_entry));
    entry->symfile_addr = b->start;
    entry->symfile_size = b->pos;
    entry->next_entry = entry->prev_entry = NULL;
    __jit_debug_descriptor.action_flag = JIT_REGISTER_FN;
    __jit_debug_descriptor.relevant_entry = entry;
    __jit_debug_descriptor.first_entry = entry;
    __jit_debug_register_code();
  }
}

void print_area_symbols(area *a)
{
  struct buffer b = buffer_init();
  print_area_symbols_to_buffer(a, &b);
  commit_buffer(&b);
}

void print_all_symbols()
{
  struct buffer b = buffer_init();
  print_area_symbols_to_buffer(active_dynamic_area, &b);
  print_area_symbols_to_buffer(g1_area, &b);
  print_area_symbols_to_buffer(g2_area, &b);
  print_area_symbols_to_buffer(readonly_area, &b);
  commit_buffer(&b);
}

void count_sizes()
{
  LispObj *start = (LispObj*)code_area->low, *end = (LispObj*)code_area->active;
  natural sizes[24] = { 0 };
  while (start < end) {
    LispObj header = *start;
    natural size = header_element_count(header);
    sizes[64 - __builtin_clzl(size - 1)]++;
    start = (LispObj*)skip_over_ivector((natural)start, header);
  }
  for (int i = 0; i < 24; i++)
    fprintf(stderr, "(%8d, %8d]: %6d\n", 2 << (i - 1), 2 << i, sizes[i]);
}
