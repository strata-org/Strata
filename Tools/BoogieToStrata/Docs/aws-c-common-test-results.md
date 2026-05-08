# SMACK → BoogieToStrata → Strata Pipeline Test Results

## Programs Tested

### aws_byte_cursor_advance.c

```c
#include "smack.h"
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

struct aws_byte_cursor {
  size_t len;
  uint8_t *ptr;
};

struct aws_byte_cursor aws_byte_cursor_advance(struct aws_byte_cursor *cursor, size_t len) {
  struct aws_byte_cursor rv;
  if (cursor->len >= len) {
    rv.ptr = cursor->ptr;
    rv.len = len;
    cursor->ptr += len;
    cursor->len -= len;
  } else {
    rv.ptr = NULL;
    rv.len = 0;
  }
  return rv;
}

int main(void) {
  uint8_t buf[16];
  struct aws_byte_cursor cursor;
  cursor.ptr = buf;
  cursor.len = 16;

  struct aws_byte_cursor slice = aws_byte_cursor_advance(&cursor, 4);
  assert(slice.len == 4);
  assert(cursor.len == 12);
  assert(slice.ptr == buf);
  assert(cursor.ptr == buf + 4);
  return 0;
}
```

### aws_array_eq.c

```c
#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

bool aws_array_eq(const void *a, size_t a_len, const void *b, size_t b_len) {
  if (a_len != b_len) return false;
  const uint8_t *a_bytes = (const uint8_t *)a;
  const uint8_t *b_bytes = (const uint8_t *)b;
  for (size_t i = 0; i < a_len; i++) {
    if (a_bytes[i] != b_bytes[i]) return false;
  }
  return true;
}

int main(void) {
  uint8_t a[] = {1, 2, 3, 4};
  uint8_t b[] = {1, 2, 3, 4};
  uint8_t c[] = {1, 2, 3, 5};

  assert(aws_array_eq(a, 4, b, 4) == true);
  assert(aws_array_eq(a, 4, c, 4) == false);
  assert(aws_array_eq(a, 4, b, 3) == false);
  return 0;
}
```

### aws_ring_buffer.c

```c
#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

struct ring_buffer {
  uint8_t *buf;
  size_t capacity;
  size_t head;
  size_t tail;
};

size_t ring_buffer_used(struct ring_buffer *rb) {
  if (rb->head >= rb->tail)
    return rb->head - rb->tail;
  else
    return rb->capacity - rb->tail + rb->head;
}

size_t ring_buffer_free(struct ring_buffer *rb) {
  return rb->capacity - ring_buffer_used(rb) - 1;
}

int main(void) {
  uint8_t storage[8];
  struct ring_buffer rb;
  rb.buf = storage;
  rb.capacity = 8;
  rb.head = 0;
  rb.tail = 0;

  assert(ring_buffer_used(&rb) == 0);
  assert(ring_buffer_free(&rb) == 7);

  rb.head = 3;
  assert(ring_buffer_used(&rb) == 3);
  assert(ring_buffer_free(&rb) == 4);

  rb.tail = 2;
  assert(ring_buffer_used(&rb) == 1);
  assert(ring_buffer_free(&rb) == 6);

  rb.head = 1;
  rb.tail = 6;
  assert(ring_buffer_used(&rb) == 3);
  assert(ring_buffer_free(&rb) == 4);

  return 0;
}
```

## Pipeline Results

### SMACK Basic Tests (Category 1)

| Program | C → .bpl | Strip | BoogieToStrata | Strata verify | Failure reason |
|---------|:---:|:---:|:---:|:---:|---|
| simple_assert (function call) | OK | OK | OK | FAIL | Namespace collision: `const main` vs `procedure main` |
| swap (pointers) | OK | OK | OK | FAIL | Namespace collision: `const main` vs `procedure main` |
| array_sum (loop + array) | OK | OK | OK | FAIL | Type synonym panic: `<=` on `ref := i64 := int` |
| abs_func (if/else) | OK | OK | FAIL | — | Multi-target goto in user code (LLVM if/else) |
| max_func (ternary) | OK | OK | FAIL | — | Multi-target goto in user code (LLVM ternary) |
| nondet_branch (if/else) | OK | OK | FAIL | — | Multi-target goto in user code (LLVM if/else) |

### AWS C Common Style (Category 3)

| Program | C → .bpl | Strip | BoogieToStrata | Strata verify | Failure reason |
|---------|:---:|:---:|:---:|:---:|---|
| aws_byte_cursor_advance (struct+ptr) | OK | OK | OK | FAIL | Namespace collision: `const main` vs `procedure main` |
| aws_ring_buffer (arithmetic) | OK | OK | OK | FAIL | Namespace collision: `const main` vs `procedure main` |
| aws_array_eq (loop+early return) | OK | OK | FAIL | — | Irreducible CFG: loop with early `return` creates overlapping regions |

## Failure Details

### Namespace collision (5 programs)

```
Error in procedure main: a declaration of this name already exists.
```

SMACK emits `const main : ref;` (function pointer address) alongside `procedure main(...)`.
Strata Core has a single namespace, so these collide.

**Blocked by**: [issue-namespace-collision](issues/issue-namespace-collision.md)

### Multi-target goto in user code (3 programs)

```
Unsupported: goto with two targets that aren't obvious inverses
```

Even simple C `if/else` and ternary operators compile to unstructured multi-target
gotos after LLVM optimization. BoogieToStrata only handles the structured pattern
where one target's assume is the negation of the other.

### Irreducible control flow (1 program: aws_array_eq)

```
Irreducible control-flow: overlapping loop regions between labels '$bb3' and '$bb4'
```

The `for` loop with `return false` inside the body compiles to an irreducible CFG.
LLVM generates a loop header (`$bb4`) and a return block (`$bb3`) with overlapping
back-edges that BoogieToStrata's loop region analysis cannot handle.

### Type synonym panic (1 program: array_sum)

```
translateExpr unexpected type for { dialect := "Core", name := "le" }
```

Strata panics when comparison/arithmetic operators are applied to `ref`-typed values.
The type synonym chain `ref := i64 := int` is not resolved transitively.

**Blocked by**: [issue-type-synonym-comparison](issues/issue-type-synonym-comparison.md)

## Additional blockers (not reached)

Even if the namespace collision were fixed, these programs would hit:

1. **Type synonym comparison panic** — The programs use `ref`-typed comparisons in
   `$$alloc` and pointer arithmetic. See [issue-type-synonym-comparison](issues/issue-type-synonym-comparison.md).

2. **SMACK assert encoding** — Assertions are encoded as `call assert_.i32(cond)`,
   not `assert` statements, so zero VCs would be generated.
   See [issue-smack-assert-encoding](issues/issue-smack-assert-encoding.md).

## Summary

None of the three AWS C Common style programs can be verified end-to-end through the
current pipeline. The programs exercise:

- Struct field access and pointer arithmetic (byte_cursor_advance)
- Loops with early return (array_eq)  
- Conditional arithmetic (ring_buffer)

These are representative of real-world C verification targets and expose the main gaps
in the SMACK → BoogieToStrata → Strata pipeline.
