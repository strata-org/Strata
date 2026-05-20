#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

struct aws_byte_cursor {
  size_t len;
  const uint8_t *ptr;
};

// Simplified aws_byte_cursor_eq
bool aws_byte_cursor_eq(const struct aws_byte_cursor *a, const struct aws_byte_cursor *b) {
  if (a->len != b->len) return false;
  for (size_t i = 0; i < a->len; i++) {
    if (a->ptr[i] != b->ptr[i]) return false;
  }
  return true;
}

int main(void) {
  uint8_t da[] = {1, 2, 3, 4};
  uint8_t db[] = {1, 2, 3, 4};
  uint8_t dc[] = {1, 2, 3, 5};

  struct aws_byte_cursor a = {4, da};
  struct aws_byte_cursor b = {4, db};
  struct aws_byte_cursor c = {4, dc};
  struct aws_byte_cursor short_a = {3, da};

  assert(aws_byte_cursor_eq(&a, &b) == true);
  assert(aws_byte_cursor_eq(&a, &c) == false);
  assert(aws_byte_cursor_eq(&a, &short_a) == false);
  assert(aws_byte_cursor_eq(&a, &a) == true);
  return 0;
}
