#include "smack.h"
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

// Simplified aws_byte_cursor (models the real AWS C Common struct)
struct aws_byte_cursor {
  size_t len;
  uint8_t *ptr;
};

// Simplified aws_byte_cursor_advance
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
