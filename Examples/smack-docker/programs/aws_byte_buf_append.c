#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

struct aws_byte_buf {
  size_t len;
  uint8_t *buffer;
  size_t capacity;
};

struct aws_byte_cursor {
  size_t len;
  const uint8_t *ptr;
};

// Simplified aws_byte_buf_append: copy a cursor into the buffer if it fits.
bool aws_byte_buf_append(struct aws_byte_buf *buf, struct aws_byte_cursor src) {
  if (buf->len + src.len > buf->capacity) return false;
  for (size_t i = 0; i < src.len; i++) {
    buf->buffer[buf->len + i] = src.ptr[i];
  }
  buf->len += src.len;
  return true;
}

int main(void) {
  uint8_t storage[8];
  struct aws_byte_buf buf;
  buf.buffer = storage;
  buf.capacity = 8;
  buf.len = 0;

  uint8_t data[] = {1, 2, 3};
  struct aws_byte_cursor cur;
  cur.ptr = data;
  cur.len = 3;

  bool ok = aws_byte_buf_append(&buf, cur);
  assert(ok == true);
  assert(buf.len == 3);
  assert(buf.buffer[0] == 1);
  assert(buf.buffer[1] == 2);
  assert(buf.buffer[2] == 3);

  // Overflow case: 3 + 6 > 8
  uint8_t big[] = {4, 5, 6, 7, 8, 9};
  struct aws_byte_cursor big_cur;
  big_cur.ptr = big;
  big_cur.len = 6;
  bool fail = aws_byte_buf_append(&buf, big_cur);
  assert(fail == false);
  assert(buf.len == 3);
  return 0;
}
