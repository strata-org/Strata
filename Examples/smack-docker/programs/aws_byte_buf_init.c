#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

// Simplified aws_byte_buf (models the real AWS C Common struct)
struct aws_byte_buf {
  size_t len;
  uint8_t *buffer;
  size_t capacity;
};

// Simplified aws_byte_buf_init using a caller-supplied storage buffer
// (avoids heap allocation, which SMACK models conservatively).
bool aws_byte_buf_init(struct aws_byte_buf *buf, uint8_t *storage, size_t capacity) {
  if (buf == NULL || storage == NULL) return false;
  buf->buffer = storage;
  buf->capacity = capacity;
  buf->len = 0;
  return true;
}

bool aws_byte_buf_is_valid(const struct aws_byte_buf *buf) {
  if (buf == NULL) return false;
  return buf->buffer != NULL && buf->len <= buf->capacity;
}

int main(void) {
  uint8_t storage[16];
  struct aws_byte_buf buf;
  bool ok = aws_byte_buf_init(&buf, storage, 16);
  assert(ok == true);
  assert(buf.len == 0);
  assert(buf.capacity == 16);
  assert(buf.buffer == storage);
  assert(aws_byte_buf_is_valid(&buf) == true);
  return 0;
}
