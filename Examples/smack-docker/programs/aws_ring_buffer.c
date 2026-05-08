#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

// Simplified ring buffer (models AWS C Common's aws_ring_buffer)
struct ring_buffer {
  uint8_t *buf;
  size_t capacity;
  size_t head;  // write position
  size_t tail;  // read position
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

  // Empty buffer
  assert(ring_buffer_used(&rb) == 0);
  assert(ring_buffer_free(&rb) == 7);

  // Simulate writing 3 bytes
  rb.head = 3;
  assert(ring_buffer_used(&rb) == 3);
  assert(ring_buffer_free(&rb) == 4);

  // Simulate reading 2 bytes
  rb.tail = 2;
  assert(ring_buffer_used(&rb) == 1);
  assert(ring_buffer_free(&rb) == 6);

  // Wrap-around case
  rb.head = 1;
  rb.tail = 6;
  assert(ring_buffer_used(&rb) == 3);  // 8 - 6 + 1 = 3
  assert(ring_buffer_free(&rb) == 4);

  return 0;
}
