#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

// Simplified aws_array_eq
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
