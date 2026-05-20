#include "smack.h"
#include <stdlib.h>
#include <stdint.h>

// Simplified DJB2 hash, like AWS C Common's aws_hash_string
uint64_t aws_hash_string_djb2(const uint8_t *bytes, size_t len) {
  uint64_t hash = 5381;
  for (size_t i = 0; i < len; i++) {
    hash = ((hash << 5) + hash) + bytes[i];
  }
  return hash;
}

int main(void) {
  // Empty input: starting seed
  assert(aws_hash_string_djb2((const uint8_t *)"", 0) == 5381);

  // Same input -> same hash (deterministic)
  uint8_t a[] = {1, 2, 3};
  uint8_t b[] = {1, 2, 3};
  assert(aws_hash_string_djb2(a, 3) == aws_hash_string_djb2(b, 3));

  // Different input -> typically different hash
  uint8_t c[] = {1, 2, 4};
  assert(aws_hash_string_djb2(a, 3) != aws_hash_string_djb2(c, 3));

  // Single byte: hash = 5381 * 33 + byte
  uint8_t one[] = {1};
  assert(aws_hash_string_djb2(one, 1) == 5381ULL * 33 + 1);
  return 0;
}
