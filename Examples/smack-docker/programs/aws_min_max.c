#include "smack.h"
#include <stdlib.h>
#include <stdint.h>

// Simplified aws_min_size / aws_max_size
size_t aws_min_size(size_t a, size_t b) {
  return a < b ? a : b;
}

size_t aws_max_size(size_t a, size_t b) {
  return a > b ? a : b;
}

int main(void) {
  assert(aws_min_size(3, 7) == 3);
  assert(aws_min_size(7, 3) == 3);
  assert(aws_min_size(5, 5) == 5);
  assert(aws_max_size(3, 7) == 7);
  assert(aws_max_size(7, 3) == 7);
  assert(aws_max_size(5, 5) == 5);
  return 0;
}
