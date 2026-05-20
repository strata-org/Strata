#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <limits.h>

// Simplified aws_add_size_checked: detects overflow on size_t addition.
bool aws_add_size_checked(size_t a, size_t b, size_t *out) {
  if (a > SIZE_MAX - b) {
    return false;
  }
  *out = a + b;
  return true;
}

int main(void) {
  size_t r;
  assert(aws_add_size_checked(0, 0, &r) == true);
  assert(r == 0);
  assert(aws_add_size_checked(10, 20, &r) == true);
  assert(r == 30);
  assert(aws_add_size_checked(SIZE_MAX, 0, &r) == true);
  assert(r == SIZE_MAX);
  // Overflow case
  assert(aws_add_size_checked(SIZE_MAX, 1, &r) == false);
  assert(aws_add_size_checked(SIZE_MAX - 5, 10, &r) == false);
  return 0;
}
