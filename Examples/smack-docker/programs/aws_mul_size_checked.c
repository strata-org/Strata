#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <limits.h>

// Simplified aws_mul_size_checked: detects overflow on size_t multiplication.
bool aws_mul_size_checked(size_t a, size_t b, size_t *out) {
  if (a != 0 && b > SIZE_MAX / a) {
    return false;
  }
  *out = a * b;
  return true;
}

int main(void) {
  size_t r;
  assert(aws_mul_size_checked(0, 1000, &r) == true);
  assert(r == 0);
  assert(aws_mul_size_checked(7, 6, &r) == true);
  assert(r == 42);
  assert(aws_mul_size_checked(SIZE_MAX, 1, &r) == true);
  assert(r == SIZE_MAX);
  // Overflow: SIZE_MAX * 2 cannot fit
  assert(aws_mul_size_checked(SIZE_MAX, 2, &r) == false);
  return 0;
}
