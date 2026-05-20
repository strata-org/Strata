#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

// Simplified aws_is_power_of_two
bool aws_is_power_of_two(size_t x) {
  if (x == 0) return false;
  return (x & (x - 1)) == 0;
}

int main(void) {
  assert(aws_is_power_of_two(1) == true);
  assert(aws_is_power_of_two(2) == true);
  assert(aws_is_power_of_two(4) == true);
  assert(aws_is_power_of_two(8) == true);
  assert(aws_is_power_of_two(16) == true);
  assert(aws_is_power_of_two(0) == false);
  assert(aws_is_power_of_two(3) == false);
  assert(aws_is_power_of_two(6) == false);
  assert(aws_is_power_of_two(7) == false);
  return 0;
}
