#include "smack.h"
#include <stdlib.h>
#include <stdint.h>

// Simplified aws_round_up_to_power_of_two for 32-bit input
uint32_t aws_round_up_to_power_of_two_u32(uint32_t x) {
  if (x <= 1) return 1;
  x--;
  x |= x >> 1;
  x |= x >> 2;
  x |= x >> 4;
  x |= x >> 8;
  x |= x >> 16;
  x++;
  return x;
}

int main(void) {
  assert(aws_round_up_to_power_of_two_u32(0) == 1);
  assert(aws_round_up_to_power_of_two_u32(1) == 1);
  assert(aws_round_up_to_power_of_two_u32(2) == 2);
  assert(aws_round_up_to_power_of_two_u32(3) == 4);
  assert(aws_round_up_to_power_of_two_u32(5) == 8);
  assert(aws_round_up_to_power_of_two_u32(8) == 8);
  assert(aws_round_up_to_power_of_two_u32(9) == 16);
  assert(aws_round_up_to_power_of_two_u32(17) == 32);
  return 0;
}
