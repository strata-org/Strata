#include "smack.h"

int main(void) {
  int sum = 0;
  for (int i = 0; i < 5; i++) {
    sum += i;
  }
  assert(sum == 10);
  return 0;
}
