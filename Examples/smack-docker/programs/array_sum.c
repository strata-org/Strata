#include "smack.h"

int main(void) {
  int a[4] = {1, 2, 3, 4};
  int sum = 0;
  for (int i = 0; i < 4; i++) {
    sum += a[i];
  }
  assert(sum == 10);
  return 0;
}
