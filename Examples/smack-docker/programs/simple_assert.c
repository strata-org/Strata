#include "smack.h"

int add(int a, int b) {
  return a + b;
}

int main(void) {
  int r = add(3, 4);
  assert(r == 7);
  return 0;
}
