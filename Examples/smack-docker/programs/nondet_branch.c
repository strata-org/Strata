#include "smack.h"

int main(void) {
  int x = __VERIFIER_nondet_int();
  assume(x >= 0 && x <= 100);
  int y;
  if (x < 50) {
    y = x + 50;
  } else {
    y = x;
  }
  assert(y >= 50 && y <= 100);
  return 0;
}
