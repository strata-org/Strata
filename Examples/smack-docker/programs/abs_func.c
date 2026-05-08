#include "smack.h"

int abs_val(int x) {
  if (x < 0) return -x;
  return x;
}

int main(void) {
  int x = __VERIFIER_nondet_int();
  assume(x > -1000 && x < 1000);
  int r = abs_val(x);
  assert(r >= 0);
  return 0;
}
