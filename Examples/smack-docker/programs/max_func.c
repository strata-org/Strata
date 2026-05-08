#include "smack.h"

int max(int a, int b) {
  return (a > b) ? a : b;
}

int main(void) {
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int m = max(a, b);
  assert(m >= a);
  assert(m >= b);
  assert(m == a || m == b);
  return 0;
}
