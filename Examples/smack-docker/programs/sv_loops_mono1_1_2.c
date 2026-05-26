#include "smack.h"
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "Mono1_1-2.c", 3, "reach_error"); }

int main(void) {
  unsigned int x = 0;

  while (x < 100000000) {
    if (x < 10000000) {
      x++;
    } else {
      x += 2;
    }
  }

  __VERIFIER_assert(x == 100000000) ;
}
