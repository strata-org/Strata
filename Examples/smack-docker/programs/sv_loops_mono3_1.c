#include "smack.h"
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "Mono3_1.c", 3, "reach_error"); }


int main(void) {
  unsigned int x = 0;
  unsigned int y = 0;
  while (x < 1000000) {
    if (x<500000) {
	y++;
    } else {
	y--;
    }
	x++;
  }
  __VERIFIER_assert(y!=0) ;
}
