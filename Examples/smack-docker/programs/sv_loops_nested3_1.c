#include "smack.h"
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested3-1.c", 3, "reach_error"); }



int main()
{
  unsigned int x = 0;
  unsigned int y = 0;
  unsigned int z = 0;
  unsigned int w = 0;

  while (x < 0x0fffffff) {
    y = 0;

    while (y < 0x0fffffff) {
   	z =0;
	while (z <0x0fffffff) {
	  z++;
	}
    	__VERIFIER_assert(z % 4);
	y++;
    }
    __VERIFIER_assert(y % 2);

    x++;
  }
  __VERIFIER_assert(x % 2);
  return 0;

}
