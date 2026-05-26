#include "smack.h"
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "in-de31.c", 3, "reach_error"); }
extern unsigned int __VERIFIER_nondet_uint(void);


int main()
{
  unsigned int n = __VERIFIER_nondet_uint();
  unsigned int x=n, y=0, z;
  while(x>0)
  {
    x--;
    y++;
  }

  z = y;
  while(z>0)
  {
    x++;
    z--;
  }

  while(y>0)
  {
    y--;
    z++;
  }

  __VERIFIER_assert(z==n);
  return 0;
}
