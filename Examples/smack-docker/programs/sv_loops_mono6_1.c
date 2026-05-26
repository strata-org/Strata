#include "smack.h"
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "Mono6_1.c", 3, "reach_error"); }


int main(void) {
unsigned int x = 0;
unsigned int y = 10000000;
unsigned int z=5000000;
	while(x<y){	
		if(x>=5000000)
			z++;
		x++;
	}
  __VERIFIER_assert(z!=x);
  return 0;
}
