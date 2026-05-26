#include "smack.h"
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "Mono4_1.c", 3, "reach_error"); }


int main() {
    int x = 0;
    int y = 500000;
    while(x < 1000000) {
	if (x < 500000) {
	    x = x + 1;
	} else {
	    x = x + 1;
	    y = y + 1;
	}
    }
    __VERIFIER_assert(y!=x);
    return 0;
}
