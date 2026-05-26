#include "smack.h"
int SIZE = 50000001;


int __VERIFIER_nondet_int();
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "loopv1.c", 7, "reach_error"); }
extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}



int main() {
  int n,i,j;
  n = __VERIFIER_nondet_int();
  if (!(n <= SIZE)) return 0;
  i = 0; j=0;
  while(i<n){ 
 
    if(__VERIFIER_nondet_int())	  
      i = i + 6; 
    else
     i = i + 3;    
  }
  __VERIFIER_assert( (i%3) == 0 );
  return 0;
}
