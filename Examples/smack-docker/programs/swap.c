#include "smack.h"

void swap(int *a, int *b) {
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

int main(void) {
  int x = 5, y = 10;
  swap(&x, &y);
  assert(x == 10);
  assert(y == 5);
  return 0;
}
