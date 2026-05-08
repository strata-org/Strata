#include "smack.h"
#include <stdlib.h>

int main(void) {
  int *arr = (int *)malloc(3 * sizeof(int));
  arr[0] = 10;
  arr[1] = 20;
  arr[2] = 30;
  assert(arr[0] + arr[1] + arr[2] == 60);
  free(arr);
  return 0;
}
