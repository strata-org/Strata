#include "smack.h"
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

struct aws_array_list {
  size_t length;
  size_t current_size;
  size_t item_size;
  void *data;
};

bool aws_array_list_set_at(struct aws_array_list *list, const void *value, size_t index) {
  if (index >= list->length) return false;
  uint8_t *dst = (uint8_t *)list->data + index * list->item_size;
  const uint8_t *src = (const uint8_t *)value;
  for (size_t i = 0; i < list->item_size; i++) {
    dst[i] = src[i];
  }
  return true;
}

int main(void) {
  int storage[4] = {0, 0, 0, 0};
  struct aws_array_list list;
  list.data = storage;
  list.item_size = sizeof(int);
  list.current_size = sizeof(storage);
  list.length = 4;

  int v = 99;
  assert(aws_array_list_set_at(&list, &v, 2) == true);
  assert(storage[2] == 99);
  assert(storage[0] == 0);
  assert(storage[1] == 0);
  assert(storage[3] == 0);

  int v2 = 7;
  assert(aws_array_list_set_at(&list, &v2, 4) == false);
  return 0;
}
