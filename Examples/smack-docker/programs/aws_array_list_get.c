#include "smack.h"
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

// Simplified aws_array_list (fixed-element-size, untyped storage)
struct aws_array_list {
  size_t length;
  size_t current_size;  // capacity in bytes
  size_t item_size;
  void *data;
};

bool aws_array_list_get_at(const struct aws_array_list *list, void *out, size_t index) {
  if (index >= list->length) return false;
  uint8_t *src = (uint8_t *)list->data + index * list->item_size;
  uint8_t *dst = (uint8_t *)out;
  for (size_t i = 0; i < list->item_size; i++) {
    dst[i] = src[i];
  }
  return true;
}

int main(void) {
  int storage[4] = {10, 20, 30, 40};
  struct aws_array_list list;
  list.data = storage;
  list.item_size = sizeof(int);
  list.current_size = sizeof(storage);
  list.length = 4;

  int v;
  assert(aws_array_list_get_at(&list, &v, 0) == true);
  assert(v == 10);
  assert(aws_array_list_get_at(&list, &v, 3) == true);
  assert(v == 40);
  assert(aws_array_list_get_at(&list, &v, 4) == false);
  assert(aws_array_list_get_at(&list, &v, 100) == false);
  return 0;
}
