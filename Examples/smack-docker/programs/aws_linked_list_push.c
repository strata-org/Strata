#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

// Simplified intrusive doubly-linked list, like AWS C Common's aws_linked_list.
struct aws_linked_list_node {
  struct aws_linked_list_node *next;
  struct aws_linked_list_node *prev;
};

struct aws_linked_list {
  struct aws_linked_list_node head;
  struct aws_linked_list_node tail;
};

void aws_linked_list_init(struct aws_linked_list *list) {
  list->head.next = &list->tail;
  list->head.prev = NULL;
  list->tail.prev = &list->head;
  list->tail.next = NULL;
}

bool aws_linked_list_empty(const struct aws_linked_list *list) {
  return list->head.next == &list->tail;
}

void aws_linked_list_push_back(struct aws_linked_list *list, struct aws_linked_list_node *node) {
  struct aws_linked_list_node *prev = list->tail.prev;
  node->prev = prev;
  node->next = &list->tail;
  prev->next = node;
  list->tail.prev = node;
}

int main(void) {
  struct aws_linked_list list;
  aws_linked_list_init(&list);
  assert(aws_linked_list_empty(&list) == true);

  struct aws_linked_list_node n1, n2;
  aws_linked_list_push_back(&list, &n1);
  assert(aws_linked_list_empty(&list) == false);
  assert(list.head.next == &n1);
  assert(list.tail.prev == &n1);
  assert(n1.prev == &list.head);
  assert(n1.next == &list.tail);

  aws_linked_list_push_back(&list, &n2);
  assert(list.head.next == &n1);
  assert(list.tail.prev == &n2);
  assert(n1.next == &n2);
  assert(n2.prev == &n1);
  assert(n2.next == &list.tail);
  return 0;
}
