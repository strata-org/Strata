#include "smack.h"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

// Simplified aws_string (length-prefixed, no NUL requirement)
struct aws_string {
  size_t len;
  const uint8_t *bytes;
};

bool aws_string_eq(const struct aws_string *a, const struct aws_string *b) {
  if (a == b) return true;
  if (a == NULL || b == NULL) return false;
  if (a->len != b->len) return false;
  for (size_t i = 0; i < a->len; i++) {
    if (a->bytes[i] != b->bytes[i]) return false;
  }
  return true;
}

int main(void) {
  uint8_t d_hello[] = {'h','e','l','l','o'};
  uint8_t d_hello2[] = {'h','e','l','l','o'};
  uint8_t d_world[] = {'w','o','r','l','d'};
  uint8_t d_hi[]    = {'h','i'};

  struct aws_string a = {5, d_hello};
  struct aws_string b = {5, d_hello2};
  struct aws_string c = {5, d_world};
  struct aws_string d = {2, d_hi};

  assert(aws_string_eq(&a, &b) == true);
  assert(aws_string_eq(&a, &c) == false);
  assert(aws_string_eq(&a, &d) == false);
  assert(aws_string_eq(&a, &a) == true);
  return 0;
}
