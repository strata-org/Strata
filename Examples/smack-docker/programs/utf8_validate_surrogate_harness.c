#include "smack.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include <assert.h>

#define __CPROVER_assume(x) __VERIFIER_assume(x)

// Bjoern Hoehrmann's UTF-8 DFA decoder (public domain).
// http://bjoern.hoehrmann.de/utf-8/decoder/dfa/

#define UTF8_ACCEPT 0
#define UTF8_REJECT 1

static const uint8_t utf8d[] = {
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
  9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9, 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
  7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7, 8,8,2,2,2,2,2,2,2,2,2,2,2,2,2,2,
  2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2, 10,3,3,3,3,3,3,3,3,3,3,3,3,4,3,3,
  11,6,6,6,5,8,8,8,8,8,8,8,8,8,8,8,
  0,12,24,36,60,96,84,12,12,12,48,72,
  12,12,12,12,12,12,12,12,12,12,12,12,
  12, 0,12,12,12,12,12, 0,12, 0,12,12,
  12,24,12,12,12,12,12,24,12,24,12,12,
  12,12,12,12,12,12,12,24,12,12,12,12,
  12,24,12,12,12,12,12,12,12,24,12,12,
  12,12,12,12,12,12,12,36,12,36,12,12,
  12,36,12,12,12,12,12,36,12,36,12,12,
  12,36,12,12,12,12,12,12,12,12,12,12,
};

static uint32_t inline_decode(uint32_t* state, uint32_t* codep, uint32_t byte) {
  uint32_t type = utf8d[byte];
  *codep = (*state != UTF8_ACCEPT) ?
    (byte & 0x3fu) | (*codep << 6) :
    (0xff >> type) & (byte);
  *state = utf8d[256 + *state*16 + type];
  return *state;
}

static int validate_utf8(const uint8_t *s, size_t len) {
    uint32_t state = UTF8_ACCEPT;
    uint32_t codep = 0;
    for (size_t i = 0; i < len; i++) {
        inline_decode(&state, &codep, s[i]);
    }
    return state == UTF8_ACCEPT ? 1 : 0;
}

int main(void) {
    uint8_t buf[3] = {0xED, 0xA0, 0x80};
    int valid = validate_utf8(buf, 3);
    assert(valid == 0);
    return 0;
}
