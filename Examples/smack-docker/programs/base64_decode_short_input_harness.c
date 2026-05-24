#include "smack.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include <assert.h>

#define __CPROVER_assume(x) __VERIFIER_assume(x)

// Minimal RFC 4648 base64 decoder (BSD-style).

static const int8_t b64_table[256] = {
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
  -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,62,-1,-1,-1,63,
  52,53,54,55,56,57,58,59,60,61,-1,-1,-1,-2,-1,-1,
  -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,
  15,16,17,18,19,20,21,22,23,24,25,-1,-1,-1,-1,-1,
  -1,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,
  41,42,43,44,45,46,47,48,49,50,51,-1,-1,-1,-1,-1,
};

static int b64_decode_byte(uint8_t c) {
    return (int)b64_table[c];
}

static size_t base64_decode(const uint8_t *src, size_t src_len, uint8_t *dst) {
    size_t i, o = 0;
    if (src_len % 4 != 0) return (size_t)-1;
    for (i = 0; i + 4 <= src_len; i += 4) {
        int v0 = b64_decode_byte(src[i]);
        int v1 = b64_decode_byte(src[i+1]);
        int v2 = b64_decode_byte(src[i+2]);
        int v3 = b64_decode_byte(src[i+3]);
        if (v0 < 0 || v1 < 0) return (size_t)-1;
        dst[o++] = (uint8_t)((v0 << 2) | (v1 >> 4));
        if (v2 == -2) {
            if (v3 != -2) return (size_t)-1;
            return o;
        }
        if (v2 < 0) return (size_t)-1;
        dst[o++] = (uint8_t)(((v1 & 0x0f) << 4) | (v2 >> 2));
        if (v3 == -2) return o;
        if (v3 < 0) return (size_t)-1;
        dst[o++] = (uint8_t)(((v2 & 0x03) << 6) | v3);
    }
    return o;
}

int main(void) {
    uint8_t src[3] = {'A','B','C'};
    uint8_t dst[3];
    size_t r = base64_decode(src, 3, dst);
    assert(r == (size_t)-1);
    return 0;
}
