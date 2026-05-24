#include "smack.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include <assert.h>

#define __CPROVER_assume(x) __VERIFIER_assume(x)

// Minimal RFC 3986 percent-decoder.

static int hex_digit(uint8_t c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return 10 + c - 'a';
    if (c >= 'A' && c <= 'F') return 10 + c - 'A';
    return -1;
}

static size_t percent_decode(const uint8_t *src, size_t src_len, uint8_t *dst) {
    size_t i = 0, o = 0;
    while (i < src_len) {
        if (src[i] == '%') {
            if (i + 2 >= src_len) return (size_t)-1;
            int hi = hex_digit(src[i+1]);
            int lo = hex_digit(src[i+2]);
            if (hi < 0 || lo < 0) return (size_t)-1;
            dst[o++] = (uint8_t)((hi << 4) | lo);
            i += 3;
        } else {
            dst[o++] = src[i++];
        }
    }
    return o;
}

int main(void) {
    uint8_t src[2] = {'a','%'};
    uint8_t dst[2];
    size_t r = percent_decode(src, 2, dst);
    assert(r == (size_t)-1);
    return 0;
}
