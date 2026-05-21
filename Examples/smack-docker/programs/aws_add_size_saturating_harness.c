// Imported verbatim from awslabs/aws-c-common
//   verification/cbmc/proofs/aws_add_size_saturating/aws_add_size_saturating_harness.c
// Function bodies inlined from include/aws/common/byte_order.inl, include/aws/common/clock.inl, include/aws/common/encoding.inl, include/aws/common/math.fallback.inl, include/aws/common/math.inl.
// Adapter prelude shims CBMC primitives onto SMACK's __VERIFIER_*.

#include "smack.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include <assert.h>

// CBMC primitive shims.
#define __CPROVER_assume(x)   __VERIFIER_assume(x)
#define nondet_bool()         ((bool)__VERIFIER_nondet_int())
#define nondet_uint8_t()      ((uint8_t)__VERIFIER_nondet_int())
#define nondet_uint16_t()     ((uint16_t)__VERIFIER_nondet_int())
#define nondet_uint32_t()     ((uint32_t)__VERIFIER_nondet_int())
#define nondet_uint64_t()     ((uint64_t)__VERIFIER_nondet_long())
#define nondet_int8_t()       ((int8_t)__VERIFIER_nondet_int())
#define nondet_int16_t()      ((int16_t)__VERIFIER_nondet_int())
#define nondet_int32_t()      __VERIFIER_nondet_int()
#define nondet_int64_t()      __VERIFIER_nondet_long()
#define nondet_size_t()       ((size_t)__VERIFIER_nondet_long())

// AWS macro stubs.
#define AWS_STATIC_IMPL       static inline
#define AWS_OP_SUCCESS        0
#define AWS_OP_ERR            (-1)
#define AWS_ERROR_OVERFLOW_DETECTED 0
#define aws_raise_error(e)    AWS_OP_ERR
#define AWS_PRECONDITION(x)
#define AWS_POSTCONDITION(x)
#define SIZE_BITS             64
#define SIZE_MAX_POWER_OF_TWO (((size_t)1) << (SIZE_BITS - 1))

// --- Function bodies under test (verbatim) ---
AWS_STATIC_IMPL uint32_t aws_add_u32_saturating(uint32_t a, uint32_t b) {
    if ((b > 0) && (a > (UINT32_MAX - b)))
        return UINT32_MAX;
    return a + b;
}

AWS_STATIC_IMPL uint64_t aws_add_u64_saturating(uint64_t a, uint64_t b) {
    if ((b > 0) && (a > (UINT64_MAX - b)))
        return UINT64_MAX;
    return a + b;
}

// --- Harness body, folded into main() ---

/**
 * Coverage: 1.00 (24 lines out of 24 statically-reachable lines in 3 functions reached)
 * Runtime: 0m2.698s
 *
 * Assumptions:
 *     - given 2 non-deterministics unsigned integers
 *
 * Assertions:
 *     - if a + b overflows, aws_add_u32_saturating and aws_add_u64_saturating
 *       functions must always return the corresponding saturated value
 */
int main(void) {
    if (nondet_bool()) {
        uint64_t a = nondet_uint64_t();
        uint64_t b = nondet_uint64_t();
        uint64_t r = aws_add_u64_saturating(a, b);
        if ((b > 0) && (a > (UINT64_MAX - b))) {
            assert(r == UINT64_MAX);
        } else {
            assert(r == a + b);
        }
    } else {
        uint32_t a = nondet_uint32_t();
        uint32_t b = nondet_uint32_t();
        uint32_t r = aws_add_u32_saturating(a, b);
        if ((b > 0) && (a > (UINT32_MAX - b))) {
            assert(r == UINT32_MAX);
        } else {
            assert(r == a + b);
        }
    }
    return 0;
}
