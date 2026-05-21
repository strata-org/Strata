// Imported verbatim from awslabs/aws-c-common
//   verification/cbmc/proofs/aws_is_power_of_two/aws_is_power_of_two_harness.c
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
AWS_STATIC_IMPL bool aws_is_power_of_two(const size_t x) {
    /* First x in the below expression is for the case when x is 0 */
    return x && (!(x & (x - 1)));
}

// --- Harness body, folded into main() ---
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */


int main(void) {
    size_t test_val;
    bool rval = aws_is_power_of_two(test_val);
#if ULONG_MAX == SIZE_MAX
    int popcount = __builtin_popcountl(test_val);
#elif ULLONG_MAX == SIZE_MAX
    int popcount = __builtin_popcountll(test_val);
#else
#    error
#endif
    assert(rval == (popcount == 1));
    return 0;
}
