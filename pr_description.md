## PR Title

Add automated overflow/underflow checks for bitvector and floating-point arithmetic

## PR Description

### Motivation

Arithmetic overflow is a major source of bugs in systems code. Signed integer overflow is undefined behavior in C/C++, unsigned overflow silently wraps, and floating-point overflow silently produces infinity. Unlike division-by-zero (added in #510), these errors are easy to miss in code review and hard to trigger in testing.

This PR extends Strata's automated verification to catch arithmetic overflow at every use site — the same way #510 catches every division by zero — so that front-end languages like Laurel (and future C/Java front-ends) get overflow checking for free, without any source-level instrumentation.

### Approach

Following the pattern established by #510 for division-by-zero:

1. **Safe operator variants** (e.g., `Bv32.SafeAdd`) carry built-in preconditions asserting that overflow does not occur.
2. **The existing `PrecondElim` transform** automatically generates verification conditions at each use site.
3. **Front-end translators** emit safe variants instead of unchecked ones — no language-level instrumentation required.

This keeps the architecture uniform: the same mechanism handles division-by-zero, signed overflow, unsigned overflow, signed division overflow (`INT_MIN / -1`), and floating-point overflow to infinity.

### What's covered

**Signed bitvector overflow** (all sizes: bv1, bv2, bv8, bv16, bv32, bv64):
- `SafeAdd/SafeSub/SafeMul/SafeNeg` with preconditions using SMT-LIB's `bvsaddo`/`bvssubo`/`bvsmulo`/`bvnego`

**Signed division overflow** (`INT_MIN / -1`):
- `SafeSDiv/SafeSMod` with dual preconditions: divisor ≠ 0 AND ¬(dividend = INT_MIN ∧ divisor = −1)

**Unsigned bitvector overflow** (configurable via `unsignedOverflowCheck` option):
- `SafeUAdd/SafeUSub/SafeUMul/SafeUNeg` with unsigned overflow predicates

**IEEE 754 Float64**:
- New `float64` type in the SMT layer, encoded as `(_ FloatingPoint 11 53)`
- `Float64.SafeAdd/SafeSub/SafeMul/SafeDiv` with overflow predicates
- Overflow = finite inputs producing ±infinity (following CBMC's `float_overflow_check`)
- Laurel's `TFloat64` now translates to real Float64 (was `"Float64IsNotSupportedYet"`)

**GOTO backend**:
- Overflow predicates translate to CBMC's native `overflow-+`, `overflow--`, `overflow-*`, `overflow-unary-` expressions
- Safe operators translate to the same GOTO operations as their unchecked counterparts

### Key design decisions

- **Safe variants are opt-in at the Core level** — `Bv32.Add` (wrapping) and `Bv32.SafeAdd` (checked) coexist. Front-end translators choose which to emit.
- **Unsigned overflow is off by default** — wrapping is the intended semantics in most languages. Enable with `unsignedOverflowCheck := true`.
- **Signed overflow is always checked** when using safe variants — this matches C/C++ undefined behavior semantics.
- **The GOTO backend uses CBMC's native overflow expressions** rather than the SMT encoding, so CBMC's solver infrastructure handles them natively.

*Description of changes:*

New `arithmeticOverflow` property type alongside the existing `divisionByZero`, with SARIF classification, display labels, and check mode handling. Overflow predicates and safe operators for all BV sizes generated via Lean4 macros. SMT encoding for signed overflow uses SMT-LIB builtins; unsigned and Float64 use custom encodings. Comprehensive unit tests verify factory presence, WF obligation generation, and GOTO translation.

Co-authored-by: Kiro <kiro-agent@users.noreply.github.com>

By submitting this pull request, I confirm that you can use, modify, copy, and redistribute this contribution, under the terms of your choice.
