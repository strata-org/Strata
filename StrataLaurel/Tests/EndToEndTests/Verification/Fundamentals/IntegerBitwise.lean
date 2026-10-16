/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
End-to-end verification tests for Laurel's bitvector primitives, Bv↔Int casts,
and width- and signedness-explicit integer bitwise procedures.

## API coverage and intentional exclusions

`CoreDefinitionsForLaurel` declares, for widths 1…128, the bitvector
primitives (`$bv<W>And/Or/Xor/Not/Shl/UShr/SShr`) and the casts
(`$intToBv<W>`, `$bv<W>ToInt`, `$bv<W>ToUInt`); and on top of those, for widths
8/16/32/64 and both signednesses, the bounded-integer operations
`$bitAnd<S|U><W>`, `$bitOr<S|U><W>`, `$bitXor<S|U><W>`.

The API has no operator spellings at `int`, integer shifts, or integer
complement. §7 and §8 cover the rationale:

  * complement, AND-NOT, and right/left shifts by a CONSTANT k are pure integer
    arithmetic — `-x - 1`, `2^W - 1 - x`, `x / 2^k`, `x * 2^k`. §8 proves each
    arithmetic form against the bitwise operations.
  * a bitvector `<<` **wraps** (§7.2: `$bv8Shl(128, 1)` is 0). A front end that
    models bounded integers as constrained `int`s may instead report overflow as
    an OBLIGATION. Lowering integer `<<` onto `$bv<W>Shl` would quietly swap one
    semantics for the other, so no integer `<<` is provided and §8.3 pins that
    `x * 2^k` keeps the overflow as a reported obligation.
  * an `int` overload of `&` could carry no width, and bitwise operations on
    bounded integers need one.

## Boundary promise

`$bit<Op><Sign><W>(x, y)` requires both operands to be in width `W`'s range for
the stated signedness, and returns the two's-complement bitwise result read back
in that same range. Out of range is REJECTED (§6), not wrapped — `$intToBv<W>` is
truncating, and the `requires` is what makes the round trip exact. Because a
bitwise and/or/xor of two in-range values is itself in range, there is no
overflow case and no wraparound anywhere in these three operations; §4 proves the
result range rather than assuming it.

## Why the signed forms go through the UNSIGNED cast

Measured at the Core level, cvc5 1.3.4, 60 s per obligation: `sbv_to_int` at
width 32 is a cliff in BOTH directions — the true `sbv_to_int(b) >= -2^31` times
out in three phrasings, and so does the FALSE `sbv_to_int(b) >= 0`, which means
no countermodel either. At widths 8 and 16 it is fine. `ubv_to_int` has no such
problem: both bounds discharge, and so does the range of an `and` built on it.
So the prelude's signed forms recover the signed value from the unsigned one
arithmetically, `s = ((u + 2^(W-1)) mod 2^W) - 2^(W-1)`, and §5 is the test that
the resulting range is derivable — which it is, where a direct `$bv32ToInt` would
not have been.

Also measured: z3 4.12.6 does not implement `int_to_bv`/`sbv_to_int`/`ubv_to_int`
at all ("unknown constant"), so this whole family is **cvc5-only** in the current
toolchain. That is why no block here names a solver, unlike
`StringOrdering.lean`, which needs z3 for the opposite reason.

## Verification only — the interpreter cannot run any of this yet

Every block here is `testLaurelVerification`. Measured: under
`testLaurelExecution` both `$bitAndU8(12, 10)` and the raw
`$bv8ToUInt($bv8And($intToBv8(12), $intToBv8(10)))` report
`condition did not reduce to bool`. The bitwise operators themselves DO carry
concrete evaluators (`Factory.lean`'s `BVOpSpecs` builds each as a `binaryOp`);
the three Bv↔Int casts do not — `bvToUIntFunc`/`bvToIntFunc`/`intToBvFunc` are
`unaryFuncUneval` — and they sit at both ends of every chain.

Making them evaluable is NOT the three-line change the string case was: `unaryOp`
needs a width-concrete `InValTy := BitVec W` (see `BVEvalKind.toDefRHS`, which
passes a literal `sizeNum`), whereas these three are defined width-generically and
are consumed that way by `WFFactoryArray` and by `Core.bvToUIntOp` and friends.
The evaluator therefore needs a per-width macro of its own. Until one exists, a
front end's interpret-mode path cannot execute a bitwise expression at all.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-- A longer solver budget than the 10 s default. Bitvector obligations that
    cross the Bv/Int boundary are not fast; measured, every block in this file
    discharges inside this. -/
private def bwOptions : Laurel.LaurelVerifyOptions :=
  { defaultLaurelTestOptions with
    verifyOptions := { defaultLaurelTestOptions.verifyOptions with solverTimeout := 60 } }

/-! ## Operator arity mismatches produce diagnostics

This directly exercises the schema pass because ordinary source programs are
rejected earlier by resolution. A binary operator with one argument and a unary
operator with two arguments must both report a user error, not panic. -/

private def intLiteral (value : Int) : Laurel.StmtExprMd :=
  ⟨.LiteralInt value, default⟩

private def reportWrongOperatorArity
    (callee : String) (args : List Laurel.StmtExprMd) : IO Unit := do
  let call : Laurel.StmtExprMd :=
    ⟨.StaticCall (Laurel.mkId callee) args [], default⟩
  let model : Laurel.SemanticModel :=
    { nextId := 0, compositeCount := 0, refToDef := {} }
  let (_, state) :=
    Laurel.runTranslateM { model := model } (Laurel.translateExpr call)
  for diagnostic in state.diagnostics do
    IO.println s!"{diagnostic.message}"

/--
info: operator procedure '$intAdd' called with wrong number of arguments
operator procedure '$bv8Not' called with wrong number of arguments
-/
#guard_msgs in
#eval do
  reportWrongOperatorArity "$intAdd" [intLiteral 1]
  reportWrongOperatorArity "$bv8Not" [intLiteral 1, intLiteral 2]

/-! ## 1. Concrete values, per width and signedness.

`12 & 10 == 8`, `12 | 10 == 14`, `12 ^ 10 == 6` are the same three operands
throughout so a wrong operator cannot pass one row by accident. The negative rows
are the ones that distinguish a two's-complement reading from a magnitude one:
`-2 & 3 == 2` needs `-2` to be `…11111110`. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p() opaque {
  assert $bitAndU8(12, 10) == 8;
  assert $bitOrU8(12, 10) == 14;
  assert $bitXorU8(12, 10) == 6;
  assert $bitXorU8(255, 15) == 240;
  assert $bitAndU16(65535, 256) == 256;
  assert $bitAndU32(4294967295, 1) == 1;
  assert $bitXorU64(18446744073709551615, 18446744073709551615) == 0;
  assert $bitAndS32(0 - 2, 3) == 2;
  assert $bitAndS8(0 - 1, 0 - 1) == (0 - 1);
  assert $bitOrS8(0 - 2, 1) == (0 - 1);
  assert $bitXorS32(0 - 1, 0) == (0 - 1);
  assert $bitXorS16(0 - 1, 0 - 1) == 0;
  assert $bitAndS64(0 - 1, 9223372036854775807) == 9223372036854775807
};
#end

/-! ## 2. Symbolic algebraic laws, unsigned 32.

Over SYMBOLIC operands, so none of these can be reached by constant folding. A
fresh uninterpreted function would prove none of them. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int, y: int)
  requires x >= 0
  requires x <= 4294967295
  requires y >= 0
  requires y <= 4294967295
  opaque
{
  assert $bitAndU32(x, x) == x;
  assert $bitOrU32(x, x) == x;
  assert $bitXorU32(x, x) == 0;
  assert $bitAndU32(x, y) == $bitAndU32(y, x);
  assert $bitAndU32(x, 0) == 0;
  assert $bitOrU32(x, 0) == x;
  assert $bitXorU32(x, 0) == x
};
#end

/-! ## 3. The same laws, signed 32 — i.e. through the re-centring arithmetic. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int, y: int)
  requires x >= (0 - 2147483648)
  requires x <= 2147483647
  requires y >= (0 - 2147483648)
  requires y <= 2147483647
  opaque
{
  assert $bitAndS32(x, x) == x;
  assert $bitXorS32(x, x) == 0;
  assert $bitAndS32(x, y) == $bitAndS32(y, x);
  assert $bitAndS32(x, 0) == 0;
  assert $bitOrS32(x, 0) == x
};
#end

/-! ## 4. Range of the result, unsigned.

This is the fact a front end needs to put the result back into a bounded type,
and it is the reason the encoding reads back unsigned. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int, y: int)
  requires x >= 0
  requires x <= 4294967295
  requires y >= 0
  requires y <= 4294967295
  opaque
{
  assert $bitAndU32(x, y) >= 0;
  assert $bitAndU32(x, y) <= 4294967295;
  assert $bitOrU32(x, y) >= 0;
  assert $bitOrU32(x, y) <= 4294967295;
  assert $bitXorU32(x, y) >= 0;
  assert $bitXorU32(x, y) <= 4294967295
};
#end

/-! ## 5. Range of the result, SIGNED — the measurement the design turns on.

A direct `$bv32ToInt` readback cannot discharge the lower bound (see the header).
Through the re-centring these are arithmetic, and they pass. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int, y: int)
  requires x >= (0 - 2147483648)
  requires x <= 2147483647
  requires y >= (0 - 2147483648)
  requires y <= 2147483647
  opaque
{
  assert $bitAndS32(x, y) >= (0 - 2147483648);
  assert $bitAndS32(x, y) <= 2147483647;
  assert $bitOrS32(x, y) >= (0 - 2147483648);
  assert $bitOrS32(x, y) <= 2147483647;
  assert $bitXorS32(x, y) >= (0 - 2147483648);
  assert $bitXorS32(x, y) <= 2147483647
};
#end

/-! ## 6. Disproofs and rejections.

Every annotation below reports "does not hold", which `Core/Verifier.lean` emits
only for an obligation that is reachable AND false — a real countermodel, not an
`unknown`. That matters here more than usual: the alternative design for these
operations was a universally quantified defining axiom over `int`, under which a
false property is expected to degrade to `unknown`. These blocks are the evidence
that the shipped encoding does not.

### 6.1 `and` is not `or`. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int, y: int)
  requires x >= 0
  requires x <= 4294967295
  requires y >= 0
  requires y <= 4294967295
  opaque
{
  assert $bitAndU32(x, y) == $bitOrU32(x, y)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### 6.2 `x & y` is not `x`, and `x ^ y` is not `0`. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int, y: int)
  requires x >= 0
  requires x <= 255
  requires y >= 0
  requires y <= 255
  opaque
{
  assert $bitAndU8(x, y) == x
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int, y: int)
  requires x >= 0
  requires x <= 255
  requires y >= 0
  requires y <= 255
  opaque
{
  assert $bitXorU8(x, y) == 0
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### 6.3 A concrete value is the real one, not a constant.

Control for §1: `12 & 10` is 8, so asserting 9 must fail. Without this the §1
block would pass just as happily if the operation returned the wrong number for
every input. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p() opaque {
  assert $bitAndU8(12, 10) == 9
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### 6.4 An operand outside the width's range is REJECTED, not wrapped.

`$intToBv8` truncates, so without the `requires` this would silently compute on
`x mod 256`. The precondition turns that into a call-site obligation, and the
summary names which operand. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int) opaque {
  assert $bitAndU8(x, 1) >= 0
//       ^^^^^^^^^^^^^^^ error: left operand fits uint8 does not hold
};
#end

/-! ### 6.5 A NEGATIVE operand is rejected by the unsigned form.

The signedness in the name matters: `-1` is a valid `int8` but not a `uint8`. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int)
  requires x >= (0 - 128)
  requires x <= 127
  opaque
{
  assert $bitAndU8(x, 1) >= 0
//       ^^^^^^^^^^^^^^^ error: left operand fits uint8 does not hold
};
#end

/-! ## 7. The bitvector primitives, directly.

### 7.1 Conversions and the unary complement round-trip through `int`. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p() opaque {
  assert $bv32ToUInt($bv32Not($intToBv32(0))) == 4294967295;
  assert $bv8ToUInt($bv8UShr($intToBv8(255), $intToBv8(4))) == 15;
  assert $bv128ToUInt($bv128And($intToBv128(12), $intToBv128(10))) == 8;
  assert $bv32ToInt($bv32Not($intToBv32(5))) == (0 - 6)
};
#end

/-! ### 7.2 A bitvector `<<` WRAPS.

This is the measurement behind not providing an integer `<<`: at width 8,
shifting 128 left by one is 0, and shifting 64 left by one is -128 read signed.
These assertions pin the bitvector wraparound semantics. A bounded-integer front
end that reports overflow instead must not lower integer `<<` directly to
`$bv<W>Shl`. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p() opaque {
  assert $bv8ToUInt($bv8Shl($intToBv8(128), $intToBv8(1))) == 0;
  assert $bv8ToInt($bv8Shl($intToBv8(64), $intToBv8(1))) == (0 - 128);
  assert $bv32ToUInt($bv32Shl($intToBv32(3), $intToBv32(2))) == 12
};
#end

/-! ### 7.3 A VARIABLE-count `>>` is composable from the primitives.

No integer wrapper is provided for it because the shift amount's own range
obligation and the semantics for a count at or beyond the width are front-end
decisions. What is pinned here is that the composition type-checks, computes,
and keeps the result in range. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int, s: int)
  requires x >= 0
  requires x <= 4294967295
  requires s >= 0
  requires s <= 31
  opaque
{
  assert $bv32ToUInt($bv32UShr($intToBv32(x), $intToBv32(s))) >= 0;
  assert $bv32ToUInt($bv32UShr($intToBv32(x), $intToBv32(s))) <= 4294967295
};
#end

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p() opaque {
  assert $bv32ToInt($bv32SShr($intToBv32(0 - 5), $intToBv32(1))) == (0 - 3);
  assert $bv8ToUInt($bv8Shl($intToBv8(1), $intToBv8(3))) == 8
};
#end

/-! ## 8. The operations that need no primitive.

### 8.1 Complement and AND-NOT by composition.

At width `W`, complement is `-x - 1` for a signed value and `2^W - 1 - x` for
an unsigned value; AND-NOT is AND with the complement of the right operand.
Both forms are checked against the bitwise operations, so a future integer
`$bitNot` would have to agree with these numbers. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p() opaque {
  // int8: the complement of 5 is -6, and AND-NOT(12, 10) is 4
  assert $bitAndS8(12, (0 - 10) - 1) == 4;
  // uint8: the complement of 10 is 245, and AND-NOT(12, 10) is 4
  assert $bitAndU8(12, 255 - 10) == 4;
  // the two agree on a value both types hold
  assert $bitAndS8(12, (0 - 10) - 1) == $bitAndU8(12, 255 - 10)
};
#end

/-! ### 8.2 `x >> k` for a constant k is floor division.

For a positive power-of-two divisor, Laurel's floor division matches arithmetic
shift right, including on a negative value where TRUNCATING division would give
a different answer. The `/t` row is what makes that distinction observable
rather than asserted. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int)
  requires x >= (0 - 2147483648)
  requires x <= 2147483647
  opaque
{
  assert (0 - 5) / 2 == (0 - 3);
  assert (0 - 1) / 2 == (0 - 1);
  assert 7 / 2 == 3;
  assert (0 - 5) /t 2 == (0 - 2);
  // and it agrees with the bitvector arithmetic shift
  assert (0 - 5) / 2 == $bv32ToInt($bv32SShr($intToBv32(0 - 5), $intToBv32(1)));
  // the result of a right shift stays inside the operand's range
  assert (x / 8) >= (0 - 2147483648);
  assert (x / 8) <= 2147483647
};
#end

/-! ### 8.3 `x << k` for a constant k is multiplication, and its overflow stays a
reported obligation.

This is the block that says what the boundary promise is NOT: `x * 8` on an
`int32`-ranged `x` does not stay in `int32`, and that is REPORTED. Had `<<` been
lowered onto `$bv32Shl` the same program would have wrapped silently. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(x: int)
  requires x >= (0 - 2147483648)
  requires x <= 2147483647
  opaque
{
  assert 3 * 4 == 12;
  assert (x * 8) <= 2147483647
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## 9. 128-bit comparisons are unavailable.

`bvOperatorWidths` includes `128` for the bitwise and cast externals.
`bvComparisonOp` has no 128-bit arm and the prelude declares no `$lt` at
`bv 128`, so a 128-bit comparison reports "no overload". -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(a: bv 128, b: bv 128) opaque {
  assert a < b
//       ^^^^^ error: no overload of '$lt' matches the argument types
};
#end

/-! ### 9.2 A `bv 32` comparison still resolves. -/

#eval testLaurelVerification (options := bwOptions) <|
#strata
program Laurel;
procedure p(a: bv 32, b: bv 32) opaque {
  assert (a < b) == (b > a)
};
#end
