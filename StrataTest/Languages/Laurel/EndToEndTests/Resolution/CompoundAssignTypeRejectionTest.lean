/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Compound-assignment type rules. The accepted element types are per-operator,
driven by what the Laurel→Core lowering of `target op rhs` supports:

  * `+= -= *= /=` — `int`, int-based constrained types, and `real`.
  * `%=`          — `int` (and int-based constrained) only (`.Mod` has no real
                    lowering).
  * `^=`          — `string` only.

Two independent checks reject a bad compound assignment: `checkCompoundAssignTargetType`
flags an operator applied to an unsupported *target* element type (e.g. `^=` on an int,
`%=`/`+=` on a real/bv), and the bidirectional typing's `Check` rule flags a *RHS* whose
type doesn't match the target (`expected 'T', got 'U'`). A statement that is wrong both
ways (e.g. `s += 1`: `+=` rejects a string target, and the int RHS mismatches the string
target) legitimately reports both — same as elsewhere in the type checker.

This file also pins the *intended* asymmetry with `++`/`--`: `r += 1.0` on a real
succeeds (user-written RHS), while `r++` is rejected (synthesized int `1`; `realVar + 1`
is a type error under strict numeric typing). That asymmetry is deliberate, not a bug.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Rejected: target-type violations

Each uses a RHS whose type matches the target, so only the target-type check fires
(an op-vs-target mismatch, not a RHS mismatch). -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure strConcatOnInt() opaque {
  var x: int := 0;
  x ^= 1
//^^^^^^ error: The '^=' operator is only supported on 'string'
};
procedure addOnString() opaque {
  var s: string := "a";
  s += "b"
//^^^^^^^^ error: but the operand has type 'string'
};
procedure modOnReal() opaque {
  var r: real := 1.0;
  r %= 2.0
//^^^^^^^^ error: The '%=' operator is only supported on 'int' and int-based constrained types
};
procedure addOnBv(y: bv 32) opaque {
  var b: bv 32 := y;
  b += y
//^^^^^^ error: but the operand has type 'bv32'
};
procedure addOnFloat64(g: float64) opaque {
  var f: float64 := g;
  f += g
//^^^^^^ error: but the operand has type 'float64'
};
procedure modOnBv(y: bv 32) opaque {
  var b: bv 32 := y;
  b %= y
//^^^^^^ error: The '%=' operator is only supported on 'int' and int-based constrained types
};
procedure concatOnReal() opaque {
  var r: real := 1.0;
  r ^= r
//^^^^^^ error: The '^=' operator is only supported on 'string'
};
#end

/-! ## Rejected: RHS-type mismatch (valid target, wrong RHS — caught by the `Check` rule) -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure intPlusString() opaque {
  var x: int := 0;
  x += "s"
//     ^^^ error: expected 'int', got 'string'
};
procedure strConcatIntRhs() opaque {
  var s: string := "a";
  s ^= 1
//     ^ error: expected 'string', got 'int'
};
#end

/-! ## Accepted: `+=` on int, real, and a constrained int -/

#eval testLaurel <|
#strata
program Laurel;
constrained nat = v: int where v >= 0 witness 0
procedure addReal() opaque {
  var r: real := 1.0;
  r += 1.0;
  assert r == 2.0
};
procedure addNat() opaque {
  var n: nat := 1;
  n += 2;
  assert n == 3
};
#end

/-! ## The intended `++`-vs-`+=` asymmetry on reals

`r += 1.0` succeeds (above); `r++` is rejected (below). Side by side so the
divergence is documented as deliberate, not a regression to be "fixed". -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure incrReal() opaque {
  var r: real := 1.0;
  r++
//^^^ error: The increment ('++') operator is only supported on 'int' and int-based constrained types
};
#end

/-! ## A real-based constrained type is rejected by `%=` (peels to `real`)

`checkCompoundAssignTargetType` peels the constraint via `underlyingBaseType`, so a
`real`-backed constrained type lands on the same `%=`-rejects-`real` rule. -/

#eval testLaurelResolution <|
#strata
program Laurel;
constrained posReal = v: real where v >= 0.0 witness 0.0
procedure modConstrainedReal() opaque {
  var r: posReal := 1.0;
  r %= 2.0
//^^^^^^^^ error: The '%=' operator is only supported on 'int' and int-based constrained types
};
#end

/-! ## `/= 0` and `%= 0` retain the division-by-zero proof obligation (`skipProof := false`)

`x /= d` / `x %= d` lower to `x := x / d` / `x := x % d`, which carry the divisor≠0 VC.
With an unconstrained divisor the assertion-that-it-succeeds cannot be proved. -/

#eval testLaurel <|
#strata
program Laurel;
procedure divByZero(d: int) opaque {
  var x: int := 10;
  x /= d
//^^^^^^ error: assertion does not hold
};
procedure modByZero(d: int) opaque {
  var x: int := 10;
  x %= d
//^^^^^^ error: assertion does not hold
};
#end
