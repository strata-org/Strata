/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Eager (non-short-circuit) boolean operators `&` and `|`

`&` and `|` are the eager boolean conjunction/disjunction. Unlike their
short-circuiting counterparts `&&`/`||` (see `ShortCircuit.lean`), they evaluate
*both* operands, so a precondition on the right operand (e.g. a divide-by-zero
check) is discharged regardless of what the left operand evaluates to.

This file covers:
- The truth tables of `&` and `|` on literals, plus `!` and boolean `==`.
- The defining logical laws on symbolic operands (using `==>`).
- The eager-evaluation contrast: the right operand's verification condition
  fires even when, under short-circuiting, the left operand would skip it.
-/

/-! ### Truth tables

`&`, `|`, `!` and boolean `==` are all supported by the standalone Laurel
interpreter, so this block runs all three paths. -/

#eval testLaurelExecution { skipCoreInterpreter := false, skipLaurelInterpreter := false } <|
#strata
program Laurel;
procedure eagerAndTruthTable()
  entry
  opaque
{
  assert true & true;
  assert !(true & false);
  assert !(false & true);
  assert !(false & false)
};

procedure eagerOrTruthTable()
  entry
  opaque
{
  assert true | true;
  assert true | false;
  assert false | true;
  assert !(false | false)
};

procedure eagerNotAndEq()
  entry
  opaque
{
  var t: bool := true;
  var f: bool := false;
  assert (!f) == true;
  assert (t & f) == false;
  assert (t | f) == true;
  assert (t == t) == true
};

procedure eagerAndNegative()
  entry
  opaque
{
  var t: bool := true;
  var f: bool := false;
  assert (t & f) == true
//^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### Logical laws (`==>`)

`==>` (implies) is not yet supported by the standalone Laurel interpreter, so these
laws stay verify-only (no `entry`; symbolic over `a`/`b`). -/

#eval testLaurelExecution {}
#strata
program Laurel;
procedure eagerAndLaws(a: bool, b: bool)
  opaque
{
  // `a & b` implies each conjunct.
  assert (a & b) ==> a;
  assert (a & b) ==> b
};

procedure eagerOrLaws(a: bool, b: bool)
  opaque
{
  // Each disjunct implies `a | b`.
  assert a ==> (a | b);
  assert b ==> (a | b)
};
#end

/-! ### Eager evaluation: the right operand is always evaluated

`&`/`|` do not short-circuit, so an imperative call in the right operand is
evaluated unconditionally. `mustNotBeCalled` has `requires false`; under `&&`
the call would be guarded and never reached (see `ShortCircuit.lean`), but `&`
evaluates it regardless of the left operand, so its precondition must be
discharged here and fails. -/

#eval testLaurelExecution { skipCoreInterpreter := false } <|
#strata
program Laurel;
procedure mustNotBeCalled(): int
  requires false
  opaque
{
  return 0
};

procedure eagerAndEvaluatesRightOperand()
  entry
  opaque
{
  var b: bool := false & mustNotBeCalled() > 0
//                       ^^^^^^^^^^^^^^^^^ error: precondition does not hold
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure mustNotBeCalled(): int
  requires false
  opaque
{
  return 0
};

procedure eagerOrEvaluatesRightOperand()
  opaque
{
  var b: bool := true | mustNotBeCalled() > 0
//                      ^^^^^^^^^^^^^^^^^ error: precondition does not hold
};
#end
