/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution { skipCoreInterpreter := false }
#strata
program Laurel;
procedure mustNotCallFunc(x: int): int
  requires false
{ return x };

procedure mustNotCallProc(): int
  requires false
  opaque
{
  return 0
};

// Pure path: function with requires false
procedure testAndThenFunc()
  entry
  opaque
{
  var b: bool := false && mustNotCallFunc(0) > 0;
  assert !b
};

procedure testOrElseFunc()
  entry
  opaque
{
  var b: bool := true || mustNotCallFunc(0) > 0;
  assert b
};

procedure testImpliesFunc()
  entry
  opaque
{
  var b: bool := false ==> mustNotCallFunc(0) > 0;
  assert b
};

// Pure path: division by zero

procedure testAndThenDivByZero()
  entry
  opaque
{
  assert !(false && 1 / 0 > 0)
};

procedure testOrElseDivByZero()
  entry
  opaque
{
  assert true || 1 / 0 > 0
};

procedure testImpliesDivByZero()
  entry
  opaque
{
  assert false ==> 1 / 0 > 0
};

// Imperative path: procedure with requires false

procedure testAndThenProc()
  entry
  opaque
{
  var b: bool := false && mustNotCallProc() > 0;
  assert !b
};

procedure testOrElseProc()
  entry
  opaque
{
  var b: bool := true || mustNotCallProc() > 0;
  assert b
};

procedure testImpliesProc()
  entry
  opaque
{
  var b: bool := false ==> mustNotCallProc() > 0;
  assert b
};
#end

/-! ## Standalone Laurel interpreter: skip-free `&&` / `||`

The blocks above use `> 0` comparisons and `==>`, which the standalone Laurel
interpreter does not yet implement, so they stay verify + Core only. This block
covers the same short-circuit behavior for `&&`/`||` in a form the Laurel
interpreter *can* run — with no skips — by booby-trapping the right-operand callee
two ways so every path (verify, Core interpret, Laurel interpret) observes a
short-circuit miss:

- `requires false` — the verifier proves the callee's own body vacuously (fine in
  isolation); at a *guarded* call site the precondition is never checked because
  `&&`/`||` short-circuit. If a short-circuit misfired, it would fail.
- body `assert false` — the interpreters ignore contracts, so if either actually
  called the callee it would record an assertion failure. Short-circuited, the
  callee is never entered, so no failure fires.

Making the callee bool-returning drops the `>` dependency. (`==>` is left to the
verify+Core blocks above until a lazy `.Implies` case lands beside
`.AndThen`/`.OrElse` in `evalExpr`.) -/

#eval testLaurelExecution { skipCoreInterpreter := false, skipLaurelInterpreter := false } <|
#strata
program Laurel;
procedure boom() returns (r: bool)
  requires false
  opaque
{
  assert false;
  return true
};

procedure shortCircuitAndThen()
  entry
  opaque
{
  var b: bool := false && boom();
  assert !b
};

procedure shortCircuitOrElse()
  entry
  opaque
{
  var b: bool := true || boom();
  assert b
};
#end
