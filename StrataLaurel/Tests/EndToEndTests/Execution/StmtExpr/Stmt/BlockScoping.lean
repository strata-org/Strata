/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A declaration in a nested block is visible inside that block only: on the way
out, a local it shadowed means what it meant before. A branch of an `if` is a block
too. The pipeline accepts such shadowing in a transparent body. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure nestedBlock(): int
{
  var x: int := 0;
  {
    var x: int := 1
  };
  return x
};

procedure branch(c: bool): int
{
  var x: int := 0;
  if c then {
    var x: int := 1
  };
  return x
};

procedure runAll()
  entry
  opaque
{
  assert nestedBlock() == 0;
  assert branch(true) == 0;
  assert branch(false) == 0
};
#end

/-! A write to the outer local inside the block, before the declaration that
shadows it, is kept: leaving the block restores the value the local had when it
was shadowed, not when the block was entered. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure writeBeforeShadow(): int
{
  var x: int := 0;
  {
    x := 5;
    var x: int := 1
  };
  return x
};

procedure runAll()
  entry
  opaque
{
  assert writeBeforeShadow() == 5
};
#end

/-! A block-local named like a global hides the global inside the block only:
afterwards reads and writes reach the global again. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
var g: int := 10

procedure readGlobal(): int
{
  return g
};

procedure runAll()
  entry
  opaque
{
  {
    var g: int := 1
  };
  assert g == 10;
  g := 7;
  assert readGlobal() == 7
};
#end

/-! So is an unbraced `try` body or `catch` body. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
var g: int := 10
procedure inTry()
  requires g == 10
  opaque
{
  try var g: int := 1 finally { };
  assert g == 10
};

procedure inCatch()
  requires g == 10
  opaque
{
  try { throw 0 } catch c var g: int := 3;
  assert g == 10
};

procedure runAll()
  entry
  opaque
{
  inTry();
  inCatch()
};
#end

/-! An unbraced `finally` body is a scope too, but the lowering to Core runs its
declaration in the enclosing scope, so the verifier and the Core interpreter both see
`g` as 2 afterwards. Only the Laurel interpreter runs this block until that is fixed. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
var g: int := 10
procedure inFinally()
  entry
  opaque
{
  try { } finally var g: int := 2;
  assert g == 10
};
#end

/-! An arm of an `if` in expression position is a scope as well. Lifting the
declaration out of the expression loses it, so the verifier and the Core interpreter
fail on this program with an internal resolution error; only the Laurel interpreter
runs it. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
var g: int := 10
procedure runAll()
  entry
  opaque
{
  var r: int := if true then var g: int := 1 else 0;
  assert g == 10
};
#end
