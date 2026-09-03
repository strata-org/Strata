/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

-- Laurel interpreter stays off: `fooReassign` uses destructive assignment
-- (`x := x + 1`), which the standalone evaluator does not yet support.
#eval testLaurelExecution { skipCoreInterpreter := false }
#strata
program Laurel;
procedure fooReassign(): int
  opaque // required because we don't yet support destructive assignment in transparent bodies
{
  var x: int := 0;
  x := x + 1;
  assert x == 1;
  x := x + 1;
  x
};

procedure fooSingleAssign(): int
{
  var x: int := 0;
  var x2: int := x + 1;
  var x3: int := x2 + 1;
  return x3
};

procedure fooProof()
  entry
  opaque
{
  var x: int := fooReassign();
  var y: int := fooSingleAssign()
// The following assertions fails while it should succeed,
// because we don't yet support making fooReassign transparent
//  assert x == y;
};

procedure aFunction(x: int): int
{
  return x
};

procedure aFunctionCaller()
  entry
  opaque
{
  var x: int := aFunction(3);
  assert x == 3
};
#end

/-! Multi-argument and nested procedure calls with boolean return values, using
    only operators the standalone Laurel interpreter implements (`&`, `!`).

    The helper procedures are transparent (no `opaque`) so the verifier sees the
    bodies and can prove the call-site assertions, matching what the interpreters
    compute concretely. -/

#eval testLaurelExecution { skipCoreInterpreter := false, skipLaurelInterpreter := false } <|
#strata
program Laurel;
procedure idBool(b: bool) returns (r: bool)
{ return b };

procedure myAnd(a: bool, b: bool) returns (r: bool)
{ return a & b };

procedure check3(a: bool, b: bool, c: bool) returns (r: bool)
{ return a & b & !c };

procedure myNot(b: bool) returns (r: bool)
{ return !b };

procedure myNand(a: bool, b: bool) returns (r: bool)
{ return myNot(a & b) };

procedure boolCallsOK()
  entry
  opaque
{
  var t: bool := true;
  var f: bool := false;

  assert idBool(t) == true;
  assert myAnd(t, t) == true;
  assert myAnd(t, f) == false;
  assert check3(t, t, f) == true;
  assert myNand(t, t) == false;
  assert myNand(t, f) == true
};
#end
