/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution {} <|
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

/-! Multi-argument and nested procedure calls with boolean return values.

    The helper procedures are transparent (no `opaque`) so the verifier sees the
    bodies and can prove the call-site assertions, matching what the interpreters
    compute concretely. -/

#eval testLaurelExecution {} <|
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

/-! An output that is also an input is an in-out parameter: it starts with the
argument's value. Run by the Laurel interpreter only. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure inc(x: int) returns (x: int)
  opaque
{
  x := x + 1
};

procedure main()
  entry
  opaque
{
  var y: int := 4;
  y := inc(y);
  assert y == 5
};
#end

/-! The Laurel interpreter runs a program only once it resolves, as the Core
interpreter does: without resolution an overloaded call cannot be bound to its
overload. -/

/-- error: laurel-interpret: resolution failed: #[Resolution failed: 'undefinedThing' is not defined]
-/
#guard_msgs in
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure f(x: int): int { return x + 1 };
procedure f(x: bool): bool { return !x };

procedure broken()
  opaque
{
  var z: int := undefinedThing
//              ^^^^^^^^^^^^^^ error: 'undefinedThing' is not defined
};

procedure main()
  entry
  opaque
{
  var a: int := f(1);
  assert a == 2
};
#end

/-! An output the body never assigns, a field never written and a declared local
never assigned each hold an arbitrary but fixed value, which can be computed with.
The Laurel interpreter starts each at its type's default; the Core interpreter
does not reduce an assertion over an unconstrained value, so it does not run this
block. -/

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Box {
  var v: int
}

procedure unassigned() returns (r: int)
  opaque
{
  assert true
};

procedure main()
  entry
  opaque
  modifies *
{
  var x: int := unassigned();
  assert x + 0 == x;
  var b: Box := new Box;
  var f: int := b#v;
  assert f == b#v;
  var d: int;
  assert d == d
};
#end

/-! An unassigned local or field of a constrained type satisfies its constraint: the
Laurel interpreter starts it at the type's witness, not at the base type's zero.
The Core interpreter does not reduce an assertion over an unconstrained value, so it
does not run this block. -/

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
constrained pos = x: int where x > 0 witness 1
composite PosBox {
  var v: pos
}

procedure unassignedConstrained()
  entry
  opaque
  modifies *
{
  var q: pos;
  assert q > 0;
  var b: PosBox := new PosBox;
  assert b#v > 0
};
#end

/-! A negative witness, integer or real, is the starting value too. -/

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
constrained negInt = x: int where x < 0 witness -2
constrained negReal = x: real where x < 0.0 witness -1.5

procedure unassignedNegative()
  entry
  opaque
{
  var i: negInt;
  assert i < 0;
  var r: negReal;
  assert r < 0.0
};
#end

/-! A witness need not be a literal: it is evaluated before the entry runs. The
Core interpreter does not reduce an assertion over such a value. -/

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
constrained two = x: int where x > 1 witness 1 + 1

procedure unassignedComputedWitness()
  entry
  opaque
{
  var i: two;
  assert i > 1
};
#end

/-! A witness is checked against its type's constraint whether or not the type is
used, and a partial operation in it is reported at the witness, as the verifier
reports both. -/

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
constrained bad = x: int where x > 0 witness 1 / 0
//                                           ^^^^^ error: divisor is non-zero does not hold
//                                           ^^^^^ error: assertion does not hold
procedure main()
  entry
  opaque
{
  var y: int := 1;
  assert y == 1
};
#end

/-! A witness the interpreter cannot evaluate, because it calls an external procedure,
throws or does not terminate, is reported at the witness and leaves its type without a
starting value; a run that never uses the type carries on. The verifier rejects or
cannot prove these witnesses, so only the Laurel interpreter runs these blocks. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure mk() returns (r: int) external;
procedure thr() returns (r: int) throws (e: int) opaque { throw 1 };
procedure lp() returns (r: int) { var i: int := 0; while (true) invariant true { i := i + 1 }; return i };
constrained ext = x: int where x > 0 witness mk()
//                                           ^^^^ error: witness of 'ext' could not be evaluated
constrained thrown = x: int where x > 0 witness thr()
//                                              ^^^^^ error: witness of 'thrown' could not be evaluated
constrained diverges = x: int where x > 0 witness lp()
//                                                ^^^^ error: witness of 'diverges' could not be evaluated
procedure main()
  entry
  opaque
{
  var y: int := 1;
  assert y == 1
};
#end

/-! Declaring a variable of such a type is an error, since it has no value to start
at. -/

/-- error: 'i' has no starting value: the witness of 'ext' could not be evaluated
-/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure mk() returns (r: int) external;
constrained ext = x: int where x > 0 witness mk()
//                                           ^^^^ error: witness of 'ext' could not be evaluated
procedure main()
  entry
  opaque
{
  var i: ext;
  var j: int := i + 1
};
#end

/-! A witness is checked against the constraint of every constrained type it refines,
not only its own. -/

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
constrained big = x: int where x > 5 witness 6
constrained small = y: big where y > 0 witness 1
//                                             ^ error: assertion does not hold
procedure main()
  entry
  opaque
{
  var y: int := 1;
  assert y == 1
};
#end

/-! A file-scope initialiser's failure is reported at the initialiser, not at a
witness evaluated before it. The verifier does not check a file-scope initialiser's
preconditions, so only the Laurel interpreter runs this block. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
constrained pos = x: int where x > 0 witness 1
var g: int := 1 / 0
//            ^^^^^ error: divisor is non-zero does not hold
procedure main()
  entry
  opaque
{
  var y: int := 1;
  assert y == 1
};
#end

/-! A precondition of an operator is reported at the caller's statement even when an
operand is itself a call. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure zero() returns (r: int)
  opaque
  ensures r == 0
{
  var t: int := 0;
  r := t
};

procedure main()
  entry
  opaque
{
  var z: int := 10 / zero()
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: divisor is non-zero does not hold
};
#end
