/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
constrained posnat = x: nat where x != 0 witness 1

// Input constraint becomes requires — body can rely on it
procedure inputAssumed(n: nat)
  opaque
{
  assert n >= 0
};

// Output constraint — valid return passes
procedure outputValid(): nat
  opaque
{
  return 3
};

// Output constraint — invalid return fails
procedure outputInvalid(): nat
//                         ^^^ error: postcondition does not hold
  opaque
{
  return -1
//^^^^^^^^^ error: assertion does not hold
};

// Return value of constrained type — caller gets ensures via call elimination
procedure opaqueNat(): nat;
procedure callerAssumes() returns (r: int)
  opaque
{
  var x: int := opaqueNat();
  assert x >= 0;
  return x
};

// Assignment to constrained-typed variable — valid
procedure assignValid()
  opaque
{
  var y: nat := 5
};

// Assignment to constrained-typed variable — invalid
procedure assignInvalid()
  opaque
{
  var y: nat := -1
//^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Reassignment to constrained-typed variable — invalid
procedure reassignInvalid()
  opaque
{
  var y: nat := 5;
  y := -1
//^^^^^^^ error: assertion does not hold
};

// A hole of a constrained type meets the type's constraint, as an uninitialized local does

procedure nondetHoleAtConstrainedType()
  opaque
{
  var x: nat := <??>;
  assert x >= 0
};

procedure detHoleAtConstrainedType()
  opaque
{
  var x: nat := <?>;
  assert x >= 0
};

procedure holeAtConstrainedParameter() returns (r: int)
  opaque
{
  return takesNat(<?>)
};

// Nothing more is assumed: two holes of the type need not agree
procedure holeIsAnyValueOfItsType()
  opaque
{
  var x: nat := <?>;
  var y: nat := <??>;
  assert x == y
//^^^^^^^^^^^^^ error: assertion does not hold
};

// In a loop invariant, a quantifier body or a transparent body only the call's precondition
// check sees the constraint, not the obligation
procedure natToInt(n: nat) returns (r: int) { n };
procedure holeInInvariant()
  opaque
{
  var i: int := 0;
  while (i < 1)
    invariant natToInt(<?>) >= 0
//            ^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    i := i + 1
  }
};

procedure holeInQuantifier()
  opaque
{
  assert forall(k: int) => natToInt(<?>) >= 0
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure natOfHole() returns (r: int) { natToInt(<?>) };
procedure holeInTransparentBody()
  opaque
{
  var y: int := natOfHole();
  assert y >= 0
//^^^^^^^^^^^^^ error: assertion does not hold
};

// Argument to constrained-typed parameter — valid
procedure takesNat(n: nat) returns (r: int)
  opaque
{ return n };
procedure argValid() returns (r: int)
  opaque
{
  var x: int := takesNat(3);
  return x
};

// Argument to constrained-typed parameter — invalid (requires violation)
procedure argInvalid() returns (r: int)
  opaque
{
  var x: int := takesNat(-1);
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
  return x
};

// Nested constrained type — independent constraints require transitive collection
constrained even = x: int where x % 2 == 0 witness 0
constrained evenpos = x: even where x > 0 witness 2
procedure nestedInput(x: evenpos)
  opaque
{
  assert x > 0;
  assert x % 2 == 0
};

// Multiple constrained-typed parameters
procedure multiParam(a: nat, b: nat)
  opaque
{
  assert a >= 0;
  assert b >= 0
};

// Two calls to same procedure — no temp var collision
procedure twoCalls() returns (r: int)
  opaque
{
  var a: int := takesNat(1);
  var b: int := takesNat(2);
  return a + b
};

// Constrained type in expression position must be resolved
procedure constrainedInExpr()
  opaque
{
  var b: bool := forall(n: nat) => n + 1 > n;
  assert b
};

// Invalid witness — witness -1 does not satisfy x > 0
constrained bad = x: int where x > 0 witness -1
//                                           ^^ error: assertion does not hold

// Uninitialized constrained variable — havoc + assume constraint
procedure uninitNat()
  opaque
{
  var y: nat;
  assert y >= 0
};

procedure sideEffect()
  opaque
{
  var x : nat;
  var y : int;
  y := (x := -1) + 1;
//      ^^^^^^^ error: assertion does not hold
  assert x==-1;
  assert y==0
};

// Uninitialized nested constrained variable — havoc + assume constraint
procedure uninitPosnat()
  opaque
{
  var y: posnat;
  assert y != 0;
  assert y >= 0
};

// Uninitialized constrained variable — witness value is not provable
procedure uninitNotWitness()
  opaque
{
  var y: posnat;
  assert y == 1
//^^^^^^^^^^^^^ error: assertion does not hold
};

// Quantifier constraint injection — forall
// n + 1 > 0 is only provable with n >= 0 injected; false for all int
procedure forallNat() opaque {
  var b: bool := forall(n: nat) => n + 1 > 0;
  assert b
};

// Quantifier constraint injection — exists
// n == -1 is satisfiable for int, but not when n >= 0 is required
// n == 42 works because 42 >= 0
procedure existsNat() opaque {
  var b: bool := exists(n: nat) => n == 42;
  assert b
};

// Quantifier constraint injection — nested constrained type
// n - 1 >= 0 is only provable with n > 0 injected
procedure forallPosnat()
  opaque
{
  var b: bool := forall(n: posnat) => n - 1 >= 0;
  assert b
};

// Capture avoidance — bound var y in constraint must not collide with parameter y
// Without capture avoidance, requires becomes exists(y) => y > y (false), making body vacuously true
constrained haslarger = x: int where (exists(y: int) => y > x) witness 0
procedure captureTest(y: haslarger)
  opaque
{
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};

// A TRANSPARENT procedure returning a constrained type stays transparent, so the
// caller sees the body and can reason about the VALUE — not merely that it is
// valid. That is what makes `double(n) == n + n` provable here.
procedure double(n: nat) : nat
{
  return n + n
};
procedure callerSeesValue(n: nat)
  opaque
{
  assert double(n) == n + n
};

// A transparent procedure's constrained output is checked at the definition, at the
// return: `n - 1` leaves nat's range for n == 0.
procedure badDouble(n: nat) : nat
{
  return n - 1
//^^^^^^^^^^^^ error: assertion does not hold
};

// And enforced again wherever the value is relied on. Assigning to a
// constrained-typed variable asserts it...
procedure badDoubleAssignCaught(n: nat)
  opaque
{
  var y: nat := badDouble(n)
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// ...and a constrained-typed parameter checks the callee's generated requires.
procedure badDoubleArgCaught(n: nat) returns (r: int)
  opaque
{
  var x: int := takesNat(badDouble(n));
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
  return x
};

// A quantifier over a constrained binder in a `requires` keeps its injected
// constraint, so `p` holds for every `nat` and the body's use of it is sound;
// without that injection the binder would range over all `int`.
procedure quantifiedPrecondition(n: nat, p: bool) : nat
  requires p == forall(m: nat) => m >= 0
{
  return n
};
procedure quantifiedPreconditionHolds(n: nat) : int
  opaque
{
  var r: int := quantifiedPrecondition(n, true);
  return r
};

// A polymorphic transparent procedure with a constrained output stays transparent.
procedure countOf<T>(x: T) : nat
{
  return 0
};
procedure usesCountOf(b: bool)
  opaque
{
  assert countOf(b) == 0
};

// The constraint is still checked for a polymorphic procedure, not merely
// well-formed: `-1` leaves nat's range regardless of `T`.
procedure badCountOf<T>(x: T) : nat
{
  return 0 - 1
//^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A constrained type's base can be a generic composite instantiation: `Box<int>` is
-- monomorphized and the base names the monomorph, so a read through a `CB` parameter is
-- modelled — a correct postcondition is provable and a false one is caught.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var v: T }
constrained CB = v: Box<int> where true witness <??>

procedure readsBaseField(c: CB) returns (r: int)
  opaque
  ensures r == c#v
{
  r := c#v
};

procedure falsePostconditionIsCaught(c: CB) returns (r: int)
  opaque
  ensures r == c#v + 1
//        ^^^^^^^^^^^^ error: postcondition does not hold
{
  r := c#v
};
#end

-- The constraint and the witness are type positions too. Each names a different instantiation
-- here, so each slot is reachable through exactly one of them.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var v: T }
constrained CW = x: int
  where (forall(b: Box<int>) => true)
  witness (if (forall(c: Box<bool>) => true) then 0 else 1)

procedure readsConstrainedValue(c: CW) returns (r: int)
  opaque
  ensures r == c
{
  r := c
};
#end

-- A virtual method that is TRANSPARENT with a constrained output, reachable only because
-- a transparent body with a constrained output is not demoted to opaque.
-- `LiftInstanceProcedures` splits it into `T$m$impl` and a `T$m` dispatcher with
-- `{ proc with … }`, so the two share their output parameter's `uniqueId`.
-- `FunctionalRewrite` names an unassigned output's hole after that id, and the hole is a
-- GLOBAL procedure, so the id alone mints the same name twice and resolution reports a
-- duplicate definition.
--
-- Guards the owner-qualified hole name in `FunctionalRewrite.declHoleName`.
#eval testLaurelVerification <|
#strata
program Laurel;
constrained int32c = v: int where v >= -2147483648 && v <= 2147483647 witness 0
composite BaseH { procedure compute(self: BaseH) : int32c { return 1 }; }
composite ChildH extends BaseH { procedure compute(self: ChildH) : int32c { return 2 }; }
#end

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
composite Inner { var x: nat }
composite Outer { var i: Inner }
composite Exception {}

procedure opq(x: int) : nat opaque;
procedure viaOpq(x: int) : nat { return opq(x) };
procedure viaOpqBad(x: int) : nat
{
  return opq(x) - 1
//^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure getNested(o: Outer) : nat { return o#i#x };
procedure getNestedBad(o: Outer) : nat
{
  return o#i#x - 1
//^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure throwsNat(x: nat) : nat throws (e: Exception) { return x };
procedure throwsNatBad(x: nat) : nat throws (e: Exception)
{
  return x - 1
//^^^^^^^^^^^^ error: assertion could not be proved
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0

procedure unassignedOutput(): nat
//                            ^^^ error: postcondition does not hold
  opaque
{
  -1
};

procedure unassignedOnOnePath(b: bool) returns (r: nat)
//                                                 ^^^ error: postcondition does not hold
  opaque
{
  if b then { r := 1 }
};

procedure tailValue(): nat { 3 };
procedure tailValueIf(b: bool): nat { if b then 1 else 2 };
procedure usesTailValues() opaque { assert tailValue() == 3; assert tailValueIf(true) == 1 };

procedure badTailValue(): nat { -1 };
//                        ^^^ error: assertion does not hold
//                              ^^ error: assertion does not hold
procedure badTailValueIf(b: bool): nat { if b then 1 else -1 };
//                                 ^^^ error: assertion does not hold
//                                                        ^^ error: assertion does not hold
procedure badTailValueBeforeAssert(): nat { -1; assert true };
//                                    ^^^ error: assertion does not hold
//                                          ^^ error: assertion does not hold

procedure knowsPositive(x: int) opaque ensures x > 0;
procedure tailLemma(x: nat) returns (r: nat) { r := x * x; knowsPositive(x) };
procedure useTailLemma(x: nat) opaque { assert tailLemma(x) == x * x };

procedure partialNat(b: bool): nat { if b then { return 1 } };
//                             ^^^ error: assertion does not hold
procedure neverNat() returns (r: nat) { assert true };
//                               ^^^ error: assertion does not hold
procedure earlyBadReturn(x: int): nat { if x < 0 then { return x }; return 0 };
//                                                      ^^^^^^^^ error: assertion does not hold
#end

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
procedure q0() returns (r: nat) { r := 1; true };
//        ^^ error: ❌ Type checking error.
#end
