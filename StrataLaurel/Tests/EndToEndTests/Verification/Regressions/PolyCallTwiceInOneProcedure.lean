/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## Two instantiations of one polymorphic callee in one procedure

Both calls sit inside an expression on purpose: a call in statement position (`var b: bool :=
idp(true)`) is never lifted into a local, and a callee that is not `opaque` is rewritten functionally
rather than lifted, so either spelling silently stops exercising `LiftImperativeExpressions`. `idp`
must also be uncontracted, since `ContractPass` lifts a contracted callee's calls earlier. Its
result is then unconstrained, which is what the twin asserts against and why the positive case can
only assert tautologies.
-/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
procedure idp<T>(x: T) returns (r: T) opaque { r := x };
procedure twoInstantiationsInOneProcedure(k: int) opaque {
  assert idp(true) || true;
  assert idp(k) == k || true
};
procedure twoInstantiationsInOneProcedureFalseTwin(k: int) opaque {
  assert idp(true) || true;
  assert idp(k) == k
//^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
// One instantiation is the ENCLOSING procedure's type parameter rather than a concrete type.
procedure twoInstantiationsInGenericProcedure<U>(x: U) opaque {
  assert idp(x) == x || true;
  assert idp(1) == 1 || true
};
procedure twoInstantiationsInGenericProcedureFalseTwin<U>(x: U) opaque {
  assert idp(x) == x || true;
  assert idp(1) == 2
//^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
// A clause becomes a helper body, which this pass lifts in turn, so the collision is reachable from
// `ensures` as well. Each call sits in a disjunct the body itself discharges, because a clause does
// not assume the callee's postcondition.
procedure twoInstantiationsInEnsuresClauses(k: int) returns (o: int)
  opaque
  ensures o == k || idp(1) > 0
  ensures idp(true) || true
{ o := k };
procedure twoInstantiationsInEnsuresClausesFalseTwin(k: int) returns (o: int)
  opaque
  ensures o == k + 1 || idp(1) > 0
//        ^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
  ensures idp(true) || true
{ o := k };
// A callee with NO parameters: nothing but the expected type determines its output, so the
// instantiation has to survive from the context the lift removes.
procedure mk<T>() returns (r: T) opaque;
procedure twoNullaryInstantiationsInOneProcedure() opaque {
  assert mk() == 1 || true;
  assert mk() || true
};
procedure twoNullaryInstantiationsInOneProcedureFalseTwin() opaque {
  assert mk() == 1 || true;
  assert mk() && false
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
// The type variable sits INSIDE a parameter type rather than being one, so the instantiation has
// to be read out of the argument's type arguments and not just off the parameter.
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure unwrap<T>(o: Option<T>) returns (r: T) opaque;
procedure twoInstantiationsThroughACompositeParameter() opaque {
  assert unwrap(Some(true)) || true;
  assert unwrap(Some(1)) == 1 || true
};
// The local a CONDITIONAL's result goes into is declared bare and assigned in both branches, so
// it has no initializer to be typed from and the call itself has to carry the instantiation.
procedure twoInstantiationsInConditionalBranches(k: int) opaque {
  var b: bool := if k > 0 then idp(true) else false;
  var i: int := if k > 0 then idp(k) else 0;
  assert b || i == i || true
};
procedure twoInstantiationsInConditionalBranchesFalseTwin(k: int) opaque {
  var b: bool := if k > 0 then idp(true) else false;
  var i: int := if k > 0 then idp(k) else 0;
  assert b && i != i
//^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
