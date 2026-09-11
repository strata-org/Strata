/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Base {
  var xValue: int
}

composite Base2 {
  var yValue: int
}

composite Extender extends Base, Base2 {
  var zValue: int
}

procedure inheritedFields(a: Extender)
  opaque
  modifies a
{
  a#xValue := 1;
  a#yValue := 2;
  a#zValue := 3;

  assert a#xValue == 1;
  assert a#yValue == 2;
  assert a#zValue == 3
};

procedure typeCheckingAndCasting()
  opaque
{
  var a: Base := new Base;
  assert a is Base;
  assert !(a is Extender);
  var b: Extender := new Extender;
  assert b is Base;
  assert b is Base2;
  assert b is Extender;

  var c: Base := b;
  var d: Extender := c as Extender;
  var e: Extender := a as Extender
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

composite Top {
  var tValue: int
}

composite Left extends Top {
  var lValue: int
}
composite Right extends Top {
  var rValue: int
}
composite Bottom extends Left, Right {
  var bValue: int
}

procedure diamondInheritance()
  opaque
{
  var b: Bottom := new Bottom;
  b#lValue := 1;
  b#rValue := 2;
  b#bValue := 3;
  // tValue can not be used

  assert b#lValue == 1;
  assert b#rValue == 2;
  assert b#bValue == 3;

  assert b is Left;
  assert b is Right;
  assert b is Top;
  assert b is Bottom
};

// Currently does not pass. Implementation needs b type invariant mechanism that we have yet to add.
//procedure typedParameter(b: Bottom) opaque {
//  var b: Bottom := b;
//  assert b is Left;
//  assert b is Right;
//  assert b is Top;
//  assert b is Bottom;
//}
#end

-- A front-end-defined hierarchy with two tiers under one root, which is the shape a
-- front end needs for its exception classes: the root carries shared fields, a user
-- type inherits them from two levels up, and a sibling tier is provably outside the
-- catchable one. Only `extends` and `is` are exercised — no `throw`/`try` — so this
-- belongs with inheritance rather than with the exception tests, which rely on it.
#eval testLaurelExecution {} <|
#strata
program Laurel;

// Front-end-defined root and its two tiers: a catchable tier and a "fatal" tier
// as separate children of the root.
composite Exception {
  var message: string
}
composite AppException extends Exception {}
composite FatalError extends Exception {}

// A user-defined exception under the catchable tier.
composite MyError extends AppException {
  var code: int
}

procedure rootIsUsable()
  opaque
{
  // The front-end root carries `message` and is usable directly.
  var b: Exception := new Exception;
  b#message := "root";
  assert b#message == "root";
  assert b is Exception
};

procedure userExceptionIsRooted()
  opaque
{
  var e: MyError := new MyError;
  // `message` is inherited from `Exception` two levels up the chain.
  e#message := "boom";
  e#code := 42;
  assert e#message == "boom";
  assert e#code == 42;
  // A user exception is a subtype of its parent tier and of the root.
  assert e is MyError;
  assert e is AppException;
  assert e is Exception
};

procedure fatalTierEscapesCatchAll()
  opaque
{
  // A fatal-tier value, bound at the root `Exception` (as a catch-all
  // binding would be), is provably not in the catchable tier — so a catch-all
  // predicated on `AppException` would not catch it. The escape falls out of
  // the subtype check, needing nothing beyond how the front-end wires `extends`.
  var f: Exception := new FatalError;
  assert f is Exception;
  assert !(f is AppException)
};
#end
