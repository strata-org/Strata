/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Exercises the E1 exceptional-channel root `BaseException` that ships in the
Laurel prelude (see `Strata/Languages/Laurel/CoreDefinitionsForLaurel.lean` and
`docs/design/laurel_extensions.md`).

Laurel predefines only `BaseException`. The catchable-vs-fatal tiering is
front-end policy, so this test program defines its own tiers as separate
children of the root — exactly as a real front-end would — and shows that the
F4/F5/F6 behavior falls out of ordinary `extends` + `is`.

Because `BaseException` is part of the always-on prelude, this also confirms the
prelude composite parses (a parse failure would yield an empty program and every
reference below would fail to resolve).
-/
#eval testLaurel <|
#strata
program Laurel;

// Front-end-defined tiers on top of the prelude root `BaseException`.
// Two separate children of the root: a catchable tier and a "fatal" tier.
composite AppException extends BaseException {}
composite FatalError extends BaseException {}

// A user-defined exception under the catchable tier (F4).
composite MyError extends AppException {
  var code: int
}

procedure baseExceptionIsUsable()
  opaque
{
  // The prelude root is available to every program and carries `message`.
  var b: BaseException := new BaseException;
  b#message := "root";
  assert b#message == "root";
  assert b is BaseException
};

procedure userExceptionIsRooted()
  opaque
{
  var e: MyError := new MyError;
  // `message` is inherited from `BaseException` two levels up the chain.
  e#message := "boom";
  e#code := 42;
  assert e#message == "boom";
  assert e#code == 42;
  // F4: a user exception is a subtype of its parent tier and of the root.
  assert e is MyError;
  assert e is AppException;
  assert e is BaseException
};

procedure fatalTierEscapesCatchAll()
  opaque
{
  // F5/F6: a fatal-tier value, bound at the channel root `BaseException` (as a
  // catch binding is), is provably not in the catchable tier — so a catch-all
  // predicated on `AppException` would not catch it. The escape falls out of
  // the subtype check, needing nothing beyond how the front-end wires `extends`.
  var f: BaseException := new FatalError;
  assert f is BaseException;
  assert !(f is AppException)
};
#end
