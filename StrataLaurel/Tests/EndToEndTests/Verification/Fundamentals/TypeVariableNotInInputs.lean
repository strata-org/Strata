/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A contract on a procedure with a type variable that no input mentions -/

-- Nothing mentions `Q`.
#eval testLaurelVerification <|
#strata
program Laurel;
procedure unmentioned<Q>(b: int) returns (r: int)
  requires b > 0
  opaque
  ensures r > b + 1
//        ^^^^^^^^^ error: postcondition does not hold
{ r := b + 1 };
#end

-- Only the result mentions `T`, so `arb$pre0` binds just `S` and `arb$post0` both.
#eval testLaurelVerification <|
#strata
program Laurel;
procedure arb<S, T>(s: S, n: int) returns (r: T) requires n > 0 opaque ensures r == r;

procedure factoryContract()
  opaque
{
  var a: int := arb(true, 1);
  var b: bool := arb(true, 0)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
};
#end

-- Only the clauses mention `Q`, so their helpers bind it. Nothing calls them: a call could not
-- infer `Q`.
#eval testLaurelVerification <|
#strata
program Laurel;
procedure clausesOnly<Q>(b: int) returns (r: int)
  requires forall(x: Q) => x == x
  opaque
  ensures forall(x: Q) => x == x;
#end
