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

-- Only the clauses mention `Q`; it occurs in no input or output, so it
-- becomes an opaque type, since a call could not infer it.
#eval testLaurelVerification <|
#strata
program Laurel;
procedure clausesOnly<Q>(b: int) returns (r: int)
  requires forall(x: Q) => x == x
  opaque
  ensures forall(x: Q) => x == x;
#end

-- `E` occurs only in the thrown type, so it stays a type parameter, and the
-- procedure verifies.
#eval testLaurelVerification <|
#strata
program Laurel;
procedure thrower<E>(x: int) returns (r: int)
  throws (e: E)
  opaque
  ensures r == x + 1
{ r := x + 1 };
#end

-- The body and the clauses use the same type for `Q`.
#eval testLaurelVerification <|
#strata
program Laurel;
procedure bodyUses<Q>(b: int) returns (r: int)
  requires exists(x: Q) => x == x
  opaque
  ensures exists(x: Q) => x == x
{
  var q: Q;
  assert q == q;
  r := b
};
#end
