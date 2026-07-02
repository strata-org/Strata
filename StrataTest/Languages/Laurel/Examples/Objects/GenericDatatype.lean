/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Minimal generic (polymorphic) datatypes for Laurel. Laurel's surface gains
type-parameter lists on `datatype` (`Option<T>`, `Result<Val, Err>`) and generic
type application in type positions (`Option<int>`), lowering to Strata Core's
already-existing polymorphic datatypes (SMT `(declare-datatype … (par …))`).

Laurel's own type checking is erased for generics — type arguments are carried
syntactically and checked by Core — so constructor calls are typed at the bare
datatype and `Option<int>` is treated as `Option` for consistency. This unblocks
E7's `Result<Val, Err>` lowering.
-/

-- Single type parameter: construct, test, and destruct a generic `Option`.
#eval testLaurel <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure useOption()
  opaque
{
  var o: Option<int> := Some(42);
  assert Option..isSome(o);
  assert Option..value(o) == 42;
  var n: Option<int> := Nothing();
  assert Option..isNothing(n)
};
#end

-- Two type parameters: the `Result<Val, Err>` shape that E7 lowering targets.
#eval testLaurel <|
#strata
program Laurel;
datatype Result<Val, Err> {
  Good(value: Val),
  Bad(err: Err)
}
procedure useResult()
  opaque
{
  var ok: Result<int, string> := Good(7);
  assert Result..isGood(ok);
  assert Result..value(ok) == 7;
  var err: Result<int, string> := Bad("boom");
  assert Result..isBad(err);
  assert Result..err(err) == "boom"
};
#end
