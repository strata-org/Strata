/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## DDM parsing tests for recursive functions

These tests verify that the DDM parser correctly handles recursive function
syntax, including the `decreases` clause and the function name being in scope
within the body for recursive calls.
-/

namespace Strata

-- Test: recursive function with self-call in body
def recFuncDDMPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

recursive function listLen (xs : IntList) : int
  decreases xs
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}

#end

/--
info: program Core;
datatype IntList {(
  (Nil())),
  (Cons(hd : int, tl : IntList))
};
recursive function listLen (xs : IntList) : int
  decreases xs
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}
-/
#guard_msgs in
#eval IO.println recFuncDDMPgm

end Strata

/-! ## Test: polymorphic recursive function — DDM parsing -/

namespace Strata.RecFuncPolyTest

def polyRecFuncPgm : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

recursive function len<a>(xs : MyList a) : int
  decreases xs
{
  if MyList..isNil(xs) then 0 else 1 + len(MyList..tl(xs))
}

#end

/-- info: program Core;
datatype MyList (a : Type) {(
  (Nil())),
  (Cons(hd : a, tl : (MyList a)))
};
recursive function len<a> (xs : (MyList a)) : int
  decreases xs
{
  if MyList..isNil(xs) then 0 else 1 + len(MyList..tl(xs))
}
-/
#guard_msgs in
#eval IO.println polyRecFuncPgm

end Strata.RecFuncPolyTest
