/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Recursive Function Error Tests

Tests that invalid recursive function declarations are rejected with
appropriate error messages during verification.
Note that these all consist of features that are not yet supported for
SMT-based verification; none are type errors.
-/

namespace Strata.RecursiveFunctionErrorTest

---------------------------------------------------------------------
-- Test 1: polymorphic recursive function is rejected
---------------------------------------------------------------------

def polyRecPgm : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

recursive function len<a>(xs : MyList a) : int
  decreases xs
{
  if MyList..isNil(xs) then 0 else 1 + len(MyList..tl(xs))
}

#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram polyRecPgm) |>.snd |>.isEmpty

/-- error: 🚨 Error during evaluation!
[ERROR] Polymorphic recursive functions are not yet supported: 'len'

[DEBUG] Evaluated program: datatype MyList (a : Type) {(
  (Nil())),
  (Cons(hd : a, tl : (MyList a)))
};-/
#guard_msgs in
#eval verify polyRecPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 2: recursive function without decreases clause is rejected
---------------------------------------------------------------------

def noDecreasesPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

recursive function listLen (xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}

#end

/-- error: 🚨 Error during evaluation!
[ERROR] Recursive function 'listLen' requires a decreases clause

[DEBUG] Evaluated program: datatype IntList {(
  (Nil())),
  (Cons(hd : int, tl : IntList))
};-/
#guard_msgs in
#eval verify noDecreasesPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 3: decreases on non-parameter expression is rejected
---------------------------------------------------------------------

def nonParamDecreasesPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

recursive function listLen (xs : IntList) : int
  decreases IntList..tl(xs)
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}

#end

/-- error: 🚨 Error during evaluation!
[ERROR] decreases must be a parameter name. General decreases expressions are not yet supported.

[DEBUG] Evaluated program: datatype IntList {(
  (Nil())),
  (Cons(hd : int, tl : IntList))
};-/
#guard_msgs in
#eval verify nonParamDecreasesPgm (options := .quiet)

end Strata.RecursiveFunctionErrorTest
