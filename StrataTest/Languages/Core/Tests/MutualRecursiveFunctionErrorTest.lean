/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Mutual Recursive Function Error Tests

Tests that invalid mutual recursive function declarations are rejected
with appropriate error messages.
-/

namespace Strata.MutualRecursiveFunctionErrorTest

---------------------------------------------------------------------
-- Test 1: polymorphic mutual recursive functions are rejected
---------------------------------------------------------------------

def polyMutualPgm : Program :=
#strata
program Core;

datatype MyList (a : Type) { Nil(), Cons(hd: a, tl: MyList a) };

rec function len<a>(@[cases] xs : MyList a) : int
{
  if MyList..isNil(xs) then 0 else 1 + lenHelper(MyList..tl(xs))
}
function lenHelper<a>(@[cases] xs : MyList a) : int
{
  if MyList..isNil(xs) then 0 else 1 + len(MyList..tl(xs))
};

#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram polyMutualPgm) |>.snd |>.isEmpty

/-- error: 🚨 Error during evaluation!
[ERROR] Polymorphic recursive functions are not yet supported for SMT verification: 'len'. SMT solvers require monomorphic axioms.

[DEBUG] Evaluated program: program Core;

datatype MyList (a : Type) {
  Nil(),
  Cons(hd : a, tl : MyList a)
};
rec function len<$__ty0> (@[cases] xs : MyList $__ty0) : int
{
  if MyList..isNil(xs) then 0 else 1 + lenHelper(MyList..tl(xs))
}
function lenHelper<$__ty18> (@[cases] xs : MyList $__ty18) : int
{
  if MyList..isNil(xs) then 0 else 1 + len(MyList..tl(xs))
};
procedure len$$wf (xs : MyList $__ty36) returns ()
{
  assert [len_body_calls_MyList..tl_0]: !(MyList..isNil(xs)) ==> MyList..isCons(xs);
  };
procedure lenHelper$$wf (xs : MyList $__ty48) returns ()
{
  assert [lenHelper_body_calls_MyList..tl_0]: !(MyList..isNil(xs)) ==> MyList..isCons(xs);
  };-/
#guard_msgs in
#eval verify polyMutualPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 2: missing @[cases] in mutual block is rejected
---------------------------------------------------------------------

def noCasesMutualPgm : Program :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function isEven (n : MyNat) : bool
{
  if MyNat..isZero(n) then true else isOdd(MyNat..pred(n))
}
function isOdd (n : MyNat) : bool
{
  if MyNat..isZero(n) then false else isEven(MyNat..pred(n))
};

#end

/-- error: 🚨 Error during evaluation!
[ERROR] Recursive function 'isEven' requires a @[cases] parameter

[DEBUG] Evaluated program: program Core;

datatype MyNat {
  Zero(),
  Succ(pred : MyNat)
};
rec function isEven (n : MyNat) : bool
{
  if MyNat..isZero(n) then true else isOdd(MyNat..pred(n))
}
function isOdd (n : MyNat) : bool
{
  if MyNat..isZero(n) then false else isEven(MyNat..pred(n))
};
procedure isEven$$wf (n : MyNat) returns ()
{
  assert [isEven_body_calls_MyNat..pred_0]: !(MyNat..isZero(n)) ==> MyNat..isSucc(n);
  };
procedure isOdd$$wf (n : MyNat) returns ()
{
  assert [isOdd_body_calls_MyNat..pred_0]: !(MyNat..isZero(n)) ==> MyNat..isSucc(n);
  };-/
#guard_msgs in
#eval verify noCasesMutualPgm (options := .quiet)

end Strata.MutualRecursiveFunctionErrorTest
