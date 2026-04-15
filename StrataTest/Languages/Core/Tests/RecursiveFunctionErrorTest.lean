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

rec function len<a>(@[cases] xs : MyList a) : int
{
  if MyList..isNil(xs) then 0 else 1 + len(MyList..tl(xs))
};

#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram polyRecPgm) |>.snd |>.isEmpty

/-- error: 🚨 Error during evaluation!
[ERROR] Polymorphic recursive functions are not yet supported for SMT verification: 'len'. SMT solvers require monomorphic axioms.

[DEBUG] Evaluated program: program Core;

datatype MyList (a : Type) {
  Nil(),
  Cons(hd : a, tl : MyList a)
};
rec function len<$__ty0> (@[cases] xs : MyList $__ty0) : int
{
  if MyList..isNil(xs) then 0 else 1 + len(MyList..tl(xs))
};
procedure len$$wf (xs : MyList $__ty18) returns ()
{
  assert [len_body_calls_MyList..tl_0]: !(MyList..isNil(xs)) ==> MyList..isCons(xs);
  };-/
#guard_msgs in
#eval verify polyRecPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 2: recursive function without @[cases] parameter is rejected
---------------------------------------------------------------------

def noCasesPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

#end

/-- error: 🚨 Error during evaluation!
[ERROR] Recursive function 'listLen' requires a @[cases] parameter

[DEBUG] Evaluated program: program Core;

datatype IntList {
  Nil(),
  Cons(hd : int, tl : IntList)
};
rec function listLen (xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};
procedure listLen$$wf (xs : IntList) returns ()
{
  assert [listLen_body_calls_IntList..tl_0]: !(IntList..isNil(xs)) ==> IntList..isCons(xs);
  };-/
#guard_msgs in
#eval verify noCasesPgm (options := .quiet)

end Strata.RecursiveFunctionErrorTest
