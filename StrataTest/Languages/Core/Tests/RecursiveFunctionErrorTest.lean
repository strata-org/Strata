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

/--
error: ❌ Type checking error.
Polymorphic recursive functions are not yet supported for SMT verification: 'len'. SMT solvers require monomorphic axioms.
-/
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
decreases xs
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

#end

/--
error: ❌ Type checking error.
Recursive function 'listLen' requires a @[cases] parameter
-/
#guard_msgs in
#eval verify noCasesPgm (options := .quiet)

end Strata.RecursiveFunctionErrorTest
