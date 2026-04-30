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

/--
error: ❌ Type checking error.
Polymorphic recursive functions are not yet supported for SMT verification: 'len'. SMT solvers require monomorphic axioms.
-/
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
decreases n
{
  if MyNat..isZero(n) then true else isOdd(MyNat..pred(n))
}
function isOdd (n : MyNat) : bool
decreases n
{
  if MyNat..isZero(n) then false else isEven(MyNat..pred(n))
};

#end

/--
error: ❌ Type checking error.
Recursive function 'isEven' requires a @[cases] parameter
-/
#guard_msgs in
#eval verify noCasesMutualPgm (options := .quiet)

end Strata.MutualRecursiveFunctionErrorTest
