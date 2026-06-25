/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

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
error: ❌ Symbolic evaluation error.
Polymorphic recursive functions are not yet supported for SMT verification: 'len'. SMT solvers require monomorphic axioms.
-/
#guard_msgs in
#eval Core.verify polyRecPgm (options := .quiet)

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
error: recursive function 'listLen': structural recursion requires @[cases]
-/
#guard_msgs in
#eval Core.verify noCasesPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 3: error — decreases on non-int expression
---------------------------------------------------------------------

def decreasesNonIntPgm : Program :=
#strata
program Core;

function f () : bool;

rec function bad (n : int) : int
  decreases f
{
  if n <= 0 then 0 else bad(n - 1)
};
#end

/-- error: ❌ Type checking error.
recursive function 'bad': non-variable decreases expression must have type int, got 'bool'. For structural recursion, use a parameter name-/
#guard_msgs in
#eval Strata.Core.verify decreasesNonIntPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 4: error — decreasing argument contains recursive call
---------------------------------------------------------------------

def decreasesRecCallPgm : Program :=
#strata
program Core;

rec function bad (n : int) : int
  decreases n
{
  if n <= 0 then 0 else bad(bad(n - 1))
};
#end

/-- error: termination checking 'bad': decreasing argument contains a recursive call -/
#guard_msgs in
#eval Strata.Core.verify decreasesRecCallPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 5: error — decreases expression calls function in same mutual block
---------------------------------------------------------------------

def decreasesMutualCallPgm : Program :=
#strata
program Core;

rec function size (n : int) : int
  decreases n
{
  if n <= 0 then 0 else 1 + size(n - 1)
}
function bad (n : int) : int
  decreases size(n)
{
  if n <= 0 then 0 else bad(n - 1)
};
#end

/-- error: termination checking 'bad': decreasing argument contains a recursive call -/
#guard_msgs in
#eval Strata.Core.verify decreasesMutualCallPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 6: error — mutual block mixes structural and int-valued measures
---------------------------------------------------------------------

def mixedMutualPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}
function countdown (n : int) : int
  decreases n
{
  if n <= 0 then 0 else countdown(n - 1)
};
#end

/-- error: mutual recursive block mixes structural and int-valued termination measures; all functions in a mutual block must use the same kind of measure -/
#guard_msgs in
#eval Strata.Core.verify mixedMutualPgm (options := .quiet)

end Strata.RecursiveFunctionErrorTest

end
