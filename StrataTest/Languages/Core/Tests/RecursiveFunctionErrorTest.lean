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
-- Test 1: recursive function without @[cases] parameter is rejected
---------------------------------------------------------------------

def noCasesPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (xs : IntList) : int
decreases xs
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};

#end

/--
error: recursive function 'listLen': structural recursion requires @[cases]
-/
#guard_msgs in
#eval Core.verify noCasesPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 2: error — decreases on non-int expression
---------------------------------------------------------------------

def decreasesNonIntPgm : Program :=
#strata
program Core;

function f () : bool;

rec function bad (n : int) : int
  decreases f
{
  if int.le(n, 0) then 0 else bad(int.sub(n, 1))
};
#end

/-- error: ❌ Type checking error.
recursive function 'bad': non-variable decreases expression must have type int, got 'bool'. For structural recursion, use a parameter name-/
#guard_msgs in
#eval Core.verify decreasesNonIntPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 3: error — decreasing argument contains recursive call
---------------------------------------------------------------------

def decreasesRecCallPgm : Program :=
#strata
program Core;

rec function bad (n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else bad(bad(int.sub(n, 1)))
};
#end

/-- error: termination checking 'bad': decreasing argument contains a recursive call -/
#guard_msgs in
#eval Core.verify decreasesRecCallPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 4: error — decreases expression calls function in same mutual block
---------------------------------------------------------------------

def decreasesMutualCallPgm : Program :=
#strata
program Core;

rec function size (n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else int.add(1, size(int.sub(n, 1)))
}
function bad (n : int) : int
  decreases size(n)
{
  if int.le(n, 0) then 0 else bad(int.sub(n, 1))
};
#end

/-- error: termination checking 'bad': decreasing argument contains a recursive call -/
#guard_msgs in
#eval Core.verify decreasesMutualCallPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 5: error — mutual block mixes structural and int-valued measures
---------------------------------------------------------------------

def mixedMutualPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
}
function countdown (n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else countdown(int.sub(n, 1))
};
#end

/-- error: mutual recursive block mixes structural and int-valued termination measures; all functions in a mutual block must use the same kind of measure -/
#guard_msgs in
#eval Core.verify mixedMutualPgm (options := .quiet)

end Strata.RecursiveFunctionErrorTest

end
