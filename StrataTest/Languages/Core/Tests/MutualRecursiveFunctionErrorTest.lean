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
# Mutual Recursive Function Error Tests

Tests that invalid mutual recursive function declarations are rejected
with appropriate error messages.
-/

namespace Strata.MutualRecursiveFunctionErrorTest

---------------------------------------------------------------------
-- Test 1: a used, non-terminating polymorphic mutual recursion fails its
-- termination check
--
-- `len`/`lenHelper` are polymorphic and mutually recursive with an int-valued
-- `decreases n` measure, but each recurses at `n + 1`, so the measure does not
-- decrease.  Procedure `Q` uses `len` at a ground type, so the block is
-- monomorphized and the termination procedures (specialized from the
-- polymorphic originals) reach the solver: the non-negativity checks
-- (`*_terminates_0`) pass but the decrease checks (`*_terminates_1`) FAIL.
---------------------------------------------------------------------

def polyMutualPgm : Program :=
#strata
program Core;

rec function len<a>(x : a, n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else int.add(1, lenHelper(x, int.add(n, 1)))
}
function lenHelper<a>(x : a, n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else int.add(1, len(x, int.add(n, 1)))
};

procedure Q(out r : int)
spec {
  ensures true;
}
{
  r := len(5, 3);
};

#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram polyMutualPgm) |>.snd |>.isEmpty

/--
info:
Obligation: len_terminates_0
Property: assert
Result: ✅ pass

Obligation: len_terminates_1
Property: assert
Result: ❌ fail

Obligation: lenHelper_terminates_0
Property: assert
Result: ✅ pass

Obligation: lenHelper_terminates_1
Property: assert
Result: ❌ fail

Obligation: Q_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyMutualPgm (options := .quiet)

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
error: recursive function 'isEven': structural recursion requires @[cases]
-/
#guard_msgs in
#eval Core.verify noCasesMutualPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 3: a used, non-terminating polymorphic recursive function fails its
-- termination check (single-function companion to Test 1)
--
-- `loopy<a>` declares `decreases n` but recurses at `n + 1`, so the measure
-- does not decrease.  Termination checking runs before monomorphization and
-- emits a polymorphic `$$term` procedure (specialized at a fresh opaque type
-- for `a`), so the non-decrease is caught: `loopy_terminates_1` FAILS.
---------------------------------------------------------------------

def nonTermPolyPgm : Program :=
#strata
program Core;

rec function loopy<a>(x : a, n : int) : int
  decreases n
{
  if int.le(n, 0) then 0 else loopy(x, int.add(n, 1))
};

procedure P(out r : int)
spec {
  ensures true;
}
{
  r := loopy(5, 3);
};

#end

/--
info:
Obligation: loopy_terminates_0
Property: assert
Result: ✅ pass

Obligation: loopy_terminates_1
Property: assert
Result: ❌ fail

Obligation: P_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify nonTermPolyPgm (options := .quiet)

end Strata.MutualRecursiveFunctionErrorTest

end
