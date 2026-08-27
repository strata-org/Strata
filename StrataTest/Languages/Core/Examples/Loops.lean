/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.Transform.StructuredToUnstructured
import Lean.Parser.Types
import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.Options
import StrataDDM.AST
import Strata.DL.Imperative.BasicBlock
import Strata.Languages.Core.Statement
import Strata.Languages.Core.Expressions
import StrataDDM.Integration.Lean.HashCommands
import Strata.Languages.Core.StatementSemantics
import Strata.MetaVerifier

open StrataDDM (Program)
namespace Strata

def singleCFG (p : Program) (n : Nat) : Imperative.CFG String
    (Imperative.DetBlock String Core.Command Core.Expression) :=
  let corePgm : Core.Program := TransM.run Inhabited.default (translateProgram p) |>.fst
  let proc := match corePgm.decls[n]? with
              | .some (.proc p _) => p | _ => Inhabited.default
  match proc.body with
  | .structured ss => Imperative.stmtsToCFG ss
  | .cfg cfg => cfg

---------------------------------------------------------------------

def measureFailExamplePgm :=
#strata
program Core;

procedure countUp(n : int, out i : int)
spec {
  requires (int.ge(n, 0));
  ensures (i == n);
}
{
  i := 0;
  while (int.lt(i, n))
    decreases n // WRONG
    invariant int.le(0, i)
    invariant int.le(i, n)
  {
    i := int.add(i, 1);
  }
};
#end

/--
info: Entry: before_loop$_7

before_loop$_7:
  i := 0;
  condGoto true loop_entry$_1 loop_entry$_1
loop_entry$_1:
  assert [inv$_5]: int.le(0, i);
  assert [inv$_6]: int.le(i, n);
  var loop_measure$_2 : int;
  assume [assume_loop_measure$_2]: loop_measure$_2 == n;
  assert [measure_lb_loop_measure$_2]: !(int.lt(loop_measure$_2, 0));
  condGoto int.lt(i, n) l$_4 end$_0
l$_4:
  i := int.add(i, 1);
  condGoto true measure_decrease$_3 measure_decrease$_3
measure_decrease$_3:
  assert [measure_decrease_loop_measure$_2]: int.lt(n, loop_measure$_2);
  condGoto true loop_entry$_1 loop_entry$_1
end$_0:
  finish
-/
#guard_msgs in
#eval (Std.format (singleCFG measureFailExamplePgm 0))

/--
info:
Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_lb_loop_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_decrease_loop_0
Property: assert
Result: ❓ unknown

Obligation: countUp_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify measureFailExamplePgm (options := .quiet)

---------------------------------------------------------------------

def gaussPgm :=
#strata
program Core;

procedure sum(n : int, out s : int)
spec {
  requires (int.ge(n, 0));
  ensures (s == int.safeDiv(int.mul(n, int.add(n, 1)), 2));
}
{
  var i : int;
  i := 0;
  s := 0;
  while (int.lt(i, n))
    decreases int.sub(n, i)
    invariant int.le(0, i)
    invariant int.le(i, n)
    invariant s == int.safeDiv(int.mul(i, int.add(i, 1)), 2)
  {
    i := int.add(i, 1);
    s := int.add(s, i);
  }
};
#end

/--
info: Entry: before_loop$_8

before_loop$_8:
  var i : int;
  i := 0;
  s := 0;
  condGoto true loop_entry$_1 loop_entry$_1
loop_entry$_1:
  assert [inv$_5]: int.le(0, i);
  assert [inv$_6]: int.le(i, n);
  assert [inv$_7]: s == int.safeDiv(int.mul(i, int.add(i, 1)), 2);
  var loop_measure$_2 : int;
  assume [assume_loop_measure$_2]: loop_measure$_2 == int.sub(n, i);
  assert [measure_lb_loop_measure$_2]: !(int.lt(loop_measure$_2, 0));
  condGoto int.lt(i, n) l$_4 end$_0
l$_4:
  i := int.add(i, 1);
  s := int.add(s, i);
  condGoto true measure_decrease$_3 measure_decrease$_3
measure_decrease$_3:
  assert [measure_decrease_loop_measure$_2]: int.lt(int.sub(n, i), loop_measure$_2);
  condGoto true loop_entry$_1 loop_entry$_1
end$_0:
  finish
-/
#guard_msgs in
#eval (Std.format (singleCFG gaussPgm 0))

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: sum_post_sum_ensures_1_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
sum_requires_0: int.ge(n@1, 0)
Obligation:
true

Label: loop_invariant_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
sum_requires_0: int.ge(n@2, 0)
Obligation:
true

Label: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Assumptions:
sum_requires_0: int.ge(n@2, 0)
Obligation:
true

Label: insertLoopInvAssert_entry_invariant_loop_0_1
Property: assert
Assumptions:
sum_requires_0: int.ge(n@2, 0)
Obligation:
int.le(0, n@2)

Label: insertLoopInvAssert_entry_invariant_loop_0_2
Property: assert
Assumptions:
sum_requires_0: int.ge(n@2, 0)
Obligation:
true

Label: insertLoopInvAssert_measure_lb_loop_0
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@2)
loopElimAssume_guard_loop_1: int.lt(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_0: int.le(0, i@1)
insertLoopInvAssume_invariant_loop_0_1: int.le(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_2: s@3 == int.safeDiv(int.mul(i@1, int.add(i@1, 1)), 2)
insertLoopInvAssume_measure_loop_0: $__loop_measure_loop_0 == int.sub(n@2, i@1)
sum_requires_0: int.ge(n@2, 0)
insertLoopInvAssume_entry_invariant_loop_0_1: int.le(0, n@2)
Obligation:
!(int.lt($__loop_measure_loop_0, 0))

Label: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@2)
loopElimAssume_guard_loop_1: int.lt(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_0: int.le(0, i@1)
insertLoopInvAssume_invariant_loop_0_1: int.le(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_2: s@3 == int.safeDiv(int.mul(i@1, int.add(i@1, 1)), 2)
insertLoopInvAssume_measure_loop_0: $__loop_measure_loop_0 == int.sub(n@2, i@1)
sum_requires_0: int.ge(n@2, 0)
insertLoopInvAssume_entry_invariant_loop_0_1: int.le(0, n@2)
Obligation:
int.le(0, int.add(i@1, 1))

Label: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@2)
loopElimAssume_guard_loop_1: int.lt(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_0: int.le(0, i@1)
insertLoopInvAssume_invariant_loop_0_1: int.le(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_2: s@3 == int.safeDiv(int.mul(i@1, int.add(i@1, 1)), 2)
insertLoopInvAssume_measure_loop_0: $__loop_measure_loop_0 == int.sub(n@2, i@1)
sum_requires_0: int.ge(n@2, 0)
insertLoopInvAssume_entry_invariant_loop_0_1: int.le(0, n@2)
Obligation:
int.le(int.add(i@1, 1), n@2)

Label: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_2
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@2)
loopElimAssume_guard_loop_1: int.lt(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_0: int.le(0, i@1)
insertLoopInvAssume_invariant_loop_0_1: int.le(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_2: s@3 == int.safeDiv(int.mul(i@1, int.add(i@1, 1)), 2)
insertLoopInvAssume_measure_loop_0: $__loop_measure_loop_0 == int.sub(n@2, i@1)
sum_requires_0: int.ge(n@2, 0)
insertLoopInvAssume_entry_invariant_loop_0_1: int.le(0, n@2)
Obligation:
int.add(s@3, int.add(i@1, 1)) == int.safeDiv(int.mul(int.add(i@1, 1), int.add(int.add(i@1, 1), 1)), 2)

Label: insertLoopInvAssert_measure_decrease_loop_0
Property: assert
Assumptions:
<label_ite_cond_true: int.lt(i, n)>: int.lt(0, n@2)
loopElimAssume_guard_loop_1: int.lt(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_0: int.le(0, i@1)
insertLoopInvAssume_invariant_loop_0_1: int.le(i@1, n@2)
insertLoopInvAssume_invariant_loop_0_2: s@3 == int.safeDiv(int.mul(i@1, int.add(i@1, 1)), 2)
insertLoopInvAssume_measure_loop_0: $__loop_measure_loop_0 == int.sub(n@2, i@1)
sum_requires_0: int.ge(n@2, 0)
insertLoopInvAssume_entry_invariant_loop_0_1: int.le(0, n@2)
Obligation:
int.lt(int.sub(n@2, int.add(i@1, 1)), $__loop_measure_loop_0)

Label: sum_ensures_1
Property: assert
Assumptions:
sum_requires_0: int.ge(n@2, 0)
insertLoopInvAssume_entry_invariant_loop_0_1: int.le(0, n@2)
<label_ite_cond_true: int.lt(i, n)>: if int.lt(0, n@2) then int.lt(0, n@2) else true
loopElimAssume_guard_loop_1: if int.lt(0, n@2) then int.lt(i@1, n@2) else true
insertLoopInvAssume_invariant_loop_0_0: if int.lt(0, n@2) then int.le(0, i@1) else true
insertLoopInvAssume_invariant_loop_0_1: if int.lt(0, n@2) then int.le(i@1, n@2) else true
insertLoopInvAssume_invariant_loop_0_2: if int.lt(0, n@2) then s@3 == int.safeDiv(int.mul(i@1, int.add(i@1, 1)), 2) else true
insertLoopInvAssume_measure_loop_0: if int.lt(0, n@2) then $__loop_measure_loop_0 == int.sub(n@2, i@1) else true
loopElimAssume_not_guard_loop_1: if int.lt(0, n@2) then !(int.lt(i@2, n@2)) else true
<label_ite_cond_false: !(int.lt(i, n))>: if if int.lt(0, n@2) then false else true then if int.lt(0, n@2) then false else true else true
insertLoopInvAssume_exit_invariant_loop_0_0: int.le(0, if int.lt(0, n@2) then i@2 else 0)
insertLoopInvAssume_exit_invariant_loop_0_1: int.le(if int.lt(0, n@2) then i@2 else 0, n@2)
insertLoopInvAssume_exit_invariant_loop_0_2: (if int.lt(0, n@2) then s@4 else 0) == int.safeDiv(int.mul(if int.lt(0, n@2) then i@2 else 0, int.add(if int.lt(0, n@2) then i@2 else 0, 1)), 2)
insertLoopInvAssume_exit_not_guard_loop_0: !(int.lt(if int.lt(0, n@2) then i@2 else 0, n@2))
Obligation:
(if int.lt(0, n@2) then s@4 else 0) == int.safeDiv(int.mul(n@2, int.add(n@2, 1)), 2)

---
info:
Obligation: sum_post_sum_ensures_1_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: loop_invariant_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_lb_loop_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_decrease_loop_0
Property: assert
Result: ✅ pass

Obligation: sum_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify gaussPgm

theorem gaussPgm_correct : smtVCsCorrect gaussPgm := by
  gen_smt_vcs
  all_goals (try grind)

---------------------------------------------------------------------

def nestedPgm :=
#strata
program Core;

const top : int;
axiom [top100]: top == 100;

procedure nested(n : int, out s : int)
spec {
  requires [n_pos]: int.gt(n, 0);
  requires [n_lt_top]: int.lt(n, top);
} {
  var x: int;
  var y: int;
  x := 0;
  while (int.lt(x, n))
    decreases int.sub(n, x)
    invariant int.ge(x, 0)
    invariant int.le(x, n)
    invariant int.lt(n, top)
  {
    y := 0;
    while (int.lt(y, x))
      decreases int.sub(x, y)
      invariant int.ge(y, 0)
      invariant int.le(y, x)
    {
      y := int.add(y, 1);
    }
    x := int.add(x, 1);
  }
};
#end

/--
info: Entry: before_loop$_15

before_loop$_15:
  var x : int;
  var y : int;
  x := 0;
  condGoto true loop_entry$_1 loop_entry$_1
loop_entry$_1:
  assert [inv$_12]: int.ge(x, 0);
  assert [inv$_13]: int.le(x, n);
  assert [inv$_14]: int.lt(n, top);

-- Errors encountered during conversion:
Unsupported construct in handleZeroaryOps: unknown operation, rendering as generic call: top
Context: Global scope:
  freeVars: [n]
  var loop_measure$_2 : int;
  assume [assume_loop_measure$_2]: loop_measure$_2 == int.sub(n, x);
  assert [measure_lb_loop_measure$_2]: !(int.lt(loop_measure$_2, 0));
  condGoto int.lt(x, n) before_loop$_11 end$_0
before_loop$_11:
  y := 0;
  condGoto true loop_entry$_5 loop_entry$_5
loop_entry$_5:
  assert [inv$_9]: int.ge(y, 0);
  assert [inv$_10]: int.le(y, x);
  var loop_measure$_6 : int;
  assume [assume_loop_measure$_6]: loop_measure$_6 == int.sub(x, y);
  assert [measure_lb_loop_measure$_6]: !(int.lt(loop_measure$_6, 0));
  condGoto int.lt(y, x) l$_8 l$_4
l$_8:
  y := int.add(y, 1);
  condGoto true measure_decrease$_7 measure_decrease$_7
measure_decrease$_7:
  assert [measure_decrease_loop_measure$_6]: int.lt(int.sub(x, y), loop_measure$_6);
  condGoto true loop_entry$_5 loop_entry$_5
l$_4:
  x := int.add(x, 1);
  condGoto true measure_decrease$_3 measure_decrease$_3
measure_decrease$_3:
  assert [measure_decrease_loop_measure$_2]: int.lt(int.sub(n, x), loop_measure$_2);
  condGoto true loop_entry$_1 loop_entry$_1
end$_0:
  finish
-/
#guard_msgs in
#eval (Std.format (singleCFG nestedPgm 2))

/--
info:
Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_lb_loop_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_1_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_1_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_lb_loop_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_decrease_loop_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_2
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_decrease_loop_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify nestedPgm (options := .quiet)

theorem nestedPgm_correct : smtVCsCorrect nestedPgm := by
  gen_smt_vcs
  all_goals (try grind)

---------------------------------------------------------------------

-- A loop where the `decreases` clause uses integer division `i / d`.
-- Division maps to `Int.SafeDiv`, so a precondition check (d != 0) must be
-- discharged for the measure expression.  The procedure precondition `d > 0`
-- covers it.  The measure itself is non-negative (from `i >= 0`) and
-- decreases by 1 each iteration (integer division by d drops when i drops by d).
def precondElimInMeasurePgm :=
#strata
program Core;

procedure countdownByD(n : int, d : int, out i : int)
spec {
  requires (int.ge(n, 0));
  requires (int.gt(d, 0));
  ensures (int.ge(i, 0));
  ensures (int.lt(i, d));
}
{
  i := n;
  while (int.ge(i, d))
    decreases int.safeDiv(i, d)
    invariant int.ge(i, 0)
  {
    i := int.sub(i, d);
  }
};
#end

/--
info:
Obligation: loop_measure_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_lb_loop_0
Property: assert
Result: ✅ pass

Obligation: loop_measure_end_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_decrease_loop_0
Property: assert
Result: ✅ pass

Obligation: countdownByD_ensures_2
Property: assert
Result: ✅ pass

Obligation: countdownByD_ensures_3
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify precondElimInMeasurePgm (options := .quiet)

/--
This theorem requires a little bit of manual work to handle facts about
division, though most goals are solved by `grind`.
-/
theorem precondElimInMeasurePgm_correct : smtVCsCorrect precondElimInMeasurePgm := by
  gen_smt_vcs
  all_goals (try grind)
  -- insertLoopInvAssert_measure_lb_loop_0: the loop measure i / d is non-negative
  case insertLoopInvAssert_measure_lb_loop_0 =>
    intro _ d i _ _ dpos _ _ _ inonneg meas_def
    subst meas_def
    have p := Int.ediv_nonneg (a := i) (b := d)
    grind
  -- insertLoopInvAssert_measure_decrease_loop_0: the loop measure i / d strictly decreases
  case insertLoopInvAssert_measure_decrease_loop_0 =>
    intro _ d i _ _ dpos _ _ _ _ meas_def
    subst meas_def
    have p := Int.add_mul_ediv_left (a := i) (b := d) (c := -1)
    grind

-- Now, we show the precondition (d > 0) is necessary for the measure-related
-- checks.
def precondElimInMeasureBadPgm :=
#strata
program Core;
procedure countdownByDBad(n : int, d : int, out i : int)
spec {
  requires (int.ge(n, 0));
  // requires (d > 0); NEED THIS
  ensures (int.ge(i, 0));
  ensures (int.lt(i, d));
}
{
  i := n;
  while (int.ge(i, d))
    decreases int.safeDiv(i, d)
    invariant int.ge(i, 0)
  {
    i := int.sub(i, d);
  }
};
#end


/--
info:
Obligation: loop_measure_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_lb_loop_0
Property: assert
Result: ❓ unknown

Obligation: loop_measure_end_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❓ unknown

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_decrease_loop_0
Property: assert
Result: ❓ unknown

Obligation: countdownByDBad_ensures_1
Property: assert
Result: ✅ pass

Obligation: countdownByDBad_ensures_2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify precondElimInMeasureBadPgm (options := .quiet)

---------------------------------------------------------------------

-- This example shows why `loop_measure_end` is necessary even when
-- `loop_measure` passes.  The precondition `d > 0` guarantees `k > 0`
-- at loop entry, so `loop_measure_calls_Int.SafeDiv_0` passes.  But
-- the body decrements `k`, which can reach 0 on the second iteration,
-- causing `loop_measure_end_calls_Int.SafeDiv_0` (and `insertLoopInvAssert_measure_lb_loop_0`,
-- `insertLoopInvAssert_measure_decrease_loop_0`) to fail.
def precondElimMeasureBodyMutatesPgm :=
#strata
program Core;

procedure countdownMutateD(n : int, d : int, out i : int)
spec {
  requires (int.ge(n, 0));
  requires (int.gt(d, 0));
  ensures (int.ge(i, 0));
}
{
  var k : int;
  i := n;
  k := d;
  while (int.ge(i, 1))
    decreases int.safeDiv(i, k)
    invariant int.ge(i, 0)
  {
    k := int.sub(k, 1);   // mutates the divisor; may reach 0 after first iteration
    i := int.sub(i, 1);
  }
};
#end

/--
info:
Obligation: loop_measure_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_lb_loop_0
Property: assert
Result: ❓ unknown

Obligation: loop_measure_end_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❓ unknown

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_measure_decrease_loop_0
Property: assert
Result: ❓ unknown

Obligation: countdownMutateD_ensures_2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify precondElimMeasureBodyMutatesPgm (options := .quiet)

end Strata
