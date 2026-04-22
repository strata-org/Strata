/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.Languages.Core.Verifier
import Strata.Transform.StructuredToUnstructured

namespace Strata

def singleCFG (p : Program) (n : Nat) : Imperative.CFG String
    (Imperative.DetBlock String Core.Command Core.Expression) :=
  let corePgm : Core.Program := TransM.run Inhabited.default (translateProgram p) |>.fst
  let proc := match corePgm.decls[n]? with
              | .some (.proc p _) => p | _ => Inhabited.default
  Imperative.stmtsToCFG proc.body

---------------------------------------------------------------------

def measureFailExamplePgm :=
#strata
program Core;

procedure countUp(n : int, out i : int)
spec {
  requires (n >= 0);
  ensures (i == n);
}
{
  i := 0;
  while (i < n)
    decreases n // WRONG
    invariant 0 <= i
    invariant i <= n
  {
    i := (i + 1);
  }
};
#end

/--
info: Entry: before_loop$_7

before_loop$_7:
  i := 0;
  condGoto true loop_entry$_1 loop_entry$_1
loop_entry$_1:
  assert [inv$_5]: 0 <= i;
  assert [inv$_6]: i <= n;
  var loop_measure$_2 : int;
  assume [assume_loop_measure$_2]: loop_measure$_2 == n;
  assert [measure_lb_loop_measure$_2]: !(loop_measure$_2 < 0);
  condGoto i < n l$_4 end$_0
l$_4:
  i := i + 1;
  condGoto true measure_decrease$_3 measure_decrease$_3
measure_decrease$_3:
  assert [measure_decrease_loop_measure$_2]: n < loop_measure$_2;
  condGoto true loop_entry$_1 loop_entry$_1
end$_0:
  finish
-/
#guard_msgs in
#eval (Std.format (singleCFG measureFailExamplePgm 0))

/--
info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ❓ unknown

Obligation: countUp_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify measureFailExamplePgm (options := .quiet)

---------------------------------------------------------------------

def gaussPgm :=
#strata
program Core;

procedure sum(n : int, out s : int)
spec {
  requires (n >= 0);
  ensures (s == ((n * (n + 1)) / 2));
}
{
  var i : int;
  i := 0;
  s := 0;
  while (i < n)
    decreases n - i
    invariant 0 <= i
    invariant i <= n
    invariant s == (i * (i + 1)) / 2
  {
    i := (i + 1);
    s := (s + i);
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
  assert [inv$_5]: 0 <= i;
  assert [inv$_6]: i <= n;
  assert [inv$_7]: s == i * (i + 1) / 2;
  var loop_measure$_2 : int;
  assume [assume_loop_measure$_2]: loop_measure$_2 == n - i;
  assert [measure_lb_loop_measure$_2]: !(loop_measure$_2 < 0);
  condGoto i < n l$_4 end$_0
l$_4:
  i := i + 1;
  s := s + i;
  condGoto true measure_decrease$_3 measure_decrease$_3
measure_decrease$_3:
  assert [measure_decrease_loop_measure$_2]: n - i < loop_measure$_2;
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
sum_requires_0: n@1 >= 0
Obligation:
true

Label: loop_invariant_calls_Int.SafeDiv_0
Property: division by zero check
Assumptions:
sum_requires_0: n@2 >= 0
Obligation:
true

Label: entry_invariant_0_0
Property: assert
Assumptions:
sum_requires_0: n@2 >= 0
Obligation:
true

Label: entry_invariant_0_1
Property: assert
Assumptions:
sum_requires_0: n@2 >= 0
Obligation:
0 <= n@2

Label: entry_invariant_0_2
Property: assert
Assumptions:
sum_requires_0: n@2 >= 0
Obligation:
true

Label: measure_lb_0
Property: assert
Assumptions:
<label_ite_cond_true: i < n>: 0 < n@2
assume_guard_0: i@1 < n@2
assume_invariant_0_0: 0 <= i@1
assume_invariant_0_1: i@1 <= n@2
assume_invariant_0_2: s@3 == i@1 * (i@1 + 1) / 2
assume_measure_0: $__loop_measure_0 == n@2 - i@1
sum_requires_0: n@2 >= 0
assume_entry_invariant_0_1: 0 <= n@2
Obligation:
!($__loop_measure_0 < 0)

Label: arbitrary_iter_maintain_invariant_0_0
Property: assert
Assumptions:
<label_ite_cond_true: i < n>: 0 < n@2
assume_guard_0: i@1 < n@2
assume_invariant_0_0: 0 <= i@1
assume_invariant_0_1: i@1 <= n@2
assume_invariant_0_2: s@3 == i@1 * (i@1 + 1) / 2
assume_measure_0: $__loop_measure_0 == n@2 - i@1
sum_requires_0: n@2 >= 0
assume_entry_invariant_0_1: 0 <= n@2
Obligation:
0 <= i@1 + 1

Label: arbitrary_iter_maintain_invariant_0_1
Property: assert
Assumptions:
<label_ite_cond_true: i < n>: 0 < n@2
assume_guard_0: i@1 < n@2
assume_invariant_0_0: 0 <= i@1
assume_invariant_0_1: i@1 <= n@2
assume_invariant_0_2: s@3 == i@1 * (i@1 + 1) / 2
assume_measure_0: $__loop_measure_0 == n@2 - i@1
sum_requires_0: n@2 >= 0
assume_entry_invariant_0_1: 0 <= n@2
Obligation:
i@1 + 1 <= n@2

Label: arbitrary_iter_maintain_invariant_0_2
Property: assert
Assumptions:
<label_ite_cond_true: i < n>: 0 < n@2
assume_guard_0: i@1 < n@2
assume_invariant_0_0: 0 <= i@1
assume_invariant_0_1: i@1 <= n@2
assume_invariant_0_2: s@3 == i@1 * (i@1 + 1) / 2
assume_measure_0: $__loop_measure_0 == n@2 - i@1
sum_requires_0: n@2 >= 0
assume_entry_invariant_0_1: 0 <= n@2
Obligation:
s@3 + (i@1 + 1) == (i@1 + 1) * (i@1 + 1 + 1) / 2

Label: measure_decrease_0
Property: assert
Assumptions:
<label_ite_cond_true: i < n>: 0 < n@2
assume_guard_0: i@1 < n@2
assume_invariant_0_0: 0 <= i@1
assume_invariant_0_1: i@1 <= n@2
assume_invariant_0_2: s@3 == i@1 * (i@1 + 1) / 2
assume_measure_0: $__loop_measure_0 == n@2 - i@1
sum_requires_0: n@2 >= 0
assume_entry_invariant_0_1: 0 <= n@2
Obligation:
n@2 - (i@1 + 1) < $__loop_measure_0

Label: sum_ensures_1
Property: assert
Assumptions:
sum_requires_0: n@2 >= 0
assume_entry_invariant_0_1: 0 <= n@2
<label_ite_cond_true: i < n>: if 0 < n@2 then 0 < n@2 else true
assume_guard_0: if 0 < n@2 then i@1 < n@2 else true
assume_invariant_0_0: if 0 < n@2 then 0 <= i@1 else true
assume_invariant_0_1: if 0 < n@2 then i@1 <= n@2 else true
assume_invariant_0_2: if 0 < n@2 then s@3 == i@1 * (i@1 + 1) / 2 else true
assume_measure_0: if 0 < n@2 then $__loop_measure_0 == n@2 - i@1 else true
not_guard_0: if 0 < n@2 then !(i@2 < n@2) else true
invariant_0_0: if 0 < n@2 then 0 <= i@2 else true
invariant_0_1: if 0 < n@2 then i@2 <= n@2 else true
invariant_0_2: if 0 < n@2 then s@4 == i@2 * (i@2 + 1) / 2 else true
<label_ite_cond_false: !(i < n)>: if if 0 < n@2 then false else true then if 0 < n@2 then false else true else true
Obligation:
if 0 < n@2 then s@4 else 0 == n@2 * (n@2 + 1) / 2

---
info:
Obligation: sum_post_sum_ensures_1_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: loop_invariant_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ✅ pass

Obligation: sum_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify gaussPgm

---------------------------------------------------------------------

def nestedPgm :=
#strata
program Core;

const top : int;
axiom [top100]: top == 100;

procedure nested(n : int, out s : int)
spec {
  requires [n_pos]: n > 0;
  requires [n_lt_top]: n < top;
} {
  var x: int;
  var y: int;
  x := 0;
  while (x < n)
    decreases (n - x)
    invariant x >= 0
    invariant x <= n
    invariant n < top
  {
    y := 0;
    while (y < x)
      decreases (x - y)
      invariant y >= 0
      invariant y <= x
    {
      y := y + 1;
    }
    x := x + 1;
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
  assert [inv$_12]: x >= 0;
  assert [inv$_13]: x <= n;
  assert [inv$_14]: n < re.none();

-- Errors encountered during conversion:
Unsupported construct in lopToExpr: 0-ary op not found: top
Context: Global scope:
  var loop_measure$_2 : int;
  assume [assume_loop_measure$_2]: loop_measure$_2 == n - x;
  assert [measure_lb_loop_measure$_2]: !(loop_measure$_2 < 0);
  condGoto x < n before_loop$_11 end$_0
before_loop$_11:
  y := 0;
  condGoto true loop_entry$_5 loop_entry$_5
loop_entry$_5:
  assert [inv$_9]: y >= 0;
  assert [inv$_10]: y <= x;
  var loop_measure$_6 : int;
  assume [assume_loop_measure$_6]: loop_measure$_6 == x - y;
  assert [measure_lb_loop_measure$_6]: !(loop_measure$_6 < 0);
  condGoto y < x l$_8 l$_4
l$_8:
  y := y + 1;
  condGoto true measure_decrease$_7 measure_decrease$_7
measure_decrease$_7:
  assert [measure_decrease_loop_measure$_6]: x - y < loop_measure$_6;
  condGoto true loop_entry$_5 loop_entry$_5
l$_4:
  x := x + 1;
  condGoto true measure_decrease$_3 measure_decrease$_3
measure_decrease$_3:
  assert [measure_decrease_loop_measure$_2]: n - x < loop_measure$_2;
  condGoto true loop_entry$_1 loop_entry$_1
end$_0:
  finish
-/
#guard_msgs in
#eval (Std.format (singleCFG nestedPgm 2))

/--
info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: measure_lb_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: measure_decrease_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify nestedPgm (options := .quiet)

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
  requires (n >= 0);
  requires (d > 0);
  ensures (i >= 0);
  ensures (i < d);
}
{
  i := n;
  while (i >= d)
    decreases i / d
    invariant i >= 0
  {
    i := (i - d);
  }
};
#end

/--
info:
Obligation: loop_measure_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: loop_measure_end_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
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
#eval verify precondElimInMeasurePgm (options := .quiet)

-- Now, we show the precondition (d > 0) is necessary for the measure-related
-- checks.
def precondElimInMeasureBadPgm :=
#strata
program Core;
procedure countdownByDBad(n : int, d : int, out i : int)
spec {
  requires (n >= 0);
  // requires (d > 0); NEED THIS
  ensures (i >= 0);
  ensures (i < d);
}
{
  i := n;
  while (i >= d)
    decreases i / d
    invariant i >= 0
  {
    i := (i - d);
  }
};
#end


/--
info:
Obligation: loop_measure_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ❓ unknown

Obligation: loop_measure_end_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❓ unknown

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
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
#eval verify precondElimInMeasureBadPgm (options := .quiet)

---------------------------------------------------------------------

-- This example shows why `loop_measure_end` is necessary even when
-- `loop_measure` passes.  The precondition `d > 0` guarantees `k > 0`
-- at loop entry, so `loop_measure_calls_Int.SafeDiv_0` passes.  But
-- the body decrements `k`, which can reach 0 on the second iteration,
-- causing `loop_measure_end_calls_Int.SafeDiv_0` (and `measure_lb_0`,
-- `measure_decrease_0`) to fail.
def precondElimMeasureBodyMutatesPgm :=
#strata
program Core;

procedure countdownMutateD(n : int, d : int, out i : int)
spec {
  requires (n >= 0);
  requires (d > 0);
  ensures (i >= 0);
}
{
  var k : int;
  i := n;
  k := d;
  while (i >= 1)
    decreases i / k
    invariant i >= 0
  {
    k := (k - 1);   // mutates the divisor; may reach 0 after first iteration
    i := (i - 1);
  }
};
#end

/--
info:
Obligation: loop_measure_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ❓ unknown

Obligation: loop_measure_end_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❓ unknown

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ❓ unknown

Obligation: countdownMutateD_ensures_2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify precondElimMeasureBodyMutatesPgm (options := .quiet)
