/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchors:
- `verus-examples:proposal-rw2022`, `rw2022_script`, `recursion`
- `vlir-tests:LoopSimpleWithSpec`

Loop-level `decreases` is actively verified (forwarded to Core's while-loop
measure field). Function-level `decreases` is verified by #1092 via `adtRank`
structural recursion. Procedure-level `decreases` is parsed (as `Option Measure`
on `boole_procedure`, reusing Core's `Measure` category) and emits a `dbg_trace`
warning when present; termination is not yet verified.

Int-based termination (#1167) is implemented; the `fib` seed below is active.
-/

private def decreasesMetadataSeed : Strata.Program :=
#strata
program Boole;

procedure loop_measure_seed(n: int) returns (i: int)
spec {
  requires 0 <= n;
  ensures i == n;
}
{
  i := 0;
  while (i < n)
    decreases n - i
    invariant 0 <= i
    invariant i <= n
  {
    i := i + 1;
  }
};
#end

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
Result: ✅ pass

Obligation: loop_measure_seed_ensures_1_870
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" decreasesMetadataSeed (options:=.quiet)

example : Strata.smtVCsCorrectBoole decreasesMetadataSeed := by
  gen_smt_vcs_boole
  all_goals (try grind)

-- Procedure-level `decreases` is parsed (via `Option Measure` on `boole_procedure`)
-- and silently dropped; termination is not verified.
-- `clamp` is non-recursive; no `decreases` clause needed.
private def decreasesFunctionSeed : Strata.Program :=
#strata
program Boole;

function clamp(n: int) : int
{
  if n < 0 then 0 else n
}

procedure decreases_proc_seed(n: int) returns (r: int)
decreases n
spec {
  requires 0 <= n;
  ensures r == n;
}
{
  r := clamp(n);
};
#end

/-- info:
Obligation: decreases_proc_seed_ensures_1_2160
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" decreasesFunctionSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole decreasesFunctionSeed := by
  gen_smt_vcs_boole
  all_goals (try grind)

private def fibSeed : Strata.Program :=
#strata
program Boole;

rec function fib(n: int) : int
  decreases n
{
  if n <= 1 then n else fib(n - 1) + fib(n - 2)
}
;
#end

/-- info:
Obligation: fib_terminates_0
Property: assert
Result: ✅ pass

Obligation: fib_terminates_1
Property: assert
Result: ✅ pass

Obligation: fib_terminates_2
Property: assert
Result: ✅ pass

Obligation: fib_terminates_3
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" fibSeed (options := .quiet)

-- `decreases` clause in a `for v := init to limit` loop.
private def decreasesForLoopSeed : Strata.Program :=
#strata
program Boole;

procedure for_decreases_seed(n: int) returns (s: int)
spec {
  requires 0 <= n;
  ensures s == n;
}
{
  s := 0;
  for i : int := 0 to n - 1
  decreases n - i
  invariant 0 <= i && i <= n
  invariant s == i
  {
    s := s + 1;
  }
};
#end

/-- info:
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
Result: ✅ pass

Obligation: for_decreases_seed_ensures_1_3229
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" decreasesForLoopSeed (options := .quiet)

-- Regression: a loop whose `decreases` measure does not actually decrease
-- must fail the `measure_decrease` VC.
private def decreasesNonDecreasing : Strata.Program :=
#strata
program Boole;

procedure non_decreasing_seed(n: int) returns (i: int)
spec {
  requires 0 <= n;
}
{
  i := n;
  while (0 < i)
    decreases 0
    invariant 0 <= i
  {
    i := i - 1;
  }
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ❓ unknown-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" decreasesNonDecreasing (options := .quiet)
