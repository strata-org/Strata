/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/- Import an ordinary Strata module rather than the linter directly.
The flexible linter becomes active transitively via `Strata.Init`
(every leaf module `public import`s it) rather than from a direct linter import.-/
import Strata.DL.Util.Counter

/-! Tests for the flexible linter and its `simp only [...]` suggestions. The suggestions come
from re-running the original call, so they keep its lemmas and its location. -/

set_option linter.strata.flexible true

namespace Strata.Linter.FlexibleTest

/-- Not a `simp` lemma, so `simp` cannot see through it but `exact` can. -/
def opaqueId (n : Nat) : Nat := n

-- The suggestion keeps the user-supplied lemma `h`.
/--
error: `simp [h]` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [h, Nat.add_zero]
---
info: `exact hb`
modifies the current goal, which was modified by the flexible tactic `simp` on line 37.
-/
#guard_msgs in
example (f : Nat → Nat) (a b : Nat) (h : a = b) (hb : f (b + 0) = 3) : f (a + 0) = 3 := by
  simp [h]
  exact hb

-- The suggestion keeps the `at h` location.
/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at h
---
info: `exact h`
uses `h`, which was modified by the flexible tactic `simp` on line 54.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h : p (a + 0)) : p a := by
  simp at h
  exact h

-- `simp_all` gets a `simp_all only [...]` suggestion.
/--
error: `simp_all` is a flexible tactic modifying `⊢`. Try `simp_all?` and use the suggested `simp_all only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp_all only [Nat.add_zero]
---
info: `exact hb`
modifies the current goal, which was modified by the flexible tactic `simp_all` on line 72.
-/
#guard_msgs in
example (f : Nat → Nat) (a b : Nat) (h : a = b) (hb : f (opaqueId b) = 3) :
    f (a + 0) = 3 := by
  simp_all
  exact hb

-- `simp only` is not flexible, so nothing is reported.
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h : p (a + 0)) : p a := by
  simp only [Nat.add_zero] at h
  exact h

/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only at h
---
info: `exact h`
uses `h`, which was modified by the flexible tactic `simp` on line 94.
-/
#guard_msgs in
example (h : 0 = 0) : True := by
  simp at h
  exact h

#guard_msgs in
example (x : Int) (h : x + 0 > 0) : 0 < x := by
  simp at h
  omega -- omega is treated as flexible

-- Regression: `induction` reverts hypotheses mentioning the target into the proof term for
-- structural reasons. Since `usesGoal? induction = false`, this must NOT be reported as the
-- `induction` "using" the stained `h`. `h` is reverted by `induction n` and the subgoals are
-- closed by `omega` (flexible), so the whole proof produces no flexible-linter diagnostic.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  induction n with
  | zero => omega
  | succ k _ => omega

-- Companion: `cases` is likewise exempt (`usesGoal? cases = false`) and must stay silent.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  cases n with
  | zero => omega
  | succ k => omega

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

-- Regression: `fun_induction` reverts `h` like `induction` does, so it must stay silent.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : fib n ≥ 0 := by
  simp at h
  fun_induction fib n with
  | case1 => omega
  | case2 => omega
  | case3 k ih1 ih2 => omega

-- Regression: `fun_cases` reverts `h` like `cases` does, so it must stay silent.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : isZero n = false := by
  simp at h
  fun_cases isZero n with
  | case1 => omega
  | case2 k => rfl

-- The exemption only skips the proof-term check: `cases h` on the stained `h` itself names
-- it in its syntax, so it is still reported.
/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [and_true] at h
---
info: `cases h with
| intro hp hq => exact hq`
uses `h`, which was modified by the flexible tactic `simp` on line 163.
-/
#guard_msgs in
example (p q : Prop) (h : p ∧ q ∧ True) : q := by
  simp at h
  cases h with
  | intro hp hq => exact hq

-- Regression: `simp at *` stains the goal and every hypothesis, so `exact h` matches more than
-- one stained location. The warning, the `Try this` suggestion and the info note must each be
-- emitted exactly ONCE (not once per matched stain); otherwise `warningAsError` turns the
-- duplicates into separate build errors.
/--
error: `simp at *` is a flexible tactic that potentially modifies all hypotheses and the current goal with a wildcard `*`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at *
---
info: `exact h`
uses a rigid tactic. Previously, the flexible tactic `simp`, which potentially modified all hypotheses and the goal with a wildcard `*`, was used on line 184.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h : p (a + 0)) : p (a + 0) := by
  simp at *
  exact h

/-! ## Tests ported from Mathlib's flexible linter suite

These exercise follower tactics, goal-exempt tactics (`usesGoal? = false`), stain tracking
across locations and the proof-term check. Adapted to Strata: the `Strata.Linter` namespace,
no Mathlib dependency, and Strata's single (deduplicated) wildcard message where Mathlib emits
one per matched location. -/

section mathlib_ports
set_option linter.unusedVariables false

def portN : Nat := 1
def portM : Nat := 1

-- Two consecutive flexible tactics are fine.
#guard_msgs in
example : portN = portM := by
  simp [portN]
  simp [portM]

-- A `try`-wrapped rigid tactic is still flagged.
/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at h
---
info: `exact h`
uses `h`, which was modified by the flexible tactic `simp` on line
-/
#guard_msgs (substring := true) in
example (h : 0 + 0 = 0) : True := by
  simp at h
  try exact h

-- `simp_all` then a rigid tactic that re-closes the modified goal.
/--
error: `simp_all` is a flexible tactic modifying `⊢`. Try `simp_all?` and use the suggested `simp_all only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp_all only [Nat.add_zero]
---
info: `exact Nat.le_succ_of_le h`
modifies the current goal, which was modified by the flexible tactic `simp_all` on line
-/
#guard_msgs (substring := true) in
example {a b : Nat} (h : a ≤ b) : a + 0 ≤ b + 1 := by
  simp_all
  exact Nat.le_succ_of_le h

-- `subst` does not use the goal (`usesGoal? = false`): no diagnostic.
#guard_msgs in
example {a b : Nat} (h : a = b) : a + 0 = b := by
  simp
  subst h
  rfl

-- `by_cases` does not use the goal: no diagnostic.
#guard_msgs in
example {a b : Nat} (h : a = b) : a + 0 = b := by
  simp
  by_cases a = b
  subst h; rfl
  subst h; rfl

-- `specialize` does not touch the target by default: no diagnostic.
#guard_msgs in
example {a b : Nat} (h : ∀ c, c + a + b = a + c) : (0 + 2 + 1 + a + b) = a + 3 := by
  simp
  specialize h 3
  simp_all

-- `done` is an allowed follower.
#guard_msgs in
example (h : False) : 0 ≠ 0 := by
  try (simp; done)
  exact h.elim

-- `ac_rfl` is an allowed follower.
#guard_msgs in
example {a b c d : Nat} (h : False) (h' : d = a) : a + (b + c) = (b + d) + c := by
  simp [h']
  ac_rfl

-- `grind` is a flexible follower.
#guard_msgs in
example {x y : Nat} : 0 + x + (y + x) = x + x + y := by
  simp
  grind

-- `grobner` front-end is a flexible follower.
#guard_msgs in
example {x y : Nat} : 0 + x + (y + x) = x + x + y := by
  simp
  grobner

-- `lia` front-end is a flexible follower.
#guard_msgs in
example {x y : Nat} : 0 + x + (y + x) = x + x + y := by
  simp
  lia

-- `all_goals` combinator wrapping a `lia` follower.
#guard_msgs in
example {a : Nat} : a + 1 + 0 = 1 + a := by simp; all_goals lia

-- `congr` is allowed after `simp` but "passes along the stain" to its subgoal.
/--
error: `simp` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero]
---
info: `exact h.symm`
modifies the current goal, which was modified by the flexible tactic `simp` on line
-/
#guard_msgs (substring := true) in
example {a b : Nat} (h : a = b) : a + b + 0 = b + a := by
  simp
  congr
  exact h.symm

-- Stained locations are forgotten once the corresponding goal is closed, so the later
-- `cases`/`exact` in a fresh branch must not be flagged.
#guard_msgs in
example (n : Nat) : n + 1 = 1 + n := by
  by_cases 0 = 0
  · simp_all
    lia
  · have : 0 ≠ 1 := by
      intro h
      cases h
    exact Nat.add_comm ..

-- `simp at h` stains `h` only: the `rw` on the goal above is not flagged, the `rw ... at h`
-- below is. Exercises location-scoped stain tracking.
/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only at h
---
info: `rw [← Classical.not_not (a := True)] at h`
uses `h`, which was modified by the flexible tactic `simp` on line 341.
-/
#guard_msgs (substring := true) in
example {h : 0 = 0} : True := by
  simp at h
  rw [<- Classical.not_not (a := True)]
  rw [<- Classical.not_not (a := True)] at h
  assumption

/-! ## Regression: wrapper tactics around an allowed follower (Heimdall false positives)

After `simp`, an allowed follower such as `omega` produces no diagnostic (see the bare `omega`
test above). Wrapping that same follower in a combinator that merely delegates to it (`next`,
`(..)`, `focus`, `first`, `exact by`, `case`) must behave identically — the wrapper does not
itself act on a stained location, it only runs the tactic(s) nested inside it, which the linter
visits on their own turn.

These wrappers are listed as continuators in `stoppers` (and `exact by` is handled by
`delegatesGoalViaBy`, which stops the outer `exact` from counting the goal its `by` block
discharges). The cases below are split into two groups: after `simp at h` (the wrapper never
names `h`) and after a goal-modifying `simp` (the wrapper is reached on the stained goal)
All must stay SILENT; under `warningAsError` any stray warning
would become a build error for every file that opts into the linter. -/

-- Control: a bullet-scoped allowed follower is already silent (matches the bare `omega` test).
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  · omega

-- `next => omega`: wrapper delegating to an allowed follower.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  next => omega

-- `(omega)`: parenthesised follower.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  (omega)

-- `focus omega`: focusing combinator around a follower.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  focus omega

-- `first | omega | rfl`: alternation whose taken branch is a follower.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  first | omega | rfl

-- `exact by omega`: a `by` block whose tactic is a follower.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  exact by omega

-- tactic-mode `match`: reverts `h` into the proof term like `cases`/`induction`; must be exempt.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 := by
  simp at h
  match n with
  | 0 => omega
  | k + 1 => omega

-- `case <tag> => omega`: case-selecting wrapper around a follower on each goal.
#guard_msgs in
example (n : Nat) (h : n + 0 = 5) : n = 5 ∧ True := by
  simp at h
  constructor
  case left => omega
  case right => trivial

/-! ### Wrappers after a goal-modifying `simp`

The tests above only wrap a follower after `simp at h`, where the wrapper never names `h`, so the
goal-stain path is never exercised. Here `simp` modifies `⊢`, so the stained location is the goal
the wrappers run on. Each must stay SILENT, with `simp; · omega` as the control. -/

-- Control: a bullet-scoped follower after a goal-modifying `simp` is silent.
#guard_msgs in
example (n : Nat) (h : n = 5) : n + 0 = 5 := by simp; · omega

#guard_msgs in
example (n : Nat) (h : n = 5) : n + 0 = 5 := by simp; next => omega

#guard_msgs in
example (n : Nat) (h : n = 5) : n + 0 = 5 := by simp; (omega)

#guard_msgs in
example (n : Nat) (h : n = 5) : n + 0 = 5 := by simp; focus omega

#guard_msgs in
example (n : Nat) (h : n = 5) : n + 0 = 5 := by simp; first | omega | rfl

#guard_msgs in
example (n : Nat) (h : n = 5) : n + 0 = 5 := by simp; exact by omega

/-! ### Only a *direct* `by` argument delegates the goal

`exact by omega` discharges the goal through a `by` block supplied as its direct argument, so the
`exact` must stay silent (the inner `omega` is linted on its own). But a `by` buried deeper inside
a larger term does NOT delegate: in `exact (by … ) ▸ h` the `▸ h` still genuinely uses the goal,
so the `exact` must fire. Exempting it (matching a `by` anywhere in the syntax) is a missed lint. -/

-- Nested `by` inside a `▸` rewrite term: the outer `exact` still uses the goal, so it must FIRE.
/--
error: `simp` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero]
---
info: `exact (by exact hab : a = b) ▸ h`
modifies the current goal, which was modified by the flexible tactic `simp` on line 459.
-/
#guard_msgs in
example (a b : Nat) (p : Nat → Prop) (h : p b) (hab : a = b) : p (a + 0) := by
  simp
  exact (by exact hab : a = b) ▸ h

/-! ### One warning per flexible tactic across stained locations

`simp at h ⊢` stains both `h` and the goal, so the later `exact h` matches two stained locations.
The warning and its `Try this:` render only from the two tactics' ranges, so they are emitted once
(else `warningAsError` raises duplicate errors for one `simp at h ⊢`); the warning lists every
stained location in source order (`h`, `⊢`). The per-rigid-tactic info line still names each
distinct location: one "uses `h`", one "modifies the current goal". -/
/--
error: `simp at h ⊢` is a flexible tactic modifying `h`, `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at h ⊢
---
info: `exact h`
modifies the current goal, which was modified by the flexible tactic `simp` on line 485.
---
info: `exact h`
uses `h`, which was modified by the flexible tactic `simp` on line 485.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h : p (a + 0)) : p (a + 0) := by
  simp at h ⊢
  exact h

/-! ### Warning lists stained locations in source order

The warning names every stained location a later rigid tactic uses, in the order written in the
`at` clause (`h₂ h₁ ⊢`), not in the order the rigid tactic happens to reach them. -/
/--
error: `simp at h₂ h₁ ⊢` is a flexible tactic modifying `h₂`, `h₁`, `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at h₂ h₁ ⊢
---
info: `exact h₂ h₁`
modifies the current goal, which was modified by the flexible tactic `simp` on line 512.
---
info: `exact h₂ h₁`
uses `h₂`, which was modified by the flexible tactic `simp` on line 512.
---
info: `exact h₂ h₁`
uses `h₁`, which was modified by the flexible tactic `simp` on line 512.
-/
#guard_msgs in
example (a : Nat) (p q : Nat → Prop) (h₁ : p (a + 0)) (h₂ : p (a + 0) → q (a + 0)) :
    q (a + 0) := by
  simp at h₂ h₁ ⊢
  exact h₂ h₁

/-! ### Backtracking re-runs `simp` under each run's own context

`branch a or b then t` runs `a; t` and backtracks, then runs `b; t`. Both runs of the same `simp`
act on the very same goal `MVarId`, but with `?c` assigned differently (`true`, then `false`), so
they use different lemmas (`cond_true` vs `cond_false`). The suggestion must re-run `simp` once
per run, not once per goal, or it drops `cond_false` and breaks the second branch. -/
/-- Commit `a`, run `t`, then fail and backtrack; commit `b` and run `t` again on the same goal. -/
macro "branch " a:tactic " or " b:tactic " then " t:tactic : tactic =>
  `(tactic| first | ($a; $t; fail) | ($b; $t))

/--
error: `simp` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero, Nat.zero_add, cond_eq_ite, ↓reduceIte, Bool.false_eq_true]
---
info: `assumption`
modifies the current goal, which was modified by the flexible tactic `simp` on line 540.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (_h₁ : p (a + 1)) (h₂ : p a) :
    ∃ c : Bool, p (cond c (a + 1 + 0) (0 + a)) := by
  refine ⟨?c, ?_⟩
  branch (case c => exact true) or (case c => exact false) then (simp; assumption)

/-! ### Multi-goal `simp` suggestion unions lemmas across goals

`all_goals simp` records one `simp` entry per goal, all sharing the same syntax range. The
`simp only [...]` suggestion must union the lemmas used on every goal — here `Nat.add_zero` (for
`p (a + 0)`) and `Nat.zero_add` (for `p (0 + a)`) — otherwise applying the suggestion breaks the
second goal with "`simp` made no progress". -/
/--
error: `simp` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero, Nat.zero_add]
---
info: `exact h1`
modifies the current goal, which was modified by the flexible tactic `simp` on line 562.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h1 : p a) : p (a + 0) ∧ p (0 + a) := by
  constructor
  all_goals simp
  all_goals exact h1

/-! ### `exact by …` only delegates when the inner block starts with an allowed follower

`delegatesGoalViaBy` exempts the outer `exact`/`refine` only when its direct `by` block *begins*
with a `flexible`/`stopper` tactic (the kind the stain may flow into, as in `exact by omega`).
When the `by` block starts with a rigid tactic — `exact by exact hb` — the inner `exact` runs on
a fresh, unstained goal and the outer tactic still closes the stained one, so exempting it is a
missed lint (the exact flexible→rigid pattern the linter exists to catch). It must FIRE. -/
/--
error: `simp` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero]
---
info: `exact by exact hb`
modifies the current goal, which was modified by the flexible tactic `simp` on line 585.
-/
#guard_msgs in
example (f : Nat → Nat) (a : Nat) (hb : f a = 3) : f (a + 0) = 3 := by
  simp
  exact by exact hb

/-! ### Multi-goal suggestion survives goals created at different times

When one flexible `simp` range is reached on goals created by *different* earlier tactics (here
each `constructor` under `all_goals` makes a fresh goal), those goals live in different
metavariable contexts. The suggestion must re-run `simp` for each goal under *its own* context —
re-running every goal under the first stain's context throws on the later goal and drops the whole
`Try this:`. The warning must still carry a suggestion. -/
/--
error: `simp` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero]
---
info: `exact h1`
modifies the current goal, which was modified by the flexible tactic `simp` on line 610.
-/
#guard_msgs in
example (p : Nat → Prop) (a : Nat) (h1 : p a) :
    (p (a + 0) ∧ True) ∧ (p (a + 0) ∧ True) := by
  constructor
  all_goals (constructor; simp)
  all_goals first | exact h1 | trivial

end mathlib_ports

/-! ### Rigid tactics inside wrappers still fire

The wrappers `next`, `(…)`, `focus`, `first` and `case` are `stoppers`: the linter skips the
wrapper node itself and lints the tactics nested inside it. These are the firing counterparts of
the silent wrapper tests above: a rigid `exact h` inside the wrapper must still be reported. -/

/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at h
---
info: `exact h`
uses `h`, which was modified by the flexible tactic `simp` on line 634.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h : p (a + 0)) : p a := by
  simp at h
  next => exact h

/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at h
---
info: `exact h`
uses `h`, which was modified by the flexible tactic `simp` on line 650.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h : p (a + 0)) : p a := by
  simp at h
  (exact h)

/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at h
---
info: `exact h`
uses `h`, which was modified by the flexible tactic `simp` on line 666.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h : p (a + 0)) : p a := by
  simp at h
  focus exact h

/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at h
---
info: `exact h`
uses `h`, which was modified by the flexible tactic `simp` on line 682.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h : p (a + 0)) : p a := by
  simp at h
  first | exact h

/--
error: `simp at h` is a flexible tactic modifying `h`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero] at h
---
info: `exact h`
uses `h`, which was modified by the flexible tactic `simp` on line 698.
-/
#guard_msgs in
example (a : Nat) (p : Nat → Prop) (h : p (a + 0)) : p a ∧ True := by
  simp at h
  constructor
  case left => exact h
  case right => trivial

/--
error: `simp` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero]
---
info: `exact hb`
modifies the current goal, which was modified by the flexible tactic `simp` on line 716.
-/
#guard_msgs in
example (f : Nat → Nat) (a : Nat) (hb : f a = 3) : f (a + 0) = 3 := by
  simp
  next => exact hb

/-! ### No merged suggestion when branches name different local hypotheses

`simp [*]` uses `e1` in the first branch and `e2` in the second. A single `simp only [...]` cannot
name both (`e1` is unknown in the second branch, and dropping `e2` leaves `P c` unrewritten), so
the warning stays but no `Try this:` is offered. -/
def P (n : Nat) : Prop := n = n
theorem Pa (a : Nat) : P a := rfl

/--
error: `simp [*]` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: `exact Pa a`
modifies the current goal, which was modified by the flexible tactic `simp` on line 738.
-/
#guard_msgs in
example (a b c : Nat) : (b = a → P (b + 0)) ∧ (c = a → P (0 + c)) := by
  refine ⟨fun e1 => ?_, fun e2 => ?_⟩
  all_goals (simp [*]; exact Pa a)

/-! ### Merged suggestion kept when branches share a hypothesis name

Same as above, but both hypotheses are called `e`: the call reads `simp only [..., e]` in every
branch, and each branch resolves `e` to its own hypothesis, so the suggestion is still offered. -/
/--
error: `simp [*]` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero, Nat.zero_add, e]
---
info: `exact Pa a`
modifies the current goal, which was modified by the flexible tactic `simp` on line 758.
-/
#guard_msgs in
example (a b c : Nat) : (b = a → P (b + 0)) ∧ (c = a → P (0 + c)) := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  all_goals (simp [*]; exact Pa a)

/-! ### No merged suggestion when a local shadows a used global lemma in one branch

`simp` uses the global `flexQ_eq` in both branches, but in the second branch a local hypothesis is
also called `flexQ_eq`. There `simp only [flexQ_eq]` would pick the local and fail with "`simp`
made no progress", so the call built in that branch names the lemma differently from the first;
no single text is right for both, so no `Try this:` is offered. -/
section
def FlexQ (n : Nat) : Nat := n
theorem flexQ_eq (n : Nat) : FlexQ n = n := rfl
attribute [local simp] flexQ_eq

/--
error: `simp` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.strata.flexible false`
---
info: `exact ha`
modifies the current goal, which was modified by the flexible tactic `simp` on line 783.
-/
#guard_msgs in
set_option linter.unusedVariables false in
example (a : Nat) (p : Nat → Prop) (ha : p a) : (True → p (FlexQ a)) ∧ (True → p (FlexQ a)) := by
  refine ⟨fun _ => ?_, fun flexQ_eq => ?_⟩
  all_goals (simp; exact ha)
end

end Strata.Linter.FlexibleTest
