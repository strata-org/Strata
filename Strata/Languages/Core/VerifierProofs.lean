/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.Languages.Core.Verifier

/-!
# Proofs about `SMT.Result.merge` and `evaluatorResults`

`SMT.Result.merge` computes the join (least upper bound) in the lattice:

    unsat ≤ unknown ≤ sat ≤ err

Since `Result` carries data (models, error messages), full commutativity does
not hold on the concrete `SMT.Result.merge` — `merge a b` may return a
different model than `merge b a`. We therefore introduce `ResultKind` to
abstract away the payload and prove properties at that level.

**Note:** `ResultKind.merge_comm` proves commutativity on the *abstracted*
`ResultKind.merge`, not on `SMT.Result.merge` itself. The concrete merge
function is intentionally non-commutative: when both operands are `sat` (or
both `err`, etc.), it keeps the payload from the *first* operand.

The key theorem `merge_kind` at the bottom of this file connects the two:

    (a.merge b).toKind = a.toKind.merge b.toKind

This establishes that `SMT.Result.merge` faithfully implements the lattice join
at the kind level — i.e., the *constructor tag* of the merged result is exactly
what `ResultKind.merge` predicts, even though the payloads may differ.

## Main results

- `ResultKind.merge_comm` — commutativity (on the abstraction only)
- `ResultKind.merge_assoc` — associativity
- `ResultKind.merge_idem` — idempotency
- `ResultKind.merge_eq_max` — merge computes the lattice join
- `ResultKind.le_merge_left` / `le_merge_right` — merge is an upper bound
- `ResultKind.merge_le` — merge is the *least* upper bound
- `merge_kind` — `(a.merge b).toKind = a.toKind.merge b.toKind`
- `Core.evaluatorResults_valid_sat` — when `evaluatorResults` reports a failure
- `Core.evaluatorResults_valid_sat_deductive` — the same, in `deductive` mode
- `Core.evaluatorResults_valid_sat_not_dead` — never on a known-dead path
- `Core.evaluatorResults_valid_unsat` — it reports a pass only for a goal that is literally `true`
-/

open Strata

/-- The "tag" of an SMT result, forgetting models and error messages. -/
inductive ResultKind where
  | unsat
  | unknown
  | sat
  | err
  deriving DecidableEq, Repr

/-- Project an `SMT.Result` to its kind. -/
def Core.SMT.Result.toKind (r : Core.SMT.Result) : ResultKind :=
  match r with
  | .unsat      => .unsat
  | .unknown .. => .unknown
  | .sat ..     => .sat
  | .err ..     => .err

/-- Merge on kinds: `err` dominates `sat` dominates `unknown` dominates `unsat`. -/
def ResultKind.merge (a b : ResultKind) : ResultKind :=
  match a, b with
  | .err, _    => .err
  | _, .err    => .err
  | .sat, _    => .sat
  | _, .sat    => .sat
  | .unknown, _ => .unknown
  | _, .unknown => .unknown
  | .unsat, .unsat => .unsat

-- -----------------------------------------------------------------------
-- Core algebraic properties
-- -----------------------------------------------------------------------

theorem ResultKind.merge_comm (a b : ResultKind) :
    a.merge b = b.merge a := by
  cases a <;> cases b <;> rfl

theorem ResultKind.merge_assoc (a b c : ResultKind) :
    (a.merge b).merge c = a.merge (b.merge c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem ResultKind.merge_idem (a : ResultKind) :
    a.merge a = a := by
  cases a <;> rfl

-- -----------------------------------------------------------------------
-- Lattice ordering: unsat ≤ unknown ≤ sat ≤ err
-- -----------------------------------------------------------------------

/-- Natural number encoding for the lattice ordering. -/
def ResultKind.rank : ResultKind → Nat
  | .unsat   => 0
  | .unknown => 1
  | .sat     => 2
  | .err     => 3

instance : LE ResultKind where
  le a b := a.rank ≤ b.rank

instance : DecidableRel (α := ResultKind) (· ≤ ·) :=
  fun a b => Nat.decLe a.rank b.rank

/-- `merge` computes the maximum (join) in the lattice. -/
theorem ResultKind.merge_eq_max (a b : ResultKind) :
    (a.merge b).rank = max a.rank b.rank := by
  cases a <;> cases b <;> rfl

theorem ResultKind.le_merge_left (a b : ResultKind) : a ≤ a.merge b := by
  show a.rank ≤ (a.merge b).rank
  rw [merge_eq_max]; exact Nat.le_max_left ..

theorem ResultKind.le_merge_right (a b : ResultKind) : b ≤ a.merge b := by
  show b.rank ≤ (a.merge b).rank
  rw [merge_eq_max]; exact Nat.le_max_right ..

theorem ResultKind.merge_le {a b c : ResultKind} (ha : a ≤ c) (hb : b ≤ c) :
    a.merge b ≤ c := by
  show (a.merge b).rank ≤ c.rank
  rw [merge_eq_max]; exact Nat.max_le.mpr ⟨ha, hb⟩

-- -----------------------------------------------------------------------
-- Connection to Core.SMT.Result.merge
-- -----------------------------------------------------------------------

/-- `Core.SMT.Result.merge` preserves kinds: the kind of the merged result
    equals the merge of the kinds. This links the executable `SMT.Result.merge`
    with the abstracted `ResultKind.merge`, so all lattice properties proved
    above transfer to the concrete function at the kind level. -/
theorem merge_kind (a b : Core.SMT.Result) :
    (a.merge b).toKind = a.toKind.merge b.toKind := by
  -- The unknown×unknown case requires a payload split on both Option fields
  -- since the new model-preserving branches pattern-match on Some/None.
  cases a <;> cases b <;> simp [Core.SMT.Result.merge, Core.SMT.Result.toKind, ResultKind.merge] <;>
    (try (rename_i m₁ m₂; cases m₁ <;> cases m₂ <;> rfl))

/-! ## When the evaluator reports an assertion failing

`evaluatorResults` decides validity without a solver, reporting it `sat` with an empty
model, only when the goal is literally `false` and the path condition is known to be
satisfiable. The theorems below pin which path conditions those are, so a change to the
shape check cannot quietly widen when the evaluator reports a failure. -/

namespace Core

/-- The evaluator reports validity as `sat` only for a requested validity check of a goal
that is literally `false`, under a path condition that only declares or defines variables or
that the premise of `deductiveAssumingSatisfiablePaths` takes to be satisfiable. -/
theorem evaluatorResults_valid_sat {obligation : Imperative.ProofObligation Expression}
    {checkMode : VerificationMode} {satisfiabilityCheck validityCheck : Bool}
    {m : Imperative.SMT.Model Expression.Ident}
    (h : (evaluatorResults obligation checkMode satisfiabilityCheck validityCheck).2 =
      some (.sat m)) :
    validityCheck = true ∧ obligation.obligation.isFalse = true ∧
      (pathConditionShape obligation = .onlyDefinitions ∨
        usesSatisfiablePathsPremise obligation checkMode (pathConditionShape obligation)) := by
  grind [evaluatorResults]

/-- The evaluator reports a validity check proved (`unsat`) only for a goal that is literally
`true`, in every check mode. So no mode's shortcut ever adds a pass. -/
theorem evaluatorResults_valid_unsat {obligation : Imperative.ProofObligation Expression}
    {checkMode : VerificationMode} {satisfiabilityCheck validityCheck : Bool}
    (h : (evaluatorResults obligation checkMode satisfiabilityCheck validityCheck).2 =
      some .unsat) :
    validityCheck = true ∧ obligation.obligation.isTrue = true := by
  grind [evaluatorResults]

/-- In `deductive` mode, the evaluator reports an assertion failing only when its path
condition only declares or defines variables. -/
theorem evaluatorResults_valid_sat_deductive {obligation : Imperative.ProofObligation Expression}
    {satisfiabilityCheck validityCheck : Bool} {m : Imperative.SMT.Model Expression.Ident}
    (h : (evaluatorResults obligation .deductive satisfiabilityCheck validityCheck).2 =
      some (.sat m)) :
    pathConditionShape obligation = .onlyDefinitions := by
  obtain ⟨-, -, h | h⟩ := evaluatorResults_valid_sat h
  · exact h
  · simp [usesSatisfiablePathsPremise] at h

/-- In any mode, the evaluator never reports an assertion failing on a path it knows is dead:
one with a literally `false` assumption. -/
theorem evaluatorResults_valid_sat_not_dead {obligation : Imperative.ProofObligation Expression}
    {checkMode : VerificationMode} {satisfiabilityCheck validityCheck : Bool}
    {m : Imperative.SMT.Model Expression.Ident}
    (h : (evaluatorResults obligation checkMode satisfiabilityCheck validityCheck).2 =
      some (.sat m)) :
    pathConditionShape obligation ≠ .hasFalseAssumption := by
  obtain ⟨-, -, h | h⟩ := evaluatorResults_valid_sat h
  · simp [h]
  · simp [usesSatisfiablePathsPremise] at h
    exact h.2

end Core
