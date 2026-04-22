/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.Languages.Core.Verifier

/-!
# Proofs about `SMT.Result.merge`

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
  unfold Core.SMT.Result.merge
  cases a <;> cases b <;> rfl
