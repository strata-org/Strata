/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Proofs about `SMT.Result.merge`

`SMT.Result.merge` computes the join (least upper bound) in the lattice:

    unsat ≤ unknown ≤ sat ≤ err

These proofs are stated directly on `SMT.Result.merge` using constructor
predicates (`isErr`, `isSat`, `isUnknown`, `isUnsat`).

## Main results

### Dominance / soundness
- `merge_isErr_left` / `merge_isErr_right` — `err` dominates everything
- `merge_isSat_left` / `merge_isSat_right` — `sat` dominates when no `err`
- `merge_isUnknown_of_left` / `merge_isUnknown_of_right` — `unknown` dominates
  when no `err`/`sat`
- `merge_isUnsat` — both `unsat` implies merged is `unsat`

### Algebraic properties
- `merge_idem` — idempotency: `a.merge a = a`
- `merge_assoc_isErr` / `merge_assoc_isSat` / `merge_assoc_isUnknown` /
  `merge_assoc_isUnsat` — associativity at the constructor level

### Identity element
- `merge_unsat_left` / `merge_unsat_right` — `unsat` is the identity
-/

open Strata

namespace Core.SMT.Result

/-- `r` is an error result. -/
def isErr (r : Core.SMT.Result) : Prop :=
  ∃ e, r = .err e

/-- `r` is a sat result. -/
def isSat (r : Core.SMT.Result) : Prop :=
  ∃ m, r = .sat m

/-- `r` is an unknown result. -/
def isUnknown (r : Core.SMT.Result) : Prop :=
  ∃ m, r = .unknown m

/-- `r` is unsat. -/
def isUnsat (r : Core.SMT.Result) : Prop :=
  r = .unsat

-- -----------------------------------------------------------------------
-- Dominance / soundness properties
-- -----------------------------------------------------------------------

/-- If `a` is an error, `a.merge b` is an error. -/
theorem merge_isErr_left (a b : Core.SMT.Result) (h : a.isErr) :
    (a.merge b).isErr := by
  obtain ⟨e, rfl⟩ := h; exact ⟨e, rfl⟩

/-- If `b` is an error, `a.merge b` is an error. -/
theorem merge_isErr_right (a b : Core.SMT.Result) (h : b.isErr) :
    (a.merge b).isErr := by
  obtain ⟨e, rfl⟩ := h; cases a <;> exact ⟨_, rfl⟩

/-- If `a` is sat and `b` is not an error, `a.merge b` is sat. -/
theorem merge_isSat_left (a b : Core.SMT.Result) (ha : a.isSat) (hb : ¬b.isErr) :
    (a.merge b).isSat := by
  obtain ⟨m, rfl⟩ := ha
  cases b with
  | err e => exact absurd ⟨e, rfl⟩ hb
  | _ => exact ⟨m, rfl⟩

/-- If `b` is sat and `a` is not an error, `a.merge b` is sat. -/
theorem merge_isSat_right (a b : Core.SMT.Result) (hb : b.isSat) (ha : ¬a.isErr) :
    (a.merge b).isSat := by
  obtain ⟨m, rfl⟩ := hb
  cases a with
  | err e => exact absurd ⟨e, rfl⟩ ha
  | sat m' => exact ⟨m', rfl⟩
  | _ => exact ⟨m, rfl⟩

/-- If `a` is unknown and `b` is neither error nor sat, `a.merge b` is unknown. -/
theorem merge_isUnknown_of_left (a b : Core.SMT.Result)
    (ha : a.isUnknown) (hbe : ¬b.isErr) (hbs : ¬b.isSat) :
    (a.merge b).isUnknown := by
  obtain ⟨m, rfl⟩ := ha
  cases b with
  | err e => exact absurd ⟨e, rfl⟩ hbe
  | sat m' => exact absurd ⟨m', rfl⟩ hbs
  | _ => exact ⟨m, rfl⟩

/-- If `b` is unknown and `a` is neither error nor sat, `a.merge b` is unknown. -/
theorem merge_isUnknown_of_right (a b : Core.SMT.Result)
    (hb : b.isUnknown) (hae : ¬a.isErr) (has : ¬a.isSat) :
    (a.merge b).isUnknown := by
  obtain ⟨m, rfl⟩ := hb
  cases a with
  | err e => exact absurd ⟨e, rfl⟩ hae
  | sat m' => exact absurd ⟨m', rfl⟩ has
  | unknown m' => exact ⟨m', rfl⟩
  | unsat => exact ⟨m, rfl⟩

/-- If both are unsat, the merged result is unsat. -/
theorem merge_isUnsat (a b : Core.SMT.Result) (ha : a.isUnsat) (hb : b.isUnsat) :
    (a.merge b).isUnsat := by
  subst ha; subst hb; rfl

-- -----------------------------------------------------------------------
-- Idempotency
-- -----------------------------------------------------------------------

/-- `merge` is idempotent: `a.merge a = a`. -/
theorem merge_idem (a : Core.SMT.Result) : a.merge a = a := by
  cases a <;> rfl

-- -----------------------------------------------------------------------
-- Associativity (at the constructor level)
-- -----------------------------------------------------------------------

/-- Associativity for `isErr`:
    `(a.merge b).merge c` is err iff `a.merge (b.merge c)` is err. -/
theorem merge_assoc_isErr (a b c : Core.SMT.Result) :
    ((a.merge b).merge c).isErr ↔ (a.merge (b.merge c)).isErr := by
  cases a <;> cases b <;> cases c <;> simp [merge, isErr]

/-- Associativity for `isSat`:
    `(a.merge b).merge c` is sat iff `a.merge (b.merge c)` is sat. -/
theorem merge_assoc_isSat (a b c : Core.SMT.Result) :
    ((a.merge b).merge c).isSat ↔ (a.merge (b.merge c)).isSat := by
  cases a <;> cases b <;> cases c <;> simp [merge, isSat]

/-- Associativity for `isUnknown`:
    `(a.merge b).merge c` is unknown iff `a.merge (b.merge c)` is unknown. -/
theorem merge_assoc_isUnknown (a b c : Core.SMT.Result) :
    ((a.merge b).merge c).isUnknown ↔ (a.merge (b.merge c)).isUnknown := by
  cases a <;> cases b <;> cases c <;> simp [merge, isUnknown]

/-- Associativity for `isUnsat`:
    `(a.merge b).merge c` is unsat iff `a.merge (b.merge c)` is unsat. -/
theorem merge_assoc_isUnsat (a b c : Core.SMT.Result) :
    ((a.merge b).merge c).isUnsat ↔ (a.merge (b.merge c)).isUnsat := by
  cases a <;> cases b <;> cases c <;> simp [merge, isUnsat]

-- -----------------------------------------------------------------------
-- Unsat is the identity element
-- -----------------------------------------------------------------------

/-- `unsat` is a left identity for `merge`. -/
theorem merge_unsat_left (b : Core.SMT.Result) :
    SMT.Result.merge .unsat b = b := by
  cases b <;> rfl

/-- `unsat` is a right identity for `merge`. -/
theorem merge_unsat_right (a : Core.SMT.Result) :
    a.merge .unsat = a := by
  cases a <;> rfl

end Core.SMT.Result
