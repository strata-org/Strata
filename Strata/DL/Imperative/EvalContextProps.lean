/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.EvalContext
import all Strata.DL.Imperative.EvalContext
import Strata.Util.DecidableEqProps

/-!
## Properties of path-condition contexts

Key results:

- `PathConditionEntry.fastEq_eq` / `PathConditionEntry.fastEq_rfl` — the
  pointer-accelerated `fastEq` decides structural equality: a `true` result
  is a proof of equality, and every entry compares equal to itself.
- `RevPathConditions.consume_prepend` / `consume_addInNewest` /
  `consume_push` / `consume_pop` / `consume_newest` — `consume` commutes
  with each `RevPathConditions` operation, relating the reversed-scope
  representation to plain `PathConditions`.
-/

namespace Imperative

public section

variable {P : PureExpr}

/-- When `fastEq` returns `true`, the result is a proof of equality. -/
theorem PathConditionEntry.fastEq_eq
    [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr]
    {a b : PathConditionEntry P}
    (h : a.fastEq b = true) : a = b := by
  cases a <;> cases b <;>
    simp only [PathConditionEntry.fastEq, Bool.and_eq_true, Bool.false_eq_true] at h
  case assumption.assumption =>
    obtain ⟨h1, h2⟩ := h
    rw [ptrFastEq_eq h1, ptrFastEq_eq h2]
  case varDecl.varDecl =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [ptrFastEq_eq h1, ptrFastEq_eq h2, ptrFastEq_eq h3]
  case distinct.distinct =>
    obtain ⟨h1, h2⟩ := h
    rw [ptrFastEq_eq h1, ptrFastEq_eq h2]

/-- Every path-condition entry compares equal to itself. -/
theorem PathConditionEntry.fastEq_rfl
    [DecidableEq P.Ident] [DecidableEq P.Ty] [DecidableEq P.Expr]
    (a : PathConditionEntry P) : a.fastEq a = true := by
  cases a <;>
    simp only [PathConditionEntry.fastEq, ptrFastEq_self, Bool.and_self]

/-- Prepending an entry then consuming is the same as adding that entry to the
    consumed path conditions. -/
theorem RevPathConditions.consume_prepend (r : RevPathConditions P)
    (e : PathConditionEntry P) :
    (r.prepend e).consume = (r.consume).addEntry e := by
  obtain ⟨scopes⟩ := r
  cases scopes <;>
    simp [RevPathConditions.prepend, RevPathConditions.consume,
          PathConditions.addEntry, List.map_cons, List.reverse_cons]

/-- Adding a batch to the newest scope then consuming is the same as
    `addInNewest` on the consumed path conditions. -/
theorem RevPathConditions.consume_addInNewest (r : RevPathConditions P)
    (m : PathCondition P) :
    (r.addInNewest m).consume = (r.consume).addInNewest m := by
  obtain ⟨scopes⟩ := r
  cases scopes with
  | nil =>
    simp only [RevPathConditions.addInNewest, RevPathConditions.consume,
          PathConditions.addInNewest, PathConditions.newest,
          PathConditions.pop, PathConditions.push, List.map_cons,
          List.reverse_reverse, List.map_nil, List.nil_append]
  | cons q rest =>
      simp only [RevPathConditions.addInNewest, RevPathConditions.consume,
                 PathConditions.addInNewest, PathConditions.newest,
                 PathConditions.pop, PathConditions.push, List.map_cons]
      induction m generalizing q with
      | nil => simp only [List.foldl_nil, List.map_cons, List.append_nil]
      | cons e m' ih =>
        -- Peel one fold step.
        have hstep :
            List.foldl (·.prepend ·) (⟨q :: rest⟩ : RevPathConditions P) (e :: m')
              = List.foldl (·.prepend ·) ⟨(e :: q) :: rest⟩ m' := rfl
        rw [hstep, ih (e :: q)]
        -- At this point, both tails are List.map (·.reverse) rest,
        -- so we only need to prove that the heads are equal.
        congr 1
        -- ⊢ (e :: q).reverse ++ m' = q.reverse ++ (e :: m')
        simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem RevPathConditions.consume_push (r : RevPathConditions P) (p : PathCondition P) :
    (r.push p).consume = (r.consume).push p := by
  obtain ⟨scopes⟩ := r
  cases scopes <;>
  simp only [RevPathConditions.consume, RevPathConditions.push,
      PathConditions.push, List.map_cons, List.reverse_reverse, List.map_nil]

theorem RevPathConditions.consume_pop (r : RevPathConditions P) :
    (r.pop).consume = (r.consume).pop := by
  obtain ⟨scopes⟩ := r
  cases scopes <;>
  simp only [RevPathConditions.consume, RevPathConditions.pop,
      PathConditions.pop, List.map_cons, List.map_nil]

theorem RevPathConditions.consume_newest (r : RevPathConditions P) :
    r.newest = (r.consume).newest := by
  obtain ⟨scopes⟩ := r
  cases scopes <;>
  simp only [RevPathConditions.consume, RevPathConditions.newest,
      PathConditions.newest, List.map_cons, List.map_nil]

end -- public section

end Imperative
