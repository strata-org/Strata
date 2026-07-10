/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.EvalContext
import all Strata.DL.Imperative.EvalContext

namespace Imperative

public section

variable {P : PureExpr}

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
