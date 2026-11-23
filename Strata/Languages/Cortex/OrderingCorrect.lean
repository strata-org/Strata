/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.LangDef
public import Strata.Languages.Cortex.Ordering
public import Strata.Transform.Specification
import all Strata.Languages.Cortex.Ordering

/-! # Correctness of `Ordering`

`Ordering.order` turns an unordered Cortex program into an ordered one: type declarations
first, then the procedures in their order. It requires the composites, constrained types,
globals and global initialization to be lowered already. The relation reads a program only
through its context (`Program.ctx`), and the context of the ordered program is the
context of the unordered one, so both programs have the same event-trace language.

## Key theorems

- `Ordering.order_ctx`: the ordered program has the context of the unordered one.
- `Ordering.order_overapproximates`: `Ordering` trace-overapproximates its input, up to
  equal traces and equal environments.
-/

namespace Cortex.Ordering

open Imperative Strata.Logic Imperative.Specification.Transform Cortex.Sem

public section

/-- The program that `order` produces has the context of its input: the same procedures,
in the same order, and no composites and no globals. -/
theorem order_ctx {p : UnorderedProgram} {q : OrderedProgram} (h : order p = .ok q) :
    (Program.ordered q).ctx = (Program.unordered p).ctx := by
  simp only [order, bind, Except.bind, pure, Except.pure] at h
  iterate 4 split at h <;> try cases h
  have hnone : ∀ {α : Type} (l : List α), l.filterMap (fun _ => (none : Option Procedure)) = [] :=
    fun l => List.filterMap_eq_nil_iff.2 fun _ _ => rfl
  simp only [Program.ctx, OrderedProgram.procedures, List.filterMap_append, List.filterMap_map,
    Function.comp_def, hnone, List.nil_append, List.filterMap_some]
  simp_all

/-- `Ordering` trace-overapproximates its input: from equal entries and equal initial
environments, every finite run, terminal run and exiting run of the unordered program has
a run of the ordered program with the same trace and the same final environment, and the
initial environment is well formed for the ordered program. -/
theorem order_overapproximates {p : UnorderedProgram} {q : OrderedProgram}
    (h : order p = .ok q) (params : Core.Logic.InitEnvWFParams) :
    OverapproximatesTracesUptoWhen (· = ·) (· = ·) (· = ·)
      (EventLang.cortex (.unordered p)) (EventLang.cortex (.ordered q)) some (fun _ => True)
      params params := by
  intro st st' hT _ ρ₀ ρ₀' hρ hwf
  cases hT
  cases hρ
  simp only [EventLang.cortex, EventLang.traceStar, order_ctx h] at hwf ⊢
  exact ⟨fun cfg tr h => ⟨cfg, tr, h, rfl⟩, fun ρ' tr h => ⟨ρ', tr, h, rfl, rfl⟩,
    fun _ ρ' tr h => ⟨ρ', tr, h, rfl, rfl⟩, hwf⟩

end -- public section

end Cortex.Ordering
