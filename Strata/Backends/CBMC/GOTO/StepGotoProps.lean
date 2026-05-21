/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Semantics
public import Strata.DL.Util.Relations

public section

/-! # Properties of `StepGoto`

This module provides Phase-1.b/1.d infrastructure for the
GOTO-semantics-expansion plan
(`docs/superpowers/specs/2026-05-20-goto-semantics-expansion-design.md`):

* `DeterministicEvalGoto` / `DeterministicEvalGotoBool` — the standard
  determinism predicates for the parametric expression evaluators.
* `GotoConfig.shape` and `StepGoto_shape_deterministic` — two
  `StepGoto` derivations from the same running configuration produce
  the same shape (running-with-pc vs terminal). The constructor
  guards already pin the shape down without needing an external
  determinism hypothesis on the boolean evaluator: a guard cannot
  simultaneously evaluate to `some true` and `some false`. Used by
  downstream determinism arguments without committing to determinism
  on the existential-witness side (`InitState` / `UpdateState` /
  `RemoveState`).
* `StepGotoRange` — range-bounded reflexive-transitive closure of
  `StepGoto`. Mirrors the shape of `tautschnig/goto-semantics`'s
  `ExecRange`. Comes with `StepGotoRange_refl`, `StepGotoRange_trans`,
  `StepGotoRange_to_StepGotoStar`, and a single-step coercion.

Full determinism for state-changing instructions (`DECL`, `DEAD`,
`ASSIGN`, `ASSIGN`-nondet) is not provable on the current `StepGoto`
shape because the constructors take their state-update witnesses
(`x`, `v`, the abstract `InitState` / `UpdateState` / `RemoveState`
derivations) as existentials. Recovering full determinism requires
either (1) refactoring `StepGoto` so it pulls those witnesses from
the instruction code à la tautschnig's `StepInstr`, or (2) supplying
an external "the witness is uniquely determined by the instruction"
hypothesis at the call site. Both are out of scope for Phase 1.b. -/

namespace CProverGOTO

open Imperative

/-! ## Determinism predicates -/

/-- A deterministic GOTO expression evaluator: it agrees with itself on
the same store and expression. -/
@[expose] def DeterministicEvalGoto {P : PureExpr} (δ : SemanticEvalGoto P) : Prop :=
  ∀ σ e v₁ v₂, δ σ e = some v₁ → δ σ e = some v₂ → v₁ = v₂

/-- A deterministic GOTO boolean evaluator: it agrees with itself on
the same store and expression. -/
@[expose] def DeterministicEvalGotoBool {P : PureExpr} [HasBool P] [HasNot P]
    (δ : SemanticEvalGotoBool P) : Prop :=
  ∀ σ e b₁ b₂, δ σ e = some b₁ → δ σ e = some b₂ → b₁ = b₂

/-! ## Configuration shape -/

/-- The "shape" of a `GotoConfig`: `some pc` for `.running pc _ _` and
`none` for `.terminal _ _`. -/
@[expose] def GotoConfig.shape {P : PureExpr} : GotoConfig P → Option Nat
  | .running pc _ _ => some pc
  | .terminal _ _ => none

/-- Two `StepGoto` derivations from the same running configuration
produce successor configurations of the same shape: either both
`.running` with the same PC, or both `.terminal`.

The post-store and the new failed flag may still differ for
state-changing instructions, since the existential witnesses (`x`,
`v`, the abstract state-update derivations) are not pinned down by
the instruction alone. -/
theorem StepGoto_shape_deterministic
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {c₁ c₂ : GotoConfig P}
    (h₁ : StepGoto P δ_goto δ_goto_bool pgm (.running pc σ failed) c₁)
    (h₂ : StepGoto P δ_goto δ_goto_bool pgm (.running pc σ failed) c₂) :
    c₁.shape = c₂.shape := by
  cases h₁ <;> cases h₂ <;>
    simp_all [GotoConfig.shape, Program.instrAt]

/-! ## Range-bounded execution

`StepGotoRange pgm pc_end` is the reflexive-transitive closure of
`StepGoto pgm` restricted to running configurations whose PC stays
strictly below `pc_end`. Mirrors `tautschnig/goto-semantics`'s
`ExecRange` and serves the same purpose: stating "this slice of the
program executes" without committing to a specific terminal
configuration. -/

/-- Range-bounded reflexive-transitive closure of `StepGoto`.

`StepGotoRange P δ δ_bool pgm pc_end c c'` means there is a chain of
`StepGoto` steps from `c` to `c'` such that every intermediate
running configuration's PC is strictly below `pc_end`. The chain may
end at a configuration whose PC has reached `pc_end` (one step beyond
the range) or at a `.terminal`. -/
inductive StepGotoRange
    (P : PureExpr) [HasBool P] [HasNot P]
    (δ_goto : SemanticEvalGoto P)
    (δ_goto_bool : SemanticEvalGotoBool P)
    (pgm : Program) (pc_end : Nat) :
    GotoConfig P → GotoConfig P → Prop where
  /-- Empty range: no steps. -/
  | refl : StepGotoRange P δ_goto δ_goto_bool pgm pc_end c c
  /-- Extend by a single step whose source PC is below `pc_end`. -/
  | step
      (pc : Nat) (h_lt : pc < pc_end)
      (σ : SemanticStore P) (failed : Bool)
      (h_step : StepGoto P δ_goto δ_goto_bool pgm
                  (.running pc σ failed) c_mid) :
      StepGotoRange P δ_goto δ_goto_bool pgm pc_end c_mid c' →
      StepGotoRange P δ_goto δ_goto_bool pgm pc_end (.running pc σ failed) c'

/-- Transitivity of `StepGotoRange`. -/
theorem StepGotoRange_trans
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc_end : Nat}
    {c₁ c₂ c₃ : GotoConfig P} :
    StepGotoRange P δ_goto δ_goto_bool pgm pc_end c₁ c₂ →
    StepGotoRange P δ_goto δ_goto_bool pgm pc_end c₂ c₃ →
    StepGotoRange P δ_goto δ_goto_bool pgm pc_end c₁ c₃ := by
  intro h₁₂ h₂₃
  induction h₁₂ with
  | refl => exact h₂₃
  | step pc h_lt σ failed h_step _ ih =>
    exact .step pc h_lt σ failed h_step (ih h₂₃)

/-- Every `StepGotoRange` chain is also a `StepGotoStar` chain
(forgetting the range bound). -/
theorem StepGotoRange_to_StepGotoStar
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc_end : Nat}
    {c₁ c₂ : GotoConfig P} :
    StepGotoRange P δ_goto δ_goto_bool pgm pc_end c₁ c₂ →
    StepGotoStar P δ_goto δ_goto_bool pgm c₁ c₂ := by
  intro h
  unfold StepGotoStar
  induction h with
  | refl => exact .refl _
  | step _ _ _ _ h_step _ ih =>
    exact .step _ _ _ h_step ih

/-- A single step within the range extends to a `StepGotoRange` chain. -/
theorem StepGotoRange_single
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc_end pc : Nat}
    {σ : SemanticStore P} {failed : Bool}
    {c' : GotoConfig P}
    (h_lt : pc < pc_end)
    (h_step : StepGoto P δ_goto δ_goto_bool pgm
                (.running pc σ failed) c') :
    StepGotoRange P δ_goto δ_goto_bool pgm pc_end
      (.running pc σ failed) c' :=
  .step pc h_lt σ failed h_step .refl

/-! ## Per-instruction progress

Progress lemmas state that, given a well-formed instruction at `pc`,
the configuration can take a `StepGoto`. Each lemma takes the
minimal hypotheses needed to construct the matching constructor.

For state-changing instructions (`DECL`, `DEAD`, `ASSIGN`,
`ASSIGN`-nondet) the caller must additionally supply the existential
witness — name, value, and an `InitState` / `UpdateState` /
`RemoveState` derivation — because the abstract state-update
relations are not pinned down by the instruction alone in this
branch's `StepGoto`. -/

theorem progress_location
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .LOCATION) :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' :=
  ⟨_, .step_location h_at h_ty⟩

theorem progress_skip
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .SKIP) :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' :=
  ⟨_, .step_skip h_at h_ty⟩

theorem progress_decl
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .DECL)
    (x : P.Ident) (v : P.Expr) (σ' : SemanticStore P)
    (h_init : InitState P σ x v σ') :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' :=
  ⟨_, .step_decl h_at h_ty h_init⟩

theorem progress_dead
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .DEAD)
    (x : P.Ident) (σ' : SemanticStore P)
    (h_remove : RemoveState P σ x σ') :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' :=
  ⟨_, .step_dead h_at h_ty h_remove⟩

theorem progress_assign
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSIGN)
    (x : P.Ident) (rhs : Expr) (v : P.Expr) (σ' : SemanticStore P)
    (h_eval : δ_goto σ rhs = some v)
    (h_upd : UpdateState P σ x v σ') :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' :=
  ⟨_, .step_assign h_at h_ty h_eval h_upd⟩

theorem progress_assign_nondet
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSIGN)
    (x : P.Ident) (v : P.Expr) (σ' : SemanticStore P)
    (h_upd : UpdateState P σ x v σ') :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' :=
  ⟨_, .step_assign_nondet h_at h_ty h_upd⟩

theorem progress_assert
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSERT)
    (b : Bool) (h_g : δ_goto_bool σ instr.guard = some b) :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' := by
  cases b with
  | true => exact ⟨_, .step_assert_pass h_at h_ty h_g⟩
  | false => exact ⟨_, .step_assert_fail h_at h_ty h_g⟩

/-- ASSUME progress is partial: a `false` guard has *no* `StepGoto`
derivation (mirrors tautschnig's "ASSUME blocks the path" reading).
The caller learns whether the guard holds and dispatches accordingly. -/
theorem progress_assume_pass
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSUME)
    (h_g : δ_goto_bool σ instr.guard = some true) :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' :=
  ⟨_, .step_assume_pass h_at h_ty h_g⟩

theorem progress_goto
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .GOTO)
    (b : Bool) (h_g : δ_goto_bool σ instr.guard = some b)
    (h_target : b = true →
      ∃ tgt, instr.target = some tgt) :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' := by
  cases b with
  | false => exact ⟨_, .step_goto_fallthrough h_at h_ty h_g⟩
  | true =>
    obtain ⟨tgt, h_tgt⟩ := h_target rfl
    exact ⟨_, .step_goto_taken h_at h_ty h_tgt h_g⟩

theorem progress_end_function
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .END_FUNCTION) :
    ∃ c', StepGoto P δ_goto δ_goto_bool pgm
            (.running pc σ failed) c' :=
  ⟨_, .step_end_function h_at h_ty⟩

end CProverGOTO
