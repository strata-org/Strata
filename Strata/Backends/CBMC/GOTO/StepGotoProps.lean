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

end CProverGOTO
