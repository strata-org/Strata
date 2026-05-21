/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Semantics
public import Strata.Backends.CBMC.GOTO.StepGotoProps

public section

/-! # Statement-level simulation primitives over `StepGoto`

Phase 4 of the GOTO-semantics-expansion plan
(`docs/superpowers/specs/2026-05-20-goto-semantics-expansion-design.md`).

This file ports a subset of `tautschnig/goto-semantics`'s
`SemanticsSim.lean` primitives over this branch's `StepGoto` /
`StepGotoStar`. The primitives mirror the structured-pipeline
`sim_X` building blocks: each takes a single instruction at a known
PC and produces a `StepGotoStar` segment that advances PC by one.

Coverage at this commit (covers the cheapest no-state-change primitives):

* `sim_location` / `sim_skip` — single `step_location` / `step_skip` step.
* `sim_assume_pass` — single `step_assume_pass` step.
* `sim_assert_pass` — single `step_assert_pass` step.

The remaining primitives (`sim_assign`, `sim_init`, `sim_havoc`,
`sim_cmd`, `sim_block`, `sim_loop`, `sim_ite_*`, `sim_end_to_end`)
are larger and depend on the choices Phase 3 made about
correspondence layers; they are deferred until a downstream consumer
of the structured pipeline appears. -/

namespace CProverGOTO.Sim

open CProverGOTO Imperative

/-- `sim_location`: at a `LOCATION` instruction, advance PC by one
without changing the store. The result is a one-step `StepGotoStar`
chain. -/
theorem sim_location
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .LOCATION) :
    StepGotoStar P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ failed) := by
  unfold StepGotoStar
  exact .step _ _ _ (.step_location h_at h_ty) (.refl _)

/-- `sim_skip`: at a `SKIP` instruction, advance PC by one without
changing the store. -/
theorem sim_skip
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .SKIP) :
    StepGotoStar P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ failed) := by
  unfold StepGotoStar
  exact .step _ _ _ (.step_skip h_at h_ty) (.refl _)

/-- `sim_assume_pass`: at an `ASSUME` instruction whose guard
evaluates to `true`, advance PC by one without changing the store. -/
theorem sim_assume_pass
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSUME)
    (h_g : δ_goto_bool σ instr.guard = some true) :
    StepGotoStar P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ failed) := by
  unfold StepGotoStar
  exact .step _ _ _ (.step_assume_pass h_at h_ty h_g) (.refl _)

/-- `sim_assert_pass`: at an `ASSERT` instruction whose guard
evaluates to `true`, advance PC by one without flipping `failed`. -/
theorem sim_assert_pass
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSERT)
    (h_g : δ_goto_bool σ instr.guard = some true) :
    StepGotoStar P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ failed) := by
  unfold StepGotoStar
  exact .step _ _ _ (.step_assert_pass h_at h_ty h_g) (.refl _)

/-- `sim_goto_fallthrough`: at a `GOTO` instruction whose guard
evaluates to `false`, advance PC by one. -/
theorem sim_goto_fallthrough
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .GOTO)
    (h_g : δ_goto_bool σ instr.guard = some false) :
    StepGotoStar P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ failed) := by
  unfold StepGotoStar
  exact .step _ _ _ (.step_goto_fallthrough h_at h_ty h_g) (.refl _)

/-- `sim_end_function`: at an `END_FUNCTION` instruction, terminate
the chain in a `.terminal` configuration with the same store and
failed flag. -/
theorem sim_end_function
    {P : PureExpr} [HasBool P] [HasNot P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ : SemanticStore P} {failed : Bool}
    {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .END_FUNCTION) :
    StepGotoStar P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.terminal σ failed) := by
  unfold StepGotoStar
  exact .step _ _ _ (.step_end_function h_at h_ty) (.refl _)

end CProverGOTO.Sim
