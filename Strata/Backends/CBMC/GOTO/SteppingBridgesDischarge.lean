/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Bisim
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrectStore

public section

/-! # Discharging the `SteppingBridges` bundle from translator-shape hypotheses

This module produces a `SteppingBridges` value (consumed by
`StepGotoStar_to_ExecProg` in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean`) from a
*single* hypothesis package describing the actual translator output.

## Architecture

`SteppingBridges` (in `CoreCFGToGOTOCorrectStore.lean`) has two
fields, each universally quantified over a *single arbitrary*
`StepGoto` derivation:

* `step_running` — turn a running-to-running `StepGoto` into a
  `StepInstr`.
* `step_terminal` — turn a running-to-terminal `StepGoto` into an
  `ExecProg`.

Because the `StepGoto` derivation is arbitrary, the discharge must
case-split on its 12 constructors and dispatch to the corresponding
per-constructor bridge in `Bisim.lean`. Each bridge has its own
hypotheses that depend on the PC at which the step fires (lhs/rhs
lookups for ASSIGN, symbol-name lookups for DECL/DEAD,
`findLocIdx`-resolution for GOTO-taken). Those hypotheses must be
provided uniformly across PCs.

The interface here packages those hypotheses as a structure
`TranslatorBridgeHyps`, parameterised by the program. A consumer that
already has a `WellFormedTranslation` witness can derive a
`TranslatorBridgeHyps` value via
`TranslatorBridgeHypsDischarge.wellFormedTranslation_to_translatorBridgeHyps_v2`.

## Per-constructor coverage

* **Direct from `Bisim.lean` bridges.** The five non-state-changing
  cases (`location`, `skip`, `assert_pass`, `assume_pass`,
  `goto_fallthrough`), `assert_fail`, and the closure-level
  `end_function`.
* **Closed under `TranslatorBridgeHyps`.** `decl`, `dead`, `assign`,
  `assign_nondet`, `goto_taken` discharge from per-PC
  instruction-shape information that the translator emits, carried
  in `TranslatorBridgeHyps`.

Two structural obligations cannot be discharged from
`WellFormedTranslation` + `valueCorrCore` alone and are surfaced as
fields on `TranslatorBridgeHyps`:

* **`step_decl` empty-value condition.**
  `Bisim.stepGoto_decl_to_stepInstr` requires
  `vc.toValue v = some .vEmpty`; under `valueCorrCore` no
  `Lambda.LExpr` constructor satisfies this. Surfaced as
  `decl_empty_value`. Folding the translator's DECL+ASSIGN pair
  into one `StepInstr` step would require a different bridge
  shape (one StepGoto ↔ two StepInstrs).
* **`findLocIdx` resolution.**
  `Bisim.stepGoto_goto_taken_to_stepInstr` needs the second-pass
  patcher's `locationNum`-to-instruction-index resolution.
  `WellFormedTranslation.layout_cond_goto` gives the index target
  but says nothing about the underlying `locationNum`. Surfaced as
  `goto_target_resolves`. -/

namespace CProverGOTO.SteppingBridgesDischarge

open Imperative
open CProverGOTO
open CProverGOTO.SemanticsTautschnig (ValueCorr StoreCorr CallResultRel ExprEval FuncEnv Store StepInstr ExecProg)

/-! ## TranslatorBridgeHyps: per-PC structural information from the translator -/

/-- Bundle of per-PC structural hypotheses needed to discharge
`SteppingBridges`. Each field is universally quantified over the PC
because the bridges fire at unknown locations during the trace lift.

Some fields are **conditional** — they only need to hold *given the
shape of the* `StepGoto` step that fires at this PC. We encode those
as implications in the field type. -/
structure TranslatorBridgeHyps
    {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    (pgm : Program)
    (nameMap : P.Ident → String)
    (δ_goto : SemanticEvalGoto P)
    (eval : SemanticsTautschnig.ExprEval) : Prop where
  /-- Injectivity of the renaming map. Required by `step_dead`,
  `step_decl`, `step_assign`, `step_assign_nondet` to preserve
  `StoreCorr` across a single-key store mutation. -/
  nameMap_inj : Function.Injective nameMap
  /-- For every PC carrying a DECL instruction, the underlying
  `Code` resolves via `getSymbolName` to the renamed identifier of
  the `InitState` witness. -/
  decl_lookup :
    ∀ {pc : Nat} {instr : Instruction} {x : P.Ident}
      {σ σ' : Imperative.SemanticStore P} {v : P.Expr},
      pgm.instrAt pc = some instr → instr.type = .DECL →
      Imperative.InitState P σ x v σ' →
      (SemanticsTautschnig.instrCode pgm pc).bind
        SemanticsTautschnig.getSymbolName = some (nameMap x)
  /-- For every PC carrying a DEAD instruction, the underlying
  `Code` resolves via `getSymbolName` to the renamed identifier of
  the `RemoveState` witness. -/
  dead_lookup :
    ∀ {pc : Nat} {instr : Instruction} {x : P.Ident}
      {σ σ' : Imperative.SemanticStore P},
      pgm.instrAt pc = some instr → instr.type = .DEAD →
      RemoveState P σ x σ' →
      (SemanticsTautschnig.instrCode pgm pc).bind
        SemanticsTautschnig.getSymbolName = some (nameMap x)
  /-- For every PC carrying an ASSIGN instruction whose
  `StepGoto.step_assign` derivation supplies a GOTO-side rhs `rhs_g`
  (the second argument to `δ_goto`) and source-side value `v_imp`,
  the underlying `Code` resolves via
  `getAssignLhs/getAssignRhs` to `(nameMap x, rhs_g)`. (Matches the
  shape `tautschnig.StepInstr.assign` requires.) -/
  assign_lookup :
    ∀ {pc : Nat} {instr : Instruction} {x : P.Ident}
      {σ σ' : Imperative.SemanticStore P}
      {rhs_g : Expr} {v_imp : P.Expr},
      pgm.instrAt pc = some instr → instr.type = .ASSIGN →
      δ_goto σ rhs_g = some v_imp →
      Imperative.UpdateState P σ x v_imp σ' →
      (SemanticsTautschnig.instrCode pgm pc).bind
          SemanticsTautschnig.getAssignLhs = some (nameMap x) ∧
      (SemanticsTautschnig.instrCode pgm pc).bind
          SemanticsTautschnig.getAssignRhs = some rhs_g
  /-- For every PC carrying an ASSIGN instruction whose
  `StepGoto.step_assign_nondet` derivation fires, the underlying
  `Code` has `getAssignLhs = nameMap x` and `getAssignRhs = rhs`,
  where `rhs` is the constructor's rhs. The
  `step_assign_nondet` constructor itself carries the rhs-shape
  witnesses (`instr.code = Code.assign lhs rhs` and
  `rhs.id = .side_effect .Nondet`), passed in as preconditions; the
  lookup chain reduces structurally from `h_code` via
  `assign_code_to_lhsRhs`. -/
  assign_nondet_lookup :
    ∀ {pc : Nat} {instr : Instruction} {x : P.Ident}
      {lhs rhs : Expr}
      {σ σ' : Imperative.SemanticStore P} {v_imp : P.Expr},
      pgm.instrAt pc = some instr → instr.type = .ASSIGN →
      instr.code = Code.assign lhs rhs →
      rhs.id = .side_effect .Nondet →
      Imperative.UpdateState P σ x v_imp σ' →
      (SemanticsTautschnig.instrCode pgm pc).bind
          SemanticsTautschnig.getAssignLhs = some (nameMap x) ∧
      (SemanticsTautschnig.instrCode pgm pc).bind
          SemanticsTautschnig.getAssignRhs = some rhs
  /-- For every PC carrying a GOTO instruction with a pre-resolved
  index target, there's a matching `findLocIdx` resolution: the
  `instrTarget` exposes a `locationNum` whose `findLocIdx` lands
  back on the index target. Genuinely-extra hypothesis (not in
  current `WellFormedTranslation`). -/
  goto_target_resolves :
    ∀ {pc target : Nat} {instr : Instruction},
      pgm.instrAt pc = some instr → instr.type = .GOTO →
      instr.target = some target →
      ∃ loc, SemanticsTautschnig.instrTarget pgm pc = some (some loc) ∧
             SemanticsTautschnig.findLocIdx pgm.instructions loc =
               some target
  /-- For every fresh `step_decl`, the source-side initialisation
  value `v` translates via `vc.toValue` to the GOTO-side `vEmpty`
  sentinel. **Not** discharged by `valueCorrCore` for any concrete
  `Lambda.LExpr`; either the translator must be reshaped to fold
  DECL+ASSIGN, or `ValueCorr` enriched. -/
  decl_empty_value :
    ∀ {pc : Nat} {instr : Instruction} {x : P.Ident} {v : P.Expr}
      {σ σ' : Imperative.SemanticStore P},
      pgm.instrAt pc = some instr → instr.type = .DECL →
      Imperative.InitState P σ x v σ' →
      (SemanticsTautschnig.ValueCorr.toValue v
        : Option SemanticsTautschnig.Value)
        = some .vEmpty
  /-- For every `step_assign` at an ASSIGN PC, the source-side
  evaluator's value `v_imp` translates via `vc.toValue` to a
  concrete GOTO-side `Value` `v_goto`, and the GOTO-side `eval`
  agrees on the same rhs.

  Combines `vc.toValue v_imp = some v_goto` with the
  `eval σ_goto rhs_g = some v_goto` step that
  `tautschnig.StepInstr.assign` needs. The GOTO-side `eval`
  agreement is the `EvalCorr` / `EvalValueCorr` output pinned to
  the rhs `rhs_g` that the translator emits. -/
  assign_value_corr :
    ∀ {pc : Nat} {instr : Instruction} {x : P.Ident}
      {σ_imp σ_imp' : Imperative.SemanticStore P}
      {σ_goto : SemanticsTautschnig.Store}
      {rhs_g : Expr} {v_imp : P.Expr},
      pgm.instrAt pc = some instr → instr.type = .ASSIGN →
      δ_goto σ_imp rhs_g = some v_imp →
      Imperative.UpdateState P σ_imp x v_imp σ_imp' →
      SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto →
      ∃ v_goto,
        (SemanticsTautschnig.ValueCorr.toValue v_imp
          : Option SemanticsTautschnig.Value) = some v_goto ∧
        eval σ_goto rhs_g = some v_goto
  /-- For every `step_assign_nondet`, the (arbitrary) assigned value
  translates via `vc.toValue` to a concrete GOTO-side `Value`. -/
  assign_nondet_value_corr :
    ∀ {pc : Nat} {instr : Instruction} {x : P.Ident}
      {σ σ' : Imperative.SemanticStore P} {v_imp : P.Expr},
      pgm.instrAt pc = some instr → instr.type = .ASSIGN →
      Imperative.UpdateState P σ x v_imp σ' →
      ∃ v_goto,
        (SemanticsTautschnig.ValueCorr.toValue v_imp
          : Option SemanticsTautschnig.Value)
          = some v_goto

/-! ## Helpers: `StoreCorr` preservation under single-key mutations -/

/-- StoreCorr preservation under a single-key update. Mirror of the
proof inside `Bisim.stepGoto_assign_to_stepInstr`, lifted out here
so we can apply `StepInstr.assign` directly with the GOTO-side rhs
the translator emits (rather than via `EvalValueCorr` on
`exprTrans`). -/
private theorem storeCorr_preserve_update
    {P : Imperative.PureExpr} [SemanticsTautschnig.ValueCorr P]
    {nameMap : P.Ident → String}
    {x : P.Ident} {v_imp : P.Expr}
    {v_goto : SemanticsTautschnig.Value}
    {σ σ' : SemanticStore P} {σ_goto : SemanticsTautschnig.Store}
    (h_inj : Function.Injective nameMap)
    (h_upd : UpdateState P σ x v_imp σ')
    (h_value_corr :
      (SemanticsTautschnig.ValueCorr.toValue v_imp
        : Option SemanticsTautschnig.Value) = some v_goto)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ σ_goto) :
    SemanticsTautschnig.StoreCorr nameMap σ' (σ_goto.update (nameMap x) v_goto) := by
  intro y
  cases h_upd with
  | update _h_pre h_post h_other =>
    by_cases h_eq : x = y
    · subst h_eq
      right
      refine ⟨v_imp, v_goto, h_post, h_value_corr, ?_⟩
      simp [SemanticsTautschnig.Store.update]
    · have h_imp_eq : σ' y = σ y := h_other y h_eq
      have h_goto_eq : (σ_goto.update (nameMap x) v_goto) (nameMap y)
                        = σ_goto (nameMap y) := by
        simp [SemanticsTautschnig.Store.update]
        intro h_collide
        exact absurd (h_inj h_collide).symm h_eq
      rcases h_corr y with ⟨h_imp_n, h_goto_n⟩ | ⟨e, v, h_imp_s, h_to, h_goto_s⟩
      · left; exact ⟨by rw [h_imp_eq]; exact h_imp_n,
                     by rw [h_goto_eq]; exact h_goto_n⟩
      · right
        exact ⟨e, v, by rw [h_imp_eq]; exact h_imp_s, h_to,
                       by rw [h_goto_eq]; exact h_goto_s⟩

/-! ## Top-level discharge

The `step_running` field case-splits on the `StepGoto` derivation
and dispatches each constructor either to a `Bisim.*` bridge or to
direct `StepInstr` constructor application. The `step_terminal`
field handles only `step_end_function` (the only `StepGoto`
constructor that produces a `.terminal` configuration). -/

/-- The main theorem. Build a `SteppingBridges` value from:

* `Bisim.EvalBoolCorr` (boolean-evaluator output),
* a `TranslatorBridgeHyps` describing the actual translator output
  (`WellFormedTranslation`-derivable lookups plus the extra
  `findLocIdx` resolution, value-correspondence, and `vEmpty`
  obligations).

The `Bisim.EvalValueCorr` interface is *not* taken as a hypothesis
here; instead, the value-side correspondence is folded into
`TranslatorBridgeHyps.assign_value_corr`. This is because
`StepGoto.step_assign`'s rhs is an arbitrary GOTO `Expr` (not
necessarily of the form `exprTrans rhs_imp`), so we cannot rely on
the `exprTrans`-shaped `EvalValueCorr` directly; we need a per-PC
fact tying the rhs the translator emits to the `eval` outcome. -/
theorem steppingBridges_of_translator
    {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    {δ_goto : SemanticEvalGoto P} {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    (h_eval_bool_corr : Bisim.EvalBoolCorr nameMap δ_goto_bool eval)
    (h_brHyps : TranslatorBridgeHyps pgm nameMap δ_goto eval) :
    SteppingBridges δ_goto δ_goto_bool pgm nameMap callResult eval fenv where
  step_running := by
    intro pc pc' σ_imp σ_imp' failed failed' σ_goto h_step h_corr
    cases h_step with
    | step_location h_at h_ty =>
      exact Bisim.stepGoto_location_to_stepInstr h_at h_ty h_corr
    | step_skip h_at h_ty =>
      exact Bisim.stepGoto_skip_to_stepInstr h_at h_ty h_corr
    | step_decl h_at h_ty h_init =>
      exact Bisim.stepGoto_decl_to_stepInstr h_brHyps.nameMap_inj h_at h_ty h_init
        (h_brHyps.decl_lookup h_at h_ty h_init)
        (h_brHyps.decl_empty_value h_at h_ty h_init) h_corr
    | step_dead h_at h_ty h_remove =>
      exact Bisim.stepGoto_dead_to_stepInstr h_brHyps.nameMap_inj h_at h_ty h_remove
        (h_brHyps.dead_lookup h_at h_ty h_remove) h_corr
    | step_assign h_at h_ty h_eval_imp h_upd =>
      -- Apply `StepInstr.assign` directly with the rhs the translator emits.
      obtain ⟨h_lhs, h_rhs⟩ :=
        h_brHyps.assign_lookup h_at h_ty h_eval_imp h_upd
      obtain ⟨v_goto, h_vc, h_eval⟩ :=
        h_brHyps.assign_value_corr h_at h_ty h_eval_imp h_upd h_corr
      refine ⟨_, ?_,
        .assign (Bisim.instrAt_to_instrType h_at h_ty) h_lhs h_rhs h_eval⟩
      exact storeCorr_preserve_update h_brHyps.nameMap_inj h_upd h_vc h_corr
    | step_assign_nondet h_at h_ty h_code h_id h_upd =>
      -- The `step_assign_nondet` constructor carries the rhs-shape
      -- witness directly via `h_code` and `h_id`; the bridge field
      -- receives them as preconditions and reduces the
      -- `getAssignLhs/getAssignRhs` lookup chain structurally.
      obtain ⟨h_lhs, h_rhs⟩ :=
        h_brHyps.assign_nondet_lookup h_at h_ty h_code h_id h_upd
      obtain ⟨v_goto, h_vc⟩ :=
        h_brHyps.assign_nondet_value_corr h_at h_ty h_upd
      exact Bisim.stepGoto_assign_nondet_to_stepInstr h_brHyps.nameMap_inj
        h_at h_ty h_upd h_lhs h_rhs h_id h_vc h_corr
    | step_assert_pass h_at h_ty h_g =>
      exact Bisim.stepGoto_assert_pass_to_stepInstr h_eval_bool_corr
        h_at h_ty h_g h_corr
    | step_assert_fail h_at h_ty h_g =>
      -- Discard the AssertFails witness — `step_running` only
      -- requires the StepInstr step.
      obtain ⟨σ_goto', h_corr', h_step', _⟩ :=
        Bisim.stepGoto_assert_fail_to_stepInstr h_eval_bool_corr h_at h_ty h_g h_corr
      exact ⟨σ_goto', h_corr', h_step'⟩
    | step_assume_pass h_at h_ty h_g =>
      exact Bisim.stepGoto_assume_pass_to_stepInstr h_eval_bool_corr
        h_at h_ty h_g h_corr
    | step_goto_taken h_at h_ty h_target h_g =>
      exact Bisim.stepGoto_goto_taken_to_stepInstr h_eval_bool_corr
        h_at h_ty h_target h_g
        (h_brHyps.goto_target_resolves h_at h_ty h_target) h_corr
    | step_goto_fallthrough h_at h_ty h_g =>
      exact Bisim.stepGoto_goto_fallthrough_to_stepInstr h_eval_bool_corr
        h_at h_ty h_g h_corr
  step_terminal := by
    intro pc σ_imp σ_imp' failed failed' σ_goto h_step h_corr
    cases h_step with
    | step_end_function h_at h_ty =>
      obtain ⟨h_corr', h_exec⟩ :=
        Bisim.stepGoto_end_function_to_execProg
          (callResult := callResult) (eval := eval) (fenv := fenv)
          h_at h_ty h_corr
      exact ⟨σ_goto, h_corr', h_exec⟩

end CProverGOTO.SteppingBridgesDischarge
