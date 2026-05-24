/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Semantics
public import Strata.Backends.CBMC.GOTO.SemanticsTautschnig
public import Strata.Backends.CBMC.GOTO.ValueCorrCore

public section

/-! # Bisimulation bridge between `StepGoto` and `StepInstr`

This module connects this branch's `CProverGOTO.StepGoto` (over an
expression-valued `Imperative.SemanticStore`) to the ported tautschnig
relation `CProverGOTO.SemanticsTautschnig.StepInstr` (over a concrete
`Value`-valued `Store`).

Each per-constructor forward bridge (`StepGoto → StepInstr`) is stated
as a theorem here. Non-state-changing constructors (`step_location`,
`step_skip`, `step_assert_pass`, `step_assume_pass`,
`step_goto_fallthrough`) are direct: they leave the store unchanged so
`StoreCorr` is trivially preserved. State-changing constructors
(`step_decl`, `step_dead`, `step_assign`, `step_assign_nondet`) plus
the failure / branching constructors (`step_assert_fail`,
`step_goto_taken`) take additional structural hypotheses (well-formed
instruction code on the GOTO side, plus `EvalCorr` for `ASSIGN`,
plus a `findLocIdx` resolution for `step_goto_taken`).

The closure-level `step_end_function` bridge produces an `ExecProg`
rather than a `StepInstr`. The trace-level lift assembling these
per-step bridges into `StepGotoStar → ExecProg` lives in
`Strata/Backends/CBMC/GOTO/CoreCFGToGOTOCorrectStore.lean`. -/

namespace CProverGOTO.Bisim

open Imperative
open CProverGOTO
open CProverGOTO.SemanticsTautschnig (ValueCorr StoreCorr CallResultRel ExprEval FuncEnv Store StepInstr)

/-! ## Helper lemmas: bridging `Program.instrAt` to `SemanticsTautschnig.instrType` -/

/-- The two instruction-lookup helpers agree: if `pgm.instrAt pc =
some instr` and `instr.type = ty`, then `instrType pgm pc = some ty`. -/
theorem instrAt_to_instrType
    {pgm : Program} {pc : Nat} {instr : Instruction} {ty : InstructionType}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = ty) :
    SemanticsTautschnig.instrType pgm pc = some ty := by
  unfold Program.instrAt at h_at
  unfold SemanticsTautschnig.instrType
  rw [h_at, Option.map_some, h_ty]

/-- Same for the guard accessor. -/
theorem instrAt_to_instrGuard
    {pgm : Program} {pc : Nat} {instr : Instruction}
    (h_at : pgm.instrAt pc = some instr) :
    SemanticsTautschnig.instrGuard pgm pc = some instr.guard := by
  unfold Program.instrAt at h_at
  unfold SemanticsTautschnig.instrGuard
  rw [h_at, Option.map_some]

/-! ## Forward bridges for non-state-changing constructors

For the constructors that leave the imperative-side store unchanged,
the bridge consists of:

1. Recovering the GOTO-side instruction (`pgm.instrAt pc = some instr`,
   `instr.type = ...`).
2. Forwarding `eval σ_goto instr.guard` to `δ_goto_bool σ_imp
   instr.guard`. For the bridge to succeed, an `EvalBoolCorr`-shaped
   external hypothesis is needed; we surface it as a parameter on
   each bridge theorem rather than making it a global typeclass.

The state portion of `StoreCorr` is preserved by reflexivity. -/

/-- Boolean-evaluator correspondence: the GOTO-side boolean evaluator
agrees with the tautschnig-side concrete evaluator on translated
guards.

This is the boolean analogue of `EvalCorr` on the concrete-evaluator
side. Stated separately so the bridges for ASSERT/ASSUME/GOTO can
require *only* this, not the full `EvalCorr` for value-returning
expressions. -/
@[expose] def EvalBoolCorr {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    (nameMap : P.Ident → String)
    (δ_goto_bool : SemanticEvalGotoBool P)
    (eval : SemanticsTautschnig.ExprEval) : Prop :=
  ∀ σ_imp σ_goto (e : Expr) (b : Bool),
    SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto →
    δ_goto_bool σ_imp e = some b →
    eval σ_goto e = some (.vBool b)

/-- Bridge for `step_location`.

The bridge for store-unchanged instructions does not depend on the
GOTO evaluators (`δ_goto`, `δ_goto_bool`) — the constructor just
needs `instrType pgm pc = some .LOCATION`. -/
theorem stepGoto_location_to_stepInstr
    {P : Imperative.PureExpr} [SemanticsTautschnig.ValueCorr P]
    {pgm : Program} {pc : Nat} {σ_imp : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .LOCATION)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' :=
  ⟨σ_goto, h_corr, .location (instrAt_to_instrType h_at h_ty)⟩

/-- Bridge for `step_skip`. -/
theorem stepGoto_skip_to_stepInstr
    {P : Imperative.PureExpr} [SemanticsTautschnig.ValueCorr P]
    {pgm : Program} {pc : Nat} {σ_imp : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .SKIP)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' :=
  ⟨σ_goto, h_corr, .skip (instrAt_to_instrType h_at h_ty)⟩

/-- Bridge for `step_assert_pass`. The asserted guard evaluates to
`true` on both sides, so the resulting GOTO-side step is `assert_pass`
with no store change. -/
theorem stepGoto_assert_pass_to_stepInstr
    {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ_imp : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_eval_bool_corr : EvalBoolCorr nameMap δ_goto_bool eval)
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSERT)
    (h_g : δ_goto_bool σ_imp instr.guard = some true)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' := by
  refine ⟨σ_goto, h_corr, .assert_pass (instrAt_to_instrType h_at h_ty) ?_⟩
  rw [instrAt_to_instrGuard h_at, Option.bind_some]
  exact h_eval_bool_corr σ_imp σ_goto instr.guard true h_corr h_g

/-- Bridge for `step_assume_pass`. -/
theorem stepGoto_assume_pass_to_stepInstr
    {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ_imp : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_eval_bool_corr : EvalBoolCorr nameMap δ_goto_bool eval)
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSUME)
    (h_g : δ_goto_bool σ_imp instr.guard = some true)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' := by
  refine ⟨σ_goto, h_corr, .assume_pass (instrAt_to_instrType h_at h_ty) ?_⟩
  rw [instrAt_to_instrGuard h_at, Option.bind_some]
  exact h_eval_bool_corr σ_imp σ_goto instr.guard true h_corr h_g

/-- Bridge for `step_goto_fallthrough`. The guard evaluates to `false`,
so both sides advance to `pc + 1` without store change. -/
theorem stepGoto_goto_fallthrough_to_stepInstr
    {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ_imp : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_eval_bool_corr : EvalBoolCorr nameMap δ_goto_bool eval)
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .GOTO)
    (h_g : δ_goto_bool σ_imp instr.guard = some false)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' := by
  refine ⟨σ_goto, h_corr, .goto_not_taken (instrAt_to_instrType h_at h_ty) ?_⟩
  rw [instrAt_to_instrGuard h_at, Option.bind_some]
  exact h_eval_bool_corr σ_imp σ_goto instr.guard false h_corr h_g

/-! ## Bridges with extra structural hypotheses

The next two bridges need information that the `StepGoto` constructor
alone does not carry: the failure flag (for `step_assert_fail`) and a
`locationNum`-to-instruction-index resolution (for `step_goto_taken`).
Both are surfaced as explicit hypotheses on the bridge theorem rather
than encoded in `StepGoto`. -/

/-- Bridge for `step_assert_fail`. This branch's `step_assert_fail`
flips the failed flag in the configuration; tautschnig's
`StepInstr.assert_fail` advances PC normally and surfaces failure
via the separate `AssertFails` predicate. The bridge therefore
produces *both* a `StepInstr` step *and* an `AssertFails` witness on
the GOTO-side store. -/
theorem stepGoto_assert_fail_to_stepInstr
    {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc : Nat} {σ_imp : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_eval_bool_corr : EvalBoolCorr nameMap δ_goto_bool eval)
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSERT)
    (h_g : δ_goto_bool σ_imp instr.guard = some false)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' ∧
      SemanticsTautschnig.AssertFails eval pgm pc σ_goto := by
  refine ⟨σ_goto, h_corr, ?_, ?_, ?_⟩
  · exact .assert_fail (instrAt_to_instrType h_at h_ty)
      (by rw [instrAt_to_instrGuard h_at, Option.bind_some]
          exact h_eval_bool_corr σ_imp σ_goto instr.guard false h_corr h_g)
  · exact instrAt_to_instrType h_at h_ty
  · rw [instrAt_to_instrGuard h_at, Option.bind_some]
    exact h_eval_bool_corr σ_imp σ_goto instr.guard false h_corr h_g

/-- Bridge for `step_goto_taken`. This branch's `step_goto_taken`
uses a pre-resolved instruction index (`instr.target = some target`);
tautschnig's `StepInstr.goto_taken` walks `findLocIdx` over a
`locationNum`. The bridge needs the resolution as an external
hypothesis: there must exist a `locationNum` `loc` whose `findLocIdx`
yields the same target index. -/
theorem stepGoto_goto_taken_to_stepInstr
    {P : Imperative.PureExpr} [HasBool P] [HasNot P]
    [SemanticsTautschnig.ValueCorr P]
    {δ_goto_bool : SemanticEvalGotoBool P}
    {pgm : Program} {pc target : Nat} {σ_imp : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_eval_bool_corr : EvalBoolCorr nameMap δ_goto_bool eval)
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .GOTO)
    (_h_target : instr.target = some target)
    (h_g : δ_goto_bool σ_imp instr.guard = some true)
    (h_findLoc : ∃ loc, SemanticsTautschnig.instrTarget pgm pc = some (some loc) ∧
                        SemanticsTautschnig.findLocIdx pgm.instructions loc = some target)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto target σ_goto' := by
  obtain ⟨loc, h_loc, h_idx⟩ := h_findLoc
  refine ⟨σ_goto, h_corr,
    .goto_taken (instrAt_to_instrType h_at h_ty) h_loc ?_ h_idx⟩
  rw [instrAt_to_instrGuard h_at, Option.bind_some]
  exact h_eval_bool_corr σ_imp σ_goto instr.guard true h_corr h_g

/-! ## Bridge for `step_dead`

Bridges via `RemoveState ↔ Store.kill`. Both sides remove the binding
for the same identifier (`nameMap` translates between `P.Ident` and
the GOTO-side `String`). Preserves `StoreCorr` because:

* For the killed key `x`: `RemoveState` sets `σ_imp' x = none` and
  `Store.kill` sets `σ_goto' (nameMap x) = none`. The "both none"
  branch of `StoreCorr` is satisfied.
* For other keys: both stores agree with their predecessors, so
  `StoreCorr` propagates from the input. -/

theorem stepGoto_dead_to_stepInstr
    {P : Imperative.PureExpr} [SemanticsTautschnig.ValueCorr P]
    {pgm : Program} {pc : Nat}
    {σ_imp σ_imp' : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    (h_inj : Function.Injective nameMap)
    {x : P.Ident}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .DEAD)
    (h_remove : RemoveState P σ_imp x σ_imp')
    (h_codeName : (SemanticsTautschnig.instrCode pgm pc).bind
                    SemanticsTautschnig.getSymbolName = some (nameMap x))
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp' σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' := by
  refine ⟨σ_goto.kill (nameMap x), ?_, .dead (instrAt_to_instrType h_at h_ty) h_codeName⟩
  -- StoreCorr preservation: RemoveState removes x on imp side;
  -- Store.kill removes (nameMap x) on goto side.
  intro y
  cases h_remove with
  | remove h_y_none h_other =>
    by_cases h_eq : x = y
    · -- y = x: both stores have the binding removed.
      subst h_eq
      left; refine ⟨h_y_none, ?_⟩
      simp [SemanticsTautschnig.Store.kill]
    · -- y ≠ x: both stores agree with their predecessors at y.
      have h_imp_eq : σ_imp' y = σ_imp y := h_other y h_eq
      have h_goto_eq : (σ_goto.kill (nameMap x)) (nameMap y) = σ_goto (nameMap y) := by
        simp [SemanticsTautschnig.Store.kill]
        intro h_collide
        exact absurd (h_inj h_collide).symm h_eq
      rcases h_corr y with ⟨h_imp_n, h_goto_n⟩ | ⟨e, v, h_imp_s, h_to, h_goto_s⟩
      · left; exact ⟨by rw [h_imp_eq]; exact h_imp_n, by rw [h_goto_eq]; exact h_goto_n⟩
      · right
        exact ⟨e, v, by rw [h_imp_eq]; exact h_imp_s, h_to,
                       by rw [h_goto_eq]; exact h_goto_s⟩

/-! ## Bridge for `step_assign`

Bridges `step_assign` (this branch) to `StepInstr.assign` (tautschnig)
via three external pieces:

* `EvalCorr` for the value-returning evaluator: the GOTO-side
  evaluator `δ_goto` agrees with tautschnig's `eval` on translated
  expressions. Stated as a hypothesis on this bridge rather than a
  global typeclass (mirroring `EvalBoolCorr` for the boolean
  bridges).
* `Function.Injective nameMap`: distinct source identifiers must not
  collide on the same GOTO-side symbol, otherwise `StoreCorr` cannot
  be preserved across the assignment.
* The instruction-code lookup giving the assign's `lhs` and `rhs`
  components on the GOTO side, plus the agreement that the source
  identifier `x` translates to the GOTO-side symbol name. -/

/-- The full value-evaluator correspondence (cousin of
`EvalBoolCorr`). The GOTO-side evaluator `δ_goto`, applied to a
source-side expression, agrees with tautschnig's `eval` on the
translated GOTO `Expr`, modulo `StoreCorr` and `vc.toValue`. -/
@[expose] def EvalValueCorr {P : Imperative.PureExpr}
    [SemanticsTautschnig.ValueCorr P]
    (nameMap : P.Ident → String)
    (exprTrans : P.Expr → Expr)
    (δ_goto : SemanticEvalGoto P)
    (eval : SemanticsTautschnig.ExprEval) : Prop :=
  ∀ σ_imp σ_goto e_imp v_imp,
    SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto →
    δ_goto σ_imp (exprTrans e_imp) = some v_imp →
    eval σ_goto (exprTrans e_imp) =
      (SemanticsTautschnig.ValueCorr.toValue v_imp : Option SemanticsTautschnig.Value)

/-- Bridge for `step_assign`. -/
theorem stepGoto_assign_to_stepInstr
    {P : Imperative.PureExpr} [SemanticsTautschnig.ValueCorr P]
    {δ_goto : SemanticEvalGoto P}
    {pgm : Program} {pc : Nat}
    {σ_imp σ_imp' : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    {exprTrans : P.Expr → Expr}
    (h_inj : Function.Injective nameMap)
    {x : P.Ident}
    {rhs_imp : P.Expr} {v_imp : P.Expr}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_eval_corr : EvalValueCorr nameMap exprTrans δ_goto eval)
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSIGN)
    (h_eval_imp : δ_goto σ_imp (exprTrans rhs_imp) = some v_imp)
    (h_upd : Imperative.UpdateState P σ_imp x v_imp σ_imp')
    (h_codeLhs : (SemanticsTautschnig.instrCode pgm pc).bind
                   SemanticsTautschnig.getAssignLhs = some (nameMap x))
    (h_codeRhs : (SemanticsTautschnig.instrCode pgm pc).bind
                   SemanticsTautschnig.getAssignRhs = some (exprTrans rhs_imp))
    {v_goto : SemanticsTautschnig.Value}
    (h_value_corr :
      (SemanticsTautschnig.ValueCorr.toValue v_imp : Option SemanticsTautschnig.Value) = some v_goto)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp' σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' := by
  refine ⟨σ_goto.update (nameMap x) v_goto, ?_,
    .assign (instrAt_to_instrType h_at h_ty) h_codeLhs h_codeRhs ?_⟩
  · -- StoreCorr preservation. Mirror of stepGoto_dead bridge.
    intro y
    cases h_upd with
    | update h_pre h_post h_other =>
      by_cases h_eq : x = y
      · subst h_eq
        right
        refine ⟨v_imp, v_goto, h_post, h_value_corr, ?_⟩
        simp [SemanticsTautschnig.Store.update]
      · have h_imp_eq : σ_imp' y = σ_imp y := h_other y h_eq
        have h_goto_eq : (σ_goto.update (nameMap x) v_goto) (nameMap y) = σ_goto (nameMap y) := by
          simp [SemanticsTautschnig.Store.update]
          intro h_collide
          exact absurd (h_inj h_collide).symm h_eq
        rcases h_corr y with ⟨h_imp_n, h_goto_n⟩ | ⟨e, v, h_imp_s, h_to, h_goto_s⟩
        · left; exact ⟨by rw [h_imp_eq]; exact h_imp_n, by rw [h_goto_eq]; exact h_goto_n⟩
        · right
          exact ⟨e, v, by rw [h_imp_eq]; exact h_imp_s, h_to,
                         by rw [h_goto_eq]; exact h_goto_s⟩
  · -- Eval correspondence: eval σ_goto (exprTrans rhs_imp) = some v_goto.
    rw [h_eval_corr σ_imp σ_goto rhs_imp v_imp h_corr h_eval_imp]
    exact h_value_corr

/-! ## Bridge for `step_decl`

Bridges `step_decl` (this branch) to `StepInstr.decl` (tautschnig).
The two constructors disagree on the *value* a freshly-declared
binding gets: this branch's `InitState` produces some witness value
`v` (whatever the caller supplied), while tautschnig's `decl` always
sets the symbol to `vEmpty`.

The bridge therefore takes a hypothesis
`SemanticsTautschnig.ValueCorr.toValue v = some .vEmpty`: the
caller-supplied initialization value translates to `vEmpty` on the
GOTO side. For `Core.Expression`, no `Lambda.LExpr` constructor
satisfies this hypothesis under the `valueCorrCore` instance — so
the bridge fires only at call sites that supply a different
`ValueCorr P` instance whose `toValue` recognizes some sentinel
expression as `vEmpty`. -/

theorem stepGoto_decl_to_stepInstr
    {P : Imperative.PureExpr} [SemanticsTautschnig.ValueCorr P]
    {pgm : Program} {pc : Nat}
    {σ_imp σ_imp' : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    (h_inj : Function.Injective nameMap)
    {x : P.Ident} {v : P.Expr}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .DECL)
    (h_init : Imperative.InitState P σ_imp x v σ_imp')
    (h_codeName : (SemanticsTautschnig.instrCode pgm pc).bind
                    SemanticsTautschnig.getSymbolName = some (nameMap x))
    (h_value_empty :
      (SemanticsTautschnig.ValueCorr.toValue v : Option SemanticsTautschnig.Value)
        = some .vEmpty)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp' σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' := by
  refine ⟨σ_goto.declare (nameMap x), ?_,
    .decl (instrAt_to_instrType h_at h_ty) h_codeName⟩
  -- StoreCorr preservation. Mirror of step_dead and step_assign.
  intro y
  cases h_init with
  | init h_pre h_post h_other =>
    by_cases h_eq : x = y
    · subst h_eq
      right
      refine ⟨v, .vEmpty, h_post, h_value_empty, ?_⟩
      simp [SemanticsTautschnig.Store.declare]
    · have h_imp_eq : σ_imp' y = σ_imp y := h_other y h_eq
      have h_goto_eq : (σ_goto.declare (nameMap x)) (nameMap y) = σ_goto (nameMap y) := by
        simp [SemanticsTautschnig.Store.declare]
        intro h_collide
        exact absurd (h_inj h_collide).symm h_eq
      rcases h_corr y with ⟨h_imp_n, h_goto_n⟩ | ⟨e, v', h_imp_s, h_to, h_goto_s⟩
      · left; exact ⟨by rw [h_imp_eq]; exact h_imp_n, by rw [h_goto_eq]; exact h_goto_n⟩
      · right
        exact ⟨e, v', by rw [h_imp_eq]; exact h_imp_s, h_to,
                        by rw [h_goto_eq]; exact h_goto_s⟩

/-! ## Bridge for `step_assign_nondet`

Bridges `step_assign_nondet` (this branch) to `StepInstr.assign_nondet`
(tautschnig). The structural difference is on the syntactic side:
tautschnig's `assign_nondet` requires `rhs.id = .side_effect .Nondet`
on the GOTO-side instruction; this branch's `step_assign_nondet`
does not impose that constraint at the constructor level (it relies
on the upstream `CmdEmittedAt.set_nondet` layout predicate to gate
where the rule fires).

The bridge takes the syntactic check as an external hypothesis
(`h_rhs_nondet`), plus the lhs/rhs lookups and the
`toValue v = some v_goto` correspondence on the assigned value.
StoreCorr preservation is identical to `step_assign`. -/

theorem stepGoto_assign_nondet_to_stepInstr
    {P : Imperative.PureExpr} [SemanticsTautschnig.ValueCorr P]
    {pgm : Program} {pc : Nat}
    {σ_imp σ_imp' : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    (h_inj : Function.Injective nameMap)
    {x : P.Ident} {v_imp : P.Expr}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .ASSIGN)
    (h_upd : Imperative.UpdateState P σ_imp x v_imp σ_imp')
    (h_codeLhs : (SemanticsTautschnig.instrCode pgm pc).bind
                   SemanticsTautschnig.getAssignLhs = some (nameMap x))
    {rhs_g : Expr}
    (h_codeRhs : (SemanticsTautschnig.instrCode pgm pc).bind
                   SemanticsTautschnig.getAssignRhs = some rhs_g)
    (h_rhs_nondet : rhs_g.id = .side_effect .Nondet)
    {v_goto : SemanticsTautschnig.Value}
    (h_value_corr :
      (SemanticsTautschnig.ValueCorr.toValue v_imp : Option SemanticsTautschnig.Value) = some v_goto)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    ∃ σ_goto', SemanticsTautschnig.StoreCorr nameMap σ_imp' σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv pgm
        pc σ_goto (pc + 1) σ_goto' := by
  refine ⟨σ_goto.update (nameMap x) v_goto, ?_,
    .assign_nondet (instrAt_to_instrType h_at h_ty) h_codeLhs h_codeRhs h_rhs_nondet⟩
  -- StoreCorr preservation: identical to step_assign.
  intro y
  cases h_upd with
  | update h_pre h_post h_other =>
    by_cases h_eq : x = y
    · subst h_eq
      right
      refine ⟨v_imp, v_goto, h_post, h_value_corr, ?_⟩
      simp [SemanticsTautschnig.Store.update]
    · have h_imp_eq : σ_imp' y = σ_imp y := h_other y h_eq
      have h_goto_eq : (σ_goto.update (nameMap x) v_goto) (nameMap y) = σ_goto (nameMap y) := by
        simp [SemanticsTautschnig.Store.update]
        intro h_collide
        exact absurd (h_inj h_collide).symm h_eq
      rcases h_corr y with ⟨h_imp_n, h_goto_n⟩ | ⟨e, v', h_imp_s, h_to, h_goto_s⟩
      · left; exact ⟨by rw [h_imp_eq]; exact h_imp_n, by rw [h_goto_eq]; exact h_goto_n⟩
      · right
        exact ⟨e, v', by rw [h_imp_eq]; exact h_imp_s, h_to,
                        by rw [h_goto_eq]; exact h_goto_s⟩

/-! ## Closure-level bridge for `step_end_function`

Tautschnig's `StepInstr` does not have a constructor for
`END_FUNCTION`; that instruction is observed by
`SemanticsTautschnig.ExecProg.end_function`, which closes out the
multi-step relation rather than producing a `StepInstr` step.
Bridging therefore lives at the closure level: a `step_end_function`
step from this branch corresponds to *terminating* the `ExecProg`
chain via the `end_function` constructor.

The bridge below produces a one-step `ExecProg` derivation whose
post-store agrees with `σ_goto` (since `END_FUNCTION` does not
modify the store). -/

/-- Bridge for `step_end_function` at the closure level. Given a
GOTO-side `pc` whose instruction is `END_FUNCTION`, the
`ExecProg.end_function` constructor closes out the chain on `σ_goto`
without store change. The imperative-side store correspondence is
preserved by reflexivity. -/
theorem stepGoto_end_function_to_execProg
    {P : Imperative.PureExpr} [SemanticsTautschnig.ValueCorr P]
    {pgm : Program} {pc : Nat}
    {σ_imp : Imperative.SemanticStore P}
    {instr : Instruction}
    {nameMap : P.Ident → String}
    {callResult : SemanticsTautschnig.CallResultRel}
    {eval : SemanticsTautschnig.ExprEval}
    {fenv : SemanticsTautschnig.FuncEnv}
    {σ_goto : SemanticsTautschnig.Store}
    (h_at : pgm.instrAt pc = some instr) (h_ty : instr.type = .END_FUNCTION)
    (h_corr : SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto) :
    SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto ∧
    SemanticsTautschnig.ExecProg callResult eval fenv pgm
      pc σ_goto σ_goto none :=
  ⟨h_corr, .end_function (instrAt_to_instrType h_at h_ty)⟩


end CProverGOTO.Bisim
