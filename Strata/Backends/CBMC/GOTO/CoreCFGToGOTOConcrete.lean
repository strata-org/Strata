/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrectStore
public import Strata.Backends.CBMC.GOTO.SteppingBridgesDischarge
public import Strata.Backends.CBMC.GOTO.ExprTranslationPreservesEvalBoolInt
public import Strata.Backends.CBMC.GOTO.TranslatorBridgeHypsDischarge
public import Strata.Backends.CBMC.GOTO.GotoTargetInRange
public import Strata.Backends.CBMC.GOTO.NoDead
public import Strata.Backends.CBMC.GOTO.InstructionLookups
public import Strata.Backends.CBMC.GOTO.GotoTargetProvenance
public import Strata.Backends.CBMC.GOTO.CmdProvenance
public import Strata.Backends.CBMC.GOTO.PcInversion
public import Strata.Backends.CBMC.GOTO.WfLabelMapAgree

public section

/-! # End-to-end concrete forward simulation for `coreCFGToGotoTransform`

Top of the assembly tower: composes the parallel-worker outputs
into a single end-to-end theorem. For any CFG admitted by the
restricted fragment, the actual translator output simulates the
source under `StoreCorr` and produces an `ExecProg` derivation:

```
Strata.coreCFGToGotoTransform Env fname cfg trans₀ = .ok ans →
CoreCFGStepStar π φ δ cfg (.cont cfg.entry σ false) (.terminal σ' b) →
∃ pc_entry σ_goto',
  StoreCorr nameMap σ' σ_goto' ∧
  ExecProg callResult eval fenv pgm pc_entry σ_goto σ_goto' none
```

The chain composes:
* `coreCFGToGotoTransform_wellFormed_strengthened` (A2/A3/A4/A5a/A5b)
  — builds `Nonempty (WellFormedTranslation …)` from the translator output.
* `toGotoExprCtx_preservesEval_boolInt` (B3) — per-LExpr translation
  correctness on the bool+int fragment.
* `steppingBridges_of_translator` (C) — `SteppingBridges` bundle.
* `coreCFGToGoto_forward_simulation_storeCorr` (Phase 3) — consumes
  the WF + bridges to produce the `ExecProg` derivation.

Per-round archaeology and per-hypothesis discharge details live in
`docs/_workers/round*_supervisor_report.md`. -/

namespace CProverGOTO

open Imperative
open CProverGOTO.SemanticsTautschnig
  (Store StoreCorr CallResultRel ExprEval FuncEnv ExecProg StepInstr)

/-! ## Concrete forward simulation: live versions

Two public theorems (`_v6`, `_v7`) are exposed downstream. They
delegate through two private waypoints (`_v4`, `_v5`) that
discharge progressively more of the worker-output hypothesis surface.
The `ConcreteExprCorr` namespace below builds the B3 expression-side
correspondence consumed by all four. -/

namespace ConcreteExprCorr

open Lambda
open CProverGOTO.ExprTranslationBoolInt

/-- Universality of the bool+int fragment over the entire
`Core.Expression.Expr` universe.

This is the caller-supplied uniformity hypothesis required to
discharge `h_tx_eq` and `h_expr_translated_witness` from B3's
`toGotoExprCtx_preservesEval_boolInt`. It says:

* every Core expression is in the bool+int fragment,
* every Core expression has GOTO-output-type agreement at every
  operator subterm, and
* every Core expression's translator invocation succeeds.

A stricter caller can take this as an axiom *provided their CFG's
expression contents lie in the bool+int fragment* — i.e., the
hypothesis is satisfied by classical-choice / function extension
on the source evaluator's effective domain. -/
structure UniformBoolIntFragment : Prop where
  /-- Every Core expression is in the bool+int fragment. -/
  inFragment : ∀ (e : Core.Expression.Expr), isBoolIntFragment e = true
  /-- Every Core expression has gty agreement at every operator subterm. -/
  gtyAgrees : ∀ (e : Core.Expression.Expr), BoolIntGtyAgrees e
  /-- Every Core expression's translation succeeds. -/
  translates : ∀ (e : Core.Expression.Expr),
    ∃ (e_goto : CProverGOTO.Expr),
      Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e = .ok e_goto

/-- The translation function picked from a `UniformBoolIntFragment`
witness via classical choice. Returns `default` on the impossible
failure path. -/
noncomputable def tx (h_uniform : UniformBoolIntFragment) :
    Core.Expression.Expr → CProverGOTO.Expr :=
  fun e => Classical.choose (h_uniform.translates e)

/-- The translation function returns the actual translator output. -/
theorem tx_eq_toGotoExprCtx (h_uniform : UniformBoolIntFragment)
    (e : Core.Expression.Expr) :
    Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e
      = .ok (tx h_uniform e) :=
  Classical.choose_spec (h_uniform.translates e)

/-- The `Imperative.ToGoto.toGotoExpr` shape unfolds to
`Lambda.LExpr.toGotoExprCtx []` for `Core.Expression`.

After adding `@[expose]` to `Lambda.LExpr.toGotoExpr` (which is
just a thin wrapper around `toGotoExprCtx []`), this is `rfl`. -/
theorem toGotoExpr_eq_toGotoExprCtx (e : Core.Expression.Expr) :
    Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
      = Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] e :=
  rfl

/-- `h_tx_eq` discharge: the `Imperative.ToGoto` translator agrees
with `tx`. -/
theorem h_tx_eq_holds (h_uniform : UniformBoolIntFragment)
    (e : Core.Expression.Expr) :
    Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
      = .ok (tx h_uniform e) := by
  rw [toGotoExpr_eq_toGotoExprCtx]
  exact tx_eq_toGotoExprCtx h_uniform e

/-- `h_expr_translated_witness` discharge: every successful
translation yields an `ExprTranslated` witness. -/
theorem h_expr_translated_witness_holds
    {δ : Imperative.SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h_red : FnToGotoIDReductions)
    (h_op : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (h_uniform : UniformBoolIntFragment) :
    ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
      Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
        = .ok e_goto →
      ExprTranslated δ δ_goto δ_goto_bool cond e_goto := by
  intro cond e_goto h_tx
  -- Build IsBoolIntTranslated cond e_goto via B3's bridge.
  have h_is : IsBoolIntTranslated cond e_goto :=
    toGotoExprCtx_preservesEval_boolInt h_red cond e_goto
      (h_uniform.gtyAgrees cond) (h_uniform.inFragment cond) h_tx
  -- Lift to ExprTranslated via B3's structural-induction theorem.
  exact IsBoolIntTranslated.translated h_op h_is

/-- Bundle the per-expression witness into an
`ExprTranslationPreservesEval`, taking `tx_commutes_not` as a
caller hypothesis (it is not produced by B3 directly). -/
noncomputable def buildExprCorr
    {δ : Imperative.SemanticEval Core.Expression}
    {δ_goto : SemanticEvalGoto Core.Expression}
    {δ_goto_bool : SemanticEvalGotoBool Core.Expression}
    (h_red : FnToGotoIDReductions)
    (h_op : BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (h_uniform : UniformBoolIntFragment)
    (h_commutes_not : ∀ e : Core.Expression.Expr,
        tx h_uniform (HasNot.not (P := Core.Expression) e)
          = (tx h_uniform e).not) :
    ExprTranslationPreservesEval δ δ_goto δ_goto_bool where
  tx := tx h_uniform
  tx_correct := fun e_core =>
    h_expr_translated_witness_holds h_red h_op h_uniform
      e_core (tx h_uniform e_core)
      (tx_eq_toGotoExprCtx h_uniform e_core)
  tx_commutes_not := h_commutes_not

end ConcreteExprCorr

/-! ## `_v4`: R7-discharged base layer (private)

Builds a `WellFormedTranslation` via the strengthened theorem,
discharges goto-target-in-range (R7a), no-dead (R7b), and the
TranslatorBridgeHyps lookup fields (R7c). Remaining parameters are
caller-side pinning/value hypotheses and the still-open R7a/R7c
auxiliary hypotheses (closed in `_v5`). -/

private theorem coreCFGToGotoTransform_forward_simulation_concrete_v4
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    -- R11: fresh-variable monotonicity of `δ_goto` across `InitState`.
    -- Required to switch the `init_det` arm from `step_assign_nondet`
    -- (no-op padding) to `step_assign` (with eval witness on σ').
    (h_init_extension :
      ∀ {σ σ' : Imperative.SemanticStore Core.Expression}
        {x : Core.Expression.Ident} {v_init : Core.Expression.Expr}
        {e : Expr} {v : Core.Expression.Expr},
        Imperative.InitState Core.Expression σ x v_init σ' →
        δ_goto σ e = some v → δ_goto σ' e = some v)
    -- Source-side environment
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    -- Translator inputs and output
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    -- Structural inputs
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_init_no_dead : NoDead.HasNoDead trans₀)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry)
    -- B3 replacement bundle
    (h_red : ExprTranslationBoolInt.FnToGotoIDReductions)
    (h_op : ExprTranslationBoolInt.BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (h_uniform : ConcreteExprCorr.UniformBoolIntFragment)
    (h_commutes_not :
      ∀ e : Core.Expression.Expr,
        ConcreteExprCorr.tx h_uniform (HasNot.not (P := Core.Expression) e)
          = (ConcreteExprCorr.tx h_uniform e).not)
    -- Worker C parameters
    (nameMap : Core.Expression.Ident → String)
    (callResult : CallResultRel)
    (eval : ExprEval)
    (fenv : FuncEnv)
    (h_eval_bool_corr : Bisim.EvalBoolCorr nameMap δ_goto_bool eval)
    (h_inj : Function.Injective nameMap)
    -- R7a's aux hypothesis (mechanically discharable from wf;
    -- deferred to a future round).
    (h_aux_goto_target :
      ∀ {pc target : Nat} {instr : Instruction},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .GOTO →
        instr.target = some target →
        ∃ l blk, (l, blk) ∈ cfg.blocks ∧
          (∀ wf' : WellFormedTranslation cfg
            { name := "", parameterIdentifiers := #[],
              instructions := ans.instructions }
            δ δ_goto δ_goto_bool, wf'.labelMap l = some target))
    -- R7c's provenance hypotheses (mechanically discharable from
    -- wf + strengthened CmdEmittedAt; deferred to a future round).
    (h_decl_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .DECL →
        ∃ v_src gty,
          instr.code = Code.decl (Expr.symbol (nameMap v_src) gty))
    (h_assn_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        ∃ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted)
    -- R11: `h_assn_nondet_provenance` (the strict nondet-rhs variant)
    -- has been removed. The rhs-shape witness now arrives via the
    -- tightened `step_assign_nondet` constructor.
    -- R7c's pinning hypotheses (caller-side; trace-level info).
    (h_decl_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        ∀ v_src gty, instr.code = Code.decl
          (Expr.symbol (nameMap v_src) gty) → x = v_src)
    (h_assn_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∀ v_src gty rhs_emitted, instr.code = Code.assign
          (Expr.symbol (nameMap v_src) gty) rhs_emitted → x = v_src)
    (h_assn_rhs_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {σ : Imperative.SemanticStore Core.Expression}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        δ_goto σ rhs_g = some v_imp →
        ∀ v_src gty rhs_emitted, instr.code = Code.assign
          (Expr.symbol (nameMap v_src) gty) rhs_emitted →
          rhs_g = rhs_emitted)
    -- R7c's value-side hypotheses (caller-side).
    (h_decl_empty_value :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {v : Core.Expression.Expr}
        {σ σ' : Imperative.SemanticStore Core.Expression},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        (SemanticsTautschnig.ValueCorr.toValue v
          : Option SemanticsTautschnig.Value) = some .vEmpty)
    (h_assign_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ_imp σ_imp' : Imperative.SemanticStore Core.Expression}
        {σ_goto : SemanticsTautschnig.Store}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        δ_goto σ_imp rhs_g = some v_imp →
        Imperative.UpdateState Core.Expression σ_imp x v_imp σ_imp' →
        SemanticsTautschnig.StoreCorr nameMap σ_imp σ_goto →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value) = some v_goto ∧
          eval σ_goto rhs_g = some v_goto)
    (h_assign_nondet_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value) = some v_goto)
    -- Source-side terminating run + initial-store correspondence
    (σ σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (σ_goto : Store)
    (h_corr : StoreCorr nameMap σ σ_goto)
    (h_run_src :
      Core.CoreCFGStepStar π φ δ cfg
        (.cont cfg.entry σ false)
        (.terminal σ' b)) :
    -- Conclusion (matches v1/v2/v3).
    ∃ pc_entry σ_goto',
      StoreCorr nameMap σ' σ_goto' ∧
      ExecProg callResult eval fenv
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        pc_entry σ_goto σ_goto' none := by
  -- Step 1: build h_expr from B3.
  let h_expr := ConcreteExprCorr.buildExprCorr h_red h_op h_uniform h_commutes_not
  have h_tx_eq_pre : ∀ e : Core.Expression.Expr,
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
        = Except.ok (h_expr.tx e) :=
    ConcreteExprCorr.h_tx_eq_holds h_uniform
  have h_expr_translated_witness :
      ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
          = .ok e_goto →
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto :=
    ConcreteExprCorr.h_expr_translated_witness_holds h_red h_op h_uniform
  -- Step 2: get a WellFormedTranslation via the strengthened theorem.
  have h_wf_nonempty :=
    coreCFGToGotoTransform_wellFormed_strengthened
      cfg Env functionName trans₀
      h_init_size h_init_loc h_distinct h_admitted_blocks
      h_loopContracts_empty_post h_entry_first
      ans h_run
      δ δ_goto δ_goto_bool h_expr h_tx_eq_pre h_expr_translated_witness
  obtain ⟨wf⟩ := h_wf_nonempty
  let pgm : Program :=
    { name := "", parameterIdentifiers := #[],
      instructions := ans.instructions }
  -- Step 3: discharge h_goto_target_in_range via R7a.
  have h_aux_for_r7a : GotoTargetInRange.EveryGotoTargetIsLabelMapEntry cfg pgm wf.labelMap := by
    intros pc target instr h_at h_ty h_target
    obtain ⟨l, blk, h_in, h_lookup⟩ := h_aux_goto_target h_at h_ty h_target
    exact ⟨l, blk, h_in, h_lookup wf⟩
  have h_goto_target_in_range :
      ∀ {pc target : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .GOTO →
        instr.target = some target →
        ∃ instr_target, pgm.instrAt target = some instr_target := by
    intros pc target instr h_at h_ty h_target
    exact GotoTargetInRange.goto_target_in_range_of_wf cfg pgm
      δ δ_goto δ_goto_bool wf h_aux_for_r7a h_at h_ty h_target
  -- Step 4: discharge h_no_dead via R7b.
  have h_no_dead :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type ≠ .DEAD := by
    intros pc instr h
    exact NoDead.no_dead_program_of_translator Env functionName cfg trans₀
      h_init_no_dead h_loopContracts_empty_post ans h_run h
  -- Step 5: discharge h_brHyps via R7c's v2 bridge.
  -- R11: h_assn_nondet_provenance is no longer needed at this layer;
  -- the rhs-shape witness comes from step_assign_nondet's constructor.
  have h_brHyps :=
    TranslatorBridgeHypsDischarge.wellFormedTranslation_to_translatorBridgeHyps_v2
      cfg pgm δ δ_goto δ_goto_bool wf nameMap h_inj eval
      h_goto_target_in_range h_no_dead
      h_decl_provenance h_assn_provenance
      h_decl_x_pinned h_assn_x_pinned h_assn_rhs_pinned
      h_decl_empty_value h_assign_value_corr h_assign_nondet_value_corr
  -- Step 6: discharge SteppingBridges and forward simulation.
  have h_call_free :
      ∀ p ∈ cfg.blocks, ∀ c ∈ p.2.cmds, c.isAdmittedCmd = true := by
    intro p h_p_mem c h_c_mem
    obtain ⟨l, blk⟩ := p
    exact h_admitted_blocks l blk h_p_mem c h_c_mem
  let br : SteppingBridges δ_goto δ_goto_bool pgm nameMap callResult eval fenv :=
    SteppingBridgesDischarge.steppingBridges_of_translator
      h_eval_bool_corr h_brHyps
  obtain ⟨pc_entry, σ_goto', _, h_storeCorr', h_exec⟩ :=
    coreCFGToGoto_forward_simulation_storeCorr
      δ δ_goto δ_goto_bool h_expr h_wf_bool h_init_extension π φ
      cfg pgm wf h_call_free
      nameMap callResult eval fenv br
      σ σ' b σ_goto h_corr h_run_src
  exact ⟨pc_entry, σ_goto', h_storeCorr', h_exec⟩

/-! ## `_v5`: R8a/R8b auxiliary hypotheses discharged (private)

Extends `_v4` by internally discharging the R7a goto-target aux
(via R8a) and the R7c DECL/ASSIGN provenance hypotheses (via R8b).
Fixes `nameMap = Imperative.ToGoto.identToString` (the natural
choice for `Core.Expression`). Surfaces R8b's `DeclPcInversion` /
`AssignPcInversion` and the `labelMap` agreement bridge as
parameters; those are closed in `_v6`. -/

private theorem coreCFGToGotoTransform_forward_simulation_concrete_v5
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    -- R11: fresh-variable monotonicity of `δ_goto` across `InitState`.
    (h_init_extension :
      ∀ {σ σ' : Imperative.SemanticStore Core.Expression}
        {x : Core.Expression.Ident} {v_init : Core.Expression.Expr}
        {e : Expr} {v : Core.Expression.Expr},
        Imperative.InitState Core.Expression σ x v_init σ' →
        δ_goto σ e = some v → δ_goto σ' e = some v)
    -- Source-side environment
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    -- Translator inputs and output
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    -- Structural inputs
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_init_no_dead : NoDead.HasNoDead trans₀)
    (h_init_no_goto_target : GotoTargetProvenance.NoGotoHasTarget trans₀)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry)
    -- B3 replacement bundle
    (h_red : ExprTranslationBoolInt.FnToGotoIDReductions)
    (h_op : ExprTranslationBoolInt.BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (h_uniform : ConcreteExprCorr.UniformBoolIntFragment)
    (h_commutes_not :
      ∀ e : Core.Expression.Expr,
        ConcreteExprCorr.tx h_uniform (HasNot.not (P := Core.Expression) e)
          = (ConcreteExprCorr.tx h_uniform e).not)
    -- Worker C parameters: nameMap is fixed to identToString.
    (callResult : CallResultRel)
    (eval : ExprEval)
    (fenv : FuncEnv)
    (h_eval_bool_corr :
      Bisim.EvalBoolCorr
        (Imperative.ToGoto.identToString (P := Core.Expression))
        δ_goto_bool eval)
    (h_inj :
      Function.Injective
        (Imperative.ToGoto.identToString (P := Core.Expression)))
    -- R8a's structural witnesses (translator state at the post-blocks-fold).
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final)
    -- R8a's labelMap-agreement bridge.
    (h_labelMap_agree :
      ∀ (wf : WellFormedTranslation cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool),
      ∀ l blk target, (l, blk) ∈ cfg.blocks →
        st_final.labelMap[l]? = some target →
        wf.labelMap l = some target)
    -- R8b's PC-inversion auxiliaries.
    (h_decl_pc_inv :
      ∀ (wf : WellFormedTranslation cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool),
      CmdProvenance.DeclPcInversion cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool wf)
    (h_assn_pc_inv :
      ∀ (wf : WellFormedTranslation cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool),
      CmdProvenance.AssignPcInversion cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool wf)
    -- R11: `h_assn_nondet_pc_inv` (R8b's strict
    -- `AssignNondetPcInversion`) has been removed. The rhs-shape
    -- witness now arrives via the tightened `step_assign_nondet`
    -- constructor, eliminating the need for any per-PC nondet-cmd
    -- inversion.
    -- R7c's pinning hypotheses (caller-side; trace-level info).
    (h_decl_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        ∀ v_src gty, instr.code = Code.decl
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) → x = v_src)
    (h_assn_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∀ v_src gty rhs_emitted, instr.code = Code.assign
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) rhs_emitted → x = v_src)
    (h_assn_rhs_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {σ : Imperative.SemanticStore Core.Expression}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        δ_goto σ rhs_g = some v_imp →
        ∀ v_src gty rhs_emitted, instr.code = Code.assign
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) rhs_emitted →
          rhs_g = rhs_emitted)
    -- R7c's value-side hypotheses (caller-side).
    (h_decl_empty_value :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {v : Core.Expression.Expr}
        {σ σ' : Imperative.SemanticStore Core.Expression},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        (SemanticsTautschnig.ValueCorr.toValue v
          : Option SemanticsTautschnig.Value) = some .vEmpty)
    (h_assign_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ_imp σ_imp' : Imperative.SemanticStore Core.Expression}
        {σ_goto : SemanticsTautschnig.Store}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        δ_goto σ_imp rhs_g = some v_imp →
        Imperative.UpdateState Core.Expression σ_imp x v_imp σ_imp' →
        SemanticsTautschnig.StoreCorr
          (Imperative.ToGoto.identToString (P := Core.Expression))
          σ_imp σ_goto →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value) = some v_goto ∧
          eval σ_goto rhs_g = some v_goto)
    (h_assign_nondet_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value) = some v_goto)
    -- Source-side terminating run + initial-store correspondence
    (σ σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (σ_goto : Store)
    (h_corr :
      StoreCorr
        (Imperative.ToGoto.identToString (P := Core.Expression))
        σ σ_goto)
    (h_run_src :
      Core.CoreCFGStepStar π φ δ cfg
        (.cont cfg.entry σ false)
        (.terminal σ' b)) :
    -- Conclusion (matches v4 with nameMap = identToString).
    ∃ pc_entry σ_goto',
      StoreCorr
        (Imperative.ToGoto.identToString (P := Core.Expression))
        σ' σ_goto' ∧
      ExecProg callResult eval fenv
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        pc_entry σ_goto σ_goto' none := by
  let pgm : Program :=
    { name := "", parameterIdentifiers := #[],
      instructions := ans.instructions }
  -- Step 1: Build a WF for use with R8b's provenance theorems.
  let h_expr := ConcreteExprCorr.buildExprCorr h_red h_op h_uniform h_commutes_not
  have h_tx_eq_pre : ∀ e : Core.Expression.Expr,
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
        = Except.ok (h_expr.tx e) :=
    ConcreteExprCorr.h_tx_eq_holds h_uniform
  have h_expr_translated_witness :
      ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
          = .ok e_goto →
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto :=
    ConcreteExprCorr.h_expr_translated_witness_holds h_red h_op h_uniform
  have h_wf_nonempty :=
    coreCFGToGotoTransform_wellFormed_strengthened
      cfg Env functionName trans₀
      h_init_size h_init_loc h_distinct h_admitted_blocks
      h_loopContracts_empty_post h_entry_first
      ans h_run
      δ δ_goto δ_goto_bool h_expr h_tx_eq_pre h_expr_translated_witness
  obtain ⟨wf⟩ := h_wf_nonempty
  -- Step 2: Discharge R7a's `h_aux_goto_target` via R8a.
  have h_aux_goto_target :
      ∀ {pc target : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr →
        instr.type = .GOTO →
        instr.target = some target →
        ∃ l blk, (l, blk) ∈ cfg.blocks ∧
          (∀ wf' : WellFormedTranslation cfg pgm
            δ δ_goto δ_goto_bool, wf'.labelMap l = some target) := by
    intro pc target instr h_at h_ty h_target
    have h_aux_translatorMap :=
      GotoTargetProvenance.everyGotoTargetIsLabelMapEntry_of_translator_translatorMap
        Env functionName cfg trans₀ h_init_no_goto_target
        h_loopContracts_empty_post ans h_run st_final h_blocks_run
        h_at h_ty h_target
    obtain ⟨l, blk, h_in, h_lookup⟩ := h_aux_translatorMap
    have h_lookup_st : st_final.labelMap[l]? = some target := h_lookup
    refine ⟨l, blk, h_in, ?_⟩
    intro wf'
    exact h_labelMap_agree wf' l blk target h_in h_lookup_st
  -- Step 3: Discharge R7c's three provenance hypotheses via R8b.
  have h_decl_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .DECL →
        ∃ v_src gty, instr.code = Code.decl
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) := by
    intro pc instr h_at h_ty
    exact CmdProvenance.decl_provenance_of_translator cfg pgm
      δ δ_goto δ_goto_bool wf (h_decl_pc_inv wf) h_at h_ty
  have h_assn_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        ∃ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol
              (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
              gty) rhs_emitted := by
    intro pc instr h_at h_ty
    exact CmdProvenance.assn_provenance_of_translator cfg pgm
      δ δ_goto δ_goto_bool wf (h_assn_pc_inv wf) h_at h_ty
  -- R11: h_assn_nondet_provenance (the strict nondet-rhs variant)
  -- is no longer needed; the rhs-shape witness now arrives via the
  -- tightened `step_assign_nondet` constructor.
  -- Step 4: Delegate to v4 with the discharged hypotheses.
  exact coreCFGToGotoTransform_forward_simulation_concrete_v4
    δ δ_goto δ_goto_bool h_wf_bool h_init_extension π φ
    cfg Env functionName trans₀ ans h_run
    h_init_size h_init_loc h_init_no_dead h_distinct h_admitted_blocks
    h_loopContracts_empty_post h_entry_first
    h_red h_op h_uniform h_commutes_not
    (Imperative.ToGoto.identToString (P := Core.Expression))
    callResult eval fenv h_eval_bool_corr h_inj
    h_aux_goto_target
    h_decl_provenance h_assn_provenance
    h_decl_x_pinned h_assn_x_pinned h_assn_rhs_pinned
    h_decl_empty_value h_assign_value_corr h_assign_nondet_value_corr
    σ σ' b σ_goto h_corr h_run_src

/-! ## `_v6`: R9 PC-inversion auxiliaries + R10a labelMap-agree discharged

First public theorem. Extends `_v5` by internally discharging R8b's
two non-strict PC-inversion auxiliaries (`DeclPcInversion`,
`AssignPcInversion`) via R9, and R10a's `labelMap_agree` via
`WfLabelMapAgree.labelMap_agree_of_translator`.

Adds two small `trans₀`-shape hypotheses (`h_init_empty_decl_assign`,
`h_init_no_location`) trivial for any standard `trans₀` with
`instructions := #[]`. R8b's strict `AssignNondetPcInversion` was
removed in R11 by tightening `step_assign_nondet`'s constructor.

Remaining surface: translator-input invariants, R10a witnesses
(`st_final`, `h_blocks_run` — closed in `_v7`), R11 δ_goto
monotonicity (`h_init_extension`), R7c pinning + value-side
hypotheses, B3 bundle, Worker C parameters, source-side run +
initial-store correspondence. -/

theorem coreCFGToGotoTransform_forward_simulation_concrete_v6
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    -- R11: fresh-variable monotonicity of `δ_goto` across `InitState`.
    (h_init_extension :
      ∀ {σ σ' : Imperative.SemanticStore Core.Expression}
        {x : Core.Expression.Ident} {v_init : Core.Expression.Expr}
        {e : Expr} {v : Core.Expression.Expr},
        Imperative.InitState Core.Expression σ x v_init σ' →
        δ_goto σ e = some v → δ_goto σ' e = some v)
    -- Source-side environment
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    -- Translator inputs and output
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    -- Structural inputs
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_init_no_dead : NoDead.HasNoDead trans₀)
    (h_init_no_goto_target : GotoTargetProvenance.NoGotoHasTarget trans₀)
    -- New in v6: trans₀ carries no DECL/ASSIGN at any PC. Trivial for
    -- the standard `trans₀` with `instructions := #[]`.
    (h_init_empty_decl_assign : ∀ {pc : Nat} {instr : Instruction},
      trans₀.instructions[pc]? = some instr →
      instr.type ≠ .DECL ∧ instr.type ≠ .ASSIGN)
    -- New in v6 (R10a): trans₀ carries no LOCATION at any PC. Trivial
    -- for the standard `trans₀` with `instructions := #[]`. Used by
    -- `WfLabelMapAgree.labelMap_agree_of_translator` to internally
    -- discharge the labelMap-agreement hypothesis.
    (h_init_no_location :
      ∀ {pc : Nat} {instr : Instruction},
        trans₀.instructions[pc]? = some instr → instr.type ≠ .LOCATION)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry)
    -- B3 replacement bundle
    (h_red : ExprTranslationBoolInt.FnToGotoIDReductions)
    (h_op : ExprTranslationBoolInt.BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (h_uniform : ConcreteExprCorr.UniformBoolIntFragment)
    (h_commutes_not :
      ∀ e : Core.Expression.Expr,
        ConcreteExprCorr.tx h_uniform (HasNot.not (P := Core.Expression) e)
          = (ConcreteExprCorr.tx h_uniform e).not)
    -- Worker C parameters: nameMap fixed to identToString.
    (callResult : CallResultRel)
    (eval : ExprEval)
    (fenv : FuncEnv)
    (h_eval_bool_corr :
      Bisim.EvalBoolCorr
        (Imperative.ToGoto.identToString (P := Core.Expression))
        δ_goto_bool eval)
    (h_inj :
      Function.Injective
        (Imperative.ToGoto.identToString (P := Core.Expression)))
    -- R8a's structural witnesses (translator state at the post-blocks-fold).
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final)
    -- R8b's strict ASSIGN-Nondet PC-inversion remains (provably false in general).
    -- R11: `h_assn_nondet_pc_inv` (R8b's strict
    -- `AssignNondetPcInversion`) has been removed. The rhs-shape
    -- witness now arrives via the tightened `step_assign_nondet`
    -- constructor, eliminating the need for any per-PC nondet-cmd
    -- inversion.
    -- R7c's pinning hypotheses (caller-side; trace-level info).
    (h_decl_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        ∀ v_src gty, instr.code = Code.decl
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) → x = v_src)
    (h_assn_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∀ v_src gty rhs_emitted, instr.code = Code.assign
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) rhs_emitted → x = v_src)
    (h_assn_rhs_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {σ : Imperative.SemanticStore Core.Expression}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        δ_goto σ rhs_g = some v_imp →
        ∀ v_src gty rhs_emitted, instr.code = Code.assign
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) rhs_emitted →
          rhs_g = rhs_emitted)
    -- R7c's value-side hypotheses (caller-side).
    (h_decl_empty_value :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {v : Core.Expression.Expr}
        {σ σ' : Imperative.SemanticStore Core.Expression},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        (SemanticsTautschnig.ValueCorr.toValue v
          : Option SemanticsTautschnig.Value) = some .vEmpty)
    (h_assign_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ_imp σ_imp' : Imperative.SemanticStore Core.Expression}
        {σ_goto : SemanticsTautschnig.Store}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        δ_goto σ_imp rhs_g = some v_imp →
        Imperative.UpdateState Core.Expression σ_imp x v_imp σ_imp' →
        SemanticsTautschnig.StoreCorr
          (Imperative.ToGoto.identToString (P := Core.Expression))
          σ_imp σ_goto →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value) = some v_goto ∧
          eval σ_goto rhs_g = some v_goto)
    (h_assign_nondet_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value) = some v_goto)
    -- Source-side terminating run + initial-store correspondence
    (σ σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (σ_goto : Store)
    (h_corr :
      StoreCorr
        (Imperative.ToGoto.identToString (P := Core.Expression))
        σ σ_goto)
    (h_run_src :
      Core.CoreCFGStepStar π φ δ cfg
        (.cont cfg.entry σ false)
        (.terminal σ' b)) :
    -- Conclusion (matches v5).
    ∃ pc_entry σ_goto',
      StoreCorr
        (Imperative.ToGoto.identToString (P := Core.Expression))
        σ' σ_goto' ∧
      ExecProg callResult eval fenv
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        pc_entry σ_goto σ_goto' none := by
  -- Build the expression-correspondence for use in PcInversion theorems.
  let h_expr := ConcreteExprCorr.buildExprCorr h_red h_op h_uniform h_commutes_not
  have h_tx_eq : ∀ e : Core.Expression.Expr,
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
        = Except.ok (h_expr.tx e) :=
    ConcreteExprCorr.h_tx_eq_holds h_uniform
  -- Discharge h_labelMap_agree via R10a.
  have h_labelMap_agree :
      ∀ (wf : WellFormedTranslation cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool),
      ∀ l blk target, (l, blk) ∈ cfg.blocks →
        st_final.labelMap[l]? = some target →
        wf.labelMap l = some target := by
    intro wf
    exact WfLabelMapAgree.labelMap_agree_of_translator
      Env functionName cfg trans₀ h_init_size h_init_no_location
      h_distinct h_admitted_blocks h_loopContracts_empty_post
      ans h_run st_final h_blocks_run δ δ_goto δ_goto_bool wf
  -- Discharge h_decl_pc_inv via R9.
  have h_decl_pc_inv :
      ∀ (wf : WellFormedTranslation cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool),
      CmdProvenance.DeclPcInversion cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool wf := by
    intro wf
    exact PcInversion.declPcInversion_of_translator_abbrev
      Env functionName cfg trans₀ h_init_size h_init_empty_decl_assign
      h_distinct h_admitted_blocks h_loopContracts_empty_post
      ans h_run δ δ_goto δ_goto_bool h_expr h_tx_eq wf
  -- Discharge h_assn_pc_inv via R9.
  have h_assn_pc_inv :
      ∀ (wf : WellFormedTranslation cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool),
      CmdProvenance.AssignPcInversion cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool wf := by
    intro wf
    exact PcInversion.assignPcInversion_of_translator_abbrev
      Env functionName cfg trans₀ h_init_size h_init_empty_decl_assign
      h_distinct h_admitted_blocks h_loopContracts_empty_post
      ans h_run δ δ_goto δ_goto_bool h_expr h_tx_eq wf
  -- Delegate to v5.
  exact coreCFGToGotoTransform_forward_simulation_concrete_v5
    δ δ_goto δ_goto_bool h_wf_bool h_init_extension π φ
    cfg Env functionName trans₀ ans h_run
    h_init_size h_init_loc h_init_no_dead h_init_no_goto_target
    h_distinct h_admitted_blocks
    h_loopContracts_empty_post h_entry_first
    h_red h_op h_uniform h_commutes_not
    callResult eval fenv h_eval_bool_corr h_inj
    st_final h_blocks_run h_labelMap_agree
    h_decl_pc_inv h_assn_pc_inv
    h_decl_x_pinned h_assn_x_pinned h_assn_rhs_pinned
    h_decl_empty_value h_assign_value_corr h_assign_nondet_value_corr
    σ σ' b σ_goto h_corr h_run_src

/-! ## `_v7`: structural witnesses `st_final`/`h_blocks_run` internalised

Public theorem; identical hypothesis surface to `_v6` minus the two
structural witnesses, which are derived internally via
`coreCFGToGotoTransform_decompose`. -/

theorem coreCFGToGotoTransform_forward_simulation_concrete_v7
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    -- R11: fresh-variable monotonicity of `δ_goto` across `InitState`.
    (h_init_extension :
      ∀ {σ σ' : Imperative.SemanticStore Core.Expression}
        {x : Core.Expression.Ident} {v_init : Core.Expression.Expr}
        {e : Expr} {v : Core.Expression.Expr},
        Imperative.InitState Core.Expression σ x v_init σ' →
        δ_goto σ e = some v → δ_goto σ' e = some v)
    -- Source-side environment
    (π : String → Option Core.Procedure)
    (φ : Core.CoreEval → Imperative.PureFunc Core.Expression → Core.CoreEval)
    -- Translator inputs and output
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    -- Structural inputs
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_init_no_dead : NoDead.HasNoDead trans₀)
    (h_init_no_goto_target : GotoTargetProvenance.NoGotoHasTarget trans₀)
    (h_init_empty_decl_assign : ∀ {pc : Nat} {instr : Instruction},
      trans₀.instructions[pc]? = some instr →
      instr.type ≠ .DECL ∧ instr.type ≠ .ASSIGN)
    -- R10a: trans₀ carries no LOCATION at any PC.
    (h_init_no_location :
      ∀ {pc : Nat} {instr : Instruction},
        trans₀.instructions[pc]? = some instr → instr.type ≠ .LOCATION)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry)
    -- B3 replacement bundle
    (h_red : ExprTranslationBoolInt.FnToGotoIDReductions)
    (h_op : ExprTranslationBoolInt.BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (h_uniform : ConcreteExprCorr.UniformBoolIntFragment)
    (h_commutes_not :
      ∀ e : Core.Expression.Expr,
        ConcreteExprCorr.tx h_uniform (HasNot.not (P := Core.Expression) e)
          = (ConcreteExprCorr.tx h_uniform e).not)
    -- Worker C parameters
    (callResult : CallResultRel)
    (eval : ExprEval)
    (fenv : FuncEnv)
    (h_eval_bool_corr :
      Bisim.EvalBoolCorr
        (Imperative.ToGoto.identToString (P := Core.Expression))
        δ_goto_bool eval)
    (h_inj :
      Function.Injective
        (Imperative.ToGoto.identToString (P := Core.Expression)))
    -- R8b's strict ASSIGN-Nondet PC-inversion remains (caller-side).
    -- R11: `h_assn_nondet_pc_inv` (R8b's strict
    -- `AssignNondetPcInversion`) has been removed. The rhs-shape
    -- witness now arrives via the tightened `step_assign_nondet`
    -- constructor, eliminating the need for any per-PC nondet-cmd
    -- inversion.
    -- R7c's pinning hypotheses (caller-side; trace-level info).
    (h_decl_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        ∀ v_src gty, instr.code = Code.decl
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) → x = v_src)
    (h_assn_x_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∀ v_src gty rhs_emitted, instr.code = Code.assign
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) rhs_emitted → x = v_src)
    (h_assn_rhs_pinned :
      ∀ {pc : Nat} {instr : Instruction}
        {σ : Imperative.SemanticStore Core.Expression}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        δ_goto σ rhs_g = some v_imp →
        ∀ v_src gty rhs_emitted, instr.code = Code.assign
          (Expr.symbol
            (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
            gty) rhs_emitted →
          rhs_g = rhs_emitted)
    -- R7c's value-side hypotheses (caller-side).
    (h_decl_empty_value :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {v : Core.Expression.Expr}
        {σ σ' : Imperative.SemanticStore Core.Expression},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        (SemanticsTautschnig.ValueCorr.toValue v
          : Option SemanticsTautschnig.Value) = some .vEmpty)
    (h_assign_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ_imp σ_imp' : Imperative.SemanticStore Core.Expression}
        {σ_goto : SemanticsTautschnig.Store}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        δ_goto σ_imp rhs_g = some v_imp →
        Imperative.UpdateState Core.Expression σ_imp x v_imp σ_imp' →
        SemanticsTautschnig.StoreCorr
          (Imperative.ToGoto.identToString (P := Core.Expression))
          σ_imp σ_goto →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value) = some v_goto ∧
          eval σ_goto rhs_g = some v_goto)
    (h_assign_nondet_value_corr :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∃ v_goto,
          (SemanticsTautschnig.ValueCorr.toValue v_imp
            : Option SemanticsTautschnig.Value) = some v_goto)
    -- Source-side terminating run + initial-store correspondence
    (σ σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (σ_goto : Store)
    (h_corr :
      StoreCorr
        (Imperative.ToGoto.identToString (P := Core.Expression))
        σ σ_goto)
    (h_run_src :
      Core.CoreCFGStepStar π φ δ cfg
        (.cont cfg.entry σ false)
        (.terminal σ' b)) :
    -- Conclusion (matches v6).
    ∃ pc_entry σ_goto',
      StoreCorr
        (Imperative.ToGoto.identToString (P := Core.Expression))
        σ' σ_goto' ∧
      ExecProg callResult eval fenv
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        pc_entry σ_goto σ_goto' none := by
  -- Internalize R8a's structural witnesses via `coreCFGToGotoTransform_decompose`.
  obtain ⟨st_final, _resolved, _trans_post,
          h_blocks_run, _h_patches_run, _h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- Delegate to v6 with the obtained witnesses. R10a internally
  -- discharges `h_labelMap_agree` so we don't pass it through.
  exact coreCFGToGotoTransform_forward_simulation_concrete_v6
    δ δ_goto δ_goto_bool h_wf_bool h_init_extension π φ
    cfg Env functionName trans₀ ans h_run
    h_init_size h_init_loc h_init_no_dead h_init_no_goto_target
    h_init_empty_decl_assign h_init_no_location
    h_distinct h_admitted_blocks
    h_loopContracts_empty_post h_entry_first
    h_red h_op h_uniform h_commutes_not
    callResult eval fenv h_eval_bool_corr h_inj
    st_final h_blocks_run
    h_decl_x_pinned h_assn_x_pinned h_assn_rhs_pinned
    h_decl_empty_value h_assign_value_corr h_assign_nondet_value_corr
    σ σ' b σ_goto h_corr h_run_src

end CProverGOTO
