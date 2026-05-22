/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrectStore
public import Strata.Backends.CBMC.GOTO.SteppingBridgesDischarge
public import Strata.Backends.CBMC.GOTO.ExprTranslationPreservesEvalBoolInt

public section

/-! # End-to-end concrete forward simulation for `coreCFGToGotoTransform`

This module composes the parallel-worker outputs into a single
end-to-end theorem stating that, for any CFG admitted by the
restricted fragment, the actual translator output simulates the
source under `StoreCorr` and produces an `ExecProg` derivation:

```
coreCFGToGotoTransform_forward_simulation_concrete :
  ...
  Strata.coreCFGToGotoTransform Env fname cfg trans₀ = .ok ans →
  CoreCFGStepStar π φ δ cfg (.cont cfg.entry σ false) (.terminal σ' b) →
  ∃ pc_entry σ_goto',
    StoreCorr nameMap σ' σ_goto' ∧
    ExecProg callResult eval fenv pgm pc_entry σ_goto σ_goto' none
```

The chain composes:

* **A2/A3/A4/A5a/A5b** —
  `coreCFGToGotoTransform_wellFormed_strengthened`
  (`CoreCFGToGotoTransformWF.lean`): produces a
  `Nonempty (WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)`
  from the translator output. **All five A4 hypothesis-parameter
  fields closed in round 5**, so this only needs the structural
  inputs + caller-supplied evaluator-translation hypotheses.
* **B3** — `toGotoExprCtx_preservesEval_boolInt`
  (`ExprTranslationPreservesEvalBoolInt.lean`): per-LExpr translation
  correctness on the bool+int fragment.
* **C** — `steppingBridges_of_translator`
  (`SteppingBridgesDischarge.lean`): `SteppingBridges` bundle from
  `EvalBoolCorr` + `TranslatorBridgeHyps`.
* **Phase 3** — `coreCFGToGoto_forward_simulation_storeCorr`
  (`CoreCFGToGOTOCorrectStore.lean`): consumes a `WellFormedTranslation`
  and a `SteppingBridges` to produce an `ExecProg` derivation.

The theorem still takes a number of hypotheses as parameters
(remaining open obligations after rounds 1-5):

* `h_loopContracts_empty_post` — A3's loop-contracts simplification
  (the patch step's guard-tweak branch is sidestepped by assuming
  no loop contracts in the translator state). Inhabited for any
  CFG without `specLoopInvariant`/`specDecreases` metadata.
* `h_distinct` — `BlockLabelsDistinct cfg.blocks`. The source CFG
  must have pairwise distinct block labels (a global invariant of
  any well-formed input).
* `h_admitted_blocks` — every Cmd is `isAdmittedCmd` (no `.call`,
  no `.cover`, no nondet `.init`). The original Gap A scope.
* `h_entry_first` — `cfg.blocks.head?.map Prod.fst = some cfg.entry`.
  The translator already checks and rejects on violation; for any
  CFG the translator accepts, this holds.
* `h_init_size` / `h_init_loc` — translator-state-initial
  invariants (typically `trans₀.instructions = #[]` and
  `trans₀.nextLoc = 0`, in which case both are trivial).
* `h_expr_corr` — caller-supplied `ExprTranslationPreservesEval`.
  B3 produces this for the bool+int fragment.
* `h_tx_eq` — technical equality between
  `Imperative.ToGoto.toGotoExpr` and `h_expr_corr.tx`.
* `h_expr_translated_witness` — finer-grained translation
  correctness needed by the cond-goto-guards layout proof.
* `h_brHyps` — Worker C's `TranslatorBridgeHyps` (per-PC structural
  facts about the actual translator output).
* `h_eval_bool_corr` — `EvalBoolCorr` (target/target evaluator
  agreement; caller-supplied).
* `h_corr` — initial-store `StoreCorr`.

This file is the top of the assembly tower. It does not introduce
any new proof obligations beyond what the workers already produced;
it just shows that the pieces compose. -/

namespace CProverGOTO

open Imperative
open CProverGOTO.SemanticsTautschnig
  (Store StoreCorr CallResultRel ExprEval FuncEnv ExecProg StepInstr)

/-- End-to-end concrete forward simulation for `coreCFGToGotoTransform`.

After round 5, the WF discharge requires only the structural
hypotheses and caller-supplied evaluator hypotheses; A4's five
"open" layout-field hypotheses have been closed by A5a/A5b. -/
theorem coreCFGToGotoTransform_forward_simulation_concrete
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    -- Source-side environment for CFG runs
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
    -- Caller-supplied evaluator hypotheses
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr.tx e))
    (h_expr_translated_witness :
      ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
          = .ok e_goto →
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto)
    -- Worker C parameters for the SteppingBridges discharge
    (nameMap : Core.Expression.Ident → String)
    [SemanticsTautschnig.ValueCorr Core.Expression]
    (callResult : CallResultRel)
    (eval : ExprEval)
    (fenv : FuncEnv)
    (h_eval_bool_corr :
      Bisim.EvalBoolCorr nameMap δ_goto_bool eval)
    (h_brHyps :
      SteppingBridgesDischarge.TranslatorBridgeHyps
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        nameMap δ_goto eval)
    -- Source-side terminating run + initial-store correspondence
    (σ σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (σ_goto : Store)
    (h_corr : StoreCorr nameMap σ σ_goto)
    (h_run_src :
      Core.CoreCFGStepStar π φ δ cfg
        (.cont cfg.entry σ false)
        (.terminal σ' b)) :
    -- Conclusion: ExecProg derivation matching the source run
    ∃ pc_entry σ_goto',
      StoreCorr nameMap σ' σ_goto' ∧
      ExecProg callResult eval fenv
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        pc_entry σ_goto σ_goto' none := by
  -- Step 1: A5-strengthened WF theorem produces a Nonempty witness.
  have h_wf_nonempty :=
    coreCFGToGotoTransform_wellFormed_strengthened
      cfg Env functionName trans₀
      h_init_size h_init_loc h_distinct h_admitted_blocks
      h_loopContracts_empty_post h_entry_first
      ans h_run
      δ δ_goto δ_goto_bool h_expr h_tx_eq h_expr_translated_witness
  -- Step 2: extract a concrete WellFormedTranslation.
  obtain ⟨wf⟩ := h_wf_nonempty
  -- Step 3: discharge SteppingBridges from C's theorem.
  let pgm : Program :=
    { name := "", parameterIdentifiers := #[],
      instructions := ans.instructions }
  have h_call_free :
      ∀ p ∈ cfg.blocks, ∀ c ∈ p.2.cmds, c.isAdmittedCmd = true := by
    intro p h_p_mem c h_c_mem
    obtain ⟨l, blk⟩ := p
    exact h_admitted_blocks l blk h_p_mem c h_c_mem
  let br : SteppingBridges δ_goto δ_goto_bool pgm nameMap callResult eval fenv :=
    SteppingBridgesDischarge.steppingBridges_of_translator
      h_eval_bool_corr h_brHyps
  -- Step 4: invoke the storeCorr forward simulation, then drop the
  -- `wf.labelMap cfg.entry` projection from the conclusion.
  obtain ⟨pc_entry, σ_goto', _, h_storeCorr', h_exec⟩ :=
    coreCFGToGoto_forward_simulation_storeCorr
      δ δ_goto δ_goto_bool h_expr h_wf_bool π φ
      cfg pgm wf h_call_free
      nameMap callResult eval fenv br
      σ σ' b σ_goto h_corr h_run_src
  exact ⟨pc_entry, σ_goto', h_storeCorr', h_exec⟩

/-! ## v2: discharging `h_tx_eq` and `h_expr_translated_witness`

This section closes two of the v1 hypotheses in
`coreCFGToGotoTransform_forward_simulation_concrete`:

* `h_tx_eq` — the technical identity
  `∀ e, Imperative.ToGoto.toGotoExpr e = .ok (h_expr_corr.tx e)`.
* `h_expr_translated_witness` —
  `∀ cond e_goto, Lambda.LExpr.toGotoExprCtx [] cond = .ok e_goto →
   ExprTranslated δ δ_goto δ_goto_bool cond e_goto`.

Both follow from B3's
`ExprTranslationBoolInt.toGotoExprCtx_preservesEval_boolInt` plus a
"uniformity" hypothesis on the source LExprs the program references.

### Hypothesis bundle

For B3 to apply, the caller must witness:

* `h_red : FnToGotoIDReductions` — operator-name → GOTO-id
  reductions (each defining equation is provable by `rfl`/`decide`
  for any concrete operator string).
* `h_op : BoolIntOpHypotheses δ δ_goto δ_goto_bool` — per-operator
  source/target evaluator agreements.
* `h_uniform : UniformBoolIntFragment` — for *every* Core
  expression, fragment membership and gty-agreement hold AND the
  translator succeeds.

The first two are directly B3's interface. The third is a
caller-supplied uniformity claim — it is *false* for arbitrary
`Core.Expression.Expr` values (the translator fails on
abstractions, etc.), but it is *valid* for any restricted
evaluation context the caller wishes to reason about.

In practice the caller proves `h_uniform` either:

1. By restricting `δ` (the source semantic-evaluator) so that the
   only expressions ever evaluated come from a CFG whose static
   contents lie in the bool+int fragment — at which point
   `h_uniform` reduces to a finite check on the program text. -/

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

/-- **v2 of the end-to-end concrete forward simulation theorem.**

This version *internally discharges* `h_tx_eq` and
`h_expr_translated_witness` from a more "discoverable" hypothesis
bundle:

* `h_red : FnToGotoIDReductions` — B3's operator-name → GOTO-id
  reductions.
* `h_op : BoolIntOpHypotheses` — B3's per-operator source/target
  evaluator agreements.
* `h_uniform : UniformBoolIntFragment` — every Core expression is
  in the bool+int fragment + has gty agreements + translates
  successfully.
* `h_commutes_not` — `tx (HasNot.not e) = (tx e).not` for the `tx`
  picked by `h_uniform`. This single side-equation encodes the
  caller's promise that the source-side `HasNot.not` and the
  target-side `Expr.not` agree on translated expressions, parallel
  to v1's `h_expr.tx_commutes_not`.

All other hypotheses (translator structural inputs, evaluator
hypotheses, store-corr) match v1.

After the v2 obligations are met, this theorem delegates to v1
without requiring the caller to construct
`ExprTranslationPreservesEval`, `h_tx_eq`, or
`h_expr_translated_witness` by hand. -/
theorem coreCFGToGotoTransform_forward_simulation_concrete_v2
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
    -- Source-side environment for CFG runs
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
    -- Replacement bundle: B3 + uniformity + commutes-not.
    (h_red : ExprTranslationBoolInt.FnToGotoIDReductions)
    (h_op : ExprTranslationBoolInt.BoolIntOpHypotheses δ δ_goto δ_goto_bool)
    (h_uniform : ConcreteExprCorr.UniformBoolIntFragment)
    (h_commutes_not :
      ∀ e : Core.Expression.Expr,
        ConcreteExprCorr.tx h_uniform (HasNot.not (P := Core.Expression) e)
          = (ConcreteExprCorr.tx h_uniform e).not)
    -- Worker C parameters for the SteppingBridges discharge
    (nameMap : Core.Expression.Ident → String)
    [SemanticsTautschnig.ValueCorr Core.Expression]
    (callResult : CallResultRel)
    (eval : ExprEval)
    (fenv : FuncEnv)
    (h_eval_bool_corr :
      Bisim.EvalBoolCorr nameMap δ_goto_bool eval)
    (h_brHyps :
      SteppingBridgesDischarge.TranslatorBridgeHyps
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        nameMap δ_goto eval)
    -- Source-side terminating run + initial-store correspondence
    (σ σ' : Imperative.SemanticStore Core.Expression) (b : Bool)
    (σ_goto : Store)
    (h_corr : StoreCorr nameMap σ σ_goto)
    (h_run_src :
      Core.CoreCFGStepStar π φ δ cfg
        (.cont cfg.entry σ false)
        (.terminal σ' b)) :
    -- Conclusion (matches v1).
    ∃ pc_entry σ_goto',
      StoreCorr nameMap σ' σ_goto' ∧
      ExecProg callResult eval fenv
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        pc_entry σ_goto σ_goto' none := by
  -- Build h_expr from B3 + uniformity.
  let h_expr := ConcreteExprCorr.buildExprCorr h_red h_op h_uniform h_commutes_not
  -- Discharge h_tx_eq.
  have h_tx_eq : ∀ e : Core.Expression.Expr,
      Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
        = Except.ok (h_expr.tx e) :=
    ConcreteExprCorr.h_tx_eq_holds h_uniform
  -- Discharge h_expr_translated_witness.
  have h_expr_translated_witness :
      ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
          = .ok e_goto →
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto :=
    ConcreteExprCorr.h_expr_translated_witness_holds h_red h_op h_uniform
  -- Delegate to v1.
  exact coreCFGToGotoTransform_forward_simulation_concrete
    δ δ_goto δ_goto_bool h_expr h_wf_bool π φ
    cfg Env functionName trans₀ ans h_run
    h_init_size h_init_loc h_distinct h_admitted_blocks
    h_loopContracts_empty_post h_entry_first
    h_tx_eq h_expr_translated_witness
    nameMap callResult eval fenv h_eval_bool_corr h_brHyps
    σ σ' b σ_goto h_corr h_run_src

end CProverGOTO
