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

/-! ## v3: replacing `h_brHyps` with R6a's bridge

`coreCFGToGotoTransform_forward_simulation_concrete_v3` extends v2
by also discharging the `h_brHyps : TranslatorBridgeHyps` input via
Worker R6a's `wellFormedTranslation_to_translatorBridgeHyps` bridge.

The caller no longer has to construct a `TranslatorBridgeHyps`
witness explicitly. Instead they supply:

* `nameMap` + `Function.Injective nameMap`,
* eight per-PC bridge hypotheses (the same eight that R6a's bridge
  consumes — most are caller obligations about the source/target
  evaluator agreement that the structural `WellFormedTranslation`
  cannot discharge alone).

This is the "category-2 hypotheses fully internalised" milestone:
v3 takes only translator-input invariants and caller obligations
about evaluator agreement; everything else is discharged from the
translator's own structural soundness.

The remaining hypotheses on `_v3` are exactly the
"category-3 caller obligations" from the round-5 supervisor report:

* `h_eval_bool_corr` — target/target evaluator agreement.
* `h_corr` — initial-store correspondence.
* `h_run_src` — the source-side run.
* `h_red`, `h_op`, `h_uniform`, `h_commutes_not` — B3's expression-
  side hypotheses.
* `h_inj` — `Function.Injective nameMap`.
* The eight per-PC bridge hypotheses (shape-and-evaluator
  obligations on the actual translator output).
* The translator-input invariants (`h_init_size`, `h_init_loc`,
  `h_distinct`, `h_admitted_blocks`, `h_loopContracts_empty_post`,
  `h_entry_first`).

`h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool` rounds out
the list. -/

theorem coreCFGToGotoTransform_forward_simulation_concrete_v3
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
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
    -- B3 replacement bundle for the expression side (same as v2).
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
    -- R6a's bridge inputs (replaces v1's `h_brHyps`).
    (h_inj : Function.Injective nameMap)
    (h_goto_target_in_range :
      ∀ {pc target : Nat} {instr : Instruction},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
            = some instr →
        instr.type = .GOTO →
        instr.target = some target →
        ∃ instr_target,
          ({ name := "", parameterIdentifiers := #[],
             instructions := ans.instructions } : Program).instrAt target
            = some instr_target)
    (h_no_dead :
      ∀ {pc : Nat} {instr : Instruction},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
            = some instr →
        instr.type ≠ .DEAD)
    (h_decl_lookup :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
            = some instr →
        instr.type = .DECL →
        Imperative.InitState Core.Expression σ x v σ' →
        (SemanticsTautschnig.instrCode
            { name := "", parameterIdentifiers := #[],
              instructions := ans.instructions } pc).bind
          SemanticsTautschnig.getSymbolName = some (nameMap x))
    (h_assign_lookup :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {rhs_g : Expr} {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
            = some instr →
        instr.type = .ASSIGN →
        δ_goto σ rhs_g = some v_imp →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        (SemanticsTautschnig.instrCode
            { name := "", parameterIdentifiers := #[],
              instructions := ans.instructions } pc).bind
            SemanticsTautschnig.getAssignLhs = some (nameMap x) ∧
        (SemanticsTautschnig.instrCode
            { name := "", parameterIdentifiers := #[],
              instructions := ans.instructions } pc).bind
            SemanticsTautschnig.getAssignRhs = some rhs_g)
    (h_assign_nondet_lookup :
      ∀ {pc : Nat} {instr : Instruction} {x : Core.Expression.Ident}
        {σ σ' : Imperative.SemanticStore Core.Expression}
        {v_imp : Core.Expression.Expr},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
            = some instr →
        instr.type = .ASSIGN →
        Imperative.UpdateState Core.Expression σ x v_imp σ' →
        ∃ rhs_g,
          (SemanticsTautschnig.instrCode
              { name := "", parameterIdentifiers := #[],
                instructions := ans.instructions } pc).bind
              SemanticsTautschnig.getAssignLhs = some (nameMap x) ∧
          (SemanticsTautschnig.instrCode
              { name := "", parameterIdentifiers := #[],
                instructions := ans.instructions } pc).bind
              SemanticsTautschnig.getAssignRhs = some rhs_g ∧
          rhs_g.id = .side_effect .Nondet)
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
    -- Conclusion (matches v1 / v2).
    ∃ pc_entry σ_goto',
      StoreCorr nameMap σ' σ_goto' ∧
      ExecProg callResult eval fenv
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        pc_entry σ_goto σ_goto' none := by
  -- Step 1: build h_expr from B3 + uniformity (same as v2).
  let h_expr := ConcreteExprCorr.buildExprCorr h_red h_op h_uniform h_commutes_not
  -- Step 2: get a WellFormedTranslation via the strengthened WF theorem.
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
  -- Step 3: discharge h_brHyps via R6a's bridge.
  let pgm : Program :=
    { name := "", parameterIdentifiers := #[],
      instructions := ans.instructions }
  have h_brHyps :=
    TranslatorBridgeHypsDischarge.wellFormedTranslation_to_translatorBridgeHyps
      cfg pgm δ δ_goto δ_goto_bool wf nameMap h_inj eval
      h_goto_target_in_range h_no_dead
      h_decl_lookup h_assign_lookup h_assign_nondet_lookup
      h_decl_empty_value h_assign_value_corr h_assign_nondet_value_corr
  -- Step 4: discharge SteppingBridges from C's theorem.
  have h_call_free :
      ∀ p ∈ cfg.blocks, ∀ c ∈ p.2.cmds, c.isAdmittedCmd = true := by
    intro p h_p_mem c h_c_mem
    obtain ⟨l, blk⟩ := p
    exact h_admitted_blocks l blk h_p_mem c h_c_mem
  let br : SteppingBridges δ_goto δ_goto_bool pgm nameMap callResult eval fenv :=
    SteppingBridgesDischarge.steppingBridges_of_translator
      h_eval_bool_corr h_brHyps
  -- Step 5: invoke the storeCorr forward simulation.
  obtain ⟨pc_entry, σ_goto', _, h_storeCorr', h_exec⟩ :=
    coreCFGToGoto_forward_simulation_storeCorr
      δ δ_goto δ_goto_bool h_expr h_wf_bool π φ
      cfg pgm wf h_call_free
      nameMap callResult eval fenv br
      σ σ' b σ_goto h_corr h_run_src
  exact ⟨pc_entry, σ_goto', h_storeCorr', h_exec⟩

/-! ## v4: also discharge `h_goto_target_in_range`, `h_no_dead`, and
the lookup fields via R7a/R7b/R7c

`coreCFGToGotoTransform_forward_simulation_concrete_v4` extends v3
by internally discharging:

* **`h_goto_target_in_range`** via R7a's `goto_target_in_range_of_wf`
  (modulo a small `EveryGotoTargetIsLabelMapEntry` aux hypothesis).
* **`h_no_dead`** via R7b's `no_dead_program_of_translator` (using
  the empty translator-state base case `HasNoDead trans₀` —
  trivially satisfied for any `trans₀.instructions = #[]` initial
  state).
* **`h_decl_lookup` / `h_assign_lookup` / `h_assign_nondet_lookup`**
  via R7c's `wellFormedTranslation_to_translatorBridgeHyps_v2`
  (modulo provenance + pinning hypotheses; the provenance
  hypotheses are mechanically discharable from `wf` and
  `CmdEmittedAt` per R7c's report).

The remaining hypotheses on `_v4` are all category-3 (genuine
caller obligations) plus the translator-input invariants:

* Translator-input invariants (mostly trivial for `stmtsToCFG`
  + empty initial state).
* B3 expression-side bundle.
* `nameMap` + `Function.Injective nameMap`.
* R7a's `EveryGotoTargetIsLabelMapEntry` aux (mechanically
  discharable; deferred).
* R7c's provenance hypotheses (mechanically discharable;
  deferred).
* R7c's pinning hypotheses (irreducible at the WF layer; trace-
  level caller obligation).
* R7c's value-side hypotheses (caller obligations about source
  ↔ target evaluator agreement).
* Target-side `h_eval_bool_corr` and `h_init_no_dead`.
* Source-side: `σ`, `σ'`, `b`, `σ_goto`, `h_corr`, `h_run_src`. -/

theorem coreCFGToGotoTransform_forward_simulation_concrete_v4
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
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
    (h_assn_nondet_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        ({ name := "", parameterIdentifiers := #[],
           instructions := ans.instructions } : Program).instrAt pc
          = some instr →
        instr.type = .ASSIGN →
        ∃ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol (nameMap v_src) gty) rhs_emitted ∧
          rhs_emitted.id = .side_effect .Nondet)
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
  have h_brHyps :=
    TranslatorBridgeHypsDischarge.wellFormedTranslation_to_translatorBridgeHyps_v2
      cfg pgm δ δ_goto δ_goto_bool wf nameMap h_inj eval
      h_goto_target_in_range h_no_dead
      h_decl_provenance h_assn_provenance h_assn_nondet_provenance
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
      δ δ_goto δ_goto_bool h_expr h_wf_bool π φ
      cfg pgm wf h_call_free
      nameMap callResult eval fenv br
      σ σ' b σ_goto h_corr h_run_src
  exact ⟨pc_entry, σ_goto', h_storeCorr', h_exec⟩

/-! ## v5: also discharge the R7 auxiliary hypotheses via R8a/R8b

`coreCFGToGotoTransform_forward_simulation_concrete_v5` extends v4 by
internally discharging the three "mechanically-discharable structural
auxiliaries" left as parameters in v4:

* **`h_aux_goto_target`** (R7a's `EveryGotoTargetIsLabelMapEntry`)
  via R8a's `everyGotoTargetIsLabelMapEntry_of_translator_translatorMap`
  bridged to `wf.labelMap` via the caller-supplied `h_labelMap_agree`
  hypothesis (trivially provable for any WF built via the strengthened
  theorem, since that WF's `labelMap` is definitionally
  `hashMapToLabelMap st_final.labelMap`).
* **`h_decl_provenance` / `h_assn_provenance` /
  `h_assn_nondet_provenance`** via R8b's three theorems. R8b takes
  three PC-inversion auxiliaries (`DeclPcInversion`,
  `AssignPcInversion`, `AssignNondetPcInversion`) characterizing
  which translator constructor emitted each DECL/ASSIGN PC.

## `nameMap = identToString` constraint

R8b's theorems prove `instr.code = Code.decl (Expr.symbol
(identToString v_src) gty)` (literal `identToString`), while v4
expects `instr.code = Code.decl (Expr.symbol (nameMap v_src) gty)`
(caller-supplied `nameMap`). To bridge, **v5 fixes
`nameMap = Imperative.ToGoto.identToString`**. This is the natural
choice for `Core.Expression` (matches the `Imperative.ToGoto`
instance in `CoreToCProverGOTO.lean`), so this restriction does not
exclude any practical caller.

## Remaining hypotheses on `_v5`

After v5, the only "structural" hypotheses left are:
* `NoGotoHasTarget trans₀` — trivial for any `trans₀` with empty
  `instructions = #[]` (the standard initial state).
* `st_final` and `h_blocks_run` — explicit witness for the inner
  blocks-fold result.
* `h_labelMap_agree` — agreement of the WF's `labelMap` with the
  translator's hashmap-keyed labelMap. Trivially provable for any WF
  built via the strengthened theorem (definitional unfolding).
* `DeclPcInversion`, `AssignPcInversion`, `AssignNondetPcInversion` —
  R8b's PC-to-cmd inversions. Mechanically discharable from the
  translator's outer-loop structure.

All of these are mechanically discharable; they are surfaced as
hypotheses on v5 to keep this round's deliverables auditable. A
follow-up round (R9) can close them all internally. -/

theorem coreCFGToGotoTransform_forward_simulation_concrete_v5
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
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
    (h_assn_nondet_pc_inv :
      ∀ (wf : WellFormedTranslation cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool),
      CmdProvenance.AssignNondetPcInversion cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool wf)
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
  have h_assn_nondet_provenance :
      ∀ {pc : Nat} {instr : Instruction},
        pgm.instrAt pc = some instr → instr.type = .ASSIGN →
        ∃ v_src gty rhs_emitted,
          instr.code = Code.assign
            (Expr.symbol
              (Imperative.ToGoto.identToString (P := Core.Expression) v_src)
              gty) rhs_emitted ∧
          rhs_emitted.id = .side_effect .Nondet := by
    intro pc instr h_at h_ty
    exact CmdProvenance.assn_nondet_provenance_of_translator_strict cfg pgm
      δ δ_goto δ_goto_bool wf (h_assn_nondet_pc_inv wf) h_at h_ty
  -- Step 4: Delegate to v4 with the discharged hypotheses.
  exact coreCFGToGotoTransform_forward_simulation_concrete_v4
    δ δ_goto δ_goto_bool h_wf_bool π φ
    cfg Env functionName trans₀ ans h_run
    h_init_size h_init_loc h_init_no_dead h_distinct h_admitted_blocks
    h_loopContracts_empty_post h_entry_first
    h_red h_op h_uniform h_commutes_not
    (Imperative.ToGoto.identToString (P := Core.Expression))
    callResult eval fenv h_eval_bool_corr h_inj
    h_aux_goto_target
    h_decl_provenance h_assn_provenance h_assn_nondet_provenance
    h_decl_x_pinned h_assn_x_pinned h_assn_rhs_pinned
    h_decl_empty_value h_assign_value_corr h_assign_nondet_value_corr
    σ σ' b σ_goto h_corr h_run_src

/-! ## v6: also discharge R8b's two non-strict PC-inversion auxiliaries

`coreCFGToGotoTransform_forward_simulation_concrete_v6` extends v5 by
internally discharging:

* **`h_decl_pc_inv`** (R8b's `DeclPcInversion`)
  via R9's `declPcInversion_of_translator_abbrev`.
* **`h_assn_pc_inv`** (R8b's `AssignPcInversion`)
  via R9's `assignPcInversion_of_translator_abbrev`.

The third PC-inversion auxiliary, `h_assn_nondet_pc_inv` (R8b's
strict `AssignNondetPcInversion`), **remains as a hypothesis** because
it is *provably false* in general (per R8b's finding) — closing it
cleanly would require a bridge-level refactor of
`assign_nondet_lookup_of_provenance_and_pinned` in
`InstructionLookups.lean` to accept a per-firing-trace gating
precondition. See `docs/CoreToGOTO_ProofStatusRound8.md` for the
full discussion.

## New hypothesis introduced

`_v6` adds a single small hypothesis `h_init_empty_decl_assign`:
that `trans₀.instructions` carries no DECL or ASSIGN instructions.
This is **trivial** for the standard caller (whose `trans₀` is the
identity-initialised state with `instructions := #[]`). The
hypothesis appears here because R9's `BodyPcCovered` predicate's
inductive base case requires it.

## Remaining hypotheses on `_v6`

After v6, the only "structural" hypotheses left are:

* **Translator-input invariants**: `h_init_size`, `h_init_loc`,
  `h_init_no_dead`, `h_init_no_goto_target`,
  `h_init_empty_decl_assign`, `h_distinct`, `h_admitted_blocks`,
  `h_loopContracts_empty_post`, `h_entry_first`. All *trivial* for
  any standard `trans₀` with `instructions := #[]`.
* **R8a's structural witnesses**: `st_final`, `h_blocks_run`,
  `h_labelMap_agree`. Mechanically discharable from
  `coreCFGToGotoTransform_decompose` plus a uniqueness-of-WF-labelMap
  lemma.
* **R8b's strict ASSIGN-Nondet PC-inversion**: `h_assn_nondet_pc_inv`.
  Bridge-level [bridge-required].
* **R7c's pinning hypotheses**: `h_decl_x_pinned`, `h_assn_x_pinned`,
  `h_assn_rhs_pinned`. Trace-level [caller-irreducible].
* **R7c's value-side hypotheses**: `h_decl_empty_value`,
  `h_assign_value_corr`, `h_assign_nondet_value_corr`.
  Caller-side [caller-irreducible].
* **B3 expression-side bundle**, **Worker C parameters**,
  **source-side run + initial-store correspondence**.

This is the absolute minimum hypothesis surface the translator-side
work can deliver; remaining gaps are documented as either
trivial-for-standard-callers or fundamentally caller-side. -/

theorem coreCFGToGotoTransform_forward_simulation_concrete_v6
    -- Source-side semantics
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_wf_bool : WellFormedSemanticEvalGotoBool δ_goto_bool)
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
    -- R8a's labelMap-agreement bridge.
    (h_labelMap_agree :
      ∀ (wf : WellFormedTranslation cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool),
      ∀ l blk target, (l, blk) ∈ cfg.blocks →
        st_final.labelMap[l]? = some target →
        wf.labelMap l = some target)
    -- R8b's strict ASSIGN-Nondet PC-inversion remains (provably false in general).
    (h_assn_nondet_pc_inv :
      ∀ (wf : WellFormedTranslation cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool),
      CmdProvenance.AssignNondetPcInversion cfg
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        δ δ_goto δ_goto_bool wf)
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
    δ δ_goto δ_goto_bool h_wf_bool π φ
    cfg Env functionName trans₀ ans h_run
    h_init_size h_init_loc h_init_no_dead h_init_no_goto_target
    h_distinct h_admitted_blocks
    h_loopContracts_empty_post h_entry_first
    h_red h_op h_uniform h_commutes_not
    callResult eval fenv h_eval_bool_corr h_inj
    st_final h_blocks_run h_labelMap_agree
    h_decl_pc_inv h_assn_pc_inv h_assn_nondet_pc_inv
    h_decl_x_pinned h_assn_x_pinned h_assn_rhs_pinned
    h_decl_empty_value h_assign_value_corr h_assign_nondet_value_corr
    σ σ' b σ_goto h_corr h_run_src

end CProverGOTO
