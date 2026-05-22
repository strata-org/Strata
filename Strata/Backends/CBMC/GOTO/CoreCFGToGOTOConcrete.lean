/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrectStore
public import Strata.Backends.CBMC.GOTO.SteppingBridgesDischarge

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

end CProverGOTO
