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

This module composes the four parallel-worker outputs into a single
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

* **A2/A3/A4** — `coreCFGToGotoTransform_wellFormed_nonempty`
  (`CoreCFGToGotoTransformWF.lean`): produces a
  `Nonempty (WellFormedTranslation cfg pgm δ δ_goto δ_goto_bool)`
  from the translator output, modulo four hypothesis bundles for
  the layout fields A4 left as parameters.
* **B3** — `toGotoExprCtx_preservesEval_boolInt`
  (`ExprTranslationPreservesEvalBoolInt.lean`): per-LExpr translation
  correctness on the bool+int fragment.
* **C** — `steppingBridges_of_translator`
  (`SteppingBridgesDischarge.lean`): `SteppingBridges` bundle from
  `EvalBoolCorr` + `TranslatorBridgeHyps`.
* **Phase 3** — `coreCFGToGoto_forward_simulation_storeCorr`
  (`CoreCFGToGOTOCorrectStore.lean`): consumes a `WellFormedTranslation`
  and a `SteppingBridges` to produce an `ExecProg` derivation.

The theorem still takes a number of hypotheses as parameters:

* A4's four open layout-field hypotheses.
* C's `TranslatorBridgeHyps` (which depends on A4's labelMap output).
* `EvalBoolCorr` (the cross-evaluator boolean agreement).
* `ExprTranslationPreservesEval` (B3's bridge consumes
  `BoolIntOpHypotheses` + `BoolIntGtyAgrees` and produces this for
  the bool+int fragment; we take it as input here so the theorem
  remains pipeline-shape).

These are the "still open" obligations after rounds 1-4. They are
documented in `docs/_workers/integration_notes.md` and the round
reports.

This file is the top of the assembly tower. It does not introduce
any new proof obligations beyond what the workers already produced;
it just shows that the pieces compose.

-/

namespace CProverGOTO

open Imperative
open CProverGOTO.SemanticsTautschnig
  (Store StoreCorr CallResultRel ExprEval FuncEnv ExecProg StepInstr)

/-- End-to-end concrete forward simulation for `coreCFGToGotoTransform`.

Composes A2/A3/A4 (translator well-formedness), B3 (expression
translation correctness, supplied as `ExprTranslationPreservesEval`
hypothesis), and C (per-step bridges) with the existing closed
forward-simulation theorems. The conclusion is a
`StoreCorr`-shaped `ExecProg` derivation matching the source's
terminating run. -/
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
    -- A4 hypotheses for the structural side of WellFormedTranslation
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
    -- A4 hypotheses for the layout fields not closed by round 4
    (h_layout_cond_goto :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l blk pc cond lt lf md, (l, blk) ∈ cfg.blocks →
        hashMapToLabelMap st_final.labelMap l = some pc →
        blk.transfer = .condGoto cond lt lf md →
        ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
          pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
          pc_uncond = pc_neg + 1 ∧
          ans.instructions[pc_neg]? = some instr_neg ∧
          instr_neg.type = .GOTO ∧
          instr_neg.target = some pc_lf ∧
          hashMapToLabelMap st_final.labelMap lf = some pc_lf ∧
          ans.instructions[pc_uncond]? = some instr_uncond ∧
          instr_uncond.type = .GOTO ∧
          instr_uncond.target = some pc_lt ∧
          hashMapToLabelMap st_final.labelMap lt = some pc_lt)
    (h_layout_cond_goto_guards :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l blk pc cond lt lf md instr_neg instr_uncond,
        (l, blk) ∈ cfg.blocks →
        hashMapToLabelMap st_final.labelMap l = some pc →
        blk.transfer = .condGoto cond lt lf md →
        ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg →
        ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond →
        ∃ e_goto,
          instr_neg.guard = e_goto.not ∧
          ExprTranslated δ δ_goto δ_goto_bool cond e_goto ∧
          instr_uncond.guard = CProverGOTO.Expr.true)
    (h_layout_block_body :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l blk pc, (l, blk) ∈ cfg.blocks →
        hashMapToLabelMap st_final.labelMap l = some pc →
      ∀ k inner,
        (h : k < blk.cmds.length) →
        blk.cmds[k]'h = .cmd inner →
        CmdEmittedAt δ δ_goto δ_goto_bool
          { name := "", parameterIdentifiers := #[],
            instructions := ans.instructions }
          (pc + 1 + cmdsPrefixInstrCount blk.cmds k) inner)
    (h_labelMap_inj :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l₁ l₂ pc,
        hashMapToLabelMap st_final.labelMap l₁ = some pc →
        hashMapToLabelMap st_final.labelMap l₂ = some pc → l₁ = l₂)
    (h_entry_in_map :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
        ∃ pc, hashMapToLabelMap st_final.labelMap cfg.entry = some pc)
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
  -- Step 1: A4's WF theorem produces a Nonempty witness.
  have h_wf_nonempty :=
    coreCFGToGotoTransform_wellFormed_nonempty
      cfg Env functionName trans₀ h_init_size h_init_loc h_distinct
      h_admitted_blocks h_loopContracts_empty_post ans h_run
      δ δ_goto δ_goto_bool
      h_layout_cond_goto h_layout_cond_goto_guards h_layout_block_body
      h_labelMap_inj h_entry_in_map
  -- Step 2: extract a concrete WellFormedTranslation (Nonempty + Classical.choice).
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
