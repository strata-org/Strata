/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.Shape
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.Preservation
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.StepPreservation
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.FoldAndDecompose
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.BlockBodyClosures
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.CondGotoClosures
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

/-! # Discharging `WellFormedTranslation` against `coreCFGToGotoTransform`

This module proves that the program output by
`Strata.coreCFGToGotoTransform` (composed with
`procedureToGotoCtxViaCFG`) satisfies the `WellFormedTranslation`
predicate consumed by `CProverGOTO.coreCFGToGoto_forward_simulation`.

The file is organised in three layers:

1. **Per-`Cmd` shape lemmas** (`Cmd_toGotoInstructions_*_ok`): for each
   constructor of `Imperative.Cmd Core.Expression` (in the admitted
   fragment), the resulting `GotoTransform` has a precisely-described
   `instructions` suffix appended and `nextLoc` advanced by exactly
   `Imperative.Cmd.gotoInstrCount`.

2. **Emit-helper shape lemmas** (`emitLabel_shape`, `emitCondGoto_shape`,
   `emitUncondGoto_shape`): one-liners characterising each helper's
   suffix.

3. **`patchGotoTargets` invariants**: the second pass mutates only the
   `target` field, so all type/guard/code/locationNum invariants
   transfer through patching unchanged.

These layers compose into `coreCFGToGotoTransform_wellFormed_nonempty`
and the strengthened `coreCFGToGotoTransform_wellFormed_strengthened`
at the bottom of the module.
-/

namespace CProverGOTO

open Imperative

public section

/-! ## Strengthened top-level theorem

`coreCFGToGotoTransform_wellFormed_strengthened` composes the
`layout_*_of_translator` and `{labelMap_inj,entry_in_map}_of_translator`
closures with `coreCFGToGotoTransform_wellFormed_nonempty`, internalising
its five hypothesis parameters covering layout and labelMap fields.

External hypotheses still required from callers:

* `h_entry_first` — `cfg.blocks.head?.map Prod.fst = some cfg.entry`.
  The translator already checks this and rejects on violation.
* `h_expr_corr` — `ExprTranslationPreservesEval` (caller-supplied).
* `h_tx_eq` — technical equality between
  `Imperative.ToGoto.toGotoExpr` and `h_expr_corr.tx`.
* `h_expr_translated_witness` — finer-grained version of
  `h_expr_corr` for the cond-goto layout proof. -/

theorem coreCFGToGotoTransform_wellFormed_strengthened
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
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
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e))
    (h_expr_translated_witness :
      ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
          = .ok e_goto →
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto) :
    Nonempty (WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool) := by
  -- Discharge each of `_wellFormed_nonempty`'s five hypothesis
  -- parameters via the closure theorems, then plug into it.
  have h_layout_cond_goto :=
    layout_cond_goto_of_translator cfg Env functionName trans₀
      h_init_size h_distinct h_admitted_blocks
      h_loopContracts_empty_post ans h_run
  have h_layout_cond_goto_guards :=
    layout_cond_goto_guards_of_translator cfg Env functionName trans₀
      h_init_size h_distinct h_admitted_blocks
      h_loopContracts_empty_post ans h_run
      δ δ_goto δ_goto_bool h_expr_translated_witness
  have h_layout_block_body :=
    layout_block_body_of_translator cfg Env functionName trans₀
      h_init_size h_distinct h_admitted_blocks
      h_loopContracts_empty_post ans h_run
      δ δ_goto δ_goto_bool h_expr_corr h_tx_eq
  have h_labelMap_inj :=
    labelMap_inj_of_translator cfg functionName trans₀
      h_admitted_blocks
  have h_entry_in_map :=
    entry_in_map_of_translator cfg functionName trans₀
      h_init_size h_distinct h_admitted_blocks h_entry_first
  exact coreCFGToGotoTransform_wellFormed_nonempty
    cfg Env functionName trans₀
    h_init_size h_init_loc h_distinct h_admitted_blocks
    h_loopContracts_empty_post ans h_run
    δ δ_goto δ_goto_bool
    h_layout_cond_goto h_layout_cond_goto_guards h_layout_block_body
    h_labelMap_inj h_entry_in_map

end -- public section

end CProverGOTO
