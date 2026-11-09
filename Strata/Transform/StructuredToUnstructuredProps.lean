/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.StructuredToUnstructured
public import Strata.DL.Imperative.StmtProps

import all Strata.Transform.StructuredToUnstructured

/-! # Structured-to-unstructured lowering properties

Properties of the definitions in `StructuredToUnstructured`. The trace
correctness proofs live in `StructuredToUnstructuredCorrect` and
`StructuredToUnstructuredCoreCorrect`.

Key results:
  * `Core.stmtsToCFG_eq_some` — `Core.stmtsToCFG` succeeds with the embedded
    generic lowering whenever the Core block projects to a call-free
    Imperative block.
  * `Core.StructuredToUnstructured.loweringShape_of_checks` — a body accepted
    by the shape checks of `structuredToUnstructuredDecl` satisfies the
    lowering correctness theorem's shape conditions: covered exits,
    duplicate-free non-generated-shape labels, and no initialized
    lowering-generated name. -/

public section

namespace Core

open Imperative

/-- `Core.stmtsToCFG` succeeds with the embedded generic lowering whenever the
Core block projects to a call-free Imperative block. -/
theorem stmtsToCFG_eq_some {ss : Statements}
    {bs : List (Imperative.Stmt Expression (Cmd Expression))}
    (h : projectStmts ss = some bs) :
    stmtsToCFG ss = some (embedCFG (Imperative.stmtsToCFG bs)) := by
  simp [stmtsToCFG, h]

/-- A body accepted by the three shape checks of `structuredToUnstructuredDecl`
satisfies the shape conditions of the lowering's correctness theorem: every
`exit` is covered, user labels are duplicate-free and not `_<digits>`-shaped,
and no initialized name is a lowering-generated name. -/
theorem StructuredToUnstructured.loweringShape_of_checks {ss : Statements}
    (hexits : Imperative.Block.checkExitsCoveredByBlocks [] ss = true)
    (hlabels : StructuredToUnstructured.userLabelsOk ss = true)
    (hinits : StructuredToUnstructured.initsAvoidReservedPrefixes ss = true) :
    Block.exitsCoveredByBlocks (CmdT := Command) [] ss
      ∧ Block.userLabelsShapeNodup (C := Command) ss
      ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
          HasIdent.ident (P := Expression) name ∉
            Block.initVars (C := Command) ss) := by
  refine ⟨Block.exitsCoveredByBlocks_of_check hexits, ?_, ?_⟩
  · simp only [StructuredToUnstructured.userLabelsOk, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true', decide_eq_true_eq] at hlabels
    refine ⟨fun l hl hshape => ?_, hlabels.2⟩
    have := String.endsWithUnderscoreDigits_of_hasUnderscoreDigitSuffix hshape
    simp_all
  · intro name hgen hmem
    simp only [StructuredToUnstructured.initsAvoidReservedPrefixes, List.all_eq_true,
      Bool.not_eq_true', List.any_eq_false] at hinits
    have hfresh := hinits _ hmem
    -- Every lowering-generated name starts with a reserved prefix.
    obtain ⟨pfx, hpfx, hpre⟩ : ∃ pfx ∈ Imperative.StructuredToUnstructured.prefixesReserved,
        pfx.toList.isPrefixOf name.toList = true := by
      rcases hgen with ⟨pfx, hpfx, state, rfl⟩ | ⟨label, state, rfl⟩
      · exact ⟨pfx, hpfx,
          String.HasGenPrefix.bare_isPrefixOf (StringGenState.gen_hasGenPrefix pfx state)⟩
      · refine ⟨"block$", by simp [Imperative.StructuredToUnstructured.prefixesReserved], ?_⟩
        have h := String.HasGenPrefix.bare_isPrefixOf
          (StringGenState.gen_hasGenPrefix
            (Imperative.StructuredToUnstructured.blockExitPrefix label) state)
        rw [List.isPrefixOf_iff_prefix] at h ⊢
        refine List.IsPrefix.trans ?_ h
        simp only [Imperative.StructuredToUnstructured.blockExitPrefix, String.toList_append,
          List.append_assoc]
        exact List.prefix_append _ _
    exact hfresh pfx hpfx hpre

end Core

end -- public section
