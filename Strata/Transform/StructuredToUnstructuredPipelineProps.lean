/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.StructuredToUnstructuredPipelineCorrect
public import Strata.Transform.NondetElimCoreCorrect
import all Strata.Transform.NondetElimCoreCorrect
public import Strata.Transform.LoopInitHoistCoreCorrect
public import Strata.Transform.StructuredToUnstructuredCoreCorrect
import all Strata.Transform.StructuredToUnstructuredCoreCorrect

/-! # Core structured-to-unstructured pipeline properties

Cross-pass precondition facts for the Core pipeline `s2uPipeline`, consumed by
`StructuredToUnstructuredPipelineCoreCorrect`.

Key results:
  * `Core.StructuredToUnstructuredPipeline.nondetElim_establishes_hoistPre` — a
    `nondetElim` output of a block satisfying the pipeline source condition
    satisfies the loop-init hoist input condition.
  * `Core.StructuredToUnstructuredPipeline.hoist_establishes_loweringPre` — a
    successful Core loop-init hoist maps that condition to the `stmtsToCFG`
    input condition. -/

public section

namespace Core.StructuredToUnstructuredPipeline

open Core Core.Logic Imperative Imperative.Logic Strata.Logic
open Imperative.StructuredToUnstructured

/-! ## Core cross-pass precondition implications

The Core pipeline correctness theorem exposes its complete source precondition
directly. These implications connect that visible source condition to the next
pass's visible condition; neither hides the pipeline precondition behind a named
predicate.
-/

/-- A Core `Block.nondetElim` output satisfies the strengthened hoist input
condition used by the pipeline. -/
theorem nondetElim_establishes_hoistPre :
    ∀ ss out, (fun ss => some (Imperative.Block.nondetElim ss)) ss = some out →
      (Statements.noCalls ss = Bool.true
        ∧ Block.loopHasNoInvariants ss = Bool.true
        ∧ Block.noMeasureLoops ss = Bool.true
        ∧ Block.uniqueInits (C := Command) ss
        ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] ss
        ∧ Block.userLabelsShapeNodup (C := Command) ss
        ∧ (∀ name : String, Imperative.NondetElim.isGeneratedName name →
            HasIdent.ident (P := Expression) name ∉
              (Block.definedVars (C := Command) ss false ++
                Block.modifiedVars (C := Command) ss))
        ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
            HasIdent.ident (P := Expression) name ∉
              Block.initVars (C := Command) ss)) →
      (Statements.noCalls out = Bool.true
        ∧ Block.noNondetGuards out = Bool.true
        ∧ Block.uniqueInits (C := Command) out
        ∧ Block.loopHasNoInvariants out = Bool.true
        ∧ Block.noMeasureLoops out = Bool.true
        ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] out
        ∧ Block.userLabelsShapeNodup (C := Command) out
        ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
            HasIdent.ident (P := Expression) name ∉
              Block.initVars (C := Command) out)) := by
  intro ss out ht hpre
  simp only [Option.some.injEq] at ht
  subst out
  obtain ⟨hnc, hlhni, hnml, huniq, hcov, hlabels, hnogen, hs2u⟩ := hpre
  obtain ⟨bs, hproj, hemb⟩ := Core.noCalls_projectStmts hnc
  have hout : Imperative.Block.nondetElim ss =
      Imperative.embedStmts (Imperative.Block.nondetElim bs) := by
    rw [← hemb, Core.embedStmts_nondetElim]
  have hlhniBase : Block.loopHasNoInvariants bs = Bool.true := by
    rw [← Imperative.embedStmts_loopHasNoInvariants bs, hemb]
    exact hlhni
  have hnmlBase : Block.noMeasureLoops bs = Bool.true := by
    rw [← Imperative.embedStmts_noMeasureLoops bs, hemb]
    exact hnml
  have huniqBase : Block.uniqueInits (C := Cmd Expression) bs :=
    (Imperative.embedStmts_uniqueInits bs).mp (by rwa [hemb])
  have hcovBase : Block.exitsCoveredByBlocks (CmdT := Cmd Expression) [] bs :=
    (Imperative.embedStmts_exitsCoveredByBlocks [] bs).mp (by rwa [hemb])
  have hlabelsBase : Block.userLabelsShapeNodup (C := Cmd Expression) bs :=
    (Imperative.embedStmts_userLabelsShapeNodup bs).mp (by rwa [hemb])
  have hnogenBase : Imperative.SrcNoGenWrites Imperative.NondetElim.isGeneratedName bs :=
    (Imperative.projectStmts_noDefinedOrModifiedKind_iff Imperative.NondetElim.isGeneratedName hproj).mp hnogen
  have hndelimInitBase : ∀ name : String, Imperative.NondetElim.isGeneratedName name →
      HasIdent.ident (P := Expression) name ∉ Block.initVars (C := Cmd Expression) bs := by
    intro name hkind hmem
    exact hnogenBase name hkind (List.mem_append_left _ hmem)
  have hs2uBase : ∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
      HasIdent.ident (P := Expression) name ∉ Block.initVars (C := Cmd Expression) bs := by
    intro name hkind hmem
    exact hs2u name hkind (by
      rw [← hemb, Block.initVars, Imperative.embedStmts_definedVars]
      exact hmem)
  have huniqOutBase : Block.uniqueInits (C := Cmd Expression)
      (Imperative.Block.nondetElim bs) := by
    exact (Imperative.Block.nondetElimM_initVars_nodup bs StringGenState.emp
      StringGenState.wf_emp huniqBase hndelimInitBase).2
  have hlabelsOutBase : Block.userLabelsShapeNodup (C := Cmd Expression)
      (Imperative.Block.nondetElim bs) := by
    unfold Block.userLabelsShapeNodup
    rw [Imperative.Block.nondetElim_getBlockLabels]
    exact hlabelsBase
  have hs2uOutBase : ∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
      HasIdent.ident (P := Expression) name ∉
        Block.initVars (C := Cmd Expression) (Imperative.Block.nondetElim bs) := by
    intro name hkind hmem
    rcases Imperative.Block.nondetElimM_initVars_classified
        bs StringGenState.emp _ hmem with hsource | ⟨generated, heq, hgenerated⟩
    · exact hs2uBase name hkind hsource
    · exact
        Imperative.StructuredToUnstructuredPipeline.nondetElim_generated_not_s2uGenerated
          hgenerated
        (LawfulHasIdent.ident_inj heq ▸ hkind)
  refine ⟨Core.NondetElim.preserves_noCalls hnc,
    Imperative.nondetElim_noNondetGuards ss, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout]
    exact (Imperative.embedStmts_uniqueInits _).mpr huniqOutBase
  · rw [hout, Imperative.embedStmts_loopHasNoInvariants]
    exact Imperative.nondetElim_loopHasNoInvariants bs hlhniBase
  · rw [hout, Imperative.embedStmts_noMeasureLoops]
    exact Imperative.nondetElim_noMeasureLoops bs hnmlBase
  · rw [hout]
    exact (Imperative.embedStmts_exitsCoveredByBlocks [] _).mpr
      (Imperative.Block.nondetElim_exitsCoveredByBlocks bs hcovBase)
  · rw [hout]
    exact (Imperative.embedStmts_userLabelsShapeNodup _).mpr hlabelsOutBase
  · intro name hkind hmem
    apply hs2uOutBase name hkind
    rw [hout, Block.initVars, Imperative.embedStmts_definedVars] at hmem
    exact hmem

/-- A successful Core loop-init hoist maps the strengthened pipeline hoist
condition to the complete visible `stmtsToCFG` condition. -/
theorem hoist_establishes_loweringPre :
    ∀ ss out, Core.hoistLoopPrefixInits ss = some out →
      (Statements.noCalls ss = Bool.true
        ∧ Block.noNondetGuards ss = Bool.true
        ∧ Block.uniqueInits (C := Command) ss
        ∧ Block.loopHasNoInvariants ss = Bool.true
        ∧ Block.noMeasureLoops ss = Bool.true
        ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] ss
        ∧ Block.userLabelsShapeNodup (C := Command) ss
        ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
            HasIdent.ident (P := Expression) name ∉
              Block.initVars (C := Command) ss)) →
      (Statements.noCalls out = Bool.true
        ∧ Block.noNondetGuards out = Bool.true
        ∧ Block.uniqueInits (C := Command) out
        ∧ Block.loopBodyNoInits (C := Command) out = Bool.true
        ∧ Block.loopHasNoInvariants out = Bool.true
        ∧ Block.noMeasureLoops out = Bool.true
        ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] out
        ∧ Block.userLabelsShapeNodup (C := Command) out
        ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
            HasIdent.ident (P := Expression) name ∉
              Block.initVars (C := Command) out)) := by
  intro ss out ht hpre
  obtain ⟨hnc, hng, huniq, hlhni, hnml, hcov, hlabels, hs2u⟩ := hpre
  obtain ⟨bs, hproj, hemb⟩ := Core.noCalls_projectStmts hnc
  have hngBase : Block.noNondetGuards bs = Bool.true := by
    rw [← Imperative.embedStmts_noNondetGuards bs, hemb]
    exact hng
  have huniqBase : Block.uniqueInits (C := Cmd Expression) bs :=
    (Imperative.embedStmts_uniqueInits bs).mp (by rwa [hemb])
  have hlhniBase : Block.loopHasNoInvariants bs = Bool.true := by
    rw [← Imperative.embedStmts_loopHasNoInvariants bs, hemb]
    exact hlhni
  have hnmlBase : Block.noMeasureLoops bs = Bool.true := by
    rw [← Imperative.embedStmts_noMeasureLoops bs, hemb]
    exact hnml
  have hcovBase : Block.exitsCoveredByBlocks (CmdT := Cmd Expression) [] bs :=
    (Imperative.embedStmts_exitsCoveredByBlocks [] bs).mp (by rwa [hemb])
  have hlabelsBase : Block.userLabelsShapeNodup (C := Cmd Expression) bs :=
    (Imperative.embedStmts_userLabelsShapeNodup bs).mp (by rwa [hemb])
  have hs2uBase : ∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
      HasIdent.ident (P := Expression) name ∉ Block.initVars (C := Cmd Expression) bs := by
    intro name hkind hmem
    exact hs2u name hkind (by
      rw [← hemb, Block.initVars, Imperative.embedStmts_definedVars]
      exact hmem)
  rw [Core.hoistLoopPrefixInits_eq_some hproj] at ht
  obtain rfl := Option.some.inj ht
  refine ⟨Core.noCalls_embedStmts _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Imperative.embedStmts_noNondetGuards]
    exact Imperative.LoopInitHoistProducerProps.Block.hoistP_noNondetGuards bs hngBase
  · exact (Imperative.embedStmts_uniqueInits _).mpr
      ((Imperative.LoopInitHoistProducerProps.Block.hoistP_initVars_perm bs).nodup_iff.mpr
        huniqBase)
  · rw [Imperative.embedStmts_loopBodyNoInits]
    exact Imperative.LoopInitHoistProducerProps.Block.hoistP_loopBodyNoInits bs
  · rw [Imperative.embedStmts_loopHasNoInvariants]
    exact Imperative.LoopInitHoistProducerProps.Block.hoistP_loopHasNoInvariants bs hlhniBase
  · rw [Imperative.embedStmts_noMeasureLoops]
    exact Imperative.LoopInitHoistProducerProps.Block.hoistP_noMeasureLoops bs hnmlBase
  · exact (Imperative.embedStmts_exitsCoveredByBlocks [] _).mpr
      (Imperative.Block.hoistP_exitsCoveredByBlocks [] bs hcovBase)
  · apply (Imperative.embedStmts_userLabelsShapeNodup _).mpr
    unfold Block.userLabelsShapeNodup
    rw [Imperative.LoopInitHoistProducerProps.Block.hoistP_getBlockLabels]
    exact hlabelsBase
  · intro name hkind hmem
    apply hs2uBase name hkind
    apply Imperative.LoopInitHoistProducerProps.Block.hoistP_initVars_sub bs
    rw [Block.initVars, Imperative.embedStmts_definedVars] at hmem
    exact hmem

end Core.StructuredToUnstructuredPipeline

end -- public section
