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
public import Strata.Transform.StructuredToUnstructuredPipelineProps
import Strata.DL.Imperative.Logic.TraceRelationsProps

/-! # Core structured-to-unstructured pipeline correctness

This module transports and composes the three generic structured-transform
trace proofs across their Core call-free wrappers.

The source gate is `(base.extend StructuredToUnstructured.prefixesReserved).extend
NondetElim.prefixesReserved` and the final CFG gate is `base`.

Key results:
  * `Core.StructuredToUnstructuredPipeline.overapproximatesTraces`
    — the Core pipeline `s2uPipeline` overapproximates the source Core block
    event language by the Core CFG event language under `Trace.WithWF` matching.
  * `Core.StructuredToUnstructuredPipeline.assertValid` — assertion validity on
    the final CFG reflects to the source for interpretations stable under
    `EventArg.WithWF`; `evalInterp_stableUnder` supplies this for `evalInterp`.
-/

public section

namespace Core.StructuredToUnstructuredPipeline

open Core Core.Logic Imperative Imperative.Logic Strata.Logic
open Imperative.StructuredToUnstructured
open Imperative.Specification Imperative.Specification.Transform

variable (π : String → Option Procedure)

/-! ## Pipeline stage parameters

The intermediate stage uses `base.extend StructuredToUnstructured.prefixesReserved`
(the canonical S2U source gate), the source additionally reserves NondetElim's
generated names, and the final CFG stage uses `base`. A caller supplies
disjointness for the base prefixes; the generic
`Imperative.StructuredToUnstructuredPipeline.intermediateParams_prefixesDisjoint`
derives it for the S2U prefixes. All stages preserve the base declared
functions. -/

/-! ## Core pipeline composition -/

/-- The composed Core NondetElim, loop-init-hoist, and structured-to-CFG
pipeline overapproximates source block traces by target CFG traces under
`Trace.WithWF` matching; final environments agree on source bindings.
The caller's base prefixes must be disjoint from NondetElim-generated names. -/
theorem overapproximatesTraces (base : InitEnvWFParams)
    (hbase : prefixesDisjoint base.prefixIdents
      Imperative.NondetElim.isGeneratedName) :
    OverapproximatesTracesUptoWhen
      (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True)))
      (· = ·)
      (EnvStoreAgree (P := Expression))
      (EventLang.coreBlock π) (EventLang.coreCFG π)
      s2uPipeline
      (fun ss =>
        Statements.noCalls ss = Bool.true
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
              Block.initVars (C := Command) ss))
      ((base.extend Imperative.StructuredToUnstructured.prefixesReserved).extend
        Imperative.NondetElim.prefixesReserved) base := by
  let params_src := (base.extend Imperative.StructuredToUnstructured.prefixesReserved).extend
    Imperative.NondetElim.prefixesReserved
  let params_a := base.extend Imperative.StructuredToUnstructured.prefixesReserved
  have hprefixes : prefixesDisjoint params_a.prefixIdents
      Imperative.NondetElim.isGeneratedName := by
    simpa only [params_a, Imperative.StructuredToUnstructuredPipeline.intermediateParams]
      using Imperative.StructuredToUnstructuredPipeline.intermediateParams_prefixesDisjoint
        base hbase
  have h_nd :
      OverapproximatesTracesUptoWhen
        (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv NondetElimTrace.NdExtra)) (· = ·)
        (EnvStoreAgree (P := Expression))
        (EventLang.coreBlock π) (EventLang.coreBlock π)
        (fun ss => some (Imperative.Block.nondetElim ss))
        (fun ss =>
          Statements.noCalls ss = Bool.true
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
                Block.initVars (C := Command) ss))
        params_src params_a := by
    intro ss out ht hpre ρ₀ ρ₀' hEq hwf
    obtain ⟨hnc, _, _, _, _, _, hnogen, _⟩ := hpre
    obtain ⟨h1, h2, h3, h4⟩ :=
      Core.NondetElim.overapproximatesTraces π params_a hprefixes
        ss out ht ⟨hnc, hnogen⟩ ρ₀ ρ₀' hEq hwf
    refine ⟨?_, ?_, ?_, h4⟩
    · exact h1
    · intro ρ' trace hrun
      obtain ⟨ρ'', tr', hr, hout, hrel⟩ := h2 ρ' trace hrun
      exact ⟨ρ'', tr', hr, envStoreAgree_of_extendsWith hout, hrel⟩
    · intro lbl ρ' trace hrun
      obtain ⟨ρ'', tr', hr, hout, hrel⟩ := h3 lbl ρ' trace hrun
      exact ⟨ρ'', tr', hr, envStoreAgree_of_extendsWith hout, hrel⟩
  have h_hoist :
      OverapproximatesTracesUptoWhen
        (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True))) (· = ·)
        (EnvStoreAgree (P := Expression))
        (EventLang.coreBlock π) (EventLang.coreBlock π)
        Core.hoistLoopPrefixInits
        (fun ss =>
          Statements.noCalls ss = Bool.true
          ∧ Block.noNondetGuards ss = Bool.true
          ∧ Block.uniqueInits (C := Command) ss
          ∧ Block.loopHasNoInvariants ss = Bool.true
          ∧ Block.noMeasureLoops ss = Bool.true
          ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] ss
          ∧ Block.userLabelsShapeNodup (C := Command) ss
          ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
              HasIdent.ident (P := Expression) name ∉
                Block.initVars (C := Command) ss))
        params_a params_a := by
    intro ss out ht hpre ρ₀ ρ₀' hEq hwf
    obtain ⟨hnc, _, huniq, _⟩ := hpre
    exact Core.LoopInitHoist.overapproximatesTraces π params_a
      ss out ht ⟨hnc, huniq⟩ ρ₀ ρ₀' hEq hwf
  -- Stage 1: `nondetElim` then hoist, composed into the pipeline relation.
  have h_lockstep :=
    (OverapproximatesTracesUptoWhen.comp_trans_eq
      (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv NondetElimTrace.NdExtra))
      (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True)))
      (EnvStoreAgree (P := Expression))
      (fun _ _ _ h₁ h₂ => EnvStoreAgree_trans h₁ h₂)
      (EventLang.coreBlock π) (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (Imperative.Block.nondetElim ss)) Core.hoistLoopPrefixInits
      params_src params_a params_a
      nondetElim_establishes_hoistPre
      h_nd
      h_hoist).mono_trace
        (fun _ _ h => h.elim (fun _ hmid =>
          (Trace.WithWF.trans hmid.1 hmid.2).mono (fun _ _ => trivial)))
  -- The combined stage-1 precondition bridge into `stmtsToCFG`'s precondition.
  have hpre_lockstep_cfg :
      ∀ st st',
        ((fun ss => some (Imperative.Block.nondetElim ss)) st >>=
          Core.hoistLoopPrefixInits) = some st' →
        (Statements.noCalls st = Bool.true
          ∧ Block.loopHasNoInvariants st = Bool.true
          ∧ Block.noMeasureLoops st = Bool.true
          ∧ Block.uniqueInits (C := Command) st
          ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] st
          ∧ Block.userLabelsShapeNodup (C := Command) st
          ∧ (∀ name : String, Imperative.NondetElim.isGeneratedName name →
              HasIdent.ident (P := Expression) name ∉
                (Block.definedVars (C := Command) st false ++
                  Block.modifiedVars (C := Command) st))
          ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
              HasIdent.ident (P := Expression) name ∉
                Block.initVars (C := Command) st)) →
        (Statements.noCalls st' = Bool.true
          ∧ Block.noNondetGuards st' = Bool.true
          ∧ Block.uniqueInits (C := Command) st'
          ∧ Block.loopBodyNoInits (C := Command) st' = Bool.true
          ∧ Block.loopHasNoInvariants st' = Bool.true
          ∧ Block.noMeasureLoops st' = Bool.true
          ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] st'
          ∧ Block.userLabelsShapeNodup (C := Command) st'
          ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
              HasIdent.ident (P := Expression) name ∉
                Block.initVars (C := Command) st')) := by
    intro st st' ht hpre
    simp only [bind, Option.bind] at ht
    exact hoist_establishes_loweringPre _ _ ht (nondetElim_establishes_hoistPre _ _ rfl hpre)
  -- Stage 2: compose the structured prefix with `stmtsToCFG`, then collapse
  -- the relational composition to `Trace.WithWF` matching.
  exact (OverapproximatesTracesUptoWhen.comp_trans_eq
    (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True)))
    (Trace.WithWF (P := Expression) (EventArg.ExtendsEnv (fun _ => True)))
    (EnvStoreAgree (P := Expression))
    (fun _ _ _ h₁ h₂ => EnvStoreAgree_trans h₁ h₂)
    (EventLang.coreBlock π) (EventLang.coreBlock π) (EventLang.coreCFG π)
    (fun ss => (fun ss => some (Imperative.Block.nondetElim ss)) ss >>= Core.hoistLoopPrefixInits)
    Core.stmtsToCFG
    params_src params_a base
    hpre_lockstep_cfg
    h_lockstep
    (Core.StructuredToUnstructured.overapproximatesTraces π base)).mono_trace
      (fun _ _ h => h.elim (fun _ hmid =>
        (Trace.WithWF.trans hmid.1 hmid.2).mono (fun _ _ => trivial)))

/-- Evaluation to `true` is stable under end-to-end pipeline event matching. -/
theorem evalInterp_stableUnder :
    ConditionInterp.StableUnder (P := Expression)
      (Imperative.BigStep.evalInterp : ConditionInterp Expression)
      (EventArg.WithWF (EventArg.ExtendsEnv (fun _ => True))
        (P := Expression)) :=
  Imperative.BigStep.evalInterp_stableUnder

/-- Assertion validity for the CFG produced by the composed structured pipeline
reflects to its source block when condition truth is stable under pipeline
event matching. `evalInterp_stableUnder` supplies this for `evalInterp`. -/
theorem assertValid (base : InitEnvWFParams)
    (hbase : prefixesDisjoint base.prefixIdents
      Imperative.NondetElim.isGeneratedName)
    {ss : Statements} {out : CFG String (DetBlock String Command Expression)}
    (htransform : s2uPipeline ss = some out)
    (hpre :
      Statements.noCalls ss = Bool.true
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
            Block.initVars (C := Command) ss))
    {I : ConditionInterp Expression}
    (hstable : I.StableUnder
      (EventArg.WithWF (EventArg.ExtendsEnv (fun _ => True))
        (P := Expression)))
    {aid : AssertId Expression}
    (hvalid : AssertValidOnTracesWhen (EventLang.coreCFG π) I
      (Core.Logic.CFGInitEnvWF base out) out aid) :
    AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (Core.Logic.BlockInitEnvWF
        ((base.extend Imperative.StructuredToUnstructured.prefixesReserved).extend
          Imperative.NondetElim.prefixesReserved) ss) ss aid :=
  overapproximatesTracesUptoWhen_assertValid I _ _
    (EventLang.coreBlock π) (EventLang.coreCFG π)
    s2uPipeline
    (fun block =>
      Statements.noCalls block = Bool.true
      ∧ Block.loopHasNoInvariants block = Bool.true
      ∧ Block.noMeasureLoops block = Bool.true
      ∧ Block.uniqueInits (C := Command) block
      ∧ Block.exitsCoveredByBlocks (CmdT := Command) [] block
      ∧ Block.userLabelsShapeNodup (C := Command) block
      ∧ (∀ name : String, Imperative.NondetElim.isGeneratedName name →
          HasIdent.ident (P := Expression) name ∉
            (Block.definedVars (C := Command) block false ++
              Block.modifiedVars (C := Command) block))
      ∧ (∀ name : String, Imperative.StructuredToUnstructured.isGeneratedName name →
          HasIdent.ident (P := Expression) name ∉
            Block.initVars (C := Command) block))
    ((base.extend Imperative.StructuredToUnstructured.prefixesReserved).extend
        Imperative.NondetElim.prefixesReserved) base
    (fun _ _ htrace aid =>
      Trace.WithWF.assertionValidFrom_reflect hstable htrace aid)
    (overapproximatesTraces π base hbase)
    htransform hpre hvalid

end Core.StructuredToUnstructuredPipeline

end -- public section
