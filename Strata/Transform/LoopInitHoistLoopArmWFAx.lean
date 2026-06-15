/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT

  Axiom audit (non-`module`, so `#print axioms` is permitted): confirms the
  producer-precondition WF sub-lemmas for the §E `.loop` arm rest only on the
  Lean standard axioms (no `sorryAx`).
-/
import Strata.Transform.LoopInitHoistLoopArmWF

open Imperative LoopInitHoistLoopArmWF

#print axioms Imperative.LoopInitHoistLoopArmWF.Stmt.entriesOf_targetGen
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.entriesOf_targetGen
#print axioms Imperative.LoopInitHoistLoopArmWF.targetsOf'_append
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.transportShape_hoistLoopPrefixInitsM

-- namesFreshInExprs-preservation family (TARGET side; the SOURCE-side corollary
-- is no longer needed — the producer needs no source freshness)
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.hoistLoopPrefixInitsM_namesFreshInExprs_targets

-- shape-free / disjointness producer-precondition family
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.entriesOf_target_hasUnderscoreDigitSuffix
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.mem_targetsOf'_entriesOf_hasUnderscoreDigitSuffix
#print axioms Imperative.LoopInitHoistLoopArmWF.targetsOf'_entriesOf_disjoint_of_shapefree
#print axioms Imperative.LoopInitHoistLoopArmWF.modifiedVars_disjoint_targetsOf'_entriesOf
#print axioms Imperative.LoopInitHoistLoopArmWF.modifiedVars_disjoint_sourcesOf'_entriesOf
#print axioms Imperative.LoopInitHoistLoopArmWF.targetsOf'_entriesOf_disjoint_ambient_A
#print axioms Imperative.LoopInitHoistLoopArmWF.targetsOf'_entriesOf_disjoint_ambient_B
#print axioms Imperative.LoopInitHoistLoopArmWF.targetsOf'_entriesOf_disjoint_initVars_stmt
#print axioms Imperative.LoopInitHoistLoopArmWF.sourcesOf'_entriesOf_disjoint_ambient

-- sources-Nodup producer-precondition family
#print axioms Imperative.LoopInitHoistLoopArmWF.Stmt.sourcesOf_entriesOf_sublist
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.sourcesOf_entriesOf_sublist
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.entriesOf_sourcesOf_nodup_of_initVars
#print axioms Imperative.LoopInitHoistLoopArmWF.substOf'_map_fst
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.entriesOf_substOf_src_nodup_of_initVars

-- GAP 1 part (b): (initVars body₁).Nodup of the post-order pass output
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.applyRenames_initVars_isEmpty
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.applyRenames_liftResidual_initVars_nil
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.initVars_havocStmts'
#print axioms Imperative.LoopInitHoistLoopArmWF.hoistInitClass_disjoint
#print axioms Imperative.LoopInitHoistLoopArmWF.Stmt.hoistLoopPrefixInitsM_initVars_classified
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.hoistLoopPrefixInitsM_initVars_classified
#print axioms Imperative.LoopInitHoistLoopArmWF.Block.hoistLoopPrefixInitsM_initVars_nodup
