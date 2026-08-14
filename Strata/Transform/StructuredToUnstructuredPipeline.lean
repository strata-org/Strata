/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.NondetElimCorrect
public import Strata.Transform.LoopInitHoistCorrect
public import Strata.Transform.StructuredToUnstructuredCorrect

import all Strata.Transform.NondetElim
import all Strata.Transform.LoopInitHoistCorrect

/-! # Structured-to-unstructured pipeline: definitions

The composed transform `pipeline = stmtsToCFG ∘ hoistLoopPrefixInits ∘ nondetElim`,
the combined generated-name kind `pipelineKind`, and the purely syntactic
precondition `PipelinePre` under which the pipeline refines its input.  The
soundness proofs live in `StructuredToUnstructuredPipelineCorrect`. -/

public section

namespace Imperative

/-- The composed structured-to-unstructured pipeline. -/
@[expose] def s2uPipeline {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    [HasBoolOps P] [HasInt P] [HasIntOps P]
    (ss : List (Stmt P (Cmd P))) :
    CFG String (DetBlock String (Cmd P) P) :=
  (stmtsToCFG ∘ Block.hoistLoopPrefixInits ∘ Block.nondetElim) ss

/-- The combined generated-name kind of the whole pipeline: a name is
`pipelineKind` when it is either an `nondetElim`-generated (`ndelimKind`) or an
`stmtsToCFG`-generated (`s2uKind`) name.

Used as the source language's `initEnvWF` parameter: a store leaving every
`pipelineKind` slot undefined supplies the freshness both passes' generated names
demand, each recovered by the corresponding disjunct. -/
@[expose] def pipelineKind (s : String) : Prop :=
  ndelimKind s ∨ StructuredToUnstructuredCorrect.s2uKind s

/-- The purely syntactic precondition under which `s2uPipeline ss` refines `ss`:
source shape restrictions, exit-coverage, and generated-name disjointness. -/
structure PipelinePre {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasVarsPure P P.Expr]
    [HasIdent P] [HasInt P] [HasIntOps P] [HasSubstFvar P]
    [DecidableEq P.Ident]
    (ss : List (Stmt P (Cmd P))) : Prop where
  h_nofd : Block.noFuncDecl ss = true
  h_lhni : Block.loopHasNoInvariants ss = true
  h_nml : Block.noMeasureLoops ss = true
  h_unique : Block.uniqueInits ss
  h_userlabels : Block.userLabelsShapeNodup ss
  h_covered : Block.exitsCoveredByBlocks [] ss
  h_ndelim_writes : SrcNoGenWrites (P := P) ndelimKind ss
  h_disj_initVars : ∀ str : String, pipelineKind str →
    HasIdent.ident (P := P) str ∉ Block.initVars ss

end Imperative

end -- public section
