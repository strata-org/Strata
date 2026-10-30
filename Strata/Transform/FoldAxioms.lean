/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.Simplify

/-! # Fold axioms

A Core-to-Core phase that folds each axiom without quantifiers with `LExpr.eval`,
using the folding factory `simplify` uses. An axiom `g(0) == Box..w(box())`, where
`box()` is an inline function returning the constructor application `MkBox(5)`,
becomes `g(0) == 5`.

`simplify` rewrites procedures and lemmas, not axioms, and in a pipeline that inlines
functions after `simplify` an axiom's constructor applications only appear later.
This phase can run wherever they have appeared; `equalitySimplification` then reads
the folded axioms as facts.
-/

public section

namespace Core.FoldAxioms

open Lambda Imperative

/-- `e` folded with `F`, or `e` itself when the fold leaves a beta redex, so that the
    phase preserves `noBetaRedexes`. -/
def foldAxiom (F : Expression.Factory) (fuel : Nat) (e : Expression.Expr) : Expression.Expr :=
  let e' := Simplify.fold F fuel e
  if e'.noBetaRedex then e' else e

/-- Fold every axiom of `p` that has no bound variable. -/
def runFoldAxioms (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  let ctx := Simplify.Ctx.ofFactory (← Simplify.programFactory p) (Simplify.lambdaCarriers p)
  let decls := p.decls.map fun d =>
    match d with
    | .ax a md =>
      if a.e.hasBVar then d else .ax { a with e := foldAxiom ctx.foldFactory ctx.evalFuel a.e } md
    | other => other
  let p' := { p with decls := decls }
  return (decide (p' ≠ p), p')

end Core.FoldAxioms

/-- Axiom folding pipeline phase.

    Model-preserving: folding replaces an axiom by one equal to it in every model, since
    `LExpr.eval` only takes steps of the Lambda semantics. It needs no function to carry
    a precondition, since folding can expand a function body, which is only right where
    its precondition holds. It changes only axioms, so it preserves every fact about
    procedure bodies, and `noBetaRedexes` because a fold that leaves a redex is
    discarded. -/
def Core.foldAxiomsPhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "foldAxioms" Core.FoldAxioms.runFoldAxioms
    (requires := factSet![.noPrecondsFromFuncs])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment, .noBetaRedexes,
                         .noPrecondsFromFuncs, .noNondetGuards, .hasObligationForm,
                         .noProcedureContracts,
                         .noPolymorphicProcedures, .noPolymorphicFunctions,
                         .typeAnnotated])

end
