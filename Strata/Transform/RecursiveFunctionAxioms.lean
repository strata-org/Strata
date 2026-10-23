/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.Simplify
import Strata.DL.Lambda.RecursiveAxioms

/-! # Per-constructor axioms for recursive functions

A recursive function with a `@[cases]` parameter reaches the solver as an uninterpreted
function, described by one axiom per constructor of that parameter's datatype:
`f(C(x̄)) = body[C(x̄)]`, its body unfolded once. Symbolic evaluation generates these
axioms as it builds the obligation program. A pipeline that does not run symbolic
evaluation needs them generated another way, or a valid assertion about `f` on a
symbolic argument fails with a spurious counterexample. This phase generates them on the
program as it stands. -/

public section

namespace Core

/-- Pre-compute the per-constructor axioms for a recursive function with a
    `@[cases]` parameter and store them in the function's `axioms` field.

    Generating the axioms before encoding lets the encoder consume `func.axioms`
    directly and keeps it independent of transient evaluation state.

    Non-recursive functions, recursive functions without `@[cases]`
    (e.g. int-recursive functions encoded as pure UFs), and functions that
    already carry axioms are returned unchanged, so generating twice, by
    `recursiveAxioms` and then by symbolic evaluation, adds nothing. Core's surface
    syntax gives a function no axioms of its own, so an axiom on a recursive
    function is one generated here. -/
def generateRecursiveAxioms (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (exprEval : Expression.Expr → Expression.Expr) (func : Lambda.LFunc CoreLParams) :
    Except Strata.Message (Lambda.LFunc CoreLParams) := do
  if func.isRecursive && (Strata.DL.Util.FuncAttr.findInlineIfConstr func.attr).isSome &&
      func.axioms.isEmpty then
    match Lambda.genRecursiveAxioms func tf exprEval () with
    | .ok recAxioms => .ok { func with axioms := recAxioms }
    | .error msg => throw (Strata.Message.fromFormat msg)
  else
    .ok func

namespace RecursiveAxioms

open Core.Simplify

/-- `f` with its per-constructor axioms, as `generateRecursiveAxioms` gives them. -/
def withRecursiveAxioms (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (pe : Expression.Expr → Expression.Expr) (f : Function) : Except Strata.Message Function := do
  let lf ← generateRecursiveAxioms tf pe f.toLFunc
  return { f with axioms := lf.axioms }

/-- Attach per-constructor axioms to every recursive `@[cases]` function of `p`.

    Each axiom's right-hand side is the function's body applied to a constructor and
    folded, against the program's own factory with unconditional `inline` withheld, as
    symbolic evaluation folds it.

    With `recursiveFnsAsDefineFunRec` the back end emits each recursive function's
    definition itself, so, as in symbolic evaluation, no axiom is generated. -/
def run (options : VerifyOptions) (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  if options.recursiveFnsAsDefineFunRec then return (false, p)
  let tf : @Lambda.TypeFactory CoreLParams.IDMeta := (p.decls.filterMap fun
    | .type (.data d) _ => some d
    | _ => none).toArray
  let F := withoutInline (lambdaCarriers p) (← programFactory p)
  let pe := fold F (Ctx.ofFactory F).evalFuel
  let mut changed := false
  let mut decls := #[]
  for d in p.decls do
    match d with
    | .recFuncBlock fs md =>
      let fs' ← Transform.liftDiag (fs.mapM (withRecursiveAxioms tf pe))
      if fs' != fs then changed := true
      decls := decls.push (.recFuncBlock fs' md)
    | other => decls := decls.push other
  return (changed, { p with decls := decls.toList })

end RecursiveAxioms
end Core

/-- Recursive-function axioms pipeline phase.

    Model-preserving: each axiom is an equation the function's definition satisfies, so
    it holds in every model of the program and removes none. It changes only function
    declarations, adding axioms, so it preserves every fact about procedure bodies,
    contracts and polymorphism. It does not claim `noBetaRedexes`, which `betaReduce`
    establishes after it. -/
def Core.recursiveAxiomsPhase (options : VerifyOptions := VerifyOptions.default) :
    Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "recursiveAxioms" (Core.RecursiveAxioms.run options)
    (requires := factSet![])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment,
                         .noPrecondsFromFuncs, .noNondetGuards, .hasObligationForm,
                         .noProcedureContracts, .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .typeAnnotated])

end
