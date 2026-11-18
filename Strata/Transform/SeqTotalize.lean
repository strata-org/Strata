/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import Strata.Languages.Core.Factory

/-! # Checked sequence operations to their total twins

Core has two forms of the partial sequence operations: a checked one with a
bounds precondition (`Sequence.select`, `Sequence.update`, `Sequence.take`,
`Sequence.drop`) and a total twin without it (`Sequence.select!`, ...). They
denote the same function; they differ only in the obligation the checked form
carries. `PrecondElim` turns that obligation into an assertion ahead of the
statement, and from then on the two forms are interchangeable.

This pass runs after `PrecondElim` and rewrites every checked operation in the
program to its total twin, so that everything downstream, the symbolic
evaluator, the encoders and the factory axioms (stated over the total forms),
sees one symbol per operation and a fact proved about either form applies to
the other. Nothing else about the program changes.
-/

public section

namespace Core.SeqTotalize

open Lambda

/-- The checked sequence operations and their total twins, by factory name. -/
def pairs : List (WFLFunc CoreLParams × WFLFunc CoreLParams) :=
  [ (seqSelectFunc, seqSelectUnsafeFunc),
    (seqUpdateFunc, seqUpdateUnsafeFunc),
    (seqTakeFunc, seqTakeUnsafeFunc),
    (seqDropFunc, seqDropUnsafeFunc) ]

/-- Rewrite each checked operation to its total twin, keeping the occurrence's
    own type annotation. The renamed operator gets a synthesized location, as
    the operator renaming in `Factory.lean` does; the enclosing application keeps
    the source location. -/
def totalize (e : Expression.Expr) : Expression.Expr :=
  e.substOps (Strata.Util.HMap.ofList (pairs.map fun (checked, total) =>
    (checked.name, fun ty => .op (ExprSourceLoc.synthesized "seqTotalize") total.name ty)))

private def totalizeFunction (f : Function) : Function :=
  { f with
    body := f.body.map totalize
    axioms := f.axioms.map totalize
    preconditions := f.preconditions.map fun pc => { pc with expr := totalize pc.expr }
    measure := f.measure.map totalize }

/-- Rewrite the commands and the branch conditions of a CFG body. -/
private def totalizeCFG (g : DetCFG) : DetCFG :=
  { g with blocks := g.blocks.map fun (l, b) =>
      (l, { b with
        cmds := b.cmds.map (Command.mapExpr totalize)
        transfer := match b.transfer with
          | .condGoto e lt lf md => .condGoto (totalize e) lt lf md
          | t => t }) }

/-- Rewrite the contract and the body of a procedure, whether the body is structured
    or a CFG. -/
private def totalizeProcedure (proc : Procedure) : Procedure :=
  let proc := proc.mapExprs totalize
  match proc.body with
  | .cfg g => { proc with body := .cfg (totalizeCFG g) }
  | .structured _ => proc

/-- Rewrite every expression of the program, and report whether anything changed.
    It leaves the transform state, cached analyses included, as it is: renaming an
    operator adds or removes no call, so a cached call graph stays valid. -/
def totalizeProgram (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  let p' : Program :=
    { decls := p.decls.map fun decl =>
        match decl with
        | .proc proc md => .proc (totalizeProcedure proc) md
        | .func f md => .func (totalizeFunction f) md
        | .recFuncBlock fs md => .recFuncBlock (fs.map totalizeFunction) md
        | .ax a md => .ax { a with e := totalize a.e } md
        | .lemma l md => .lemma { l with e := totalize l.e } md
        | .distinct n es md => .distinct n (es.map totalize) md
        | d => d }
  return (decide (p' ≠ p), p')

end Core.SeqTotalize

/-- SeqTotalize pipeline phase: after the bounds obligations of the checked
    sequence operations have been emitted, replace each by its total twin.
    Model-preserving: the two forms denote the same function. Renaming an
    operator changes no statement, binder or redex, so every fact carries
    over; `noPrecondsFromFuncs` is required because the obligations must
    already be in place when the checked form disappears. -/
def Core.seqTotalizePipelinePhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "seqTotalize"
    (requires := factSet![.noPrecondsFromFuncs])
    (preserves := factSet![.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops,
                         .noLoopInvariants, .noLoopMeasures, .uniqueInits, .loopBodyNoInits,
                         .staticSingleAssignment, .noBetaRedexes, .noPrecondsFromFuncs,
                         .noNondetGuards, .hasObligationForm, .noProcedureContracts,
                         .noPolymorphicProcedures, .noPolymorphicFunctions, .typeAnnotated,
                         .noInits, .treeForm, .exitsCovered, .armsHaveObligations])
    Core.SeqTotalize.totalizeProgram

end -- public section
