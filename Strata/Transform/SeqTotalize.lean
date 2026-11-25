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
denote the same function, at every argument, out of range included: each checked
operation carries a factory axiom stating so, so the rewrite below is valid in every
model of Core's factory, in function bodies, axioms, lemma goals and `distinct`
declarations as well as in statements. They differ only in the obligation the
checked form carries. `PrecondElim` turns that obligation into an assertion ahead of
the statement, and from then on the two forms are interchangeable.

This pass runs after `PrecondElim`, which it requires through
`precondObligationsEmitted`, and rewrites every checked operation in the program to its
total twin, so that the program everything downstream reads, the symbolic evaluator and
the encoders, uses one symbol per operation, and a fact stated with either form applies
to the other. Some factory axioms are also stated with the checked `Sequence.select`
(`withSelectBang`), so a query can still declare it; its agreement axiom relates the
two. Nothing else about the program changes.
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

/-- Rewrite the body, the axioms, the preconditions and the measure of a function. -/
private def totalizeFunction (f : Function) : Function :=
  { f with
    body := f.body.map totalize
    axioms := f.axioms.map totalize
    preconditions := f.preconditions.map fun pc => { pc with expr := totalize pc.expr }
    measure := f.measure.map totalize }

/-- Rewrite the contract and the body of a procedure, whether the body is structured
    or a CFG. -/
private def totalizeProcedure (proc : Procedure) : Procedure :=
  let proc := proc.mapExprs totalize
  match proc.body with
  | .cfg g o =>
    { proc with body := .cfg (DetCFG.mapCmdsGuards g (Command.mapExpr totalize) totalize) o }
  | .structured _ _ | .abstract => proc

/-- Rewrite the functions of a factory that are not Core built-ins, such as those a
    caller supplies with `moreFns`. A call of such a function in the program would
    otherwise unfold to a checked operation, while the program around it uses the total
    twin. The built-ins keep their definitions: the axioms of the sequence operations are
    stated over both forms already. -/
def totalizeFactory (F : @Lambda.Factory CoreLParams) : @Lambda.Factory CoreLParams :=
  F.map (fun f => if f.name.name ∈ Core.Factory then f
    else { f with toFunc := totalizeFunction f.toFunc })
    (fun f => by by_cases h : f.name.name ∈ Core.Factory <;> simp [h, totalizeFunction])

/-- Rewrite every expression of the program and every function of the factory in the
    transform state that is not a Core built-in, and report whether the program or the
    factory changed. It leaves the rest of the transform state, cached analyses included,
    as it is: renaming an operator adds or removes no call, so a cached call graph stays
    valid. -/
def totalizeProgram (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  let F ← Transform.getFactory
  let factoryChanged := F.toArray.any fun f =>
    !(decide (f.name.name ∈ Core.Factory)) && decide (totalizeFunction f.toFunc ≠ f.toFunc)
  if factoryChanged then Transform.setFactory (totalizeFactory F)
  let p' : Program :=
    { p with decls := p.decls.map fun decl =>
        match decl with
        | .proc proc md => .proc (totalizeProcedure proc) md
        | .func f md => .func (totalizeFunction f) md
        | .recFuncBlock fs md => .recFuncBlock (fs.map totalizeFunction) md
        | .ax a md => .ax { a with e := totalize a.e } md
        | .lemma l md => .lemma { l with e := totalize l.e } md
        | .distinct n es md => .distinct n (es.map totalize) md
        | .type .. => decl }
  return (factoryChanged || decide (p' ≠ p), p')

end Core.SeqTotalize

/-- SeqTotalize pipeline phase: `totalizeProgram`, which the module header justifies.
    Model-preserving: a model of the output, with each checked operation interpreted
    as its twin, is a model of the input. It requires `precondObligationsEmitted`, which
    only `PrecondElim` establishes, so the bounds obligations are in place before the
    checked forms disappear; `noPrecondsFromFuncs` alone would let an order that asserts
    it and runs `PrecondElim` later drop them. It preserves every other fact, since
    renaming an operator changes no statement, binder or redex. -/
def Core.seqTotalizePipelinePhase : Core.PipelinePhase :=
  -- Renaming an operator introduces no `$__` name, so the recorded prefixes stay accurate.
  Core.modelPreservingPipelinePhase "seqTotalize" (maintainsIdentPrefixes := true)
    (requires := factSet![.noPrecondsFromFuncs, .precondObligationsEmitted])
    (preserves := factSet![.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops,
                         .noLoopInvariants, .noLoopMeasures, .uniqueInits, .loopBodyNoInits,
                         .staticSingleAssignment, .noBetaRedexes, .noLambdas,
                         .noPrecondsFromFuncs, .precondObligationsEmitted,
                         .noNondetGuards, .hasObligationForm, .noProcedureContracts,
                         .noPolymorphicProcedures, .noPolymorphicFunctions, .typeAnnotated,
                         .noInits, .treeForm, .exitsCovered, .armsHaveObligations,
                         .noCFGCycles])
    Core.SeqTotalize.totalizeProgram

end -- public section
