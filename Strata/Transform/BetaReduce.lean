/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import all Strata.DL.Imperative.Stmt

/-! # Beta Reduction

Core-to-Core transformation that beta-reduces directly-applied lambda redexes
(`(fun x => body)(arg)`) in every expression of the program: function
definition bodies and axioms (top-level, recursive, and locally declared via
`funcDecl` statements), top-level axioms, `distinct` facts, procedure spec
clauses, and all statement expressions in procedure bodies (structured and
CFG form).

Such redexes arise from front-end lowerings that name an intermediate value
with a `let`-style binding. For example, a pattern-match binding like Java's
`instanceof` pattern (`if (r instanceof Circle c) { … c … }`, which introduces
`c` as a name for the checked value `r`) lowers to the redex
`(fun c => … c …)(r)` — a *let-alias* redex. Argument-value preconditions
supplied by a front end can likewise inject constant-lambda redexes
`(fun ignored => e)(arg)` into obligation expressions. The SMT encoder cannot
encode an `.app` of an abstraction, so such redexes must be contracted before
encoding.

The phase is currently scheduled at the end of `corePipelinePhases`; in
principle it could run at any point after type checking. Reduction uses the
erasing `LExpr.betaReduceRedexes`. The termination checker — the one consumer
that must not erase calls hidden in dead arguments — does not rely on this
phase: it runs on the unreduced program with its own non-erasing
`betaReduceRedexesPreservingArgs`.

Genuine higher-order function bodies still contain an abstraction after
reduction; the SMT encoder continues to reject those with its existing
diagnostics.
-/

public section

namespace Core.BetaReduce

open Lambda Imperative

/-- Beta-reduce every expression of a top-level function declaration: its body,
    axioms, preconditions, and measure. -/
private def reduceFunction (f : Function) : Function :=
  { f with
    body := f.body.map LExpr.betaReduceRedexes
    axioms := f.axioms.map LExpr.betaReduceRedexes
    preconditions := f.preconditions.map fun pc => { pc with expr := LExpr.betaReduceRedexes pc.expr }
    measure := f.measure.map LExpr.betaReduceRedexes }

/-- Beta-reduce every expression of a locally-declared function (a `funcDecl`
    statement): its body, axioms, preconditions, and measure. The SMT factory
    registers these bodies verbatim (`collectFuncDecls` in `Verifier.lean`), so
    they need the same reduction as top-level function bodies. -/
private def reducePureFunc (decl : Imperative.PureFunc Expression) :
    Imperative.PureFunc Expression :=
  { decl with
    body := decl.body.map LExpr.betaReduceRedexes
    axioms := decl.axioms.map LExpr.betaReduceRedexes
    preconditions := decl.preconditions.map fun pc => { pc with expr := LExpr.betaReduceRedexes pc.expr }
    measure := decl.measure.map LExpr.betaReduceRedexes }

mutual
/-- Beta-reduce all expressions in a statement. Unlike
    `Imperative.Stmt.mapExpr` (which treats `funcDecl` as a leaf), this
    traversal recurses into locally-declared functions, so a redex inside a
    nested `funcDecl` body is reduced like any other function body. -/
private def reduceStmt (s : Statement) : Statement :=
  match s with
  | .cmd c => .cmd (Command.mapExpr LExpr.betaReduceRedexes c)
  | .block l ss md => .block l (reduceBlock ss) md
  | .ite (.det c) tss ess md =>
    .ite (.det (LExpr.betaReduceRedexes c)) (reduceBlock tss) (reduceBlock ess) md
  | .ite .nondet tss ess md =>
    .ite .nondet (reduceBlock tss) (reduceBlock ess) md
  | .loop (.det g) measure inv body md =>
    .loop (.det (LExpr.betaReduceRedexes g)) (measure.map LExpr.betaReduceRedexes)
      (inv.map fun (l, e) => (l, LExpr.betaReduceRedexes e)) (reduceBlock body) md
  | .loop .nondet measure inv body md =>
    .loop .nondet (measure.map LExpr.betaReduceRedexes)
      (inv.map fun (l, e) => (l, LExpr.betaReduceRedexes e)) (reduceBlock body) md
  | .exit l md => .exit l md
  | .funcDecl decl md => .funcDecl (reducePureFunc decl) md
  | .typeDecl tc md => .typeDecl tc md
  termination_by Imperative.Stmt.sizeOf s

/-- Beta-reduce all expressions in a block of statements. -/
private def reduceBlock (ss : List Statement) : List Statement :=
  match ss with
  | [] => []
  | s :: rest => reduceStmt s :: reduceBlock rest
  termination_by Imperative.Block.sizeOf ss
end

/-- Beta-reduce all expressions in a deterministic basic block: its commands
    and its transfer guard. -/
private def reduceDetBlock (blk : Imperative.DetBlock String Command Expression) :
    Imperative.DetBlock String Command Expression :=
  { cmds := blk.cmds.map (Command.mapExpr LExpr.betaReduceRedexes)
    transfer :=
      match blk.transfer with
      | .condGoto p lt lf md => .condGoto (LExpr.betaReduceRedexes p) lt lf md
      | .finish md => .finish md }

/-- Beta-reduce all lambda redexes in every expression of the program. -/
def betaReduceProgram (p : Program) : Program :=
  { decls := p.decls.map fun decl =>
      match decl with
      | .proc proc md =>
        let spec := { proc.spec with
          preconditions := proc.spec.preconditions.map
            fun (n, c) => (n, { c with expr := LExpr.betaReduceRedexes c.expr }),
          postconditions := proc.spec.postconditions.map
            fun (n, c) => (n, { c with expr := LExpr.betaReduceRedexes c.expr }) }
        let body := match proc.body with
          | .structured ss => .structured (reduceBlock ss)
          | .cfg g => .cfg { g with blocks := g.blocks.map fun (l, b) => (l, reduceDetBlock b) }
        .proc { proc with spec := spec, body := body } md
      | .func f md => .func (reduceFunction f) md
      | .recFuncBlock fs md => .recFuncBlock (fs.map reduceFunction) md
      | .ax a md => .ax { a with e := LExpr.betaReduceRedexes a.e } md
      | .distinct n es md => .distinct n (es.map LExpr.betaReduceRedexes) md
      | d => d }

end Core.BetaReduce

/-- BetaReduce pipeline phase: contracts directly-applied lambda redexes in
    every program expression, so the SMT encoder never sees a reducible `.app`
    of an abstraction. Model-preserving: beta reduction does not change the
    value of any expression. -/
def Core.betaReducePipelinePhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "betaReduce" fun prog => do
    return (true, Core.BetaReduce.betaReduceProgram prog)

end -- public section
