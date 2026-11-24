/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core.Verifier
public meta import Strata.Languages.Core
public meta import Strata.MetaVerifier
public meta import StrataDDM.SourcedProgram
import Strata.DL.Imperative.Stmt

/-! # Helpers of the tests of the WP and SSA phases

Verdict printing: the tests of `--vcgen wp` run `Core.verify` on a program in symbolic mode and
under `--vcgen wp` and print one verdict per obligation, so that `#guard_msgs` compares the two
modes.

Checks on the phases' outputs: nothing follows an `assert` (`NoStmtAfterAssert`), and the
duplication checker (`noDuplication`). -/

meta section

public section

namespace Strata.WPTestUtils

open _root_.Core Imperative Imperative.BigStep Imperative.WP

/-- The two modes the tests compare, each with its name: symbolic evaluation and
    `--vcgen wp`. -/
def modes : List (String × Core.VerifyOptions) :=
  [("symbolic", Core.VerifyOptions.quiet), ("wp", { Core.VerifyOptions.quiet with vcgen := .wp })]

/-- `unknown` when the solver answered unknown to both checks, `error` when the pipeline or the
    solver failed (an SMT encoding error, a solver crash or a timeout), and `other` otherwise. -/
def errorUnknownOrOther (r : Core.VCResult) : String :=
  if r.isUnknown then "unknown"
  else if r.isImplementationError || r.isTimeout then "error"
  else "other"

/-- The verdict of the obligation result `r`. A cover is `covered` when the solver finds it
    satisfiable and `uncovered` when it finds it unsatisfiable. Any other obligation is `proved`
    when the solver proves it, and `refuted` when the validity check is `sat`, that is when the
    solver found a counterexample (a model of the query, which may be spurious when the query
    over-approximates the program; only `proved` is certified). Otherwise the verdict is
    `errorUnknownOrOther`, whose `other` makes a new kind of outcome show in a test instead of
    reading as one of the named ones. -/
def verdict (r : Core.VCResult) : String :=
  if r.obligation.property == .cover then
    if r.outcome matches .ok { satisfiabilityProperty := .sat _, .. } then "covered"
    else if r.outcome matches .ok { satisfiabilityProperty := .unsat, .. } then "uncovered"
    else errorUnknownOrOther r
  else if r.isSuccess then "proved"
  else if r.outcome matches .ok { validityProperty := .sat _, .. } then "refuted"
  else errorUnknownOrOther r

/-- The line `pre label: v` for the obligation result `r`, `v` being its `verdict`. -/
def provedLine (pre : String) (r : Core.VCResult) : String :=
  s!"{pre}{r.obligation.label}: {verdict r}"

/-- Prints `provedLine pre r` for each obligation result `r` of `pgm`, verified with `opts` and,
    when given, `pipeline`. -/
def printProved (pgm : StrataDDM.SourcedProgram) (opts : Core.VerifyOptions := .quiet)
    (pipeline : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := none)
    (pre : String := "") : IO Unit := do
  for r in ← Core.verify pgm (options := opts) (pipeline := pipeline) do
    IO.println (provedLine pre r)

/-- Prints, for each of the two `modes`, the lines of `printProved` on `pgm`, each prefixed
    by the mode's name. -/
def printModesProved (pgm : StrataDDM.SourcedProgram) : IO Unit := do
  for (mode, opts) in modes do printProved pgm opts (pre := s!"{mode} ")

/-- Prints, for each of the two `modes`, one line `mode: ` followed by `label verdict` for
    every obligation of `pgm`, comma-separated, the verdict being its `verdict`; sorted by label when `sorted` holds, in the verifier's order otherwise. -/
def printModesVerdicts (pgm : StrataDDM.SourcedProgram) (sorted : Bool := false) : IO Unit := do
  for (mode, opts) in modes do
    let rs ← Core.verify pgm (options := opts)
    let vs := rs.toList.map fun r =>
      s!"{r.obligation.label} {verdict r}"
    IO.println s!"{mode}: {", ".intercalate (if sorted then vs.mergeSort (· ≤ ·) else vs)}"

/-! ## Checks on the outputs of the phases -/

section
variable {P : PureExpr}

/-- Every `.assert` is the last statement of its list; branches recurse. -/
def NoStmtAfterAssert : PStmts P → Bool
  | [] => true
  | (.cmd (.cmd (.assert _ _ _))) :: rest => rest.isEmpty
  | (.ite _ thenSs elseSs _) :: rest =>
      NoStmtAfterAssert thenSs && NoStmtAfterAssert elseSs && NoStmtAfterAssert rest
  | _ :: rest => NoStmtAfterAssert rest
end

/-! ## Duplication checker

`noDuplication input output` checks, for every expression of the loop-free statement
list `input` that applies an operator (a factory function or an abstraction), that the
number of top-level expressions of `output` containing a subterm with the same
*skeleton* (the expression with every free variable replaced by a placeholder, so a
renaming does not change it) is at most the number of top-level expressions of
`input` containing one.  Expressions built only from variables, literals, `ite` and
`==` are not checked: they are what the pass emits for guards, reachability and
merges. -/

/-- The expression with every free variable replaced by a placeholder. -/
def skeleton : Expression.Expr → Expression.Expr
  | .fvar _ _ _ => .fvar Core.valueLoc ⟨"_", ()⟩ none
  | .abs m n ty e => .abs m n ty (skeleton e)
  | .quant m k n ty tr e => .quant m k n ty (skeleton tr) (skeleton e)
  | .app m f a => .app m (skeleton f) (skeleton a)
  | .ite m c t e => .ite m (skeleton c) (skeleton t) (skeleton e)
  | .eq m a b => .eq m (skeleton a) (skeleton b)
  | e => e

/-- Does the expression apply an operator (a factory function, an abstraction or a
    quantifier)? -/
def hasOperator : Expression.Expr → Bool
  | .op _ _ _ | .abs _ _ _ _ | .quant _ _ _ _ _ _ => true
  | .app _ f a => hasOperator f || hasOperator a
  | .ite _ c t e => hasOperator c || hasOperator t || hasOperator e
  | .eq _ a b => hasOperator a || hasOperator b
  | _ => false

/-- All subterms of an expression. -/
def subterms (e : Expression.Expr) : List Expression.Expr :=
  e :: match e with
  | .abs _ _ _ b => subterms b
  | .quant _ _ _ _ tr b => subterms tr ++ subterms b
  | .app _ f a => subterms f ++ subterms a
  | .ite _ c t f => subterms c ++ subterms t ++ subterms f
  | .eq _ a b => subterms a ++ subterms b
  | _ => []

mutual
/-- The top-level expressions of a statement list. -/
def stmtsExprs : Statements → List Expression.Expr
  | [] => []
  | s :: rest => stmtExprs s ++ stmtsExprs rest
def stmtExprs : Statement → List Expression.Expr
  | .cmd (.cmd (.init _ _ (.det e) _)) | .cmd (.cmd (.set _ (.det e) _))
  | .cmd (.cmd (.assume _ e _)) | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.cover _ e _)) => [e]
  | .block _ ss _ => stmtsExprs ss
  | .ite c tss ess _ =>
    (match c with | .det c => [c] | .nondet => []) ++ stmtsExprs tss ++ stmtsExprs ess
  | .loop _ _ _ body _ => stmtsExprs body
  | _ => []
end

/-- Number of expressions in `es` having a subterm whose skeleton is `sk`. -/
def countContaining (sk : Expression.Expr) (es : List Expression.Expr) : Nat :=
  (es.filter fun e => (subterms e).any fun t => skeleton t == sk).length

/-- The duplication check (see the section docstring). -/
def noDuplication (input output : Statements) : Bool :=
  let ins := stmtsExprs input
  let outs := stmtsExprs output
  ins.all fun e =>
    !hasOperator e ||
      let sk := skeleton e
      countContaining sk outs ≤ countContaining sk ins

end Strata.WPTestUtils

end -- public section
end -- meta section
