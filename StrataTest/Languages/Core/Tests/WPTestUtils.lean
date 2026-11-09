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

Checks on the phases' outputs: nothing follows an `assert` (`NoStmtAfterAssert`), the names an
output declares (`stmtsInits`), and the duplication checker (`noDuplication`). -/

meta section

public section

namespace Strata.WPTestUtils

open _root_.Core Imperative Imperative.BigStep Imperative.WP

/-- The two modes the tests compare, each with its name: symbolic evaluation and
    `--vcgen wp`. -/
def modes : List (String × Core.VerifyOptions) :=
  [("symbolic", Core.VerifyOptions.quiet), ("wp", { Core.VerifyOptions.quiet with vcgen := .wp })]

/-- Prints one line `pre label: proved` or `pre label: not proved` per obligation of `pgm`,
    verified with `opts` and, when given, `pipeline`. -/
def printProved (pgm : StrataDDM.SourcedProgram) (opts : Core.VerifyOptions := .quiet)
    (pipeline : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := none)
    (pre : String := "") : IO Unit := do
  for r in ← Core.verify pgm (options := opts) (pipeline := pipeline) do
    IO.println s!"{pre}{r.obligation.label}: {if r.isSuccess then "proved" else "not proved"}"

/-- Prints, for each of the two `modes`, the lines of `printProved` on `pgm`, each prefixed
    by the mode's name. -/
def printModesProved (pgm : StrataDDM.SourcedProgram) : IO Unit := do
  for (mode, opts) in modes do printProved pgm opts (pre := s!"{mode} ")

/-- Prints, for each of the two `modes`, one line `mode: ` followed by `label verdict` for
    every obligation of `pgm`, comma-separated, the verdict being `proved`, `failed` or
    `unknown`; sorted by label when `sorted` holds, in the verifier's order otherwise. -/
def printModesVerdicts (pgm : StrataDDM.SourcedProgram) (sorted : Bool := false) : IO Unit := do
  for (mode, opts) in modes do
    let rs ← Core.verify pgm (options := opts)
    let vs := rs.toList.map fun r =>
      let v := if r.isSuccess then "proved" else if r.isFailure then "failed" else "unknown"
      s!"{r.obligation.label} {v}"
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

/-- The names declared by the `init`s of a list, at any depth. -/
def stmtsInits : PStmts P → List P.Ident
  | [] => []
  | .cmd (.cmd (.init x _ _ _)) :: rest => x :: stmtsInits rest
  | .ite _ t e _ :: rest => stmtsInits t ++ stmtsInits e ++ stmtsInits rest
  | .block _ b _ :: rest => stmtsInits b ++ stmtsInits rest
  | .loop _ _ _ b _ :: rest => stmtsInits b ++ stmtsInits rest
  | _ :: rest => stmtsInits rest
  termination_by ss => sizeOf ss
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
  | .fvar _ _ _ => .fvar () ⟨"_", ()⟩ none
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
