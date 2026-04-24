/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env
/-! # Proof Obligation Extraction

A Core-to-obligations pass that walks a post-PE, post-dedup program and extracts
proof obligations with their path conditions reconstructed from the program
structure.

After partial evaluation and ANF encoding, a procedure body contains only:
- `assume` statements (path conditions)
- `assert` statements (proof obligations)
- `cover` statements (proof obligations)
- non-deterministic terminal branching (`if *`)
- `var` declarations (from ANF encoding or global initialization)

This pass reconstructs path conditions by tracking `assume` statements
encountered on the path to each `assert`/`cover`.
-/

public section

namespace Core.ObligationExtraction

open Lambda Imperative

/-- Check if a statement list is a valid input for obligation extraction.
    Valid inputs contain only: `assume`, `assert`, `cover`, `var` declarations,
    and non-deterministic branching (`if *`). -/
private def isValidObligationInput : Statements → Bool
  | [] => true
  | s :: rest => isValidObligationStatement s && isValidObligationInput rest
where
  isValidObligationStatement : Statement → Bool
    | .cmd (.cmd (.assert _ _ _)) => true
    | .cmd (.cmd (.assume _ _ _)) => true
    | .cmd (.cmd (.cover _ _ _)) => true
    | .cmd (.cmd (.init _ _ _ _)) => true
    | .ite .nondet thenSs elseSs _ => isValidObligationInput thenSs && isValidObligationInput elseSs
    | _ => false

/-- Extract proof obligations from a procedure body, reconstructing path
    conditions from the program structure.

    `pathConditions` accumulates the current path conditions (from `assume`
    statements and `var` definitions) as we walk the statement tree.

    Returns the extracted obligations. -/
private partial def extractFromStatements
    (pathConditions : PathConditions Expression)
    (ss : Statements) : Except String (Array (ProofObligation Expression)) :=
  go pathConditions ss #[]
where
  go (pc : PathConditions Expression) : Statements →
      Array (ProofObligation Expression) →
      Except String (Array (ProofObligation Expression))
  | [], acc => .ok acc
  | s :: rest, acc =>
    match s with
    | .cmd (.cmd (.assert label e md)) =>
      let propType := match md.getPropertyType with
        | some s => if s == MetaData.divisionByZero then .divisionByZero else .assert
        | none => .assert
      go pc rest (acc.push (ProofObligation.mk label propType pc e md))

    | .cmd (.cmd (.cover label e md)) =>
      go pc rest (acc.push (ProofObligation.mk label .cover pc e md))

    | .cmd (.cmd (.assume label e _md)) =>
      go (pc.addInNewest [(label, e)]) rest acc

    | .ite .nondet thenSs elseSs _md => do
      let thenObs ← extractFromStatements pc thenSs
      let elseObs ← extractFromStatements pc elseSs
      go pc rest (acc ++ thenObs ++ elseObs)

    | .cmd (.cmd (.init name ty (.det e) _md)) =>
      -- Variable definitions become equalities in the path conditions,
      -- so the SMT solver knows the variable's value.
      let varTy := if h : ty.isMonoType then some (ty.toMonoType h) else none
      let varExpr : Expression.Expr := .fvar () name varTy
      go (pc.insert name.toPretty (.eq () varExpr e)) rest acc

    | _other =>
      .error s!"ObligationExtraction: unsupported statement"

/-- Extract proof obligations from a program. Axioms become global assumptions
    that are prepended to the path conditions of every obligation. -/
def extractObligations (p : Program) : Except String (ProofObligations Expression) := do
  -- Accumulate axioms and obligations as we walk declarations in order
  let (_, allObs) ← p.decls.foldlM (init := (([] : PathCondition Expression), (#[] : Array (ProofObligation Expression)))) fun (axiomPc, allObs) decl =>
    match decl with
    | .ax a _ =>
      -- Add axiom to path conditions for subsequent procedures
      .ok (axiomPc ++ [(a.name, a.e)], allObs)
    | .proc proc _md => do
      let globalPc : PathConditions Expression := [axiomPc]
      let obs ← extractFromStatements globalPc proc.body
      .ok (axiomPc, allObs ++ obs)
    | _ => .ok (axiomPc, allObs)
  return allObs

end Core.ObligationExtraction

end -- public section
