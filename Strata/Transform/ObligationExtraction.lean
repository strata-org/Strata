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

After partial evaluation and deduplication, a procedure body contains only:
- `assume` statements (path conditions)
- `assert` statements (proof obligations)
- `cover` statements (proof obligations)
- non-deterministic terminal branching (`if *`)
- `var` declarations (from deduplication or global initialization)

This pass reconstructs path conditions by tracking `assume` statements
encountered on the path to each `assert`/`cover`.
-/

public section

namespace Core.ObligationExtraction

open Lambda Imperative

/-- Extract proof obligations from a procedure body, reconstructing path
    conditions from the program structure.

    `pathConditions` accumulates the current path conditions (from `assume`
    statements and ITE branch conditions) as we walk the statement tree.

    Returns (obligations, final path conditions). -/
private partial def extractFromStatements
    (pathConditions : PathConditions Expression)
    (ss : Statements) : Except String (Array (ProofObligation Expression) × PathConditions Expression) :=
  go pathConditions ss #[]
where
  go (pc : PathConditions Expression) : Statements →
      Array (ProofObligation Expression) →
      Except String (Array (ProofObligation Expression) × PathConditions Expression)
  | [], acc => .ok (acc, pc)
  | s :: rest, acc =>
    match s with
    | .ite .nondet thenSs elseSs _md =>
      -- PE ensures nondet branching is the last statement in a sequence.
      if !rest.isEmpty then
        .error "ObligationExtraction: .ite .nondet must be the last statement (rest is non-empty)"
      else do
        let (thenObs, _) ← extractFromStatements pc thenSs
        let (elseObs, _) ← extractFromStatements pc elseSs
        .ok (thenObs ++ elseObs ++ acc, pc)
    | _ => do
      let (acc', pc') ← extractFromStatement pc s acc
      go pc' rest acc'

  extractFromStatement (pc : PathConditions Expression) (s : Statement)
      (acc : Array (ProofObligation Expression)) :
      Except String (Array (ProofObligation Expression) × PathConditions Expression) :=
    match s with
    | .cmd (.cmd (.assert label e md)) =>
      let propType := match md.getPropertyType with
        | some s => if s == MetaData.divisionByZero then .divisionByZero else .assert
        | none => .assert
      .ok (acc.push (ProofObligation.mk label propType pc e md), pc)

    | .cmd (.cmd (.cover label e md)) =>
      .ok (acc.push (ProofObligation.mk label .cover pc e md), pc)

    | .cmd (.cmd (.assume label e _md)) =>
      -- Add assumption to path conditions
      .ok (acc, pc.insert label e)

    | .ite .nondet thenSs elseSs _md => do
      let (thenObs, _) ← extractFromStatements pc thenSs
      let (elseObs, _) ← extractFromStatements pc elseSs
      .ok (thenObs ++ elseObs ++ acc, pc)

    | .ite (.det _) _ _ _ =>
      .error "ObligationExtraction: .ite (.det _) is unsupported; PE should have resolved all deterministic branches"

    | .block _label innerSs _md => do
      -- Process inner statements; propagate path conditions from the block
      -- so that assumes inside blocks are visible to subsequent statements.
      let (innerObs, innerPc) ← extractFromStatements pc innerSs
      .ok (acc ++ innerObs, innerPc)

    | .cmd (.cmd (.init name ty (.det e) _md)) =>
      -- Variable definitions become equalities in the path conditions,
      -- so the SMT solver knows the variable's value.
      let varTy := if h : ty.isMonoType then some (ty.toMonoType h) else none
      let varExpr : Expression.Expr := .fvar () name varTy
      .ok (acc, pc.insert name.toPretty (.eq () varExpr e))

    | .cmd (.cmd (.init _ _ _ _)) => .ok (acc, pc)
    | .cmd (.cmd (.set _ _ _)) => .ok (acc, pc)
    | .cmd (.call _ _ _ _) => .ok (acc, pc)
    | .funcDecl _ _ => .ok (acc, pc)
    | .typeDecl _ _ => .ok (acc, pc)
    | .exit _ _ => .ok (acc, pc)
    | .loop _ _ _ _ _ => .ok (acc, pc)

/-- Extract proof obligations from a program. Axioms become global assumptions
    that are prepended to the path conditions of every obligation. -/
def extractObligations (p : Program) : Except String (ProofObligations Expression) := do
  -- Collect axioms as global path conditions
  let axiomPc : PathCondition Expression := p.decls.filterMap fun decl =>
    match decl with
    | .ax a _ => some (toString a.name, a.e)
    | _ => none
  let globalPc : PathConditions Expression := [axiomPc]
  -- Extract obligations from each procedure
  let mut revObs : Array (ProofObligation Expression) := #[]
  for decl in p.decls do
    match decl with
    | .proc proc _md =>
      let (obs, _) ← extractFromStatements globalPc proc.body
      revObs := revObs ++ obs
    | _ => pure ()
  return revObs

end Core.ObligationExtraction

end -- public section
