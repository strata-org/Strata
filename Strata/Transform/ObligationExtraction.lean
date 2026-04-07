/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env

/-! # Proof Obligation Extraction

A Core-to-obligations pass that walks a post-PE program and extracts proof
obligations with their path conditions reconstructed from the program structure.

After partial evaluation, a procedure body contains only:
- `assume` statements (path conditions)
- `assert` statements (proof obligations)
- `cover` statements (proof obligations)
- `if-then-else` statements (control flow / non-deterministic branching)
- `var` declarations (from deduplication or global initialization)

This pass reconstructs path conditions by tracking `assume` statements and
ITE branch conditions encountered on the path to each `assert`/`cover`.
-/

public section

namespace Core.ObligationExtraction

open Lambda Imperative

/-- Extract proof obligations from a procedure body, reconstructing path
    conditions from the program structure.

    `pathConditions` accumulates the current path conditions (from `assume`
    statements and ITE branch conditions) as we walk the statement tree.

    Returns obligations in reverse order; caller reverses. -/
private partial def extractFromStatements
    (pathConditions : PathConditions Expression)
    (ss : Statements) : Array (ProofObligation Expression) :=
  go pathConditions ss #[]
where
  go (pc : PathConditions Expression) : Statements →
      Array (ProofObligation Expression) → Array (ProofObligation Expression)
  | [], acc => acc
  | s :: rest, acc =>
    let (acc', pc') := extractFromStatement pc s acc
    go pc' rest acc'

  extractFromStatement (pc : PathConditions Expression) (s : Statement)
      (acc : Array (ProofObligation Expression)) :
      Array (ProofObligation Expression) × PathConditions Expression :=
    match s with
    | .cmd (.cmd (.assert label e md)) =>
      let propType := match md.getPropertyType with
        | some s => if s == MetaData.divisionByZero then .divisionByZero else .assert
        | none => .assert
      (acc.push (ProofObligation.mk label propType pc e md), pc)

    | .cmd (.cmd (.cover label e md)) =>
      (acc.push (ProofObligation.mk label .cover pc e md), pc)

    | .cmd (.cmd (.assume label e _md)) =>
      -- Add assumption to path conditions
      (acc, pc.insert label e)

    | .ite (.det cond) thenSs elseSs _md =>
      let thenLabel := toString (f!"<label_ite_cond_true: {cond.eraseTypes}>")
      let elseLabel := toString (f!"<label_ite_cond_false: !{cond.eraseTypes}>")
      let pcThen := pc.push [(thenLabel, cond)]
      let pcElse := pc.push [(elseLabel, (.ite () cond (LExpr.false ()) (LExpr.true ())))]
      -- Check for dead branches (condition is literal true/false)
      if cond.isTrue then
        -- Then branch is live, else branch is dead
        let acc := acc ++ extractFromStatements pcThen thenSs
        let acc := collectDeadBranch pcElse elseSs acc
        (acc, pc)
      else if cond.isFalse then
        -- Else branch is live, then branch is dead
        let acc := collectDeadBranch pcThen thenSs acc
        let acc := acc ++ extractFromStatements pcElse elseSs
        (acc, pc)
      else
        -- Both branches are live
        let acc := acc ++ extractFromStatements pcThen thenSs
        let acc := acc ++ extractFromStatements pcElse elseSs
        (acc, pc)

    | .ite .nondet thenSs elseSs _md =>
      let acc := extractFromStatements pc thenSs ++ acc
      let acc := extractFromStatements pc elseSs ++ acc
      (acc, pc)

    | .block _label innerSs _md =>
      let innerObs := extractFromStatements pc innerSs
      (acc ++ innerObs, pc)

    | .cmd (.cmd (.init name ty (.det e) _md)) =>
      -- Variable definitions become equalities in the path conditions,
      -- so the SMT solver knows the variable's value.
      let varTy := if h : ty.isMonoType then some (ty.toMonoType h) else none
      let varExpr : Expression.Expr := .fvar () name varTy
      (acc, pc.insert name.toPretty (.eq () varExpr e))

    | .cmd (.cmd (.init _ _ _ _)) => (acc, pc)
    | .cmd (.cmd (.set _ _ _)) => (acc, pc)
    | .cmd (.call _ _ _ _) => (acc, pc)
    | .funcDecl _ _ => (acc, pc)
    | .typeDecl _ _ => (acc, pc)
    | .exit _ _ => (acc, pc)
    | .loop _ _ _ _ _ => (acc, pc)

  /-- Collect obligations from a dead (unreachable) branch. Covers become
      false obligations, asserts become true obligations. -/
  collectDeadBranch (pc : PathConditions Expression) (ss : Statements)
      (acc : Array (ProofObligation Expression)) :
      Array (ProofObligation Expression) :=
    ss.foldl (fun acc s => collectDeadStatement pc s acc) acc

  collectDeadStatement (pc : PathConditions Expression) (s : Statement)
      (acc : Array (ProofObligation Expression)) :
      Array (ProofObligation Expression) :=
    match s with
    | .cmd (.cmd (.cover label _e md)) =>
      acc.push (ProofObligation.mk label .cover pc (LExpr.false ()) md)
    | .cmd (.cmd (.assert label _e md)) =>
      let propType := match md.getPropertyType with
        | some s => if s == MetaData.divisionByZero then .divisionByZero else .assert
        | none => .assert
      acc.push (ProofObligation.mk label propType pc (LExpr.true ()) md)
    | .ite _ thenSs elseSs _ =>
      let acc := collectDeadBranch pc thenSs acc
      collectDeadBranch pc elseSs acc
    | .block _ innerSs _ => collectDeadBranch pc innerSs acc
    | .loop _ _ _ bodySs _ => collectDeadBranch pc bodySs acc
    | _ => acc

/-- Extract proof obligations from a program. Axioms become global assumptions
    that are prepended to the path conditions of every obligation. -/
def extractObligations (p : Program) : ProofObligations Expression :=
  -- Collect axioms as global path conditions
  let axiomPc : PathCondition Expression := p.decls.filterMap fun decl =>
    match decl with
    | .ax a _ => some (toString a.name, a.e)
    | _ => none
  let globalPc : PathConditions Expression := [axiomPc]
  -- Extract obligations from each procedure
  let revObs := p.decls.foldl (fun acc decl =>
    match decl with
    | .proc proc _md =>
      let obs := extractFromStatements globalPc proc.body
      acc ++ obs
    | _ => acc) #[]
  revObs

end Core.ObligationExtraction

end -- public section
