/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env
import Strata.Transform.ANFEncoder
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

/-- Substitute free variables in an expression according to a substitution map. -/
private partial def substFVars (subst : List (CoreIdent × Expression.Expr))
    (e : Expression.Expr) : Expression.Expr :=
  if subst.isEmpty then e
  else go e
where
  go : Expression.Expr → Expression.Expr
    | .fvar m name ty => match subst.find? (·.1 == name) with
      | some (_, replacement) => replacement
      | none => .fvar m name ty
    | .app m fn arg => .app m (go fn) (go arg)
    | .ite m c t f => .ite m (go c) (go t) (go f)
    | .eq m e1 e2 => .eq m (go e1) (go e2)
    | .abs m n ty body => .abs m n ty (go body)
    | .quant m k n ty tr body => .quant m k n ty (go tr) (go body)
    | e => e

/-- Inline ANF-generated variable definitions in proof obligations.

    ANF encoding introduces temporary variables (`$__anf.N`) that appear as
    equality assumptions in path conditions. These extra equalities can make
    SMT queries harder to solve (causing timeouts). This pass removes ANF
    variable equalities from path conditions and substitutes their values
    into all remaining expressions, keeping the SMT query equivalent to the
    pre-ANF form. -/
def inlineAnfVariables (obs : ProofObligations Expression) : ProofObligations Expression :=
  obs.map fun ob =>
    -- Collect ANF variable substitutions from path conditions.
    -- Each ANF entry has key "$__anf.N" and value (.eq () (.fvar ..) rhs).
    let (subst, cleanedPc) := ob.assumptions.foldl (init := ([], [])) fun (subst, pcs) pc =>
      let (pcSubst, kept) := pc.foldl (init := (subst, [])) fun (subst, kept) (key, expr) =>
        if key.startsWith ANFEncoder.anfVarPrefix then
          match expr with
          | .eq _ (.fvar _ name _) rhs =>
            -- Apply existing substitutions to the RHS before adding
            (subst ++ [(name, substFVars subst rhs)], kept)
          | _ => (subst, kept ++ [(key, expr)])
        else
          (subst, kept ++ [(key, expr)])
      (pcSubst, pcs ++ [kept])
    if subst.isEmpty then ob
    else
      -- Apply substitutions to remaining path condition expressions
      let finalPc := cleanedPc.map fun pc =>
        pc.map fun (key, expr) => (key, substFVars subst expr)
      { ob with
        assumptions := finalPc
        obligation := substFVars subst ob.obligation }

end Core.ObligationExtraction

end -- public section
