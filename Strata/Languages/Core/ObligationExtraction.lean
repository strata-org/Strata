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

mutual
/-- Check if a single statement is valid for obligation extraction. -/
def isValidObligationStatement : Statement → Bool
  | .cmd (.cmd (.assert _ _ _)) => true
  | .cmd (.cmd (.assume _ _ _)) => true
  | .cmd (.cmd (.cover _ _ _)) => true
  | .cmd (.cmd (.init _ _ _ _)) => true
  | .ite .nondet thenSs elseSs _ => isValidObligationInput thenSs && isValidObligationInput elseSs
  | _ => false

/-- Check if a statement list is a valid input for obligation extraction.
    Valid inputs contain only: `assume`, `assert`, `cover`, `var` declarations,
    and non-deterministic branching (`if *`). -/
def isValidObligationInput : Statements → Bool
  | [] => true
  | s :: rest => isValidObligationStatement s && isValidObligationInput rest
end

mutual
/-- Core recursive worker for `extractFromStatements`. Walks the statement list,
    accumulating path conditions and collecting proof obligations. -/
def extractGo (pc : PathConditions Expression) : Statements →
    Array (ProofObligation Expression) →
    Except String (Array (ProofObligation Expression))
  | [], acc => .ok acc
  | s :: rest, acc =>
    match s with
    | .cmd (.cmd (.assert label e md)) =>
      let propType := match md.getPropertyType with
        | some s => if s == MetaData.divisionByZero then .divisionByZero else .assert
        | none => .assert
      extractGo pc rest (acc.push (ProofObligation.mk label propType pc e md))

    | .cmd (.cmd (.cover label e md)) =>
      extractGo pc rest (acc.push (ProofObligation.mk label .cover pc e md))

    | .cmd (.cmd (.assume label e _md)) =>
      extractGo (pc.addInNewest [.assumption label e]) rest acc

    | .ite .nondet thenSs elseSs _md => do
      let thenObs ← extractFromStatements pc thenSs
      let elseObs ← extractFromStatements pc elseSs
      extractGo pc rest (acc ++ thenObs ++ elseObs)

    | .cmd (.cmd (.init name ty e _md)) =>
      extractGo (pc.addEntry (.varDecl name ty e)) rest acc

    | _other =>
      .error s!"ObligationExtraction: unsupported statement"

/-- Extract proof obligations from a procedure body, reconstructing path
    conditions from the program structure.

    `pathConditions` accumulates the current path conditions (from `assume`
    statements and `var` definitions) as we walk the statement tree.

    Returns the extracted obligations. -/
def extractFromStatements
    (pathConditions : PathConditions Expression)
    (ss : Statements) : Except String (Array (ProofObligation Expression)) :=
  extractGo pathConditions ss #[]
end

/-- Extract proof obligations from a program. Axioms become global assumptions
    that are prepended to the path conditions of every obligation. -/
def extractObligations (p : Program) : Except String (ProofObligations Expression) := do
  -- Accumulate axioms and obligations as we walk declarations in order
  let (_, allObs) ← p.decls.foldlM (init := (([] : PathCondition Expression), (#[] : Array (ProofObligation Expression)))) fun (axiomPc, allObs) decl =>
    match decl with
    | .ax a _ =>
      -- Add axiom to path conditions for subsequent procedures
      .ok (axiomPc ++ [.assumption a.name a.e], allObs)
    | .proc proc _md => do
      let globalPc : PathConditions Expression := [axiomPc]
      let obs ← extractFromStatements globalPc proc.body
      .ok (axiomPc, allObs ++ obs)
    | _ => .ok (axiomPc, allObs)
  return allObs

private theorem extractGo_ok (pc : PathConditions Expression) (ss : Statements)
    (acc : Array (ProofObligation Expression))
    (h : isValidObligationInput ss = true) :
    (extractGo pc ss acc).isOk = true := by
  match ss with
  | [] => unfold extractGo; rfl
  | s :: rest =>
    unfold isValidObligationInput at h
    simp [Bool.and_eq_true] at h
    obtain ⟨hs, hrest⟩ := h
    unfold extractGo; split
    · exact extractGo_ok _ _ _ hrest
    · exact extractGo_ok _ _ _ hrest
    · exact extractGo_ok _ _ _ hrest
    · rename_i thenSs elseSs _
      unfold isValidObligationStatement at hs
      simp [Bool.and_eq_true] at hs
      obtain ⟨hthen, helse⟩ := hs
      simp only [extractFromStatements]
      have h1 := extractGo_ok pc thenSs #[] hthen
      have h2 := extractGo_ok pc elseSs #[] helse
      revert h1 h2
      cases extractGo pc thenSs #[] with
      | error => intro h; simp [Except.isOk, Except.toBool] at h
      | ok v1 =>
        cases extractGo pc elseSs #[] with
        | error => intro _ h; simp [Except.isOk, Except.toBool] at h
        | ok v2 => intro _ _; simp; exact extractGo_ok _ _ _ hrest
    · exact extractGo_ok _ _ _ hrest
    · unfold isValidObligationStatement at hs; simp at hs
  termination_by ss

/-- If the input satisfies `isValidObligationInput`, then `extractFromStatements`
    never returns an error. -/
theorem extractFromStatements_ok (pc : PathConditions Expression) (ss : Statements)
    (h : isValidObligationInput ss = true) :
    (extractFromStatements pc ss).isOk = true := by
  unfold extractFromStatements; exact extractGo_ok pc ss #[] h

end Core.ObligationExtraction

end -- public section
