/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.EvalContext
import all Strata.DL.Imperative.EvalContext
public import Strata.Languages.Core.Program
/-! # Proof Obligation Extraction

A Core-to-obligations pass that walks a post-PE program and extracts
proof obligations with their path conditions reconstructed from the program
structure.

The input is a body satisfying `Statements.hasObligationForm`, the pipeline fact
`ProgramFact.hasObligationForm`: only `assume` (path conditions), `assert` and
`cover` (proof obligations), and `init` (from CSE or global initialization),
nested under `if *` to any depth.

This pass reconstructs path conditions by tracking `assume` statements
encountered on the path to each `assert`/`cover`.
-/

public section

namespace Core.ObligationExtraction

open Lambda Imperative

mutual
/-- Core recursive worker for `extractFromStatements`. Walks the statement list,
    accumulating path conditions in a `RevPathConditions` (newest scope stored
    most-recent-first for O(1) growth) and collecting proof obligations. Each
    captured obligation restores natural order via `RevPathConditions.consume`. -/
def extractGo (pc : RevPathConditions Expression) : Statements →
    Array (ProofObligation Expression) →
    Except String (Array (ProofObligation Expression))
  | [], acc => .ok acc
  | s :: rest, acc =>
    match s with
    | .cmd (.cmd (.assert label e md)) =>
      let propType := convertMetaDataPropertyType md
      extractGo pc rest (acc.push (ProofObligation.mk label propType pc.consume e md))

    | .cmd (.cmd (.cover label e md)) =>
      extractGo pc rest (acc.push (ProofObligation.mk label .cover pc.consume e md))

    | .cmd (.cmd (.assume label e _md)) =>
      extractGo (pc.prepend (.assumption label e)) rest acc

    | .ite .nondet thenSs elseSs _md => do
      let thenObs ← extractFromStatements pc thenSs
      let elseObs ← extractFromStatements pc elseSs
      extractGo pc rest (acc ++ thenObs ++ elseObs)

    | .cmd (.cmd (.init name ty e _md)) =>
      extractGo (pc.prepend (.varDecl name ty e)) rest acc

    | _other =>
      .error s!"ObligationExtraction: unsupported statement"

/-- Extract proof obligations from a procedure body, reconstructing path
    conditions from the program structure.

    `pathConditions` accumulates the current path conditions (from `assume`
    statements and `var` definitions) as we walk the statement tree.

    Returns the extracted obligations. -/
def extractFromStatements
    (pathConditions : RevPathConditions Expression)
    (ss : Statements) : Except String (Array (ProofObligation Expression)) :=
  extractGo pathConditions ss #[]
end

/-- Extract proof obligations from a program. Axioms become global assumptions
    and `distinct` declarations become distinctness facts. -/
def extractObligations (p : Program) : Except String (ProofObligations Expression) := do
  -- Accumulate global path-condition facts (axioms and distinct groups) and
  -- obligations as we walk declarations in order.
  let (_, allObs) ← p.decls.foldlM (init := (([] : PathCondition Expression), (#[] : Array (ProofObligation Expression)))) fun (globalPc, allObs) decl =>
    match decl with
    | .ax a _ =>
      .ok (.assumption a.name a.e :: globalPc, allObs)
    | .distinct name es _ =>
      .ok (.distinct (toString name) es :: globalPc, allObs)
    | .func func _ =>
      -- A surviving function precondition is an obligation nobody generates,
      -- and the encoder emits total `SafeDiv`, `SafeMod` and safe bitvector
      -- operations on the strength of those preconditions having been checked.
      if func.preconditions.isEmpty then .ok (globalPc, allObs)
      else
        .error ("ObligationExtraction: function '" ++ toString func.name ++
          "' still carries a precondition; run precondition elimination before " ++
          "extracting obligations")
    | .recFuncBlock funcs _ =>
      match funcs.find? (fun f => !f.preconditions.isEmpty) with
      | some f =>
        .error ("ObligationExtraction: function '" ++ toString f.name ++
          "' still carries a precondition; run precondition elimination before " ++
          "extracting obligations")
      | none => .ok (globalPc, allObs)
    | .proc proc _md => do
      let obs ← match proc.body with
        | .structured ss =>
          -- `globalPC` is accumulated newest-first (via ::) which
          -- is what RevPathConditions expects.
          extractFromStatements ⟨[globalPc]⟩ ss
        -- A CFG body cannot be walked here. Returning no obligations would
        -- report success on a procedure whose assertions were never checked,
        -- so it is an error: the back end requires structured bodies.
        | .cfg _ =>
          .error ("ObligationExtraction: procedure '" ++ toString proc.header.name ++
            "' has a CFG body; obligations can only be extracted from " ++
            "structured bodies")
      .ok (globalPc, allObs ++ obs)
    | _ => .ok (globalPc, allObs)
  return allObs

@[simp] theorem extractFromStatements_eq (pc : RevPathConditions Expression) (ss : Statements) :
    extractFromStatements pc ss = extractGo pc ss #[] := by
  unfold extractFromStatements; rfl

/-- `extractGo` succeeds on any body satisfying `hasObligationForm`, for any path
    conditions and accumulator. -/
private theorem extractGo_ok (pc : RevPathConditions Expression) (ss : Statements)
    (acc : Array (ProofObligation Expression))
    (h : Statements.hasObligationForm ss = true) :
    (extractGo pc ss acc).isOk = true := by
  match ss with
  | [] => unfold extractGo; rfl
  | s :: rest =>
    -- Split into: `s` itself, the statements nested in `s`, and `rest`.
    unfold Statements.hasObligationForm Imperative.Block.allSubstmts
      Imperative.Stmt.allSubstmts at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hs, hsub⟩, hrest⟩ := h
    unfold extractGo; split
    · exact extractGo_ok _ _ _ hrest
    · exact extractGo_ok _ _ _ hrest
    · exact extractGo_ok _ _ _ hrest
    · rename_i thenSs elseSs _
      simp only [Bool.and_eq_true] at hsub
      obtain ⟨hthen, helse⟩ := hsub
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
    · -- `isObligationForm` rejects every statement that reaches this case.
      unfold Statement.isObligationForm at hs; simp at hs

/-- `extractFromStatements` succeeds on any body satisfying `hasObligationForm`. -/
theorem extractFromStatements_ok (pc : RevPathConditions Expression) (ss : Statements)
    (h : Statements.hasObligationForm ss = true) :
    (extractFromStatements pc ss).isOk = true := by
  unfold extractFromStatements; exact extractGo_ok pc ss #[] h

end Core.ObligationExtraction

end -- public section
