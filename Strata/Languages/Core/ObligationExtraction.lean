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
  | .cmd (.cmd (.assert _ _ _)) | .cmd (.cmd (.assume _ _ _))
  | .cmd (.cmd (.cover _ _ _)) | .cmd (.cmd (.init _ _ _ _)) => true
  | .ite .nondet thenSs elseSs _ => isValidObligationInput thenSs && isValidObligationInput elseSs
  | _ => false

/-- Check if a statement list is a valid input for obligation extraction.
    Valid inputs contain only: `assume`, `assert`, `cover`, `var` declarations,
    and non-deterministic branching (`if *`). -/
def isValidObligationInput : Statements → Bool
  | [] => true
  | s :: rest => isValidObligationStatement s && isValidObligationInput rest
end

/-- A path-condition accumulator whose newest scope is stored reversed
    (most-recent-first) so that appending a statement is O(1).

    Orientation is encoded in the type: entries only ever enter through
    `prepend` (which pushes onto the front of the newest scope), and the only
    way to read the accumulator back out is `consume` (which restores natural
    order). -/
structure RevPathConditions where
  /-- Scopes with the newest (head) scope held in most-recent-first order. -/
  scopes : PathConditions Expression

/-- O(1) prepend of a new entry to the newest scope. -/
private def RevPathConditions.prepend (r : RevPathConditions)
    (e : PathConditionEntry Expression) : RevPathConditions :=
  ⟨match r.scopes with
   | [] => [[e]]
   | p :: rest => (e :: p) :: rest⟩

/-- Restore natural (oldest-first) order, producing a
    `PathConditions Expression` suitable for a `ProofObligation`.

    Only the head scope is reversed; the walker `extractGo`
    never `push`es a second scope onto the accumulator (the only `push` in the
    pass is `Array.push` on the obligation result). -/
private def RevPathConditions.consume (r : RevPathConditions) : PathConditions Expression :=
  match r.scopes with
  | [] => []
  | p :: rest => p.reverse :: rest

/-- Prepending an entry to RevPathConditions and then consuming
    is equivalent to adding an entry to PathConditions -/
private theorem RevPathConditions.consume_prepend (r : RevPathConditions)
    (e : PathConditionEntry Expression) :
    (r.prepend e).consume = (r.consume).addEntry e := by
  cases r with | mk scopes => cases scopes <;>
    simp [RevPathConditions.prepend, RevPathConditions.consume,
          PathConditions.addEntry, List.reverse_cons]

mutual
/-- Core recursive worker for `extractFromStatements`. Walks the statement list,
    accumulating path conditions in a `RevPathConditions` (newest scope stored
    most-recent-first for O(1) growth) and collecting proof obligations. Each
    captured obligation restores natural order via `RevPathConditions.consume`. -/
def extractGo (pc : RevPathConditions) : Statements →
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
    (pathConditions : RevPathConditions)
    (ss : Statements) : Except String (Array (ProofObligation Expression)) :=
  extractGo pathConditions ss #[]
end

/-- Extract proof obligations from a program. Axioms become global assumptions
    and `distinct` declarations become distinctness facts; both are prepended,
    in declaration order, to the path conditions of every subsequent
    procedure's obligations. -/
def extractObligations (p : Program) : Except String (ProofObligations Expression) := do
  -- Accumulate global path-condition facts (axioms and distinct groups) and
  -- obligations as we walk declarations in order.
  let (_, allObs) ← p.decls.foldlM (init := (([] : PathCondition Expression), (#[] : Array (ProofObligation Expression)))) fun (globalPc, allObs) decl =>
    match decl with
    | .ax a _ =>
      -- Add axiom to path conditions for subsequent procedures
      .ok (globalPc ++ [.assumption a.name a.e], allObs)
    | .distinct name es _ =>
      -- Add distinctness fact to path conditions for subsequent procedures
      .ok (globalPc ++ [.distinct (toString name) es], allObs)
    | .proc proc _md => do
      let obs ← match proc.body with
        -- Start from one empty scope and prepend the global facts in declaration order;
        | .structured ss =>
          extractFromStatements (globalPc.foldl (·.prepend ·) { scopes := [[]] }) ss
        -- CFG bodies are not supported on procedure-body branch.
        | .cfg _ => .ok #[]
      .ok (globalPc, allObs ++ obs)
    | _ => .ok (globalPc, allObs)
  return allObs

@[simp] theorem extractFromStatements_eq (pc : RevPathConditions) (ss : Statements) :
    extractFromStatements pc ss = extractGo pc ss #[] := by
  unfold extractFromStatements; rfl

private theorem extractGo_ok (pc : RevPathConditions) (ss : Statements)
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

/-- If the input satisfies `isValidObligationInput`, then `extractFromStatements`
    never returns an error. -/
theorem extractFromStatements_ok (pc : RevPathConditions) (ss : Statements)
    (h : isValidObligationInput ss = true) :
    (extractFromStatements pc ss).isOk = true := by
  unfold extractFromStatements; exact extractGo_ok pc ss #[] h

end Core.ObligationExtraction

end -- public section
