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
    non-deterministic or deterministic branching (`if *` / `if cond`),
    labelled blocks (from loop elimination), and `exit` statements. -/
private def isValidInput : Statements → Bool
  | [] => true
  | s :: rest => isValidStatement s && isValidInput rest
where
  isValidStatement : Statement → Bool
    | .cmd (.cmd (.assert _ _ _)) => true
    | .cmd (.cmd (.assume _ _ _)) => true
    | .cmd (.cmd (.cover _ _ _)) => true
    | .cmd (.cmd (.init _ _ _ _)) => true
    | .ite _ thenSs elseSs _ => isValidInput thenSs && isValidInput elseSs
    | .block _ innerSs _ => isValidInput innerSs
    | .exit _ _ => true
    | _ => false

/-- Collect assert and cover obligations from a dead (unreachable) branch.
    Asserts get obligation `true` (trivially pass), covers get `false` (unreachable).
    A dead-branch path condition is added so the solver can detect unreachability. -/
private partial def extractDeadBranchObligations
    (pc : PathConditions Expression) (cond : Expression.Expr)
    (ss : Statements) : Except String (Array (ProofObligation Expression)) :=
  let deadLabel := toString (Std.format f!"<dead_branch: {cond.eraseTypes}>")
  let deadPc := pc.push [(deadLabel, Lambda.LExpr.false ())]
  go deadPc ss #[]
where
  go (pc : PathConditions Expression) : Statements →
      Array (ProofObligation Expression) →
      Except String (Array (ProofObligation Expression))
  | [], acc => .ok acc
  | s :: rest, acc =>
    match s with
    | .cmd (.cmd (.assert label _e md)) =>
      let propType := match md.getPropertyType with
        | some s => if s == MetaData.divisionByZero then .divisionByZero else .assert
        | none => .assert
      go pc rest (acc.push (ProofObligation.mk label propType pc (Lambda.LExpr.true ()) md))
    | .cmd (.cmd (.cover label _e md)) =>
      go pc rest (acc.push (ProofObligation.mk label .cover pc (Lambda.LExpr.false ()) md))
    | .block _ innerSs _ => do
      let innerObs ← extractDeadBranchObligations pc cond innerSs
      go pc rest (acc ++ innerObs)
    | .ite _ thenSs elseSs _ => do
      let thenObs ← extractDeadBranchObligations pc cond thenSs
      let elseObs ← extractDeadBranchObligations pc cond elseSs
      go pc rest (acc ++ thenObs ++ elseObs)
    | _ => go pc rest acc

/-- Guard an assumption with a branch condition: `if cond then e else true`.
    This makes the assumption conditional so that contradictory branch
    assumptions don't make the path conditions unsatisfiable. -/
private def guardAssumption (cond : Expression.Expr) (e : Expression.Expr) : Expression.Expr :=
  Lambda.LExpr.ite () cond e (Lambda.LExpr.true ())

/-- Extract the first `assume` expression from a statement list (top-level only).
    Used to identify the branch condition in post-PE nondet ITE branches. -/
private def firstAssumeCond (ss : Statements) : Option Expression.Expr :=
  ss.findSome? fun
    | .cmd (.cmd (.assume _ e _)) => some e
    | _ => none

/-- Guard a list of new assumptions with a branch condition. If no condition
    is available, assumptions are kept as-is. -/
private def guardNewAssumptions (cond? : Option Expression.Expr)
    (newPcs : List (String × Expression.Expr)) : List (String × Expression.Expr) :=
  match cond? with
  | some cond => newPcs.map fun (l, e) => (l, guardAssumption cond e)
  | none => newPcs

/-- At a loop_N block boundary, strip unguarded loop-elim assumptions and
    rename guarded ones so they don't trigger the loopElimPipelinePhase
    demotion. Guarded versions carry loop invariant information needed by
    post-loop obligations; renaming preserves the information while
    preventing spurious demotion. -/
private def stripLoopElimForLoop (pc : PathConditions Expression) (loopNum : String) : PathConditions Expression :=
  let guardPrefix := s!"assume_guard_{loopNum}"
  let invPrefix := s!"assume_invariant_{loopNum}_"
  pc.map (·.filterMap (fun (l, e) =>
    let isThisLoop := l.startsWith guardPrefix || l.startsWith invPrefix
    if !isThisLoop then some (l, e)
    else match e with
      | .ite _ _ _ _ => some (s!"post_loop_{l}", e)  -- rename to avoid demotion
      | _ => none))

/-- Check if a block label is a loop-elim top-level block (loop_N). -/
private def isLoopElimBlock (label : String) : Bool :=
  label.startsWith "loop_" && label.length > 5 &&
    (label.toList.drop 5).all (·.isDigit)

/-- Merge path conditions from two nondet ITE branches for post-ITE statements.
    Each branch's new assumptions (those not in the pre-ITE path conditions) are
    guarded by the branch condition extracted from the first `assume` statement
    in each branch. This prevents contradictory branch assumptions from making
    the path conditions unsatisfiable while preserving information needed by
    post-ITE statements (e.g., loop invariants).
    Loop-elim-internal assumptions are excluded from the merge because they are
    scoped to the loop body and should not leak to post-loop obligations. -/
private def mergeNondetBranchPcs (preItePc : PathConditions Expression)
    (thenSs elseSs : Statements)
    (thenPc elsePc : PathConditions Expression) : PathConditions Expression :=
  let preLabels := preItePc.flatten.map (·.1) |>.toArray
  let isNew := fun (label : String) => !preLabels.contains label
  let thenNew := thenPc.flatten.filter (fun (l, _) => isNew l)
  let elseNew := elsePc.flatten.filter (fun (l, _) => isNew l)
  let thenGuarded := guardNewAssumptions (firstAssumeCond thenSs) thenNew
  let elseGuarded := guardNewAssumptions (firstAssumeCond elseSs) elseNew
  preItePc.push (thenGuarded ++ elseGuarded)

/-- Result of extracting obligations from a statement sequence.
    `exitLabel` is `some l` when the path ended with `exit l` (or `some none`
    for an unlabelled exit), meaning subsequent statements are unreachable. -/
private structure ExtractionResult where
  obligations : Array (ProofObligation Expression)
  pathConditions : PathConditions Expression
  exitLabel : Option (Option String) := .none

/-- Extract proof obligations from a procedure body, reconstructing path
    conditions from the program structure.

    `pathConditions` accumulates the current path conditions (from `assume`
    statements and ITE branch conditions) as we walk the statement tree.

    Returns obligations, final path conditions, and an optional exit label
    indicating whether the path terminated via an `exit` statement. -/
private partial def extractFromStatements
    (pathConditions : PathConditions Expression)
    (ss : Statements) : Except String ExtractionResult :=
  go pathConditions ss #[]
where
  go (pc : PathConditions Expression) : Statements →
      Array (ProofObligation Expression) →
      Except String ExtractionResult
  | [], acc => .ok { obligations := acc, pathConditions := pc }
  | s :: rest, acc =>
    match s with
    | .ite .nondet thenSs elseSs _md => do
        let thenRes ← extractFromStatements pc thenSs
        let elseRes ← extractFromStatements pc elseSs
        -- Merge path conditions: guard each branch's new assumptions with its
        -- branch condition so contradictory assumptions don't make the path
        -- conditions unsatisfiable, while preserving information for post-ITE
        -- statements (e.g., loop invariants).
        -- Exit labels from branches are intentionally ignored: in a nondet ITE,
        -- both paths are explored independently, so an exit in one branch does
        -- not affect reachability of statements after the ITE.
        let mergedPc := mergeNondetBranchPcs pc thenSs elseSs
          thenRes.pathConditions elseRes.pathConditions
        go mergedPc rest (acc ++ thenRes.obligations ++ elseRes.obligations)
    | _ => do
      let res ← extractFromStatement pc s acc
      -- If the statement caused an exit, stop processing remaining statements
      if res.exitLabel.isSome then
        return res
      go res.pathConditions rest res.obligations

  extractFromStatement (pc : PathConditions Expression) (s : Statement)
      (acc : Array (ProofObligation Expression)) :
      Except String ExtractionResult :=
    match s with
    | .cmd (.cmd (.assert label e md)) =>
      let propType := match md.getPropertyType with
        | some s => if s == MetaData.divisionByZero then .divisionByZero else .assert
        | none => .assert
      .ok { obligations := acc.push (ProofObligation.mk label propType pc e md), pathConditions := pc }

    | .cmd (.cmd (.cover label e md)) =>
      .ok { obligations := acc.push (ProofObligation.mk label .cover pc e md), pathConditions := pc }

    | .cmd (.cmd (.assume label e _md)) =>
      .ok { obligations := acc, pathConditions := pc.addInNewest [(label, e)] }

    | .ite .nondet thenSs elseSs _md => do
      let thenRes ← extractFromStatements pc thenSs
      let elseRes ← extractFromStatements pc elseSs
      .ok { obligations := acc ++ thenRes.obligations ++ elseRes.obligations, pathConditions := pc }

    | .ite (.det c) thenSs elseSs _md => do
      let condBool := Lambda.LExpr.denoteBool c
      if condBool.isSome then
        let isTrue := condBool == some true
        let (liveSs, deadSs) := if isTrue then (thenSs, elseSs) else (elseSs, thenSs)
        let liveRes ← extractFromStatements pc liveSs
        let deadObs ← extractDeadBranchObligations pc c deadSs
        -- Propagate exit from the live branch
        .ok { obligations := acc ++ liveRes.obligations ++ deadObs,
              pathConditions := liveRes.pathConditions,
              exitLabel := liveRes.exitLabel }
      else do
        let thenRes ← extractFromStatements pc thenSs
        let elseRes ← extractFromStatements pc elseSs
        .ok { obligations := acc ++ thenRes.obligations ++ elseRes.obligations, pathConditions := pc }

    | .block label innerSs _md => do
      let innerRes ← extractFromStatements pc innerSs
      let consumed := match innerRes.exitLabel with
        | .some .none => true
        | .some (.some l) => l == label
        | .none => true
      -- Strip unguarded loop-elim assumptions for this specific loop
      -- at the loop_N block boundary, preserving outer loop assumptions.
      let outPc := if isLoopElimBlock label
        then stripLoopElimForLoop innerRes.pathConditions (label.drop 5).toString
        else innerRes.pathConditions
      .ok ⟨acc ++ innerRes.obligations, outPc,
           if consumed then .none else innerRes.exitLabel⟩

    | .cmd (.cmd (.init name ty (.det e) _md)) =>
      -- Variable definitions become equalities in the path conditions,
      -- so the SMT solver knows the variable's value.
      let varTy := if h : ty.isMonoType then some (ty.toMonoType h) else none
      let varExpr : Expression.Expr := .fvar () name varTy
      .ok { obligations := acc, pathConditions := pc.insert name.toPretty (.eq () varExpr e) }

    | .cmd (.cmd (.init _ _ _ _)) => .ok { obligations := acc, pathConditions := pc }
    | .cmd (.cmd (.set _ _ _)) => .ok { obligations := acc, pathConditions := pc }
    | .cmd (.call _ _ _) => .ok { obligations := acc, pathConditions := pc }
    | .funcDecl _ _ => .ok { obligations := acc, pathConditions := pc }
    | .typeDecl _ _ => .ok { obligations := acc, pathConditions := pc }
    | .exit l _ => .ok { obligations := acc, pathConditions := pc, exitLabel := .some l }
    | .loop _ _ _ _ _ => .ok { obligations := acc, pathConditions := pc }

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
      let res ← extractFromStatements globalPc proc.body
      .ok (axiomPc, allObs ++ res.obligations)
    | _ => .ok (axiomPc, allObs)
  return allObs

end Core.ObligationExtraction

end -- public section
