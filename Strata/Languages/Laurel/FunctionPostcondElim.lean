/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.LaurelTypes
import Strata.Util.Tactics

/-!
# Function Postcondition Elimination

A Laurel-to-Laurel pass that eliminates function postconditions by:
1. Collecting postconditions from functions
2. Generating a postcondition function per function (`f$post`)
3. Generating a check procedure per function with a body (`f$check`)
4. Lifting calls to functions with postconditions out of nested expression positions
5. Inserting `assume f$post(args, result)` at call sites
6. Keeping function bodies `Transparent`

This pass runs after `ConstrainedTypeElim`, which converts constrained return types
into postconditions on `Transparent` bodies. Explicit `ensures` clauses on functions
are also carried as `Transparent` postconditions (or `Opaque` for `opaque function`).
-/

namespace Strata.Laurel

open Strata

/-- Set of function names that have postconditions -/
abbrev FuncPostSet := Std.HashSet String


/-- Collected postconditions for a function -/
structure FuncPostconds where
  /-- The function procedure -/
  proc : Procedure
  /-- All postconditions (ensures clauses, including those derived from constrained return types) -/
  postconditions : List StmtExprMd
  /-- The output parameter (result) -/
  resultParam : Parameter
  /-- Whether the function has a body (used to decide if a check procedure is needed) -/
  hasBody : Bool
  /-- Whether the function is opaque (body hidden from callers) -/
  isOpaque : Bool

/-- Collect postconditions from a functional procedure.
    Returns `none` if the procedure has no postconditions or no output parameter. -/
def collectFuncPostconds (proc : Procedure) : Option FuncPostconds :=
  if !proc.isFunctional then none
  else
    let (posts, hasBody, isOpaque) := match proc.body with
      | .Transparent _ posts => (posts, true, false)
      | .Opaque posts (some _) _ => (posts, true, true)
      | .Opaque posts none _ => (posts, false, true)
      | _ => ([], false, false)
    match proc.outputs.head?, posts.isEmpty with
    | some resultParam, false => some { proc, postconditions := posts, resultParam, hasBody, isOpaque }
    | _, _ => none

/-- Generate a postcondition function for a function.
    Takes all inputs + result as parameters, returns the conjunction of postconditions. -/
def mkPostcondFunc (fpc : FuncPostconds) : Procedure :=
  let md := fpc.proc.md
  let bodyExpr := match fpc.postconditions with
    | [] => ⟨.LiteralBool true, md⟩  -- shouldn't happen
    | [single] => single
    | first :: rest => rest.foldl (fun acc p => ⟨.PrimitiveOp .And [acc, p], md⟩) first
  { name := mkId s!"{fpc.proc.name.text}$post"
    inputs := fpc.proc.inputs ++ [fpc.resultParam]
    outputs := [{ name := mkId "$post_result", type := ⟨.TBool, #[]⟩ }]
    body := .Transparent ⟨.Block [bodyExpr] none, md⟩ []
    isFunctional := true
    determinism := .deterministic none
    decreases := none
    preconditions := []
    md := md }

/-- Generate a check procedure that calls the function and asserts the postcondition.
    Returns `none` for functions without a body. -/
def mkCheckProc (fpc : FuncPostconds) : Option Procedure :=
  if !fpc.hasBody then none
  else
    let md := fpc.proc.md
    let resultId := mkId "$result"
    let resultType := fpc.resultParam.type
    let callArgs := fpc.proc.inputs.map fun p => ⟨StmtExpr.Identifier p.name, md⟩
    let initExpr := if fpc.isOpaque then
      -- Opaque: inline the body directly (callers can't see it)
      match fpc.proc.body with
      | .Opaque _ (some impl) _ => impl
      | .Transparent impl _ => impl
      | _ => ⟨.LiteralBool false, md⟩  -- unreachable: hasBody is true
    else
      -- Transparent: call the function
      ⟨.StaticCall fpc.proc.name callArgs, md⟩
    let initResult : StmtExprMd := ⟨.LocalVariable resultId resultType (some initExpr), md⟩
    let postCallArgs := callArgs ++ [⟨.Identifier resultId, md⟩]
    let postCall : StmtExprMd := ⟨.StaticCall (mkId s!"{fpc.proc.name.text}$post") postCallArgs, md⟩
    let assertPost : StmtExprMd := ⟨.Assert postCall, md⟩
    some {
      name := mkId s!"{fpc.proc.name.text}$check"
      inputs := fpc.proc.inputs
      outputs := []
      preconditions := fpc.proc.preconditions
      body := .Transparent ⟨.Block [initResult, assertPost] none, md⟩ []
      isFunctional := false
      determinism := .deterministic none
      decreases := none
      md := md }

/-- Strip postconditions from a function after they've been collected. -/
def stripFuncPostconds (proc : Procedure) : Procedure :=
  if !proc.isFunctional then proc
  else match proc.body with
    | .Transparent body (_ :: _) => { proc with body := .Transparent body [] }
    | _ => proc

/-- State for the lifting sub-pass -/
abbrev LiftM := StateM Nat

private def freshLiftVar : LiftM Identifier := do
  let n := ← get
  modify (· + 1)
  return mkId s!"$pc_{n}"

mutual
/-- Lift a nested expression: if it's a call to a function with postconditions,
    extract it to a fresh variable. -/
partial def liftNestedPostcondCall (funcPostSet : FuncPostSet) (expr : StmtExprMd)
    (model : SemanticModel) : LiftM (List StmtExprMd × StmtExprMd) := do
  let (innerStmts, expr') ← liftPostcondCalls funcPostSet expr model
  match expr'.val with
  | StmtExpr.StaticCall callee _ =>
    if funcPostSet.contains callee.text then
      let tmpVar ← freshLiftVar
      let ty := computeExprType model expr'
      let initStmt : StmtExprMd := ⟨.LocalVariable tmpVar ty (some expr'), expr'.md⟩
      return (innerStmts ++ [initStmt], ⟨.Identifier tmpVar, expr'.md⟩)
    else
      return (innerStmts, expr')
  | _ => return (innerStmts, expr')

/-- Lift calls to functions with postconditions out of nested expression positions.
    Returns (lifted statements to prepend, transformed expression). -/
partial def liftPostcondCalls (funcPostSet : FuncPostSet) (expr : StmtExprMd)
    (model : SemanticModel) : LiftM (List StmtExprMd × StmtExprMd) := do
  let md := expr.md
  match expr.val with
  | .StaticCall callee args =>
    -- First lift inside arguments
    let mut liftedStmts : List StmtExprMd := []
    let mut newArgs : List StmtExprMd := []
    for arg in args do
      let (stmts, arg') ← liftNestedPostcondCall funcPostSet arg model
      liftedStmts := liftedStmts ++ stmts
      newArgs := newArgs ++ [arg']
    let newCall : StmtExprMd := ⟨.StaticCall callee newArgs, md⟩
    return (liftedStmts, newCall)
  | .PrimitiveOp op args =>
    let mut liftedStmts : List StmtExprMd := []
    let mut newArgs : List StmtExprMd := []
    for arg in args do
      let (stmts, arg') ← liftNestedPostcondCall funcPostSet arg model
      liftedStmts := liftedStmts ++ stmts
      newArgs := newArgs ++ [arg']
    return (liftedStmts, ⟨.PrimitiveOp op newArgs, md⟩)
  | .IfThenElse c t el =>
    let (cStmts, c') ← liftNestedPostcondCall funcPostSet c model
    let (tStmts, t') ← liftNestedPostcondCall funcPostSet t model
    match el with
    | some e =>
      let (elStmts, e') ← liftNestedPostcondCall funcPostSet e model
      return (cStmts ++ tStmts ++ elStmts, ⟨.IfThenElse c' t' (some e'), md⟩)
    | none =>
      return (cStmts ++ tStmts, ⟨.IfThenElse c' t' none, md⟩)
  | .Forall param trigger body =>
    let (bodyStmts, body') ← liftNestedPostcondCall funcPostSet body model
    return (bodyStmts, ⟨.Forall param trigger body', md⟩)
  | .Exists param trigger body =>
    let (bodyStmts, body') ← liftNestedPostcondCall funcPostSet body model
    return (bodyStmts, ⟨.Exists param trigger body', md⟩)
  | _ => return ([], expr)
end

/-- Lift postcond calls from an expression and generate lifted stmts + assumes.
    Returns (prepend statements, transformed expression). -/
private def liftExprWithAssumes (funcPostSet : FuncPostSet) (model : SemanticModel)
    (expr : StmtExprMd) : LiftM (List StmtExprMd × StmtExprMd) := do
  let (liftedStmts, expr') ← liftPostcondCalls funcPostSet expr model
  let liftedAssumes := liftedStmts.filterMap fun s => match s.val with
    | .LocalVariable liftedName _ (some ⟨.StaticCall callee args, callMd⟩) =>
      if funcPostSet.contains callee.text then
        let postFuncName := s!"{callee.text}$post"
        let postArgs := args ++ [⟨.Identifier liftedName, callMd⟩]
        some ⟨.Assume ⟨.StaticCall (mkId postFuncName) postArgs, callMd⟩, callMd⟩
      else none
    | _ => none
  return (liftedStmts ++ liftedAssumes, expr')

/-- Generate an assume for a top-level function call if it has postconditions.
    `resultVar` is the variable the result is assigned to. -/
private def mkTopAssume (funcPostSet : FuncPostSet) (expr : StmtExprMd) (resultVar : Identifier)
    (md : Imperative.MetaData Core.Expression) : List StmtExprMd :=
  match expr.val with
  | .StaticCall callee args =>
    if funcPostSet.contains callee.text then
      let postFuncName := s!"{callee.text}$post"
      let postArgs := args ++ [⟨.Identifier resultVar, md⟩]
      [⟨.Assume ⟨.StaticCall (mkId postFuncName) postArgs, md⟩, md⟩]
    else []
  | _ => []

/-- Lift postcondition calls in a statement's expressions and insert assumes.
    Returns the transformed list of statements. -/
partial def liftAndAssumeInStmt (funcPostSet : FuncPostSet) (model : SemanticModel)
    (stmt : StmtExprMd) : LiftM (List StmtExprMd) := do
  let md := stmt.md
  match stmt.val with
  | .LocalVariable name ty (some init) =>
    let (prepend, init') ← liftExprWithAssumes funcPostSet model init
    let initStmt : StmtExprMd := ⟨.LocalVariable name ty (some init'), md⟩
    return prepend ++ [initStmt] ++ mkTopAssume funcPostSet init' name md

  | .Assign [⟨.Identifier name, _⟩] value =>
    let (prepend, value') ← liftExprWithAssumes funcPostSet model value
    let assignStmt : StmtExprMd := ⟨.Assign [⟨.Identifier name, md⟩] value', md⟩
    return prepend ++ [assignStmt] ++ mkTopAssume funcPostSet value' name md

  | .Assert cond =>
    let (prepend, cond') ← liftExprWithAssumes funcPostSet model cond
    return prepend ++ [⟨.Assert cond', md⟩]

  | .Assume cond =>
    let (prepend, cond') ← liftExprWithAssumes funcPostSet model cond
    return prepend ++ [⟨.Assume cond', md⟩]

  | .Return (some value) =>
    let (prepend, value') ← liftExprWithAssumes funcPostSet model value
    return prepend ++ [⟨.Return (some value'), md⟩]

  | .Block stmts sep =>
    let stmts' ← stmts.flatMapM (liftAndAssumeInStmt funcPostSet model)
    return [⟨.Block stmts' sep, md⟩]

  | .IfThenElse cond thenBr elseBr =>
    let (condPrepend, cond') ← liftExprWithAssumes funcPostSet model cond
    let thenStmts ← liftAndAssumeInStmt funcPostSet model thenBr
    let thenBr' := match thenStmts with | [s] => s | ss => ⟨.Block ss none, md⟩
    match elseBr with
    | some eb =>
      let elseStmts ← liftAndAssumeInStmt funcPostSet model eb
      let elseBr' := match elseStmts with | [s] => s | ss => ⟨.Block ss none, md⟩
      return condPrepend ++ [⟨.IfThenElse cond' thenBr' (some elseBr'), md⟩]
    | none =>
      return condPrepend ++ [⟨.IfThenElse cond' thenBr' none, md⟩]

  | .While cond inv dec body =>
    let (condPrepend, cond') ← liftExprWithAssumes funcPostSet model cond
    let mut newInv : List StmtExprMd := []
    let mut invPrepend : List StmtExprMd := []
    for i in inv do
      let (prep, i') ← liftExprWithAssumes funcPostSet model i
      invPrepend := invPrepend ++ prep
      newInv := newInv ++ [i']
    let bodyStmts ← liftAndAssumeInStmt funcPostSet model body
    let body' := match bodyStmts with | [s] => s | ss => ⟨.Block ss none, md⟩
    return condPrepend ++ invPrepend ++ [⟨.While cond' newInv dec body', md⟩]

  | _ => return [stmt]

/-- Apply lifting and assume insertion to a procedure body -/
def liftAndAssumeInProc (funcPostSet : FuncPostSet) (model : SemanticModel)
    (proc : Procedure) : Procedure :=
  if funcPostSet.isEmpty then proc
  else match proc.body with
    | .Transparent bodyExpr posts =>
      let (stmts, _) := (liftAndAssumeInStmt funcPostSet model bodyExpr).run 0
      let body := match stmts with | [s] => s | ss => ⟨.Block ss none, bodyExpr.md⟩
      { proc with body := .Transparent body posts }
    | .Opaque posts (some impl) mods =>
      let (stmts, _) := (liftAndAssumeInStmt funcPostSet model impl).run 0
      let impl' := match stmts with | [s] => s | ss => ⟨.Block ss none, impl.md⟩
      { proc with body := .Opaque posts (some impl') mods }
    | _ => proc

/-- Main entry point: eliminate function postconditions from a Laurel program -/
public def functionPostcondElim (model : SemanticModel) (program : Program) : Program × List DiagnosticModel :=
  -- Step 1: Collect postconditions from all functional procedures
  let funcPostconds := program.staticProcedures.filterMap collectFuncPostconds
  if funcPostconds.isEmpty then (program, []) else

  -- Step 2: Generate postcondition functions
  let postFuncs := funcPostconds.map mkPostcondFunc

  -- Step 3: Generate check procedures (only for functions with bodies)
  let checkProcs := funcPostconds.filterMap mkCheckProc

  -- Step 4: Build set of functions with postconditions
  let funcPostSet : FuncPostSet := funcPostconds.foldl (init := {}) fun s fpc =>
    s.insert fpc.proc.name.text

  -- Step 5: Clear postconditions from functions (already captured in $post functions)
  let procs := program.staticProcedures.map stripFuncPostconds

  -- Step 6: Lift and insert assumes in all procedure bodies
  let procs := procs.map (liftAndAssumeInProc funcPostSet model)

  ({ program with
    staticProcedures := procs ++ postFuncs ++ checkProcs },
   [])

end Strata.Laurel
