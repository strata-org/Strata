/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.UnorderedCore
import Strata.Languages.Laurel.TransparencyPass
import Strata.Languages.Laurel.LaurelTypes
import Strata.Util.Tactics

/-!
# Functional Rewrite Pass

Rewrites function bodies to use a purely functional style:
1. Converts imperative assignments (`x := expr`) into functional variable
   declarations (`var x : T := expr`), using the variable's type from the
   semantic model.
2. Lifts if-statements that assign a single variable into if-expressions:
   `if (c) { x := e1; } else { x := e2; }; <rest>`
   becomes `var x := if (c) then e1 else e2; <rest>`
3. Appends a single `Return outputParam` at the end of the body.
   Removes the `Exit "$return"` / `"$return"` label mechanism that is no longer
   needed in the functional form.

This pass operates only on functions (procedures with `isFunctional = true`)
in the `UnorderedCoreWithLaurelTypes` representation. It runs after the
transparency pass which creates those functions.

Functions with early exits (multiple `Exit "$return"` paths) are left
untransformed in this version.

## Follow-up: Multi-variable if-lifting with Tuples

A future pass should add a `StmtExpr.Tuple` constructor to handle cases where
an if-statement assigns multiple variables with sequential dependencies within
a branch. For example:

    if (b) { x := a + 1; y := x + 10; } else { x := a; y := x; }

Would become:

    var x, y := if (b) then { var x := a + 1; Tuple [x, x + 10] }
                       else { Tuple [a, x] };

This requires:
- Adding `StmtExpr.Tuple (elements : List (AstNode StmtExpr))` to LaurelAST
- Updating MapStmtExpr traversals
- Updating the Core translator to destructure tuples into let-bindings
- Handling the case where branch bodies have internal dependencies
-/

namespace Strata.Laurel

public section

/-- Check whether a function body is safe to functionalize.
    Returns `true` if the body consists only of:
    - Variable declarations (Var Declare)
    - Assignments to local variables (Assign [Local _] _)
    - If-then-else statements
    - A single Exit "$return" at the end
    Returns `false` if the body contains early exits, loops, calls in statement
    position, or other constructs that can't be converted to functional style. -/
private partial def isFunctionalizableBody (body : StmtExprMd) : Bool :=
  checkStmts (getTopStmts body)
where
  getTopStmts (e : StmtExprMd) : List StmtExprMd :=
    match e.val with
    | .Block stmts _ => stmts
    | _ => [e]

  checkStmt (s : StmtExprMd) : Bool :=
    match s.val with
    | .Assign [⟨.Local _, _⟩] _ => true
    | .Assign [⟨.Declare _, _⟩] _ => true
    | .Var (.Declare _) => true
    | .Exit "$return" => true
    | .IfThenElse _ thenBranch elseBranch =>
      checkStmts (getTopStmts thenBranch) &&
      match elseBranch with
      | some eb => checkStmts (getTopStmts eb)
      | none => true
    | _ => false

  checkStmts (stmts : List StmtExprMd) : Bool :=
    stmts.all checkStmt

private def rewriteAssignToFunctional (model : SemanticModel) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Assign [target] value =>
      match target.val with
      | .Local varName =>
        let varType := (model.get varName).getType
        ⟨.Assign [⟨.Declare ⟨varName, varType⟩, target.source⟩] value, e.source⟩
      | _ => e
    | _ => e) expr

/-- Collect the names of variables assigned (via `Assign [Local name] _`) in the
    top level of a block or single statement. Does not recurse into nested
    if-then-else or while bodies. -/
private def collectAssignedVars : StmtExprMd → List Identifier
  | ⟨.Block stmts _, _⟩ => stmts.flatMap collectSingleAssigned
  | stmt => collectSingleAssigned stmt
where
  collectSingleAssigned (stmt : StmtExprMd) : List Identifier :=
    match stmt.val with
    | .Assign [⟨.Local name, _⟩] _ => [name]
    | _ => []

/-- Extract the RHS of a single assignment `x := expr` if the statement assigns
    exactly to `varName`. -/
private def extractAssignValue (varName : Identifier) : StmtExprMd → Option StmtExprMd
  | ⟨.Assign [⟨.Local name, _⟩] value, _⟩ =>
    if name == varName then some value else none
  | _ => none

/-- Try to lift an if-statement that assigns a single variable in both branches
    into a functional if-expression assignment. Returns `none` if the pattern
    doesn't match. -/
private def liftIfToExpr (model : SemanticModel) (stmt : StmtExprMd)
    : Option StmtExprMd :=
  match stmt.val with
  | .IfThenElse cond thenBranch elseBranch =>
    let thenVars := collectAssignedVars thenBranch
    let elseVars := match elseBranch with
      | some eb => collectAssignedVars eb
      | none => []
    match thenVars with
    | [varName] =>
      let thenValue := match extractAssignValue varName thenBranch with
        | some v => v
        | none =>
          -- Could be inside a block
          match thenBranch.val with
          | .Block stmts _ =>
            stmts.findSome? (extractAssignValue varName) |>.getD thenBranch
          | _ => thenBranch
      let elseValue := match elseBranch with
        | some eb =>
          match extractAssignValue varName eb with
          | some v => v
          | none =>
            match eb.val with
            | .Block stmts _ =>
              stmts.findSome? (extractAssignValue varName) |>.getD
                ⟨.Var (.Local varName), stmt.source⟩
            | _ => ⟨.Var (.Local varName), stmt.source⟩
        | none => ⟨.Var (.Local varName), stmt.source⟩
      -- Only lift if both branches assign exactly the same single variable
      if elseBranch.isSome && elseVars != [varName] then none
      else if elseBranch.isNone || elseVars == [varName] || elseVars.isEmpty then
        let varType := (model.get varName).getType
        let ifExpr : StmtExprMd := ⟨.IfThenElse cond thenValue (some elseValue), stmt.source⟩
        some ⟨.Assign [⟨.Declare ⟨varName, varType⟩, stmt.source⟩] ifExpr, stmt.source⟩
      else none
    | _ => none
  | _ => none

/-- Rewrite a block's statements by lifting if-statements to if-expressions
    where possible. -/
private def liftIfsInBlock (model : SemanticModel) (stmts : List StmtExprMd) : List StmtExprMd :=
  stmts.map fun stmt =>
    match liftIfToExpr model stmt with
    | some lifted => lifted
    | none => stmt

/-- Remove `Exit "$return"` statements and strip the `"$return"` block label.
    Append `Return (Var (Local outputName))` at the end. -/
private def addReturnAndStripExits (outputName : Identifier) (source : Option FileRange)
    (body : StmtExprMd) : StmtExprMd :=
  let retStmt : StmtExprMd := ⟨.Return (some ⟨.Var (.Local outputName), source⟩), source⟩
  -- Strip the $return block wrapper and remove Exit "$return" statements
  let stmts := match body.val with
    | .Block stmts (some "$return") => stmts
    | .Block stmts none => stmts
    | _ => [body]
  let filtered := stmts.filter fun s =>
    match s.val with
    | .Exit "$return" => false
    | _ => true
  ⟨.Block (filtered ++ [retStmt]) none, body.source⟩

private def rewriteFunctionBody (model : SemanticModel) (proc : Procedure) : Procedure :=
  match proc.outputs with
  | [output] =>
    match proc.body with
    | .Transparent body =>
      if !isFunctionalizableBody body then proc
      else
        let body' := rewriteAssignToFunctional model body
        let stmts := match body'.val with
          | .Block stmts _ => liftIfsInBlock model stmts
          | _ => [body']
        let body'' : StmtExprMd := ⟨.Block stmts none, body'.source⟩
        let result := addReturnAndStripExits output.name proc.name.source body''
        { proc with body := .Transparent result }
    | _ => proc
  | _ => proc

def functionalRewrite (uc : UnorderedCoreWithLaurelTypes) (model : SemanticModel)
    : UnorderedCoreWithLaurelTypes :=
  { uc with
    functions := uc.functions.map fun proc =>
      if proc.isFunctional then rewriteFunctionBody model proc else proc
  }

public def functionalRewritePass : LaurelPass UnorderedCoreWithLaurelTypes UnorderedCoreWithLaurelTypes where
  name := "FunctionalRewritePass"
  documentation := "Rewrites function bodies to purely functional style: imperative assignments become functional declarations, if-statements assigning a single variable are lifted to if-expressions, and an explicit return of the output parameter is appended."
  comesAfter := [⟨transparencyPass.meta, "Functions are created by the transparency pass"⟩]
  run := fun _ uc model => (functionalRewrite uc model, [], {})

end -- public section

end Strata.Laurel
