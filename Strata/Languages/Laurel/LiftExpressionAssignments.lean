/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Languages.Core.Verifier

namespace Strata
namespace Laurel

/-
Transform assignments that appear in expression contexts into preceding statements.

When we see expressions, we traverse them right to left.
For each variable, we maintain a substitution map, which is initially filled with the actual variable.
If we encounter an assignment, we replace it with the current substitution for that variable. We then come up with a new snapshot variable name, and push that to the subsitution map, we also push both the assignment and an assignment to the snapshot variable to a stack over prependStatements.

When we encounter an if-then-else, we rerun our algorithm from scratch on both branches. If any assignments were discovered in the branches, lift the entire if-then-else by putting it on the prependStatements stack. Introduce a fresh variable and for each branch, assign the last statement in that branch to the fresh variable.

Example 1 — Assignments in expression position:
  var y: int := x + (x := 1;) + x + (x := 2;);

Becomes:
  var $x_1 := x;              -- before snapshot 1
  x := 1;                     -- lifted first assignment
  var $x_0 := x;              -- before snapshot 0
  x := 2;                     -- lifted second assignment
  var y: int := $x_1 + $x_0 + $x_0 + x;

Example 2 — Conditional (if-then-else) inside an expression position:
  var z: bool := (if (b) { b := false; } else (b := true;)) || b;

Becomes:
  var $c_0: bool;
  if (b) {
    var $b_0 := b;
    b := false;
    $c_0 := b;
  } else {
    var $b_0 := b;
    b := true;
    $c_0 := b;
  }
  var z: bool := #c_0 || b;

Example 3 — Statement-level assignment:
  x := expr;

Becomes:
  var $x_0 := x;               -- before-snapshot of x
  x := expr;                   -- original assignment
-/

private abbrev TypeEnv := List (Identifier × HighType)

private def lookupType (env : TypeEnv) (name : Identifier) : HighType :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => ty
  | none => .TInt  -- Default fallback

/-- Substitution map: variable name → name to use in expressions -/
private abbrev SubstMap := List (Identifier × Identifier)

private def SubstMap.lookup (m : SubstMap) (name : Identifier) : Option Identifier :=
  m.find? (·.1 == name) |>.map (·.2)

private def SubstMap.set (m : SubstMap) (name : Identifier) (value : Identifier) : SubstMap :=
  (name, value) :: m.filter (·.1 != name)

structure LiftState where
  /-- Statements to prepend before the current expression (in reverse order) -/
  prependedStmts : List StmtExpr := []
  /-- Counter for generating unique temp names per variable -/
  varCounters : List (Identifier × Nat) := []
  /-- Substitution map: variable name → name to use -/
  subst : SubstMap := []
  /-- Type environment -/
  env : TypeEnv := []
  /-- Global counter for fresh conditional variables -/
  condCounter : Nat := 0

abbrev LiftM := StateM LiftState

private def freshTempFor (varName : Identifier) : LiftM Identifier := do
  let counters := (← get).varCounters
  let counter := counters.find? (·.1 == varName) |>.map (·.2) |>.getD 0
  modify fun s => { s with varCounters := (varName, counter + 1) :: s.varCounters.filter (·.1 != varName) }
  return s!"${varName}_{counter}"

private def freshCondVar : LiftM Identifier := do
  let n := (← get).condCounter
  modify fun s => { s with condCounter := n + 1 }
  return s!"$c_{n}"

private def addPrepend (stmt : StmtExpr) : LiftM Unit :=
  modify fun s => { s with prependedStmts := stmt :: s.prependedStmts }

private def takePrepends : LiftM (List StmtExpr) := do
  let stmts := (← get).prependedStmts
  modify fun s => { s with prependedStmts := [] }
  return stmts.reverse

private def getVarType (varName : Identifier) : LiftM HighType := do
  return lookupType (← get).env varName

private def addToEnv (varName : Identifier) (ty : HighType) : LiftM Unit :=
  modify fun s => { s with env := (varName, ty) :: s.env }

private def getSubst (varName : Identifier) : LiftM Identifier := do
  match (← get).subst.lookup varName with
  | some mapped => return mapped
  | none => return varName

private def setSubst (varName : Identifier) (value : Identifier) : LiftM Unit :=
  modify fun s => { s with subst := s.subst.set varName value }

/-- Apply the current substitution map to an expression (replaces Identifiers). -/
private partial def applySubst (expr : StmtExpr) : LiftM StmtExpr := do
  match expr with
  | .Identifier name =>
      return .Identifier (← getSubst name)
  | .PrimitiveOp op args =>
      return .PrimitiveOp op (← args.mapM applySubst)
  | .IfThenElse cond th el => do
      let newEl ← match el with
        | some e => pure (some (← applySubst e))
        | none => pure none
      return .IfThenElse (← applySubst cond) (← applySubst th) newEl
  | .StaticCall name args =>
      return .StaticCall name (← args.mapM applySubst)
  | .LiteralInt _ | .LiteralBool _ => return expr
  | _ => return expr

/-- Infer the type of a StmtExpr from the environment. Best-effort. -/
private def inferType (expr : StmtExpr) : LiftM HighType := do
  match expr with
  | .Identifier name => getVarType name
  | .LiteralInt _ => return .TInt
  | .LiteralBool _ => return .TBool
  | .PrimitiveOp op _ =>
      match op with
      | .Eq | .Neq | .And | .Or | .Not | .Lt | .Leq | .Gt | .Geq => return .TBool
      | .Neg | .Add | .Sub | .Mul | .Div | .Mod => return .TInt
  | .IfThenElse _ th _ => inferType th
  | _ => return .TInt  -- fallback

/-- Check if an expression contains any assignments (recursively). -/
private partial def containsAssignment : StmtExpr → Bool
  | .Assign .. => true
  | .PrimitiveOp _ args => args.any containsAssignment
  | .IfThenElse cond th el =>
      containsAssignment cond || containsAssignment th ||
      match el with | some e => containsAssignment e | none => false
  | .StaticCall _ args => args.any containsAssignment
  | .Block stmts _ => stmts.any containsAssignment
  | _ => false

mutual
/--
Process an expression in expression context, traversing arguments right to left.
Assignments are lifted to prependedStmts and replaced with snapshot variable references.
Returns the transformed (pure) expression.
-/
partial def transformExpr (expr : StmtExpr) : LiftM StmtExpr := do
  match expr with
  | .Identifier name =>
      -- Look up substitution: if a later (rightward) assignment updated the map, use the snapshot
      return .Identifier (← getSubst name)

  | .LiteralInt _ | .LiteralBool _ => return expr

  | .Assign targets value md =>
      -- Assignment in expression position.
      -- First, transform the value (it may itself contain assignments)
      let seqValue ← transformExpr value
      -- The expression result is the current substitution for the target variable
      -- (this is what the variable maps to AFTER this assignment, which we already know
      -- because we traversed right-to-left)
      let firstTarget := targets.head?.getD (.Identifier "__unknown")
      let resultExpr ← match firstTarget with
        | .Identifier varName => pure (.Identifier (← getSubst varName))
        | other => pure other
      -- Now create a before-snapshot: the variable's value before this assignment.
      -- This becomes the new substitution for references to the LEFT of this assignment.
      match firstTarget with
      | .Identifier varName =>
          let snapshotName ← freshTempFor varName
          let varType ← getVarType varName
          -- Prepend: snapshot declaration before the assignment.
          -- Since the stack is reversed on take, we add snapshot last (so it ends up first).
          addPrepend (.LocalVariable snapshotName varType (some (.Identifier varName)))
          addPrepend (.Assign targets seqValue md)
          -- Update substitution: references to the left of this assignment use the snapshot
          setSubst varName snapshotName
      | _ =>
          addPrepend (.Assign targets seqValue md)
      return resultExpr

  | .PrimitiveOp op args =>
      -- Process arguments right to left
      let seqArgs ← args.reverse.mapM transformExpr
      return .PrimitiveOp op seqArgs.reverse

  | .StaticCall name args =>
      let seqArgs ← args.reverse.mapM transformExpr
      return .StaticCall name seqArgs.reverse

  | .IfThenElse cond thenBranch elseBranch =>
      -- Check if either branch contains assignments
      let thenHasAssign := containsAssignment thenBranch
      let elseHasAssign := match elseBranch with
        | some e => containsAssignment e
        | none => false
      if thenHasAssign || elseHasAssign then
        -- Lift the entire if-then-else to a prepended statement.
        -- Introduce a fresh variable to capture the result of each branch.
        let condVar ← freshCondVar
        -- Process the condition (it might contain assignments too)
        let seqCond ← transformExpr cond
        -- Process each branch independently (fresh algorithm run).
        -- Save and restore subst/prepends so branches don't interfere with each other
        -- or with the outer expression.
        let savedSubst := (← get).subst
        let savedPrepends := (← get).prependedStmts
        -- Process then-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqThen ← transformExpr thenBranch
        let thenPrepends ← takePrepends
        -- Build then-branch block: prepended stmts + assign result to condVar
        let emptyMd : Imperative.MetaData Core.Expression := #[]
        let thenBlock := .Block (thenPrepends ++ [.Assign [.Identifier condVar] seqThen emptyMd]) none
        -- Process else-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqElse ← match elseBranch with
          | some e => do
              let se ← transformExpr e
              let elsePrepends ← takePrepends
              pure (some (.Block (elsePrepends ++ [.Assign [.Identifier condVar] se emptyMd]) none))
          | none => pure none
        -- Restore outer state
        modify fun s => { s with subst := savedSubst, prependedStmts := savedPrepends }
        -- Infer the type from the then-branch result expression
        let condType ← inferType seqThen
        -- Prepend: declaration of condVar, then the if-then-else
        addPrepend (.LocalVariable condVar condType none)
        addPrepend (.IfThenElse seqCond thenBlock seqElse)
        return .Identifier condVar
      else
        -- No assignments in branches — just recurse normally
        let seqCond ← transformExpr cond
        let seqThen ← transformExpr thenBranch
        let seqElse ← match elseBranch with
          | some e => pure (some (← transformExpr e))
          | none => pure none
        return .IfThenElse seqCond seqThen seqElse

  | .Block stmts metadata =>
      -- Block in expression position: process statements in order,
      -- lifting all but the last to prepends. The last is the expression value.
      let rec processBlock (remStmts : List StmtExpr) : LiftM StmtExpr := do
        match remStmts with
        | [] => return .Block [] metadata
        | [last] => transformExpr last
        | head :: tail => do
            let lifted ← transformStmt head
            for s in lifted do
              addPrepend s
            processBlock tail
      processBlock stmts

  | _ => return expr

/--
Process a statement, handling any assignments in its sub-expressions.
Returns a list of statements (the original may expand into multiple).
-/
partial def transformStmt (stmt : StmtExpr) : LiftM (List StmtExpr) := do
  match stmt with
  | .Assert cond md =>
      let seqCond ← transformExpr cond
      let prepends ← takePrepends
      return prepends ++ [.Assert seqCond md]

  | .Assume cond md =>
      let seqCond ← transformExpr cond
      let prepends ← takePrepends
      return prepends ++ [.Assume seqCond md]

  | .Block stmts metadata =>
      let seqStmts ← stmts.mapM transformStmt
      return [.Block seqStmts.flatten metadata]

  | .LocalVariable name ty initializer =>
      addToEnv name ty
      match initializer with
      | some initExpr =>
          let seqInit ← transformExpr initExpr
          let prepends ← takePrepends
          -- Clear substitution after processing initializer so it doesn't leak
          modify fun s => { s with subst := [] }
          return prepends ++ [.LocalVariable name ty (some seqInit)]
      | none =>
          return [stmt]

  | .Assign targets value md =>
      -- Statement-level assignment: snapshot before, then assign
      let seqValue ← transformExpr value
      let prepends ← takePrepends
      -- Create before-snapshots for each target
      let mut snapshots : List StmtExpr := []
      for target in targets do
        match target with
        | .Identifier varName =>
            let snapshotName ← freshTempFor varName
            let snapshotType ← getVarType varName
            snapshots := snapshots ++ [.LocalVariable snapshotName snapshotType (some (.Identifier varName))]
        | _ => pure ()
      -- Clear substitution after statement-level assignment
      modify fun s => { s with subst := [] }
      return prepends ++ snapshots ++ [.Assign targets seqValue md]

  | .IfThenElse cond thenBranch elseBranch =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      let seqThen ← do
        let stmts ← transformStmt thenBranch
        pure (.Block stmts none)
      let seqElse ← match elseBranch with
        | some e => do
            let se ← transformStmt e
            pure (some (.Block se none))
        | none => pure none
      return condPrepends ++ [.IfThenElse seqCond seqThen seqElse]

  | .While cond inv dec body =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      let seqBody ← do
        let stmts ← transformStmt body
        pure (.Block stmts none)
      return condPrepends ++ [.While seqCond inv dec seqBody]

  | .StaticCall name args =>
      let seqArgs ← args.mapM transformExpr
      let prepends ← takePrepends
      return prepends ++ [.StaticCall name seqArgs]

  | _ => return [stmt]

end

def transformProcedureBody (body : StmtExpr) : LiftM StmtExpr := do
  let stmts ← transformStmt body
  match stmts with
  | [single] => pure single
  | multiple => pure (.Block multiple none)

def transformProcedure (proc : Procedure) : LiftM Procedure := do
  -- Initialize environment with procedure parameters
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type))
  -- Reset state for each procedure
  modify fun s => { s with subst := [], prependedStmts := [], varCounters := [], env := initEnv }
  match proc.body with
  | .Transparent bodyExpr =>
      let seqBody ← transformProcedureBody bodyExpr
      pure { proc with body := .Transparent seqBody }
  | _ => pure proc

/--
Transform a program to lift all assignments that occur in an expression context.
-/
def liftExpressionAssignments (program : Program) : Except (Array DiagnosticModel) Program :=
  let initState : LiftState := { prependedStmts := [], env := [] }
  let (seqProcedures, _) := (program.staticProcedures.mapM transformProcedure).run initState
  .ok { program with staticProcedures := seqProcedures }

end Laurel
