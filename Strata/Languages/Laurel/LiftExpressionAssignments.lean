/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Languages.Laurel.LaurelTypes
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

/-- Substitution map: variable name → name to use in expressions -/
private abbrev SubstMap := List (Identifier × Identifier)

private def SubstMap.lookup (m : SubstMap) (name : Identifier) : Option Identifier :=
  m.find? (·.1 == name) |>.map (·.2)

private def SubstMap.set (m : SubstMap) (name : Identifier) (value : Identifier) : SubstMap :=
  (name, value) :: m.filter (·.1 != name)
structure LiftState where
  /-- Statements to prepend before the current expression (in reverse order) -/
  prependedStmts : List StmtExprMd := []
  /-- Counter for generating unique temp names per variable -/
  varCounters : List (Identifier × Nat) := []
  /-- Substitution map: variable name → name to use -/
  subst : SubstMap := []
  /-- Type environment -/
  env : LaurelTypes.TypeEnv := []
  /-- Type definitions for type inference -/
  types : List TypeDefinition := []
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

private def addPrepend (stmt : StmtExprMd) : LiftM Unit :=
  modify fun s => { s with prependedStmts := stmt :: s.prependedStmts }

private def takePrepends : LiftM (List StmtExprMd) := do
  let stmts := (← get).prependedStmts
  modify fun s => { s with prependedStmts := [] }
  return stmts.reverse

private def getVarType (varName : Identifier) : LiftM HighTypeMd := do
  let env := (← get).env
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => return ty
  | none => return default

private def addToEnv (varName : Identifier) (ty : HighTypeMd) : LiftM Unit :=
  modify fun s => { s with env := (varName, ty) :: s.env }

private def getSubst (varName : Identifier) : LiftM Identifier := do
  match (← get).subst.lookup varName with
  | some mapped => return mapped
  | none => return varName

private def setSubst (varName : Identifier) (value : Identifier) : LiftM Unit :=
  modify fun s => { s with subst := s.subst.set varName value }

private def inferExprType (expr : StmtExprMd) : LiftM HighTypeMd := do
  let s ← get
  return LaurelTypes.computeExprType s.env s.types expr

/-- Helper to wrap a StmtExpr with metadata from a source expression -/
private def mkMd (e : StmtExpr) (src : StmtExprMd) : StmtExprMd :=
  { val := e, md := src.md }

/-- Helper to wrap a StmtExpr with empty metadata -/
private def mkMdEmpty (e : StmtExpr) : StmtExprMd :=
  { val := e, md := #[] }

/-- Check if an expression contains any assignments (recursively). -/
private partial def containsAssignment : StmtExprMd → Bool
  | ⟨.Assign .., _⟩ => true
  | ⟨.PrimitiveOp _ args, _⟩ => args.any containsAssignment
  | ⟨.IfThenElse cond th el, _⟩ =>
      containsAssignment cond || containsAssignment th ||
      match el with | some e => containsAssignment e | none => false
  | ⟨.StaticCall _ args, _⟩ => args.any containsAssignment
  | ⟨.Block stmts _, _⟩ => stmts.any containsAssignment
  | _ => false

mutual
/--
Process an expression in expression context, traversing arguments right to left.
Assignments are lifted to prependedStmts and replaced with snapshot variable references.
Returns the transformed (pure) expression.
-/
partial def transformExpr (expr : StmtExprMd) : LiftM StmtExprMd := do
  let md := expr.md
  match expr.val with
  | .Identifier name =>
      return mkMd (.Identifier (← getSubst name)) expr

  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ => return expr

  | .Assign targets value =>
      let seqValue ← transformExpr value
      let firstTarget := targets.head?.getD (mkMdEmpty (.Identifier "__unknown"))
      let resultExpr ← match firstTarget.val with
        | .Identifier varName => pure (mkMd (.Identifier (← getSubst varName)) expr)
        | _ => pure firstTarget
      match firstTarget.val with
      | .Identifier varName =>
          let snapshotName ← freshTempFor varName
          let varType ← getVarType varName
          addPrepend (mkMd (.LocalVariable snapshotName varType (some (mkMd (.Identifier varName) expr))) expr)
          addPrepend (mkMd (.Assign targets seqValue) expr)
          setSubst varName snapshotName
      | _ =>
          addPrepend (mkMd (.Assign targets seqValue) expr)
      return resultExpr

  | .PrimitiveOp op args =>
      let seqArgs ← args.reverse.mapM transformExpr
      return mkMd (.PrimitiveOp op seqArgs.reverse) expr

  | .StaticCall name args =>
      let seqArgs ← args.reverse.mapM transformExpr
      return mkMd (.StaticCall name seqArgs.reverse) expr

  | .IfThenElse cond thenBranch elseBranch =>
      let thenHasAssign := containsAssignment thenBranch
      let elseHasAssign := match elseBranch with
        | some e => containsAssignment e
        | none => false
      if thenHasAssign || elseHasAssign then
        let condVar ← freshCondVar
        let seqCond ← transformExpr cond
        let savedSubst := (← get).subst
        let savedPrepends := (← get).prependedStmts
        -- Process then-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqThen ← transformExpr thenBranch
        let thenPrepends ← takePrepends
        let thenBlock := mkMd (.Block (thenPrepends ++ [mkMd (.Assign [mkMd (.Identifier condVar) expr] seqThen) expr]) none) expr
        -- Process else-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqElse ← match elseBranch with
          | some e => do
              let se ← transformExpr e
              let elsePrepends ← takePrepends
              pure (some (mkMd (.Block (elsePrepends ++ [mkMd (.Assign [mkMd (.Identifier condVar) expr] se) expr]) none) expr))
          | none => pure none
        -- Restore outer state
        modify fun s => { s with subst := savedSubst, prependedStmts := savedPrepends }
        let condType ← inferExprType seqThen
        addPrepend (mkMd (.LocalVariable condVar condType none) expr)
        addPrepend (mkMd (.IfThenElse seqCond thenBlock seqElse) expr)
        return mkMd (.Identifier condVar) expr
      else
        let seqCond ← transformExpr cond
        let seqThen ← transformExpr thenBranch
        let seqElse ← match elseBranch with
          | some e => pure (some (← transformExpr e))
          | none => pure none
        return mkMd (.IfThenElse seqCond seqThen seqElse) expr

  | .Block stmts metadata =>
      let rec processBlock (remStmts : List StmtExprMd) : LiftM StmtExprMd := do
        match remStmts with
        | [] => return mkMd (.Block [] metadata) expr
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
partial def transformStmt (stmt : StmtExprMd) : LiftM (List StmtExprMd) := do
  let md := stmt.md
  match stmt.val with
  | .Assert cond =>
      let seqCond ← transformExpr cond
      let prepends ← takePrepends
      return prepends ++ [mkMd (.Assert seqCond) stmt]

  | .Assume cond =>
      let seqCond ← transformExpr cond
      let prepends ← takePrepends
      return prepends ++ [mkMd (.Assume seqCond) stmt]

  | .Block stmts metadata =>
      let seqStmts ← stmts.mapM transformStmt
      return [mkMd (.Block seqStmts.flatten metadata) stmt]

  | .LocalVariable name ty initializer =>
      addToEnv name ty
      match initializer with
      | some initExpr =>
          let seqInit ← transformExpr initExpr
          let prepends ← takePrepends
          modify fun s => { s with subst := [] }
          return prepends ++ [mkMd (.LocalVariable name ty (some seqInit)) stmt]
      | none =>
          return [stmt]

  | .Assign targets value =>
      let seqValue ← transformExpr value
      let prepends ← takePrepends
      let mut snapshots : List StmtExprMd := []
      for target in targets do
        match target.val with
        | .Identifier varName =>
            let snapshotName ← freshTempFor varName
            let snapshotType ← getVarType varName
            snapshots := snapshots ++ [mkMd (.LocalVariable snapshotName snapshotType (some (mkMd (.Identifier varName) target))) stmt]
        | _ => pure ()
      modify fun s => { s with subst := [] }
      return prepends ++ snapshots ++ [mkMd (.Assign targets seqValue) stmt]

  | .IfThenElse cond thenBranch elseBranch =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      let seqThen ← do
        let stmts ← transformStmt thenBranch
        pure (mkMd (.Block stmts none) thenBranch)
      let seqElse ← match elseBranch with
        | some e => do
            let se ← transformStmt e
            pure (some (mkMd (.Block se none) e))
        | none => pure none
      return condPrepends ++ [mkMd (.IfThenElse seqCond seqThen seqElse) stmt]

  | .While cond inv dec body =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      let seqBody ← do
        let stmts ← transformStmt body
        pure (mkMd (.Block stmts none) body)
      return condPrepends ++ [mkMd (.While seqCond inv dec seqBody) stmt]

  | .StaticCall name args =>
      let seqArgs ← args.mapM transformExpr
      let prepends ← takePrepends
      return prepends ++ [mkMd (.StaticCall name seqArgs) stmt]

  | _ => return [stmt]

end

def transformProcedureBody (body : StmtExprMd) : LiftM StmtExprMd := do
  let stmts ← transformStmt body
  match stmts with
  | [single] => pure single
  | multiple => pure (mkMd (.Block multiple none) body)

def transformProcedure (proc : Procedure) : LiftM Procedure := do
  let initEnv : LaurelTypes.TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type))
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
  let initState : LiftState := {}
  let (seqProcedures, _) := (program.staticProcedures.mapM transformProcedure).run initState
  .ok { program with staticProcedures := seqProcedures }

end Laurel
