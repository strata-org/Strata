/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelFormat
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Core.Verifier
public import Strata.DL.Util.Map
import Strata.Util.Tactics

namespace Strata
namespace Laurel

public section

/-
Transform assignments that appear in expression contexts into preceding statements.

When we see expressions, we traverse them right to left.
For each variable, we maintain a substitution map, which is initially filled with the actual variable.
If we encounter an assignment, we replace it with the current substitution for that variable. We then come up with a new snapshot variable name, and push that to the subsitution map.
We also push both the assignment and an assignment to the snapshot variable to a stack over prependStatements.

When we encounter an if-then-else, we rerun our algorithm from scratch on both branches,
so nested assignments are moved to the start of each branch.
If any assignments were discovered in the branches,
lift the entire if-then-else by putting it on the prependStatements stack.
Introduce a fresh variable and for each branch,
assign the last statement in that branch to the fresh variable.

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
  var z: bool := $c_0 || b;

Example 3 — Statement-level assignment:
  x := expr;

Becomes:
  var $x_0 := x;               -- before-snapshot of x
  x := expr;                   -- original assignment
-/

/-- Substitution map: variable name → name to use in expressions -/
private abbrev SubstMap := Map Identifier Identifier

structure LiftState where
  /-- Statements to prepend (in reverse order — newest first) -/
  prependedStmts : List StmtExprMd := []
  /-- Counter for generating unique temp names per variable -/
  varCounters : List (Identifier × Nat) := []
  /-- Substitution map: variable name → name to use -/
  private subst : SubstMap := []
  /-- Type environment -/
  model : SemanticModel
  /-- Global counter for fresh conditional variables -/
  condCounter : Nat := 0
  /-- All procedures in the program, used to look up return types of imperative calls -/
  procedures : List Procedure := []

@[expose] abbrev LiftM := StateM LiftState

private def emptyMd : Imperative.MetaData Core.Expression := #[]

/-- Wrap a StmtExpr value with empty metadata -/
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, emptyMd⟩

/-- Wrap a HighType value with empty metadata -/
private def bareType (v : HighType) : HighTypeMd := ⟨v, emptyMd⟩

private def freshTempFor (varName : Identifier) : LiftM Identifier := do
  let counters := (← get).varCounters
  let counter := counters.find? (·.1 == varName) |>.map (·.2) |>.getD 0
  modify fun s => { s with varCounters := (varName, counter + 1) :: s.varCounters.filter (·.1 != varName) }
  return s!"${varName.text}_{counter}"

private def freshCondVar : LiftM Identifier := do
  let n := (← get).condCounter
  modify fun s => { s with condCounter := n + 1 }
  return s!"$c_{n}"

private def addPrepend (stmt : StmtExprMd) : LiftM Unit :=
  modify fun s => { s with prependedStmts := stmt :: s.prependedStmts }

private def takePrepends : LiftM (List StmtExprMd) := do
  let stmts := (← get).prependedStmts
  modify fun s => { s with prependedStmts := [] }
  return stmts

private def getSubst (varName : Identifier) : LiftM Identifier := do
  match (← get).subst.lookup varName with
  | some mapped => return mapped
  | none => return varName

private def setSubst (varName : Identifier) (value : Identifier) : LiftM Unit :=
  modify fun s => { s with subst := ⟨ varName, value ⟩ :: s.subst }

private def computeType (expr : StmtExprMd) : LiftM HighTypeMd := do
  let s ← get
  return computeExprType s.model expr

/-- Check if an expression contains any assignments or imperative calls (recursively). -/
private def containsAssignmentOrImperativeCall (model: SemanticModel) (expr : StmtExprMd) : Bool :=
  match expr with
  | WithMetadata.mk val _ =>
  match val with
  | .Assign .. => true
  | .StaticCall name args1 =>
    (match model.get name with
    | .staticProcedure proc => !proc.isFunctional
    | _ => false) ||
      args1.attach.any (fun x => containsAssignmentOrImperativeCall model x.val)
  | .PrimitiveOp _ args2 => args2.attach.any (fun x => containsAssignmentOrImperativeCall model x.val)
  | .Block stmts _ => stmts.attach.any (fun x => containsAssignmentOrImperativeCall model x.val)
  | .IfThenElse cond th el =>
      containsAssignmentOrImperativeCall model cond ||
      containsAssignmentOrImperativeCall model th ||
      match el with | some e => containsAssignmentOrImperativeCall model e | none => false
  | _ => false
  termination_by expr
  decreasing_by
    all_goals ((try cases x); simp_all; try term_by_mem)

/--
Shared logic for lifting an assignment in expression position:
prepends the assignment, creates before-snapshots for all targets,
and updates substitutions. The value should already be transformed by the caller.
-/
private def liftAssignExpr (targets : List StmtExprMd) (seqValue : StmtExprMd)
    (md : Imperative.MetaData Core.Expression) : LiftM Unit := do
  -- Prepend the assignment itself
  addPrepend (⟨.Assign targets seqValue, md⟩)
  -- Create a before-snapshot for each target and update substitutions
  for target in targets do
    match target.val with
    | .Identifier varName =>
        let snapshotName ← freshTempFor varName
        let varType ← computeType target
        -- Snapshot goes before the assignment (cons pushes to front)
        addPrepend (⟨.LocalVariable snapshotName varType (some (⟨.Identifier varName, md⟩)), md⟩)
        setSubst varName snapshotName
    | _ => pure ()

mutual
/--
Process an expression in expression context, traversing arguments right to left.
Assignments are lifted to prependedStmts and replaced with snapshot variable references.
-/
def transformExpr (expr : StmtExprMd) : LiftM StmtExprMd := do
  match expr with
  | WithMetadata.mk val md =>
  match val with
  | .Identifier name =>
      return ⟨.Identifier (← getSubst name), md⟩

  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ => return expr

  | .Assign targets value =>
      -- The expression result is the current substitution for the first target
      -- (we already know what it maps to AFTER this assignment from right-to-left traversal)
      let firstTarget := targets.head?.getD (panic "Assign must have non-empty targets")
      let resultExpr ← match firstTarget.val with
        | .Identifier varName => pure (⟨.Identifier (← getSubst varName), md⟩)
        | _ => panic "Non-identifier targets not supported in the lift expression phase"

      -- Use the original value (not seqValue) for the prepended assignment,
      -- because prepended statements execute in program order and don't need substitutions.
      liftAssignExpr targets value md

      return resultExpr

  | .PrimitiveOp op args =>
      -- Process arguments right to left
      let seqArgs ← args.reverse.mapM transformExpr
      return ⟨.PrimitiveOp op seqArgs.reverse, md⟩

  | .StaticCall callee args =>
    let model := (← get).model
    let seqArgs ← args.reverse.mapM transformExpr
    let seqCall := ⟨.StaticCall callee seqArgs.reverse, md⟩
    if model.isFunction callee then
      return seqCall
    else
      -- Imperative call in expression position: lift it like an assignment
      -- Order matters: assign must be prepended first (it's newest-first),
      -- so that when reversed the var declaration comes before the call.
      let callResultVar ← freshCondVar
      let callResultType ← computeType expr
      addPrepend (⟨.Assign [bare (.Identifier callResultVar)] seqCall, md⟩)
      addPrepend (bare (.LocalVariable callResultVar callResultType none))
      return bare (.Identifier callResultVar)

  | .IfThenElse cond thenBranch elseBranch =>
      let model :=  (← get).model
      let thenHasAssign := containsAssignmentOrImperativeCall model thenBranch
      let elseHasAssign := match elseBranch with
        | some e => containsAssignmentOrImperativeCall model e
        | none => false
      if thenHasAssign || elseHasAssign then
        -- Lift the entire if-then-else. Introduce a fresh variable for the result.
        let condVar ← freshCondVar
        let seqCond ← transformExpr cond
        -- Save outer state
        let savedSubst := (← get).subst
        let savedPrepends := (← get).prependedStmts
        -- Process then-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqThen ← transformExpr thenBranch
        let thenPrepends ← takePrepends
        let thenBlock := bare (.Block (thenPrepends ++ [⟨.Assign [bare (.Identifier condVar)] seqThen, md⟩]) none)
        -- Process else-branch from scratch
        modify fun s => { s with prependedStmts := [], subst := [] }
        let seqElse ← match elseBranch with
          | some e => do
              let se ← transformExpr e
              let elsePrepends ← takePrepends
              pure (some (bare (.Block (elsePrepends ++ [⟨.Assign [bare (.Identifier condVar)] se, md⟩]) none)))
          | none => pure none
        -- Restore outer state
        modify fun s => { s with subst := savedSubst, prependedStmts := savedPrepends }
        -- Infer type from the ORIGINAL then-branch (not the transformed one),
        -- because the transformed expression may reference freshly generated
        -- variables (e.g. $c_2) that don't exist in the SemanticModel yet.
        let condType ← computeType thenBranch
        -- IfThenElse added first (cons puts it deeper), then declaration (cons puts it on top)
        -- Output order: declaration, then if-then-else
        addPrepend (⟨.IfThenElse seqCond thenBlock seqElse, md⟩)
        addPrepend (bare (.LocalVariable condVar condType none))
        return bare (.Identifier condVar)
      else
        -- No assignments in branches — recurse normally
        let seqCond ← transformExpr cond
        let seqThen ← transformExpr thenBranch
        let seqElse ← match elseBranch with
          | some e => pure (some (← transformExpr e))
          | none => pure none
        return ⟨.IfThenElse seqCond seqThen seqElse, md⟩

  | .Block stmts metadata =>
      -- Block in expression position: lift all but last to prepends
      match h_last : stmts.getLast? with
      | none => return bare (.Block [] metadata)
      | some last => do
          have := List.mem_of_getLast? h_last

          -- Process all-but-last as statements and prepend them in order
          let mut blockStmts : List StmtExprMd := []
          for nonLastStatement in stmts.dropLast.attach do
            have := List.dropLast_subset stmts nonLastStatement.property
            blockStmts := blockStmts ++ (← transformStmt nonLastStatement)
          for s in blockStmts.reverse do addPrepend s
          -- Last element is the expression value
          transformExpr last

  | .LocalVariable name ty initializer =>
      -- If the substitution map has an entry for this variable, it was
      -- assigned to the right and we need to lift this declaration so it
      -- appears before the snapshot that references it.
      let hasSubst := (← get).subst.lookup name |>.isSome
      if hasSubst then
        match initializer with
        | some initExpr =>
            let seqInit ← transformExpr initExpr
            addPrepend (⟨.LocalVariable name ty (some seqInit), expr.md⟩)
        | none =>
            addPrepend (⟨.LocalVariable name ty none, expr.md⟩)
        return ⟨.Identifier (← getSubst name), expr.md⟩
      else
        return expr

  | _ => return expr
  termination_by (sizeOf expr, 0)
  decreasing_by
    all_goals (simp_all; try term_by_mem)

/--
Process a statement, handling any assignments in its sub-expressions.
Returns a list of statements (the original may expand into multiple).
-/
def transformStmt (stmt : StmtExprMd) : LiftM (List StmtExprMd) := do
  match stmt with
  | WithMetadata.mk val md =>
  match val with
  | .Assert _ =>
      -- Do not transform assert conditions: impure expressions inside contracts
      -- must be rejected by the translator, not silently lifted.
      return [stmt]

  | .Assume _ =>
      -- Do not transform assume conditions: same reasoning as assert.
      return [stmt]

  | .Block stmts metadata =>
      let seqStmts ← stmts.mapM transformStmt
      return [bare (.Block seqStmts.flatten metadata)]

  | .LocalVariable name ty initializer =>
      match _ : initializer with
      | some initExprMd =>
          -- If the initializer is a direct imperative StaticCall, don't lift it —
          -- translateStmt handles LocalVariable + StaticCall directly as a call statement.
          match _: initExprMd with
          | WithMetadata.mk initExpr _ =>
          match _: initExpr with
          | .StaticCall callee args =>
              let model := (← get).model
              if model.isFunction callee then
                let seqInit ← transformExpr initExprMd
                let prepends ← takePrepends
                modify fun s => { s with subst := [] }
                return prepends ++ [⟨.LocalVariable name ty (some seqInit), md⟩]
              else
                -- Pass through as-is; translateStmt will emit init + call
                let seqArgs ← args.mapM transformExpr
                let argPrepends ← takePrepends
                modify fun s => { s with subst := [] }
                return argPrepends ++ [⟨.LocalVariable name ty (some ⟨.StaticCall callee seqArgs, initExprMd.md⟩), md⟩]
          | _ =>
              let seqInit ← transformExpr initExprMd
              let prepends ← takePrepends
              modify fun s => { s with subst := [] }
              return prepends ++ [⟨.LocalVariable name ty (some seqInit), md⟩]
      | none =>
          return [stmt]

  | .Assign targets valueMd =>
      -- If the RHS is a direct imperative StaticCall, don't lift it —
      -- translateStmt handles Assign + StaticCall directly as a call statement.
      match _: valueMd with
      | WithMetadata.mk value _ =>
      match _: value with
      | .StaticCall callee args =>
          let model := (← get).model
          if model.isFunction callee then
            let seqValue ← transformExpr valueMd
            let prepends ← takePrepends
            modify fun s => { s with subst := [] }
            return prepends ++ [⟨.Assign targets seqValue, md⟩]
          else
            let seqArgs ← args.mapM transformExpr
            let argPrepends ← takePrepends
            modify fun s => { s with subst := [] }
            return argPrepends ++ [⟨.Assign targets ⟨.StaticCall callee seqArgs, md⟩, md⟩]
      | _ =>
          let seqValue ← transformExpr valueMd
          let prepends ← takePrepends
          modify fun s => { s with subst := [] }
          return prepends ++ [⟨.Assign targets seqValue, md⟩]

  | .IfThenElse cond thenBranch elseBranch =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      let seqThen ← do
        let stmts ← transformStmt thenBranch
        pure (bare (.Block stmts none))
      let seqElse ← match elseBranch with
        | some e => do
            let se ← transformStmt e
            pure (some (bare (.Block se none)))
        | none => pure none
      return condPrepends ++ [⟨.IfThenElse seqCond seqThen seqElse, md⟩]

  | .While cond invs dec body =>
      let seqCond ← transformExpr cond
      let condPrepends ← takePrepends
      let seqBody ← do
        let stmts ← transformStmt body
        pure (bare (.Block stmts none))
      return condPrepends ++ [⟨.While seqCond invs dec seqBody, md⟩]

  | .StaticCall name args =>
      let seqArgs ← args.mapM transformExpr
      let prepends ← takePrepends
      return prepends ++ [⟨.StaticCall name seqArgs, md⟩]

  | _ =>
      return [stmt]
  termination_by (sizeOf stmt, 0)
  decreasing_by
    all_goals (try term_by_mem)
    all_goals (apply Prod.Lex.left; try term_by_mem)
end

def transformProcedureBody (body : StmtExprMd) : LiftM StmtExprMd := do
  let stmts ← transformStmt body
  match stmts with
  | [single] => pure single
  | multiple => pure (bare (.Block multiple none))

def transformProcedure (proc : Procedure) : LiftM Procedure := do
  modify fun s => { s with subst := [], prependedStmts := [], varCounters := [] }
  match proc.body with
  | .Transparent bodyExpr =>
      let seqBody ← transformProcedureBody bodyExpr
      pure { proc with body := .Transparent seqBody }
  | .Opaque postconds impl modif =>
      let impl' ← impl.mapM transformProcedureBody
      pure { proc with body := .Opaque postconds impl' modif }
  | .Abstract _ =>
      pure proc
  | .External =>
      pure proc

/--
Transform a program to lift all assignments that occur in an expression context.
-/
def liftExpressionAssignments (model: SemanticModel) (program : Program) : Program :=
  let initState : LiftState := { model := model }
  let (seqProcedures, _) := (program.staticProcedures.mapM transformProcedure).run initState
  { program with staticProcedures := seqProcedures }

/-! ## Hole Lifting

Lift `.Hole` nodes out of expression positions so that every Hole only appears
as the RHS of a `LocalVariable` initializer (which the translator handles as havoc).

A Hole in expression position is replaced by a fresh variable whose declaration
has no initializer, giving it an arbitrary value — a sound over-approximation.
-/

/-- Counter state for generating fresh hole variable names. -/
structure HoleLiftState where
  counter : Nat := 0

private abbrev HoleLiftM := StateM HoleLiftState

private def freshHoleVar : HoleLiftM Identifier := do
  let n := (← get).counter
  modify fun s => { s with counter := n + 1 }
  return s!"$hole_{n}"

private def defaultHoleType : HighTypeMd := bareType .Top

/-- Lightweight syntactic type inference — returns a type when it can be
    determined without a semantic model (literals, arithmetic ops, etc.). -/
private def inferType : StmtExpr → Option HighTypeMd
  | .LiteralInt _     => some (bareType .TInt)
  | .LiteralBool _    => some (bareType .TBool)
  | .LiteralString _  => some (bareType .TString)
  | .LiteralDecimal _ => some (bareType .TReal)
  | .PrimitiveOp op _ =>
      match op with
      | .Eq | .Neq | .And | .Or | .Not | .Implies
      | .Lt | .Leq | .Gt | .Geq => some (bareType .TBool)
      | .StrConcat => some (bareType .TString)
      | _ => none
  | _ => none

/-- For a comparison operator, infer the argument type from the first
    non-hole sibling whose type can be determined syntactically. -/
private def inferComparisonArgType (args : List StmtExprMd) : HighTypeMd :=
  args.findSome? (fun a => match a.val with | .Hole => none | _ => inferType a.val)
    |>.getD defaultHoleType

mutual
/-- Lift holes from a list of arguments, collecting declarations. -/
private def liftHoleArgs (args : List StmtExprMd) (expectedType : HighTypeMd) : HoleLiftM (List StmtExprMd × List StmtExprMd) := do
  let mut newArgs : List StmtExprMd := []
  let mut decls : List StmtExprMd := []
  for a in args do
    let (a', ds) ← liftHoleExpr a expectedType
    newArgs := newArgs ++ [a']
    decls := decls ++ ds
  return (newArgs, decls)

/-- Replace every `.Hole` in an expression with a fresh variable reference,
    accumulating `LocalVariable` declarations (no initializer) to prepend.
    `expectedType` is the type inferred from the surrounding context. -/
private def liftHoleExpr (expr : StmtExprMd) (expectedType : HighTypeMd) : HoleLiftM (StmtExprMd × List StmtExprMd) := do
  match expr with
  | WithMetadata.mk val md =>
  match val with
  | .Hole =>
      let v ← freshHoleVar
      let decl := bare (.LocalVariable v expectedType none)
      return (⟨.Identifier v, md⟩, [decl])
  | .PrimitiveOp op args =>
      let argType := match op with
        | .Eq | .Neq | .Lt | .Leq | .Gt | .Geq => inferComparisonArgType args
        | _ => expectedType
      let (newArgs, decls) ← liftHoleArgs args argType
      return (⟨.PrimitiveOp op newArgs, md⟩, decls)
  | .StaticCall callee args =>
      let (newArgs, decls) ← liftHoleArgs args defaultHoleType
      return (⟨.StaticCall callee newArgs, md⟩, decls)
  | .InstanceCall target callee args =>
      let (target', d1) ← liftHoleExpr target defaultHoleType
      let (newArgs, d2) ← liftHoleArgs args defaultHoleType
      return (⟨.InstanceCall target' callee newArgs, md⟩, d1 ++ d2)
  | .ReferenceEquals lhs rhs =>
      let (lhs', d1) ← liftHoleExpr lhs defaultHoleType
      let (rhs', d2) ← liftHoleExpr rhs defaultHoleType
      return (⟨.ReferenceEquals lhs' rhs', md⟩, d1 ++ d2)
  | .IfThenElse cond th el =>
      let (cond', d1) ← liftHoleExpr cond (bareType .TBool)
      let (th', d2) ← liftHoleExpr th expectedType
      let (el', d3) ← match el with
        | some e => do let (e', ds) ← liftHoleExpr e expectedType; pure (some e', ds)
        | none => pure (none, [])
      return (⟨.IfThenElse cond' th' el', md⟩, d1 ++ d2 ++ d3)
  | .Block stmts label =>
      let stmts' ← liftHoleStmtList stmts
      return (⟨.Block stmts' label, md⟩, [])
  | .Assign targets value =>
      let (value', decls) ← liftHoleExpr value defaultHoleType
      return (⟨.Assign targets value', md⟩, decls)
  | .LocalVariable name ty init =>
      match init with
      | some initExpr =>
          let (initExpr', decls) ← liftHoleExpr initExpr ty
          return (⟨.LocalVariable name ty (some initExpr'), md⟩, decls)
      | none => return (expr, [])
  | .Old v =>
      let (v', ds) ← liftHoleExpr v expectedType
      return (⟨.Old v', md⟩, ds)
  | .Fresh v =>
      let (v', ds) ← liftHoleExpr v defaultHoleType
      return (⟨.Fresh v', md⟩, ds)
  | .Assigned n =>
      let (n', ds) ← liftHoleExpr n defaultHoleType
      return (⟨.Assigned n', md⟩, ds)
  | .ProveBy v p =>
      let (v', d1) ← liftHoleExpr v expectedType
      let (p', d2) ← liftHoleExpr p defaultHoleType
      return (⟨.ProveBy v' p', md⟩, d1 ++ d2)
  | .ContractOf ty f =>
      let (f', ds) ← liftHoleExpr f defaultHoleType
      return (⟨.ContractOf ty f', md⟩, ds)
  | .Forall p trigger b =>
      let (trigger', d1) ← match trigger with
        | some t => let (t', ds) ← liftHoleExpr t defaultHoleType; pure (some t', ds)
        | none => pure (none, [])
      let (b', d2) ← liftHoleExpr b (bareType .TBool)
      return (⟨.Forall p trigger' b', md⟩, d1 ++ d2)
  | .Exists p trigger b =>
      let (trigger', d1) ← match trigger with
        | some t => let (t', ds) ← liftHoleExpr t defaultHoleType; pure (some t', ds)
        | none => pure (none, [])
      let (b', d2) ← liftHoleExpr b (bareType .TBool)
      return (⟨.Exists p trigger' b', md⟩, d1 ++ d2)
  | _ => return (expr, [])

/-- Process a statement, lifting holes from sub-expressions.
    Returns the replacement statements (may expand) and any declarations to hoist. -/
private def liftHoleStmt (stmt : StmtExprMd) : HoleLiftM (List StmtExprMd × List StmtExprMd) := do
  match stmt with
  | WithMetadata.mk val md =>
  match val with
  | .LocalVariable name ty (some initExpr) =>
      -- If the initializer IS a bare Hole, keep it in place (translator handles this as havoc)
      match initExpr.val with
      | .Hole => return ([stmt], [])
      | _ =>
          let (initExpr', decls) ← liftHoleExpr initExpr ty
          return ([⟨.LocalVariable name ty (some initExpr'), md⟩], decls)
  | .Assign targets value =>
      let (value', decls) ← liftHoleExpr value defaultHoleType
      return ([⟨.Assign targets value', md⟩], decls)
  | .Block stmts label =>
      let stmts' ← liftHoleStmtList stmts
      return ([⟨.Block stmts' label, md⟩], [])
  | .IfThenElse cond th el =>
      let (cond', d1) ← liftHoleExpr cond (bareType .TBool)
      let (th', d2) ← liftHoleStmt th
      let thStmts := bare (.Block th' none)
      let (el', d3) ← match el with
        | some e => do let (es, ds) ← liftHoleStmt e; pure (some (bare (.Block es none)), ds)
        | none => pure (none, [])
      return ([⟨.IfThenElse cond' thStmts el', md⟩], d1 ++ d2 ++ d3)
  | .While cond invs dec body =>
      let (cond', d1) ← liftHoleExpr cond (bareType .TBool)
      let mut invDecls : List StmtExprMd := []
      let mut newInvs : List StmtExprMd := []
      for inv in invs do
        let (inv', ds) ← liftHoleExpr inv (bareType .TBool)
        newInvs := newInvs ++ [inv']
        invDecls := invDecls ++ ds
      let (dec', d3) ← match dec with
        | some d => do let (d', ds) ← liftHoleExpr d (bareType .TInt); pure (some d', ds)
        | none => pure (none, [])
      let (bodyStmts, d2) ← liftHoleStmt body
      let bodyBlock := bare (.Block bodyStmts none)
      return ([⟨.While cond' newInvs dec' bodyBlock, md⟩], d1 ++ invDecls ++ d3 ++ d2)
  | .Assert cond =>
      let (cond', decls) ← liftHoleExpr cond (bareType .TBool)
      return ([⟨.Assert cond', md⟩], decls)
  | .Assume cond =>
      let (cond', decls) ← liftHoleExpr cond (bareType .TBool)
      return ([⟨.Assume cond', md⟩], decls)
  | .StaticCall callee args =>
      let (newArgs, decls) ← liftHoleArgs args defaultHoleType
      return ([⟨.StaticCall callee newArgs, md⟩], decls)
  | .Return (some retExpr) =>
      let (retExpr', decls) ← liftHoleExpr retExpr defaultHoleType
      return ([⟨.Return (some retExpr'), md⟩], decls)
  | _ => return ([stmt], [])

/-- Process a list of statements, inlining hoisted declarations before each statement. -/
private def liftHoleStmtList (stmts : List StmtExprMd) : HoleLiftM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  for s in stmts do
    let (expanded, decls) ← liftHoleStmt s
    -- Inline declarations immediately before the statement that needs them
    result := result ++ decls ++ expanded
  return result
end

private def liftHoleProcedure (proc : Procedure) : HoleLiftM Procedure := do
  -- Reset counter per procedure for deterministic, debuggable output
  modify fun _ => { counter := 0 }
  match proc.body with
  | .Transparent bodyExpr =>
      let (stmts, decls) ← liftHoleStmt bodyExpr
      if decls.isEmpty && stmts.length == 1 then
        return { proc with body := .Transparent stmts.head! }
      else
        let body := bare (.Block (decls ++ stmts) none)
        return { proc with body := .Transparent body }
  | .Opaque postconds (some impl) modif =>
      let (stmts, decls) ← liftHoleStmt impl
      if decls.isEmpty && stmts.length == 1 then
        return { proc with body := .Opaque postconds (some stmts.head!) modif }
      else
        let body := bare (.Block (decls ++ stmts) none)
        return { proc with body := .Opaque postconds (some body) modif }
  | _ => return proc

/--
Lift `.Hole` nodes out of expression positions so that every Hole only appears
as the RHS of a `LocalVariable` initializer (translated as havoc).
-/
def liftHoles (program : Program) : Program :=
  let initState : HoleLiftState := {}
  let (procs, _) := (program.staticProcedures.mapM liftHoleProcedure).run initState
  { program with staticProcedures := procs }

end -- public section
end Laurel
