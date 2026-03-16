/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelFormat
public import Strata.Languages.Laurel.LaurelTypes

/-!
# Hole Lifting

Lift `.Hole` nodes out of expression positions so that every Hole only appears
as the RHS of a `LocalVariable` initializer (which the translator handles as havoc).

A Hole in expression position is replaced by a fresh variable whose declaration
has no initializer, giving it an arbitrary value — a sound over-approximation.

The type assigned to each lifted variable is inferred from its surrounding
context using the `SemanticModel` and `computeExprType`.
-/

namespace Strata
namespace Laurel

public section

private def emptyMd : Imperative.MetaData Core.Expression := #[]
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, emptyMd⟩
private def bareType (v : HighType) : HighTypeMd := ⟨v, emptyMd⟩

/-- State for the hole lifting pass. -/
structure HoleLiftState where
  counter : Nat := 0
  /-- Semantic model for type inference. -/
  model : SemanticModel
  /-- Output type of the procedure currently being processed (for Return). -/
  currentOutputType : HighTypeMd := ⟨.Top, #[]⟩

private abbrev HoleLiftM := StateM HoleLiftState

private def freshHoleVar : HoleLiftM Identifier := do
  let n := (← get).counter
  modify fun s => { s with counter := n + 1 }
  return s!"$hole_{n}"

private def defaultHoleType : HighTypeMd := bareType .Top

/-- Compute the type of an expression using the semantic model. -/
private def exprType (expr : StmtExprMd) : HoleLiftM HighTypeMd := do
  return computeExprType (← get).model expr

/-- For a comparison operator, infer the argument type from the first
    non-hole sibling whose type can be determined via the semantic model. -/
private def inferComparisonArgType (args : List StmtExprMd) : HoleLiftM HighTypeMd := do
  for a in args do
    match a.val with
    | .Hole => continue
    | _ => return ← exprType a
  return defaultHoleType

/-- Look up the input parameter types for a callee via the semantic model. -/
private def calleeParamTypes (callee : Identifier) : HoleLiftM (Option (List HighTypeMd)) := do
  match (← get).model.get callee with
  | .staticProcedure proc => return some (proc.inputs.map (·.type))
  | _ => return none

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

/-- Lift holes from a list of arguments where each position may have a different expected type. -/
private def liftHoleArgsTyped (args : List StmtExprMd) (types : List HighTypeMd) : HoleLiftM (List StmtExprMd × List StmtExprMd) := do
  let mut newArgs : List StmtExprMd := []
  let mut decls : List StmtExprMd := []
  let mut i := 0
  for a in args do
    let ty := types.getD i defaultHoleType
    let (a', ds) ← liftHoleExpr a ty
    newArgs := newArgs ++ [a']
    decls := decls ++ ds
    i := i + 1
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
      let argType ← match op with
        | .Eq | .Neq | .Lt | .Leq | .Gt | .Geq => inferComparisonArgType args
        | _ => pure expectedType
      let (newArgs, decls) ← liftHoleArgs args argType
      return (⟨.PrimitiveOp op newArgs, md⟩, decls)
  | .StaticCall callee args =>
      let (newArgs, decls) ← do
        match (← calleeParamTypes callee) with
        | some paramTypes => liftHoleArgsTyped args paramTypes
        | none => liftHoleArgs args defaultHoleType
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
      let (newArgs, decls) ← do
        match (← calleeParamTypes callee) with
        | some paramTypes => liftHoleArgsTyped args paramTypes
        | none => liftHoleArgs args defaultHoleType
      return ([⟨.StaticCall callee newArgs, md⟩], decls)
  | .Return (some retExpr) =>
      let retType := (← get).currentOutputType
      let (retExpr', decls) ← liftHoleExpr retExpr retType
      return ([⟨.Return (some retExpr'), md⟩], decls)
  | _ => return ([stmt], [])

/-- Process a list of statements, inlining hoisted declarations before each statement. -/
private def liftHoleStmtList (stmts : List StmtExprMd) : HoleLiftM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  for s in stmts do
    let (expanded, decls) ← liftHoleStmt s
    result := result ++ decls ++ expanded
  return result
end

private def liftHoleProcedure (proc : Procedure) : HoleLiftM Procedure := do
  let outputType := match proc.outputs with
    | [single] => single.type
    | _ => defaultHoleType
  modify fun s => { s with counter := 0, currentOutputType := outputType }
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
def liftHoles (model : SemanticModel) (program : Program) : Program :=
  let initState : HoleLiftState := {
    model := model
    currentOutputType := defaultHoleType
  }
  let (procs, _) := (program.staticProcedures.mapM liftHoleProcedure).run initState
  { program with staticProcedures := procs }

end -- public section
end Laurel
