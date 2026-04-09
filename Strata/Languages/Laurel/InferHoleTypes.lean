/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
public import Strata.Languages.Laurel.LaurelTypes

/-!
# Hole Type Inference

Annotate each `.Hole` node with a type inferred from its surrounding context
using the `SemanticModel` and `computeExprType`. After this pass every `Hole`
carries `some ty` so that the hole elimination pass can generate correctly
typed uninterpreted functions.
-/

namespace Strata
namespace Laurel

public section

private def bareType (v : HighType) : HighTypeMd := ⟨v, (#[] : Imperative.MetaData Core.Expression)⟩
private def defaultHoleType : HighTypeMd := bareType .Unknown

/-- Compute the expected type for an argument of a comparison operator
    by looking at the first non-hole sibling. -/
private def inferComparisonArgType (model : SemanticModel) (args : List StmtExprMd) : HighTypeMd :=
  args.findSome? (fun a => match a.val with | .Hole _ _ => none | _ => some (computeExprType model a))
    |>.getD defaultHoleType

/-- Get the expected type for each argument of a call from the callee's parameter list. -/
private def calleeParamTypes (model : SemanticModel) (callee : Identifier) : Option (List HighTypeMd) :=
  match model.get callee with
  | .staticProcedure proc => some (proc.inputs.map (·.type))
  | _ => none

structure InferHoleState where
  model : SemanticModel
  currentOutputType : HighTypeMd := ⟨.Unknown, #[]⟩

private abbrev InferHoleM := StateM InferHoleState

mutual
private def inferArgs (args : List StmtExprMd) (expectedType : HighTypeMd) : InferHoleM (List StmtExprMd) :=
  args.mapM (inferExpr · expectedType)

private def inferArgsTyped (args : List StmtExprMd) (types : List HighTypeMd) : InferHoleM (List StmtExprMd) := do
  let mut result : List StmtExprMd := []
  let mut i := 0
  for a in args do
    result := result ++ [← inferExpr a (types.getD i defaultHoleType)]
    i := i + 1
  return result

/-- Annotate every `.Hole` in an expression with its contextual type. -/
private def inferExpr (expr : StmtExprMd) (expectedType : HighTypeMd) : InferHoleM StmtExprMd := do
  let model := (← get).model
  match expr with
  | WithMetadata.mk val md =>
  match val with
  | .Hole det _ => return ⟨.Hole det (some expectedType), md⟩
  | .PrimitiveOp op args =>
      let argType := match op with
        | .Eq | .Neq | .Lt | .Leq | .Gt | .Geq => inferComparisonArgType model args
        | _ =>
          -- Use computeExprType on the whole expression to get the result type,
          -- which equals the argument type for arithmetic/logic/string ops.
          -- Fall back to expectedType if computeExprType can't determine it
          -- (e.g. when the first arg is a Hole).
          let computed := computeExprType model expr
          match computed.val with
          | .TCore _ | .Unknown => expectedType
          | _ => computed
      return ⟨.PrimitiveOp op (← inferArgs args argType), md⟩
  | .StaticCall callee args =>
      let args' ← match calleeParamTypes model callee with
        | some paramTypes => inferArgsTyped args paramTypes
        | none => inferArgs args defaultHoleType
      return ⟨.StaticCall callee args', md⟩
  | .InstanceCall target callee args =>
      return ⟨.InstanceCall (← inferExpr target defaultHoleType) callee (← inferArgs args defaultHoleType), md⟩
  | .ReferenceEquals lhs rhs =>
      return ⟨.ReferenceEquals (← inferExpr lhs defaultHoleType) (← inferExpr rhs defaultHoleType), md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with
        | some e => pure (some (← inferExpr e expectedType))
        | none => pure none
      return ⟨.IfThenElse (← inferExpr cond (bareType .TBool)) (← inferExpr th expectedType) el', md⟩
  | .Block stmts label => return ⟨.Block (← inferStmtList stmts) label, md⟩
  | .Assign targets value => return ⟨.Assign targets (← inferExpr value defaultHoleType), md⟩
  | .LocalVariable name ty init =>
      match init with
      | some initExpr => return ⟨.LocalVariable name ty (some (← inferExpr initExpr ty)), md⟩
      | none => return expr
  | .Old v => return ⟨.Old (← inferExpr v expectedType), md⟩
  | .Fresh v => return ⟨.Fresh (← inferExpr v defaultHoleType), md⟩
  | .Assigned n => return ⟨.Assigned (← inferExpr n defaultHoleType), md⟩
  | .ProveBy v p => return ⟨.ProveBy (← inferExpr v expectedType) (← inferExpr p defaultHoleType), md⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← inferExpr f defaultHoleType), md⟩
  | .Forall p trigger b =>
      let trigger' ← match trigger with
        | some t => pure (some (← inferExpr t defaultHoleType))
        | none => pure none
      return ⟨.Forall p trigger' (← inferExpr b (bareType .TBool)), md⟩
  | .Exists p trigger b =>
      let trigger' ← match trigger with
        | some t => pure (some (← inferExpr t defaultHoleType))
        | none => pure none
      return ⟨.Exists p trigger' (← inferExpr b (bareType .TBool)), md⟩
  | _ => return expr

private def inferStmt (stmt : StmtExprMd) : InferHoleM StmtExprMd := do
  let model := (← get).model
  match stmt with
  | WithMetadata.mk val md =>
  match val with
  | .LocalVariable name ty (some initExpr) =>
      return ⟨.LocalVariable name ty (some (← inferExpr initExpr ty)), md⟩
  | .Assign targets value => return ⟨.Assign targets (← inferExpr value defaultHoleType), md⟩
  | .Block stmts label => return ⟨.Block (← inferStmtList stmts) label, md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with
        | some e => pure (some (← inferStmt e))
        | none => pure none
      return ⟨.IfThenElse (← inferExpr cond (bareType .TBool)) (← inferStmt th) el', md⟩
  | .While cond invs dec body =>
      let dec' ← match dec with
        | some d => pure (some (← inferExpr d (bareType .TInt)))
        | none => pure none
      return ⟨.While (← inferExpr cond (bareType .TBool)) (← invs.mapM (inferExpr · (bareType .TBool))) dec' (← inferStmt body), md⟩
  | .Assert cond => return ⟨.Assert (← inferExpr cond (bareType .TBool)), md⟩
  | .Assume cond => return ⟨.Assume (← inferExpr cond (bareType .TBool)), md⟩
  | .StaticCall callee args =>
      let args' ← match calleeParamTypes model callee with
        | some paramTypes => inferArgsTyped args paramTypes
        | none => inferArgs args defaultHoleType
      return ⟨.StaticCall callee args', md⟩
  | .Return (some retExpr) =>
      return ⟨.Return (some (← inferExpr retExpr (← get).currentOutputType)), md⟩
  | .Hole det _ => return ⟨.Hole det (some (← get).currentOutputType), md⟩
  | _ => return stmt

private def inferStmtList (stmts : List StmtExprMd) : InferHoleM (List StmtExprMd) :=
  stmts.mapM inferStmt
end

private def inferProcedure (proc : Procedure) : InferHoleM Procedure := do
  let outputType := match proc.outputs with
    | [single] => single.type
    | _ => defaultHoleType
  modify fun s => { s with currentOutputType := outputType }
  match proc.body with
  | .Transparent bodyExpr => return { proc with body := .Transparent (← inferStmt bodyExpr) }
  | .Opaque postconds (some impl) modif =>
      return { proc with body := .Opaque postconds (some (← inferStmt impl)) modif }
  | _ => return proc

/--
Annotate every `.Hole` in the program with a type inferred from context.
-/
def inferHoleTypes (model : SemanticModel) (program : Program) : Program :=
  let initState : InferHoleState := { model := model }
  let (procs, _) := (program.staticProcedures.mapM inferProcedure).run initState
  { program with staticProcedures := procs }

end -- public section
end Laurel
