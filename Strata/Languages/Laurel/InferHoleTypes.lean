/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Util.Statistics

/-!
# Hole Type Inference

Annotate each `.Hole` node with a type inferred from its surrounding context
using the `SemanticModel` and `computeExprType`. After this pass every `Hole`
carries `some ty` so that the hole elimination pass can generate correctly
typed uninterpreted functions.

Every node is handled by `inferExpr` with an `expectedType` parameter.
For statement positions the expected type is `TVoid`, except for the last
statement in a block which inherits the block's expected type, and for
`return` expressions which use the procedure's output type.
-/

namespace Strata
namespace Laurel

public section

private def bareType (v : HighType) : HighTypeMd := ⟨v, none⟩
private def voidType : HighTypeMd := bareType .TVoid
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

inductive InferHoleTypesStats where
  /-- Number of holes successfully annotated with an inferred type. -/
  | holesAnnotated
  /-- Number of holes left with `Unknown` type (context could not determine type). -/
  | holesLeftUnknown

#derive_prefixed_toString InferHoleTypesStats "InferHoleTypes"

structure InferHoleState where
  model : SemanticModel
  currentOutputType : HighTypeMd := ⟨.Unknown, none⟩
  statistics : Statistics := {}

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

/-- Traverse a block's statement list: all statements except the last get `TVoid`,
    the last statement gets `expectedType`. -/
private def inferBlockStmts (stmts : List StmtExprMd) (expectedType : HighTypeMd) : InferHoleM (List StmtExprMd) :=
  match stmts with
  | [] => return []
  | [last] => return [← inferExpr last expectedType]
  | head :: tail => return (← inferExpr head voidType) :: (← inferBlockStmts tail expectedType)

/-- Annotate every `.Hole` in an expression with its contextual type.
    Statement-position nodes should be called with `expectedType = voidType`,
    except where a more specific type is known (block tail, return value). -/
private def inferExpr (expr : StmtExprMd) (expectedType : HighTypeMd) : InferHoleM StmtExprMd := do
  let model := (← get).model
  match expr with
  | AstNode.mk val source =>
  match val with
  | .Hole det _ =>
      if expectedType.val == .Unknown then
        modify fun s => { s with statistics := s.statistics.increment s!"{InferHoleTypesStats.holesLeftUnknown}" }
        return expr
      else
        modify fun s => { s with statistics := s.statistics.increment s!"{InferHoleTypesStats.holesAnnotated}" }
        return ⟨.Hole det (some expectedType), source⟩
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
      return ⟨.PrimitiveOp op (← inferArgs args argType), source⟩
  | .StaticCall callee args =>
      let args' ← match calleeParamTypes model callee with
        | some paramTypes => inferArgsTyped args paramTypes
        | none => inferArgs args defaultHoleType
      return ⟨.StaticCall callee args', source⟩
  | .InstanceCall target callee args =>
      return ⟨.InstanceCall (← inferExpr target defaultHoleType) callee (← inferArgs args defaultHoleType), source⟩
  | .ReferenceEquals lhs rhs =>
      return ⟨.ReferenceEquals (← inferExpr lhs defaultHoleType) (← inferExpr rhs defaultHoleType), source⟩
  | .IfThenElse cond th el =>
      let el' ← match el with
        | some e => pure (some (← inferExpr e expectedType))
        | none => pure none
      return ⟨.IfThenElse (← inferExpr cond (bareType .TBool)) (← inferExpr th expectedType) el', source⟩
  | .Block stmts label =>
      return ⟨.Block (← inferBlockStmts stmts expectedType) label, source⟩
  | .Assign targets value =>
      let targetType := match targets with
        | target :: _ => match target.val with
          | .Local name => computeExprType model ⟨.Var (.Local name), target.source⟩
          | .Field _ fieldName => computeExprType model ⟨.Var (.Field ⟨.Hole, none⟩ fieldName), target.source⟩
          | .Declare param => param.type
        | _ => defaultHoleType
      return ⟨.Assign targets (← inferExpr value targetType), source⟩
  | .While cond invs dec body =>
      let dec' ← match dec with
        | some d => pure (some (← inferExpr d (bareType .TInt)))
        | none => pure none
      return ⟨.While (← inferExpr cond (bareType .TBool)) (← invs.mapM (inferExpr · (bareType .TBool))) dec' (← inferExpr body voidType), source⟩
  | .Assert ⟨condExpr, summary⟩ =>
      return ⟨.Assert { condition := ← inferExpr condExpr (bareType .TBool), summary }, source⟩
  | .Assume cond => return ⟨.Assume (← inferExpr cond (bareType .TBool)), source⟩
  | .Return (some retExpr) =>
      return ⟨.Return (some (← inferExpr retExpr (← get).currentOutputType)), source⟩
  | .Old v => return ⟨.Old (← inferExpr v expectedType), source⟩
  | .Fresh v => return ⟨.Fresh (← inferExpr v defaultHoleType), source⟩
  | .Assigned n => return ⟨.Assigned (← inferExpr n defaultHoleType), source⟩
  | .ProveBy v p => return ⟨.ProveBy (← inferExpr v expectedType) (← inferExpr p defaultHoleType), source⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← inferExpr f defaultHoleType), source⟩
  | .Quantifier mode p trigger b =>
      let trigger' ← match trigger with
        | some t => pure (some (← inferExpr t defaultHoleType))
        | none => pure none
      return ⟨.Quantifier mode p trigger' (← inferExpr b (bareType .TBool)), source⟩
  | _ => return expr
end

private def inferProcedure (proc : Procedure) : InferHoleM Procedure := do
  let outputType := match proc.outputs with
    | [single] => single.type
    | _ => { val := .Unknown, source := none }
  modify fun s => { s with currentOutputType := outputType }
  match proc.body with
  | .Transparent bodyExpr => return { proc with body := .Transparent (← inferExpr bodyExpr outputType) }
  | .Opaque postconds (some impl) modif =>
      return { proc with body := .Opaque postconds (some (← inferExpr impl outputType)) modif }
  | _ => return proc

/--
Annotate every `.Hole` in the program with a type inferred from context.
-/
def inferHoleTypes (model : SemanticModel) (program : Program) : Program × Statistics :=
  let initState : InferHoleState := { model := model }
  let (procs, finalState) := (program.staticProcedures.mapM inferProcedure).run initState
  ({ program with staticProcedures := procs }, finalState.statistics)

end -- public section
end Laurel
