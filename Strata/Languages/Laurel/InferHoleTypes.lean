/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Util.Statistics
public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.EliminateDeterministicHoles
import Strata.Util.Tactics

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

## TODO: make this pass obsolete by improving `Resolution`

This pass exists only because `Resolution` does not currently assign a concrete
type to every hole. It should: resolution already type-checks the whole program
bidirectionally, so it is the natural place to type holes, and doing so there
would make this pass redundant and let us delete it.

The missing piece is in how `Resolution` *synthesizes* the type of a hole.
Today a hole in synth position synthesizes to `Unknown`, and that `Unknown` is
discarded rather than being unified with the type its context later imposes.
Instead, synthesizing a hole should return a fresh **type variable** that is
recorded on the hole node, so that when the surrounding expression is checked
(e.g. via `checkSubtype`, or by overload selection in `Synth.staticCall`) the
variable is solved to the concrete type and that solution is written back onto
the hole.
With that, holes such as `1 + <?>`, `<?> > 0`, or a call argument would be
typed during resolution exactly as this pass types them now, and `Resolution`
would assign a type to every hole on its own.
-/

namespace Strata
namespace Laurel

public section

/-- Compute the expected type for an argument of a comparison operator
    by looking at the first non-hole sibling. -/
private def inferComparisonArgType (model : SemanticModel) (args : List StmtExprMd) (source: FileRange) : HighTypeMd :=
  args.findSome? (fun a => match a.val with | .Hole _ _ => none | _ => some (computeExprType model a))
    |>.getD ⟨ .TInt, source ⟩ -- use Int as a default type for comparisons where both operands are holes

/-- Get the expected type for each argument of a call from the callee's parameter list.

    Auto-generated datatype destructors (`TypeName..fieldName[!]`) and testers
    (`TypeName..isCtor`) are unary, taking the datatype itself as their single
    input. Their `ResolvedNode` (`.datatypeDestructor` / `.datatypeConstructor`)
    carries the resolved type Identifier (with its `uniqueId`), so we can
    construct the input `HighType` directly without falling back to textual
    decoding of the override name. -/
private def calleeParamTypes (model : SemanticModel) (callee : Identifier) : Option (List HighTypeMd) :=
  -- `$eq`/`$neq` are declared `external` with a placeholder `int → int → bool`
  -- signature, because polymorphic equality has no monomorphic Laurel type. Those
  -- `int`s describe nothing about the operands, so typing a hole from them would
  -- make `<?> == "hello"` infer `int` and only fail once a later pass re-resolves
  -- the program — surfacing a plain type error as a `StrataBug`. Fall through to
  -- `unresolvedOperatorArgType`, which reads the first non-hole sibling instead.
  if callee.text == Operation.Eq.procName || callee.text == Operation.Neq.procName then
    none
  else
  match model.get callee with
  | .staticProcedure proc => some (proc.inputs.map (·.type))
  | .datatypeConstructor typeName _
  | .datatypeDestructor typeName _ =>
      some [⟨.UserDefined typeName, callee.source⟩]
  | _ => none

/-- Expected type for the arguments of a `StaticCall` whose callee did not
    resolve to a single definition.

    This is the operator case. `x + y` is a `StaticCall` to the overloaded
    wrapper `$add`, and overload selection needs the argument types to pick
    between the `int` and `real` overloads — so when *every* argument is a hole
    (`<?> + <?>`, `-<?>`) there is nothing to select on, the callee keeps no
    `uniqueId`, and `calleeParamTypes` yields nothing. The operand type is still
    determined by the context: `var x: int := -<?>` says the operand is an `int`.

    So fall back to the type the context imposes, mirroring what the dedicated
    operator arm did before operators became calls:

    - comparisons yield `bool` regardless of their operands, so `expectedType`
      says nothing about the arguments; use the first non-hole sibling's type
      instead (`inferComparisonArgType`, which defaults to `int`);
    - for the other operators the result type is the operand type, so
      `expectedType` *is* the argument type.

    A non-operator callee that failed to resolve is a genuine error reported
    elsewhere; keep the previous `Unknown` there rather than inventing a type. -/
private def unresolvedOperatorArgType (model : SemanticModel) (callee : Identifier)
    (args : List StmtExprMd) (expectedType : HighTypeMd) (source : FileRange) : HighTypeMd :=
  match Operation.ofProcName? callee.text with
  | some op =>
    match op with
    | .Eq | .Neq | .Lt | .Leq | .Gt | .Geq => inferComparisonArgType model args source
    | _ => expectedType
  | none => ⟨ .Unknown, source ⟩

/-- Recover the expected receiver type for a resolved field reference. -/
private def fieldOwnerType (model : SemanticModel) (fieldName : Identifier)
    (source : FileRange) : HighTypeMd :=
  match model.get? fieldName with
  | some (.field ownerName _) => ⟨.UserDefined ownerName, source⟩
  | _ => ⟨.Unknown, source⟩

inductive InferHoleTypesStats where
  /-- Number of holes successfully annotated with an inferred type. -/
  | holesAnnotated
  /-- Number of holes left with `Unknown` type (context could not determine type). -/
  | holesLeftUnknown

#derive_prefixed_toString InferHoleTypesStats "InferHoleTypes"

structure InferHoleState where
  model : SemanticModel
  statistics : Statistics := {}
  diagnostics : List Message := []

private abbrev InferHoleM := StateM InferHoleState

mutual
private def inferArgs (args : List StmtExprMd) (expectedType : HighTypeMd)
    (outputType : HighTypeMd) : InferHoleM (List StmtExprMd) :=
  args.mapM (inferExpr · expectedType outputType)
  termination_by sizeOf args

private def inferArgsTyped (args : List StmtExprMd) (types : List HighTypeMd) (source : FileRange)
    (outputType : HighTypeMd) : InferHoleM (List StmtExprMd) := do
  if args.length != types.length then
    return ← args.mapM (inferExpr · ⟨.Unknown, source⟩ outputType)
  let mut result : List StmtExprMd := []
  let mut i := 0
  for a in args do
    result := result ++ [← inferExpr a types[i]! outputType]
    i := i + 1
  return result
  termination_by sizeOf args

/-- Traverse a block's statement list: all statements except the last get `TVoid`,
    the last statement gets `expectedType`. -/
private def inferBlockStmts (stmts : List StmtExprMd) (expectedType : HighTypeMd)
    (outputType : HighTypeMd) : InferHoleM (List StmtExprMd) :=
  match stmts with
  | [] => return []
  | [last] => return [← inferExpr last expectedType outputType]
  | head :: tail =>
      return (← inferExpr head ⟨ .TVoid, head.source⟩ outputType)
               :: (← inferBlockStmts tail expectedType outputType)
  termination_by sizeOf stmts

/-- Annotate every `.Hole` in an expression with its contextual type.
    Statement-position nodes should be called with `expectedType = voidType`,
    except where a more specific type is known (block tail, return value).
    `outputType` is the enclosing procedure's return type, used for `.Return`. -/
private def inferExpr (expr : StmtExprMd) (expectedType : HighTypeMd)
    (outputType : HighTypeMd) : InferHoleM StmtExprMd := do
  let model := (← get).model
  match expr with
  | AstNode.mk val source =>
  match val with
  | .Hole det _ =>
      -- A hole with no inferable context (expectedType `.Unknown`, e.g. a bare `<?>` proc body) is a
      -- genuine "could not infer type" error, so the diagnostic fires here. The sound gradual escape
      -- for an unmodeled field-write RHS hole is handled in the `.Assign` arm (which knows the target
      -- is Unknown-typed), so such a hole never reaches this arm.
      if expectedType.val == .Unknown then
        modify fun s => { s with
          statistics := s.statistics.increment s!"{InferHoleTypesStats.holesLeftUnknown}"
          diagnostics := s.diagnostics ++ [diagnosticFromSource source "could not infer type"]
        }
        return expr
      else
        modify fun s => { s with statistics := s.statistics.increment s!"{InferHoleTypesStats.holesAnnotated}" }
        return ⟨.Hole det (some expectedType), source⟩
  | .StaticCall callee args =>
      let args' ← match calleeParamTypes model callee with
        | some paramTypes => inferArgsTyped args paramTypes source outputType
        | none =>
          inferArgs args (unresolvedOperatorArgType model callee args expectedType source) outputType
      return ⟨.StaticCall callee args', source⟩
  | .InstanceCall target callee args =>
      return ⟨.InstanceCall (← inferExpr target ⟨ .Unknown, source ⟩ outputType) callee (← inferArgs args ⟨ .Unknown, source ⟩ outputType), source⟩
  | .ReferenceEquals lhs rhs =>
      let lhsType := computeExprType model lhs
      let rhsType := computeExprType model rhs
      let lhsExpected := if lhsType.val == .Unknown then rhsType else lhsType
      let rhsExpected := if rhsType.val == .Unknown then lhsType else rhsType
      return ⟨.ReferenceEquals (← inferExpr lhs lhsExpected outputType) (← inferExpr rhs rhsExpected outputType), source⟩
  | .AsType target targetType =>
      return ⟨.AsType (← inferExpr target targetType outputType) targetType, source⟩
  | .IsType target targetType =>
      return ⟨.IsType (← inferExpr target targetType outputType) targetType, source⟩
  | .IfThenElse cond th el =>
      let el' ← match el with
        | some e => pure (some (← inferExpr e expectedType outputType))
        | none => pure none
      return ⟨.IfThenElse (← inferExpr cond ⟨ .TBool, source ⟩ outputType) (← inferExpr th expectedType outputType) el', source⟩
  | .Block stmts label =>
      return ⟨.Block (← inferBlockStmts stmts expectedType outputType) label, source⟩
  | .Assign targets value =>
      let targetType := match targets with
        | target :: _ => match target.val with
          | .Local name => computeExprType model ⟨.Var (.Local name), target.source⟩
          | .Field _ fieldName => computeExprType model ⟨.Var (.Field ⟨.Hole, target.source⟩ fieldName), target.source⟩
          | .Declare param => param.type.getD ⟨ .Unknown, target.source ⟩
        | _ => ⟨ .Unknown, source ⟩
      -- An unmodeled field-write target yields `targetType = .Unknown`. The RHS of an assignment whose
      -- target type is Unknown is a sound gradual hole: annotate it `.Unknown` directly so hole
      -- elimination emits an uninterpreted fn over `Unknown`, rather than treating it as a contextless
      -- hole that "could not infer type". A contextless hole is not an assign RHS, so it still errors.
      let value' ← match value.val, targetType.val with
        | .Hole det _, .Unknown => do
            modify fun s => { s with
              statistics := s.statistics.increment s!"{InferHoleTypesStats.holesLeftUnknown}" }
            pure (⟨.Hole det (some ⟨.Unknown, value.source⟩), value.source⟩ : StmtExprMd)
        | _, _ => inferExpr value targetType outputType
      let targets' ← targets.mapM fun target =>
        match _targetEq : target.val with
        | .Field receiver fieldName =>
            return ⟨.Field
              (← inferExpr receiver (fieldOwnerType model fieldName receiver.source) outputType)
              fieldName, target.source⟩
        | .Local _ | .Declare _ => pure target
      return ⟨.Assign targets' value', source⟩
  | .Var (.Field receiver fieldName) =>
      return ⟨.Var (.Field
        (← inferExpr receiver (fieldOwnerType model fieldName receiver.source) outputType)
        fieldName), source⟩
  | .IncrDecr mode op target =>
      let target' ← match _targetEq : target.val with
        | .Field receiver fieldName =>
            pure ⟨.Field
              (← inferExpr receiver (fieldOwnerType model fieldName receiver.source) outputType)
              fieldName, target.source⟩
        | .Local _ | .Declare _ => pure target
      return ⟨.IncrDecr mode op target', source⟩
  | .CompoundAssign op target rhs =>
      let targetType := match target.val with
        | .Local name => computeExprType model ⟨.Var (.Local name), target.source⟩
        | .Field _ fieldName => computeExprType model ⟨.Var (.Field ⟨.Hole, target.source⟩ fieldName), target.source⟩
        | .Declare param => param.type.getD ⟨ .Unknown, target.source ⟩
      let target' ← match _targetEq : target.val with
        | .Field receiver fieldName =>
            pure ⟨.Field
              (← inferExpr receiver (fieldOwnerType model fieldName receiver.source) outputType)
              fieldName, target.source⟩
        | .Local _ | .Declare _ => pure target
      return ⟨.CompoundAssign op target' (← inferExpr rhs targetType outputType), source⟩
  | .PureFieldUpdate target fieldName newValue =>
      let valueType := computeExprType model ⟨.Var (.Field target fieldName), source⟩
      return ⟨.PureFieldUpdate
        (← inferExpr target (fieldOwnerType model fieldName target.source) outputType)
        fieldName (← inferExpr newValue valueType outputType), source⟩
  | .While cond invs dec body postTest =>
      let dec' ← match dec with
        | some d => pure (some (← inferExpr d (⟨ .TInt, source ⟩) outputType))
        | none => pure none
      return ⟨.While (← inferExpr cond ⟨ .TBool, source ⟩ outputType) (← invs.mapM (inferExpr · ⟨ .TBool, source ⟩ outputType)) dec' (← inferExpr body ⟨ .TVoid, source⟩ outputType) postTest, source⟩
  | .Assert condExpr summary =>
      return ⟨.Assert (← inferExpr condExpr ⟨ .TBool, source ⟩ outputType) summary, source⟩
  | .Assume cond =>
      return ⟨.Assume (← inferExpr cond ⟨ .TBool, source ⟩ outputType), source⟩
  | .Throw v =>
      return ⟨.Throw (← inferExpr v ⟨ .Unknown, source ⟩ outputType), source⟩
  -- `Try` is returned unchanged rather than recursed into: descending through the
  -- catch-clause list would force this mutual block from structural onto well-founded
  -- recursion. Consequence: holes inside `try`/`catch`/`finally` arms are not
  -- type-inferred yet. Revisit if holes in those positions need inference.
  | .Try .. => return expr
  | .Return (some retExpr) =>
      return ⟨.Return (some (← inferExpr retExpr outputType outputType)), source⟩
  | .Old v => return ⟨.Old (← inferExpr v expectedType outputType), source⟩
  | .Fresh v => return ⟨.Fresh (← inferExpr v ⟨ .Unknown, source ⟩ outputType), source⟩
  | .Assigned n => return ⟨.Assigned (← inferExpr n ⟨ .Unknown, source ⟩ outputType), source⟩
  | .ProveBy v p => return ⟨.ProveBy (← inferExpr v expectedType outputType) (← inferExpr p ⟨ .Unknown, source ⟩ outputType), source⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← inferExpr f ⟨ .Unknown, source ⟩ outputType), source⟩
  | .Quantifier mode p trigger b =>
      let trigger' ← match trigger with
        | some t => pure (some (← inferExpr t ⟨ .Unknown, source ⟩ outputType))
        | none => pure none
      return ⟨.Quantifier mode p trigger' (← inferExpr b ⟨ .TBool, source ⟩ outputType), source⟩
  | .Exit _ | .Return none | .LiteralInt _ | .LiteralBool _ | .LiteralString _
  | .LiteralDecimal _ | .LiteralBv _ _ | .Var (.Local _) | .Var (.Declare _)
  | .New _ | .This | .Abstract | .All => return expr
  termination_by sizeOf expr
  decreasing_by
    all_goals simp_wf
    all_goals (try have := AstNode.sizeOf_val_lt expr)
    all_goals (try term_by_mem)
    all_goals (try (cases expr; simp_all; omega))
    all_goals (try (
      have hfield := Variable.sizeOf_field_target_lt_of_eq (by assumption)
      omega))
    all_goals (try (
      have hmember := List.sizeOf_lt_of_mem ‹_›
      have hfield := Variable.sizeOf_field_target_lt_of_eq (by assumption)
      omega))
end

private def inferProcedure (proc : Procedure) : InferHoleM Procedure := do
  let outputType := match proc.outputs with
    | [single] => single.type
    | _ => { val := .Unknown, source := proc.name.source }
  let inferCondition (expr : StmtExprMd) := inferExpr expr ⟨.TBool, expr.source⟩ outputType
  let inferValue (expr : StmtExprMd) := inferExpr expr ⟨.Unknown, expr.source⟩ outputType
  let body ← match proc.body with
    | .Transparent bodyExpr =>
        pure (.Transparent (← inferExpr bodyExpr outputType outputType))
    | .Opaque postconds impl modifies =>
        pure (.Opaque
          (← postconds.mapM (·.mapM inferCondition))
          (← impl.mapM (inferExpr · outputType outputType))
          (← modifies.mapM (fun g => do
            pure { g with targets := ← g.targets.mapM inferValue,
                          guard := ← g.guard.mapM inferValue })))
    | .Abstract postconds =>
        pure (.Abstract (← postconds.mapM (·.mapM inferCondition)))
    | .External => pure .External
  mapProcedureSpecificationsWithM inferCondition inferValue { proc with body }

/--
Annotate every `.Hole` in the program with a type inferred from context.
Returns the updated program and any diagnostics (e.g. holes whose type could not be inferred).
-/
def inferHoleTypes (model : SemanticModel) (program : Program) : Program × List Message × Statistics :=
  let initState : InferHoleState := { model := model }
  let (program, finalState) := (mapProgramProceduresM inferProcedure program).run initState
  (program, finalState.diagnostics, finalState.statistics)

end -- public section

/-- Pipeline pass: infer hole types. -/
public def inferHoleTypesPass : LoweringPass where
  name := "InferHoleTypes"
  documentation := "Annotates every verification hole (`.Hole`) in the program with a type inferred from context. This type information is needed by subsequent passes that replace holes with uninterpreted functions or nondeterministic values. TODO: this pass should be removed by improving `Resolution` to assign a concrete type to every hole during type checking (see the module doc for the type-variable approach), making this pass obsolete."
  run := fun _ p m =>
    let (p', diags, stats) := inferHoleTypes m p
    (p', diags, stats)
  comesBefore := [
      ⟨ eliminateDeterministicHolesPass.meta, "eliminating deterministic holes relies on knowing the type of holes"⟩]

end Laurel
