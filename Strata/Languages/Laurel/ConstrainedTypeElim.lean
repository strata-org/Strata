/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Util.Tactics

/-!
# Constrained Type Elimination

A Laurel-to-Laurel pass that eliminates constrained types by:
1. Generating a constraint function per constrained type (e.g. `nat$constraint(x: int): bool`)
2. Adding `requires constraintFunc(param)` for constrained-typed inputs
3. Adding `ensures constraintFunc(result)` for constrained-typed outputs
   - Skipped for `isFunctional` procedures since the Laurel translator does not yet support
     function postconditions. Constrained return types on functions are not checked.
4. Inserting `assert constraintFunc(var)` for local variable init and reassignment
5. Assuming the constraint for uninitialized constrained-typed variables (havoc + assume)
6. Adding a synthetic witness-validation procedure per constrained type
7. Injecting constraint function calls into quantifier bodies (`forall` → `implies`, `exists` → `and`)
8. Resolving all constrained type references to their base types
-/

namespace Strata.Laurel

open Strata

abbrev ConstrainedTypeMap := Std.HashMap String ConstrainedType
/-- Map from variable name to its constrained HighType (e.g. UserDefined "nat") -/
abbrev PredVarMap := Std.HashMap String HighType

def buildConstrainedTypeMap (types : List TypeDefinition) : ConstrainedTypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Constrained ct => m.insert ct.name.text ct | _ => m

partial def resolveBaseType (ptMap : ConstrainedTypeMap) (ty : HighType) : HighType :=
  match ty with
  | .UserDefined name => match ptMap.get? name.text with
    | some ct => resolveBaseType ptMap ct.base.val | none => ty
  | .Applied ctor args =>
    .Applied ctor (args.map fun a => ⟨resolveBaseType ptMap a.val, a.source⟩)
  | _ => ty

def resolveType (ptMap : ConstrainedTypeMap) (ty : HighTypeMd) : HighTypeMd :=
  ⟨resolveBaseType ptMap ty.val, ty.source⟩

def isConstrainedType (ptMap : ConstrainedTypeMap) (ty : HighType) : Bool :=
  match ty with | .UserDefined name => ptMap.contains name.text | _ => false

/-- Build a call to the constraint function for a constrained type, or `none` if not constrained -/
def constraintCallFor (ptMap : ConstrainedTypeMap) (ty : HighType)
    (varName : Identifier) (src : Option FileRange := none) : Option StmtExprMd :=
  match ty with
  | .UserDefined name => if ptMap.contains name.text then
      some ⟨.StaticCall (mkId s!"{name.text}$constraint") [⟨.Var (.Local varName), src⟩], src⟩
    else none
  | _ => none

/-- Generate a constraint function for a constrained type.
    For nested types, the function calls the parent's constraint function. -/
def mkConstraintFunc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let baseType := resolveType ptMap ct.base
  let bodyExpr := match ct.base.val with
    | .UserDefined parent =>
      if ptMap.contains parent.text then
        let paramId := { ct.valueName with uniqueId := none }
        let paramRef : StmtExprMd :=
          { val := .Var (.Local paramId), source := none }
        let parentCall : StmtExprMd :=
          { val := .StaticCall (mkId s!"{parent.text}$constraint") [paramRef], source := none }
        { val := .PrimitiveOp .And [ct.constraint, parentCall], source := none }
      else ct.constraint
    | _ => ct.constraint
  { name := mkId s!"{ct.name.text}$constraint"
    inputs := [{ name := ct.valueName, type := baseType }]
    outputs := [{ name := mkId "result", type := { val := .TBool, source := none } }]
    body := .Transparent { val := .Block [bodyExpr] none, source := none }
    isFunctional := true
    decreases := none
    preconditions := [] }

private def wrap (stmts : List StmtExprMd) (src : Option FileRange)
    : StmtExprMd :=
  match stmts with | [s] => s | ss => ⟨.Block ss none, src⟩

def resolveVariable (ptMap : ConstrainedTypeMap) (v : VariableMd) : VariableMd :=
  match v.val with
  | .Declare param => ⟨.Declare { param with type := resolveType ptMap param.type }, v.source⟩
  | _ => v

/-- Resolve constrained types in type positions and inject constraint calls into quantifier bodies.
    Recursion into StmtExprMd children is handled by `mapStmtExpr`. -/
def resolveExprNode (ptMap : ConstrainedTypeMap) (expr : StmtExprMd) : StmtExprMd :=
  let source := expr.source

  match expr.val with
  | .Assign targets value =>
    ⟨.Assign (targets.map (resolveVariable ptMap)) value, source⟩
  | .Var (.Declare param) =>
    ⟨.Var (.Declare { param with type := resolveType ptMap param.type }), source⟩
  | .Quantifier mode param trigger body =>
    let param' := { param with type := resolveType ptMap param.type }
    -- With bottom-up traversal, `body` is already recursed into. The newly
    -- created `PrimitiveOp` won't be visited again, which is safe because
    -- `c` (from `constraintCallFor`) is a StaticCall with Identifier leaves
    -- that don't need further resolution.
    let combiner := match mode with | .Forall => Operation.Implies | .Exists => Operation.And
    let injected := match constraintCallFor ptMap param.type.val param.name (src := source) with
      | some c => ⟨.PrimitiveOp combiner [c, body], source⟩
      | none => body
    ⟨.Quantifier mode param' trigger injected, source⟩
  | .AsType t ty => ⟨.AsType t (resolveType ptMap ty), source⟩
  | .IsType t ty => ⟨.IsType t (resolveType ptMap ty), source⟩
  | _ => expr

abbrev ElimM := StateM PredVarMap

private def inScope (action : ElimM α) : ElimM α := do
  let saved ← get
  let result ← action
  set saved
  return result

/-- If `target` is an assignment target of a constrained type, return the
    constrained type's name together with an expression that reads the target
    back. The declared type is taken from the `Declare` parameter or, for
    `Local`/`Field` targets, from the semantic model. -/
def constrainedTargetReadback (ptMap : ConstrainedTypeMap) (model : SemanticModel)
    (target : VariableMd) : Option (Identifier × StmtExprMd) :=
  let src := target.source
  let check (ty : HighType) (ref : StmtExprMd) : Option (Identifier × StmtExprMd) :=
    match ty with
    | .UserDefined name => if ptMap.contains name.text then some (name, ref) else none
    | _ => none
  match target.val with
  | .Local name => check (model.get name).getType.val ⟨.Var (.Local name), src⟩
  | .Declare param => check param.type.val ⟨.Var (.Local param.name), src⟩
  | .Field tgt fieldName => check (model.get fieldName).getType.val ⟨.Var (.Field tgt fieldName), src⟩

/-- Wrap an assignment that appears in *expression* position so that the
    constraint of any constrained-typed target is checked.

    For `x := v` where `x : T` is constrained, produces the block expression
    `{ x := v; assert T$constraint(x); x }`, whose value is the assigned value.
    The constraint is asserted on a read-back of the target (after the
    assignment) rather than on the value `v`, so `v` is evaluated exactly once
    and the check is semantics-preserving.

    `elimStmt` already handles assignments that appear as statements; this covers
    assignments nested inside expressions (e.g. `y := (x := -1) + 1`), which are
    only hoisted to statement level by the later `LiftExpressionAssignments`
    pass. That pass preserves the order of side-effecting statements within an
    expression-position block, so the assertion stays after the assignment.
    Non-`Assign` nodes are returned unchanged. -/
def wrapAssignNode (ptMap : ConstrainedTypeMap) (model : SemanticModel)
    (node : StmtExprMd) : StmtExprMd :=
  match node.val with
  | .Assign targets _value =>
    match targets.filterMap (constrainedTargetReadback ptMap model) with
    | [] => node
    | infos@((_, resultRef) :: _) =>
      let src := node.source
      let asserts : List StmtExprMd := infos.map fun (name, ref) =>
        ⟨.Assert { condition := ⟨.StaticCall (mkId s!"{name.text}$constraint") [ref], src⟩ }, src⟩
      ⟨.Block ([node] ++ asserts ++ [resultRef]) none, src⟩
  | _ => node

/-- Insert constraint assertions for every assignment to a constrained-typed
    target that appears within an expression. A no-op on expressions that
    contain no such assignment. -/
def wrapExprAssigns (ptMap : ConstrainedTypeMap) (model : SemanticModel)
    (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (wrapAssignNode ptMap model) expr

def elimStmt (ptMap : ConstrainedTypeMap) (model : SemanticModel)
    (stmt : StmtExprMd) : ElimM (List StmtExprMd) := do
  let source := stmt.source

  match _h : stmt.val with
  | .Var (.Declare param) =>
    let callOpt := constraintCallFor ptMap param.type.val param.name (src := source)
    if callOpt.isSome then modify fun pv => pv.insert param.name.text param.type.val
    let check := match callOpt with
      | some c => [⟨.Assume c, source⟩]
      | none => []
    pure ([stmt] ++ check)

  | .Assign targets value =>
    -- Wrap any assignments nested in the value expression (expression-position
    -- assignments) so their constrained-type constraints are checked too.
    let value := wrapExprAssigns ptMap model value
    let stmt' : StmtExprMd := ⟨.Assign targets value, source⟩
    -- Handle Declare targets for constrained type elimination
    let declareChecks ← targets.foldlM (init := ([] : List StmtExprMd)) fun acc target =>
      match target.val with
      | .Declare param => do
        let callOpt := constraintCallFor ptMap param.type.val param.name (src := source)
        if callOpt.isSome then modify fun pv => pv.insert param.name.text param.type.val
        pure (acc ++ callOpt.toList.map fun c => ⟨.Assert { condition := c }, source⟩)
      | .Local name => do
        match (← get).get? name.text with
        | some ty =>
          let assert := (constraintCallFor ptMap ty name (src := source)).toList.map
            fun c => ⟨.Assert { condition := c }, source⟩
          pure (acc ++ assert)
        | none => pure acc
      | .Field _fieldTarget fieldName => do
        -- Writing to a constrained-typed composite field: assert the
        -- constraint holds for the value being stored. The field's declared
        -- type comes from the semantic model. (When this pass ran after
        -- HeapParameterization, this check was produced via the `Declare`
        -- temporary that lowering introduced; running first, we must emit it
        -- directly from the field write, asserting on the assigned value.)
        match (model.get fieldName).getType.val with
        | .UserDefined name =>
          if ptMap.contains name.text then
            let c : StmtExprMd := ⟨.StaticCall (mkId s!"{name.text}$constraint") [value], source⟩
            pure (acc ++ [⟨.Assert { condition := c }, source⟩])
          else pure acc
        | _ => pure acc
    pure ([stmt'] ++ declareChecks)

  | .Block stmts sep =>
    let stmtss ← inScope (stmts.mapM (elimStmt ptMap model))
    pure [⟨.Block stmtss.flatten sep, source⟩]

  | .IfThenElse cond thenBr (some elseBr) =>
    let cond := wrapExprAssigns ptMap model cond
    let thenSs ← inScope (elimStmt ptMap model thenBr)
    let elseSs ← inScope (elimStmt ptMap model elseBr)
    pure [⟨.IfThenElse cond (wrap thenSs source) (some (wrap elseSs source)), source⟩]
  | .IfThenElse cond thenBr none =>
    let cond := wrapExprAssigns ptMap model cond
    let thenSs ← inScope (elimStmt ptMap model thenBr)
    pure [⟨.IfThenElse cond (wrap thenSs source) none, source⟩]

  | .While cond inv dec body =>
    let cond := wrapExprAssigns ptMap model cond
    let bodySs ← inScope (elimStmt ptMap model body)
    pure [⟨.While cond inv dec (wrap bodySs source), source⟩]

  | _ => pure [stmt]
termination_by sizeOf stmt
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt stmt)
  all_goals (try term_by_mem)
  all_goals omega

def elimProc (ptMap : ConstrainedTypeMap) (model : SemanticModel) (proc : Procedure) : Procedure :=
  let inputRequires : List Condition := proc.inputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name (src := p.type.source)).map
      fun c => { condition := c }
  let outputEnsures : List Condition := if proc.isFunctional then [] else proc.outputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name (src := p.type.source)).map
      fun c => { condition := ⟨c.val, p.type.source⟩ }
  let initVars : PredVarMap := proc.inputs.foldl (init := {}) fun s p =>
    if isConstrainedType ptMap p.type.val then s.insert p.name.text p.type.val else s
  let body' := match proc.body with
  | .Transparent bodyExpr =>
    let (stmts, _) := (elimStmt ptMap model bodyExpr).run initVars
    let body := wrap stmts bodyExpr.source
    if outputEnsures.isEmpty then .Transparent body
    else
      let retBody := if proc.isFunctional then ⟨.Return (some body), bodyExpr.source⟩ else body
      .Opaque outputEnsures (some retBody) []
  | .Opaque postconds impl modif =>
    let impl' := impl.map fun b => wrap ((elimStmt ptMap model b).run initVars).1 b.source
    .Opaque (postconds ++ outputEnsures) impl' modif
  | .Abstract postconds => .Abstract (postconds ++ outputEnsures)
  | .External => .External
  let resolve := mapStmtExpr (resolveExprNode ptMap)
  let resolveBody : Body → Body := fun body => match body with
    | .Transparent b => .Transparent (resolve b)
    | .Opaque ps impl modif => .Opaque (ps.map (·.mapCondition resolve)) (impl.map resolve) (modif.map resolve)
    | .Abstract ps => .Abstract (ps.map (·.mapCondition resolve))
    | .External => .External
  { proc with
    body := resolveBody body'
    inputs := proc.inputs.map fun p => { p with type := resolveType ptMap p.type }
    outputs := proc.outputs.map fun p => { p with type := resolveType ptMap p.type }
    preconditions := (proc.preconditions ++ inputRequires).map (·.mapCondition resolve) }

private def mkWitnessProc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let src := ct.witness.source

  let witnessId : Identifier := mkId "$witness"
  let witnessInit : StmtExprMd :=
    ⟨.Assign [⟨.Declare ⟨witnessId, resolveType ptMap ct.base⟩, src⟩] ct.witness, src⟩
  let assert : StmtExprMd :=
    ⟨.Assert { condition := (constraintCallFor ptMap (.UserDefined ct.name) witnessId (src := src)).get! }, src⟩
  { name := mkId s!"$witness_{ct.name.text}"
    inputs := []
    outputs := []
    body := .Opaque [] (some ⟨.Block [witnessInit, assert] none, src⟩) []
    preconditions := []
    isFunctional := false
    decreases := none }

/-- Eliminate constrained types within a composite type definition: resolve
    constrained field types to their base types and run constrained type
    elimination on the composite's instance procedures.

    This is necessary because `constrainedTypeElim` removes the constrained type
    definitions from the program. Any reference to a constrained type left inside
    a composite (e.g. a `count: nat` field) would otherwise dangle and fail to
    resolve in later passes and the final Core translation. -/
def elimCompositeType (ptMap : ConstrainedTypeMap) (model : SemanticModel) (ct : CompositeType) : CompositeType :=
  { ct with
    fields := ct.fields.map fun f => { f with type := resolveType ptMap f.type }
    instanceProcedures := ct.instanceProcedures.map (elimProc ptMap model) }

public def constrainedTypeElim (model : SemanticModel) (program : Program)
    : Program × List DiagnosticModel :=
  let ptMap := buildConstrainedTypeMap program.types
  if ptMap.isEmpty then (program, []) else
  let constraintFuncs := program.types.filterMap fun
    | .Constrained ct => some (mkConstraintFunc ptMap ct) | _ => none
  let witnessProcedures := program.types.filterMap fun
    | .Constrained ct => some (mkWitnessProc ptMap ct) | _ => none
  let funcDiags := program.staticProcedures.foldl (init := []) fun acc proc =>
    if proc.isFunctional && proc.outputs.any (fun p => isConstrainedType ptMap p.type.val) then
      acc.cons (diagnosticFromSource proc.name.source "constrained return types on functions are not yet supported")
    else acc
  ({ program with
    staticProcedures := constraintFuncs ++ program.staticProcedures.map (elimProc ptMap model)
                        ++ witnessProcedures
    types := program.types.filterMap fun
      | .Constrained _ => none
      | .Composite ct => some (.Composite (elimCompositeType ptMap model ct))
      | other => some other },
   funcDiags)

/-- Pipeline pass: constrained type elimination. -/
public def constrainedTypeElimPass : LaurelPass where
  name := "ConstrainedTypeElim"
  documentation := "Eliminates constrained types by replacing them with their base types and generating constraint-checking functions and witness procedures. Type tests against constrained types are rewritten to call the generated constraint function."
  needsResolves := true
  run := fun p m =>
    let (p', diags) := constrainedTypeElim m p
    (p', diags, {})

end Strata.Laurel
