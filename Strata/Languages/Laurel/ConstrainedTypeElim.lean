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

/-- Build a call to the constraint function for a constrained type, asserting
    the constraint on the read-back expression `ref`. Returns `none` if `ty` is
    not a constrained type.

    `ref` is the expression whose value is checked (e.g. a local read
    `x` or a field read `c#count`), allowing this to serve every assignment
    target kind uniformly. -/
def constraintCallForExpr (ptMap : ConstrainedTypeMap) (ty : HighType)
    (ref : StmtExprMd) (src : Option FileRange := none) : Option StmtExprMd :=
  match ty with
  | .UserDefined name => if ptMap.contains name.text then
      some ⟨.StaticCall (mkId s!"{name.text}$constraint") [ref], src⟩
    else none
  | _ => none

/-- Build a call to the constraint function for a constrained type, checking a
    local variable read, or `none` if not constrained. -/
def constraintCallFor (ptMap : ConstrainedTypeMap) (ty : HighType)
    (varName : Identifier) (src : Option FileRange := none) : Option StmtExprMd :=
  constraintCallForExpr ptMap ty ⟨.Var (.Local varName), src⟩ src

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

/-- Per-node constrained-type elimination, applied bottom-up (with flattening)
    by `mapStmtExprFlattenM`. `resultUsed` is `true` when the node occupies a
    value position.

    - Uninitialized constrained declaration `var x: T;` → assume its constraint.
    - Assignment to constrained target(s) → emit the assignment followed by an
      `assert T$constraint(<read-back>)` per constrained target. The constraint
      is checked on a *read-back* of the target rather than on the RHS, so the
      RHS is evaluated exactly once. In value position the read-back is also
      appended as the final statement, so the resulting value-block evaluates to
      the assigned value (this covers expression-position assignments such as
      `y := (x := -1) + 1`); in statement position it is omitted.
    - All other nodes are returned unchanged; the traversal handles recursion. -/
def elimNode (ptMap : ConstrainedTypeMap) (model : SemanticModel)
    (resultUsed : Bool) (node : StmtExprMd) : List StmtExprMd :=
  let source := node.source
  match node.val with
  | .Var (.Declare param) =>
    let check := (constraintCallFor ptMap param.type.val param.name (src := source)).toList.map
      fun c => ⟨.Assume c, source⟩
    [node] ++ check
  | .Assign targets _value =>
    let asserts: List StmtExprMd := targets.filterMap (fun target =>
      let ref : StmtExprMd := VariableMd.toReadbackExpr target
      let ty : HighType := (computeExprType model ref).val
      (constraintCallForExpr ptMap ty ref (src := source)).map (⟨.Assert { condition := · }, source⟩))
    let suffix := match targets with
      | [single] => if resultUsed then [VariableMd.toReadbackExpr single] else []
      | _ => []
    [node] ++ asserts ++ suffix
  | _ => [node]

/-- Apply `elimNode` across a body via the flattening, `resultUsed`-aware
    traversal. A procedure body is a statement, so the top-level `resultUsed`
    is `false`. -/
def elimStmts (ptMap : ConstrainedTypeMap) (model : SemanticModel) (body : StmtExprMd) : StmtExprMd :=
  mapStmtExprFlattenM (m := Id) (fun _ _ => none) (elimNode ptMap model) false body

def elimProc (ptMap : ConstrainedTypeMap) (model : SemanticModel) (proc : Procedure) : Procedure :=
  let inputRequires : List Condition := proc.inputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name (src := p.type.source)).map
      fun c => { condition := c }
  let outputEnsures : List Condition := if proc.isFunctional then [] else proc.outputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name (src := p.type.source)).map
      fun c => { condition := ⟨c.val, p.type.source⟩ }
  let body' := match proc.body with
  | .Transparent bodyExpr =>
    let body := elimStmts ptMap model bodyExpr
    if outputEnsures.isEmpty then .Transparent body
    else
      let retBody := if proc.isFunctional then ⟨.Return (some body), bodyExpr.source⟩ else body
      .Opaque outputEnsures (some retBody) []
  | .Opaque postconds impl modif =>
    let impl' := impl.map (elimStmts ptMap model)
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
