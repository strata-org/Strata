/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.GlobalVarAnalysis
import Strata.Languages.Laurel.HeapParameterization
import Strata.Util.Tactics

/-!
# Constrained Type Elimination

A Laurel-to-Laurel pass that eliminates constrained types by:
1. Generating a constraint procedure per constrained type (e.g. `nat$constraint(x: int): bool`)
2. Adding `requires constraintProc(param)` for constrained-typed inputs
3. Adding `ensures constraintProc(result)` for constrained-typed outputs
4. Inserting `assert constraintProc(var)` for local variable init and reassignment
5. Assuming the constraint for uninitialized constrained-typed variables (havoc + assume)
6. Adding a synthetic witness-validation procedure per constrained type
7. Injecting constraint procedure calls into quantifier bodies (`forall` → `implies`, `exists` → `and`)
8. Resolving all constrained type references to their base types
-/

namespace Strata.Laurel

open Strata

abbrev ConstrainedTypeMap := Std.HashMap String ConstrainedType

def buildConstrainedTypeMap (types : List TypeDefinition) : ConstrainedTypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Constrained ct => m.insert ct.name.text ct | _ => m

partial def resolveBaseType (ptMap : ConstrainedTypeMap) (ty : HighType) : HighType :=
  -- Resolve every constrained `UserDefined` type to its base, recursing through
  -- all component types via the generic `HighType.mapType` traversal.
  ty.mapType fun
    | .UserDefined name => match ptMap.get? name.text with
      | some ct => resolveBaseType ptMap ct.base.val
      | none => .UserDefined name
    | t => t

def resolveType (ptMap : ConstrainedTypeMap) (ty : HighTypeMd) : HighTypeMd :=
  ⟨resolveBaseType ptMap ty.val, ty.source⟩

def isConstrainedType (ptMap : ConstrainedTypeMap) (ty : HighType) : Bool :=
  match ty with | .UserDefined name => ptMap.contains name.text | _ => false

/-- Build a call to the constraint procedure for a constrained type, asserting
    the constraint on the read-back expression `ref`. Returns `none` if `ty` is
    not a constrained type.

    `ref` is the expression whose value is checked (e.g. a local read
    `x` or a field read `c#count`), allowing this to serve every assignment
    target kind uniformly. -/
def constraintCallForExpr (ptMap : ConstrainedTypeMap) (ty : HighType)
    (ref : StmtExprMd) (src : FileRange) : Option StmtExprMd :=
  match ty with
  | .UserDefined name => if ptMap.contains name.text then
      some ⟨.StaticCall (mkId s!"{name.text}$constraint") [ref], src⟩
    else none
  | _ => none

/-- Build a call to the constraint procedure for a constrained type, checking a
    local variable read, or `none` if not constrained. -/
def constraintCallFor (ptMap : ConstrainedTypeMap) (ty : HighType)
    (varName : Identifier) (src : FileRange) : Option StmtExprMd :=
  constraintCallForExpr ptMap ty ⟨.Var (.Local varName), src⟩ src

/-- Generate a constraint procedure for a constrained type.
    For nested types, the procedure calls the parent's constraint procedure. -/
def mkConstraintProc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let baseType := resolveType ptMap ct.base
  let src := ct.constraint.source
  let bodyExpr: StmtExprMd := match ct.base.val with
    | .UserDefined parent =>
      if ptMap.contains parent.text then
        let paramId := { ct.valueName with uniqueId := none }
        let paramRef : StmtExprMd :=
          { val := .Var (.Local paramId), source := src }
        let parentCall : StmtExprMd :=
          { val := .StaticCall (mkId s!"{parent.text}$constraint") [paramRef], source := src }
        { val := .StaticCall (mkId Operation.And.procName) [ct.constraint, parentCall], source := src }
      else ct.constraint
    | _ => ct.constraint
  { name := mkId s!"{ct.name.text}$constraint"
    inputs := [{ name := ct.valueName, type := baseType }]
    outputs := [{ name := mkId resultOutputName, type := { val := .TBool, source := src } }]
    body := .Transparent { val := .Return bodyExpr, source := src }
    decreases := none
    preconditions := [] }

def resolveVariable (ptMap : ConstrainedTypeMap) (v : VariableMd) : VariableMd :=
  match v.val with
  | .Declare param => ⟨.Declare { param with type := param.type.map (resolveType ptMap ·) }, v.source⟩
  | _ => v

/-- Resolve constrained types in type positions and inject constraint calls into quantifier bodies.
    Recursion into StmtExprMd children is handled by `mapStmtExpr`. -/
def resolveExprNode (ptMap : ConstrainedTypeMap) (expr : StmtExprMd) : StmtExprMd :=
  let source := expr.source

  match expr.val with
  | .Assign targets value =>
    ⟨.Assign (targets.map (resolveVariable ptMap)) value, source⟩
  | .Var (.Declare param) =>
    ⟨.Var (.Declare { param with type := param.type.map (resolveType ptMap ·) }), source⟩
  | .Quantifier mode param trigger body =>
    let param' := { param with type := resolveType ptMap param.type }
    -- With bottom-up traversal, `body` is already recursed into. The newly
    -- created operator call won't be visited again, which is safe because
    -- `c` (from `constraintCallFor`) is a StaticCall with Identifier leaves
    -- that don't need further resolution.
    let combiner := match mode with | .Forall => Operation.Implies | .Exists => Operation.And
    let injected := match constraintCallFor ptMap param.type.val param.name (src := source) with
      | some c => ⟨.StaticCall (mkId combiner.procName) [c, body], source⟩
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
  | .Var (.Declare ⟨name, some ty⟩) =>
    let check := (constraintCallFor ptMap ty.val name (src := source)).toList.map
      fun c => ⟨.Assume c, source⟩
    [node] ++ check
  | .Assign targets _value =>
    let asserts: List StmtExprMd := targets.filterMap (fun target =>
      let ref : StmtExprMd := VariableMd.toReadbackExpr target
      let ty : HighType := (computeExprType model ref).val
      (constraintCallForExpr ptMap ty ref (src := source)).map (⟨.Assert · none, source⟩))
    let suffix := match targets with
      | [single] => if resultUsed then [VariableMd.toReadbackExpr single] else []
      | _ => []
    [node] ++ asserts ++ suffix
  | .Var (.Field ..) =>
    -- Constrained field read → `{ assume T$constraint(read); read }`.
    -- `elimCompositeType` lowers the declared type to its base without restating the
    -- predicate on READ, while the range OBLIGATION still lands at the destination
    -- (`ensures` on a constrained output, `assert` on a constrained local) --
    -- unprovable rather than imprecise: without this assume, `return self#x` on an
    -- `int32` field cannot discharge its own `int32` postcondition.
    --
    -- ASSUMED, not asserted, resting on the DECLARED type as a standing fact about
    -- every value read out of the field (as `.Declare` above does for an
    -- uninitialized local), NOT on write coverage: a fresh composite's fields are
    -- never assigned, yet a read is assumed in range (measured). Writes are covered
    -- anyway -- `.Assign` checks each, and `IncrDecr` / `CompoundAssign` lower to
    -- `.Assign` first (LaurelCompilationPipeline runs
    -- eliminateIncrDecrAndCompoundAssign before constrainedTypeElim).
    --
    -- On the READ: hoisting to the enclosing statement could reference a local that
    -- statement declares. The duplicated read is pure (`readField(heap, obj, field)`);
    -- `.Assign` needs a read-back because its RHS may not be. Bottom-up traversal
    -- leaves the copy inside the assume unvisited, as `.Quantifier` relies on too.
    --
    -- Field reads only: a datatype destructor read (`MkCell(v).val`) has no checked
    -- write, so the `Datatype` branch over-approximates.
    match constraintCallForExpr ptMap (computeExprType model node).val node (src := source) with
    | some c => [⟨.Assume c, source⟩, node]
    | none => [node]
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
  let outputEnsures : List Condition := proc.outputs.filterMap fun p =>
    (constraintCallFor ptMap p.type.val p.name (src := p.type.source)).map
      fun c => { condition := ⟨c.val, p.type.source⟩ }
  let body' := match proc.body with
  | .Transparent bodyExpr =>
    let body := elimStmts ptMap model bodyExpr
    if outputEnsures.isEmpty then .Transparent body
    else
      .Opaque outputEnsures (some body) []
  | .Opaque postconds impl modif =>
    let impl' := impl.map (elimStmts ptMap model)
    .Opaque (postconds ++ outputEnsures) impl' modif
  | .Abstract postconds => .Abstract (postconds ++ outputEnsures)
  | .External => .External
  let resolve := mapStmtExpr (resolveExprNode ptMap)
  let proc := { proc with
    body := body'
    inputs := proc.inputs.map fun p => { p with type := resolveType ptMap p.type }
    outputs := proc.outputs.map fun p => { p with type := resolveType ptMap p.type }
    -- Prepend the generated input type-constraint requires. This is a
    -- semantics-preserving normalization, not a verification change: each
    -- precondition lowers to its own `$preN` helper (ContractPass), so the
    -- assume block at the callee body start and the independent asserts at
    -- call sites do not depend on this order. Kept constraints-first for
    -- readability.
    preconditions := inputRequires ++ proc.preconditions }
  mapProcedureM (m := Id) resolve proc

private def mkWitnessProc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let src := ct.witness.source

  let witnessId : Identifier := mkId "$witness"
  let witnessInit : StmtExprMd :=
    ⟨.Assign [⟨.Declare ⟨witnessId, some (resolveType ptMap ct.base)⟩, src⟩] ct.witness, src⟩
  let assert : StmtExprMd :=
    ⟨.Assert (constraintCallFor ptMap (.UserDefined ct.name) witnessId (src := src)).get! none, src⟩
  { name := mkId s!"$witness_{ct.name.text}"
    inputs := []
    outputs := []
    body := .Opaque [] (some ⟨.Block [witnessInit, assert] none, src⟩) []
    preconditions := []
    decreases := none }

/-- Eliminate constrained types within a composite type definition: resolve
    constrained field types to their base types and run constrained type
    elimination on the composite's instance procedures.

    This is necessary because `constrainedTypeElim` removes the constrained type
    definitions from the program. Any reference to a constrained type left inside
    a composite (e.g. a `count: nat` field) would otherwise dangle and fail to
    resolve in later passes and the final Core translation. -/
def elimCompositeType (ptMap : ConstrainedTypeMap) (model : SemanticModel)
    (ct : CompositeType) (prepare : Procedure → Procedure := id) : CompositeType :=
  { ct with
    fields := ct.fields.map fun f => { f with type := resolveType ptMap f.type }
    instanceProcedures := ct.instanceProcedures.map (elimProc ptMap model ∘ prepare) }

private def procedureHasEffect (ids : Std.HashSet Nat) (proc : Procedure) : Bool :=
  proc.name.uniqueId.any ids.contains

/-- Preserve constrained-global invariants while globals are still represented
    as fields. Readers require a valid incoming value; writers additionally
    guarantee a valid outgoing value. -/
private def addConstrainedGlobalConditions (ptMap : ConstrainedTypeMap)
    (effects : GlobalEffectsByProcId) (fields : List Field)
    (proc : Procedure) : Procedure :=
  let (requires, ensures) := fields.foldl (init := ([], []))
    fun (requires, ensures) field =>
      let isConstrained := match field.type.val with
        | .UserDefined name => ptMap.contains name.text
        | _ => false
      if !isConstrained then (requires, ensures) else
      let qualifiedName := { field.name with text := s!"$static.{field.name.text}" }
      let reference : StmtExprMd := ⟨.Var (.Local qualifiedName), field.name.source⟩
      let condition := (constraintCallForExpr ptMap field.type.val reference
        (src := field.type.source)).map fun call => ({ condition := call } : Condition)
      let readers := match field.name.uniqueId with
        | some id => effects.readers.getD id {}
        | none => {}
      let writers := match field.name.uniqueId with
        | some id => effects.writers.getD id {}
        | none => {}
      let requires := if procedureHasEffect readers proc || procedureHasEffect writers proc then
        requires ++ condition.toList else requires
      let ensures := if procedureHasEffect writers proc then
        ensures ++ condition.toList else ensures
      (requires, ensures)
  let body := if ensures.isEmpty then proc.body else match proc.body with
    | .Transparent implementation => .Opaque ensures (some implementation) []
    | .Opaque posts implementation modifies =>
        .Opaque (posts ++ ensures) implementation modifies
    | .Abstract posts => .Abstract (posts ++ ensures)
    | .External => .External
  { proc with preconditions := requires ++ proc.preconditions, body }

public def constrainedTypeElim (model : SemanticModel) (program : Program)
    : Program × List Message :=
  let ptMap := buildConstrainedTypeMap program.types
  if ptMap.isEmpty then (program, []) else
  let constraintProcs := program.types.filterMap fun
    | .Constrained ct => some (mkConstraintProc ptMap ct) | _ => none
  let witnessProcedures := program.types.filterMap fun
    | .Constrained ct => some (mkWitnessProc ptMap ct) | _ => none
  let instanceProcedures := program.types.flatMap fun
    | .Composite composite => composite.instanceProcedures
    | _ => []
  let allProcedures := program.staticProcedures ++ instanceProcedures
  let effects := computeGlobalEffectsByProcId model allProcedures program.staticFields
  let addGlobalConditions :=
    addConstrainedGlobalConditions ptMap effects program.staticFields
  ({ program with
    staticProcedures := constraintProcs ++
      program.staticProcedures.map (elimProc ptMap model ∘ addGlobalConditions)
                        ++ witnessProcedures
    staticFields := program.staticFields.map fun field =>
      { field with
        type := resolveType ptMap field.type
        initializer := field.initializer.map (mapStmtExpr (resolveExprNode ptMap)) }
    types := program.types.filterMap fun
      | .Constrained _ => none
      | .Composite ct =>
          some (.Composite (elimCompositeType ptMap model ct addGlobalConditions))
      | .Datatype dt =>
        -- Resolve constrained types used as datatype constructor field
        -- types (e.g. `int32` -> `int`). Without this, the constrained
        -- type reference dangles after its definition is dropped below,
        -- and the Laurel-to-Core translator cannot resolve it.
        -- This lowers the field *type* only; the range predicate is not
        -- re-asserted on field reads, so field range constraints are
        -- intentionally over-approximated away (a `MkCell(out_of_range).val`
        -- read is not caught) — matching bare-parameter and `elimCompositeType`
        -- handling.
        some (.Datatype { dt with constructors := dt.constructors.map fun c =>
          { c with args := c.args.map fun p =>
            { p with type := resolveType ptMap p.type } } })
      | other => some other },
   [])

/-- Pipeline pass: constrained type elimination. -/
public def constrainedTypeElimPass : LoweringPass where
  name := "ConstrainedTypeElim"
  documentation := "Eliminates constrained types by replacing them with their base types and generating constraint-checking procedures and witness procedures. Type tests against constrained types are rewritten to call the generated constraint procedure."
  needsResolves := true
  run := fun _ p m =>
    let (p', diags) := constrainedTypeElim m p
    (p', diags, {})
  comesBefore :=
    [⟨ heapParameterizationPass.meta,
       "constrained types must be reduced to their base types before heap values are boxed." ⟩]

end Strata.Laurel
