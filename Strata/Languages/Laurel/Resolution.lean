/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Tactics
import Strata.Languages.Python.PythonLaurelCorePrelude

/-!
# Name Resolution Pass

Assigns a unique numeric ID to every definition and reference node in a
Laurel program, then resolves references to their definitions.

## Design

The resolution pass operates in two phases:

### Phase 1: ID Assignment and Reference Resolution
Walks the AST, assigning fresh unique IDs to all definition nodes and
resolving references by looking up names in the current lexical scope.
After this phase, every definition and reference node has its `id` field
filled in.

### Phase 2: Build refToDef Map
Walks the *resolved* AST (where all definitions already have their UUIDs)
and builds a map from each definition's ID to its `ResolvedNode`. Because this
happens after Phase 1, the `ResolvedNode` values in the map contain the fully
resolved sub-trees (e.g. a procedure's parameters already have their IDs).

### Definition nodes (introduce a name into scope)
- `StmtExpr.LocalVariable` — local variable declaration
- `StmtExpr.Quantifier` — quantifier-bound variable
- `Parameter` — procedure parameter
- `Procedure` — procedure definition
- `Field` — field on a composite type
- `CompositeType` / `ConstrainedType` / `DatatypeDefinition` — type definitions
- `DatatypeConstructor` — datatype constructor
- `Constant` — named constant

### Reference nodes (use a name)
- `StmtExpr.Identifier` — variable reference
- `StmtExpr.StaticCall` — static procedure call
- `StmtExpr.InstanceCall` — instance method call
- `StmtExpr.FieldSelect` — field access
- `StmtExpr.New` — object creation (references a type)
- `StmtExpr.Exit` — exit a labelled block
- `HighType.UserDefined` — type reference

Each of these nodes carries an `id : Nat` field (defaulting to `0`).
The ID assignment pass fills in unique values. The resolution pass then
builds a map from reference IDs to `ResolvedNode` values describing the
definition each reference resolves to.
-/

namespace Strata.Laurel

public section

/-! ## ResolvedNode — the target of a resolved reference -/

/-- The kind (constructor tag) of a `ResolvedNode`, used to assert that a reference
    resolves to the expected sort of definition. -/
inductive ResolvedNodeKind where
  | var
  | parameter
  | staticProcedure
  | instanceProcedure
  | field
  | compositeType
  | constrainedType
  | datatypeDefinition
  | datatypeConstructor
  | typeAlias
  | constant
  | quantifierVar
  | unresolved
  deriving Repr, BEq

def ResolvedNodeKind.name : ResolvedNodeKind → String
  | .var               => "variable"
  | .parameter         => "parameter"
  | .staticProcedure   => "static procedure"
  | .instanceProcedure => "instance procedure"
  | .field             => "field"
  | .compositeType     => "composite type"
  | .constrainedType   => "constrained type"
  | .datatypeDefinition => "datatype definition"
  | .datatypeConstructor => "datatype constructor"
  | .typeAlias         => "type alias"
  | .constant          => "constant"
  | .quantifierVar     => "quantifier variable"
  | .unresolved        => "unresolved"

/-- A definition-site AST node that a reference can resolve to. -/
inductive ResolvedNode where
  /-- A local variable declaration. -/
  | var (name : Identifier) (type : HighTypeMd)
  /-- A procedure parameter. -/
  | parameter (param : Parameter)
  /-- A static procedure. -/
  | staticProcedure (proc : Procedure)
  /-- An instance procedure (method) on a composite type. -/
  | instanceProcedure (typeName : Identifier) (proc : Procedure)
  /-- A field on a composite type. -/
  | field (typeName : Identifier) (fld : Field)
  /-- A composite type definition. -/
  | compositeType (ty : CompositeType)
  /-- A constrained type definition. -/
  | constrainedType (ty : ConstrainedType)
  /-- A datatype definition. -/
  | datatypeDefinition (ty : DatatypeDefinition)
  /-- A datatype constructor. -/
  | datatypeConstructor (typeName : Identifier) (ctor : DatatypeConstructor)
  /-- A type alias. -/
  | typeAlias (ty : TypeAlias)
  /-- A constant. -/
  | constant (c : Constant)
  /-- A quantifier-bound variable. -/
  | quantifierVar (name : Identifier) (type : HighTypeMd)
  | unresolved (referenceSource: Option FileRange)
  deriving Repr

instance : Inhabited ResolvedNode where
  default := ResolvedNode.unresolved none

/-- Return the constructor tag of a `ResolvedNode`. -/
def ResolvedNode.kind : ResolvedNode → ResolvedNodeKind
  | .var ..               => .var
  | .parameter ..         => .parameter
  | .staticProcedure ..   => .staticProcedure
  | .instanceProcedure .. => .instanceProcedure
  | .field ..             => .field
  | .compositeType ..     => .compositeType
  | .constrainedType ..   => .constrainedType
  | .datatypeDefinition .. => .datatypeDefinition
  | .datatypeConstructor .. => .datatypeConstructor
  | .typeAlias ..         => .typeAlias
  | .constant ..          => .constant
  | .quantifierVar ..     => .quantifierVar
  | .unresolved _          => .unresolved

def ResolvedNode.getType (node: ResolvedNode): HighTypeMd := match node with
 | .var _ type => type
 | .parameter p => p.type
 | .field _ f => f.type
 | .datatypeConstructor type _ => ⟨ .UserDefined type, none ⟩
 | .constant c => c.type
 | .quantifierVar _ type => type
 | .unresolved source => ⟨ .Unknown, source ⟩
 | _ => dbg_trace s!"SOUND BUG: getType called on {repr node}"; default

/-! ## Resolution result -/

structure SemanticModel where
  nextId: Nat
  compositeCount: Nat
  refToDef: Std.HashMap Nat ResolvedNode
  deriving Repr

def SemanticModel.get (model: SemanticModel) (iden: Identifier): ResolvedNode :=
  match iden.uniqueId with
  | some key => (model.refToDef.get? key).getD default
  | none => default

def SemanticModel.isFunction (model: SemanticModel) (id: Identifier): Bool :=
  match model.get id with
      | .staticProcedure proc => proc.isFunctional
      | .parameter _ => true
      | .datatypeConstructor _ _ => true
      | .constant _ => true
      | .unresolved _ => true -- functions calls are more permissive, so true avoids possibly incorrect errors
      | node =>
          dbg_trace s!"Sound but incomplete BUG! id: {repr id}, is not a procedure, but a node {repr node}"
          false

/-- The output of the resolution pass. -/
structure ResolutionResult where
  /-- The program with unique IDs on all definition and reference nodes. -/
  program : Program
  /-- Map from reference node ID to the definition it resolves to. -/
  model : SemanticModel
  /-- Diagnostics collected during resolution (e.g. unresolved references). -/
  errors : Array DiagnosticModel := #[]

/-! ## Phase 1: ID assignment and reference resolution -/

/-- A scope entry stores the definition-site ID and the ResolvedNode for type lookups. -/
@[expose] abbrev ScopeEntry := Nat × ResolvedNode

/-- Scope maps a name to its definition-site ID and optional ResolvedNode. -/
@[expose] abbrev Scope := Std.HashMap String ScopeEntry

/-- Per-composite-type scope mapping field names to their scope entries. -/
@[expose] abbrev TypeScopes := Std.HashMap String Scope

/-- State threaded through the resolution pass. -/
structure ResolveState where
  /-- Next fresh ID to allocate. -/
  nextId : Nat := 1
  /-- Current lexical scope (name → definition ID). -/
  scope : Scope := {}
  /-- Names defined at the current scope level (for duplicate detection). -/
  currentScopeNames : Std.HashSet String := {}
  /-- Per-composite-type field scopes (type name → field name → scope entry). -/
  typeScopes : TypeScopes := {}
  /-- Diagnostics collected during resolution. -/
  errors : Array DiagnosticModel := #[]
  /-- When resolving inside an instance procedure, the owning composite type name.
      Used by `resolveFieldRef` to resolve `self.field` when `self` has type `Any`. -/
  instanceTypeName : Option String := none

@[expose] abbrev ResolveM := StateM ResolveState

/-- Allocate a fresh unique ID. -/
private def freshId : ResolveM Nat := do
  let s ← get
  let id := s.nextId
  set { s with nextId := id + 1 }
  return id


/-- Like `defineName`, but reports a diagnostic if the name already exists in the current scope.
    Inserts an `.unresolved` node so subsequent references still resolve without cascading errors. -/
def defineNameCheckDup (iden : Identifier) (node : ResolvedNode) (overrideResolutionName: Option String := none) : ResolveM Identifier := do
  let resolutionName := overrideResolutionName.getD iden.text
  if (← get).currentScopeNames.contains resolutionName then
    let diag := diagnosticFromSource iden.source s!"Duplicate definition '{resolutionName}' is already defined in this scope"
    modify fun s => { s with errors := s.errors.push diag }
    defineName iden (.unresolved iden.source) overrideResolutionName
  else
    defineName iden node overrideResolutionName
  where
  defineName (iden : Identifier) (node : ResolvedNode) (overrideResolutionName: Option String := none) : ResolveM Identifier := do
    let resolutionName := overrideResolutionName.getD iden.text
    let (name', uniqueId) ← match iden.uniqueId with
      | some uid => pure (iden, uid)
      | none =>
        let id ← freshId
        pure ({ iden with uniqueId := some (id) }, id)

    modify fun s => { s with scope := s.scope.insert resolutionName (uniqueId, node),
                             currentScopeNames := s.currentScopeNames.insert resolutionName }
    return name'

/-- Resolve a reference: look up the name in scope and assign the definition's ID.
    Returns the identifier with its ID filled in.
    When `expected` is provided, emits a diagnostic if the resolved node's kind is not
    in the list of expected kinds. -/
def resolveRef (name : Identifier) (source : Option FileRange := none)
    (expected : Array ResolvedNodeKind := #[]) : ResolveM Identifier := do
  let s ← get
  match s.scope.get? name.text with
  | some (defId, node) =>
    let name' := { name with uniqueId := some defId }
    if expected.size > 0 && node.kind != .unresolved && !expected.contains node.kind then
      let expectedStr := ", ".intercalate (expected.toList.map ResolvedNodeKind.name)
      let diag := diagnosticFromSource (source.orElse fun _ => name.source)
        s!"'{name}' resolves to {node.kind.name}, but expected {expectedStr}"
      modify fun s => { s with errors := s.errors.push diag }
    return name'
  | none =>
    let diag := diagnosticFromSource (source.orElse fun _ => name.source) s!"Resolution failed: '{name}' is not defined"
    modify fun s => { s with errors := s.errors.push diag }
    return { name with uniqueId := none }

/-- Extract the UserDefined type name from a resolved target expression by looking up its scope entry. -/
private def targetTypeName (target : StmtExprMd) : ResolveM (Option String) := do
  let s ← get
  match target.val with
  | .Identifier ref =>
    match s.scope.get? ref.text with
    | some (_, node) =>
      match node.getType.val with
      | .UserDefined typRef => pure (some typRef.text)
      | .TArray _ => pure (some arrayCompositeName)
      | _ => pure none
    | none => pure none
  | _ => pure none

/-- Try to resolve a field name via a type scope lookup. Returns `some id` on success. -/
private def resolveFieldInTypeScope (typeName : String) (fieldName : Identifier) : ResolveM (Option Identifier) := do
  let s ← get
  match s.typeScopes.get? typeName with
  | some typeScope =>
    match typeScope.get? fieldName.text with
    | some (defId, _) => return some { fieldName with uniqueId := some defId }
    | none => return none
  | none => return none

/-- Resolve a field reference using the target's type to build a qualified lookup key.
    Falls back to the instance type name (for `self.field` in instance methods),
    then to unqualified lookup if the target type cannot be determined. -/
def resolveFieldRef (target : StmtExprMd) (fieldName : Identifier)
    (source : Option FileRange) : ResolveM Identifier := do
  let typeName? ← targetTypeName target
  -- Try type scope from the target's declared type
  if let some typeName := typeName? then
    if let some resolved ← resolveFieldInTypeScope typeName fieldName then
      return resolved
  -- Fallback: use the owning instance type (handles `self.field` when self has type `Any`)
  if let some instTypeName := (← get).instanceTypeName then
    if let some resolved ← resolveFieldInTypeScope instTypeName fieldName then
      return resolved
  resolveRef fieldName source

/-- Save and restore scope around a block (for lexical scoping). -/
def withScope (action : ResolveM α) : ResolveM α := do
  let savedScope := (← get).scope
  let savedNames := (← get).currentScopeNames
  modify fun s => { s with currentScopeNames := {} }
  let result ← action
  modify fun s => { s with scope := savedScope, currentScopeNames := savedNames }
  return result

/-! ## AST traversal (Phase 1) -/


def resolveHighType (ty : HighTypeMd) : ResolveM HighTypeMd := do
  match ty with
  | AstNode.mk val _ =>
  let val' ← match val with
  | .UserDefined ref =>
    let ref' ← resolveRef ref ty.source
      (expected := #[.compositeType, .constrainedType, .datatypeDefinition, .typeAlias])
    pure (.UserDefined ref')
  | .TTypedField vt =>
    let vt' ← resolveHighType vt
    pure (.TTypedField vt')
  | .TSet et =>
    let et' ← resolveHighType et
    pure (.TSet et')
  | .TMap kt vt =>
    let kt' ← resolveHighType kt
    let vt' ← resolveHighType vt
    pure (.TMap kt' vt')
  | .TSeq et =>
    let et' ← resolveHighType et
    pure (.TSeq et')
  | .TArray et =>
    let et' ← resolveHighType et
    pure (.TArray et')
  | .Applied base args =>
    let base' ← resolveHighType base
    let args' ← args.mapM resolveHighType
    pure (.Applied base' args')
  | .Pure base =>
    let base' ← resolveHighType base
    pure (.Pure base')
  | .Intersection tys =>
    let tys' ← tys.mapM resolveHighType
    pure (.Intersection tys')
  | other => pure other
  return { val := val', source := ty.source }

def resolveStmtExpr (exprMd : StmtExprMd) : ResolveM StmtExprMd := do
  match _: exprMd with
  | AstNode.mk expr source =>
  let val' ← match _: expr with
  | .IfThenElse cond thenBr elseBr =>
    let cond' ← resolveStmtExpr cond
    let thenBr' ← resolveStmtExpr thenBr
    let elseBr' ← elseBr.attach.mapM (fun a => have := a.property; resolveStmtExpr a.val)
    pure (.IfThenElse cond' thenBr' elseBr')
  | .Block stmts label =>
    withScope do
      let stmts' ← stmts.mapM resolveStmtExpr
      pure (.Block stmts' label)
  | .LocalVariable name ty init =>
    let ty' ← resolveHighType ty
    let init' ← init.attach.mapM (fun a => have := a.property; resolveStmtExpr a.val)
    let name' ← defineNameCheckDup name (.var name ty')
    pure (.LocalVariable name' ty' init')
  | .While cond invs dec body =>
    let cond' ← resolveStmtExpr cond
    let invs' ← invs.attach.mapM (fun a => have := a.property; resolveStmtExpr a.val)
    let dec' ← dec.attach.mapM (fun a => have := a.property; resolveStmtExpr a.val)
    let body' ← resolveStmtExpr body
    pure (.While cond' invs' dec' body')
  | .Exit target => pure (.Exit target)
  | .Return val => do
    let val' ← val.attach.mapM (fun a => have := a.property; resolveStmtExpr a.val)
    pure (.Return val')
  | .LiteralInt v => pure (.LiteralInt v)
  | .LiteralBool v => pure (.LiteralBool v)
  | .LiteralString v => pure (.LiteralString v)
  | .LiteralDecimal v => pure (.LiteralDecimal v)
  | .Identifier ref =>
    let ref' ← resolveRef ref source
    pure (.Identifier ref')
  | .Assign targets value =>
    let targets' ← targets.mapM resolveStmtExpr
    let value' ← resolveStmtExpr value
    pure (.Assign targets' value')
  | .FieldSelect target fieldName =>
    let target' ← resolveStmtExpr target
    let fieldName' ← resolveFieldRef target' fieldName source
    pure (.FieldSelect target' fieldName')
  | .PureFieldUpdate target fieldName newVal =>
    let target' ← resolveStmtExpr target
    let fieldName' ← resolveFieldRef target' fieldName source
    let newVal' ← resolveStmtExpr newVal
    pure (.PureFieldUpdate target' fieldName' newVal')
  | .StaticCall callee args =>
    let callee' ← resolveRef callee source
      (expected := #[.parameter, .staticProcedure, .datatypeConstructor, .constant])
    let args' ← args.mapM resolveStmtExpr
    pure (.StaticCall callee' args')
  | .PrimitiveOp op args =>
    let args' ← args.mapM resolveStmtExpr
    pure (.PrimitiveOp op args')
  | .New ref =>
    let ref' ← resolveRef ref source
      (expected := #[.compositeType, .datatypeDefinition])
    pure (.New ref')
  | .This => pure .This
  | .ReferenceEquals lhs rhs =>
    let lhs' ← resolveStmtExpr lhs
    let rhs' ← resolveStmtExpr rhs
    pure (.ReferenceEquals lhs' rhs')
  | .AsType target ty =>
    let target' ← resolveStmtExpr target
    let ty' ← resolveHighType ty
    pure (.AsType target' ty')
  | .IsType target ty =>
    let target' ← resolveStmtExpr target
    let ty' ← resolveHighType ty
    pure (.IsType target' ty')
  | .InstanceCall target callee args =>
    let target' ← resolveStmtExpr target
    let callee' ← resolveRef callee source
      (expected := #[.instanceProcedure, .staticProcedure])
    let args' ← args.mapM resolveStmtExpr
    pure (.InstanceCall target' callee' args')
  | .Quantifier mode param trigger body =>
    withScope do
      let paramTy' ← resolveHighType param.type
      let paramName' ← defineNameCheckDup param.name (.quantifierVar param.name paramTy')
      let trigger' ← trigger.attach.mapM (fun pv => have := pv.property; resolveStmtExpr pv.val)
      let body' ← resolveStmtExpr body
      pure (.Quantifier mode ⟨paramName', paramTy'⟩ trigger' body')
  | .Assigned name =>
    let name' ← resolveStmtExpr name
    pure (.Assigned name')
  | .Old val =>
    let val' ← resolveStmtExpr val
    pure (.Old val')
  | .Fresh val =>
    let val' ← resolveStmtExpr val
    pure (.Fresh val')
  | .Assert ⟨condExpr, summary⟩ =>
    let cond' ← resolveStmtExpr condExpr
    pure (.Assert { condition := cond', summary })
  | .Assume cond =>
    let cond' ← resolveStmtExpr cond
    pure (.Assume cond')
  | .ProveBy val proof =>
    let val' ← resolveStmtExpr val
    let proof' ← resolveStmtExpr proof
    pure (.ProveBy val' proof')
  | .ContractOf ty fn =>
    let fn' ← resolveStmtExpr fn
    pure (.ContractOf ty fn')
  | .Abstract => pure .Abstract
  | .All => pure .All
  | .Hole det type => match type with
    | some ty =>
      let ty' ← resolveHighType ty
      pure (.Hole det ty')
    | none => pure (.Hole det none)
  | .Subscript target index update =>
    let target' ← resolveStmtExpr target
    let index' ← resolveStmtExpr index
    let update' ← update.attach.mapM (fun a => have := a.property; resolveStmtExpr a.val)
    pure (.Subscript target' index' update')
  return { val := val', source := source }
  termination_by exprMd
  decreasing_by all_goals term_by_mem

/-- Resolve a parameter: assign a fresh ID and add to scope. -/
def resolveParameter (param : Parameter) : ResolveM Parameter := do
  let ty' ← resolveHighType param.type
  let name' ← defineNameCheckDup param.name (.parameter ⟨param.name, ty'⟩)
  return ⟨name', ty'⟩

/-- Resolve a procedure body. -/
def resolveBody (body : Body) : ResolveM Body := do
  match body with
  | .Transparent b =>
    let b' ← resolveStmtExpr b
    return .Transparent b'
  | .Opaque posts impl mods =>
    let posts' ← posts.mapM (·.mapM resolveStmtExpr)
    let impl' ← impl.mapM resolveStmtExpr
    let mods' ← mods.mapM resolveStmtExpr
    return .Opaque posts' impl' mods'
  | .Abstract posts =>
    let posts' ← posts.mapM (·.mapM resolveStmtExpr)
    return .Abstract posts'
  | .External => return .External

/-- Resolve a procedure: resolve its name, then resolve params, contracts, and body in a new scope. -/
def resolveProcedure (proc : Procedure) : ResolveM Procedure := do
  let procName' ← resolveRef proc.name
  withScope do
    let inputs' ← proc.inputs.mapM resolveParameter
    let outputs' ← proc.outputs.mapM resolveParameter
    let pres' ← proc.preconditions.mapM (·.mapM resolveStmtExpr)
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let body' ← resolveBody proc.body
    if !proc.isFunctional && body'.isTransparent then
      let diag := diagnosticFromSource proc.name.source
        s!"transparent procedures are not yet supported. Add 'opaque' to make the procedure opaque"
      modify fun s => { s with errors := s.errors.push diag }
    let invokeOn' ← proc.invokeOn.mapM resolveStmtExpr
    return { name := procName', inputs := inputs', outputs := outputs',
             isFunctional := proc.isFunctional,
             preconditions := pres', decreases := dec',
             invokeOn := invokeOn',
             body := body' }

/-- Resolve a field: define its name under the qualified key (OwnerType.fieldName) and resolve its type. -/
def resolveField (ownerName : Identifier) (field : Field) : ResolveM Field := do
  let ty' ← resolveHighType field.type
  let qualifiedName := ownerName.text ++ "." ++ field.name.text
  let resolved ← resolveRef qualifiedName
  -- Keep the original field name text; only take the uniqueId from resolution.
  -- resolveRef returns text = "Owner.field" (the qualified lookup key), but the
  -- field's own name should stay unqualified.
  let name' := { field.name with uniqueId := resolved.uniqueId }
  return { name := name', isMutable := field.isMutable, type := ty' }

/-- Resolve an instance procedure on a composite type. -/
def resolveInstanceProcedure (typeName : Identifier) (proc : Procedure) : ResolveM Procedure := do
  let procName' ← resolveRef proc.name
  withScope do
    let savedInstType := (← get).instanceTypeName
    modify fun s => { s with instanceTypeName := some typeName.text }
    let inputs' ← proc.inputs.mapM resolveParameter
    let outputs' ← proc.outputs.mapM resolveParameter
    let pres' ← proc.preconditions.mapM (·.mapM resolveStmtExpr)
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let body' ← resolveBody proc.body
    if !proc.isFunctional && body'.isTransparent then
      let diag := diagnosticFromSource proc.name.source
        s!"transparent procedures are not yet supported. Add 'opaque' to make the procedure opaque"
      modify fun s => { s with errors := s.errors.push diag }
    let invokeOn' ← proc.invokeOn.mapM resolveStmtExpr
    modify fun s => { s with instanceTypeName := savedInstType }
    return { name := procName', inputs := inputs', outputs := outputs',
             isFunctional := proc.isFunctional,
             preconditions := pres', decreases := dec',
             invokeOn := invokeOn',
             body := body' }

/-- Resolve a type definition. -/
def resolveTypeDefinition (td : TypeDefinition) : ResolveM TypeDefinition := do
  match td with
  | .Composite ct =>
    let ctName' ← resolveRef ct.name
    let extending' ← ct.extending.mapM (resolveRef · none (expected := #[.compositeType]))
    let fields' ← ct.fields.mapM (resolveField ctName')
    -- Build per-type scope BEFORE resolving instance procedures, so that
    -- field references (e.g. self.field) inside methods can be resolved.
    let s ← get
    let mut typeScope : Scope := {}
    for parent in extending' do
      match s.typeScopes.get? parent.text with
      | some parentScope =>
        for (k, v) in parentScope do
          typeScope := typeScope.insert k v
      | none => pure ()
    -- Add own fields (these override inherited ones with the same name)
    for field in fields' do
      let qualifiedKey := ctName'.text ++ "." ++ field.name.text
      match s.scope.get? qualifiedKey with
      | some entry => typeScope := typeScope.insert field.name.text entry
      | none => pure ()
    modify fun s => { s with typeScopes := s.typeScopes.insert ctName'.text typeScope }
    let instProcs' ← ct.instanceProcedures.mapM (resolveInstanceProcedure ctName')
    return .Composite { name := ctName', extending := extending',
                        fields := fields', instanceProcedures := instProcs' }
  | .Constrained ct =>
    let ctName' ← resolveRef ct.name
    let base' ← resolveHighType ct.base
    -- The valueName (e.g. `x` in `constrained nat = x: int where x >= 0`) must be
    -- in scope when resolving the constraint and witness expressions.
    let (valueName', constraint', witness') ← withScope do
      let valueName' ← defineNameCheckDup ct.valueName (.quantifierVar ct.valueName base')
      let constraint' ← resolveStmtExpr ct.constraint
      let witness' ← resolveStmtExpr ct.witness
      return (valueName', constraint', witness')
    return .Constrained { name := ctName', base := base', valueName := valueName',
                          constraint := constraint', witness := witness' }
  | .Datatype dt =>
    let dtName' ← resolveRef dt.name
    let ctors' ← dt.constructors.mapM fun ctor => do
      let ctorName' ← resolveRef ctor.name
      let args' ← ctor.args.mapM fun (p: Parameter) => do
        let ty' ← resolveHighType p.type
        let resolved ← resolveRef (dt.destructorName p)
        -- Keep the original parameter name; only take the uniqueId from resolution.
        -- resolveRef returns text = "DtName..field" (the qualified lookup key), but the
        -- parameter's own name should stay unqualified.
        let destructorId := { p.name with uniqueId := resolved.uniqueId }
        return ⟨ destructorId, ty' ⟩
      return { name := ctorName', args := args' : DatatypeConstructor }
    return .Datatype { name := dtName', typeArgs := dt.typeArgs, constructors := ctors' }
  | .Alias ta =>
    let target' ← resolveHighType ta.target
    let taName' ← resolveRef ta.name
    return .Alias { name := taName', target := target' }

/-- Resolve a constant definition. -/
def resolveConstant (c : Constant) : ResolveM Constant := do
  let ty' ← resolveHighType c.type
  let init' ← c.initializer.mapM resolveStmtExpr
  let name' ← resolveRef c.name
  return { name := name', type := ty', initializer := init' }

/-! ## Phase 2: Build refToDef map from the resolved program -/

/-- Insert a definition into the refToDef map using the ID already on the identifier. -/
private def register (map : Std.HashMap Nat ResolvedNode) (iden : Identifier) (node : ResolvedNode)
    : Std.HashMap Nat ResolvedNode :=
  match iden.uniqueId with
  | some uuid => map.insert uuid node
  | none => map  -- shouldn't happen after Phase 1

private def collectHighType (map : Std.HashMap Nat ResolvedNode) (ty : HighTypeMd)
    : Std.HashMap Nat ResolvedNode :=
  match ty with
  | AstNode.mk val _ =>
  match val with
  | .TTypedField vt => collectHighType map vt
  | .TSet et => collectHighType map et
  | .TMap kt vt =>
    let map := collectHighType map kt
    collectHighType map vt
  | .TSeq et => collectHighType map et
  | .TArray et => collectHighType map et
  | .Applied base args =>
    let map := collectHighType map base
    args.foldl collectHighType map
  | .Pure base => collectHighType map base
  | .Intersection tys => tys.foldl collectHighType map
  | _ => map

private def collectStmtExpr (map : Std.HashMap Nat ResolvedNode) (expr : StmtExprMd)
    : Std.HashMap Nat ResolvedNode :=
  match expr with
  | AstNode.mk val _ =>
  match val with
  | .IfThenElse cond thenBr elseBr =>
    let map := collectStmtExpr map cond
    let map := collectStmtExpr map thenBr
    match elseBr with
    | some e => collectStmtExpr map e
    | none => map
  | .Block stmts _ => stmts.foldl collectStmtExpr map
  | .LocalVariable name ty init =>
    let map := register map name (.var name ty)
    let map := collectHighType map ty
    match init with
    | some i => collectStmtExpr map i
    | none => map
  | .While cond invs dec body =>
    let map := collectStmtExpr map cond
    let map := invs.foldl collectStmtExpr map
    let map := match dec with | some d => collectStmtExpr map d | none => map
    collectStmtExpr map body
  | .Return val => match val with | some v => collectStmtExpr map v | none => map
  | .Identifier _ => map
  | .Assign targets value =>
    let map := targets.foldl collectStmtExpr map
    collectStmtExpr map value
  | .FieldSelect target _ => collectStmtExpr map target
  | .PureFieldUpdate target _ newVal =>
    let map := collectStmtExpr map target
    collectStmtExpr map newVal
  | .StaticCall _ args => args.foldl collectStmtExpr map
  | .PrimitiveOp _ args => args.foldl collectStmtExpr map
  | .ReferenceEquals lhs rhs =>
    let map := collectStmtExpr map lhs
    collectStmtExpr map rhs
  | .AsType target ty =>
    let map := collectStmtExpr map target
    collectHighType map ty
  | .IsType target ty =>
    let map := collectStmtExpr map target
    collectHighType map ty
  | .InstanceCall target _ args =>
    let map := collectStmtExpr map target
    args.foldl collectStmtExpr map
  | .Quantifier _ param trigger body =>
    let map := register map param.name (.quantifierVar param.name param.type)
    let map := collectHighType map param.type
    let map := match trigger with | some t => collectStmtExpr map t | none => map
    collectStmtExpr map body
  | .Assigned name => collectStmtExpr map name
  | .Old val => collectStmtExpr map val
  | .Fresh val => collectStmtExpr map val
  | .Assert ⟨cond, _⟩ => collectStmtExpr map cond
  | .Assume cond => collectStmtExpr map cond
  | .ProveBy val proof =>
    let map := collectStmtExpr map val
    collectStmtExpr map proof
  | .ContractOf _ fn => collectStmtExpr map fn
  | .Subscript target index update =>
    let map := collectStmtExpr map target
    let map := collectStmtExpr map index
    match update with
    | some u => collectStmtExpr map u
    | none => map
  | .New _ | .This | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .Abstract | .All | .Hole _ _ => map

private def collectBody (map : Std.HashMap Nat ResolvedNode) (body : Body)
    : Std.HashMap Nat ResolvedNode :=
  match body with
  | .Transparent b => collectStmtExpr map b
  | .Opaque posts impl mods =>
    let map := posts.foldl (fun map c => collectStmtExpr map c.condition) map
    let map := match impl with | some i => collectStmtExpr map i | none => map
    mods.foldl collectStmtExpr map
  | .Abstract posts => posts.foldl (fun map c => collectStmtExpr map c.condition) map
  | .External => map

private def collectParameter (map : Std.HashMap Nat ResolvedNode) (param : Parameter)
    : Std.HashMap Nat ResolvedNode :=
  let map := register map param.name (.parameter param)
  collectHighType map param.type

private def collectProcedure (map : Std.HashMap Nat ResolvedNode) (proc : Procedure)
    (mkNode : Procedure → ResolvedNode) : Std.HashMap Nat ResolvedNode :=
  let map := register map proc.name (mkNode proc)
  let map := proc.inputs.foldl collectParameter map
  let map := proc.outputs.foldl collectParameter map
  let map := proc.preconditions.foldl (fun map c => collectStmtExpr map c.condition) map
  let map := match proc.decreases with | some d => collectStmtExpr map d | none => map
  collectBody map proc.body

private def collectField (map : Std.HashMap Nat ResolvedNode) (ownerName : Identifier) (field : Field)
    : Std.HashMap Nat ResolvedNode :=
  let map := register map field.name (.field ownerName field)
  collectHighType map field.type

private def collectTypeDefinition (map : Std.HashMap Nat ResolvedNode) (td : TypeDefinition)
    : Std.HashMap Nat ResolvedNode :=
  match td with
  | .Composite ct =>
    let map := register map ct.name (.compositeType ct)
    let map := ct.fields.foldl (collectField · ct.name ·) map
    ct.instanceProcedures.foldl (collectProcedure · · (.instanceProcedure ct.name ·)) map
  | .Constrained ct =>
    let map := register map ct.name (.constrainedType ct)
    let map := collectHighType map ct.base
    let map := collectStmtExpr map ct.constraint
    collectStmtExpr map ct.witness
  | .Datatype dt =>
    let map := register map dt.name (.datatypeDefinition dt)
    dt.constructors.foldl (fun map ctor =>
      let map := register map ctor.name (.datatypeConstructor dt.name ctor)
      ctor.args.foldl (fun map p =>
        let map := register map p.name (.parameter p)
        collectHighType map p.type
      ) map
    ) map
  | .Alias ta =>
    let map := register map ta.name (.typeAlias ta)
    collectHighType map ta.target

private def collectConstant (map : Std.HashMap Nat ResolvedNode) (c : Constant)
    : Std.HashMap Nat ResolvedNode :=
  let map := register map c.name (.constant c)
  let map := collectHighType map c.type
  match c.initializer with
  | some init => collectStmtExpr map init
  | none => map

/-- Build the refToDef map by walking the fully-resolved program (Phase 2). -/
def buildRefToDef (program : Program) : Std.HashMap Nat ResolvedNode :=
  let map : Std.HashMap Nat ResolvedNode := {}
  let map := program.types.foldl collectTypeDefinition map
  let map := program.constants.foldl collectConstant map
  let map := program.staticFields.foldl (collectField · "$static" ·) map
  program.staticProcedures.foldl (collectProcedure · · .staticProcedure) map

/-! ## Pre-registration: populate scope with all top-level names before resolving bodies -/

/-- Pre-register all top-level names into scope so that declaration order doesn't matter.
    This assigns fresh IDs and adds placeholder scope entries for:
    - Type names (composite, constrained, datatype) and their constructors/destructors/fields
    - Constant names
    - Static procedure names -/
private def preRegisterTopLevel (program : Program) : ResolveM Unit := do
  -- Pre-register type definitions
  for td in program.types do
    match td with
    | .Composite ct =>
      let _ ← defineNameCheckDup ct.name (.compositeType ct)
      for field in ct.fields do
        let qualifiedName := ct.name.text ++ "." ++ field.name.text
        let _ ← defineNameCheckDup field.name (.field ct.name field) (some qualifiedName)
      for proc in ct.instanceProcedures do
        let _ ← defineNameCheckDup proc.name (.instanceProcedure ct.name proc)
    | .Constrained ct =>
      let _ ← defineNameCheckDup ct.name (.constrainedType ct)
    | .Datatype dt =>
      let _ ← defineNameCheckDup dt.name (.datatypeDefinition dt)
      for ctor in dt.constructors do
        _ ← defineNameCheckDup ctor.name (.datatypeConstructor dt.name ctor) (some (dt.testerName ctor))
        let _ ← defineNameCheckDup ctor.name (.datatypeConstructor dt.name ctor)
        for p in ctor.args do
          let _ ← defineNameCheckDup p.name (.parameter p) (some (dt.destructorName p))
          -- unsafeDestructorId
          let _ ← defineNameCheckDup p.name (.parameter p) (some (dt.unsafeDestructorName p))
    | .Alias ta =>
      let _ ← defineNameCheckDup ta.name (.typeAlias ta)
  -- Pre-register constants
  for c in program.constants do
    let _ ← defineNameCheckDup c.name (.constant c)
  -- Pre-register static procedures
  for proc in program.staticProcedures do
    let _ ← defineNameCheckDup proc.name (.staticProcedure proc)

/-! ## Entry point -/

/-- Run the full resolution pass on a Laurel program. -/
def resolve (program : Program) (existingModel: Option SemanticModel := none) : ResolutionResult :=
  -- Phase 1: pre-register all top-level names, then assign IDs and resolve references
  let phase1 : ResolveM Program := do
    preRegisterTopLevel program
    let types' ← program.types.mapM resolveTypeDefinition
    let constants' ← program.constants.mapM resolveConstant
    let staticFields' ← program.staticFields.mapM (resolveField "$static")
    let staticProcs' ← program.staticProcedures.mapM resolveProcedure
    return { staticProcedures := staticProcs', staticFields := staticFields',
             types := types', constants := constants' }
  let nextId := existingModel.elim 1 (fun m => m.nextId)
  let (program', finalState) := phase1.run { nextId := nextId }
  -- Phase 2: build refToDef from the resolved program (all definitions now have UUIDs)
  let refToDef := buildRefToDef program'
  { program := program',
    model := {
      compositeCount := program.types.length,
      refToDef := refToDef,
      nextId := finalState.nextId
    },
    errors := finalState.errors
  }

end
