/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Util.Tactics

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
and builds a map from each definition's ID to its `AstNode`. Because this
happens after Phase 1, the `AstNode` values in the map contain the fully
resolved sub-trees (e.g. a procedure's parameters already have their IDs).

### Definition nodes (introduce a name into scope)
- `StmtExpr.LocalVariable` — local variable declaration
- `StmtExpr.Forall` / `StmtExpr.Exists` — quantifier-bound variable
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
builds a map from reference IDs to `AstNode` values describing the
definition each reference resolves to.
-/

namespace Strata.Laurel

/-! ## AstNode — the target of a resolved reference -/

/-- A definition-site AST node that a reference can resolve to. -/
inductive AstNode where
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
  /-- A constant. -/
  | constant (c : Constant)
  /-- A quantifier-bound variable. -/
  | quantifierVar (name : Identifier) (type : HighTypeMd)
  | unresolved
  deriving Repr

instance : Inhabited AstNode where
  default := AstNode.unresolved

def AstNode.getType (node: AstNode): Option HighTypeMd := match node with
 | .var _ type => type
 | .parameter p => p.type
 | .field _ f => f.type
 | .datatypeConstructor type _ => some ⟨ .UserDefined type, default ⟩
 | .constant c => c.type
 | .unresolved =>
    -- The Python through Laurel pipeline does not resolve yet
    some ⟨ .UserDefined "dummyName", default ⟩
 | _ => panic! s!"getType called on {repr node}"

/-! ## Resolution result -/

structure SemanticModel where
  nextId: Nat
  compositeCount: Nat
  refToDef: Std.HashMap Nat AstNode
  deriving Repr

def SemanticModel.get (model: SemanticModel) (iden: Identifier): AstNode :=
  match iden.uniqueId with
  | some key => (model.refToDef.get? key).getD (panic! s!"could not find key {key}")
  | none => default -- panic! s!"model.get called on identifier {iden.text} without number"

def SemanticModel.isFunction (model: SemanticModel) (id: Identifier): Bool :=
  if id.uniqueId == none then
    -- The Python pipeline generates constructor/discriminator calls that may not
    -- be resolved at the Laurel level. Treating them as functions keeps them as
    -- expressions; any real errors will be caught during Core type checking.
    -- Make an exception for 'test_helper_procedure' since it's a procedure
    -- We will remove this hack when we enable the Python through Laurel pipeline to correctly resolve
    id.text != "test_helper_procedure"
  else
    match model.get id with
    | .staticProcedure proc => proc.isFunctional
    | .parameter _ => true
    | .datatypeConstructor _ _ => true
    | .constant _ => true
    | node => panic! s!"id: {repr id}, is not a procedure, node {repr node}"

/-- The output of the resolution pass. -/
structure ResolutionResult where
  /-- The program with unique IDs on all definition and reference nodes. -/
  program : Program
  /-- Map from reference node ID to the definition it resolves to. -/
  model : SemanticModel
  /-- Diagnostics collected during resolution (e.g. unresolved references). -/
  errors : Array DiagnosticModel := #[]

/-! ## Phase 1: ID assignment and reference resolution -/

/-- A scope entry stores the definition-site ID and the AstNode for type lookups. -/
abbrev ScopeEntry := Nat × AstNode

/-- Scope maps a name to its definition-site ID and optional AstNode. -/
abbrev Scope := Std.HashMap String ScopeEntry

/-- Per-composite-type scope mapping field names to their scope entries. -/
abbrev TypeScopes := Std.HashMap String Scope

/-- State threaded through the resolution pass. -/
structure ResolveState where
  /-- Next fresh ID to allocate. -/
  nextId : Nat := 1
  /-- Current lexical scope (name → definition ID). -/
  scope : Scope := {}
  /-- Per-composite-type field scopes (type name → field name → scope entry). -/
  typeScopes : TypeScopes := {}
  /-- Diagnostics collected during resolution. -/
  errors : Array DiagnosticModel := #[]

abbrev ResolveM := StateM ResolveState

/-- Allocate a fresh unique ID. -/
private def freshId : ResolveM Nat := do
  let s ← get
  let id := s.nextId
  set { s with nextId := id + 1 }
  return id

/-- Register a definition: assign a fresh ID to the identifier and record it in scope with its AstNode. -/
def defineName (iden : Identifier) (node : AstNode) (overrideResolutionName: Option String := none) : ResolveM Identifier := do
  let resolutionName := overrideResolutionName.getD iden.text
  let name' ← if iden.uniqueId == none then
    let id ← freshId
    pure { iden with uniqueId := some (id) }
  else
    pure iden

  modify fun s => { s with scope := s.scope.insert resolutionName (name'.uniqueId.getD (panic "key was just inserted"), node) }
  return name'

/-- Resolve a reference: look up the name in scope and assign the definition's ID.
    Returns the identifier with its ID filled in. -/
def resolveRef (name : Identifier) (md : Imperative.MetaData Core.Expression := .empty) : ResolveM Identifier := do
  let s ← get
  match s.scope.get? name.text with
  | some (defId, _) =>
    let name' := { name with uniqueId := some defId }
    return name'
  | none =>
    let diag := md.toDiagnostic s!"Resolution failed: '{name}' is not defined"
    modify fun s => { s with errors := s.errors.push diag }
    return { name with uniqueId := none }

/-- Extract the UserDefined type name from a resolved target expression by looking up its scope entry. -/
private def targetTypeName (target : StmtExprMd) : ResolveM (Option String) := do
  let s ← get
  match target.val with
  | .Identifier ref =>
    match s.scope.get? ref.text with
    | some (_, node) =>
      match node.getType with
      | some ty =>
        match ty.val with
        | .UserDefined typRef => pure (some typRef.text)
        | _ => pure none
      | none => pure none
    | none => pure none
  | _ => pure none

/-- Resolve a field reference using the target's type to build a qualified lookup key.
    Falls back to unqualified lookup if the target type cannot be determined. -/
def resolveFieldRef (target : StmtExprMd) (fieldName : Identifier)
    (md : Imperative.MetaData Core.Expression) : ResolveM Identifier := do
  let typeName? ← targetTypeName target
  match typeName? with
  | some typeName =>
    let s ← get
    match s.typeScopes.get? typeName with
    | some typeScope =>
      match typeScope.get? fieldName.text with
      | some (defId, _) => return { fieldName with uniqueId := some defId }
      | none => resolveRef fieldName md
    | none => resolveRef fieldName md
  | none => resolveRef fieldName md

/-- Save and restore scope around a block (for lexical scoping). -/
def withScope (action : ResolveM α) : ResolveM α := do
  let savedScope := (← get).scope
  let result ← action
  modify fun s => { s with scope := savedScope }
  return result

/-! ## AST traversal (Phase 1) -/


def resolveHighType (ty : HighTypeMd) : ResolveM HighTypeMd := do
  match ty with
  | WithMetadata.mk val _ =>
  let val' ← match val with
  | .UserDefined ref =>
    let ref' ← resolveRef ref ty.md
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
  return ⟨val', ty.md⟩

def resolveStmtExpr (exprMd : StmtExprMd) : ResolveM StmtExprMd := do
  match _: exprMd with
  | WithMetadata.mk expr md =>
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
    let name' ← defineName name (.var name ty')
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
  | .Identifier ref =>
    let ref' ← resolveRef ref md
    pure (.Identifier ref')
  | .Assign targets value =>
    let targets' ← targets.mapM resolveStmtExpr
    let value' ← resolveStmtExpr value
    pure (.Assign targets' value')
  | .FieldSelect target fieldName =>
    let target' ← resolveStmtExpr target
    let fieldName' ← resolveFieldRef target' fieldName md
    pure (.FieldSelect target' fieldName')
  | .PureFieldUpdate target fieldName newVal =>
    let target' ← resolveStmtExpr target
    let fieldName' ← resolveFieldRef target' fieldName md
    let newVal' ← resolveStmtExpr newVal
    pure (.PureFieldUpdate target' fieldName' newVal')
  | .StaticCall callee args =>
    let callee' ← resolveRef callee md
    let args' ← args.mapM resolveStmtExpr
    pure (.StaticCall callee' args')
  | .PrimitiveOp op args =>
    let args' ← args.mapM resolveStmtExpr
    pure (.PrimitiveOp op args')
  | .New ref =>
    let ref' ← resolveRef ref md
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
    let callee' ← resolveRef callee md
    let args' ← args.mapM resolveStmtExpr
    pure (.InstanceCall target' callee' args')
  | .Forall param body =>
    withScope do
      let paramTy' ← resolveHighType param.type
      let paramName' ← defineName param.name (.quantifierVar param.name paramTy')
      let body' ← resolveStmtExpr body
      pure (.Forall ⟨paramName', paramTy'⟩ body')
  | .Exists param body =>
    withScope do
      let paramTy' ← resolveHighType param.type
      let paramName' ← defineName param.name (.quantifierVar param.name paramTy')
      let body' ← resolveStmtExpr body
      pure (.Exists ⟨paramName', paramTy'⟩ body')
  | .Assigned name =>
    let name' ← resolveStmtExpr name
    pure (.Assigned name')
  | .Old val =>
    let val' ← resolveStmtExpr val
    pure (.Old val')
  | .Fresh val =>
    let val' ← resolveStmtExpr val
    pure (.Fresh val')
  | .Assert cond =>
    let cond' ← resolveStmtExpr cond
    pure (.Assert cond')
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
  | .Hole => pure .Hole
  return ⟨val', md⟩
  termination_by exprMd
  decreasing_by all_goals term_by_mem

/-- Resolve a parameter: assign a fresh ID and add to scope. -/
def resolveParameter (param : Parameter) : ResolveM Parameter := do
  let ty' ← resolveHighType param.type
  let name' ← defineName param.name (.parameter ⟨param.name, ty'⟩)
  return ⟨name', ty'⟩

/-- Resolve a procedure body. -/
def resolveBody (body : Body) : ResolveM Body := do
  match body with
  | .Transparent b =>
    let b' ← resolveStmtExpr b
    return .Transparent b'
  | .Opaque posts impl mods =>
    let posts' ← posts.mapM resolveStmtExpr
    let impl' ← impl.mapM resolveStmtExpr
    let mods' ← mods.mapM resolveStmtExpr
    return .Opaque posts' impl' mods'
  | .Abstract posts =>
    let posts' ← posts.mapM resolveStmtExpr
    return .Abstract posts'
  | .External => return .External

/-- Resolve a determinism clause. -/
def resolveDeterminism (d : Determinism) : ResolveM Determinism := do
  match d with
  | .deterministic reads =>
    let reads' ← reads.mapM resolveStmtExpr
    return .deterministic reads'
  | .nondeterministic => return .nondeterministic

/-- Resolve a procedure: define its name, then resolve params, contracts, and body in a new scope. -/
def resolveProcedure (proc : Procedure) : ResolveM Procedure := do
  let procName' ← defineName proc.name (.staticProcedure proc)
  withScope do
    let inputs' ← proc.inputs.mapM resolveParameter
    let outputs' ← proc.outputs.mapM resolveParameter
    let pres' ← proc.preconditions.mapM resolveStmtExpr
    let det' ← resolveDeterminism proc.determinism
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let body' ← resolveBody proc.body
    return { name := procName', inputs := inputs', outputs := outputs',
             isFunctional := proc.isFunctional,
             preconditions := pres', determinism := det', decreases := dec',
             body := body', md := proc.md }

/-- Resolve a field: define its name under the qualified key (OwnerType.fieldName) and resolve its type. -/
def resolveField (ownerName : Identifier) (field : Field) : ResolveM Field := do
  let ty' ← resolveHighType field.type
  let qualifiedName := ownerName.text ++ "." ++ field.name.text
  let name' ← defineName field.name (.field ownerName { field with type := ty' }) (some qualifiedName)
  return { name := name', isMutable := field.isMutable, type := ty' }

/-- Resolve an instance procedure on a composite type. -/
def resolveInstanceProcedure (typeName : Identifier) (proc : Procedure) : ResolveM Procedure := do
  let procName' ← defineName proc.name (.instanceProcedure typeName proc)
  withScope do
    let inputs' ← proc.inputs.mapM resolveParameter
    let outputs' ← proc.outputs.mapM resolveParameter
    let pres' ← proc.preconditions.mapM resolveStmtExpr
    let det' ← resolveDeterminism proc.determinism
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let body' ← resolveBody proc.body
    return { name := procName', inputs := inputs', outputs := outputs',
             isFunctional := proc.isFunctional,
             preconditions := pres', determinism := det', decreases := dec',
             body := body', md := proc.md }

/-- Resolve a type definition. -/
def resolveTypeDefinition (td : TypeDefinition) : ResolveM TypeDefinition := do
  match td with
  | .Composite ct =>
    let ctName' ← defineName ct.name (.compositeType ct)
    let extending' ← ct.extending.mapM (resolveRef · .empty)
    let fields' ← ct.fields.mapM (resolveField ctName')
    let instProcs' ← ct.instanceProcedures.mapM (resolveInstanceProcedure ctName')
    -- Build per-type scope: start with inherited fields from parents, then add own fields
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
    return .Composite { name := ctName', extending := extending',
                        fields := fields', instanceProcedures := instProcs' }
  | .Constrained ct =>
    let ctName' ← defineName ct.name (.constrainedType ct)
    let base' ← resolveHighType ct.base
    let constraint' ← resolveStmtExpr ct.constraint
    let witness' ← resolveStmtExpr ct.witness
    return .Constrained { name := ctName', base := base', valueName := ct.valueName,
                          constraint := constraint', witness := witness' }
  | .Datatype dt =>
    let dtName' ← defineName dt.name (.datatypeDefinition dt)
    let ctors' ← dt.constructors.mapM fun ctor => do
      let ctorName' ← defineName ctor.name (.datatypeConstructor dt.name ctor)
      let args' ← ctor.args.mapM fun (p: Parameter) => do
        let ty' ← resolveHighType p.type
        let destructorId ← defineName p.name (.parameter p) (some $ dt.name.text ++ ".." ++ p.name.text)
        return ⟨ destructorId, ty' ⟩
      return { name := ctorName', args := args' : DatatypeConstructor }
    return .Datatype { name := dtName', typeArgs := dt.typeArgs, constructors := ctors' }

/-- Resolve a constant definition. -/
def resolveConstant (c : Constant) : ResolveM Constant := do
  let ty' ← resolveHighType c.type
  let init' ← c.initializer.mapM resolveStmtExpr
  let name' ← defineName c.name (.constant c)
  return { name := name', type := ty', initializer := init' }

/-! ## Phase 2: Build refToDef map from the resolved program -/

/-- Insert a definition into the refToDef map using the ID already on the identifier. -/
private def register (map : Std.HashMap Nat AstNode) (iden : Identifier) (node : AstNode)
    : Std.HashMap Nat AstNode :=
  match iden.uniqueId with
  | some uuid => map.insert uuid node
  | none => map  -- shouldn't happen after Phase 1

private def collectHighType (map : Std.HashMap Nat AstNode) (ty : HighTypeMd)
    : Std.HashMap Nat AstNode :=
  match ty with
  | WithMetadata.mk val _ =>
  match val with
  | .TTypedField vt => collectHighType map vt
  | .TSet et => collectHighType map et
  | .TMap kt vt =>
    let map := collectHighType map kt
    collectHighType map vt
  | .Applied base args =>
    let map := collectHighType map base
    args.foldl collectHighType map
  | .Pure base => collectHighType map base
  | .Intersection tys => tys.foldl collectHighType map
  | _ => map

private def collectStmtExpr (map : Std.HashMap Nat AstNode) (expr : StmtExprMd)
    : Std.HashMap Nat AstNode :=
  match expr with
  | WithMetadata.mk val _ =>
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
  | .Forall param body =>
    let map := register map param.name (.quantifierVar param.name param.type)
    let map := collectHighType map param.type
    collectStmtExpr map body
  | .Exists param body =>
    let map := register map param.name (.quantifierVar param.name param.type)
    let map := collectHighType map param.type
    collectStmtExpr map body
  | .Assigned name => collectStmtExpr map name
  | .Old val => collectStmtExpr map val
  | .Fresh val => collectStmtExpr map val
  | .Assert cond => collectStmtExpr map cond
  | .Assume cond => collectStmtExpr map cond
  | .ProveBy val proof =>
    let map := collectStmtExpr map val
    collectStmtExpr map proof
  | .ContractOf _ fn => collectStmtExpr map fn
  | .New _ | .This | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _
  | .Abstract | .All | .Hole => map

private def collectBody (map : Std.HashMap Nat AstNode) (body : Body)
    : Std.HashMap Nat AstNode :=
  match body with
  | .Transparent b => collectStmtExpr map b
  | .Opaque posts impl mods =>
    let map := posts.foldl collectStmtExpr map
    let map := match impl with | some i => collectStmtExpr map i | none => map
    mods.foldl collectStmtExpr map
  | .Abstract posts => posts.foldl collectStmtExpr map
  | .External => map

private def collectDeterminism (map : Std.HashMap Nat AstNode) (d : Determinism)
    : Std.HashMap Nat AstNode :=
  match d with
  | .deterministic (some reads) => collectStmtExpr map reads
  | _ => map

private def collectParameter (map : Std.HashMap Nat AstNode) (param : Parameter)
    : Std.HashMap Nat AstNode :=
  let map := register map param.name (.parameter param)
  collectHighType map param.type

private def collectProcedure (map : Std.HashMap Nat AstNode) (proc : Procedure)
    (mkNode : Procedure → AstNode) : Std.HashMap Nat AstNode :=
  let map := register map proc.name (mkNode proc)
  let map := proc.inputs.foldl collectParameter map
  let map := proc.outputs.foldl collectParameter map
  let map := proc.preconditions.foldl collectStmtExpr map
  let map := collectDeterminism map proc.determinism
  let map := match proc.decreases with | some d => collectStmtExpr map d | none => map
  collectBody map proc.body

private def collectField (map : Std.HashMap Nat AstNode) (ownerName : Identifier) (field : Field)
    : Std.HashMap Nat AstNode :=
  let map := register map field.name (.field ownerName field)
  collectHighType map field.type

private def collectTypeDefinition (map : Std.HashMap Nat AstNode) (td : TypeDefinition)
    : Std.HashMap Nat AstNode :=
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

private def collectConstant (map : Std.HashMap Nat AstNode) (c : Constant)
    : Std.HashMap Nat AstNode :=
  let map := register map c.name (.constant c)
  let map := collectHighType map c.type
  match c.initializer with
  | some init => collectStmtExpr map init
  | none => map

/-- Build the refToDef map by walking the fully-resolved program (Phase 2). -/
def buildRefToDef (program : Program) : Std.HashMap Nat AstNode :=
  let map : Std.HashMap Nat AstNode := {}
  let map := program.types.foldl collectTypeDefinition map
  let map := program.constants.foldl collectConstant map
  let map := program.staticFields.foldl (collectField · "$static" ·) map
  program.staticProcedures.foldl (collectProcedure · · .staticProcedure) map

/-! ## Pre-registration: populate scope with all top-level names before resolving bodies -/

/-- A default AstNode used as a placeholder during pre-registration.
    It will be overwritten with the real node when the definition is fully resolved. -/
private def placeholderNode : AstNode := .var "$placeholder" ⟨.TVoid, #[]⟩

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
      let _ ← defineName ct.name (.compositeType ct)
      for field in ct.fields do
        let qualifiedName := ct.name.text ++ "." ++ field.name.text
        let _ ← defineName field.name placeholderNode (some qualifiedName)
      for proc in ct.instanceProcedures do
        let _ ← defineName proc.name placeholderNode
    | .Constrained ct =>
      let _ ← defineName ct.name (.constrainedType ct)
    | .Datatype dt =>
      let _ ← defineName dt.name (.datatypeDefinition dt)
      for ctor in dt.constructors do
        let _ ← defineName ctor.name (.datatypeConstructor dt.name ctor)
        for p in ctor.args do
          let _ ← defineName p.name placeholderNode (some $ dt.name.text ++ ".." ++ p.name.text)
  -- Pre-register constants
  for c in program.constants do
    let _ ← defineName c.name (.constant c)
  -- Pre-register static procedures
  for proc in program.staticProcedures do
    let _ ← defineName proc.name (.staticProcedure proc)

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
