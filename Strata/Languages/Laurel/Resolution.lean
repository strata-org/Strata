/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
import Strata.Util.Tactics
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

/-!
# Name Resolution Pass

Turns a freshly parsed Laurel `Program` (where every `Identifier` has
`uniqueId := none`) into a program where every definition has a fresh numeric
ID and every reference points to the ID of the definition it names. The pass
also synthesizes a `HighType` for every `StmtExpr` and emits diagnostics for
unresolved names, duplicate definitions, kind mismatches (e.g. using a
constant where a type is expected), and type mismatches.

The entry point is `resolve`. It returns a `ResolutionResult` containing the
resolved program, a `SemanticModel` (the `refToDef` map and ID counters), and
the accumulated diagnostics.

## Design

The resolution pass operates in two phases.

### Phase 1: ID Assignment and Reference Resolution

Walks the AST under `ResolveM`, a state monad over `ResolveState`. Phase 1:
- assigns fresh unique IDs to all definition nodes via `defineNameCheckDup`,
- resolves references by looking up names in the current lexical scope via
  `resolveRef` (and `resolveFieldRef` for fields, which uses the target's
  declared type to build a qualified lookup key),
- opens fresh nested scopes via `withScope` for blocks, quantifiers,
  procedure bodies, and constrained-type constraint/witness expressions,
- synthesizes a `HighType` for every `StmtExpr` and checks it (via
  `Check.resolveStmtExpr` for fresh subexpressions, or `checkSubtype` when a type is
  already in hand) on assignments, call arguments, condition positions,
  functional bodies, and constant initializers.

Before any bodies are walked, `preRegisterTopLevel` registers every top-level
name (types and their constructors / testers / destructors / instance
procedures / fields, constants, static procedures) into scope with a
placeholder `ResolvedNode`. The placeholders are overwritten with real nodes
as each definition is fully resolved. This is what allows declaration order to
not matter inside a Laurel program.

When a reference fails to resolve, or a `UserDefined` type reference resolves
to the wrong kind, Phase 1 records the name as `ResolvedNode.unresolved` (or
the type as `HighType.Unknown`) and continues. Both are treated as wildcards
by the type checker, so subsequent uses do not produce cascading errors.

After this phase, every definition and reference node has its `uniqueId`
field filled in.

### Phase 2: Build refToDef Map

Walks the *resolved* AST (where all definitions already have their UUIDs)
and builds a map from each definition's ID to its `ResolvedNode`. Because
this happens after Phase 1, the `ResolvedNode` values in the map contain the
fully resolved sub-trees (e.g. a procedure's parameters already have their
IDs).

### Scopes

Three forms of scope are maintained on `ResolveState`:
- `scope` — the current lexical scope, mapping name → `(uniqueId, ResolvedNode)`,
  saved and restored by `withScope`.
- `currentScopeNames` — names defined at the current nesting level only, used
  by `defineNameCheckDup` to detect duplicates.
- `typeScopes` — per-composite-type scopes mapping field names to scope
  entries. Built by `resolveTypeDefinition` *before* descending into instance
  procedures (and inheriting from `extending` parents), so that field
  references inside method bodies can be resolved.
- `instanceTypeName` — when resolving inside an instance procedure, the
  owning composite type's name. Used by `resolveFieldRef` as a fallback so
  that a bare `self.field` reference resolves through the type scope when
  `self` has type `Any`.

### Definition nodes (introduce a name into scope)
- `Variable.Declare` — local variable declaration (in `Assign` targets or `Var`)
- `StmtExpr.Quantifier` — quantifier-bound variable
- `Parameter` — procedure parameter
- `Procedure` — procedure definition
- `Field` — field on a composite type
- `CompositeType` / `ConstrainedType` / `DatatypeDefinition` — type definitions
- `DatatypeConstructor` — datatype constructor
- `Constant` — named constant

### Reference nodes (use a name)
- `StmtExpr.Var (.Local ...)` — variable reference
- `StmtExpr.StaticCall` — static procedure call
- `StmtExpr.InstanceCall` — instance method call
- `StmtExpr.Var (.Field ...)` — field access
- `StmtExpr.New` — object creation (references a type)
- `StmtExpr.Exit` — exit a labelled block
- `HighType.UserDefined` — type reference

Each of these nodes carries a `uniqueId : Option Nat` field (defaulting to
`none`). Phase 1 fills in unique values; Phase 2 then builds a map from
reference IDs to `ResolvedNode` values describing the definition each
reference resolves to.
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
  | datatypeDestructor
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
  | .datatypeDestructor => "datatype destructor"
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
  /-- An auto-generated destructor (or unsafe `!`-destructor) for a datatype field.
      `typeName` is the resolved Identifier of the parent datatype (with its
      `uniqueId`), and `field` is the underlying constructor parameter. -/
  | datatypeDestructor (typeName : Identifier) (field : Parameter)
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
  | .datatypeDestructor .. => .datatypeDestructor
  | .typeAlias ..         => .typeAlias
  | .constant ..          => .constant
  | .quantifierVar ..     => .quantifierVar
  | .unresolved _          => .unresolved

def ResolvedNode.getType (node: ResolvedNode): HighTypeMd := match node with
 | .var _ type => type
 | .parameter p => p.type
 | .field _ f => f.type
 | .datatypeConstructor type _ => ⟨ .UserDefined type, none ⟩
 | .datatypeDestructor _ fld => fld.type
 | .constant c => c.type
 | .quantifierVar _ type => type
 | .unresolved source => ⟨ .Unknown, source ⟩
 | .staticProcedure _ | .instanceProcedure _ _ | .compositeType _
 | .constrainedType _ | .datatypeDefinition _ | .typeAlias _ => ⟨ .Unknown, none ⟩

/-! ## Resolution result -/

structure SemanticModel where
  nextId: Nat
  compositeCount: Nat
  private refToDef: Std.HashMap Nat ResolvedNode
  deriving Repr

/-- Look up the resolved node for an identifier, returning `none` if the identifier
    has no `uniqueId` or is not in the model. -/
def SemanticModel.get? (model: SemanticModel) (iden: Identifier): Option ResolvedNode :=
  iden.uniqueId.bind model.refToDef.get?

def SemanticModel.get (model: SemanticModel) (iden: Identifier): ResolvedNode :=
  (model.get? iden).getD default

def SemanticModel.isFunction (model: SemanticModel) (id: Identifier): Bool :=
  match model.get id with
      | .staticProcedure proc => proc.isFunctional
      | .parameter _ => true
      | .datatypeConstructor _ _ => true
      | .datatypeDestructor _ _ => true
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
  /-- Map from definition uniqueId to its ResolvedNode. Populated alongside
      `scope` whenever a definition is registered. Unlike `scope`, this map is
      *not* saved/restored by `withScope` — uniqueIds are global. Used by
      `getVarType` to look up types for references whose `text` doesn't match
      a scope key (notably fields, which are scoped under qualified keys). -/
  idToNode : Std.HashMap Nat ResolvedNode := {}
  /-- Names defined at the current scope level (for duplicate detection). -/
  currentScopeNames : Std.HashSet String := {}
  /-- Per-composite-type field scopes (type name → field name → scope entry). -/
  typeScopes : TypeScopes := {}
  /-- Labels of enclosing labeled blocks, used by `Check.exit` to validate
      that an `exit l` targets an in-scope label. Maintained as a separate
      namespace (not part of `scope`) because labels are referenced by raw
      string, not by `uniqueId`. -/
  labelScope : Std.HashSet String := {}
  /-- Diagnostics collected during resolution. -/
  errors : Array DiagnosticModel := #[]
  /-- When resolving inside an instance procedure, the owning composite type name.
      Used by `resolveFieldRef` to resolve `self.field` when `self` has type `Any`. -/
  instanceTypeName : Option String := none
  /-- The declared output types of the enclosing procedure body, in
      declaration order. `none` means we are not currently resolving
      inside any procedure body (e.g. while resolving a constant
      initializer); in that case `Return` cannot occur and is not
      type-checked. Bound by `resolveProcedure` /
      `resolveInstanceProcedure` on entry, restored on exit, and read
      only by `Check.return` to type-check the optional payload of
      `return e`. -/
  answerType : Option (List HighTypeMd) := none
  /-- Type-relation tables (alias/constrained unfolding + composite extending
      chains) used by the subtyping/consistency checks. Built once from
      `program.types` at the start of `resolve`. -/
  typeContext : TypeContext := {}

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

    modify fun s => { s with
      scope := s.scope.insert resolutionName (uniqueId, node),
      idToNode := s.idToNode.insert uniqueId node,
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
  | .Var (.Local ref) =>
    match s.scope.get? ref.text with
    | some (_, node) =>
      match node.getType.val with
      | .UserDefined typRef => pure (some typRef.text)
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

/-- Run `action` with `label` (if any) added to `labelScope`, restoring the
    previous label scope on exit. Used by `Check.block` so that `Check.exit`
    can validate that `exit l` targets an enclosing labeled block. -/
def withLabel (label : Option String) (action : ResolveM α) : ResolveM α := do
  let savedLabels := (← get).labelScope
  if let some l := label then
    modify fun s => { s with labelScope := s.labelScope.insert l }
  let result ← action
  modify fun s => { s with labelScope := savedLabels }
  return result

/-! ## AST traversal (Phase 1) -/


def resolveHighType (ty : HighTypeMd) : ResolveM HighTypeMd := do
  match ty with
  | AstNode.mk val _ =>
  let val' ← match val with
  | .UserDefined ref =>
    let ref' ← resolveRef ref ty.source
      (expected := #[.compositeType, .constrainedType, .datatypeDefinition, .typeAlias])
    -- If the reference resolved to the wrong kind, treat the type as Unknown to avoid cascading errors
    let s ← get
    let kindOk : Bool := match s.scope.get? ref.text with
      | some (_, node) => node.kind == .unresolved ||
          (#[ResolvedNodeKind.compositeType, .constrainedType, .datatypeDefinition, .typeAlias].contains node.kind)
      | none => true  -- unresolved references already reported
    if kindOk then pure (HighType.UserDefined ref')
    else pure HighType.Unknown
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
  | .MultiValuedExpr tys =>
    let tys' ← tys.mapM resolveHighType
    pure (.MultiValuedExpr tys')
  | other => pure other
  return { val := val', source := ty.source }

/-- Format a type for use in diagnostics. -/
private def formatType (ty : HighTypeMd) : String :=
  match ty.val with
  | .MultiValuedExpr tys =>
    let parts := tys.map (fun t => toString (formatHighTypeVal t.val))
    "(" ++ ", ".intercalate parts ++ ")"
  | other => toString (formatHighTypeVal other)

/-- Emit a type mismatch diagnostic. With a `construct`, the message is
    "'<construct.constrName>' <problem>, got '<actual>'"; without,
    "<problem>, got '<actual>'". When `actual` is `Unknown` the trailing
    `got '…'` is dropped — "we couldn't synthesize a type" is the
    statement, not "the type we got was Unknown". -/
private def typeMismatch (source : Option FileRange) (construct : Option StmtExpr)
    (problem : String) (actual : HighTypeMd) : ResolveM Unit := do
  let constructor := match construct with
    | some c => s!"'{c.constrName}' "
    | none   => ""
  let suffix := match actual.val with
    | .Unknown => ""
    | _        => s!", got '{formatType actual}'"
  let diag := diagnosticFromSource source s!"{constructor}{problem}{suffix}"
  modify fun s => { s with errors := s.errors.push diag }

/-- Type-level subtype check: emits the standard "expected/got" diagnostic when
    `actual` is not a consistent subtype of `expected`. Used at sites where the
    actual type is already in hand (assignment, call args, body vs declared
    output) — equivalent to `Check.resolveStmtExpr e expected` but without re-synthesizing. -/
private def checkSubtype (source : Option FileRange) (expected : HighTypeMd) (actual : HighTypeMd) : ResolveM Unit := do
  let ctx := (← get).typeContext
  unless isConsistentSubtype ctx actual expected do
    typeMismatch source none s!"expected '{formatType expected}'" actual

/-- Test whether a type is in the set of numeric primitives. `Unknown` is
    accepted as a gradual escape hatch. Aliases and constrained types are
    unfolded first so e.g. `nat` (constrained over `int`) counts as numeric.
    Used by Op-Cmp / Op-Arith. -/
private def isNumeric (ctx : TypeContext) (ty : HighTypeMd) : Bool :=
  match (ctx.unfold ty).val with
  | .TInt | .TReal | .TFloat64 | .Unknown => true
  | _ => false

/-- Least upper bound of two types under the consistency relation
    (Siek–Taha). On Laurel's flat lattice the LUB collapses to the
    "more informative" side: `Unknown` and `T` yields `T`; equal
    types (after unfolding) yield themselves; everything else is
    inconsistent and yields `none`.

    Used by [⇒] Op-Arith to fold operand types into a single result
    type: a homogeneous arithmetic expression `1 + 2` yields `TInt`,
    `1 + <?>` yields `TInt` (Unknown promotes), `<?> + <?>` yields
    `Unknown`, and `1 + 2.0` is rejected. -/
private def join (ctx : TypeContext)
    (a b : HighTypeMd) : Option HighTypeMd :=
  let a' := ctx.unfold a
  let b' := ctx.unfold b
  match a'.val, b'.val with
  | .Unknown, _ => some b
  | _, .Unknown => some a
  | _, _ => if highEq a' b' then some a else none

/-- Test whether a type is a user-defined reference type. `Unknown` is accepted
    as a gradual escape hatch. Used by Fresh and ReferenceEquals, which only
    make sense on composite/datatype references. -/
private def isReference (ctx : TypeContext) (ty : HighTypeMd) : Bool :=
  match (ctx.unfold ty).val with
  | .UserDefined _ | .Unknown => true
  | _ => false

/-- Get the type of a resolved reference. Prefers the resolved definition by
    `uniqueId` (the post-resolution ground truth, populated as definitions are
    registered and never shadowed): a field reference carries its field's
    `uniqueId`, but its bare `text` may collide with a same-named local in
    `scope`, so a name-keyed lookup would read the shadowing local's type
    instead of the field's. Falls back to a name lookup for references whose
    `uniqueId` is not filled in — notably local loads, which `Synth.varLocal`
    passes here unresolved and which are correctly keyed by `text` — and
    finally to `Unknown`. -/
private def getVarType (ref : Identifier) : ResolveM HighTypeMd := do
  let s ← get
  match ref.uniqueId.bind s.idToNode.get? with
  | some node => pure node.getType
  | none =>
    match s.scope.get? ref.text with
    | some (_, node) => pure node.getType
    | none => pure { val := .Unknown, source := ref.source }

/-- Get the call return type and parameter types for a callee from scope. -/
private def getCallInfo (callee : Identifier) : ResolveM (HighTypeMd × List HighTypeMd) := do
  let s ← get
  match s.scope.get? callee.text with
  | some (_, .staticProcedure proc) =>
    let retTy := match proc.outputs with
      | [singleOutput] => singleOutput.type
      | outputs => { val := .MultiValuedExpr (outputs.map (·.type)), source := none }
    pure (retTy, proc.inputs.map (·.type))
  | some (_, .instanceProcedure _ proc) =>
    let retTy := match proc.outputs with
      | [singleOutput] => singleOutput.type
      | outputs => { val := .MultiValuedExpr (outputs.map (·.type)), source := none }
    pure (retTy, proc.inputs.map (·.type))
  | some (_, .datatypeConstructor t _) =>
    -- Testers (e.g. "Color..isRed") return Bool; constructors return the type
    if (callee.text.splitOn "..is").length > 1 then
      pure ({ val := .TBool, source := callee.source }, [])
    else
      pure ({ val := .UserDefined t, source := callee.source }, [])
  | some (_, .parameter p) => pure (p.type, [])
  | some (_, .constant c) => pure (c.type, [])
  | _ => pure ({ val := .Unknown, source := callee.source }, [])

/-! ## Typing rules

The judgment is bidirectional:

```
Γ ⊢ e ⇒ A          (Synth.resolveStmtExpr)
Γ ⊢ e ⇐ A          (Check.resolveStmtExpr)
```

- `Γ` — lexical scope (variables, fields). Block labels live in a
  separate namespace `Γ_lbl` (`ResolveState.labelScope`), consulted
  only by `Check.exit`.
- `A` — *value type* of the term.

The `Return` rules additionally depend on the enclosing procedure's
declared output-type list, written `T_o-bar` in the rule statements.
That list is bound on entry to a procedure body (by
`resolveProcedure` / `resolveInstanceProcedure`, stored on
`ResolveState.answerType`) and consulted only by `Check.return`;
every other rule is independent of it.

Several constructs are *statements*: their job is to have an effect,
not to produce a value. Their check rules accept whatever type the
surrounding context expects — the rule is written with the expected
type `A` left as a free variable (we call this **check at any `A`**),
which just means the rule does not look at `A` at all. There are two
reasons a construct ignores `A`:

- It is a **control-flow terminator** (`Exit`, `Return`): it jumps
  somewhere else and never hands a value back, so whatever the
  context wanted, the jump satisfies it vacuously. `if c then 5 else
  return` is fine in an `Int` context because the `else` branch never
  produces anything at all.
- It runs and then **falls through without a value** (`Assert`,
  `Assume`, `While`, `Var-Declare`). These conceptually have the unit
  type `TVoid`; accepting any `A` is a slight over-acceptance that is
  harmless in practice because such statements only ever appear in
  non-last (discard) position, which is checked at `TVoid` anyway.

`Assign` is the one statement that *does* produce a value: it
synthesizes the type of its right-hand side (so `x := e` can be used
where that type is expected), and its check rule skips the \[⇐\] Sub
boundary check only when the expected type is `TVoid` — i.e. when the
assignment is used purely for effect. `Block` routes the surrounding
expected type to its last statement (the block's value), not to the
non-last statements (which are effects, checked at `TVoid`).

Each typing rule is implemented as its own helper inside the mutual
block below. Helpers are grouped by section to mirror the *Typing
rules* index in `LaurelDoc.lean`:

- Literals — `Synth.litInt`, `Synth.litBool`, `Synth.litString`, `Synth.litDecimal`
- Variables — `Synth.varLocal`, `Synth.varField`, `Check.varDeclare`
- Control flow — `Check.while`, `Check.exit`, `Check.return`,
  `Check.block`, `Check.ifThenElse`
- Verification statements — `Check.assert`, `Check.assume`
- Assignment — `Synth.assign`, `Check.assign`
- Calls — `Synth.staticCall`, `Synth.instanceCall`
- Primitive operations — `Synth.primitiveOp`, `Check.primitiveOp`
- Object forms — `Synth.new`, `Synth.asType`, `Synth.isType`, `Synth.refEq`,
  `Synth.pureFieldUpdate`
- Verification expressions — `Synth.quantifier`, `Synth.assigned`,
  `Synth.fresh`, `Check.old`, `Check.proveBy`
- Self reference — `Synth.this`
- Untyped forms — `Synth.abstract`, `Synth.all`
- ContractOf — `Synth.contractOf`
- Holes — `Check.holeSome`, `Check.holeNone`

The dispatch functions `Synth.resolveStmtExpr` and `Check.resolveStmtExpr`
pattern-match on the constructor and delegate to the corresponding helper.
`Synth.resolveStmtExpr` is non-total: constructors without a synthesis rule
hit a wildcard arm that emits a diagnostic and returns `Unknown`. -/

namespace Resolution

-- The `h : exprMd.val = .Foo args ...` parameters on the recursive helpers
-- look unused to the linter, but each one is referenced by that helper's
-- `decreasing_by` tactic to relate `sizeOf args` to `sizeOf exprMd`.
set_option linter.unusedVariables false in
mutual

-- ### Dispatch

/-- Synth-mode resolution: resolve `e` and synthesize its `HighType`,
    written `Γ ⊢ e ⇒ T`. Each constructor with a synthesis rule delegates
    to its rule's helper; constructors without one (statement-shaped
    constructs like `IfThenElse`, `Block`, `While`, `Return`, …) hit
    a wildcard arm that emits a `typeMismatch` diagnostic and
    returns `Unknown` to suppress cascading errors.

    Synthesis returns a type inferred from the expression itself;
    checking (`Check.resolveStmtExpr`) verifies that the expression has
    a given expected type. The two functions are mutually recursive,
    with termination on a lexicographic measure `(exprMd, tag)` — tag
    `2` for synth, `3` for check, helpers smaller — so that subsumption
    (which calls synth on the *same* expression) can decrease via
    `Prod.Lex.right`. -/
def Synth.resolveStmtExpr (exprMd : StmtExprMd) : ResolveM (StmtExprMd × HighTypeMd) := do
  match h_node: exprMd with
  | AstNode.mk expr source =>
  let (val', ty) ← match h_expr: expr with
  | .LiteralInt v => pure (Synth.litInt v source)
  | .LiteralBool v => pure (Synth.litBool v source)
  | .LiteralString v => pure (Synth.litString v source)
  | .LiteralDecimal v => pure (Synth.litDecimal v source)
  | .Var (.Local ref) => Synth.varLocal ref source
  | .Var (.Field target fieldName) =>
    Synth.varField exprMd target fieldName source (by rw [h_node])
  | .Assign targets value =>
    Synth.assign exprMd targets value source (by rw [h_node])
  | .PureFieldUpdate target fieldName newVal =>
    Synth.pureFieldUpdate exprMd target fieldName newVal (by rw [h_node])
  | .StaticCall callee args =>
    Synth.staticCall exprMd callee args source (by rw [h_node])
  | .PrimitiveOp op args =>
    Synth.primitiveOp exprMd expr op args source h_expr (by rw [h_node])
  | .New ref => Synth.new ref source
  | .This => Synth.this source
  | .ReferenceEquals lhs rhs =>
    Synth.refEq exprMd expr lhs rhs source h_expr (by rw [h_node])
  | .AsType target ty =>
    Synth.asType exprMd target ty (by rw [h_node])
  | .IsType target ty =>
    Synth.isType exprMd target ty source (by rw [h_node])
  | .InstanceCall target callee args =>
    Synth.instanceCall exprMd target callee args source (by rw [h_node])
  | .Quantifier mode param trigger body =>
    Synth.quantifier exprMd mode param trigger body source (by rw [h_node])
  | .Assigned name =>
    Synth.assigned exprMd name source (by rw [h_node])
  | .Fresh val =>
    Synth.fresh exprMd expr val source h_expr (by rw [h_node])
  | .ContractOf ty fn =>
    Synth.contractOf exprMd ty fn source (by rw [h_node])
  | .Abstract => pure (Synth.abstract source)
  | .All => pure (Synth.all source)
  | .Block [] label => pure (.Block [] label, Synth.emptyBlock source)
  -- Holes in synth position are gradual: an annotated hole synthesizes its
  -- declared type; an unannotated one is `Unknown`. Without this carve-out,
  -- a hole appearing as the target of e.g. a field access (`<?>.f`) would
  -- emit "type cannot be synthesized" and abort, which over-reports against
  -- code where the hole's type is genuinely unknown to begin with.
  | .Hole det none =>
    pure (.Hole det none, { val := .Unknown, source := source })
  | .Hole det (some ty) =>
    let ty' ← resolveHighType ty
    pure (.Hole det (some ty'), ty')
  | _ =>
    let unknown : HighTypeMd := { val := .Unknown, source := source }
    typeMismatch source (some expr)
      "this expression's type cannot be synthesized; try to annotate it or use it in a context where there is an expected type"
      unknown
    pure (expr, unknown)
  return ({ val := val', source := source }, ty)
  termination_by (exprMd, 2)
  decreasing_by all_goals first
    | (apply Prod.Lex.left; term_by_mem)
    | (try subst h_node; apply Prod.Lex.right; decide)
    | (apply Prod.Lex.right; decide)

/-- Check-mode resolution (rule **Sub** at the boundary): resolve `e` and
    verify its type is a consistent subtype of `expected`, written
    `Γ ⊢ e ⇐ T`. Bidirectional rules for individual constructs push
    `expected` into subexpressions rather than bouncing through
    synthesis, which keeps error messages localized and lets the
    expected type propagate through nested control flow. Constructs
    with a dedicated `Check.<construct>` rule:

    - bindings — `Var (.Declare …)`, `Assign`
    - control flow — `Block`, `IfThenElse`, `While`, `Exit`, `Return`
    - verification — `Assert`, `Assume`, `Old`, `ProveBy`
    - holes — `Hole` (typed and untyped)
    - primitive operations — `PrimitiveOp` (arithmetic and boolean
      families only; comparison/equality/string-concat fall through to
      the synth-then-subsume wildcard)

    Everything else falls back to subsumption — synthesize, then verify
    `isConsistentSubtype actual expected`.

    The right principle for new call sites is: when the position has a
    known expected type (`TBool` for conditions, numeric for `decreases`,
    the declared output for a constant initializer or a functional body),
    use `Check.resolveStmtExpr`. When it doesn't, use `resolveStmtExpr`
    (a thin wrapper that calls `Synth.resolveStmtExpr` and discards the
    synthesized type, used at sites where typing is not enforced —
    verification annotations, modifies/reads clauses). -/
def Check.resolveStmtExpr (exprMd : StmtExprMd) (expected : HighTypeMd) : ResolveM StmtExprMd := do
  match h_node: exprMd with
  | AstNode.mk expr source =>
  match h_expr: expr with
  -- Empty block has a fixed type `TVoid` (Synth.emptyBlock); the wildcard
  -- arm below routes it through synth-then-Sub. Non-empty blocks have no
  -- synth rule and are typed structurally by Check.block.
  | .Block (head :: tail) label =>
    Check.block exprMd (head :: tail) label expected source (by rw [h_node])
  | .IfThenElse cond thenBr elseBr =>
    Check.ifThenElse exprMd cond thenBr elseBr expected source (by rw [h_node])
  | .Assign targets value =>
    Check.assign exprMd targets value expected source (by rw [h_node])
  | .Hole det none => pure (Check.holeNone det expected source)
  | .Hole det (some ty) => Check.holeSome det ty expected source
  | .Var (.Declare param) => Check.varDeclare param source
  | .While cond invs dec body =>
    Check.while exprMd cond invs dec body source (by rw [h_node])
  | .Exit target => Check.exit target source
  | .Return val =>
    Check.return exprMd val source (by rw [h_node])
  | .Assert ⟨condExpr, summary⟩ =>
    Check.assert exprMd condExpr summary source (by rw [h_node])
  | .Assume cond =>
    Check.assume exprMd cond source (by rw [h_node])
  | .Old val =>
    Check.old exprMd val expected source (by rw [h_node])
  | .ProveBy val proof =>
    Check.proveBy exprMd val proof expected source (by rw [h_node])
  | .PrimitiveOp .Neg args =>
    Check.primitiveOp exprMd .Neg args expected source (by rw [h_node])
  | .PrimitiveOp .Add args =>
    Check.primitiveOp exprMd .Add args expected source (by rw [h_node])
  | .PrimitiveOp .Sub args =>
    Check.primitiveOp exprMd .Sub args expected source (by rw [h_node])
  | .PrimitiveOp .Mul args =>
    Check.primitiveOp exprMd .Mul args expected source (by rw [h_node])
  | .PrimitiveOp .Div args =>
    Check.primitiveOp exprMd .Div args expected source (by rw [h_node])
  | .PrimitiveOp .Mod args =>
    Check.primitiveOp exprMd .Mod args expected source (by rw [h_node])
  | .PrimitiveOp .DivT args =>
    Check.primitiveOp exprMd .DivT args expected source (by rw [h_node])
  | .PrimitiveOp .ModT args =>
    Check.primitiveOp exprMd .ModT args expected source (by rw [h_node])
  | .PrimitiveOp .And args =>
    Check.primitiveOp exprMd .And args expected source (by rw [h_node])
  | .PrimitiveOp .Or args =>
    Check.primitiveOp exprMd .Or args expected source (by rw [h_node])
  | .PrimitiveOp .AndThen args =>
    Check.primitiveOp exprMd .AndThen args expected source (by rw [h_node])
  | .PrimitiveOp .OrElse args =>
    Check.primitiveOp exprMd .OrElse args expected source (by rw [h_node])
  | .PrimitiveOp .Not args =>
    Check.primitiveOp exprMd .Not args expected source (by rw [h_node])
  | .PrimitiveOp .Implies args =>
    Check.primitiveOp exprMd .Implies args expected source (by rw [h_node])
  | _ =>
    -- Subsumption fallback: synth then check `actual <: expected`.
    let (e', actual) ← Synth.resolveStmtExpr exprMd
    checkSubtype source expected actual
    pure e'
  termination_by (exprMd, 3)
  decreasing_by all_goals first
    | (apply Prod.Lex.left; term_by_mem)
    | (try subst_eqs; apply Prod.Lex.right; decide)
    | (try subst h_node; apply Prod.Lex.right; decide)
    | (apply Prod.Lex.right; decide)

-- ### Literals

/-- `Γ ⊢ LiteralInt n ⇒ TInt` -/
def Synth.litInt (v : Int) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralInt v, { val := .TInt, source := source })

/-- `Γ ⊢ LiteralBool b ⇒ TBool` -/
def Synth.litBool (v : Bool) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralBool v, { val := .TBool, source := source })

/-- `Γ ⊢ LiteralString s ⇒ TString` -/
def Synth.litString (v : String) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralString v, { val := .TString, source := source })

/-- `Γ ⊢ LiteralDecimal d ⇒ TReal` -/
def Synth.litDecimal (v : StrataDDM.Decimal) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralDecimal v, { val := .TReal, source := source })

-- ### Variables

/-- `Γ(x) = T  ∴  Γ ⊢ Var (.Local x) ⇒ T`

    Resolves `ref` against the lexical scope and reads its declared type. -/
def Synth.varLocal (ref : Identifier) (source : Option FileRange) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let ref' ← resolveRef ref source
  let ty ← getVarType ref
  pure (.Var (.Local ref'), ty)

/-- `Γ ⊢ e ⇒ _,  Γ(f) = T_f  ∴  Γ ⊢ Var (.Field e f) ⇒ T_f`

    `f` is looked up against the type of `e` (or the enclosing instance type
    for `self.f`); the typing rule itself is path-agnostic. -/
def Synth.varField (exprMd : StmtExprMd)
    (target : StmtExprMd) (fieldName : Identifier) (source : Option FileRange)
    (h : exprMd.val = .Var (.Field target fieldName)) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', _) ← Synth.resolveStmtExpr target
  let fieldName' ← resolveFieldRef target' fieldName source
  let ty ← getVarType fieldName'
  pure (.Var (.Field target' fieldName'), ty)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    try simp_all
    omega

/-- (Var-Declare)
    ```
    x ∉ dom(Γ)
    ─────────────────────────────────────────  ⊣ Γ, x : T_x
    Γ ⊢ Var (.Declare ⟨x, T_x⟩) ⇐ A
    ```
    `⊣ Γ, x : T_x` records that the surrounding scope is extended with
    the new binding for the remainder of the enclosing block. The
    declaration itself does no work other than registering `x : T_x`,
    and yields no value, so its rule accepts whatever type `A` the
    context expects (the rule ignores `A`). -/
def Check.varDeclare (param : Parameter) (source : Option FileRange) :
    ResolveM StmtExprMd := do
  let ty' ← resolveHighType param.type
  let name' ← defineNameCheckDup param.name (.var param.name ty')
  pure { val := .Var (.Declare ⟨name', ty'⟩), source := source }

-- ### Control flow

/-- (While)
    ```
    Γ ⊢ cond ⇐ TBool      Γ ⊢ invs_i ⇐ TBool
    Γ ⊢ decreases ⇒ U     Numeric U
    Γ ⊢ body ⇐ Unknown
    ─────────────────────────────────────────────────
    Γ ⊢ While cond invs decreases body ⇐ A
    ```
    `cond` is checked against `TBool`, and each invariant against
    `TBool`. The body's *value type* is discarded — control either
    re-enters the loop or falls through, so the body is checked at
    `Unknown` (the gradual wildcard) and any value the body's tail
    might produce is ignored. A loop is a statement: it yields no
    value, so its rule accepts whatever type `A` the context expects
    (the rule ignores `A`).

    The optional `decreases` clause is synthesized and required to
    have a numeric type (`TInt`, `TReal`, `TFloat64`, or `Unknown` as
    the gradual escape hatch), via the same `Numeric U` predicate
    used by the arithmetic primitive ops. `Numeric` is a predicate,
    not a single type, so the clause runs in synth mode rather than
    check mode. -/
def Check.while (exprMd : StmtExprMd)
    (cond : StmtExprMd) (invs : List StmtExprMd)
    (dec : Option StmtExprMd) (body : StmtExprMd)
    (source : Option FileRange)
    (h : exprMd.val = .While cond invs dec body) :
    ResolveM StmtExprMd := do
  let cond' ← Check.resolveStmtExpr cond { val := .TBool, source := cond.source }
  let invs' ← invs.attach.mapM (fun a => have := a.property; do
    Check.resolveStmtExpr a.val { val := .TBool, source := a.val.source })
  let dec' ← dec.attach.mapM (fun a => have := a.property; do
    let (e', decTy) ← Synth.resolveStmtExpr a.val
    let ctx := (← get).typeContext
    unless isNumeric ctx decTy do
      typeMismatch a.val.source none "expected a numeric type" decTy
    pure e')
  let body' ← Check.resolveStmtExpr body { val := .Unknown, source := body.source }
  pure { val := .While cond' invs' dec' body', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try (have := List.sizeOf_lt_of_mem ‹_ ∈ invs›)
      try simp_all
      omega

/-- (Exit)
    ```
    l ∈ Γ_lbl
    ───────────────────
    Γ ⊢ Exit l ⇐ A
    ```
    `exit` is a control-flow terminator — an unconditional jump out of
    the enclosing labeled block. Because it never falls through, it
    never delivers a value, so the rule accepts whatever type `A` the
    context expects (the rule ignores `A`): an `exit` slots into any
    position, even one expecting a value, since control leaves before
    any value would be needed. Anything after `exit l` in the same
    block is dead code, flagged by `Resolution.Check.block`.

    The premise `l ∈ Γ_lbl` requires the target label to name an
    enclosing labeled block; labels live in their own namespace
    (`ResolveState.labelScope`, populated by `Check.block` via
    `withLabel`). An unknown label is reported here as
    `"label '<l>' is not in scope"`. -/
def Check.exit (target : String) (source : Option FileRange) :
    ResolveM StmtExprMd := do
  unless (← get).labelScope.contains target do
    let diag := diagnosticFromSource source
      s!"label '{target}' is not in scope"
    modify fun s => { s with errors := s.errors.push diag }
  pure { val := .Exit target, source := source }

/-- (Return)

    Below, `T_o-bar` denotes the enclosing procedure's declared
    output-type list (bound on entry to a procedure body, stored on
    `ResolveState.answerType`).

    ```
    T_o-bar = []                                           (Return-None-Void)
    ─────────────────────────
    Γ ⊢ Return none ⇐ A

    T_o-bar = [T]    TVoid <:~ T                           (Return-None-Single)
    ──────────────────────────────────
    Γ ⊢ Return none ⇐ A

    T_o-bar = [T_1;…;T_n]  n ≥ 2                           (Return-None-Multi)
    ──────────────────────────────────
    Γ ⊢ Return none ⇐ A

    T_o-bar = [T]    Γ ⊢ e ⇐ T                             (Return-Some)
    ──────────────────────────────────
    Γ ⊢ Return (some e) ⇐ A

    T_o-bar = []                                           (Return-Void-Error)
    ───────────────────────────────────────────────────────────
    Γ ⊢ Return (some e) ↝ "void procedure cannot return a value"

    T_o-bar = [T_1;…;T_n]  n ≥ 2                           (Return-Multi-Error)
    ───────────────────────────────────────────────────────────
    Γ ⊢ Return (some e) ↝ "multi-output procedure cannot use 'return e'; assign to named outputs instead"
    ```
    `return` is the *only* rule whose premises depend on the enclosing
    procedure's declared outputs. Like `Exit`, it is a control-flow
    terminator: it transfers control out of the enclosing procedure and
    never falls through to the surrounding block, so the rule accepts
    whatever type `A` the context expects (the rule ignores `A`). The
    returned value, if any, is checked against the procedure's declared
    output rather than against `A`. Anything after `return` in the same
    block is dead code, flagged by `Resolution.Check.block`.

    When `answerType = none` we are not inside any procedure body (e.g.
    resolving a constant initializer), so all `Return` checks are
    skipped — `Return` should not occur there in well-formed input.

    `return;` synthesizes the missing payload as `TVoid`. In a
    single-output procedure it is then required to subtype the declared
    output (Return-None-Single's `TVoid <:~ T` premise) — accepted in
    void-returning procedures, rejected in `int`/`bool`/etc. ones,
    closing the soundness gap that the Dafny-style early-exit shorthand
    used to leave open. In a void-output procedure it is unconditionally
    accepted (Return-None-Void); in a multi-output procedure it is also
    accepted (Return-None-Multi) and acts as an early-exit shorthand —
    each declared output retains whatever was last assigned to it via
    named-output assignment.

    `return e` is checked against the declared output type in the
    single-output case. Multi-output procedures use named-output
    assignment (`r := …` on the declared output parameters); `return e`
    syntactically takes a single `Option StmtExpr` and cannot carry
    multiple values, so it is flagged with a diagnostic pointing users
    at the named-output convention.

    Regardless of which arm fires, `e` is always elaborated — it is
    checked against the declared output in the single-output case,
    otherwise synthesized — so any errors inside `e` are reported in
    addition to the arity diagnostic. -/
def Check.return (exprMd : StmtExprMd)
    (val : Option StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .Return val) :
    ResolveM StmtExprMd := do
  let expectedReturn := (← get).answerType
  let val' ← val.attach.mapM (fun a => have := a.property; do
    match expectedReturn with
    | some [singleOutput] => Check.resolveStmtExpr a.val singleOutput
    | _ => let (e', _) ← Synth.resolveStmtExpr a.val; pure e')
  match val, expectedReturn with
  | none,   some []          => pure ()
  | none,   some [singleOutput] =>
    -- `return;` synthesizes the missing payload as `TVoid`; require it to
    -- be a consistent subtype of the declared output.
    checkSubtype source singleOutput { val := .TVoid, source := source }
  | none,   some _           => pure ()
  | some _, some []          =>
    let diag := diagnosticFromSource source
      "void procedure cannot return a value"
    modify fun s => { s with errors := s.errors.push diag }
  | some _, some [_]         => pure ()
  | some _, some _           =>
    let diag := diagnosticFromSource source
      "multi-output procedure cannot use 'return e'; assign to named outputs instead"
    modify fun s => { s with errors := s.errors.push diag }
  | _,      none             => pure ()
  -- `return` is a control-flow jump; it doesn't deliver a value to the
  -- enclosing block, so no TVoid-vs-expected subsumption is required.
  -- The return value (if any) was already checked against the declared
  -- output above via `answerType`.
  pure { val := .Return val', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      simp_all
      omega

/-- (Skip)
    ```
    ─────────────────────────────────
    Γ ⊢ Block [] label ⇒ TVoid
    ```
    The empty block has a fixed type `TVoid` — written `skip : TVoid`
    in the source-language presentation. This is the only block-level
    rule that synthesizes: non-empty blocks are typed structurally by
    `Resolution.Check.block` (last statement carries the value, non-last
    positions `⇐ TVoid` or Discard-Call) and never recurse into an empty
    tail, so they never bottom out here. When an empty block appears in
    check position, `Resolution.Check.resolveStmtExpr`'s wildcard arm
    synth-then-subsumes via the standard \[⇐\] Sub fallback. -/
def Synth.emptyBlock (source : Option FileRange) : HighTypeMd :=
  { val := .TVoid, source := source }

/-- (Discard) Check a statement in *effect position*, written `Γ ⊢ s ⋄`.

    Laurel has no syntactic statement/expression split — everything is a
    `StmtExpr` — so "what may appear where its value is discarded" is
    defined by this rule rather than by the grammar. A statement `s` is
    admitted in effect position iff one of:

    * **`Γ ⊢ s ⇐ TVoid`** — `s` checks against `TVoid`. Every
      statement-shaped form lands here: `Var-Declare`, `Assign`, `Assert`,
      `Assume`, `While`, the terminators `Exit`/`Return` (whose check
      rules are polymorphic in the expected type), an `IfThenElse` with
      void branches, and a nested void `Block`. A stranded *value* — a
      literal `5`, a variable load `x`, a comparison `a < b`, a `new`, a
      value-producing `IfThenElse` — fails this check (its type is not
      consistent with `TVoid`) and is reported as dead code.

    * **Discard-Call** — `s` is a call (`StaticCall`/`InstanceCall`). The
      call is synthesized and its result dropped, so the `list.add(x);`
      idiom type-checks even when the callee returns a value. A call is
      the *only* value-producing form admitted in effect position: its
      effects are the point and its result is incidental.

    This is the single definition of "what counts as a statement". It is
    used by `Check.block` for every non-last statement, and for the last
    statement when the block itself sits in statement position
    (`expected = TVoid`). -/
def Check.statement (s : StmtExprMd) : ResolveM StmtExprMd := do
  match s.val with
  | .StaticCall .. | .InstanceCall .. =>
    let (s', _) ← Synth.resolveStmtExpr s; pure s'
  | _ => Check.resolveStmtExpr s { val := .TVoid, source := s.source }
  termination_by (s, 4)
  decreasing_by all_goals (apply Prod.Lex.right; decide)

/-- (Block) Check-mode typing rule for a non-empty block.

    A block's value is the value of its **last** statement; every
    earlier statement is run only for its effect. The rule splits the
    statement list into `init` (all but the last) and `last` and is one
    recursion over that structure:

    * **non-last — `Γ ⊢ s ⇐ TVoid`.** A non-last statement is a pure
      effect, so it is checked at `TVoid`. This admits every statement
      form (`Var-Declare`, `Assign`, `Assert`, `Assume`, `While`,
      `Exit`, `Return`, `IfThenElse`), since each either yields no
      value or — for the terminators `Exit`/`Return` — accepts any
      expected type, and rejects a stranded value expression like `5;`,
      whose `TInt` is not consistent with `TVoid`. The one
      **Discard-Call** carve-out: a call (`StaticCall`/`InstanceCall`)
      is synthesized and its result dropped, so the standard
      `list.add(x);` discard idiom is allowed even when the callee
      returns a value.

    * **last — `Γ ⊢ last ⇐ T`.** The surrounding expected type `T` is
      routed to the last statement, so a check-only trailing form
      (`IfThenElse`, a nested `Block`, `Hole`, `Return`, …) still
      receives its expected type. The same Discard-Call carve-out
      applies when `T = TVoid` (a trailing `foo()` in statement
      position discards its result, so `{ …; foo() }` type-checks as a
      statement even when `foo` returns a value).

    There is deliberately no synthesis rule for non-empty blocks: a
    block is statement-shaped and always occurs in check position
    (procedure bodies, branches, loop bodies, assignment RHS, call
    arguments all supply an expected type). A block in a synth-only
    operand position has no contextual type and is reported by the
    `Synth.resolveStmtExpr` wildcard.

    The block opens a fresh nested scope (declarations made inside
    don't leak), and emits a "dead code after `exit`/`return`"
    diagnostic when a terminator is followed by further statements.
    When `label` is `some l`, `l` is registered in
    `ResolveState.labelScope` (via `withLabel`) for the block's extent
    so nested `exit l` checks can see it. -/
def Check.block (exprMd : StmtExprMd)
    (stmts : List StmtExprMd) (label : Option String)
    (expected : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .Block stmts label) : ResolveM StmtExprMd := do
  -- A non-last statement is in effect position: admitted by `Check.statement`
  -- (`Γ ⊢ s ⋄` — checks at `TVoid`, with the Discard-Call carve-out for calls).
  let checkNonLast (s : StmtExprMd) (_h_mem : s ∈ stmts) : ResolveM StmtExprMd :=
    Check.statement s
  -- The last statement carries the block's value: push `expected` in (so
  -- check-only forms are reachable). When the block itself sits in statement
  -- position (`expected = TVoid`), the last statement is also in effect
  -- position and goes through `Check.statement` (same Discard-Call carve-out).
  let checkLast (s : StmtExprMd) (_h_mem : s ∈ stmts) : ResolveM StmtExprMd := do
    match expected.val with
    | .TVoid => Check.statement s
    | _ => Check.resolveStmtExpr s expected
  withScope <| withLabel label do
    let init' ← stmts.dropLast.attach.mapM fun ⟨s, hMem⟩ => do
      have h_mem : s ∈ stmts := List.dropLast_subset stmts hMem
      checkNonLast s h_mem
    -- Dead-code diagnostic: a terminator (`Exit`/`Return`) among the
    -- non-last statements is followed by at least one more statement.
    -- Flag it once at the position of the next statement.
    let isTerminator (s : StmtExprMd) : Bool :=
      match s.val with
      | .Exit _ | .Return _ => true
      | _ => false
    match init'.findIdx? isTerminator with
    | some i =>
      let nextSource : Option FileRange :=
        match init'[i + 1]? with
        | some next => next.source
        | none      => -- terminator is the last of init', so the dead one
                       -- is the block's actual last statement
          (stmts.getLast?.bind (·.source))
      let termName : String :=
        match init'[i]? with
        | some s => s.val.constrName
        | none   => "exit"
      let diag := diagnosticFromSource nextSource
        s!"dead code after '{termName}'"
      modify fun st => { st with errors := st.errors.push diag }
    | none => pure ()
    -- Check the last statement against `expected`. The dispatcher only
    -- calls `Check.block` on `head :: tail`, so the `none` (empty-list)
    -- arm is dead and kept only to remain total.
    match _lastResult: stmts.getLast? with
    | none =>
      checkSubtype source expected (Synth.emptyBlock source)
      pure { val := .Block init' label, source := source }
    | some last =>
      have := List.mem_of_getLast? _lastResult
      let last' ← checkLast last ‹_›
      pure { val := .Block (init' ++ [last']) label, source := source }
  termination_by (exprMd, 0)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try (have := List.sizeOf_lt_of_mem ‹_ ∈ stmts›)
      try simp_all
      omega

/-- (If / If-NoElse)
    ```
    Γ ⊢ cond ⇐ TBool   Γ ⊢ thenBr ⇐ T   Γ ⊢ elseBr ⇐ T            (If)
    ──────────────────────────────────────────────────────────────────
    Γ ⊢ IfThenElse cond thenBr (some elseBr) ⇐ T

    Γ ⊢ cond ⇐ TBool   Γ ⊢ thenBr ⇐ T   TVoid <: T                (If-NoElse)
    ──────────────────────────────────────────────────────────────────
    Γ ⊢ IfThenElse cond thenBr none ⇐ T
    ```
    Pushes the surrounding `T` into both branches (rather than going
    through If-Synth + Sub at the boundary): errors fire at the
    offending branch instead of at the `if`, and the expectation
    propagates through nested `Block` / `IfThenElse` / `Hole` /
    `Quantifier` constructs that have their own check rules.

    Without an `else`, the implicit branch is `skip : TVoid`, so the
    rule degenerates to require `TVoid <: T` — the standard \[⇐\] Sub
    boundary check that `Resolution.Synth.emptyBlock` composes with
    for an empty block. -/
def Check.ifThenElse (exprMd : StmtExprMd)
    (cond thenBr : StmtExprMd) (elseBr : Option StmtExprMd)
    (expected : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .IfThenElse cond thenBr elseBr) : ResolveM StmtExprMd := do
  let cond' ← Check.resolveStmtExpr cond { val := .TBool, source := cond.source }
  let thenBr' ← Check.resolveStmtExpr thenBr expected
  let elseBr' ← elseBr.attach.mapM (fun ⟨e, _⟩ => Check.resolveStmtExpr e expected)
  if elseBr.isNone then
    checkSubtype source expected { val := .TVoid, source := source }
  pure { val := .IfThenElse cond' thenBr' elseBr', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try simp_all
      omega

-- ### Verification statements

/-- (Assert)
    ```
    Γ ⊢ cond ⇐ TBool
    ──────────────────────────────────
    Γ ⊢ Assert cond ⇐ A
    ```
    `cond` is checked against `TBool`. `assert` is a statement: it
    yields no value, so the rule accepts whatever type `A` the context
    expects (the rule ignores `A`). -/
def Check.assert (exprMd : StmtExprMd)
    (condExpr : StmtExprMd) (summary : Option String)
    (source : Option FileRange)
    (h : exprMd.val = .Assert ⟨condExpr, summary⟩) :
    ResolveM StmtExprMd := do
  let cond' ← Check.resolveStmtExpr condExpr { val := .TBool, source := condExpr.source }
  pure { val := .Assert { condition := cond', summary }, source := source }
  termination_by (exprMd, 0)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    try simp_all
    omega

/-- (Assume)
    ```
    Γ ⊢ cond ⇐ TBool
    ──────────────────────────────────
    Γ ⊢ Assume cond ⇐ A
    ```
    `cond` is checked against `TBool`. `assume` is a statement: it
    yields no value, so the rule accepts whatever type `A` the context
    expects (the rule ignores `A`). -/
def Check.assume (exprMd : StmtExprMd)
    (cond : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .Assume cond) :
    ResolveM StmtExprMd := do
  let cond' ← Check.resolveStmtExpr cond { val := .TBool, source := cond.source }
  pure { val := .Assume cond', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    try simp_all
    omega

-- ### Assignment

/-- (Assign)
    ```
    Γ ⊢ targets_i ⇒ T_i    Γ ⊢ e ⇐ ExpectedTy
    ─────────────────────────────────────────────────────────
    Γ ⊢ Assign targets e ⇒ ExpectedTy
    ```
    where `ExpectedTy = T_1` if `|targets| = 1` and otherwise
    `MultiValuedExpr [T_1; …; T_n]`. The target tuple type is pushed
    into the RHS via `Check.resolveStmtExpr`, so bidirectional rules
    in the RHS receive the assignment's type. The assignment
    synthesizes `ExpectedTy` — the LHS-derived target tuple type —
    so the surrounding context sees the type the RHS was checked
    against. -/
def Synth.assign (exprMd : StmtExprMd)
    (targets : List VariableMd) (value : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .Assign targets value) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let targets' ← targets.attach.mapM fun ⟨v, _⟩ => do
    let ⟨vv, vs⟩ := v
    match vv with
    | .Local ref =>
      let ref' ← resolveRef ref source
      pure (⟨.Local ref', vs⟩ : VariableMd)
    | .Field target fieldName =>
      let (target', _) ← Synth.resolveStmtExpr target
      let fieldName' ← resolveFieldRef target' fieldName source
      pure (⟨.Field target' fieldName', vs⟩ : VariableMd)
    | .Declare param =>
      let ty' ← resolveHighType param.type
      let name' ← defineNameCheckDup param.name (.var param.name ty')
      pure (⟨.Declare ⟨name', ty'⟩, vs⟩ : VariableMd)
  let targetType (t : VariableMd) : ResolveM HighTypeMd := do
    match t.val with
    | .Local ref => getVarType ref
    | .Declare param => pure param.type
    | .Field _ fieldName => getVarType fieldName
  let targetTys ← targets'.mapM targetType
  let expectedTy : HighTypeMd := match targetTys with
    | [single] => single
    | _        => { val := .MultiValuedExpr targetTys, source := source }
  let value' ← Check.resolveStmtExpr value expectedTy
  pure (.Assign targets' value', expectedTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try simp_all
      try (have := List.sizeOf_lt_of_mem ‹_ ∈ targets›; simp_all)
      omega

/-- Check-mode rule for assignment. Synthesizes the assignment's type
    by inlining the same work as `Synth.assign` (resolving targets,
    pushing the LHS-derived `ExpectedTy` into the RHS via
    `Check.resolveStmtExpr`), then runs the standard \[⇐\] Sub
    boundary check `ExpectedTy <: T` against the surrounding `expected`
    — *unless* `T = TVoid`, the marker for statement position
    (e.g. last statement of a block whose value is being discarded).
    `Sub` against `TVoid` would only succeed when `ExpectedTy = TVoid`,
    which would reject every non-void assignment used as a statement,
    so the subsumption is skipped there. The synthesized value is
    discarded in statement position, exactly as for calls. -/
def Check.assign (exprMd : StmtExprMd)
    (targets : List VariableMd) (value : StmtExprMd)
    (expected : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .Assign targets value) : ResolveM StmtExprMd := do
  let targets' ← targets.attach.mapM fun ⟨v, _⟩ => do
    let ⟨vv, vs⟩ := v
    match vv with
    | .Local ref =>
      let ref' ← resolveRef ref source
      pure (⟨.Local ref', vs⟩ : VariableMd)
    | .Field target fieldName =>
      let (target', _) ← Synth.resolveStmtExpr target
      let fieldName' ← resolveFieldRef target' fieldName source
      pure (⟨.Field target' fieldName', vs⟩ : VariableMd)
    | .Declare param =>
      let ty' ← resolveHighType param.type
      let name' ← defineNameCheckDup param.name (.var param.name ty')
      pure (⟨.Declare ⟨name', ty'⟩, vs⟩ : VariableMd)
  let targetType (t : VariableMd) : ResolveM HighTypeMd := do
    match t.val with
    | .Local ref => getVarType ref
    | .Declare param => pure param.type
    | .Field _ fieldName => getVarType fieldName
  let targetTys ← targets'.mapM targetType
  let expectedTy : HighTypeMd := match targetTys with
    | [single] => single
    | _        => { val := .MultiValuedExpr targetTys, source := source }
  let value' ← Check.resolveStmtExpr value expectedTy
  unless expected.val matches .TVoid do
    checkSubtype source expected expectedTy
  pure { val := .Assign targets' value', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try simp_all
      try (have := List.sizeOf_lt_of_mem ‹_ ∈ targets›; simp_all)
      omega

-- ### Calls

/-- Cases on the arity of the callee's declared outputs.

    `Γ(callee) = static-procedure with input T and output T',  Γ ⊢ arg ⇐ T  ∴  Γ ⊢ StaticCall callee arg ⇒ T'`

    `Γ(callee) = static-procedure with inputs Ts and outputs [T_1; …; T_n] (n ≠ 1),  Γ ⊢ args_i ⇐ Ts_i (pairwise)  ∴  Γ ⊢ StaticCall callee args ⇒ MultiValuedExpr [T_1; …; T_n]`

    Callee is resolved against the expected kinds (parameter, static
    procedure, datatype constructor, datatype destructor, constant); each
    argument is *checked* against the corresponding parameter type. The
    bidirectional
    push lets impure-expression arguments (`{x := 1; x}`, `if c then …`,
    holes) flow through their own check rules instead of bottoming out at
    the synth wildcard. Arguments past the declared parameter list (or
    when the callee is unresolved and `paramTypes = []`) are checked
    against `Unknown`, the gradual escape hatch — this preserves the old
    behavior of resolving args without flagging arity mismatches here.
    The result type is the (possibly multi-valued) declared output type
    from `getCallInfo`. -/
def Synth.staticCall (exprMd : StmtExprMd)
    (callee : Identifier) (args : List StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .StaticCall callee args) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let callee' ← resolveRef callee source
    (expected := #[.parameter, .staticProcedure, .datatypeConstructor, .datatypeDestructor, .constant])
  let (retTy, paramTypes) ← getCallInfo callee
  let unknownTy : HighTypeMd := { val := .Unknown, source := none }
  let expectedTys : List HighTypeMd :=
    paramTypes ++ List.replicate (args.length - paramTypes.length) unknownTy
  let args' ← (args.attach.zip expectedTys).mapM (fun (⟨a, hMem⟩, paramTy) => do
    have := hMem
    Check.resolveStmtExpr a paramTy)
  pure (.StaticCall callee' args', retTy)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    have := List.sizeOf_lt_of_mem ‹_ ∈ args›
    omega

/-- `Γ ⊢ target ⇒ _,  Γ(callee) = instance- or static-procedure with inputs [self; T] and output T',  Γ ⊢ arg ⇐ T  ∴  Γ ⊢ InstanceCall target callee arg ⇒ T'`

    Target is synthesized; callee resolves to an instance or static
    procedure; arguments are checked pairwise against the callee's
    parameter types after dropping `self`. Like `Synth.staticCall`, the
    push is bidirectional so block- and conditional-shaped arguments
    route through their own check rules. -/
def Synth.instanceCall (exprMd : StmtExprMd)
    (target : StmtExprMd) (callee : Identifier) (args : List StmtExprMd)
    (source : Option FileRange)
    (h : exprMd.val = .InstanceCall target callee args) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', _) ← Synth.resolveStmtExpr target
  let callee' ← resolveRef callee source
    (expected := #[.instanceProcedure, .staticProcedure])
  let (retTy, paramTypes) ← getCallInfo callee
  let callParamTypes := match paramTypes with | _ :: rest => rest | [] => []
  let unknownTy : HighTypeMd := { val := .Unknown, source := none }
  let expectedTys : List HighTypeMd :=
    callParamTypes ++ List.replicate (args.length - callParamTypes.length) unknownTy
  let args' ← (args.attach.zip expectedTys).mapM (fun (⟨a, hMem⟩, paramTy) => do
    have := hMem
    Check.resolveStmtExpr a paramTy)
  pure (.InstanceCall target' callee' args', retTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try (have := List.sizeOf_lt_of_mem ‹_ ∈ args›)
      try simp_all
      omega

-- ### Primitive operations

/-- Cases on the operator family.

    `Γ ⊢ args_i ⇒ U_i,  U_i <: TBool,  op ∈ {And, Or, AndThen, OrElse, Not, Implies}  ∴  Γ ⊢ PrimitiveOp op args ⇒ TBool`

    `Γ ⊢ args_i ⇒ U_i,  Numeric U_i,  op ∈ {Lt, Leq, Gt, Geq}  ∴  Γ ⊢ PrimitiveOp op args ⇒ TBool`

    `Γ ⊢ lhs ⇒ T_l,  Γ ⊢ rhs ⇒ T_r,  T_l ~ T_r,  op ∈ {Eq, Neq}  ∴  Γ ⊢ PrimitiveOp op [lhs; rhs] ⇒ TBool`

    `Γ ⊢ args_i ⇒ U_i,  Numeric U_i,  T = ⨆ U_i (consistency LUB),  op ∈ {Neg, Add, Sub, Mul, Div, Mod, DivT, ModT}  ∴  Γ ⊢ PrimitiveOp op args ⇒ T`

    `Γ ⊢ args_i ⇒ U_i,  U_i <: TString,  op = StrConcat  ∴  Γ ⊢ PrimitiveOp op args ⇒ TString`

    `Numeric T` is the predicate "T unfolds to TInt / TReal / TFloat64
    (or Unknown via the gradual escape hatch)" — not a single type, so it
    cannot serve as an `expected` for `Check.resolveStmtExpr`. `~` is
    symmetric consistency under the gradual relation, so equality has no
    privileged operand direction.

    The result type is `TBool` for booleans/comparisons/equality, and
    `TString` for concatenation. Boolean / Cmp / Eq / Concat all
    synthesize operands first, then run a per-family check
    (`checkSubtype` for boolean and concat, `isNumeric` for cmp,
    `isConsistent` for equality).

    Arithmetic follows the same shape as `Op-Eq` but for n operands:
    synthesize each operand's type, require it to be `Numeric`, and
    fold the operand types under `join` (the LUB on the
    flat consistency lattice — `Unknown ⊔ T = T`, `T ⊔ T = T`,
    everything else inconsistent). The fold's result is the
    synthesized type. If any pair is inconsistent the rule emits a
    `cannot apply '<op>' to operands of types …` diagnostic and
    falls back to `Unknown`.

    The boolean family additionally has a check-mode rule
    (`Check.primitiveOp`) preferred when an `expected` type is
    available; it pushes `TBool` into operands via
    `Check.resolveStmtExpr` instead of synth-then-`checkSubtype`,
    surfacing operand-shaped errors at their natural location. -/
def Synth.primitiveOp (exprMd : StmtExprMd) (expr : StmtExpr)
    (op : Operation) (args : List StmtExprMd) (source : Option FileRange)
    (h_expr : expr = .PrimitiveOp op args)
    (h : exprMd.val = .PrimitiveOp op args) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let _ := h_expr  -- carries the constructor identity for `expr` in diagnostics
  match op with
  -- Arithmetic: synth each operand's type, then take the LUB under
  -- the consistency relation. This is the same discipline as
  -- `Op-Eq`: operands must be pairwise consistent (with `Unknown`
  -- promoting to whichever side is more informative). Each operand
  -- is also required to be numeric.
  | .Neg | .Add | .Sub | .Mul | .Div | .Mod | .DivT | .ModT =>
    let results ← args.attach.mapM (fun a => have := a.property; do
      Synth.resolveStmtExpr a.val)
    let args' := results.map (·.1)
    let argTypes := results.map (·.2)
    let ctx := (← get).typeContext
    -- Per-operand numeric check: surface the bad operand directly.
    for (a, aTy) in args'.zip argTypes do
      unless isNumeric ctx aTy do
        typeMismatch a.source (some expr) "expected a numeric type" aTy
    -- Fold operands by join, starting from `Unknown` so the
    -- empty list (impossible for these ops, but kept for totality)
    -- yields `Unknown` and a single-operand fold (`Neg`) yields the
    -- operand's type.
    let unknownTy : HighTypeMd := { val := .Unknown, source := source }
    let resultTy := argTypes.foldl
      (fun acc aTy =>
        match acc with
        | some lub => join ctx lub aTy
        | none => none)
      (some unknownTy)
    match resultTy with
    | some ty => pure (.PrimitiveOp op args', ty)
    | none =>
      let formatted := ", ".intercalate (argTypes.map (fun t => s!"'{formatType t}'"))
      let diag := diagnosticFromSource source
        s!"cannot apply '{op}' to operands of types {formatted}"
      modify fun s => { s with errors := s.errors.push diag }
      pure (.PrimitiveOp op args', unknownTy)
  | _ =>
    let results ← args.attach.mapM (fun a => have := a.property; do
      Synth.resolveStmtExpr a.val)
    let args' := results.map (·.1)
    let argTypes := results.map (·.2)
    let resultTy := match op with
      | .Eq | .Neq | .And | .Or | .AndThen | .OrElse | .Not | .Implies
      | .Lt | .Leq | .Gt | .Geq => HighType.TBool
      | .StrConcat => HighType.TString
      -- Unreachable: filtered above.
      | _ => HighType.Unknown
    match op with
    | .And | .Or | .AndThen | .OrElse | .Not | .Implies =>
      for (a, aTy) in args'.zip argTypes do
        checkSubtype a.source { val := .TBool, source := a.source } aTy
    | .Lt | .Leq | .Gt | .Geq =>
      let ctx := (← get).typeContext
      for (a, aTy) in args'.zip argTypes do
        unless isNumeric ctx aTy do
          typeMismatch a.source (some expr) "expected a numeric type" aTy
    | .Eq | .Neq =>
      match argTypes with
      | [lhsTy, rhsTy] =>
        let ctx := (← get).typeContext
        unless isConsistent ctx lhsTy rhsTy do
          let diag := diagnosticFromSource source
            s!"cannot compare '{formatType lhsTy}' with '{formatType rhsTy}' using '{op}'"
          modify fun s => { s with errors := s.errors.push diag }
      | _ => pure ()
    | .StrConcat =>
      for (a, aTy) in args'.zip argTypes do
        checkSubtype a.source { val := .TString, source := a.source } aTy
    | _ => pure ()  -- unreachable
    pure (.PrimitiveOp op args', { val := resultTy, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      have := List.sizeOf_lt_of_mem ‹_ ∈ args›
      omega

/-- Cases on the operator family.

    `Numeric T,  Γ ⊢ args_i ⇐ T,  op ∈ {Neg, Add, Sub, Mul, Div, Mod, DivT, ModT}  ∴  Γ ⊢ PrimitiveOp op args ⇐ T`

    `TBool <: T,  Γ ⊢ args_i ⇐ TBool,  op ∈ {And, Or, AndThen, OrElse, Not, Implies}  ∴  Γ ⊢ PrimitiveOp op args ⇐ T`

    Both families run in check mode: the surrounding `expected` must
    admit the family's natural result type (numeric for arithmetic,
    `TBool` for boolean), and that operand type is pushed into every
    operand via `Check.resolveStmtExpr`. Pushing `expected` (or `TBool`)
    into operands replaces the synth-then-`checkSubtype` discipline of
    `Synth.primitiveOp`, with two consequences: (a) control-flow
    operands like `(if c then 1 else 2) + 3` or `(if c then a else b) && z`
    are resolved correctly via `Check.ifThenElse` instead of hitting the
    synth wildcard, and (b) `int + real` errors at the second operand
    instead of being silently accepted under gradual mixing — the rule
    now requires every operand to subtype the pushed type.

    The remaining operator families (comparison, equality, string
    concatenation) stay in `Synth.primitiveOp`: their result types are
    fixed (`TBool` / `TString`) and their operand constraints can't be
    expressed as a single pushable type (Numeric is a predicate;
    equality is symmetric). The dispatcher routes those to the wildcard
    `_ =>` arm of `Check.resolveStmtExpr`. -/
def Check.primitiveOp (exprMd : StmtExprMd)
    (op : Operation) (args : List StmtExprMd)
    (expected : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .PrimitiveOp op args) :
    ResolveM StmtExprMd := do
  let operandTy : HighTypeMd ← match op with
    | .Neg | .Add | .Sub | .Mul | .Div | .Mod | .DivT | .ModT =>
      let ctx := (← get).typeContext
      unless isNumeric ctx expected do
        typeMismatch source none "expected a numeric type" expected
      pure expected
    | .And | .Or | .AndThen | .OrElse | .Not | .Implies =>
      let boolTy : HighTypeMd := { val := .TBool, source := source }
      checkSubtype source expected boolTy
      pure boolTy
    | _ =>
      -- Unreachable: dispatcher routes only the arithmetic and boolean
      -- families to this rule. `Unknown` keeps the function total in
      -- case the dispatcher's pattern list ever drifts.
      pure { val := .Unknown, source := source }
  let args' ← args.attach.mapM (fun a => have := a.property; do
    Check.resolveStmtExpr a.val operandTy)
  pure { val := .PrimitiveOp op args', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    have := List.sizeOf_lt_of_mem ‹_ ∈ args›
    omega

-- ### Object forms

/-- Cases on whether `ref` resolves to a composite/datatype.

    `Γ(ref) is a composite or datatype T  ∴  Γ ⊢ New ref ⇒ UserDefined T`

    `Γ(ref) is not a composite or datatype  ∴  Γ ⊢ New ref ⇒ Unknown`

    When `ref` resolves to a composite or datatype, the type is
    `UserDefined ref`; otherwise `Unknown` (suppresses cascading errors
    after the kind diagnostic has already fired). -/
def Synth.new (ref : Identifier) (source : Option FileRange) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let ref' ← resolveRef ref source
    (expected := #[.compositeType, .datatypeDefinition])
  let s ← get
  let kindOk : Bool := match s.scope.get? ref.text with
    | some (_, node) => node.kind == .unresolved ||
        (#[ResolvedNodeKind.compositeType, .datatypeDefinition].contains node.kind)
    | none => true
  let ty := if kindOk then { val := HighType.UserDefined ref', source := source }
            else { val := HighType.Unknown, source := source }
  pure (.New ref', ty)

/-- `Γ ⊢ target ⇒ U,  U ~ T  ∨  U <: T  ∨  T <: U  ∴  Γ ⊢ AsType target T ⇒ T`

    `target` synthesizes some type `U`; the cast is allowed when `U` and
    `T` sit in the same lineage modulo gradual `Unknown` — either
    consistent after unfolding aliases/constrained types (e.g. `5 as Int`
    where `Int` is a wrapper over `int`), or a subtype in either
    direction (downcast `animal as Cat` when `Cat extends Animal`,
    upcast `cat as Animal`). Sibling casts (`Dog as Cat`) and casts
    between unrelated primitives (`"hi" as int`) are rejected. The
    synthesized type is `T` — the user's claim is honored once the
    relation check passes. -/
def Synth.asType (exprMd : StmtExprMd)
    (target : StmtExprMd) (ty : HighTypeMd)
    (h : exprMd.val = .AsType target ty) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', targetTy) ← Synth.resolveStmtExpr target
  let ty' ← resolveHighType ty
  let ctx := (← get).typeContext
  unless isConsistentSubtype ctx targetTy ty' || isConsistentSubtype ctx ty' targetTy do
    let diag := diagnosticFromSource target.source
      s!"cannot cast unrelated type '{formatType targetTy}' to '{formatType ty'}'"
    modify fun s => { s with errors := s.errors.push diag }
  pure (.AsType target' ty', ty')
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- `Γ ⊢ target ⇒ U,  U ~ T  ∨  U <: T  ∨  T <: U  ∴  Γ ⊢ IsType target T ⇒ TBool`

    Same lineage check as `AsType` — `is` only makes sense between types
    that share a lineage modulo gradual `Unknown`; testing `5 is Cat`
    is statically nonsense. The synthesized type is `TBool`. -/
def Synth.isType (exprMd : StmtExprMd)
    (target : StmtExprMd) (ty : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .IsType target ty) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', targetTy) ← Synth.resolveStmtExpr target
  let ty' ← resolveHighType ty
  let ctx := (← get).typeContext
  unless isConsistentSubtype ctx targetTy ty' || isConsistentSubtype ctx ty' targetTy do
    let diag := diagnosticFromSource target.source
      s!"cannot test unrelated type '{formatType targetTy}' against '{formatType ty'}'"
    modify fun s => { s with errors := s.errors.push diag }
  pure (.IsType target' ty', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- `Γ ⊢ lhs ⇒ T_l,  Γ ⊢ rhs ⇒ T_r,  isReference T_l,  isReference T_r,  T_l ~ T_r  ∴  Γ ⊢ ReferenceEquals lhs rhs ⇒ TBool`

    Both operands must be reference types (`UserDefined` or `Unknown`) —
    reference equality is meaningless on primitives. The operands must
    also be mutually consistent (the symmetric `isConsistent`), so
    `Cat === Dog` is rejected when `Cat` and `Dog` are unrelated
    user-defined types, while `Cat === Animal` is accepted when `Cat`
    extends `Animal` (the gradual `Unknown` wildcard makes either side
    flow freely against the other). -/
def Synth.refEq (exprMd : StmtExprMd) (expr : StmtExpr)
    (lhs rhs : StmtExprMd) (source : Option FileRange)
    (h_expr : expr = .ReferenceEquals lhs rhs)
    (h : exprMd.val = .ReferenceEquals lhs rhs) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let _ := h_expr
  let (lhs', lhsTy) ← Synth.resolveStmtExpr lhs
  let (rhs', rhsTy) ← Synth.resolveStmtExpr rhs
  let ctx := (← get).typeContext
  unless isReference ctx lhsTy do
    typeMismatch lhs'.source (some expr) "expected a reference type" lhsTy
  unless isReference ctx rhsTy do
    typeMismatch rhs'.source (some expr) "expected a reference type" rhsTy
  unless isConsistent ctx lhsTy rhsTy do
    let diag := diagnosticFromSource source
      s!"'{expr.constrName}' operands have incompatible types '{formatType lhsTy}' and '{formatType rhsTy}'"
    modify fun s => { s with errors := s.errors.push diag }
  pure (.ReferenceEquals lhs' rhs', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      omega

/-- `Γ ⊢ target ⇒ T_t,  Γ(f) = T_f,  Γ ⊢ newVal ⇐ T_f  ∴  Γ ⊢ PureFieldUpdate target f newVal ⇒ T_t`

    `target` is synthesized, `f` resolved against `T_t` (or the enclosing
    instance type), and `newVal` checked against the field's declared
    type. The synthesized type is `T_t` — updating a field on a pure type
    produces a new value of the same type. -/
def Synth.pureFieldUpdate (exprMd : StmtExprMd)
    (target : StmtExprMd) (fieldName : Identifier) (newVal : StmtExprMd)
    (h : exprMd.val = .PureFieldUpdate target fieldName newVal) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', targetTy) ← Synth.resolveStmtExpr target
  let fieldName' ← resolveFieldRef target' fieldName target.source
  let fieldTy ← getVarType fieldName'
  let newVal' ← Check.resolveStmtExpr newVal fieldTy
  pure (.PureFieldUpdate target' fieldName' newVal', targetTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      omega

-- ### Verification expressions

/-- `Γ, x : T ⊢ body ⇐ TBool  ∴  Γ ⊢ Quantifier mode ⟨x, T⟩ trig body ⇒ TBool`

    Opens a fresh scope, binds `x : T` (in scope only for the body and
    trigger), resolves the optional trigger, and checks the body against
    `TBool` since a quantifier is a proposition. Without that body check,
    `forall x: int :: x + 1` would be silently accepted. The construct
    itself synthesizes `TBool`. -/
def Synth.quantifier (exprMd : StmtExprMd)
    (mode : QuantifierMode) (param : Parameter)
    (trigger : Option StmtExprMd) (body : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .Quantifier mode param trigger body) :
    ResolveM (StmtExpr × HighTypeMd) := do
  withScope do
    let paramTy' ← resolveHighType param.type
    let paramName' ← defineNameCheckDup param.name (.quantifierVar param.name paramTy')
    let trigger' ← trigger.attach.mapM (fun pv => have := pv.property; do
      let (e', _) ← Synth.resolveStmtExpr pv.val; pure e')
    let body' ← Check.resolveStmtExpr body { val := .TBool, source := body.source }
    pure (.Quantifier mode ⟨paramName', paramTy'⟩ trigger' body', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try simp_all
      omega

/-- `Γ ⊢ name ⇒ _  ∴  Γ ⊢ Assigned name ⇒ TBool`

    `assigned x` is a verification predicate that holds when `x` has
    been definitely assigned. The construct unconditionally synthesizes
    `TBool`; the operand's synthesized type is discarded, and `Assigned`
    imposes no constraint on it.

    The operand is still resolved (via `Synth.resolveStmtExpr`) purely
    for its name-resolution side effects — its identifier must point at a
    definition so that downstream passes can reason about the binding —
    but the result type is thrown away. `Assigned` is meant to name a
    variable or field, yet its AST field is an arbitrary `StmtExpr`
    (`Assigned (name : StmtExprMd)`), so this rule does *not* enforce
    that shape: it is not correct-by-construction, and the type checker
    deliberately leaves the operand unconstrained rather than rejecting,
    say, `assigned (a + b)`. -/
def Synth.assigned (exprMd : StmtExprMd)
    (name : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .Assigned name) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (name', _) ← Synth.resolveStmtExpr name
  pure (.Assigned name', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- `Γ ⊢ v ⇐ T  ∴  Γ ⊢ Old v ⇐ T`

    `old(v)` refers to the pre-state value of `v` in a postcondition.
    It has the same type as `v`, so the surrounding expectation
    propagates straight through: `v` is checked against the same `T`,
    and the result is wrapped back up as `Old v'`.

    The rule is type-transparent and deliberately does *not* restrict
    `v` to an identifier or lvalue. `old` wraps an arbitrary expression
    (`Old (value : StmtExprMd)`), matching Dafny, where `old(this.f +
    g())` is legal — the pre-state is taken of the whole expression.
    Whether `v` denotes something whose pre-state is meaningful is a
    well-formedness question for the verifier's heap model, not a typing
    one, so resolution only resolves names inside `v` and checks its
    type; it imposes no syntactic shape on `v`. -/
def Check.old (exprMd : StmtExprMd)
    (val : StmtExprMd) (expected : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .Old val) :
    ResolveM StmtExprMd := do
  let val' ← Check.resolveStmtExpr val expected
  pure { val := .Old val', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- `Γ ⊢ v ⇒ T,  isReference T  ∴  Γ ⊢ Fresh v ⇒ TBool`

    `v` is synthesized and must have a reference type (`UserDefined` or
    `Unknown`) — `Fresh` only makes sense on heap-allocated references, so
    `fresh(5)` is rejected. The construct itself synthesizes `TBool`. -/
def Synth.fresh (exprMd : StmtExprMd) (expr : StmtExpr)
    (val : StmtExprMd) (source : Option FileRange)
    (h_expr : expr = .Fresh val)
    (h : exprMd.val = .Fresh val) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let _ := h_expr
  let (val', valTy) ← Synth.resolveStmtExpr val
  unless isReference (← get).typeContext valTy do
    typeMismatch val'.source (some expr) "expected a reference type" valTy
  pure (.Fresh val', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- `Γ ⊢ v ⇐ T,  Γ ⊢ proof ⇒ _  ∴  Γ ⊢ ProveBy v proof ⇐ T`

    `ProveBy v proof` has the same type as `v` (the proof is just a hint
    for downstream verification), so the surrounding expectation
    propagates into `v`. The proof itself has no constraint on its type
    and is still synthesized. -/
def Check.proveBy (exprMd : StmtExprMd)
    (val proof : StmtExprMd) (expected : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .ProveBy val proof) :
    ResolveM StmtExprMd := do
  let val' ← Check.resolveStmtExpr val expected
  let (proof', _) ← Synth.resolveStmtExpr proof
  pure { val := .ProveBy val' proof', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      omega

-- ### Self reference

/-- Cases on whether `instanceTypeName` is set (i.e., we're inside an
    instance method).

    `Γ.instanceTypeName = some T  ∴  Γ ⊢ This ⇒ UserDefined T`

    `Γ.instanceTypeName = none  ∴  Γ ⊢ This ⇒ Unknown`  (emits "'this' is not allowed outside instance methods")

    When `instanceTypeName` is set (we're inside an instance method,
    populated on `ResolveState` by `resolveInstanceProcedure` for the
    duration of an instance method body), `This` synthesizes
    `UserDefined T`. With it, `this.field` and instance-method dispatch
    synthesize real types instead of being wildcarded through `Unknown`.
    Otherwise an error is emitted ("'this' is not allowed outside instance
    methods") and the type collapses to `Unknown` to suppress cascading
    errors. -/
def Synth.this (source : Option FileRange) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let s ← get
  match s.instanceTypeName with
  | some typeName =>
    let typeId : Identifier :=
      match s.scope.get? typeName with
      | some (uid, _) => { text := typeName, uniqueId := some uid, source := source }
      | none => { text := typeName, source := source }
    pure (.This, { val := .UserDefined typeId, source := source })
  | none =>
    let diag := diagnosticFromSource source "'this' is not allowed outside instance methods"
    modify fun s => { s with errors := s.errors.push diag }
    pure (.This, { val := .Unknown, source := source })

-- ### Untyped forms

/-- `Γ ⊢ Abstract ⇒ Unknown` -/
def Synth.abstract (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.Abstract, { val := .Unknown, source := source })

/-- `Γ ⊢ All ⇒ Unknown` -/
def Synth.all (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.All, { val := .Unknown, source := source })

-- ### ContractOf

/-- Cases on the contract type `ty` and on whether `fn` is a procedure
    reference.

    `fn = Var (.Local id),  Γ(id) ∈ {staticProcedure, instanceProcedure}  ∴  Γ ⊢ ContractOf Precondition fn ⇒ TBool  and  Γ ⊢ ContractOf PostCondition fn ⇒ TBool`

    `fn = Var (.Local id),  Γ(id) ∈ {staticProcedure, instanceProcedure}  ∴  Γ ⊢ ContractOf Reads fn ⇒ TSet Unknown  and  Γ ⊢ ContractOf Modifies fn ⇒ TSet Unknown`

    `fn is not a procedure reference  ∴  Γ ⊢ ContractOf _ fn ↝ error: "'contractOf' expected a procedure reference"`

    `ContractOf ty fn` extracts a procedure's contract clause as a value:
    its preconditions (`Precondition`), postconditions (`PostCondition`),
    reads set (`Reads`), or modifies set (`Modifies`). `fn` must be a
    direct identifier reference resolving to a procedure — a contract
    belongs to a *named* procedure, not an arbitrary expression. Anything
    else fires the diagnostic *"'contractOf' expected a procedure
    reference"* and the construct synthesizes `Unknown` to suppress
    cascading errors.

    `Precondition` and `PostCondition` are propositions, hence `TBool`.
    `Reads` and `Modifies` are sets of heap-allocated locations —
    composite/datatype references and fields. The element type is left as
    `Unknown` for now since the rule doesn't yet recover it from `fn`'s
    declared modifies/reads clauses.

    The constructor is reserved for future use — Laurel's grammar has no
    `contractOf` production today, and the translator emits "not yet
    implemented" for it. The typing rule exists so resolution remains
    exhaustive over `StmtExpr`. -/
def Synth.contractOf (exprMd : StmtExprMd)
    (ty : ContractType) (fn : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .ContractOf ty fn) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (fn', _) ← Synth.resolveStmtExpr fn
  let s ← get
  let fnIsProcRef : Bool := match fn'.val with
    | .Var (.Local ref) =>
      match s.scope.get? ref.text with
      | some (_, node) =>
        node.kind == .staticProcedure ||
        node.kind == .instanceProcedure ||
        node.kind == .unresolved
      | none => true  -- unresolved name already reported
    | _ => false
  unless fnIsProcRef do
    let diag := diagnosticFromSource fn.source
      "'contractOf' expected a procedure reference"
    modify fun s => { s with errors := s.errors.push diag }
  let resultTy : HighType := match ty with
    | .Precondition | .PostCondition => .TBool
    | .Reads | .Modifies => .TSet { val := .Unknown, source := none }
  pure (.ContractOf ty fn', { val := resultTy, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

-- ### Holes

/-- `T_h <: T  ∴  Γ ⊢ Hole d (some T_h) ⇐ T`

    A typed hole carries the user's annotation `T_h`. The annotation is
    resolved and verified against the surrounding `expected` type via
    subsumption; the resolved annotation is preserved on the node so
    downstream passes (hole elimination) can generate correctly typed
    uninterpreted functions. -/
def Check.holeSome (det : Bool) (ty : HighTypeMd) (expected : HighTypeMd)
    (source : Option FileRange) : ResolveM StmtExprMd := do
  let ty' ← resolveHighType ty
  checkSubtype source expected ty'
  pure { val := .Hole det (some ty'), source := source }

/-- `Γ ⊢ Hole d none ⇐ T  ↦  Γ ⊢ Hole d (some T)`

    An untyped hole in check mode records the expected type on the node
    so downstream passes (hole elimination) don't have to infer it
    again. -/
def Check.holeNone (det : Bool) (expected : HighTypeMd) (source : Option FileRange) :
    StmtExprMd :=
  { val := .Hole det (some expected), source := source }

end -- mutual
end Resolution

open Resolution

/-- Resolve a statement expression, discarding the synthesized type.
    Use when only the resolved expression is needed (invariants, decreases, etc.). -/
private def resolveStmtExpr (e : StmtExprMd) : ResolveM StmtExprMd := do
  let (e', _) ← Synth.resolveStmtExpr e; pure e'

/-- Resolve a parameter: assign a fresh ID and add to scope. -/
def resolveParameter (param : Parameter) : ResolveM Parameter := do
  let ty' ← resolveHighType param.type
  let name' ← defineNameCheckDup param.name (.parameter ⟨param.name, ty'⟩)
  return ⟨name', ty'⟩

/-- Resolve a procedure body, checking its impl block (if any) against
    `expected`. The expected type comes from the procedure's declared
    output: a single output `T` for functional procedures, `TVoid`
    otherwise. Bodies without an impl block (`Abstract`, `External`) ignore
    `expected`. -/
def resolveBody (body : Body) (expected : HighTypeMd) : ResolveM Body := do
  match body with
  | .Transparent b =>
    let b' ← Check.resolveStmtExpr b expected
    return .Transparent b'
  | .Opaque posts impl mods =>
    let posts' ← posts.mapM (·.mapM resolveStmtExpr)
    let impl' ← impl.mapM (Check.resolveStmtExpr · expected)
    let mods' ← mods.mapM resolveStmtExpr
    return .Opaque posts' impl' mods'
  | .Abstract posts =>
    let posts' ← posts.mapM (·.mapM resolveStmtExpr)
    return .Abstract posts'
  | .External => return .External

/-- Compute the expected *value type* `A` for a procedure body, i.e.
    the `A` in `Γ ⊢ body ⇐ A`. Functional procedures with a single
    output `T` expect `A = T`: the body's last statement is the result
    and must produce a `T`. Non-functional procedures expect
    `A = Unknown`: their body is run as a statement and the last
    statement's value (if any) is discarded — outputs are observed via
    `return e` (whose payload is matched against the procedure's
    declared outputs by `Resolution.Check.return`) or via named-output
    assignment.

    This computes only the body's value type. The procedure's declared
    output list is bound separately by the procedure rule
    (`resolveProcedure` / `resolveInstanceProcedure`) into
    `ResolveState.answerType`. -/
private def procedureBodyType (isFunctional : Bool) (outputs : List Parameter)
    (source : Option FileRange) : HighTypeMd :=
  match isFunctional, outputs with
  | true, [singleOutput] => singleOutput.type
  | _, _ => { val := .Unknown, source := source }

/-- (Procedure)
    ```
    T_o-bar = proc.outputs.types    A = procedureBodyType proc
    Γ_global, params(proc) ⊢ proc.body ⇐ A
    ──────────────────────────────────────────────────────────
    Γ_global ⊢ Procedure proc
    ```
    The body is resolved under a scope that includes the procedure's
    input and output parameters, and is checked against the value type
    `A` computed by `procedureBodyType`. The Return rules consult the
    procedure's declared output list `T_o-bar` (stored on
    `ResolveState.answerType`, set on entry and restored on exit). -/
def resolveProcedure (proc : Procedure) : ResolveM Procedure := do
  let procName' ← resolveRef proc.name
  withScope do
    let inputs' ← proc.inputs.mapM resolveParameter
    let outputs' ← proc.outputs.mapM resolveParameter
    let pres' ← proc.preconditions.mapM (·.mapM resolveStmtExpr)
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let savedAnswer := (← get).answerType
    modify fun s => { s with answerType := some (outputs'.map (·.type)) }
    let bodyExpected := procedureBodyType proc.isFunctional outputs' proc.name.source
    -- Pre-register the implicit `bodyLabel` block that the LaurelToCore
    -- translator wraps every body in (`Core.Statement.block bodyLabel …`),
    -- so that frontends emitting `Exit bodyLabel` for early-return lowering
    -- (e.g. PythonToLaurel) don't trip Check.exit's label-scope check.
    let body' ← withLabel (some bodyLabel) <| resolveBody proc.body bodyExpected
    modify fun s => { s with answerType := savedAnswer }
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
    let savedAnswer := (← get).answerType
    modify fun s => { s with answerType := some (outputs'.map (·.type)) }
    let bodyExpected := procedureBodyType proc.isFunctional outputs' proc.name.source
    -- See `resolveProcedure` for the rationale on `bodyLabel`.
    let body' ← withLabel (some bodyLabel) <| resolveBody proc.body bodyExpected
    modify fun s => { s with answerType := savedAnswer }
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
      let (constraint', _) ← Synth.resolveStmtExpr ct.constraint
      let (witness', _) ← Synth.resolveStmtExpr ct.witness
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
  let init' ← c.initializer.mapM (Check.resolveStmtExpr · ty')
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
  | .Applied base args =>
    let map := collectHighType map base
    args.foldl collectHighType map
  | .Pure base => collectHighType map base
  | .Intersection tys => tys.foldl collectHighType map
  | .MultiValuedExpr tys => tys.foldl collectHighType map
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
  | .While cond invs dec body =>
    let map := collectStmtExpr map cond
    let map := invs.foldl collectStmtExpr map
    let map := match dec with | some d => collectStmtExpr map d | none => map
    collectStmtExpr map body
  | .Return val => match val with | some v => collectStmtExpr map v | none => map
  | .Var (.Local _) => map
  | .Var (.Declare param) =>
    let map := register map param.name (.var param.name param.type)
    collectHighType map param.type
  | .Assign targets value =>
    let map := targets.foldl (fun map t =>
      match t.val with
      | .Declare param =>
        let map := register map param.name (.var param.name param.type)
        collectHighType map param.type
      | _ => map) map
    collectStmtExpr map value
  | .Var (.Field target _) => collectStmtExpr map target
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
        -- The constructor parameter's `uniqueId` (set by `resolveTypeDefinition`)
        -- is the shared uniqueId of the safe/unsafe destructor scope entries,
        -- so registering it here as `.datatypeDestructor` covers calls of the
        -- form `TypeName..fieldName` and `TypeName..fieldName!`.
        let map := register map p.name (.datatypeDestructor dt.name p)
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


/-- A default ResolvedNode used as a placeholder during pre-registration.
    It will be overwritten with the real node when the definition is fully resolved. -/
private def placeholderNode : ResolvedNode := .var "$placeholder" { val := .TVoid, source := none }

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
        -- Register the tester override first; the second call reuses the
        -- returned Identifier (now carrying a uniqueId) so the unprefixed
        -- constructor name and the `TypeName..isCtor` tester name resolve to
        -- the same uniqueId, which `buildRefToDef` in turn maps to
        -- `.datatypeConstructor`.
        let ctorName ← defineNameCheckDup ctor.name (.datatypeConstructor dt.name ctor) (some (dt.testerName ctor))
        let _ ← defineNameCheckDup ctorName (.datatypeConstructor dt.name ctor)
        for p in ctor.args do
          -- Same chaining trick for the safe and unsafe destructor names: both
          -- point to the same uniqueId so `IntList..head` and `IntList..head!`
          -- resolve to the same `.datatypeDestructor` model entry.
          let pName ← defineNameCheckDup p.name (.datatypeDestructor dt.name p) (some (dt.destructorName p))
          let _ ← defineNameCheckDup pName (.datatypeDestructor dt.name p) (some (dt.unsafeDestructorName p))
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
  let typeContext := TypeContext.ofTypes program.types
  let (program', finalState) := phase1.run { nextId := nextId, typeContext }
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
