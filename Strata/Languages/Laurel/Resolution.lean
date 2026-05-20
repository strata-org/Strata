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
  `checkStmtExpr` for fresh subexpressions, or `checkSubtype` when a type is
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

## Future structural changes

A few open structural questions worth recording — see the *Type checking* section of
`LaurelDoc.lean` for context.

- *Rename to `NameTypeResolution`.* This pass resolves names and type-checks expressions in
  one walk. The current name only mentions half of what it does. `NameTypeResolution.lean`
  (or similar) would advertise both responsibilities.
- *Eliminate `LaurelTypes.computeExprType` by caching types.* Five later passes
  (`LaurelToCoreTranslator`, `ModifiesClauses`, `LiftImperativeExpressions`,
  `HeapParameterization`, `TypeHierarchy`) re-derive `StmtExpr` types after resolution.
  Resolution already synthesizes those types and discards them. Caching per-node types on
  `SemanticModel` (or directly on the AST) would let the later passes look them up instead
  of recomputing.
- *Shrink or remove `InferHoleTypes`.* `Hole-None-Check` already records expected types
  during resolution for holes in check-mode positions. Holes in synth-only positions still
  need the post-pass, but as more constructs gain bespoke check rules, fewer holes need
  it; eventually the pass can go away.
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
  /-- Diagnostics collected during resolution. -/
  errors : Array DiagnosticModel := #[]
  /-- When resolving inside an instance procedure, the owning composite type name.
      Used by `resolveFieldRef` to resolve `self.field` when `self` has type `Any`. -/
  instanceTypeName : Option String := none
  /-- When resolving inside a procedure body, the declared output types (in
      declaration order). `none` means no enclosing procedure. Used by `Return`
      to type-check the optional return value and to flag arity/shape mismatches. -/
  expectedReturnTypes : Option (List HighTypeMd) := none
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
    "<problem>, got '<actual>'". -/
private def typeMismatch (source : Option FileRange) (construct : Option StmtExpr)
    (problem : String) (actual : HighTypeMd) : ResolveM Unit := do
  let constructor := match construct with
    | some c => s!"'{c.constrName}' "
    | none   => ""
  let diag := diagnosticFromSource source s!"{constructor}{problem}, got '{formatType actual}'"
  modify fun s => { s with errors := s.errors.push diag }

/-- Type-level subtype check: emits the standard "expected/got" diagnostic when
    `actual` is not a consistent subtype of `expected`. Used at sites where the
    actual type is already in hand (assignment, call args, body vs declared
    output) — equivalent to `checkStmtExpr e expected` but without re-synthesizing. -/
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

/-- Test whether a type is a user-defined reference type. `Unknown` is accepted
    as a gradual escape hatch. Used by Fresh and ReferenceEquals, which only
    make sense on composite/datatype references. -/
private def isReference (ctx : TypeContext) (ty : HighTypeMd) : Bool :=
  match (ctx.unfold ty).val with
  | .UserDefined _ | .Unknown => true
  | _ => false

/-- Get the type of a resolved reference. Tries the lexical scope by name
    first; if that misses (notably for fields, which are scoped under
    qualified keys like "Container.intValue"), falls back to a uniqueId
    lookup populated as definitions are registered. -/
private def getVarType (ref : Identifier) : ResolveM HighTypeMd := do
  let s ← get
  match s.scope.get? ref.text with
  | some (_, node) => pure node.getType
  | none =>
    match ref.uniqueId.bind s.idToNode.get? with
    | some node => pure node.getType
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

Each typing rule from the Laurel manual is implemented as its own helper
inside the mutual block below. Helpers are grouped by section to mirror the
*Typing rules* index in `LaurelDoc.lean`:

- Literals — `synthLitInt`, `synthLitBool`, `synthLitString`, `synthLitDecimal`
- Variables — `synthVarLocal`, `synthVarField`, `synthVarDeclare`
- Control flow — `synthIfThenElse`, `synthBlock`, `synthWhile`, `synthExit`,
  `synthReturn`, `checkBlock`, `checkIfThenElse`
- Verification statements — `synthAssert`, `synthAssume`
- Assignment — `synthAssign`
- Calls — `synthStaticCall`, `synthInstanceCall`
- Primitive operations — `synthPrimitiveOp`
- Object forms — `synthNew`, `synthAsType`, `synthIsType`, `synthRefEq`,
  `synthPureFieldUpdate`
- Verification expressions — `synthQuantifier`, `synthAssigned`, `synthOld`,
  `synthFresh`, `synthProveBy`
- Self reference — `synthThis`
- Untyped forms — `synthAbstract`, `synthAll`
- ContractOf — `synthContractOf`
- Holes — `synthHole`, `checkHoleNone`

The dispatch functions `synthStmtExpr` and `checkStmtExpr` simply pattern-match
on the constructor and delegate to the corresponding helper. -/

-- The `h : exprMd.val = .Foo args ...` parameters on the recursive helpers
-- look unused to the linter, but each one is referenced by that helper's
-- `decreasing_by` tactic to relate `sizeOf args` to `sizeOf exprMd`.
set_option linter.unusedVariables false in
mutual

-- ### Dispatch

/-- Synth-mode resolution: resolve `e` and synthesize its `HighType`.
    Each constructor delegates to its rule's helper. -/
def synthStmtExpr (exprMd : StmtExprMd) : ResolveM (StmtExprMd × HighTypeMd) := do
  match h_node: exprMd with
  | AstNode.mk expr source =>
  let (val', ty) ← match h_expr: expr with
  | .IfThenElse cond thenBr elseBr =>
    synthIfThenElse exprMd cond thenBr elseBr (by rw [h_node])
  | .Block stmts label =>
    synthBlock exprMd stmts label (by rw [h_node])
  | .While cond invs dec body =>
    synthWhile exprMd cond invs dec body (by rw [h_node])
  | .Exit target => pure (synthExit target source)
  | .Return val =>
    synthReturn exprMd source val (by rw [h_node])
  | .LiteralInt v => pure (synthLitInt v source)
  | .LiteralBool v => pure (synthLitBool v source)
  | .LiteralString v => pure (synthLitString v source)
  | .LiteralDecimal v => pure (synthLitDecimal v source)
  | .Var (.Local ref) => synthVarLocal ref source
  | .Var (.Declare param) => synthVarDeclare param source
  | .Var (.Field target fieldName) =>
    synthVarField exprMd target fieldName source (by rw [h_node])
  | .Assign targets value =>
    synthAssign exprMd targets value source (by rw [h_node])
  | .PureFieldUpdate target fieldName newVal =>
    synthPureFieldUpdate exprMd target fieldName newVal (by rw [h_node])
  | .StaticCall callee args =>
    synthStaticCall exprMd callee args source (by rw [h_node])
  | .PrimitiveOp op args =>
    synthPrimitiveOp exprMd expr op args source h_expr (by rw [h_node])
  | .New ref => synthNew ref source
  | .This => synthThis source
  | .ReferenceEquals lhs rhs =>
    synthRefEq exprMd expr lhs rhs source h_expr (by rw [h_node])
  | .AsType target ty =>
    synthAsType exprMd target ty (by rw [h_node])
  | .IsType target ty =>
    synthIsType exprMd target ty source (by rw [h_node])
  | .InstanceCall target callee args =>
    synthInstanceCall exprMd target callee args source (by rw [h_node])
  | .Quantifier mode param trigger body =>
    synthQuantifier exprMd mode param trigger body source (by rw [h_node])
  | .Assigned name =>
    synthAssigned exprMd name source (by rw [h_node])
  | .Old val =>
    synthOld exprMd val (by rw [h_node])
  | .Fresh val =>
    synthFresh exprMd expr val source h_expr (by rw [h_node])
  | .Assert ⟨condExpr, summary⟩ =>
    synthAssert exprMd condExpr summary source (by rw [h_node])
  | .Assume cond =>
    synthAssume exprMd cond source (by rw [h_node])
  | .ProveBy val proof =>
    synthProveBy exprMd val proof (by rw [h_node])
  | .ContractOf ty fn =>
    synthContractOf exprMd ty fn source (by rw [h_node])
  | .Abstract => pure (synthAbstract source)
  | .All => pure (synthAll source)
  | .Hole det type => synthHole det type source
  return ({ val := val', source := source }, ty)
  termination_by (exprMd, 2)
  decreasing_by all_goals first
    | (apply Prod.Lex.left; term_by_mem)
    | (try subst h_node; apply Prod.Lex.right; decide)
    | (apply Prod.Lex.right; decide)

/-- Check-mode resolution (rule **Sub** at the boundary): resolve `e` and
    verify its type is a consistent subtype of `expected`. Bidirectional rules
    for individual constructs push `expected` into subexpressions; everything
    else falls back to subsumption (synth, then `isConsistentSubtype actual
    expected`). -/
def checkStmtExpr (exprMd : StmtExprMd) (expected : HighTypeMd) : ResolveM StmtExprMd := do
  match h_node: exprMd with
  | AstNode.mk expr source =>
  match h_expr: expr with
  | .Block stmts label =>
    checkBlock exprMd stmts label expected source (by rw [h_node])
  | .IfThenElse cond thenBr elseBr =>
    checkIfThenElse exprMd cond thenBr elseBr expected source (by rw [h_node])
  | .Assign targets value =>
    checkAssign exprMd targets value expected source (by rw [h_node])
  | .Hole det none => pure (checkHoleNone det expected source)
  | _ =>
    -- Subsumption fallback: synth then check `actual <: expected`.
    let (e', actual) ← synthStmtExpr exprMd
    checkSubtype source expected actual
    pure e'
  termination_by (exprMd, 3)
  decreasing_by all_goals first
    | (apply Prod.Lex.left; term_by_mem)
    | (try subst_eqs; apply Prod.Lex.right; decide)
    | (try subst h_node; apply Prod.Lex.right; decide)
    | (apply Prod.Lex.right; decide)

-- ### Literals

/-- Rule **Lit-Int**: `Γ ⊢ LiteralInt n ⇒ TInt`. -/
def synthLitInt (v : Int) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralInt v, { val := .TInt, source := source })

/-- Rule **Lit-Bool**: `Γ ⊢ LiteralBool b ⇒ TBool`. -/
def synthLitBool (v : Bool) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralBool v, { val := .TBool, source := source })

/-- Rule **Lit-String**: `Γ ⊢ LiteralString s ⇒ TString`. -/
def synthLitString (v : String) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralString v, { val := .TString, source := source })

/-- Rule **Lit-Decimal**: `Γ ⊢ LiteralDecimal d ⇒ TReal`. -/
def synthLitDecimal (v : Decimal) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralDecimal v, { val := .TReal, source := source })

-- ### Variables

/-- Rule **Var-Local**: `Γ(x) = T ⊢ Var (.Local x) ⇒ T`. Resolves `ref` against
    the lexical scope and reads its declared type. -/
def synthVarLocal (ref : Identifier) (source : Option FileRange) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let ref' ← resolveRef ref source
  let ty ← getVarType ref
  pure (.Var (.Local ref'), ty)

/-- Rule **Var-Declare**: extends the surrounding scope with `x : T` and
    synthesizes `TVoid` (the declaration itself produces no value). -/
def synthVarDeclare (param : Parameter) (source : Option FileRange) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let ty' ← resolveHighType param.type
  let name' ← defineNameCheckDup param.name (.var param.name ty')
  pure (.Var (.Declare ⟨name', ty'⟩), { val := .TVoid, source := source })

/-- Rule **Var-Field**: `Γ ⊢ e ⇒ _, Γ(f) = T_f ⊢ Var (.Field e f) ⇒ T_f`.
    `f` is looked up against the type of `e` (or the enclosing instance type
    for `self.f`); the typing rule itself is path-agnostic. -/
def synthVarField (exprMd : StmtExprMd)
    (target : StmtExprMd) (fieldName : Identifier) (source : Option FileRange)
    (h : exprMd.val = .Var (.Field target fieldName)) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', _) ← synthStmtExpr target
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

-- ### Control flow

/-- Rules **If-NoElse** / **If-Synth**: `cond` is checked against `TBool`.
    With no else branch, the construct is a statement — `thenBr` is checked
    against `TVoid` and the result is `TVoid`, so `if c then 5` is rejected.
    With an else branch, the result type is the join (LUB) of the two
    branches' synthesized types, so `if c then new Left else new Right`
    synthesizes the common ancestor `Top` rather than committing to one
    branch arbitrarily. When no common supertype exists (e.g. a value branch
    paired with a `TVoid` `return`/`exit`), `joinTypes` falls back to the
    then-branch's type and the enclosing context's check surfaces any
    mismatch downstream. -/
def synthIfThenElse (exprMd : StmtExprMd)
    (cond thenBr : StmtExprMd) (elseBr : Option StmtExprMd)
    (h : exprMd.val = .IfThenElse cond thenBr elseBr) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let cond' ← checkStmtExpr cond { val := .TBool, source := cond.source }
  let voidTy : HighTypeMd := { val := .TVoid, source := exprMd.source }
  match elseBr with
  | none =>
    let thenBr' ← checkStmtExpr thenBr voidTy
    pure (.IfThenElse cond' thenBr' none, voidTy)
  | some e =>
    let (thenBr', thenTy) ← synthStmtExpr thenBr
    let (elseBr', elseTy) ← synthStmtExpr e
    let ctx := (← get).typeContext
    pure (.IfThenElse cond' thenBr' (some elseBr'), joinTypes ctx thenTy elseTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.left
         have hsz := exprMd.sizeOf_val_lt
         simp [h] at hsz
         try simp_all
         try omega)
      | (apply Prod.Lex.right; decide)

/-- Rules **Block-Synth** / **Block-Synth-Empty**: non-last statements are
    synthesized but their types discarded (the lax rule, matching
    Java/Python/JS expression-statement semantics); the last statement's type
    becomes the block's type, or `TVoid` for an empty block. The block opens
    a fresh nested scope. -/
def synthBlock (exprMd : StmtExprMd)
    (stmts : List StmtExprMd) (label : Option String)
    (h : exprMd.val = .Block stmts label) :
    ResolveM (StmtExpr × HighTypeMd) := do
  withScope do
    let results ← stmts.mapM synthStmtExpr
    let stmts' := results.map (·.1)
    let lastTy := match results.getLast? with
      | some (_, ty) => ty
      | none => { val := .TVoid, source := exprMd.source }
    pure (.Block stmts' label, lastTy)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    have := List.sizeOf_lt_of_mem ‹_ ∈ stmts›
    omega

/-- Rule **While**: `cond ⇐ TBool`, each invariant `⇐ TBool`, optional
    `decreases` is resolved without a type check (intended target is numeric),
    body is synthesized; the construct itself synthesizes `TVoid`. -/
def synthWhile (exprMd : StmtExprMd)
    (cond : StmtExprMd) (invs : List StmtExprMd)
    (dec : Option StmtExprMd) (body : StmtExprMd)
    (h : exprMd.val = .While cond invs dec body) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let cond' ← checkStmtExpr cond { val := .TBool, source := cond.source }
  let invs' ← invs.attach.mapM (fun a => have := a.property; do
    checkStmtExpr a.val { val := .TBool, source := a.val.source })
  let dec' ← dec.attach.mapM (fun a => have := a.property; do
    let (e', _) ← synthStmtExpr a.val; pure e')
  let (body', _) ← synthStmtExpr body
  pure (.While cond' invs' dec' body', { val := .TVoid, source := exprMd.source })
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try (have := List.sizeOf_lt_of_mem ‹_ ∈ invs›)
      try simp_all
      omega

/-- Rule **Exit**: `Γ ⊢ Exit target ⇒ TVoid`. -/
def synthExit (target : String) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.Exit target, { val := .TVoid, source := source })

/-- Rules **Return-None** / **Return-Some** / **Return-Void-Error** /
    **Return-Multi-Error**: matches the optional return value against the
    enclosing procedure's declared outputs (`expectedReturnTypes`). `none`
    means "no enclosing procedure" — e.g. resolving a constant initializer —
    and skips all `Return` checks. -/
def synthReturn (exprMd : StmtExprMd) (source : Option FileRange)
    (val : Option StmtExprMd)
    (h : exprMd.val = .Return val) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let expected := (← get).expectedReturnTypes
  let val' ← val.attach.mapM (fun a => have := a.property; do
    match expected with
    | some [singleOutput] => checkStmtExpr a.val singleOutput
    | _ => let (e', _) ← synthStmtExpr a.val; pure e')
  -- Arity/shape diagnostics independent of the value's own type.
  match val, expected with
  | none,   some []          => pure ()
  | none,   some [_]         => pure ()  -- Dafny-style early exit
  | none,   some _           => pure ()  -- multi-output: bare return is fine
  | some _, some []          =>
    let diag := diagnosticFromSource source
      "void procedure cannot return a value"
    modify fun s => { s with errors := s.errors.push diag }
  | some _, some [_]         => pure ()  -- value already checked above
  | some _, some _           =>
    let diag := diagnosticFromSource source
      "multi-output procedure cannot use 'return e'; assign to named outputs instead"
    modify fun s => { s with errors := s.errors.push diag }
  | _,      none             => pure ()  -- no enclosing procedure
  pure (.Return val', { val := .TVoid, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      simp_all
      omega

/-- Rules **Block-Check** / **Block-Check-Empty**: pushes `expected` into the
    *last* statement rather than comparing the block's synthesized type at the
    boundary. Errors fire at the offending subexpression, and `T` keeps
    propagating through nested `Block` / `IfThenElse` / `Hole` / `Quantifier`.
    Empty blocks reduce to a subsumption check of `TVoid` against `expected`. -/
def checkBlock (exprMd : StmtExprMd)
    (stmts : List StmtExprMd) (label : Option String)
    (expected : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .Block stmts label) : ResolveM StmtExprMd := do
  withScope do
    let init' ← stmts.dropLast.attach.mapM (fun ⟨s, hMem⟩ => do
      have : s ∈ stmts := List.dropLast_subset stmts hMem
      let (s', _) ← synthStmtExpr s; pure s')
    match _lastResult: stmts.getLast? with
    | none =>
      checkSubtype source expected { val := .TVoid, source := source }
      pure { val := .Block init' label, source := source }
    | some last =>
      have := List.mem_of_getLast? _lastResult
      let last' ← checkStmtExpr last expected
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

/-- Rules **If-Check** / **If-Check-NoElse**: pushes `expected` into both
    branches (rather than going through If-Synth + Sub at the boundary).
    Errors fire at the offending branch instead of the surrounding `if`.
    Without an else branch, the construct can only succeed when `T` admits
    `TVoid`. -/
def checkIfThenElse (exprMd : StmtExprMd)
    (cond thenBr : StmtExprMd) (elseBr : Option StmtExprMd)
    (expected : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .IfThenElse cond thenBr elseBr) : ResolveM StmtExprMd := do
  let cond' ← checkStmtExpr cond { val := .TBool, source := cond.source }
  let thenBr' ← checkStmtExpr thenBr expected
  let elseBr' ← elseBr.attach.mapM (fun ⟨e, _⟩ => checkStmtExpr e expected)
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

/-- Rule **Assert**: `cond` is checked against `TBool`; the construct
    synthesizes `TVoid`. -/
def synthAssert (exprMd : StmtExprMd)
    (condExpr : StmtExprMd) (summary : Option String) (source : Option FileRange)
    (h : exprMd.val = .Assert ⟨condExpr, summary⟩) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let cond' ← checkStmtExpr condExpr { val := .TBool, source := condExpr.source }
  pure (.Assert { condition := cond', summary }, { val := .TVoid, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    try simp_all
    omega

/-- Rule **Assume**: `cond` is checked against `TBool`; the construct
    synthesizes `TVoid`. -/
def synthAssume (exprMd : StmtExprMd)
    (cond : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .Assume cond) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let cond' ← checkStmtExpr cond { val := .TBool, source := cond.source }
  pure (.Assume cond', { val := .TVoid, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    try simp_all
    omega

-- ### Assignment

/-- Rule **Assign**: each target's declared type `T_i` (from `Local`,
    `Field`, or fresh `Declare`) is collapsed into a tuple `ExpectedTy`
    (single type if one target, otherwise `MultiValuedExpr [T_1; …; T_n]`)
    and checked against the RHS's synthesized type. When the RHS is a
    statement (`TVoid`) — `while`, `return`, … — all checks are skipped:
    there's no value to assign. The construct synthesizes the RHS's type,
    so that expression-position assignments like `x ++ (y := s)` see a
    string in the second operand; statement-position uses are accommodated
    by `checkAssign`, which accepts `TVoid` as the expected type. -/
def synthAssign (exprMd : StmtExprMd)
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
      let (target', _) ← synthStmtExpr target
      let fieldName' ← resolveFieldRef target' fieldName source
      pure (⟨.Field target' fieldName', vs⟩ : VariableMd)
    | .Declare param =>
      let ty' ← resolveHighType param.type
      let name' ← defineNameCheckDup param.name (.var param.name ty')
      pure (⟨.Declare ⟨name', ty'⟩, vs⟩ : VariableMd)
  let (value', valueTy) ← synthStmtExpr value
  let targetType (t : VariableMd) : ResolveM HighTypeMd := do
    match t.val with
    | .Local ref => getVarType ref
    | .Declare param => pure param.type
    | .Field _ fieldName => getVarType fieldName
  if valueTy.val != HighType.TVoid then
    let targetTys ← targets'.mapM targetType
    let expectedTy : HighTypeMd := match targetTys with
      | [single] => single
      | _        => { val := .MultiValuedExpr targetTys, source := source }
    checkSubtype source expectedTy valueTy
  pure (.Assign targets' value', valueTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try simp_all
      try (have := List.sizeOf_lt_of_mem ‹_ ∈ targets›; simp_all)
      omega

/-- Rule **Assign-Check**: an assignment in statement position (checked
    against `TVoid`) discards its RHS value, so the synthesized type is not
    compared against `expected`. This lets `b := 1` appear as the last
    statement of a block in an else-less `if` (whose branch is checked
    against `TVoid`) without firing a subsumption error against the RHS's
    type. For non-`TVoid` expected types, falls back to subsumption. -/
def checkAssign (exprMd : StmtExprMd)
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
      let (target', _) ← synthStmtExpr target
      let fieldName' ← resolveFieldRef target' fieldName source
      pure (⟨.Field target' fieldName', vs⟩ : VariableMd)
    | .Declare param =>
      let ty' ← resolveHighType param.type
      let name' ← defineNameCheckDup param.name (.var param.name ty')
      pure (⟨.Declare ⟨name', ty'⟩, vs⟩ : VariableMd)
  let (value', valueTy) ← synthStmtExpr value
  let targetType (t : VariableMd) : ResolveM HighTypeMd := do
    match t.val with
    | .Local ref => getVarType ref
    | .Declare param => pure param.type
    | .Field _ fieldName => getVarType fieldName
  if valueTy.val != HighType.TVoid then
    let targetTys ← targets'.mapM targetType
    let assignedTy : HighTypeMd := match targetTys with
      | [single] => single
      | _        => { val := .MultiValuedExpr targetTys, source := source }
    checkSubtype source assignedTy valueTy
  unless expected.val matches .TVoid do
    checkSubtype source expected valueTy
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

/-- Rules **Static-Call** / **Static-Call-Multi**: callee is resolved against
    the expected kinds (parameter, static procedure, datatype constructor,
    constant); each argument is synthesized and checked against the
    corresponding parameter type. The result type is the (possibly
    multi-valued) declared output type from `getCallInfo`. -/
def synthStaticCall (exprMd : StmtExprMd)
    (callee : Identifier) (args : List StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .StaticCall callee args) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let callee' ← resolveRef callee source
    (expected := #[.parameter, .staticProcedure, .datatypeConstructor, .constant])
  let results ← args.mapM synthStmtExpr
  let args' := results.map (·.1)
  let argTypes := results.map (·.2)
  let (retTy, paramTypes) ← getCallInfo callee
  for ((a, aTy), paramTy) in (args'.zip argTypes).zip paramTypes do
    checkSubtype a.source paramTy aTy
  pure (.StaticCall callee' args', retTy)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    have := List.sizeOf_lt_of_mem ‹_ ∈ args›
    omega

/-- Rule **Instance-Call**: target is synthesized; callee resolves to an
    instance or static procedure; arguments are checked pairwise against the
    callee's parameter types after dropping `self`. -/
def synthInstanceCall (exprMd : StmtExprMd)
    (target : StmtExprMd) (callee : Identifier) (args : List StmtExprMd)
    (source : Option FileRange)
    (h : exprMd.val = .InstanceCall target callee args) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', _) ← synthStmtExpr target
  let callee' ← resolveRef callee source
    (expected := #[.instanceProcedure, .staticProcedure])
  let results ← args.mapM synthStmtExpr
  let args' := results.map (·.1)
  let argTypes := results.map (·.2)
  let (retTy, paramTypes) ← getCallInfo callee
  let callParamTypes := match paramTypes with | _ :: rest => rest | [] => []
  for ((a, aTy), paramTy) in (args'.zip argTypes).zip callParamTypes do
    checkSubtype a.source paramTy aTy
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

/-- Rules **Op-Bool** / **Op-Cmp** / **Op-Eq** / **Op-Arith** / **Op-Concat**:
    each operator family has its own argument-type discipline and result
    type. Arguments are synthesized first, then the per-family check fires
    (`⇐ TBool` for booleans, `Numeric` for arithmetic/comparison, consistency
    `~` for equality, `⇐ TString` for concatenation). The result type is
    `TBool` for booleans/comparisons/equality, the head argument's type for
    arithmetic, `TString` for concatenation. -/
def synthPrimitiveOp (exprMd : StmtExprMd) (expr : StmtExpr)
    (op : Operation) (args : List StmtExprMd) (source : Option FileRange)
    (h_expr : expr = .PrimitiveOp op args)
    (h : exprMd.val = .PrimitiveOp op args) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let _ := h_expr  -- carries the constructor identity for `expr` in diagnostics
  let results ← args.mapM synthStmtExpr
  let args' := results.map (·.1)
  let argTypes := results.map (·.2)
  let resultTy := match op with
    | .Eq | .Neq | .And | .Or | .AndThen | .OrElse | .Not | .Implies
    | .Lt | .Leq | .Gt | .Geq => HighType.TBool
    | .Neg | .Add | .Sub | .Mul | .Div | .Mod | .DivT | .ModT =>
      match argTypes.head? with
      | some headTy => headTy.val
      | none => HighType.TInt
    | .StrConcat => HighType.TString
  match op with
  | .And | .Or | .AndThen | .OrElse | .Not | .Implies =>
    for (a, aTy) in args'.zip argTypes do
      checkSubtype a.source { val := .TBool, source := a.source } aTy
  | .Neg | .Add | .Sub | .Mul | .Div | .Mod | .DivT | .ModT | .Lt | .Leq | .Gt | .Geq =>
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
          s!"Operands of '{op}' have incompatible types '{formatType lhsTy}' and '{formatType rhsTy}'"
        modify fun s => { s with errors := s.errors.push diag }
    | _ => pure ()
  | .StrConcat =>
    for (a, aTy) in args'.zip argTypes do
      checkSubtype a.source { val := .TString, source := a.source } aTy
  pure (.PrimitiveOp op args', { val := resultTy, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    have := List.sizeOf_lt_of_mem ‹_ ∈ args›
    omega

-- ### Object forms

/-- Rules **New-Ok** / **New-Fallback**: when `ref` resolves to a composite or
    datatype, the type is `UserDefined ref`; otherwise `Unknown` (suppresses
    cascading errors after the kind diagnostic has already fired). -/
def synthNew (ref : Identifier) (source : Option FileRange) :
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

/-- Rule **AsType**: `target` is resolved but not checked against `T` — the
    cast is the user's claim. The synthesized type is `T`. -/
def synthAsType (exprMd : StmtExprMd)
    (target : StmtExprMd) (ty : HighTypeMd)
    (h : exprMd.val = .AsType target ty) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', _) ← synthStmtExpr target
  let ty' ← resolveHighType ty
  pure (.AsType target' ty', ty')
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- Rule **IsType**: `target` is resolved; the synthesized type is `TBool`. -/
def synthIsType (exprMd : StmtExprMd)
    (target : StmtExprMd) (ty : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .IsType target ty) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', _) ← synthStmtExpr target
  let ty' ← resolveHighType ty
  pure (.IsType target' ty', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- Rule **RefEq**: both operands must be reference types (`UserDefined` or
    `Unknown`). Reference equality is meaningless on primitives. -/
def synthRefEq (exprMd : StmtExprMd) (expr : StmtExpr)
    (lhs rhs : StmtExprMd) (source : Option FileRange)
    (h_expr : expr = .ReferenceEquals lhs rhs)
    (h : exprMd.val = .ReferenceEquals lhs rhs) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let _ := h_expr
  let (lhs', lhsTy) ← synthStmtExpr lhs
  let (rhs', rhsTy) ← synthStmtExpr rhs
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

/-- Rule **PureFieldUpdate**: `target` is synthesized, `f` resolved against
    `T_t` (or the enclosing instance type), and `newVal` checked against the
    field's declared type. The synthesized type is `T_t` — updating a field
    on a pure type produces a new value of the same type. -/
def synthPureFieldUpdate (exprMd : StmtExprMd)
    (target : StmtExprMd) (fieldName : Identifier) (newVal : StmtExprMd)
    (h : exprMd.val = .PureFieldUpdate target fieldName newVal) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', targetTy) ← synthStmtExpr target
  let fieldName' ← resolveFieldRef target' fieldName target.source
  let fieldTy ← getVarType fieldName'
  let newVal' ← checkStmtExpr newVal fieldTy
  pure (.PureFieldUpdate target' fieldName' newVal', targetTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      omega

-- ### Verification expressions

/-- Rule **Quantifier**: opens a fresh scope, binds `x : T`, resolves the
    optional trigger, and checks the body against `TBool`. The construct
    itself synthesizes `TBool` since a quantifier is a proposition. -/
def synthQuantifier (exprMd : StmtExprMd)
    (mode : QuantifierMode) (param : Parameter)
    (trigger : Option StmtExprMd) (body : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .Quantifier mode param trigger body) :
    ResolveM (StmtExpr × HighTypeMd) := do
  withScope do
    let paramTy' ← resolveHighType param.type
    let paramName' ← defineNameCheckDup param.name (.quantifierVar param.name paramTy')
    let trigger' ← trigger.attach.mapM (fun pv => have := pv.property; do
      let (e', _) ← synthStmtExpr pv.val; pure e')
    let body' ← checkStmtExpr body { val := .TBool, source := body.source }
    pure (.Quantifier mode ⟨paramName', paramTy'⟩ trigger' body', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      try simp_all
      omega

/-- Rule **Assigned**: `name` is synthesized; the construct synthesizes
    `TBool`. -/
def synthAssigned (exprMd : StmtExprMd)
    (name : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .Assigned name) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (name', _) ← synthStmtExpr name
  pure (.Assigned name', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- Rule **Old**: `Γ ⊢ v ⇒ T ⊢ Old v ⇒ T`. -/
def synthOld (exprMd : StmtExprMd)
    (val : StmtExprMd)
    (h : exprMd.val = .Old val) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (val', valTy) ← synthStmtExpr val
  pure (.Old val', valTy)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- Rule **Fresh**: `v` is synthesized and must have a reference type
    (`UserDefined` or `Unknown`). The construct itself synthesizes `TBool`. -/
def synthFresh (exprMd : StmtExprMd) (expr : StmtExpr)
    (val : StmtExprMd) (source : Option FileRange)
    (h_expr : expr = .Fresh val)
    (h : exprMd.val = .Fresh val) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let _ := h_expr
  let (val', valTy) ← synthStmtExpr val
  unless isReference (← get).typeContext valTy do
    typeMismatch val'.source (some expr) "expected a reference type" valTy
  pure (.Fresh val', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    simp [h] at hsz
    omega

/-- Rule **ProveBy**: `v` and `proof` are both synthesized; the construct's
    type is `v`'s type — `proof` is a hint for downstream verification. -/
def synthProveBy (exprMd : StmtExprMd)
    (val proof : StmtExprMd)
    (h : exprMd.val = .ProveBy val proof) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (val', valTy) ← synthStmtExpr val
  let (proof', _) ← synthStmtExpr proof
  pure (.ProveBy val' proof', valTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      simp [h] at hsz
      omega

-- ### Self reference

/-- Rules **This-Inside** / **This-Outside**: when `instanceTypeName` is set
    (we're inside an instance method), `This` synthesizes `UserDefined T`;
    otherwise an error is emitted and the type collapses to `Unknown`. -/
def synthThis (source : Option FileRange) :
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

/-- Rule **Abstract**: synthesizes `Unknown`. -/
def synthAbstract (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.Abstract, { val := .Unknown, source := source })

/-- Rule **All**: synthesizes `Unknown`. -/
def synthAll (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.All, { val := .Unknown, source := source })

-- ### ContractOf

/-- Rules **ContractOf-Bool** / **ContractOf-Set** / **ContractOf-Error**:
    `fn` must be a direct identifier reference resolving to a procedure;
    anything else is ill-formed (a contract belongs to a *named* procedure).
    Pre/postconditions are propositions (`TBool`); reads/modifies are sets of
    heap references with element type `Unknown` for now. -/
def synthContractOf (exprMd : StmtExprMd)
    (ty : ContractType) (fn : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .ContractOf ty fn) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (fn', _) ← synthStmtExpr fn
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

/-- Rules **Hole-Some** / **Hole-None-Synth**: a typed hole synthesizes its
    annotation; an untyped hole in synth position synthesizes `Unknown`. -/
def synthHole (det : Bool) (type : Option HighTypeMd) (source : Option FileRange) :
    ResolveM (StmtExpr × HighTypeMd) := do
  match type with
  | some ty =>
    let ty' ← resolveHighType ty
    pure (.Hole det ty', ty')
  | none => pure (.Hole det none, { val := .Unknown, source := source })

/-- Rule **Hole-None-Check**: an untyped hole in check mode records the
    expected type on the node so downstream passes don't have to infer it
    again. The subsumption check is trivial (`Unknown <: T` always holds), so
    this rule never fails — it just preserves the type information available
    at the check-mode boundary. -/
def checkHoleNone (det : Bool) (expected : HighTypeMd) (source : Option FileRange) :
    StmtExprMd :=
  { val := .Hole det (some expected), source := source }

end

/-- Resolve a statement expression, discarding the synthesized type.
    Use when only the resolved expression is needed (invariants, decreases, etc.). -/
private def resolveStmtExpr (e : StmtExprMd) : ResolveM StmtExprMd := do
  let (e', _) ← synthStmtExpr e; pure e'

/-- Resolve a parameter: assign a fresh ID and add to scope. -/
def resolveParameter (param : Parameter) : ResolveM Parameter := do
  let ty' ← resolveHighType param.type
  let name' ← defineNameCheckDup param.name (.parameter ⟨param.name, ty'⟩)
  return ⟨name', ty'⟩

/-- Resolve a procedure body. Returns the resolved body and its type. -/
def resolveBody (body : Body) : ResolveM (Body × HighTypeMd) := do
  match body with
  | .Transparent b =>
    let (b', ty) ← synthStmtExpr b
    return (.Transparent b', ty)
  | .Opaque posts impl mods =>
    let posts' ← posts.mapM (·.mapM resolveStmtExpr)
    let impl' ← impl.mapM resolveStmtExpr
    let mods' ← mods.mapM resolveStmtExpr
    return (.Opaque posts' impl' mods', { val := .TVoid, source := none })
  | .Abstract posts =>
    let posts' ← posts.mapM (·.mapM resolveStmtExpr)
    return (.Abstract posts', { val := .TVoid, source := none })
  | .External => return (.External, { val := .TVoid, source := none })

/-- Resolve a procedure: resolve its name, then resolve params, contracts, and body in a new scope. -/
def resolveProcedure (proc : Procedure) : ResolveM Procedure := do
  let procName' ← resolveRef proc.name
  withScope do
    let inputs' ← proc.inputs.mapM resolveParameter
    let outputs' ← proc.outputs.mapM resolveParameter
    let pres' ← proc.preconditions.mapM (·.mapM resolveStmtExpr)
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let savedReturns := (← get).expectedReturnTypes
    modify fun s => { s with expectedReturnTypes := some (outputs'.map (·.type)) }
    let (body', bodyTy) ← resolveBody proc.body
    modify fun s => { s with expectedReturnTypes := savedReturns }
    if !proc.isFunctional && body'.isTransparent then
      let diag := diagnosticFromSource proc.name.source
        s!"transparent procedures are not yet supported. Add 'opaque' to make the procedure opaque"
      modify fun s => { s with errors := s.errors.push diag }
    -- Check body type matches declared output type for functional procedures with transparent bodies
    if proc.isFunctional && body'.isTransparent then
      match proc.outputs with
      | [singleOutput] =>
        -- Only check when body produces a value (not void from return/while/assign)
        if bodyTy.val != HighType.TVoid then
          checkSubtype proc.name.source singleOutput.type bodyTy
      | _ => pure ()
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
    let savedReturns := (← get).expectedReturnTypes
    modify fun s => { s with expectedReturnTypes := some (outputs'.map (·.type)) }
    let (body', bodyTy) ← resolveBody proc.body
    modify fun s => { s with expectedReturnTypes := savedReturns }
    if !proc.isFunctional && body'.isTransparent then
      let diag := diagnosticFromSource proc.name.source
        s!"transparent procedures are not yet supported. Add 'opaque' to make the procedure opaque"
      modify fun s => { s with errors := s.errors.push diag }
    -- Check body type matches declared output type for functional procedures with transparent bodies
    if proc.isFunctional && body'.isTransparent then
      match proc.outputs with
      | [singleOutput] =>
        if bodyTy.val != HighType.TVoid then
          checkSubtype proc.name.source singleOutput.type bodyTy
      | _ => pure ()
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
      let (constraint', _) ← synthStmtExpr ct.constraint
      let (witness', _) ← synthStmtExpr ct.witness
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
  let init' ← c.initializer.mapM (checkStmtExpr · ty')
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
