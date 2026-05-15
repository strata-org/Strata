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
  unless isConsistentSubtype actual expected do
    typeMismatch source none s!"expected '{formatType expected}'" actual

/-- Test whether a type is in the set of numeric primitives. `Unknown` and
    `TCore` are accepted as gradual escape hatches. Used by Op-Cmp / Op-Arith. -/
private def isNumeric (ty : HighTypeMd) : Bool :=
  match ty.val with
  | .TInt | .TReal | .TFloat64 | .Unknown => true
  | .TCore _ => true
  | _ => false

/-- Test whether a type is a user-defined reference type. `Unknown` and `TCore`
    are accepted as gradual escape hatches. Used by Fresh and ReferenceEquals,
    which only make sense on composite/datatype references. -/
private def isReference (ty : HighTypeMd) : Bool :=
  match ty.val with
  | .UserDefined _ | .Unknown => true
  | .TCore _ => true
  | _ => false

/-- Get the type of a resolved variable reference from scope. -/
private def getVarType (ref : Identifier) : ResolveM HighTypeMd := do
  let s ← get
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

mutual
def synthStmtExpr (exprMd : StmtExprMd) : ResolveM (StmtExprMd × HighTypeMd) := do
  match _: exprMd with
  | AstNode.mk expr source =>
  let (val', ty) ← match _: expr with
  | .IfThenElse cond thenBr elseBr =>
    -- Condition is checked against TBool. The result type is TVoid when the
    -- else branch is absent (statement form: the then-branch's value is
    -- discarded), otherwise the then-branch's synthesized type. We don't
    -- compare the two branches against each other since statement-position
    -- ifs commonly mix a value branch with a TVoid branch (return/exit).
    let cond' ← checkStmtExpr cond { val := .TBool, source := cond.source }
    let (thenBr', thenTy) ← synthStmtExpr thenBr
    let elseBr' ← elseBr.attach.mapM (fun a => have := a.property; do
      let (e', _) ← synthStmtExpr a.val; pure e')
    let resultTy := match elseBr with
      | none => { val := .TVoid, source := source }
      | some _ => thenTy
    pure (.IfThenElse cond' thenBr' elseBr', resultTy)
  | .Block stmts label =>
    -- Synth-mode block: non-last statements have their synthesized type discarded
    -- (lax rule, matches Java/Python/JS expression-statement semantics).
    -- The last statement's synthesized type becomes the block's type.
    withScope do
      let results ← stmts.mapM synthStmtExpr
      let stmts' := results.map (·.1)
      let lastTy := match results.getLast? with
        | some (_, ty) => ty
        | none => { val := .TVoid, source := source }
      pure (.Block stmts' label, lastTy)
  | .While cond invs dec body =>
    let cond' ← checkStmtExpr cond { val := .TBool, source := cond.source }
    let invs' ← invs.attach.mapM (fun a => have := a.property; do
      checkStmtExpr a.val { val := .TBool, source := a.val.source })
    let dec' ← dec.attach.mapM (fun a => have := a.property; do
      let (e', _) ← synthStmtExpr a.val; pure e')
    let (body', _) ← synthStmtExpr body
    pure (.While cond' invs' dec' body', { val := .TVoid, source := source })
  | .Exit target => pure (.Exit target, { val := .TVoid, source := source })
  | .Return val => do
    -- Match the optional return value against the enclosing procedure's
    -- declared outputs. `expectedReturnTypes = none` means we're not inside a
    -- procedure body (e.g. resolving a constant initializer); skip the check.
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
  | .LiteralInt v => pure (.LiteralInt v, { val := .TInt, source := source })
  | .LiteralBool v => pure (.LiteralBool v, { val := .TBool, source := source })
  | .LiteralString v => pure (.LiteralString v, { val := .TString, source := source })
  | .LiteralDecimal v => pure (.LiteralDecimal v, { val := .TReal, source := source })
  | .Var (.Local ref) =>
    let ref' ← resolveRef ref source
    let ty ← getVarType ref
    pure (.Var (.Local ref'), ty)
  | .Var (.Declare param) =>
    let ty' ← resolveHighType param.type
    let name' ← defineNameCheckDup param.name (.var param.name ty')
    pure (.Var (.Declare ⟨name', ty'⟩), { val := .TVoid, source := source })
  | .Assign targets value =>
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
    -- Check that LHS target count matches the RHS arity (derived from the value type).
    let expectedOutputCount := match valueTy.val with
      | .MultiValuedExpr tys => tys.length
      | _ => 1
    if valueTy.val != HighType.TVoid && targets'.length != expectedOutputCount then
      let diag := diagnosticFromSource source
        s!"Assignment target count mismatch: {targets'.length} targets but right-hand side produces {expectedOutputCount} values"
      modify fun s => { s with errors := s.errors.push diag }
    -- Type check: for single-target assignments, check value type matches target type
    -- Skip when value type is void (RHS is a statement like while/return that doesn't produce a value)
    -- Skip when there's an arity mismatch (already reported above)
    if targets'.length == 1 && targets'.length == expectedOutputCount && valueTy.val != HighType.TVoid then
      if let some target := targets'.head? then
        let targetTy := match target.val with
          | .Local ref => do
            let s ← get
            match s.scope.get? ref.text with
            | some (_, node) => pure node.getType
            | none => pure { val := HighType.Unknown, source := ref.source : HighTypeMd }
          | .Declare param => pure param.type
          | .Field _ fieldName => do
            let s ← get
            match s.scope.get? fieldName.text with
            | some (_, node) => pure node.getType
            | none => pure { val := HighType.Unknown, source := fieldName.source : HighTypeMd }
        let tTy ← targetTy
        checkSubtype source tTy valueTy
    pure (.Assign targets' value', valueTy)
  | .Var (.Field target fieldName) =>
    let (target', _) ← synthStmtExpr target
    let fieldName' ← resolveFieldRef target' fieldName source
    let ty ← getVarType fieldName
    pure (.Var (.Field target' fieldName'), ty)
  | .PureFieldUpdate target fieldName newVal =>
    let (target', targetTy) ← synthStmtExpr target
    let fieldName' ← resolveFieldRef target' fieldName source
    let fieldTy ← getVarType fieldName'
    let newVal' ← checkStmtExpr newVal fieldTy
    pure (.PureFieldUpdate target' fieldName' newVal', targetTy)
  | .StaticCall callee args =>
    let callee' ← resolveRef callee source
      (expected := #[.parameter, .staticProcedure, .datatypeConstructor, .constant])
    let results ← args.mapM synthStmtExpr
    let args' := results.map (·.1)
    let argTypes := results.map (·.2)
    let (retTy, paramTypes) ← getCallInfo callee
    for (argTy, paramTy) in argTypes.zip paramTypes do
      checkSubtype source paramTy argTy
    pure (.StaticCall callee' args', retTy)
  | .PrimitiveOp op args =>
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
      for aTy in argTypes do
        checkSubtype source { val := .TBool, source := aTy.source } aTy
    | .Neg | .Add | .Sub | .Mul | .Div | .Mod | .DivT | .ModT | .Lt | .Leq | .Gt | .Geq =>
      for aTy in argTypes do
        unless isNumeric aTy do
          typeMismatch aTy.source (some expr) "expected a numeric type" aTy
    | .Eq | .Neq =>
      match argTypes with
      | [lhsTy, rhsTy] =>
        unless isConsistent lhsTy rhsTy do
          let diag := diagnosticFromSource source
            s!"Operands of '{op}' have incompatible types '{formatType lhsTy}' and '{formatType rhsTy}'"
          modify fun s => { s with errors := s.errors.push diag }
      | _ => pure ()
    | .StrConcat =>
      for aTy in argTypes do
        checkSubtype source { val := .TString, source := aTy.source } aTy
    pure (.PrimitiveOp op args', { val := resultTy, source := source })
  | .New ref =>
    let ref' ← resolveRef ref source
      (expected := #[.compositeType, .datatypeDefinition])
    -- If the reference resolved to the wrong kind, use Unknown type to avoid cascading errors
    let s ← get
    let kindOk : Bool := match s.scope.get? ref.text with
      | some (_, node) => node.kind == .unresolved ||
          (#[ResolvedNodeKind.compositeType, .datatypeDefinition].contains node.kind)
      | none => true
    let ty := if kindOk then { val := HighType.UserDefined ref', source := source }
              else { val := HighType.Unknown, source := source }
    pure (.New ref', ty)
  | .This =>
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
  | .ReferenceEquals lhs rhs =>
    let (lhs', lhsTy) ← synthStmtExpr lhs
    let (rhs', rhsTy) ← synthStmtExpr rhs
    unless isReference lhsTy do
      typeMismatch lhsTy.source (some expr) "expected a reference type" lhsTy
    unless isReference rhsTy do
      typeMismatch rhsTy.source (some expr) "expected a reference type" rhsTy
    pure (.ReferenceEquals lhs' rhs', { val := .TBool, source := source })
  | .AsType target ty =>
    let (target', _) ← synthStmtExpr target
    let ty' ← resolveHighType ty
    pure (.AsType target' ty', ty')
  | .IsType target ty =>
    let (target', _) ← synthStmtExpr target
    let ty' ← resolveHighType ty
    pure (.IsType target' ty', { val := .TBool, source := source })
  | .InstanceCall target callee args =>
    let (target', _) ← synthStmtExpr target
    let callee' ← resolveRef callee source
      (expected := #[.instanceProcedure, .staticProcedure])
    let results ← args.mapM synthStmtExpr
    let args' := results.map (·.1)
    let argTypes := results.map (·.2)
    let (retTy, paramTypes) ← getCallInfo callee
    -- Skip first param (self) when matching args.
    let callParamTypes := match paramTypes with | _ :: rest => rest | [] => []
    for (argTy, paramTy) in argTypes.zip callParamTypes do
      checkSubtype source paramTy argTy
    pure (.InstanceCall target' callee' args', retTy)
  | .Quantifier mode param trigger body =>
    withScope do
      let paramTy' ← resolveHighType param.type
      let paramName' ← defineNameCheckDup param.name (.quantifierVar param.name paramTy')
      let trigger' ← trigger.attach.mapM (fun pv => have := pv.property; do
        let (e', _) ← synthStmtExpr pv.val; pure e')
      let body' ← checkStmtExpr body { val := .TBool, source := body.source }
      pure (.Quantifier mode ⟨paramName', paramTy'⟩ trigger' body', { val := .TBool, source := source })
  | .Assigned name =>
    let (name', _) ← synthStmtExpr name
    pure (.Assigned name', { val := .TBool, source := source })
  | .Old val =>
    let (val', valTy) ← synthStmtExpr val
    pure (.Old val', valTy)
  | .Fresh val =>
    let (val', valTy) ← synthStmtExpr val
    unless isReference valTy do
      typeMismatch valTy.source (some expr) "expected a reference type" valTy
    pure (.Fresh val', { val := .TBool, source := source })
  | .Assert ⟨condExpr, summary⟩ =>
    let cond' ← checkStmtExpr condExpr { val := .TBool, source := condExpr.source }
    pure (.Assert { condition := cond', summary }, { val := .TVoid, source := source })
  | .Assume cond =>
    let cond' ← checkStmtExpr cond { val := .TBool, source := cond.source }
    pure (.Assume cond', { val := .TVoid, source := source })
  | .ProveBy val proof =>
    let (val', valTy) ← synthStmtExpr val
    let (proof', _) ← synthStmtExpr proof
    pure (.ProveBy val' proof', valTy)
  | .ContractOf ty fn =>
    -- `fn` must be a direct identifier reference resolving to a procedure.
    -- Anything else (arbitrary expressions, references to non-procedures) is
    -- ill-formed: a contract belongs to a *named* procedure.
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
    -- Result type: Bool for pre/postconditions, set of heap references for
    -- reads/modifies. The element type of the set is left as Unknown for now
    -- since the rule doesn't recover it from `fn`.
    let resultTy : HighType := match ty with
      | .Precondition | .PostCondition => .TBool
      | .Reads | .Modifies => .TSet { val := .Unknown, source := none }
    pure (.ContractOf ty fn', { val := resultTy, source := source })
  | .Abstract => pure (.Abstract, { val := .Unknown, source := source })
  | .All => pure (.All, { val := .Unknown, source := source })
  | .Hole det type => match type with
    | some ty =>
      let ty' ← resolveHighType ty
      pure (.Hole det ty', ty')
    | none => pure (.Hole det none, { val := .Unknown, source := source })
  return ({ val := val', source := source }, ty)
  termination_by (exprMd, 0)
  decreasing_by all_goals first
    | (apply Prod.Lex.left; term_by_mem)
    | (apply Prod.Lex.right; decide)

/-- Check-mode resolution: resolve `e` and verify its type is a consistent
    subtype of `expected`. Bidirectional rules for individual constructs push
    `expected` into subexpressions; everything else falls back to subsumption
    (synth, then `isConsistentSubtype actual expected`). -/
def checkStmtExpr (exprMd : StmtExprMd) (expected : HighTypeMd) : ResolveM StmtExprMd := do
  match _: exprMd with
  | AstNode.mk expr source =>
  match _: expr with
  | .Block stmts label =>
    -- Bespoke check rule: discard non-last statement types (lax), push
    -- `expected` into the last statement. Empty block reduces to subsumption
    -- of TVoid against `expected`.
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
  | .IfThenElse cond thenBr elseBr =>
    -- Push `expected` into both branches (rather than going through the synth
    -- rule + Sub at the boundary). Without an else branch, fall back to
    -- subsumption of TVoid against `expected`.
    let cond' ← checkStmtExpr cond { val := .TBool, source := cond.source }
    let thenBr' ← checkStmtExpr thenBr expected
    let elseBr' ← elseBr.attach.mapM (fun ⟨e, _⟩ => checkStmtExpr e expected)
    if elseBr.isNone then
      checkSubtype source expected { val := .TVoid, source := source }
    pure { val := .IfThenElse cond' thenBr' elseBr', source := source }
  | .Hole det none =>
    -- Untyped hole in check mode: record the expected type on the node so
    -- downstream passes don't have to infer it again. Subsumption is trivial
    -- (Unknown <: T always holds).
    pure { val := .Hole det (some expected), source := source }
  | _ =>
    -- Subsumption fallback: synth then check `actual <: expected`.
    let (e', actual) ← synthStmtExpr exprMd
    checkSubtype source expected actual
    pure e'
  termination_by (exprMd, 1)
  decreasing_by all_goals first
    | (apply Prod.Lex.left; term_by_mem)
    | (try subst_eqs; apply Prod.Lex.right; decide)
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
