/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.UnorderedCore
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Tactics
public import Strata.Languages.Laurel.SemanticModel
public import Strata.Languages.Laurel.LaurelTypes
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

/-- The output of the resolution pass. -/
public structure ResolutionResult where
  /-- The program with unique IDs on all definition and reference nodes. -/
  program : Program
  /-- Map from reference node ID to the definition it resolves to. -/
  model : SemanticModel
  /-- Diagnostics collected during resolution (e.g. unresolved references). -/
  errors : Array DiagnosticModel := #[]

/-! ## Phase 1: ID assignment and reference resolution -/

/-- A scope entry stores the definition-site ID and the ResolvedNode for type lookups. -/
abbrev ScopeEntry := Nat × ResolvedNode

/-- Scope maps a name to its definition-site ID and optional ResolvedNode. -/
abbrev Scope := Std.HashMap String ScopeEntry

/-- Per-composite-type scope mapping field names to their scope entries. -/
abbrev TypeScopes := Std.HashMap String Scope

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
  typeLattice : TypeLattice := {}

abbrev ResolveM := StateM ResolveState

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

/-- Scope key for a name nested inside a container (composite, datatype),
    used to disambiguate members in the flat global scope. -/
private def containerScopedName (containerName memberName : Identifier) : Identifier :=
  mkId s!"{containerName.text}${memberName.text}"

/-- Declared type of `fieldName` in the scope of composite type `typeName`; `none` if
    unknown. Shared by `targetTypeName` and `incrDecrTargetType`. (`resolveFieldInTypeScope`
    below is the same walk returning the field's *id* instead of its type.) -/
private def fieldTypeInScope (typeName : String) (fieldName : Identifier) : ResolveM (Option HighType) := do
  let s ← get
  match s.typeScopes.get? typeName with
  | some typeScope =>
    match typeScope.get? fieldName.text with
    | some (_, node) => pure (some node.getType.val)
    | none => pure none
  | none => pure none

/-- UserDefined type name of a resolved target: a local directly, or a chained field
    access (`a#b#c`) by recursing on the inner target then `fieldTypeInScope`.
    Self-recursive on `.Var (.Field inner _)`; the `decreasing_by` proof below holds
    only because `inner` is a strict subterm of `target`, so recurse only on subterms. -/
private def targetTypeName (target : StmtExprMd) : ResolveM (Option String) := do
  let s ← get
  match _h : target.val with
  | .Var (.Local ref) =>
    match s.scope.get? ref.text with
    | some (_, node) =>
      match node.getType.val with
      | .UserDefined typRef => pure (some typRef.text)
      | _ => pure none
    | none => pure none
  | .Var (.Field inner fieldName) => do
    match (← targetTypeName inner) with
    | none => pure none
    | some innerTy =>
      match (← fieldTypeInScope innerTy fieldName) with
      | some (.UserDefined typRef) => pure (some typRef.text)
      | _ => pure none
  | _ => pure none
  termination_by sizeOf target
  decreasing_by
    have := AstNode.sizeOf_val_lt target
    have : sizeOf target.val = sizeOf (StmtExpr.Var (Variable.Field inner fieldName)) := congrArg sizeOf _h
    simp at this
    omega

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
    -- If the reference failed to resolve (name not defined) or resolved to the
    -- wrong kind, treat the type as Unknown to avoid cascading errors. The single
    -- "is not defined" / "wrong kind" diagnostic was already emitted by `resolveRef`;
    -- collapsing the dangling `UserDefined` to `Unknown` keeps the variable's later
    -- uses from being type-checked against a phantom type. A name that genuinely
    -- resolves to a composite/datatype/alias/constrained type stays `UserDefined`
    -- so real subtype checking still works.
    let s ← get
    let kindOk : Bool := match s.scope.get? ref.text with
      | some (_, node) => node.kind == .unresolved ||
          (#[ResolvedNodeKind.compositeType, .constrainedType, .datatypeDefinition, .typeAlias].contains node.kind)
      | none => false  -- name not defined: resolveRef already reported it
    if kindOk then pure (HighType.UserDefined ref')
    else pure HighType.Unknown
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
  let ctx := (← get).typeLattice
  unless isConsistentSubtype ctx actual expected do
    typeMismatch source none s!"expected '{formatType expected}'" actual

/-- Test whether a type is in the set of numeric primitives
    (`TInt` / `TReal` / `TFloat64` / `TBv`). `Unknown` is
    accepted as a gradual escape hatch. Aliases and constrained types are
    unfolded first so e.g. `nat` (constrained over `int`) counts as numeric.
    Used by Op-Cmp / Op-Arith. -/
private def isNumeric (ctx : TypeLattice) (ty : HighTypeMd) : Bool :=
  match (ctx.unfold ty).val with
  | .TInt | .TReal | .TFloat64 | .TBv _ | .Unknown => true
  | _ => false

/-- Least upper bound of two types under the consistency relation
    (Siek–Taha). On Laurel's flat lattice the join collapses to the
    "more informative" side: `Unknown` and `T` yields `T`; equal
    types (after unfolding) yield themselves; everything else is
    inconsistent and yields `none`.

    Used by [⇒] Op-Arith to fold operand types into a single result
    type: a homogeneous arithmetic expression `1 + 2` yields `TInt`,
    `1 + <?>` yields `TInt` (Unknown promotes), `<?> + <?>` yields
    `Unknown`, and `1 + 2.0` is rejected. -/
private def join (ctx : TypeLattice)
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
private def isReference (ctx : TypeLattice) (ty : HighTypeMd) : Bool :=
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
  | some (_, .staticProcedure proc) | some (_, .instanceProcedure _ proc) =>
    let retTy := match proc.outputs with
      | [] => { val := .TVoid, source := callee.source }
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

/-- The number of positional arguments `callee` accepts, *only* when it
    genuinely resolves to a procedure with a known parameter count. Returns
    `none` for every other resolution kind — unresolved names (whose
    `getCallInfo` `paramTypes` is `[]` purely because the name was not found),
    datatype constructors/testers, parameters, and constants — so that the
    over-arity check in the call rules does not fire on those (which would
    duplicate the already-reported name-resolution error, or wrongly flag a
    constructor/parameter/constant call).

    For an instance procedure the implicit `self` receiver is not supplied
    positionally at an `InstanceCall` site, so it is dropped here exactly as
    the `dropSelf` logic in `Synth.instanceCall` does. `dropSelf` is passed by
    the caller: `false` for `Synth.staticCall` (no `self`), and `true` for an
    instance procedure reached through `Synth.instanceCall`. -/
private def procArity (callee : Identifier) (dropSelf : Bool) : ResolveM (Option Nat) := do
  match (← get).scope.get? callee.text with
  | some (_, .staticProcedure proc) => pure (some proc.inputs.length)
  | some (_, .instanceProcedure _ proc) =>
    pure (some (if dropSelf then proc.inputs.length - 1 else proc.inputs.length))
  | _ => pure none

/-- Unfold any constrained types down to their underlying base type
    (e.g. `nat` ⇒ `int`). `fuel` keeps the function total; chains longer than
    `fuel` simply stop unfolding (the conservative, no-false-positive direction). -/
private def underlyingBaseType (s : ResolveState) (fuel : Nat) (ty : HighType) : HighType :=
  match fuel with
  | 0 => ty
  | fuel + 1 =>
    match ty with
    | .UserDefined typRef =>
      match s.scope.get? typRef.text with
      | some (_, .constrainedType ct) => underlyingBaseType s fuel ct.base.val
      | _ => ty
    | _ => ty

/-- Look up the declared type of an `IncrDecr` target during resolution.
    Handles `Local` (scope lookup) and `Field` (type-scope lookup); returns
    `none` when the type cannot be determined (e.g. an unresolved name). -/
private def incrDecrTargetType (target : VariableMd) : ResolveM (Option HighType) := do
  let s ← get
  match target.val with
  | .Local ref =>
    match s.scope.get? ref.text with
    | some (_, node) => pure (some node.getType.val)
    | none => pure none
  | .Field tgt fieldName =>
    match (← targetTypeName tgt) with
    | some typeName => fieldTypeInScope typeName fieldName
    | none => pure none
  | .Declare param => pure (some param.type.val)

/-- Emit a diagnostic if `++`/`--` is applied to an unsupported element type.
    Only `int` and int-based constrained types (e.g. `nat`) are supported by the
    `EliminateIncrDecr` lowering; `bv`, `real`, and `float64` are rejected here
    with a clear Laurel diagnostic (and a source range) rather than leaking a raw
    Core unification error from a later pass. Unknown/unresolved types are left
    alone so that resolution errors are not duplicated as spurious incr/decr
    errors. -/
private def checkIncrDecrTargetType (op : IncrDecrOp) (target : VariableMd)
    (source : Option FileRange) : ResolveM Unit := do
  match (← incrDecrTargetType target) with
  | none => pure ()
  | some ty =>
    let s ← get
    let baseTy := underlyingBaseType s 100 ty
    let unsupported? : Option String := match baseTy with
      | .TReal => some "real"
      | .TFloat64 => some "float64"
      | .TBv n => some s!"bv{n}"
      | _ => none
    match unsupported? with
    | none => pure ()
    | some tyName =>
      let opName := match op with
        | .Incr => "increment ('++')"
        | .Decr => "decrement ('--')"
      let diag := diagnosticFromSource source
        s!"The {opName} operator is only supported on 'int' and int-based \
           constrained types (e.g. 'nat'), but the operand has type '{tyName}'. \
           Use an explicit assignment instead, e.g. 'x := x + 1'."
      modify fun s => { s with errors := s.errors.push diag }

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
not to produce a value. They are handled by `Synth.resolveStmtExpr`
and synthesize `TVoid`:

- **Control-flow terminators** (`Exit`, `Return`): they jump somewhere
  else and never hand a value back.
- **Effect-only forms** (`Assert`, `Assume`, `While`, `Var-Declare`):
  they run and fall through without producing a value.

In either case, `Check.statement` (the `⋄` judgment) simply
synthesizes and discards the type, so any expression — including
value-producing ones like calls — is admitted in statement position.

`Assign` is the one statement that *does* produce a value: it
synthesizes the type of its right-hand side (so `x := e` can be used
where that type is expected), and its check rule skips the \[⇐\] Sub
boundary check only when the expected type is `TVoid` — i.e. when the
assignment is used purely for effect. `Block` routes the surrounding
expected type to its last statement (the block's value); non-last
statements are in effect position (synthesized and discarded via
`Check.statement`).

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
  `Synth.fresh`, `Synth.old`/`Check.old`, `Synth.proveBy`/`Check.proveBy`
- Self reference — `Synth.this`
- Untyped forms — `Synth.abstract`, `Synth.all`
- ContractOf — `Synth.contractOf`
- Holes — `Check.holeSome`, `Check.holeNone`

The dispatch functions `Synth.resolveStmtExpr` and `Check.resolveStmtExpr`
pattern-match on the constructor and delegate to the corresponding helper. -/

namespace Resolution

-- The `h : exprMd.val = .Foo args ...` parameters on the recursive helpers
-- look unused to the linter, but each one is referenced by that helper's
-- `decreasing_by` tactic to relate `sizeOf args` to `sizeOf exprMd`.
set_option linter.unusedVariables false in
-- The well-founded-recursion termination proofs for every helper in this
-- large mutual block share a single elaboration heartbeat budget. Each
-- `decreasing_by` rewrites the node equation (`rw [h]`) and then discharges
-- the size goal with `term_by_mem` (which adds `List`/`Array` membership-size
-- lemmas, then `simp_all` and `omega`). Their cumulative cost across ~30
-- functions sits above the 200k default, so the budget is raised for the block.
set_option maxHeartbeats 400000 in
mutual

-- ### Dispatch

/-- Synth-mode resolution: resolve `e` and synthesize its `HighType`,
    written `Γ ⊢ e ⇒ T`. Each constructor with a synthesis rule delegates
    to its rule's helper. Statement-shaped constructs (`While`, `Exit`,
    `Return`, `Assert`, `Assume`, `Var-Declare`) synthesize `TVoid`.

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
  | .LiteralBv v width => pure (Synth.litBv v width source)
  | .Var (.Local ref) => Synth.varLocal ref source
  | .IncrDecr mode op target =>
    Synth.incrDecr exprMd mode op target source (by rw [h_node])
  | .Var (.Field target fieldName) =>
    Synth.varField exprMd target fieldName source (by rw [h_node])
  | .Assign targets value =>
    Synth.assign exprMd targets value source (by rw [h_node])
  | .PureFieldUpdate target fieldName newVal =>
    Synth.pureFieldUpdate exprMd target fieldName newVal (by rw [h_node])
  | .StaticCall callee args =>
    Synth.staticCall exprMd callee args source (by rw [h_node])
  | .PrimitiveOp op args skipProof =>
    Synth.primitiveOp exprMd expr op args skipProof source h_expr (by rw [h_node])
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
  | .Old val =>
    Synth.old exprMd val source (by rw [h_node])
  | .ProveBy val proof =>
    Synth.proveBy exprMd val proof source (by rw [h_node])
  | .ContractOf ty fn =>
    Synth.contractOf exprMd ty fn source (by rw [h_node])
  | .Abstract => pure (Synth.abstract source)
  | .All => pure (Synth.all source)
  | .IfThenElse cond thenBr elseBr =>
    Synth.ifThenElse exprMd cond thenBr elseBr source (by rw [h_node])
  | .Block [] label => pure (.Block [] label, Synth.emptyBlock source)
  | .Block (head :: tail) label =>
    Synth.block exprMd (head :: tail) label source (by rw [h_node])
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
  | .Var (.Declare param) => do
    let r ← Check.varDeclare param source
    return (r, ⟨ .TVoid, source ⟩)
  | .While cond invs dec body postTest => do
    let r ← Check.while exprMd cond invs dec body postTest source (by rw [h_node])
    return (r, ⟨ .TVoid, source ⟩)
  | .Exit target => do
    let r ← Check.exit target source
    return (r, ⟨ .TVoid, source ⟩)
  | .Return val => do
    let r ← Check.return exprMd val source (by rw [h_node])
    return (r, ⟨ .TVoid, source ⟩)
  | .Assert ⟨condExpr, summary, free⟩ => do
    let r ← Check.assert exprMd condExpr summary free source (by rw [h_node])
    return (r, ⟨ .TVoid, source ⟩)
  | .Assume cond => do
    let r ← Check.assume exprMd cond source (by rw [h_node])
    return (r, ⟨ .TVoid, source ⟩)
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
  | .Old val =>
    Check.old exprMd val expected source (by rw [h_node])
  | .ProveBy val proof =>
    Check.proveBy exprMd val proof expected source (by rw [h_node])
  -- Only the arithmetic (`Neg`/`Add`/…/`ModT`) and boolean
  -- (`And`/`Or`/…/`Implies`) families get a dedicated check arm: these push
  -- `expected` inward through `Check.primitiveOp`. The remaining operators —
  -- comparison/equality (`Eq`/`Neq`/`Lt`/…) and `StrConcat` — have no inward
  -- push, so they are deliberately omitted here and fall through to the
  -- synth-then-subsume wildcard at the bottom of this match.
  --
  -- The arms are written out one operator per line rather than collapsed: an
  -- inner `match op` would duplicate the wildcard's subsumption body, and a
  -- binder distributed across an or-pattern (`.PrimitiveOp (op@.Neg) …`)
  -- defeats the `by rw [h_node]` dependent-match proof, so the explicit
  -- enumeration is the form that actually typechecks.
  | .PrimitiveOp .Neg args skipProof =>
    Check.primitiveOp exprMd .Neg args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .Add args skipProof =>
    Check.primitiveOp exprMd .Add args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .Sub args skipProof =>
    Check.primitiveOp exprMd .Sub args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .Mul args skipProof =>
    Check.primitiveOp exprMd .Mul args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .Div args skipProof =>
    Check.primitiveOp exprMd .Div args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .Mod args skipProof =>
    Check.primitiveOp exprMd .Mod args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .DivT args skipProof =>
    Check.primitiveOp exprMd .DivT args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .ModT args skipProof =>
    Check.primitiveOp exprMd .ModT args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .And args skipProof =>
    Check.primitiveOp exprMd .And args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .Or args skipProof =>
    Check.primitiveOp exprMd .Or args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .AndThen args skipProof =>
    Check.primitiveOp exprMd .AndThen args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .OrElse args skipProof =>
    Check.primitiveOp exprMd .OrElse args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .Not args skipProof =>
    Check.primitiveOp exprMd .Not args skipProof expected source (by rw [h_node])
  | .PrimitiveOp .Implies args skipProof =>
    Check.primitiveOp exprMd .Implies args skipProof expected source (by rw [h_node])
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

/-- `Γ ⊢ LiteralBv v (width := n) ⇒ TBv n` — a bitvector literal's type is
    fixed by its declared width. -/
def Synth.litBv (v : Nat) (width : Nat) (source : Option FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralBv v width, { val := .TBv width, source := source })

-- ### Variables

/-- (Var-Local)
    ```
    Γ(x) = T
    ──────────────────────
    Γ ⊢ Var (.Local x) ⇒ T
    ```
    Resolves `ref` against the lexical scope and reads its declared type. -/
def Synth.varLocal (ref : Identifier) (source : Option FileRange) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let ref' ← resolveRef ref source
  let ty ← getVarType ref
  pure (.Var (.Local ref'), ty)

/-- (Var-Field)
    ```
    Γ ⊢ e ⇒ _
    Γ(f) = T_f
    ───────────────────────────
    Γ ⊢ Var (.Field e f) ⇒ T_f
    ```
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
    rw [h] at hsz
    term_by_mem

/-- (Var-Declare)
    ```
    x ∉ dom(Γ)
    ────────────────────────────────────────────────────
    Γ ⊢ Var (.Declare ⟨x, T_x⟩) ⇒ TVoid ⊣ Γ, x : T_x
    ```
    `⊣ Γ, x : T_x` records that the surrounding scope is extended with
    the new binding for the remainder of the enclosing block. The
    declaration itself does no work other than registering `x : T_x`,
    and yields no value, so it synthesizes `TVoid`.

    `x ∉ dom(Γ)` is a soft side condition, not a hard premise: when `x`
    is already bound in the current scope, `defineNameCheckDup` emits a
    `"Duplicate definition '<x>' is already defined in this scope"`
    diagnostic and still extends the scope — but with an *unresolved*
    placeholder rather than `x : T_x`, so later uses of `x` do not
    cascade further type errors. -/
def Check.varDeclare (param : Parameter) (source : Option FileRange) :
    ResolveM StmtExprMd := do
  let ty' ← resolveHighType param.type
  let name' ← defineNameCheckDup param.name (.var param.name ty')
  pure { val := .Var (.Declare ⟨name', ty'⟩), source := source }

-- ### Control flow

/-- (While)
    ```
    Γ ⊢ cond ⇐ TBool
    Γ ⊢ invs_i ⇐ TBool
    Γ ⊢ decreases ⇒ U
    Numeric U
    Γ ⊢ body ⇐ Unknown
    ─────────────────────────────────────────────────
    Γ ⊢ While cond invs decreases body ⇒ TVoid
    ```
    `cond` is checked against `TBool`, and each invariant against
    `TBool`. The body's *value type* is discarded — control either
    re-enters the loop or falls through, so the body is checked at
    `Unknown` (the gradual wildcard) and any value the body's tail
    might produce is ignored. A loop is a statement: it yields no
    value, so it synthesizes `TVoid`.

    The optional `decreases` clause is synthesized and required to
    have a numeric type, via the same `Numeric U` predicate
    used by the arithmetic primitive ops. `Numeric` is a predicate,
    not a single type, so the clause runs in synth mode rather than
    check mode. -/
def Check.while (exprMd : StmtExprMd)
    (cond : StmtExprMd) (invs : List StmtExprMd)
    (dec : Option StmtExprMd) (body : StmtExprMd) (postTest : Bool)
    (source : Option FileRange)
    (h : exprMd.val = .While cond invs dec body postTest) :
    ResolveM StmtExprMd := do
  let cond' ← Check.resolveStmtExpr cond { val := .TBool, source := cond.source }
  let invs' ← invs.attach.mapM (fun a => have := a.property; do
    Check.resolveStmtExpr a.val { val := .TBool, source := a.val.source })
  let dec' ← dec.attach.mapM (fun a => have := a.property; do
    let (e', decTy) ← Synth.resolveStmtExpr a.val
    let ctx := (← get).typeLattice
    unless isNumeric ctx decTy do
      typeMismatch a.val.source none "expected a numeric type" decTy
    pure e')
  let body' ← Check.resolveStmtExpr body { val := .Unknown, source := body.source }
  -- `postTest` (the `do … while` variant) resolves identically and is carried
  -- through unchanged for the `EliminateDoWhile` pass to lower afterwards.
  pure { val := .While cond' invs' dec' body' postTest, source := source }
  termination_by (exprMd, 0)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      rw [h] at hsz
      term_by_mem

/-- (Exit)
    ```
    l ∈ Γ_lbl
    ───────────────────
    Γ ⊢ Exit l ⇒ TVoid
    ```
    `exit` is a control-flow terminator — an unconditional jump out of
    the enclosing labeled block. Because it never falls through, it
    never delivers a value, so it synthesizes `TVoid`.

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
    Γ ⊢ Return none ⇒ TVoid

    T_o-bar = [T]                                          (Return-None-Single)
    ──────────────────────────────────
    Γ ⊢ Return none ⇒ TVoid

    T_o-bar = [T_1;…;T_n]  n ≥ 2                           (Return-None-Multi)
    ──────────────────────────────────
    Γ ⊢ Return none ⇒ TVoid

    T_o-bar = [T]    Γ ⊢ e ⇐ T                             (Return-Some)
    ──────────────────────────────────
    Γ ⊢ Return (some e) ⇒ TVoid

    T_o-bar = []                                           (Return-Void-Error)
    ───────────────────────────────────────────────────────────
    Γ ⊢ Return (some e) ↝ "void procedure cannot return a value"

    T_o-bar = [T_1;…;T_n]  n ≥ 2                           (Return-Multi-Error)
    ───────────────────────────────────────────────────────────
    Γ ⊢ Return (some e) ↝ "multi-output procedure cannot use 'return e'; assign to named outputs instead"
    ```
    `return` is the *only* rule whose premises depend on the enclosing
    procedure's declared outputs. It is a control-flow terminator: it
    transfers control out of the enclosing procedure and never falls
    through, so it synthesizes `TVoid`. The returned value, if any, is
    checked against the procedure's declared output. Anything after
    `return` in the same block is dead code, flagged by
    `Resolution.Check.block`.

    When `answerType = none` we are not inside any procedure body (e.g.
    resolving a constant initializer), so all `Return` checks are
    skipped — `Return` should not occur there in well-formed input.

    `return;` (no payload) is unconditionally accepted in all cases:
    void-output procedures (Return-None-Void), single-output procedures
    (Return-None-Single), and multi-output procedures (Return-None-Multi).
    In the multi-output case it acts as an early-exit shorthand — each
    declared output retains whatever was last assigned to it via
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
  | none,   some [singleOutput] => pure ()
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
      rw [h] at hsz
      term_by_mem

/-- (Empty-Block)
    ```
    ─────────────────────────────────
    Γ ⊢ Block [] label ⇒ TVoid
    ```
    The empty block has a fixed type `TVoid`. This is the only
    block-level rule that synthesizes unconditionally: non-empty blocks
    are typed structurally by `Resolution.Check.block` (last statement
    carries the value, non-last positions via `Check.statement`),
    which always splits off a last statement and so never reaches an
    empty list. When an empty block appears in check position,
    `Resolution.Check.resolveStmtExpr`'s wildcard arm synth-then-subsumes
    via the standard \[⇐\] Sub fallback. -/
def Synth.emptyBlock (source : Option FileRange) : HighTypeMd :=
  { val := .TVoid, source := source }

/-- (Synth-Discard) Check a statement in *effect position*, written `Γ ⊢ s ⋄`.

    Laurel has no syntactic statement/expression split — everything is a
    `StmtExpr` — so "what may appear where its value is discarded" is
    defined by this rule rather than by the grammar. Every expression in
    statement position is synthesized and its type discarded:

    ```
    Γ ⊢ s ⇒ _
    ──────────────
    Γ ⊢ s ⋄
    ```

    Statement-shaped forms (`Var-Declare`, `Assign`, `Assert`, `Assume`,
    `While`, `Exit`, `Return`) synthesize `TVoid`; value-producing forms
    (calls, `IncrDecr`, literals, etc.) synthesize their natural type,
    which is then discarded. This means any expression is accepted in
    statement position — the `f(x);` idiom works regardless of `f`'s
    return type, and `x++;` is admitted even though `++` synthesizes the
    target's type.

    This is the single definition of "what counts as a statement". It is
    used by `Check.block` for every non-last statement, and for the last
    statement when the block itself sits in statement position
    (`expected = TVoid`). -/
def Check.statement (s : StmtExprMd) : ResolveM StmtExprMd := do
  let (s', _) ← Synth.resolveStmtExpr s; pure s'
  termination_by (s, 4)
  decreasing_by all_goals (apply Prod.Lex.right; decide)

/-- (Block) Check-mode typing rule for a non-empty block.

    A block's value is the value of its **last** statement; every
    earlier statement is run only for its effect. The rule splits the
    statement list into `[s₁; … ; sₙ]` (all but the last) and `last`,
    handling each part as follows:

    * **non-last — `Γ ⊢ s ⋄`.** A non-last statement is in effect
      position: it is synthesized and its type discarded (see
      `Check.statement`). Any expression is accepted — statement-shaped
      forms synthesize `TVoid`, value-producing forms (calls,
      `IncrDecr`, etc.) synthesize their natural type which is then
      discarded.

    * **last — `Γ ⊢ last ⇐ T`.** The surrounding expected type `T` is
      routed to the last statement, so a check-only trailing form
      (`IfThenElse`, a nested `Block`, `Hole`, `Return`, …) still
      receives its expected type. When `T = TVoid` (the block is in
      statement position), the last statement is also in effect position
      and goes through `Check.statement`.

    A block most often occurs in check position (procedure bodies,
    branches, loop bodies, assignment RHS, and call arguments all supply
    an expected type). When one appears in synth-only operand position
    with no contextual type, `Resolution.Synth.block` handles it with the
    same structure, synthesizing the last statement instead.

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
  -- (`Γ ⊢ s ⋄` — synthesized and the type discarded).
  let checkNonLast (s : StmtExprMd) (_h_mem : s ∈ stmts) : ResolveM StmtExprMd :=
    Check.statement s
  -- The last statement carries the block's value: push `expected` in (so
  -- check-only forms are reachable). When the block itself sits in statement
  -- position (`expected = TVoid`), the last statement is also in effect
  -- position and goes through `Check.statement`.
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
      rw [h] at hsz
      term_by_mem

/-- (If / If-NoElse)
    ```
    Γ ⊢ cond ⇐ TBool                                            (If)
    Γ ⊢ thenBr ⇐ T
    Γ ⊢ elseBr ⇐ T
    ──────────────────────────────────────────────────────────────────
    Γ ⊢ IfThenElse cond thenBr (some elseBr) ⇐ T

    Γ ⊢ cond ⇐ TBool                                            (If-NoElse)
    Γ ⊢ thenBr ⇐ T
    TVoid <: T
    ──────────────────────────────────────────────────────────────────
    Γ ⊢ IfThenElse cond thenBr none ⇐ T
    ```
    Pushes the surrounding `T` into both branches (rather than going
    through If-Synth + Sub at the boundary): errors fire at the
    offending branch instead of at the `if`, and the expectation
    propagates through nested `Block` / `IfThenElse` / `Hole` /
    `Quantifier` constructs that have their own check rules.

    Without an `else`, the implicit branch is an empty block of type
    `TVoid`, so the rule degenerates to require `TVoid <: T` — the
    standard \[⇐\] Sub boundary check that `Resolution.Synth.emptyBlock`
    composes with for an empty block. -/
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
      rw [h] at hsz
      term_by_mem

/-- (If-Synth)
    ```
    Γ ⊢ cond ⇐ TBool   Γ ⊢ thenBr ⇒ T_t   Γ ⊢ elseBr ⇒ T_e
    T_t ~ T_e   T = T_t ⨆ T_e (consistency join)                (If-Synth)
    ──────────────────────────────────────────────────────────────────────────
    Γ ⊢ IfThenElse cond thenBr (some elseBr) ⇒ T

    Γ ⊢ cond ⇐ TBool   Γ ⊢ thenBr ⇒ _                          (If-Synth-NoElse)
    ──────────────────────────────────────────────────────────────────────────
    Γ ⊢ IfThenElse cond thenBr none ⇒ TVoid
    ```
    Synth-mode rule for an `if` used where no expected type is available
    (e.g. as an operand of `==`/`<`/`++`, whose operands are synthesized).
    `cond` is checked against `TBool`; both branches are *synthesized*.
    With an `else`, the two branch types must be mutually consistent
    (`isConsistent`, the symmetric gradual relation — `Unknown` flows
    freely either way); when consistent, the result is their symmetric
    `join` (`Unknown ⊔ T = T`), so a hole branch promotes to the other
    branch's concrete type and the synthesized type is independent of
    branch order. (`isConsistent` stays the accept/reject gate: it admits
    a lone `TCore` corner where `join` is `none`, for which the result
    falls back to the then-branch type, leaving that boundary unchanged.)
    Inconsistent branches (e.g. `if c then 1 else "x"`) emit a diagnostic
    and synthesize `Unknown` to suppress cascading errors. Without an
    `else`, the `if` cannot produce a value on the missing branch, so it
    synthesizes `TVoid`.

    This is the synth counterpart to `Check.ifThenElse`: when an expected
    type *is* available the dispatcher prefers the check rule (pushing the
    type into both branches); this rule fires only at the synth wildcard. -/
def Synth.ifThenElse (exprMd : StmtExprMd)
    (cond thenBr : StmtExprMd) (elseBr : Option StmtExprMd)
    (source : Option FileRange)
    (h : exprMd.val = .IfThenElse cond thenBr elseBr) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let cond' ← Check.resolveStmtExpr cond { val := .TBool, source := cond.source }
  let (thenBr', thenTy) ← Synth.resolveStmtExpr thenBr
  match elseBr with
  | none =>
    pure (.IfThenElse cond' thenBr' none, { val := .TVoid, source := source })
  | some e =>
    let (e', elseTy) ← Synth.resolveStmtExpr e
    let ctx := (← get).typeLattice
    let ty ←
      if isConsistent ctx thenTy elseTy then
        pure ((join ctx thenTy elseTy).getD thenTy)
      else
        let diag := diagnosticFromSource source
          s!"'if' branches have incompatible types '{formatType thenTy}' and '{formatType elseTy}'"
        modify fun s => { s with errors := s.errors.push diag }
        pure { val := .Unknown, source := source }
    pure (.IfThenElse cond' thenBr' (some e'), ty)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      rw [h] at hsz
      simp only [StmtExpr.IfThenElse.sizeOf_spec, Option.some.sizeOf_spec] at hsz
      omega

/-- (Block-Synth)
    ```
    Γ ⊢ sᵢ ⋄ (1 ≤ i ≤ n)   Γ ⊢ last ⇒ T          (Block-Synth)
    ──────────────────────────────────────────────────────────────
    Γ ⊢ Block [s₁; … ; sₙ; last] label ⇒ T
    ```
    Synth-mode rule for a non-empty block used where no expected type is
    available (e.g. `{ x := 1; x } == y`). Mirrors `Check.block`'s
    structure — fresh scope, optional label, non-last statements in
    effect position (`Check.statement`), dead-code-after-terminator
    diagnostic — but *synthesizes* the last statement instead of checking
    it against an expected type, and returns that synthesized type as the
    block's value type. The empty block is handled by `Synth.emptyBlock`
    at the dispatch site; this rule only runs on a non-empty block. -/
def Synth.block (exprMd : StmtExprMd)
    (stmts : List StmtExprMd) (label : Option String)
    (source : Option FileRange)
    (h : exprMd.val = .Block stmts label) : ResolveM (StmtExpr × HighTypeMd) := do
  withScope <| withLabel label do
    let init' ← stmts.dropLast.attach.mapM fun ⟨s, hMem⟩ => do
      have h_mem : s ∈ stmts := List.dropLast_subset stmts hMem
      Check.statement s
    let isTerminator (s : StmtExprMd) : Bool :=
      match s.val with
      | .Exit _ | .Return _ => true
      | _ => false
    match init'.findIdx? isTerminator with
    | some i =>
      let nextSource : Option FileRange :=
        match init'[i + 1]? with
        | some next => next.source
        | none      => (stmts.getLast?.bind (·.source))
      let termName : String :=
        match init'[i]? with
        | some s => s.val.constrName
        | none   => "exit"
      let diag := diagnosticFromSource nextSource
        s!"dead code after '{termName}'"
      modify fun st => { st with errors := st.errors.push diag }
    | none => pure ()
    match _lastResult: stmts.getLast? with
    | none =>
      pure (.Block init' label, Synth.emptyBlock source)
    | some last =>
      have := List.mem_of_getLast? _lastResult
      let (last', lastTy) ← Synth.resolveStmtExpr last
      pure (.Block (init' ++ [last']) label, lastTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      rw [h] at hsz
      term_by_mem

-- ### Verification statements

/-- (Assert)
    ```
    Γ ⊢ cond ⇐ TBool
    ──────────────────────────────────
    Γ ⊢ Assert cond ⇒ TVoid
    ```
    `cond` is checked against `TBool`. `assert` is a statement: it
    yields no value, so it synthesizes `TVoid`. -/
def Check.assert (exprMd : StmtExprMd)
    (condExpr : StmtExprMd) (summary : Option String) (free : Bool)
    (source : Option FileRange)
    (h : exprMd.val = .Assert ⟨condExpr, summary, free⟩) :
    ResolveM StmtExprMd := do
  let cond' ← Check.resolveStmtExpr condExpr { val := .TBool, source := condExpr.source }
  pure { val := .Assert { condition := cond', summary, free }, source := source }
  termination_by (exprMd, 0)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    term_by_mem

/-- (Assume)
    ```
    Γ ⊢ cond ⇐ TBool
    ──────────────────────────────────
    Γ ⊢ Assume cond ⇒ TVoid
    ```
    `cond` is checked against `TBool`. `assume` is a statement: it
    yields no value, so it synthesizes `TVoid`. -/
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
    rw [h] at hsz
    term_by_mem

-- ### Assignment

/-- (Assign)
    ```
    Γ ⊢ targets_i ⇒ T_i
    Γ ⊢ e ⇐ ExpectedTy
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
      rw [h] at hsz
      term_by_mem

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
      rw [h] at hsz
      term_by_mem

-- ### Increment / decrement

/-- (IncrDecr)
    ```
    Γ ⊢ target ⇒ T    T ∈ {int, int-based constrained}
    ─────────────────────────────────────────────────
    Γ ⊢ IncrDecr mode op target ⇒ T
    ```
    `++`/`--` reads and writes its target, so it synthesizes the target's
    own type. The target is resolved the same way as an `Assign` target (a
    `Local` is resolved against scope; a `Field` synthesizes its receiver
    and resolves the field against it; the `Declare` form should not occur —
    the translator rejects it — and is handled conservatively). The element
    type is then checked by `checkIncrDecrTargetType`, which emits a Laurel
    diagnostic when `++`/`--` is applied to an unsupported type (`bv`,
    `real`, `float64`) rather than letting a raw Core unification error leak
    from the later `EliminateIncrDecr` lowering. Used in expression position
    (`var y := ++x`, `if x++ > 0`, `f(x++)`); in statement position the
    yielded value is discarded by `Check.statement`. -/
def Synth.incrDecr (exprMd : StmtExprMd)
    (mode : IncrDecrMode) (op : IncrDecrOp) (target : VariableMd)
    (source : Option FileRange)
    (h : exprMd.val = .IncrDecr mode op target) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let target' ← match h_tgt : target.val with
    | .Local ref =>
      let ref' ← resolveRef ref source
      pure (⟨.Local ref', target.source⟩ : VariableMd)
    | .Field tgt fieldName =>
      let (tgt', _) ← Synth.resolveStmtExpr tgt
      let fieldName' ← resolveFieldRef tgt' fieldName source
      pure (⟨.Field tgt' fieldName', target.source⟩ : VariableMd)
    | .Declare param =>
      -- Should not occur — the translator rejects a declaration target;
      -- treat conservatively by resolving its type only.
      let ty' ← resolveHighType param.type
      pure (⟨.Declare ⟨param.name, ty'⟩, target.source⟩ : VariableMd)
  checkIncrDecrTargetType op target' source
  let resultTy ← match target'.val with
    | .Local ref => getVarType ref
    | .Declare param => pure param.type
    | .Field _ fieldName => getVarType fieldName
  pure (.IncrDecr mode op target', resultTy)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    have hsz2 := target.sizeOf_val_lt
    rw [h_tgt] at hsz2
    term_by_mem

-- ### Calls

/-- Cases on the arity of the callee's declared outputs.
    ```
    Γ(callee) = static-procedure with inputs Ts                  (Static-Call)
      and output [T'] (single output)
    Γ ⊢ args_i ⇐ Ts_i (pairwise)
    ──────────────────────────────────────────────────────
    Γ ⊢ StaticCall callee args ⇒ T'

    Γ(callee) = static-procedure with inputs Ts                  (Static-Call-Multi)
      and outputs [T_1; …; T_n] (n ≥ 2)
    Γ ⊢ args_i ⇐ Ts_i (pairwise)
    ──────────────────────────────────────────────────────
    Γ ⊢ StaticCall callee args ⇒ MultiValuedExpr [T_1; …; T_n]
    ```
    A callee with *zero* outputs synthesizes `TVoid` (the n = 0 case).
    The two rules differ only in *output* arity — argument checking is
    identical. Callee is resolved against the expected kinds (parameter,
    static procedure, datatype constructor, datatype destructor, constant);
    each argument is *checked* against the corresponding parameter type. The
    bidirectional push lets impure-expression arguments (`{x := 1; x}`,
    `if c then …`, holes) flow through their own check rules instead of
    bottoming out at the synth wildcard.

    When the callee resolves to a static procedure with a known parameter
    count and the call supplies *more* arguments than it declares, an
    over-arity diagnostic is emitted (the surplus arguments are still
    resolved first, against `Unknown`, so errors inside them are reported
    too). The check fires *only* for genuine procedures (`procArity`); for an
    unresolved name (where `paramTypes = []` purely because the name was not
    found), a datatype constructor/tester, a parameter, or a constant, no
    arity diagnostic is emitted — surplus arguments are checked against
    `Unknown`, the gradual escape hatch, exactly as before, so no
    spurious/duplicate diagnostic is produced. Under-arity (too few
    arguments) is deliberately not flagged.

    The result type is the (possibly multi-valued) declared output type
    from `getCallInfo`. -/
def Synth.staticCall (exprMd : StmtExprMd)
    (callee : Identifier) (args : List StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .StaticCall callee args) :
    ResolveM (StmtExpr × HighTypeMd) := do

  -- Hack because we use these polymorphic map primitives but Laurel does not
  -- support polymorphism yet, so they cannot be type-checked against their
  -- placeholder `int` signatures. Instead we resolve the arguments and infer the
  -- result type structurally from them, keeping a concrete `HighType` flowing into
  -- Core translation:
  --   * `select(map, key)`     ⇒ the map's value type
  --   * `update(map, key, val)` ⇒ the map type itself
  --   * `const(val)`           ⇒ `Map _ (typeof val)` (key type is not recoverable)
  if callee == "select" || callee == "update" || callee == "const" then
    let resolved ← args.attach.mapM (fun ⟨a, hMem⟩ => do
      have := hMem
      Synth.resolveStmtExpr a)
    let args' := resolved.map (·.1)
    let argTys := resolved.map (·.2)
    let resultTy : HighTypeMd ←
      match callee, argTys with
      | "select", mapTy :: _ =>
        match mapTy.val with
        | .TMap _ valueTy => pure valueTy
        | _ => pure ⟨ .Unknown, source ⟩
      | "update", mapTy :: _ => pure mapTy
      | "const", valTy :: _ => pure ⟨ .TMap ⟨.UserDefined "TypeTag", source⟩ valTy, source ⟩
      | _, _ => pure ⟨ .Unknown, source ⟩
    return (.StaticCall callee args', resultTy)

  let callee' ← resolveRef callee source
    (expected := #[.parameter, .staticProcedure, .datatypeConstructor, .datatypeDestructor, .constant])
  let (retTy, paramTypes) ← getCallInfo callee
  let unknownTy : HighTypeMd := { val := .Unknown, source := none }
  let expectedTys : List HighTypeMd :=
    paramTypes ++ List.replicate (args.length - paramTypes.length) unknownTy
  let args' ← (args.attach.zip expectedTys).mapM (fun (⟨a, hMem⟩, paramTy) => do
    have := hMem
    Check.resolveStmtExpr a paramTy)
  -- Over-arity check: reject calls that supply MORE arguments than the callee
  -- declares, but *only* when the callee genuinely resolves to a procedure with
  -- a known parameter count (`procArity`). For any other resolution kind —
  -- unresolved name, datatype constructor/tester, parameter, constant — we leave
  -- the Unknown-padding behavior above untouched, so no spurious/duplicate
  -- arity diagnostic is emitted (an unresolved name already reported "not
  -- defined"). Args are resolved above regardless, so errors inside surplus
  -- arguments are still reported. The return type is unchanged to suppress
  -- cascading errors. Under-arity (too few args) is deliberately not flagged.
  if let some arity ← procArity callee (dropSelf := false) then
    if args.length > arity then
      let diag := diagnosticFromSource source
        s!"call to '{callee}' expects {arity} argument(s) but {args.length} were provided"
      modify fun s => { s with errors := s.errors.push diag }
  pure (.StaticCall callee' args', retTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      rw [h] at hsz
      term_by_mem

/-- Cases on the arity of the callee's declared outputs.
    ```
    Γ ⊢ target ⇒ _                                            (Instance-Call)
    Γ(callee) = instance- or static-procedure
      with inputs [self; Ts] and output [T'] (single output)
    Γ ⊢ args_i ⇐ Ts_i (pairwise; self dropped)
    ─────────────────────────────────────────
    Γ ⊢ InstanceCall target callee args ⇒ T'

    Γ ⊢ target ⇒ _                                            (Instance-Call-Multi)
    Γ(callee) = instance- or static-procedure
      with inputs [self; Ts] and outputs [T_1; …; T_n] (n ≥ 2)
    Γ ⊢ args_i ⇐ Ts_i (pairwise; self dropped)
    ─────────────────────────────────────────
    Γ ⊢ InstanceCall target callee args ⇒ MultiValuedExpr [T_1; …; T_n]
    ```
    A callee with *zero* outputs synthesizes `TVoid` (the n = 0 case).
    The two rules differ only in *output* arity. Target is synthesized;
    callee resolves to an instance or static procedure; arguments are
    checked pairwise against the callee's parameter types after dropping
    `self`. As in `Synth.staticCall`, supplying *more* arguments than the
    callee declares (compared against the post-`self` parameter count) emits
    an over-arity diagnostic when the callee genuinely resolves to a
    procedure, while surplus arguments against any other resolution kind are
    still checked against `Unknown` with no arity diagnostic. Like
    `Synth.staticCall`, the push is bidirectional so block- and
    conditional-shaped arguments route through their own check rules. -/
def Synth.instanceCall (exprMd : StmtExprMd)
    (target : StmtExprMd) (callee : Identifier) (args : List StmtExprMd)
    (source : Option FileRange)
    (h : exprMd.val = .InstanceCall target callee args) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', _) ← Synth.resolveStmtExpr target
  -- An instance procedure is registered under the container-scoped key
  -- `TypeName$method` (see `preRegisterTopLevel` / `resolveInstanceProcedure`),
  -- matching the lifted top-level static procedure that `LiftInstanceProcedures`
  -- produces. Look the method up under that key, derived from the receiver's
  -- type; fall back to the bare callee name when the target's type can't be
  -- determined (an unresolved name, which already reported its own error).
  let lookupKey ← match (← targetTypeName target') with
    | some tyName => pure (containerScopedName (mkId tyName) callee)
    | none => pure callee
  let resolved ← resolveRef lookupKey source
    (expected := #[.instanceProcedure, .staticProcedure])
  -- Preserve the user-facing callee text for diagnostics; only stamp the
  -- resolved `uniqueId` from the container-scoped lookup.
  let callee' := { callee with uniqueId := resolved.uniqueId }
  let (retTy, paramTypes) ← getCallInfo lookupKey
  -- The callee resolves to either an instance- or a static-procedure. An
  -- instance procedure's first parameter is the implicit `self` receiver,
  -- which is not supplied positionally here, so it must be dropped before
  -- pairing parameter types with `args`. A static procedure (also accepted
  -- on this path) has no `self`, so all its parameters are real and none may
  -- be dropped. We distinguish the two by the same scope lookup `getCallInfo`
  -- uses.
  let dropSelf : Bool := match (← get).scope.get? lookupKey.text with
    | some (_, .instanceProcedure ..) => true
    | _ => false
  let callParamTypes :=
    if dropSelf then (match paramTypes with | _ :: rest => rest | [] => [])
    else paramTypes
  let unknownTy : HighTypeMd := { val := .Unknown, source := none }
  let expectedTys : List HighTypeMd :=
    callParamTypes ++ List.replicate (args.length - callParamTypes.length) unknownTy
  let args' ← (args.attach.zip expectedTys).mapM (fun (⟨a, hMem⟩, paramTy) => do
    have := hMem
    Check.resolveStmtExpr a paramTy)
  -- Over-arity check (mirrors `Synth.staticCall`): reject calls supplying more
  -- arguments than the callee declares, comparing against the post-`self`
  -- parameter count. `procArity` is given the same `dropSelf` flag computed
  -- above, so an instance procedure's implicit `self` is excluded; it returns
  -- `none` for any non-procedure resolution, leaving the Unknown-padding (and
  -- no duplicate diagnostic) for those. Args are resolved above regardless.
  if let some arity ← procArity lookupKey dropSelf then
    if args.length > arity then
      let diag := diagnosticFromSource source
        s!"call to '{callee}' expects {arity} argument(s) but {args.length} were provided"
      modify fun s => { s with errors := s.errors.push diag }
  pure (.InstanceCall target' callee' args', retTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      rw [h] at hsz
      term_by_mem

-- ### Primitive operations

/-- Cases on the operator family.
    ```
    Γ ⊢ args_i ⇒ U_i                                            (Op-Bool)
    U_i <: TBool
    op ∈ {And, Or, AndThen, OrElse, Not, Implies}
    ─────────────────────────────────────────────
    Γ ⊢ PrimitiveOp op args ⇒ TBool

    Γ ⊢ args_i ⇒ U_i                                            (Op-Cmp)
    Numeric U_i
    op ∈ {Lt, Leq, Gt, Geq}
    ─────────────────────────────────────────────
    Γ ⊢ PrimitiveOp op args ⇒ TBool

    Γ ⊢ lhs ⇒ T_l                                               (Op-Eq)
    Γ ⊢ rhs ⇒ T_r
    T_l ~ T_r
    op ∈ {Eq, Neq}
    ─────────────────────────────────────────────
    Γ ⊢ PrimitiveOp op [lhs; rhs] ⇒ TBool

    Γ ⊢ args_i ⇒ U_i                                            (Op-Arith)
    Numeric U_i
    T = ⨆ U_i (consistency join)
    op ∈ {Neg, Add, Sub, Mul, Div, Mod, DivT, ModT}
    ─────────────────────────────────────────────
    Γ ⊢ PrimitiveOp op args ⇒ T

    Γ ⊢ args_i ⇒ U_i                                            (Op-Concat)
    U_i <: TString
    op = StrConcat
    ─────────────────────────────────────────────
    Γ ⊢ PrimitiveOp op args ⇒ TString
    ```
    `Numeric T` is the predicate "T unfolds to TInt / TReal / TFloat64 / TBv
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
    fold the operand types under `join` (the join on the
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
    (op : Operation) (args : List StmtExprMd) (skipProof : Bool) (source : Option FileRange)
    (h_expr : expr = .PrimitiveOp op args skipProof)
    (h : exprMd.val = .PrimitiveOp op args skipProof) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let _ := h_expr  -- carries the constructor identity for `expr` in diagnostics
  -- Guard (all operator families): a `MultiValuedExpr` operand is a
  -- multi-output call (`multi(x)` declared `returns (a, b)`) used in value
  -- position. It is an internal pseudo-type with no Core lowering, so it must
  -- never reach an operator slot — letting it through crashes a later pass as
  -- a `StrataBug`. Emit the position-oriented diagnostic per offending operand
  -- and return `true` so the caller short-circuits to the operator's natural
  -- result type, suppressing the per-family check (and its cascading error)
  -- on that operand.
  let reportMultiValued (a : StmtExprMd) (aTy : HighTypeMd) : ResolveM Bool := do
    match aTy.val with
    | .MultiValuedExpr _ =>
      let diag := diagnosticFromSource a.source
        "multi-output call cannot be used as a value here; it returns multiple values. Unpack it into separate variables first"
      modify fun s => { s with errors := s.errors.push diag }
      pure true
    | _ => pure false
  match op with
  -- Arithmetic: synth each operand's type, then take the join under
  -- the consistency relation. This is the same discipline as
  -- `Op-Eq`: operands must be pairwise consistent (with `Unknown`
  -- promoting to whichever side is more informative). Each operand
  -- is also required to be numeric.
  | .Neg | .Add | .Sub | .Mul | .Div | .Mod | .DivT | .ModT =>
    let results ← args.attach.mapM (fun a => have := a.property; do
      Synth.resolveStmtExpr a.val)
    let args' := results.map (·.1)
    let argTypes := results.map (·.2)
    let unknownTy : HighTypeMd := { val := .Unknown, source := source }
    -- Multi-output operand guard: short-circuit to `Unknown` (arithmetic's
    -- natural cascade-suppression type) once any operand is multi-valued.
    let mut hasMulti := false
    for (a, aTy) in args'.zip argTypes do
      if (← reportMultiValued a aTy) then hasMulti := true
    if hasMulti then
      return (.PrimitiveOp op args' skipProof, unknownTy)
    let ctx := (← get).typeLattice
    -- Per-operand numeric check: surface the bad operand directly.
    for (a, aTy) in args'.zip argTypes do
      unless isNumeric ctx aTy do
        typeMismatch a.source (some expr) "expected a numeric type" aTy
    -- Fold operands by join, starting from `Unknown` so the
    -- empty list (impossible for these ops, but kept for totality)
    -- yields `Unknown` and a single-operand fold (`Neg`) yields the
    -- operand's type.
    let resultTy := argTypes.foldl
      (fun acc aTy =>
        match acc with
        | some acc => join ctx acc aTy
        | none => none)
      (some unknownTy)
    match resultTy with
    | some ty => pure (.PrimitiveOp op args' skipProof, ty)
    | none =>
      let formatted := ", ".intercalate (argTypes.map (fun t => s!"'{formatType t}'"))
      let diag := diagnosticFromSource source
        s!"cannot apply '{op}' to operands of types {formatted}"
      modify fun s => { s with errors := s.errors.push diag }
      pure (.PrimitiveOp op args' skipProof, unknownTy)
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
    -- Multi-output operand guard: short-circuit to the operator's natural
    -- result type (`TBool` for bool/cmp/eq, `TString` for concat) once any
    -- operand is multi-valued, suppressing the per-family check below.
    let mut hasMulti := false
    for (a, aTy) in args'.zip argTypes do
      if (← reportMultiValued a aTy) then hasMulti := true
    if hasMulti then
      return (.PrimitiveOp op args' skipProof, { val := resultTy, source := source })
    match op with
    | .And | .Or | .AndThen | .OrElse | .Not | .Implies =>
      for (a, aTy) in args'.zip argTypes do
        checkSubtype a.source { val := .TBool, source := a.source } aTy
    | .Lt | .Leq | .Gt | .Geq =>
      let ctx := (← get).typeLattice
      for (a, aTy) in args'.zip argTypes do
        unless isNumeric ctx aTy do
          typeMismatch a.source (some expr) "expected a numeric type" aTy
    | .Eq | .Neq =>
      match argTypes with
      | [lhsTy, rhsTy] =>
        let ctx := (← get).typeLattice
        unless isConsistent ctx lhsTy rhsTy do
          let diag := diagnosticFromSource source
            s!"cannot compare '{formatType lhsTy}' with '{formatType rhsTy}' using '{op}'"
          modify fun s => { s with errors := s.errors.push diag }
      | _ => pure ()
    | .StrConcat =>
      for (a, aTy) in args'.zip argTypes do
        checkSubtype a.source { val := .TString, source := a.source } aTy
    | _ => pure ()  -- unreachable
    pure (.PrimitiveOp op args' skipProof, { val := resultTy, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      rw [h] at hsz
      term_by_mem

/-- Cases on the operator family.
    ```
    Numeric T                                                   (Op-Arith)
    Γ ⊢ args_i ⇐ T
    op ∈ {Neg, Add, Sub, Mul, Div, Mod, DivT, ModT}
    ─────────────────────────────────────────────
    Γ ⊢ PrimitiveOp op args ⇐ T

    TBool <: T                                                  (Op-Bool)
    Γ ⊢ args_i ⇐ TBool
    op ∈ {And, Or, AndThen, OrElse, Not, Implies}
    ─────────────────────────────────────────────
    Γ ⊢ PrimitiveOp op args ⇐ T
    ```
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
    (op : Operation) (args : List StmtExprMd) (skipProof : Bool)
    (expected : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .PrimitiveOp op args skipProof) :
    ResolveM StmtExprMd := do
  let operandTy : HighTypeMd ← match op with
    | .Neg | .Add | .Sub | .Mul | .Div | .Mod | .DivT | .ModT =>
      let ctx := (← get).typeLattice
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
  pure { val := .PrimitiveOp op args' skipProof, source := source }
  termination_by (exprMd, 0)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    term_by_mem

-- ### Object forms

/-- Cases on whether `ref` resolves to a composite/datatype.
    ```
    ref is a composite or datatype,                (New-Ok)
      or is unresolved, or is absent from Γ
    ──────────────────────────────────────
    Γ ⊢ New ref ⇒ UserDefined ref

    ref resolves to a non-type kind               (New-Fallback)
    ──────────────────────────────────────
    Γ ⊢ New ref ⇒ Unknown
    ```
    When `ref` resolves to a composite or datatype, the type is
    `UserDefined ref`. The `Unknown` fallback fires *only* when `ref`
    resolves to a present definition whose kind is neither composite nor
    datatype (e.g. a variable or procedure name); this suppresses
    cascading errors after the kind diagnostic has already fired. An
    *unresolved* `ref`, or one absent from scope, takes the `UserDefined`
    branch instead — `resolveRef` has already reported the name, so
    re-flagging it here would only duplicate that diagnostic. -/
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

/-- (AsType)
    ```
    Γ ⊢ target ⇒ U
    U ~ T  ∨  U <: T  ∨  T <: U
    ──────────────────────────────────────────────
    Γ ⊢ AsType target T ⇒ T
    ```
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
  let ctx := (← get).typeLattice
  unless isConsistentSubtype ctx targetTy ty' || isConsistentSubtype ctx ty' targetTy do
    let diag := diagnosticFromSource target.source
      s!"cannot cast unrelated type '{formatType targetTy}' to '{formatType ty'}'"
    modify fun s => { s with errors := s.errors.push diag }
  pure (.AsType target' ty', ty')
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    term_by_mem

/-- (IsType)
    ```
    Γ ⊢ target ⇒ U
    U ~ T  ∨  U <: T  ∨  T <: U
    ──────────────────────────────────────────────
    Γ ⊢ IsType target T ⇒ TBool
    ```
    Same lineage check as `AsType` — `is` only makes sense between types
    that share a lineage modulo gradual `Unknown`; testing `5 is Cat`
    is statically nonsense. The synthesized type is `TBool`. -/
def Synth.isType (exprMd : StmtExprMd)
    (target : StmtExprMd) (ty : HighTypeMd) (source : Option FileRange)
    (h : exprMd.val = .IsType target ty) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', targetTy) ← Synth.resolveStmtExpr target
  let ty' ← resolveHighType ty
  let ctx := (← get).typeLattice
  unless isConsistentSubtype ctx targetTy ty' || isConsistentSubtype ctx ty' targetTy do
    let diag := diagnosticFromSource target.source
      s!"cannot test unrelated type '{formatType targetTy}' against '{formatType ty'}'"
    modify fun s => { s with errors := s.errors.push diag }
  pure (.IsType target' ty', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    term_by_mem

/-- (RefEq)
    ```
    Γ ⊢ lhs ⇒ T_l
    Γ ⊢ rhs ⇒ T_r
    isReference T_l
    isReference T_r
    T_l ~ T_r
    ──────────────────────────────────────────────────
    Γ ⊢ ReferenceEquals lhs rhs ⇒ TBool
    ```
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
  let ctx := (← get).typeLattice
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
      rw [h] at hsz
      term_by_mem

/-- (PureFieldUpdate)
    ```
    Γ ⊢ target ⇒ T_t
    Γ(f) = T_f
    Γ ⊢ newVal ⇐ T_f
    ─────────────────────────────────────────────────────
    Γ ⊢ PureFieldUpdate target f newVal ⇒ T_t
    ```
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
      rw [h] at hsz
      term_by_mem

-- ### Verification expressions

/-- (Quantifier)
    ```
    Γ, x : T ⊢ body ⇐ TBool
    ────────────────────────────────────────────
    Γ ⊢ Quantifier mode ⟨x, T⟩ trig body ⇒ TBool
    ```
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
      rw [h] at hsz
      term_by_mem

/-- (Assigned)
    ```
    Γ ⊢ name ⇒ _
    ────────────────────────────
    Γ ⊢ Assigned name ⇒ TBool
    ```
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
    rw [h] at hsz
    term_by_mem

/-- (Old)
    ```
    Γ ⊢ v ⇐ T
    ───────────────
    Γ ⊢ Old v ⇐ T
    ```
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
    rw [h] at hsz
    term_by_mem

/-- (Old-Synth)
    ```
    Γ ⊢ v ⇒ T
    ───────────────
    Γ ⊢ Old v ⇒ T
    ```
    `old` is a *universal morphism*: it is fully type-transparent, so
    `old(v)` has exactly the type of `v` and passes through every
    operation. When `old(...)` appears in a synthesis position (e.g. as
    an operand of `==`/`<`/`++`, which synthesize their operands — the
    documented postcondition pattern `ensures counter.value ==
    old(counter.value) + 1`), `v` is synthesized and its type `T` is
    returned unchanged, wrapped back up as `Old v'`. Without this rule the
    construct would fall into the synth wildcard and spuriously report
    that its type cannot be synthesized. -/
def Synth.old (exprMd : StmtExprMd)
    (val : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .Old val) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (val', valTy) ← Synth.resolveStmtExpr val
  pure (.Old val', valTy)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    term_by_mem

/-- (Fresh)
    ```
    Γ ⊢ v ⇒ T
    isReference T
    ────────────────────────────
    Γ ⊢ Fresh v ⇒ TBool
    ```
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
  unless isReference (← get).typeLattice valTy do
    typeMismatch val'.source (some expr) "expected a reference type" valTy
  pure (.Fresh val', { val := .TBool, source := source })
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    term_by_mem

/-- (ProveBy)
    ```
    Γ ⊢ v ⇐ T
    Γ ⊢ proof ⇒ _
    ────────────────────────────
    Γ ⊢ ProveBy v proof ⇐ T
    ```
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
      rw [h] at hsz
      term_by_mem

/-- (ProveBy-Synth)
    ```
    Γ ⊢ v ⇒ T
    Γ ⊢ proof ⇒ _
    ────────────────────────────
    Γ ⊢ ProveBy v proof ⇒ T
    ```
    Like `old`, `ProveBy v proof` is type-transparent in `v` — the proof
    is just a hint for downstream verification and carries no typing
    constraint. In a synthesis position `v` is synthesized for its type
    `T`, `proof` is synthesized only for its name-resolution side effects
    (its type is discarded), and `T` is returned. -/
def Synth.proveBy (exprMd : StmtExprMd)
    (val proof : StmtExprMd) (source : Option FileRange)
    (h : exprMd.val = .ProveBy val proof) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (val', valTy) ← Synth.resolveStmtExpr val
  let (proof', _) ← Synth.resolveStmtExpr proof
  pure (.ProveBy val' proof', valTy)
  termination_by (exprMd, 1)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      rw [h] at hsz
      term_by_mem

-- ### Self reference

/-- Cases on whether `instanceTypeName` is set (i.e., we're inside an
    instance method).

    ```
    Γ.instanceTypeName = some T      (This-Inside)
    ───────────────────────────
    Γ ⊢ This ⇒ UserDefined T

    Γ.instanceTypeName = none        (This-Outside)
    ───────────────────────────
    Γ ⊢ This ⇒ Unknown               (emits "'this' is not allowed outside instance methods")
    ```
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

    ```
    fn = Var (.Local id)                                       (ContractOf-Bool)
    Γ(id) ∈ {staticProcedure, instanceProcedure, unresolved}
    ────────────────────────────────────────────
    Γ ⊢ ContractOf Precondition fn ⇒ TBool
    Γ ⊢ ContractOf PostCondition fn ⇒ TBool

    fn = Var (.Local id)                                       (ContractOf-Set)
    Γ(id) ∈ {staticProcedure, instanceProcedure, unresolved}
    ────────────────────────────────────────────
    Γ ⊢ ContractOf Reads fn ⇒ TSet Unknown
    Γ ⊢ ContractOf Modifies fn ⇒ TSet Unknown

    fn is not a Var (.Local) resolving to a procedure          (ContractOf-Error)
      or unresolved name
    ────────────────────────────────────────────
    Γ ⊢ ContractOf _ fn ↝ error: "'contractOf' expected a procedure reference"
    ```
    `ContractOf ty fn` extracts a procedure's contract clause as a value:
    its preconditions (`Precondition`), postconditions (`PostCondition`),
    reads set (`Reads`), or modifies set (`Modifies`). `fn` must be a
    direct identifier reference resolving to a procedure — a contract
    belongs to a *named* procedure, not an arbitrary expression. The
    diagnostic *"'contractOf' expected a procedure reference"* fires (and
    the construct synthesizes `Unknown` to suppress cascading errors) when
    `fn` is anything other than a `Var (.Local id)`, or resolves to a
    present definition that is not a procedure. An *unresolved* `id`, or
    one absent from scope, is accepted without firing the diagnostic —
    its name-resolution error was already reported.

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
    rw [h] at hsz
    term_by_mem

-- ### Holes

/-- (Hole-Some)
    ```
    T_h <: T
    ────────────────────────────
    Γ ⊢ Hole d (some T_h) ⇐ T
    ```
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

/-- (Hole-None)
    ```
    ────────────────────────────────────────
    Γ ⊢ Hole d none ⇐ T  ↦  Γ ⊢ Hole d (some T)
    ```
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

/-- Resolve a single modifies-clause entry, dropping it (with a diagnostic) when
    its type is not heap-relevant — the frame only applies to heap objects. For a
    field target `o#f` the *owner* must be heap-relevant; `*` (`.All`) is always
    kept. The type is unfolded through the `TypeLattice` so aliases/constrained
    types are classified by their underlying type. Replaces the former
    `FilterNonCompositeModifies` pass. -/
private def resolveModifiesEntry (e : StmtExprMd) : ResolveM (Option StmtExprMd) := do
  let ctx := (← get).typeLattice
  match e.val with
  | .All =>
    -- `modifies *` wildcard: kept regardless of type.
    let e' ← resolveStmtExpr e
    return some e'
  | .Var (.Field target fieldName) =>
    -- Resolve the owner directly (as `Synth.varField` does) to gate on its type.
    let (target', ownerTy) ← Synth.resolveStmtExpr target
    let fieldName' ← resolveFieldRef target' fieldName e.source
    let e' : StmtExprMd := { val := .Var (.Field target' fieldName'), source := e.source }
    let ownerTy' := (ctx.unfold ownerTy).val
    if isHeapRelevantType ownerTy' then
      return some e'
    else
      let diag := diagnosticFromSource e.source
        s!"modifies clause field target has non-composite owner type \
           '{formatHighTypeVal ownerTy'}' and will be ignored"
      modify fun s => { s with errors := s.errors.push diag }
      return none
  | _ =>
    let (e', ty) ← Synth.resolveStmtExpr e
    let ty' := (ctx.unfold ty).val
    if isHeapRelevantType ty' then
      return some e'
    else
      let diag := diagnosticFromSource e.source
        s!"modifies clause entry has non-composite type \
           '{formatHighTypeVal ty'}' and will be ignored"
      modify fun s => { s with errors := s.errors.push diag }
      return none

/-- Resolve the modifies entries of an `Opaque` body, dropping the
    non-heap-relevant ones via `resolveModifiesEntry`. -/
private def resolveModifies (mods : List StmtExprMd) : ResolveM (List StmtExprMd) := do
  let resolved ← mods.mapM resolveModifiesEntry
  return resolved.filterMap id

/-- Resolve a parameter: assign a fresh ID and add to scope. -/
def resolveParameter (param : Parameter) : ResolveM Parameter := do
  let ty' ← resolveHighType param.type
  let name' ← defineNameCheckDup param.name (.parameter ⟨param.name, ty'⟩)
  return ⟨name', ty'⟩

/-- Resolve a procedure output parameter, given the names of the inputs already
    in scope. A parameter whose name also appears in the inputs is a true inout
    parameter (e.g. the `$heap` synthesized by heap parameterization): it denotes
    the *same* variable as the input, so we resolve its name as a reference to the
    existing input definition rather than re-defining it (which
    `defineNameCheckDup` would otherwise flag as a duplicate). -/
def resolveOutputParameter (inputNames : List String) (param : Parameter) : ResolveM Parameter := do
  if inputNames.contains param.name.text then
    let ty' ← resolveHighType param.type
    let name' ← resolveRef param.name
    return ⟨name', ty'⟩
  else
    resolveParameter param

/-- Resolve a procedure body by synthesizing its body (if any).
    Bodies without an body (`Abstract`, `External`) resolve
    postconditions only. -/
def resolveBody (body : Body) : ResolveM Body := do
  match body with
  | .Transparent b =>
    let (b', _) ← Synth.resolveStmtExpr b
    return .Transparent b'
  | .Opaque posts impl mods =>
    let posts' ← posts.mapM (·.mapM resolveStmtExpr)
    let impl' ← impl.mapM Synth.resolveStmtExpr
    let mods' ← resolveModifies mods
    return .Opaque posts' (impl'.map (fun t => t.1)) mods'
  | .Abstract posts =>
    let posts' ← posts.mapM (·.mapM resolveStmtExpr)
    return .Abstract posts'
  | .External => return .External

/-- (Procedure)
    ```
    T_o-bar = proc.outputs.types
    Γ_global, params(proc) ⊢ proc.body ⇒ _
    ──────────────────────────────────────────────────────────
    Γ_global ⊢ Procedure proc
    ```
    The body is synthesized (not checked against a computed expected
    type) under a scope that includes the procedure's input and output
    parameters. Outputs are matched only via `return e` (checked against
    the declared output by `Check.return`) or via named-output
    assignment. The procedure's declared output list `T_o-bar` is stored
    on `ResolveState.answerType`, set on entry and restored on exit. -/
def resolveProcedure (proc : Procedure) : ResolveM Procedure := do
  let procName' ← resolveRef proc.name
  withScope do
    let inputs' ← proc.inputs.mapM resolveParameter
    let inputNames := inputs'.map (·.name.text)
    let outputs' ← proc.outputs.mapM (resolveOutputParameter inputNames)
    let pres' ← proc.preconditions.mapM (·.mapM resolveStmtExpr)
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let savedAnswer := (← get).answerType
    modify fun s => { s with answerType := some (outputs'.map (·.type)) }
    -- Pre-register the implicit `bodyLabel` block that the LaurelToCore
    -- translator wraps every body in (`Core.Statement.block bodyLabel …`),
    -- so that frontends emitting `Exit bodyLabel` for early-return lowering
    -- (e.g. PythonToLaurel) don't trip Check.exit's label-scope check.
    let body' ← withLabel (some bodyLabel) <| resolveBody proc.body
    modify fun s => { s with answerType := savedAnswer }
    -- Transparent (static) procedure bodies are supported (#1215): the
    -- TransparencyPass derives a functional `$asFunction` copy, and the
    -- LaurelToCore translator rejects the genuinely-unsupported constructs
    -- (e.g. destructive assignments) inside a transparent body. So there is
    -- no transparent-body rejection here, unlike `resolveInstanceProcedure`.
    let invokeOn' ← proc.invokeOn.mapM resolveStmtExpr
    let axioms' ← proc.axioms.mapM resolveStmtExpr
    return { name := procName', inputs := inputs', outputs := outputs',
             isFunctional := proc.isFunctional,
             preconditions := pres', decreases := dec',
             invokeOn := invokeOn',
             axioms := axioms',
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
  let scopedKey := containerScopedName typeName proc.name
  let resolved ← resolveRef scopedKey
  let procName' := { proc.name with uniqueId := resolved.uniqueId }
  withScope do
    let savedInstType := (← get).instanceTypeName
    modify fun s => { s with instanceTypeName := some typeName.text }
    let inputs' ← proc.inputs.mapM resolveParameter
    let inputNames := inputs'.map (·.name.text)
    let outputs' ← proc.outputs.mapM (resolveOutputParameter inputNames)
    let pres' ← proc.preconditions.mapM (·.mapM resolveStmtExpr)
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let savedAnswer := (← get).answerType
    modify fun s => { s with answerType := some (outputs'.map (·.type)) }
    -- See `resolveProcedure` for the rationale on `bodyLabel`.
    let body' ← withLabel (some bodyLabel) <| resolveBody proc.body
    modify fun s => { s with answerType := savedAnswer }
    let invokeOn' ← proc.invokeOn.mapM resolveStmtExpr
    modify fun s => { s with instanceTypeName := savedInstType }
    let axioms' ← proc.axioms.mapM resolveStmtExpr
    return { name := procName', inputs := inputs', outputs := outputs',
             isFunctional := proc.isFunctional,
             preconditions := pres', decreases := dec',
             invokeOn := invokeOn',
             axioms := axioms',
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
      -- Resolve the tester name so its uniqueId is set.
      let testerResolved ← resolveRef (dt.testerName ctor)
      let testerName' := { ctor.testerName with
        text := testerResolved.text
        uniqueId := testerResolved.uniqueId }
      return { name := ctorName', args := args', testerName := testerName' : DatatypeConstructor }
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

/-- Generate a virtual tester procedure for a single constructor of a datatype.
    The tester takes a single argument of the datatype's type and returns `bool`.
    Used during resolution to synthesize the scope entry for tester calls
    (e.g. `IntList..isNil(x)`) without requiring a separate AST pass. -/
private def mkTesterProcedure (dt : DatatypeDefinition) (ctor : DatatypeConstructor) : Procedure :=
  let tName := dt.testerName ctor
  let inputParam : Parameter := {
    name := mkId "value"
    type := { val := .UserDefined dt.name, source := none }
  }
  let outputParam : Parameter := {
    name := mkId "$result"
    type := { val := .TBool, source := none }
  }
  { name := mkId tName
    inputs := [inputParam]
    outputs := [outputParam]
    preconditions := []
    decreases := none
    isFunctional := true
    body := .External }

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
  | .While cond invs dec body _ =>
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
  | .IncrDecr _ _ ⟨.Field tgt _, _⟩ => collectStmtExpr map tgt
  | .IncrDecr _ _ ⟨.Local _, _⟩ | .IncrDecr _ _ ⟨.Declare _, _⟩ => map
  | .Var (.Field target _) => collectStmtExpr map target
  | .PureFieldUpdate target _ newVal =>
    let map := collectStmtExpr map target
    collectStmtExpr map newVal
  | .StaticCall _ args => args.foldl collectStmtExpr map
  | .PrimitiveOp _ args _ => args.foldl collectStmtExpr map
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
  | .Assert ⟨cond, _, _⟩ => collectStmtExpr map cond
  | .Assume cond => collectStmtExpr map cond
  | .ProveBy val proof =>
    let map := collectStmtExpr map val
    collectStmtExpr map proof
  | .ContractOf _ fn => collectStmtExpr map fn
  | .New _ | .This | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv _ _
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
      -- Register the tester function in the refToDef map.
      let testerProc := mkTesterProcedure dt ctor
      let map := register map ctor.testerName (.staticProcedure testerProc)
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

/-! Additional checks-/

/--
Check if a field can be reached through a given type (directly declared or inherited).
Returns true if the type or any of its ancestors declares the field.
-/
def canReachField (model : SemanticModel) (typeName : Identifier) (fieldName : Identifier) : Bool :=
  match model.get fieldName with
  | .field owner _ => ((computeAncestors model typeName).find? (fun t => t.name == owner)).isSome
  | _ => false -- recover from a resolution error

/--
Check if a field is inherited through multiple parent paths (diamond inheritance).
Returns true if more than one direct parent of the given type can reach the field.
-/
def isDiamondInheritedField (model : SemanticModel) (typeName : Identifier) (fieldName : Identifier) : Bool :=
  match model.get typeName with
  | .compositeType ct =>
    -- If the field is directly declared on this type, it's not a diamond
    if ct.fields.any (·.name == fieldName) then false
    else
      -- Count how many direct parents can reach this field
      let parentsWithField := ct.extending.filter (canReachField model · fieldName)
      parentsWithField.length > 1
  | _ => false

/--
Check whether accessing `fieldName` on `target` is a diamond-inherited field access,
and if so return a diagnostic error using the given `source` range.
-/
private def checkDiamondFieldAccess (model : SemanticModel) (target : StmtExprMd)
    (fieldName : Identifier) (source : Option FileRange) : List DiagnosticModel :=
  match (computeExprType model target).val with
  | .UserDefined typeName =>
    if isDiamondInheritedField model typeName fieldName then
      match source with
      | some fileRange =>
        [DiagnosticModel.withRange fileRange s!"fields that are inherited multiple times can not be accessed."]
      | none =>
        [DiagnosticModel.fromMessage s!"fields that are inherited multiple times can not be accessed."]
    else []
  | _ => []

/--
Walk a StmtExpr AST and collect DiagnosticModel errors for diamond-inherited field accesses.
-/
def validateDiamondFieldAccessesForStmtExpr (model : SemanticModel)
    (expr : StmtExprMd) : List DiagnosticModel :=
  match _h : expr.val with
  | .Var (.Field target fieldName) =>
    let targetErrors := validateDiamondFieldAccessesForStmtExpr model target
    let fieldError := checkDiamondFieldAccess model target fieldName expr.source
    targetErrors ++ fieldError
  | .Block stmts _ =>
    stmts.flatMap (fun s => validateDiamondFieldAccessesForStmtExpr model s)
  | .Assign targets value =>
    let targetErrors := targets.attach.foldl (fun acc ⟨t, _⟩ =>
      match _hv : t.val with
      | .Field target fieldName =>
        let innerErrors := validateDiamondFieldAccessesForStmtExpr model target
        let fieldError := checkDiamondFieldAccess model target fieldName t.source
        acc ++ innerErrors ++ fieldError
      | .Local _ | .Declare _ => acc) []
    targetErrors ++ validateDiamondFieldAccessesForStmtExpr model value
  | .IfThenElse c t e =>
    let errs := validateDiamondFieldAccessesForStmtExpr model c ++
                validateDiamondFieldAccessesForStmtExpr model t
    match e with
    | some eb => errs ++ validateDiamondFieldAccessesForStmtExpr model eb
    | none => errs
  | .While c invs _ b _ =>
    let errs := validateDiamondFieldAccessesForStmtExpr model c ++
                validateDiamondFieldAccessesForStmtExpr model b
    invs.attach.foldl (fun acc ⟨inv, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model inv) errs
  | .Assert cond => validateDiamondFieldAccessesForStmtExpr model cond.condition
  | .Assume cond => validateDiamondFieldAccessesForStmtExpr model cond
  | .PrimitiveOp _ args _ =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model a) []
  | .StaticCall _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc ++ validateDiamondFieldAccessesForStmtExpr model a) []
  | .Return (some v) => validateDiamondFieldAccessesForStmtExpr model v
  | .IncrDecr _ _ target =>
    match _htgt : target.val with
    | .Field tgt fieldName =>
      let innerErrors := validateDiamondFieldAccessesForStmtExpr model tgt
      let fieldError := checkDiamondFieldAccess model tgt fieldName target.source
      innerErrors ++ fieldError
    | .Local _ | .Declare _ => []
  | _ => []
  termination_by sizeOf expr
  decreasing_by
    all_goals simp_wf
    all_goals (try have := AstNode.sizeOf_val_lt expr)
    all_goals (try have := AstNode.sizeOf_val_lt t)
    all_goals (try have := Variable.sizeOf_field_target_lt_of_eq _htgt)
    all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
    all_goals (try term_by_mem)
    all_goals (try omega)
    -- For nested Variable.Field in Var (.Field ..) or IncrDecr (.Field ..) cases
    all_goals (cases expr; rename_i val _ _ _h; subst _h; simp_all; omega)

/--
Validate a Laurel program for diamond-inherited field accesses.
Returns an array of DiagnosticModel errors.
-/
def validateDiamondFieldAccesses (model: SemanticModel) (program : Program) : List DiagnosticModel :=
  let errors := program.staticProcedures.foldl (fun acc proc =>
    let bodyErrors := match proc.body with
      | .Transparent bodyExpr => validateDiamondFieldAccessesForStmtExpr model bodyExpr
      | .Opaque postconds impl _ =>
        let postErrors := postconds.foldl (fun acc2 pc => acc2 ++ validateDiamondFieldAccessesForStmtExpr model pc.condition) []
        let implErrors := match impl with
          | some implExpr => validateDiamondFieldAccessesForStmtExpr model implExpr
          | none => []
        postErrors ++ implErrors
      | .Abstract postconds => postconds.foldl (fun acc p => acc ++ validateDiamondFieldAccessesForStmtExpr model p.condition) []
      | .External => []
    acc ++ bodyErrors) []
  errors

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
        let scopedKey := (containerScopedName ct.name proc.name).text
        let _ ← defineNameCheckDup proc.name (.instanceProcedure ct.name proc)
                                   (some scopedKey)
    | .Constrained ct =>
      let _ ← defineNameCheckDup ct.name (.constrainedType ct)
    | .Datatype dt =>
      let _ ← defineNameCheckDup dt.name (.datatypeDefinition dt)
      for ctor in dt.constructors do
        let _ ← defineNameCheckDup ctor.name (.datatypeConstructor dt.name ctor)
        -- Register the tester function (e.g. `IntList..isNil`) as a static procedure.
        let testerProc := mkTesterProcedure dt ctor
        let _ ← defineNameCheckDup (mkId (dt.testerName ctor))
          (.staticProcedure testerProc) (some (dt.testerName ctor))
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
public def resolve (program : Program) (existingModel: Option SemanticModel := none) : ResolutionResult :=
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
  let typeLattice := TypeLattice.ofTypes program.types
  let (program', finalState) := phase1.run { nextId := nextId, typeLattice }
  -- Phase 2: build refToDef from the resolved program (all definitions now have UUIDs)
  let refToDef := buildRefToDef program'
  let semanticModel := {
    compositeCount := program.types.length,
    refToDef := refToDef,
    nextId := finalState.nextId
  }
  let diamondErrors := validateDiamondFieldAccesses semanticModel program'
  { program := program',
    model := semanticModel,
    errors := finalState.errors ++ diamondErrors
  }

/-! ## Resolution for UnorderedCoreWithLaurelTypes -/

/--
Convert an `UnorderedCoreWithLaurelTypes` to a flat `Program` suitable for
resolution. Additional type definitions (e.g. composite types from the original
Laurel program) can be supplied so that `UserDefined` type references resolve
correctly.
-/
private def unorderedCoreToProgram (uc : UnorderedCoreWithLaurelTypes)
    (additionalTypes : List TypeDefinition := []) : Program :=
  { staticProcedures := uc.functions ++ uc.coreProcedures,
    staticFields := [],
    types := uc.datatypes.map TypeDefinition.Datatype ++ additionalTypes,
    constants := uc.constants }

/--
Reconstruct an `UnorderedCoreWithLaurelTypes` from a resolved `Program`.
-/
private def fromResolvedProgram (resolvedProgram : Program)
    : UnorderedCoreWithLaurelTypes :=
  let resolvedProcs := resolvedProgram.staticProcedures
  let resolvedDatatypes := resolvedProgram.types.filterMap fun td =>
    match td with | .Datatype dt => some dt | _ => none
  { functions := resolvedProcs.filter (·.isFunctional)
    coreProcedures := resolvedProcs.filter (!·.isFunctional)
    datatypes := resolvedDatatypes
    constants := resolvedProgram.constants }

/--
Resolve an `UnorderedCoreWithLaurelTypes` by converting to a flat `Program`,
running the resolution pass, and reconstructing the result. Returns the
resolved `UnorderedCoreWithLaurelTypes` and the `SemanticModel`.

`additionalTypes` can supply extra type definitions (e.g. composite types) that
are not part of the `UnorderedCoreWithLaurelTypes` but are needed for resolving
`UserDefined` type references. These additional types should not be necessary
but they are because certain type references have incorrectly not been updated.
-/
public def resolveUnorderedCore (uc : UnorderedCoreWithLaurelTypes)
    (existingModel : Option SemanticModel := none)
    (additionalTypes : List TypeDefinition := [])
    : UnorderedCoreWithLaurelTypes × SemanticModel × Array DiagnosticModel :=
  let fnProgram := unorderedCoreToProgram uc additionalTypes
  let fnResolveResult := resolve fnProgram existingModel
  (fromResolvedProgram fnResolveResult.program, fnResolveResult.model, fnResolveResult.errors)

end -- public section
end Strata.Laurel
