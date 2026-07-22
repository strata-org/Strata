/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.UnorderedCore
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Tactics
public import Strata.Languages.Laurel.SemanticModel
public import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.HeapAnalysis
import Strata.Languages.Laurel.GlobalVarAnalysis
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.PushOldInward

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
  errors : Array Message := #[]

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
  errors : Array Message := #[]
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
  /-- Overload table for static procedures: each name maps to the list of
      registered overloads as `(uniqueId, procedure)` pairs, in declaration
      order. A name with more than one entry is overloaded. The flat `scope`
      map only retains the *last* overload per name, so this table is what
      `defIdForProcedure` uses to recover each overload's own id and what
      `Synth.staticCall` uses to select the overload matching a call's
      argument types. Populated by `preRegisterStaticProcedure`. -/
  overloads : Std.HashMap String (List (Nat × Procedure)) := {}
  /-- UniqueIds of static procedures rejected as conflicting duplicates. -/
  conflictingOverloads : Std.HashSet Nat := {}

abbrev ResolveM := StateM ResolveState

/-- Allocate a fresh unique ID. -/
private def freshId : ResolveM Nat := do
  let s ← get
  let id := s.nextId
  set { s with nextId := id + 1 }
  return id

/-- Insert a definition into the current scope, allocating a fresh unique ID when
    the identifier doesn't already carry one. Does NOT check for duplicates — use
    `defineNameCheckDup` for the checked variant. -/
private def defineName (iden : Identifier) (node : ResolvedNode) (overrideResolutionName: Option String := none) : ResolveM Identifier := do
  let resolutionName := overrideResolutionName.getD iden.text
  -- A value binding (local/parameter/quantifier var) may not shadow a name RESERVED by the
  -- frontend's coercion machinery (see `TypeLattice.reservedNames`): the realizer synthesizes
  -- calls to those names by bare identifier and assumes they resolve to their prelude
  -- declarations, so a shadowing binding would silently break coercion insertion (the
  -- synthesized call would re-resolve to the local on a later pass). Reject at the binding
  -- site with a user diagnostic, like a keyword. Only value bindings are gated; the reserved
  -- names' own top-level declarations (static procedures / datatype constructors+destructors)
  -- are exempt so the prelude can define them.
  let isValueBinding := match node with
    | .var .. | .parameter .. | .quantifierVar .. => true
    | _ => false
  if isValueBinding && ((← get).typeLattice.reservedNames.contains resolutionName) then
    let diag := diagnosticFromSource iden.source
      s!"'{resolutionName}' is a reserved name and cannot be used as a local variable, parameter, or bound variable"
    modify fun s => { s with errors := s.errors.push diag }
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


/-- Resolve a reference: look up the name in scope and assign the definition's ID.
    Returns the identifier with its ID filled in.
    When `expected` is provided, emits a diagnostic if the resolved node's kind is not
    in the list of expected kinds. -/
def resolveRef (name : Identifier) (source : FileRange := name.source)
    (expected : Array ResolvedNodeKind := #[]) : ResolveM Identifier := do
  let s ← get
  match s.scope.get? name.text with
  | some (defId, node) =>
    let name' := { name with uniqueId := some defId }
    if expected.size > 0 && node.kind != .unresolved && !expected.contains node.kind then
      let expectedStr := ", ".intercalate (expected.toList.map ResolvedNodeKind.name)
      let diag := diagnosticFromSource source
        s!"'{name}' resolves to {node.kind.name}, but expected {expectedStr}"
      modify fun s => { s with errors := s.errors.push diag }
    return name'
  | none =>
    -- Name not in scope: report it. Language frontends that reference unmodeled external
    -- names (e.g. the Python pipeline's imported/stdlib names) inject bodiless declarations
    -- for them so they resolve through the normal declaration path, rather than pre-registering
    -- them in the resolver.
    let diag := diagnosticFromSource source s!"Resolution failed: '{name}' is not defined"
    modify fun s => { s with errors := s.errors.push diag }
    return { name with uniqueId := none }

/-- Scope key for a name nested inside a container (composite, datatype),
    used to disambiguate members in the flat global scope. -/
private def containerScopedName (containerName memberName : Identifier) : Identifier :=
  mkId s!"{containerName.text}${memberName.text}"

/-- Declared type of `fieldName` in the scope of composite type `typeName`; `none` if
    unknown. Shared by `targetTypeName` and `incrDecrTargetType`. (`resolveFieldInTypeScope`
    below returns the field's *id* instead of its type, and additionally unfolds a type
    alias to its target before the lookup — this function does a direct scope lookup.) -/
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
      -- Peel `Box<int>` to its base: field names don't depend on type args, so a
      -- generic instantiation resolves fields against the generic composite `Box`'s
      -- scope. Needed here because field resolution runs at the initial resolve, before
      -- monomorphization turns this into a plain `.UserDefined Box$int`.
      | .Applied base _ =>
        match base.val with
        | .UserDefined typRef => pure (some typRef.text)
        | _ => pure none
      | _ => pure none
    | none => pure none
  | .Var (.Field inner fieldName) => do
    match (← targetTypeName inner) with
    | none => pure none
    | some innerTy =>
      match (← fieldTypeInScope innerTy fieldName) with
      | some (.UserDefined typRef) => pure (some typRef.text)
      | _ => pure none
  | .AsType _ castTy =>
    -- A cast `(e as T)` fixes the static type to `T` for a following field
    -- access, e.g. `(e as IndexError)#index`. This lets a `catch` binding or a `throwsOn` case
    -- binding (typed at the least common ancestor of the thrown types) be
    -- narrowed to a more specific subtype before dereferencing its fields.
    match castTy.val with
    | .UserDefined typRef => pure (some typRef.text)
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
  -- A type alias (`type P = Pt`) has no type-scope of its own — its fields live under the
  -- target composite's name. The first resolution runs BEFORE `TypeAliasElim`, so `p : P`'s
  -- field access reaches here with the alias name; unfold it to the target's base name
  -- (transitively, fuel-guarded against cycles) before the lookup.
  let rec unfoldAlias (name : String) (fuel : Nat) : String :=
    match fuel with
    | 0 => name
    | fuel + 1 =>
      match s.scope.get? name with
      | some (_, (.typeAlias ta : ResolvedNode)) =>
        match ta.target.val with
        | .UserDefined tgt => unfoldAlias tgt.text fuel
        | .Applied base _ => match base.val with
          | .UserDefined tgt => unfoldAlias tgt.text fuel
          | _ => name
        | _ => name
      | _ => name
  let typeName := unfoldAlias typeName 16
  match s.typeScopes.get? typeName with
  | some typeScope =>
    match typeScope.get? fieldName.text with
    | some (defId, _) => return some { fieldName with uniqueId := some defId }
    | none => return none
  | none => return none

/-- Resolve a field reference using the target's type to build a qualified lookup key.

    `holderTy?` is the *authoritative* concrete type of the receiver, as synthesized
    by `Synth.resolveStmtExpr` at the call site. When supplied it is tried FIRST: its
    base composite name (peeled via `unfold`+`highBaseName?`) keys the field-scope
    lookup. This is what makes a CHAINED access through a generic composite field
    resolve — e.g. `p#b#az` where `p : Pair<int,Z>` and field `b : B` (a type
    variable): the receiver `p#b` synthesizes to the concrete `Z` (via
    `concretizeFieldType`), so `#az` finds `Z`'s field. The string-based
    `targetTypeName` fallback below cannot recover this because a `.TVar`/`.Applied`
    field type carries no composite name on its own — it dropped to `none`, falling
    through to `resolveRef` and the spurious "'az' is not defined".

    Falls back (when `holderTy?` is absent or names no known composite) to
    `targetTypeName target`, then to the instance type name (for `self.field` in
    instance methods), then to unqualified `resolveRef`. Threading the already-
    computed holder type only ever ADDS a successful resolution (it never overrides
    a name the old path resolved differently — the type-scope field map is the same
    one both paths consult), so it is a pure completeness improvement, never a
    wrong-accept: a field absent from the concrete holder still falls through. -/
def resolveFieldRef (target : StmtExprMd) (fieldName : Identifier)
    (source : FileRange) (holderTy? : Option HighTypeMd := none) : ResolveM Identifier := do
  -- Authoritative path: use the synthesized concrete holder type when available.
  if let some holderTy := holderTy? then
    let s ← get
    if let some baseName := highBaseName? (s.typeLattice.unfold holderTy).val then
      if let some resolved ← resolveFieldInTypeScope baseName.text fieldName then
        return resolved
  let typeName? ← targetTypeName target
  -- Try type scope from the target's declared type
  if let some typeName := typeName? then
    if let some resolved ← resolveFieldInTypeScope typeName fieldName then
      return resolved
  -- Fallback: use the owning instance type (handles `self.field` when self has type `Any`)
  if let some instTypeName := (← get).instanceTypeName then
    if let some resolved ← resolveFieldInTypeScope instTypeName fieldName then
      return resolved
  -- The field name (an attribute, not a variable) did not resolve in any type scope.
  -- Leave it unresolved with no diagnostic ONLY for a genuinely gradual receiver:
  -- Unknown/Any, or a `UserDefined` name registered in `gradualTypes` (the dynamic top).
  -- Such a field access is sound-but-uninterpreted. For every other receiver — a known
  -- composite that lacks this field, OR a primitive (`int`/`bool`/… whose `targetTypeName`
  -- is `none`) — a missing field is a real bug (typo'd attribute), so fall through to
  -- `resolveRef` and preserve the "Resolution failed: 'field' is not defined" diagnostic.
  let s ← get
  let isGradualReceiver (n? : Option String) : Bool := match n? with
    | some n => s.typeLattice.gradualTypes.contains n
    | none => false  -- primitive / void / inferred receiver: NOT a gradual escape
  if isGradualReceiver typeName? || isGradualReceiver s.instanceTypeName then
    return { fieldName with uniqueId := none }
  else
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

/-- Type-argument arity error when `numDeclared ≠ numProvided`; shared by `resolveHighType`'s
    `.Applied` arm and `Synth.new` for identical wording. -/
private def checkTypeArgArity (source : FileRange) (name : String)
    (numDeclared numProvided : Nat) : ResolveM Unit := do
  unless numDeclared == numProvided do
    modify fun st => { st with errors := st.errors.push (diagnosticFromSource source
      s!"'{name}' expects {numDeclared} type argument(s) but {numProvided} were provided") }

/-- Reject a constrained (subset) type used as a generic datatype *type argument*
    (e.g. `Option<int32>`), in *any* position — a variable / parameter / return
    type or a datatype constructor field type. Such a type is currently
    over-approximated away: the constrained type is reduced to its base and its
    refinement predicate is not enforced on the datatype's contents. Rather than
    silently accept a value outside the subset, we reject it at resolution time
    until subset types are properly supported under polymorphism.

    A type parameter of the enclosing datatype resolves to a `.typeParameter` (a
    type variable), not a `.constrainedType`, so it is naturally not flagged — no
    name-list bookkeeping is needed, and a parameter that shadows a constrained
    type is handled by ordinary scoping. Only the direct argument is inspected;
    nesting (e.g. `Box<Option<int32>>`) is covered by the caller recursing into
    each argument. -/
private def checkTypeArgNotConstrained (arg : HighTypeMd) : ResolveM Unit := do
  match _h : arg.val with
  | .UserDefined name =>
    match (← get).scope.get? name.text with
    | some (_, node) =>
      if node.kind == .constrainedType then
        modify fun s => { s with errors := s.errors.push (diagnosticFromSource arg.source
          s!"constrained (subset) type '{name.text}' is not yet supported as a generic datatype type argument") }
    | none => pure ()
  -- Recurse through compound types: a constrained type carried *inside* a type
  -- argument (`Option<Map int int32>`) reaches the same refinement-dropping
  -- outcome this check exists to prevent — `resolveBaseType` over-approximates it
  -- and `ConstrainedTypeElim` never sees an enforcement point for it — so the
  -- whole argument has to be inspected, not just its head.
  | .TSet et => checkTypeArgNotConstrained et
  | .TMap kt vt => do
    checkTypeArgNotConstrained kt
    checkTypeArgNotConstrained vt
  | .Applied base args => do
    checkTypeArgNotConstrained base
    args.attach.forM fun ⟨a, _⟩ => checkTypeArgNotConstrained a
  | .Intersection tys => tys.attach.forM fun ⟨t, _⟩ => checkTypeArgNotConstrained t
  | _ => pure ()
  termination_by sizeOf arg
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt arg; rw [_h] at hsz)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

/-- Whether `ty` mentions one of `typeParams` anywhere, not just at its head.

    Used to decide whether a datatype constructor's declared field type is a
    *polymorphic slot*. A field typed exactly `T` is the obvious case, but a
    container over a parameter (`Map int T`, `Set T`, `Option<T>`) is equally
    polymorphic: the parameter is erased, so checking an argument against the
    declared type would compare a concrete instantiation (`Map int int`) with the
    phantom parameter and fail at every construction site.

    Each name is tested raw *and* unfolded: `unfold` is keyed on type-name text
    through the global constrained/alias map, so a global `constrained T` would
    rewrite a same-named parameter to its base and hide the slot. -/
private def mentionsTypeParam (ctx : TypeLattice) (typeParams : List String)
    (ty : HighTypeMd) : Bool :=
  match _h : ty.val with
  | .UserDefined name =>
    typeParams.contains name.text ||
      (match (ctx.unfold ty).val with
       | .UserDefined u => typeParams.contains u.text
       | _ => false)
  | .TSet et => mentionsTypeParam ctx typeParams et
  | .TMap kt vt =>
    mentionsTypeParam ctx typeParams kt || mentionsTypeParam ctx typeParams vt
  | .Applied base args =>
    mentionsTypeParam ctx typeParams base ||
      args.attach.any (fun ⟨a, _⟩ => mentionsTypeParam ctx typeParams a)
  | .Intersection tys => tys.attach.any (fun ⟨t, _⟩ => mentionsTypeParam ctx typeParams t)
  | _ => false
  termination_by sizeOf ty
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt ty; rw [_h] at hsz)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

/-- The declared type-parameter count of `name` when it resolves to a datatype
    definition; `none` when `name` is not a datatype (so the type-application /
    bare-reference checks below do not apply to it). -/
private def datatypeTypeArgArity (name : String) : ResolveM (Option Nat) := do
  match (← get).scope.get? name with
  | some (_, .datatypeDefinition dt) => pure (some dt.typeArgs.length)
  | _ => pure none

/-- The declared type-parameter *names* of `name` when it resolves to a datatype
    definition; `[]` otherwise. Used to tell an erased (polymorphic) slot from a
    concrete one. -/
private def datatypeTypeParamNames (name : String) : ResolveM (List String) := do
  match (← get).scope.get? name with
  | some (_, .datatypeDefinition dt) => pure (dt.typeArgs.map (·.text))
  | _ => pure []

/-- Reject a bare (unapplied) reference to a *generic* datatype in a user type
    position (e.g. `var w: Option` where `Option<T>` is declared). Left unapplied
    its type arguments would be inferred by first use elsewhere in the program —
    order-dependent and surprising — so we require the arguments to be written
    explicitly (`Option<int>`). A non-generic datatype, composite, alias, or
    constrained type is unaffected. (The erased constructor-result-type reference,
    e.g. `Nothing() : Option`, is produced internally via `getCallInfo` and never
    reaches here.) -/
private def checkBareGenericDatatype (name : Identifier) (source : FileRange) : ResolveM Unit := do
  match ← datatypeTypeArgArity name.text with
  | some n =>
    if n > 0 then
      modify fun s => { s with errors := s.errors.push (diagnosticFromSource source
        s!"generic datatype '{name.text}' must be applied to {n} type argument(s)") }
  | none => pure ()

/-- Validate the base of a generic type application `base<args>`, keyed off what
    `base` resolves to:
    - a type *parameter* cannot be applied to arguments (`T<int>`);
    - a datatype must be applied at its declared arity — a non-generic datatype
      applied to arguments (`Plain<int>`) or an arity mismatch
      (`Option<int, string>`) is rejected here rather than deferred to Core;
    - a composite, constrained (subset), or alias type is not generic, so
      applying it to arguments (`C<int>`) is rejected here too — otherwise it
      reaches Core / `translateType` and surfaces as an internal-error
      `strata-bug` instead of a clean *type 'X' is not generic* diagnostic.
    An unresolved base is left alone (`resolveRef` already reported it). -/
private def checkTypeApplication (base : Identifier) (numArgs : Nat) (source : FileRange) : ResolveM Unit := do
  match (← get).scope.get? base.text with
  | some (_, .typeParameter _) =>
    modify fun s => { s with errors := s.errors.push (diagnosticFromSource source
      s!"type parameter '{base.text}' cannot be applied to type arguments") }
  | some (_, .datatypeDefinition dt) =>
    let n := dt.typeArgs.length
    if n != numArgs then
      let msg := if n == 0 then
          s!"type '{base.text}' is not generic and cannot be applied to type arguments"
        else
          s!"generic datatype '{base.text}' expects {n} type argument(s) but {numArgs} were provided"
      modify fun s => { s with errors := s.errors.push (diagnosticFromSource source msg) }
  | some (_, .constrainedType _) =>
    -- A constrained type is never generic: applying it to type arguments is
    -- rejected here so the user gets a clean diagnostic rather than a downstream
    -- Core `strata-bug` (the `appliedType` grammar op accepts any identifier).
    modify fun s => { s with errors := s.errors.push (diagnosticFromSource source
      s!"type '{base.text}' is not generic and cannot be applied to type arguments") }
  | some (_, .compositeType _) | some (_, .typeAlias _) =>
    -- Generic composites (`Box<T>`) and generic aliases (`MyPair<A,B>`) ARE
    -- applicable (#1394). Arity is checked by the `.Applied` arm of
    -- `resolveHighType` against `parentExprMap`/`unfoldMap`; a genuinely
    -- non-generic composite/alias applied to args reaches Core as a dangling
    -- ref → fail-loud StrataBug (never a wrong-accept), so nothing to reject here.
    pure ()
  | _ => pure ()

/-- Resolve a `.UserDefined` type reference to `.UserDefined ref'` (resolved) or
    `.Unknown` (on failure / wrong kind — the diagnostic was already emitted by
    `resolveRef`). Collapsing a dangling reference to `Unknown` keeps later uses
    from being type-checked against a phantom type. Shared by the bare
    `.UserDefined` arm and an `.Applied` base; the bare-generic-reference
    rejection is applied only by the former (an `.Applied` base is not bare). -/
private def resolveTypeRef (ref : Identifier) (source : FileRange) : ResolveM HighType := do
  let ref' ← resolveRef ref source
    (expected := #[.compositeType, .constrainedType, .datatypeDefinition, .typeAlias, .typeParameter])
  let s ← get
  let kindOk : Bool := match s.scope.get? ref.text with
    | some (_, node) => node.kind == .unresolved ||
        (#[ResolvedNodeKind.compositeType, .constrainedType, .datatypeDefinition, .typeAlias, .typeParameter].contains node.kind)
    | none => false  -- name not defined: resolveRef already reported it
  if kindOk then pure (HighType.UserDefined ref') else pure HighType.Unknown

def resolveHighType (ty : HighTypeMd) : ResolveM HighTypeMd := do
  match ty with
  | AstNode.mk val _ =>
  let val' ← match val with
  | .UserDefined ref =>
    -- A bare name in type position may be (a) an in-scope type PARAMETER, (b) a
    -- concrete type, or (c) undefined / the wrong kind. Read its scope kind and branch:
    --   (a) `.typeParameter` → reclassify to `HighType.TVar` (#1394 polymorphism
    --       substrate).
    --   (b) composite/datatype/alias/constrained, or still-`.unresolved` → keep
    --       `UserDefined` (real subtype checking applies downstream — #1121). A
    --       bare reference to a generic DATATYPE is additionally rejected
    --       (`checkBareGenericDatatype`): its type arguments must be explicit.
    --   (c) anything else (a value name used as a type, etc.) → collapse to
    --       `Unknown` so later uses aren't type-checked against a phantom type;
    --       the "is not defined"/"wrong kind" diagnostic was already emitted by
    --       `resolveRef` (#1121's cascade-prevention).
    let nodeKind? := ((← get).scope.get? ref.text).map (·.2.kind)
    if nodeKind? == some ResolvedNodeKind.typeParameter then
      let ref' ← resolveRef ref ty.source (expected := #[ResolvedNodeKind.typeParameter])
      pure (HighType.TVar ref')
    else
      let ref' ← resolveRef ref ty.source
        (expected := #[.compositeType, .constrainedType, .datatypeDefinition, .typeAlias])
      checkBareGenericDatatype ref ty.source
      let kindOk : Bool := match nodeKind? with
        | some k => k == .unresolved ||
            (#[ResolvedNodeKind.compositeType, .constrainedType, .datatypeDefinition, .typeAlias].contains k)
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
    -- Resolve the base as an *applied* (not bare) type reference and validate the
    -- type-argument arity here in Laurel rather than deferring to Core. `base` is
    -- a `.UserDefined` name by grammar; resolving it via `resolveTypeRef` skips
    -- the bare-generic rejection (which applies only to unapplied references).
    let base' ← match base.val with
      | .UserDefined name =>
        checkTypeApplication name args.length base.source
        pure { val := (← resolveTypeRef name base.source), source := base.source }
      | _ => resolveHighType base
    let args' ← args.mapM resolveHighType
    -- Reject constrained (subset) types used as type arguments (upstream guard).
    args'.forM checkTypeArgNotConstrained
    -- Type-argument arity check for a generic ALIAS (`unfoldMap`) or generic
    -- COMPOSITE (`parentExprMap`) — #1394 adds both, which upstream's
    -- `checkTypeApplication` (called on the base above) does not cover (it only
    -- arity-checks generic datatypes). Generic DATATYPES are handled there; a
    -- wrong-arity datatype use is caught by that path. This lives HERE
    -- (`.Applied`), not `.UserDefined`, because the base recurses through
    -- `resolveHighType`, reaching `.UserDefined` as a bare zero-arg name — a
    -- zero-args check there would reject `Box<int>` itself. A bare generic used
    -- as a COMPLETE type (`var m: MyPair`) reaches Core as a dangling ref →
    -- StrataBug — fail-loud, never a wrong-accept.
    (do
      let s ← get
      if let some name := highBaseName? base'.val then
        -- Skip constrained-type bases: `checkTypeApplication` already rejected
        -- them ("not generic") above, so arity-checking them here would emit a
        -- SECOND diagnostic for the same error (unstable ordering). Only generic
        -- aliases and composites — which `checkTypeApplication` lets through —
        -- need the arity check.
        let isConstrained := match s.scope.get? name.text with
          | some (_, .constrainedType _) => true
          | _ => false
        unless isConstrained do
          let ctx := s.typeLattice
          let declParams? := (ctx.unfoldMap.get? name.text).map (·.1)
            |>.orElse (fun _ => (ctx.parentExprMap.get? name.text).map (·.1))
          if let some declParams := declParams? then
            checkTypeArgArity ty.source name.text declParams.length args'.length)
    pure (.Applied base' args')
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
private def typeMismatch (source : FileRange) (construct : Option StmtExpr)
    (problem : String) (actual : HighTypeMd) : ResolveM Unit := do
  let constructor := match construct with
    | some c => s!"'{c.constrName}' "
    | none   => ""
  let suffix := match actual.val with
    | .Unknown => ""
    | _        => s!", got '{formatType actual}'"
  let diag := diagnosticFromSource source s!"{constructor}{problem}{suffix}"
  modify fun s => { s with errors := s.errors.push diag }

/-- Collapse a proc-output type `(T, Error, ...)` to its value type `T` by dropping trailing
    `Error` outputs. The maybe-thrown exception is carried as an output but is not a value the
    caller binds, so single-output use sites compare against `T`, not the tuple. Shared by the
    resolver's subtyping checks and the imperative-expression lifter. -/
def stripTrailingErrors (actual : HighTypeMd) : HighTypeMd :=
  match actual.val with
  | .MultiValuedExpr (first :: rest) =>
    if rest.all (fun o => match o.val with | .UserDefined id => id.text == "Error" | _ => false)
    then first else actual
  | _ => actual

/-- `void` and `()` (unit) are mutually compatible — they both denote "no value." -/
private def isVoidLikeHT (t : HighType) : Bool := match t with
  | .TVoid | .MultiValuedExpr [] => true
  | .UserDefined id => id.text == "()"
  | _ => false

/-- Type-level subtype check: emits the standard "expected/got" diagnostic when
    `actual` is not a consistent subtype of `expected`. Used at sites where the
    actual type is already in hand (assignment, call args, body vs declared
    output) — equivalent to `Check.resolveStmtExpr e expected` but without re-synthesizing. -/
private def checkSubtype (source : FileRange) (expected : HighTypeMd) (actual : HighTypeMd) : ResolveM Unit := do
  let ctx := (← get).typeLattice
  let actual' := stripTrailingErrors actual
  -- Strip trailing `Error` from BOTH sides: an `.err`-grade body has actual type
  -- `(T, Error)` and an `.err`-grade declared output has expected type `(T, Error)`.
  -- Stripping only `actual` left `T` vs `(T, Error)` → a spurious mismatch whose
  -- diagnostic misleadingly printed identical tuples ("expected '(bool, Error)', got
  -- '(bool, Error)'"). Symmetric stripping compares the value types `T` vs `T`.
  let expected' := stripTrailingErrors expected
  let compatible :=
    (isVoidLikeHT actual'.val && isVoidLikeHT expected'.val) ||
    isConsistentSubtype ctx actual' expected'
  unless compatible do
    typeMismatch source none s!"expected '{formatType expected}'" actual

/-- PROOF-RELEVANT `[⇐] Sub`: check `actual ≤ expected` AND, on success, REALIZE the
    coercion witness onto the rewritten term `e` (returning the coerced term). This
    is `checkSubtype` plus term-rewriting; use it wherever the resolver holds the
    expression and rebuilds the AST (subsumption fallback, assignment RHS, …).

    The witness is the abstract `coerce` verdict; the concrete coercion is inserted
    by the frontend-supplied `ctx.realizeCoercion` (identity for native Laurel, so
    this is a no-op there). The decision and the realized coercion share the single
    `coerce` judgment, so they cannot disagree. On failure, emits the same diagnostic
    as `checkSubtype` and returns `e` unchanged. Void-like compatibility (statement
    position) inserts no coercion. -/
-- Stamp `uniqueId`s onto the `StaticCall` callees of a realizer-synthesized coercion
-- term, using ids already registered in `scope`. Only fills a callee whose `uniqueId`
-- is `none` and whose scope entry is a callable target (static procedure or datatype
-- constructor/destructor) — the kinds the realizer's bridge calls resolve to. A scope
-- miss, or a hit of any other kind (a user local/parameter/quantifier-var that happens
-- to share a bridge name), is left untouched (no diagnostic), so a genuinely-unresolved
-- synthesized name still fails loud in `heapParameterizationPass`. This mirrors the kind
-- gate `resolveRef` applies to user-written references. Recurses into arguments. Pure
-- (does not touch resolver state or push errors).
private partial def stampSynthesizedCallIds (scope : Scope) (e : StmtExprMd) : StmtExprMd :=
  match e.val with
  | .StaticCall callee args =>
    let callee' :=
      match callee.uniqueId with
      | some _ => callee
      | none => match scope.get? callee.text with
        | some (uid, node) =>
          if #[ResolvedNodeKind.staticProcedure, .datatypeConstructor, .datatypeDestructor].contains node.kind
          then { callee with uniqueId := some uid }
          else callee
        | none => callee
    let args' := args.map (stampSynthesizedCallIds scope)
    { e with val := .StaticCall callee' args' }
  | _ => e

private def coerceTo (source : FileRange) (expected : HighTypeMd) (actual : HighTypeMd)
    (e : StmtExprMd) : ResolveM StmtExprMd := do
  let ctx := (← get).typeLattice
  let actual' := stripTrailingErrors actual
  let expected' := stripTrailingErrors expected
  if isVoidLikeHT actual'.val && isVoidLikeHT expected'.val then
    pure e
  else match coerce ctx actual' expected' with
    | some verdict =>
      match ctx.realizeCoercion with
      | some realize =>
        -- The realizer synthesizes box/unbox bridge calls (e.g. `from_int`,
        -- `Any..as_Dict!`, `Any_sets!`) with `uniqueId = none`. Stamp each such call's
        -- callee with the uniqueId already registered in scope (they are declared prelude
        -- procedures / `Any` datatype constructors+accessors), so downstream passes —
        -- notably `heapParameterizationPass` — see resolved names and need no name-list
        -- allowlist. A scope miss leaves `uniqueId = none` untouched (no diagnostic pushed):
        -- a genuinely-unresolved synthesized name then fails loud in the heap pass, as intended.
        let s ← get
        pure (stampSynthesizedCallIds s.scope (realize verdict e))
      | none => pure e
    | none =>
      typeMismatch source none s!"expected '{formatType expected}'" actual
      pure e

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
  | .TVoid, _ | _, .TVoid => some { val := .TVoid, source := a.source }
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

/-- The declared return type of a call to `proc`, tagged with `callee`'s source.
    Zero outputs synthesize `TVoid`, a single output its type, and multiple
    outputs a `MultiValuedExpr`. Shared by `getCallInfo` and overload selection. -/
private def procReturnType (callee : Identifier) (proc : Procedure) : HighTypeMd :=
  match proc.outputs with
  | [] => { val := .TVoid, source := callee.source }
  | [singleOutput] => singleOutput.type
  | outputs => { val := .MultiValuedExpr (outputs.map (·.type)), source := callee.source }

/-- Concretize a field's declared type at an access site: substitute the field's DECLARING
    composite's params with the holder's args. Else raw `.TVar T` hits the wildcard and a
    cross-type write is wrongly accepted (imprecise, not unsound — Core havocs the read back).
    - OWN: `{D.params := holderArgs}`.
    - INHERITED: find `D<dArgs>` in `substitutedAncestors holder holderArgs` (remap-aware:
      `GHolder<A,B> extends Base<B,A>` → `Base<bool,int>`), then `{D.params := dArgs}`.
    Only ever more concrete; identity on polymorphic accesses; raw-type fallback otherwise. -/
private def concretizeFieldType (holderTy : HighTypeMd) (fieldName' : Identifier)
    : ResolveM HighTypeMd := do
  let s ← get
  let raw ← getVarType fieldName'
  -- Need the field's declaring composite + raw type.
  match fieldName'.uniqueId.bind s.idToNode.get? with
  | some (.field declType fld) =>
    let ctx := s.typeLattice
    -- Peel the holder to (base name, concrete args).
    let holderTy' := ctx.unfold holderTy
    let holder? : Option (String × List HighTypeMd) := match holderTy'.val with
      | .UserDefined n => some (n.text, [])
      | .Applied base args => (highBaseName? base.val).map (fun n => (n.text, args))
      | _ => none
    match holder? with
    | none => pure raw
    | some (holderName, holderArgs) =>
      -- The concrete args the holder supplies *for the declaring composite* D.
      let declArgs? : Option (List HighTypeMd) :=
        if holderName == declType.text then some holderArgs
        else (ctx.substitutedAncestors holderName holderArgs).findSome? fun anc =>
          match anc.val with
          | .UserDefined n => if n.text == declType.text then some [] else none
          | .Applied base args =>
            match highBaseName? base.val with
            | some n => if n.text == declType.text then some args else none
            | none => none
          | _ => none
      match declArgs?, ctx.parentExprMap.get? declType.text with
      | some declArgs, some (declParams, _) =>
        -- Arity must match for the substitution to be meaningful; the legacy bare
        -- `new C` form (no args) lands here as a mismatch → safe raw fallback.
        if declParams.length == declArgs.length && !declParams.isEmpty then
          let subst : Std.HashMap String HighTypeMd :=
            (declParams.zip declArgs).foldl (fun m (p, a) => m.insert p.text a) {}
          pure (substTypeVars subst fld.type)
        else pure raw
      | _, _ => pure raw
  | _ => pure raw

/-- Get the call return type and parameter types for a callee from scope. -/
private def getCallInfo (callee : Identifier) : ResolveM (HighTypeMd × List HighTypeMd) := do
  let s ← get
  match s.scope.get? callee.text with
  | some (_, .staticProcedure proc) | some (_, .instanceProcedure _ proc) =>
    pure (procReturnType callee proc, proc.inputs.map (·.type))
  | some (_, .datatypeConstructor t ctor) =>
    -- Testers (e.g. "Color..isRed") return Bool; constructors return the type.
    -- A constructor's argument types ARE its parameter types: return them so the
    -- call rule checks + coerces each argument against them (e.g. `ListAny_cons(1,
    -- …)` coerces `1` into the `Any` head slot).
    if (callee.text.splitOn "..is").length > 1 then
      pure ({ val := .TBool, source := callee.source }, [])
    else
      pure ({ val := .UserDefined t, source := callee.source }, ctor.args.map (·.type))
  | some (_, .datatypeDestructor dtName p) =>
    -- A destructor's result is its field's declared type — except on a *generic*
    -- datatype, where that type may mention the datatype's erased type
    -- parameters: `Option..value(o)` is declared `T`, and the instantiation is not
    -- known here (the type argument is carried, not substituted). Reporting `T`
    -- would make every use of the result fail against a concrete type, e.g.
    -- `Option..value(o) == 42` -> "cannot compare 'T' with 'int'". Such a slot is
    -- gradual (`Unknown`); a field type with no parameter in it is precise as-is.
    let params ← datatypeTypeParamNames dtName.text
    let ctx := (← get).typeLattice
    if mentionsTypeParam ctx params p.type then
      pure ({ val := .Unknown, source := callee.source },
            [{ val := .Unknown, source := callee.source }])
    else
      pure (p.type, [{ val := .Unknown, source := callee.source }])
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

/-! ## Overloaded static procedures

Multiple static procedures may share a name as long as no two have *conflicting*
signatures. Overloads are tracked in `ResolveState.overloads`; the flat `scope`
map only retains the last overload per name, so these helpers recover each
overload's own id (`defIdForProcedure`) and collect the overloads matching a
call's argument types (`selectOverloads`), from which `Synth.staticCall` picks
the unique match or reports an ambiguous / unresolved call. -/

/-- Two types *overlap* when some argument could satisfy both as a parameter —
    i.e. one is a consistent subtype of the other in either direction. This is
    exactly the negation of "no call can be ambiguous between them": `Unknown`
    (the dynamic type) overlaps everything, and a subtype overlaps its
    supertype. Built from `isConsistentSubtype`, the same relation
    `overloadAccepts` uses to select an overload, so "overlapping parameters"
    and "a single call both overloads accept" stay in agreement. -/
private def typesOverlap (ctx : TypeLattice) (a b : HighTypeMd) : Bool :=
  -- Realizer-independent: clear the realizer so numeric widening (int→real) does not make
  -- the built-in `$add(int,int)`/`$add(real,real)` pairs register as conflicting overloads.
  let ctxNoWiden := { ctx with realizeCoercion := none }
  isConsistentSubtype ctxNoWiden a b || isConsistentSubtype ctxNoWiden b a

/-- Two static-procedure signatures conflict — i.e. cannot coexist as overloads —
    when they have the same arity and every parameter pair's types overlap
    (`typesOverlap`). This is deliberately more aggressive than structural
    equality: if two overloads' parameters merely overlap (e.g. one takes a
    subtype of the other's, or either takes `Unknown`) then *every* call that
    matches one matches the other, so the pair is rejected at declaration time.
    This rules out the always-ambiguous pairs up front but is not a completeness
    guarantee: pairwise non-overlap does not preclude a common descendant in the
    lattice (the `Top1`/`Top2`/`C` diamond), so a specific call can still match
    two accepted overloads. That residual ambiguity is caught per call site by
    `selectOverloads` / `Synth.staticCall` rather than at declaration. -/
private def signaturesConflict (ctx : TypeLattice) (a b : Procedure) : Bool :=
  a.inputs.length == b.inputs.length &&
    (a.inputs.zip b.inputs).all (fun (pa, pb) => typesOverlap ctx pa.type pb.type)

/-- Structural (arity + per-parameter `highEq`) signature equality. Unlike
    `signaturesConflict` this does not consult the type lattice; it is used only
    to recover an overload's own id from the (already conflict-free) overload
    table, where an exact structural match is unique. -/
private def sameSignature (a b : Procedure) : Bool :=
  a.inputs.length == b.inputs.length &&
    (a.inputs.zip b.inputs).all (fun (pa, pb) => highEq pa.type pb.type)

/-- Whether `proc` accepts a call with the given argument types: the arity
    matches and every argument is a consistent subtype of the corresponding
    parameter. Uses the same relation (`isConsistentSubtype`) as ordinary
    argument checking, so overload selection agrees with type checking. -/
private def overloadAccepts (ctx : TypeLattice) (proc : Procedure)
    (argTys : List HighTypeMd) : Bool :=
  proc.inputs.length == argTys.length &&
    (proc.inputs.zip argTys).all (fun (p, argTy) => isConsistentSubtype ctx argTy p.type)

/-- All overloads that accept a call's argument types. Registration only rejects
    *pairwise* parameter overlap (`signaturesConflict`), which is not enough to
    guarantee a unique match: with multiple inheritance a single argument type
    can be a consistent subtype of two otherwise non-overlapping parameter types
    (the diamond `C extends Top1, Top2` accepted by both `f(Top1)` and
    `f(Top2)`), and a gradual `Unknown` argument is a consistent subtype of every
    parameter. Both are genuine call-site ambiguities, so this returns *every*
    matching candidate and lets the caller decide: no match is an
    unresolved-overload error, exactly one is the resolved callee, and two or
    more is an ambiguous-call error. Returning a list (rather than the first
    match) is what lets `Synth.staticCall` report ambiguity instead of silently
    picking the first declaration. -/
private def selectOverloads (ctx : TypeLattice) (candidates : List (Nat × Procedure))
    (argTys : List HighTypeMd) : List (Nat × Procedure) :=
  -- Prefer overloads matching without numeric widening (an exact int match beats a
  -- widened int→real one); fall back to widened matches only when none match exactly.
  let accepted := candidates.filter (fun (_, p) => overloadAccepts ctx p argTys)
  let exact := accepted.filter (fun (_, p) => overloadAccepts { ctx with realizeCoercion := none } p argTys)
  if exact.isEmpty then accepted else exact

/-- Recover the uniqueId that `preRegisterStaticProcedure` assigned to *this*
    overload. The flat `scope` only remembers the last overload per name, so for
    an overloaded name we match on the structural signature (`sameSignature`),
    which is unique within the conflict-free overload table; for a non-overloaded
    name the single scope entry is used. -/
private def defIdForProcedure (proc : Procedure) : ResolveM (Option Nat) := do
  if let some uid := proc.name.uniqueId then return some uid
  let s ← get
  match s.overloads.get? proc.name.text with
  | some cands =>
    match cands.find? (fun (_, p) => sameSignature p proc) with
    | some (id, _) => pure (some id)
    | none => pure ((s.scope.get? proc.name.text).map (·.1))
  | none => pure ((s.scope.get? proc.name.text).map (·.1))

/-- Pre-register a static procedure, allowing overloads. A procedure may share
    its name with previously-registered overloads as long as none has a
    conflicting signature (`signaturesConflict`). A conflicting redeclaration —
    or a clash with a non-procedure definition already bound to the name — is
    reported as a duplicate (matching `defineNameCheckDup`) and an `unresolved`
    placeholder is bound so later references don't cascade. Otherwise the
    procedure is registered, appended to the overload table, and made the
    current scope entry for its name.

    The definition-site id is reused across resolution passes: if the
    procedure's name already carries a `uniqueId` (from an earlier `resolve`,
    e.g. a re-resolution triggered by `needsResolves`) that id is kept, exactly
    as `defineNameCheckDup.defineName` does for every other definition kind.
    Only a first-time (unstamped) declaration allocates a `freshId`. Keeping the
    id stable across passes preserves debuggability — a consumer holding a
    static procedure's id across `resolve` calls sees the same id — and stops
    `nextId` from growing every pass. -/
private def preRegisterStaticProcedure (proc : Procedure) : ResolveM Unit := do
  let name := proc.name.text
  let s ← get
  let ctx := s.typeLattice
  let existing := s.overloads.getD name []
  let nameTaken := s.currentScopeNames.contains name
  -- Reuse the already-stamped definition-site id when re-resolving; only a
  -- first-time declaration needs a fresh id.
  let id ← match proc.name.uniqueId with
    | some uid => pure uid
    | none => freshId
  -- External procedures cannot be overloaded.
  let allOverloads := existing ++ [(id, proc)]
  let externalConflict := allOverloads.length > 1 && allOverloads.any (fun (_, p) => p.body matches .External)
  if externalConflict then
    let diag := diagnosticFromSource proc.name.source
      s!"A set of procedure overloads must not have any external procedures"
    let existingIds := existing.map (·.1)
    modify fun s => { s with
      errors := s.errors.push diag,
      scope := s.scope.insert name (id, .unresolved proc.name.source),
      idToNode := s.idToNode.insert id (.unresolved proc.name.source),
      currentScopeNames := s.currentScopeNames.insert name,
      conflictingOverloads := existingIds.foldl (·.insert ·) (s.conflictingOverloads.insert id) }
    return
  -- A clash with a non-procedure definition (name taken but not by an overload
  -- set), or with an existing overload whose signature conflicts (parameters
  -- overlap), is a duplicate.
  if (nameTaken && existing.isEmpty) || existing.any (fun (_, p) => signaturesConflict ctx p proc) then
    let diag := diagnosticFromSource proc.name.source
      s!"Duplicate definition '{name}' is already defined in this scope"
    let conflictIds := existing.filter (fun (_, p) => signaturesConflict ctx p proc)
      |>.map (·.1)
    modify fun s => { s with
      errors := s.errors.push diag,
      scope := s.scope.insert name (id, .unresolved proc.name.source),
      idToNode := s.idToNode.insert id (.unresolved proc.name.source),
      currentScopeNames := s.currentScopeNames.insert name,
      conflictingOverloads := conflictIds.foldl (·.insert ·) (s.conflictingOverloads.insert id) }
  else
    modify fun s => { s with
      scope := s.scope.insert name (id, .staticProcedure proc),
      idToNode := s.idToNode.insert id (.staticProcedure proc),
      currentScopeNames := s.currentScopeNames.insert name,
      overloads := s.overloads.insert name (existing ++ [(id, proc)]) }

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

/-- A short display name for a primitive/base `HighType`, for compound-assignment
    diagnostics. Shared by the target check and the RHS check so their wording
    cannot drift. -/
private def highTypeDisplayName : HighType → String
  | .TInt => "int" | .TReal => "real" | .TFloat64 => "float64"
  | .TString => "string" | .TBool => "bool" | .TBv n => s!"bv{n}"
  | .UserDefined r => r.text | _ => "<unknown>"

/-- Whether the (already base-peeled) element type `baseTy` is an acceptable target
    for compound-assignment operator `op`. Used by the resolution-time target check
    (`checkCompoundAssignTargetType`), driven by what the Laurel→Core lowering of
    `target op rhs` supports: `+= -= *= /=` accept `int`/`real`; `%=` is `int`-only
    (`.Mod` has no real lowering); `^=` is `string`-only. `Unknown` is accepted for
    every operator so an already-unresolved target is left alone rather than stacking a
    spurious operator-type error on top of its real resolution error (mirrors the
    `.Unknown` arm of `checkIncrDecrTargetType`). -/
private def compoundAssignAccepts (op : Operation) (baseTy : HighType) : Bool :=
  match baseTy with
  | .Unknown => true
  | _ =>
    match op with
    | .StrConcat => match baseTy with | .TString => true | _ => false
    | .Mod       => match baseTy with | .TInt => true | _ => false
    | _          => match baseTy with | .TInt | .TReal => true | _ => false

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
  | .Declare param => pure (param.type.map (·.val))

/-- Emit a diagnostic if `++`/`--` is applied to an unsupported element type.
    Only `int` and int-based constrained types (e.g. `nat`) are supported by the
    `EliminateIncrDecrAndCompoundAssign` lowering; `bv`, `real`, and `float64` are rejected here
    with a clear Laurel diagnostic (and a source range) rather than leaking a raw
    Core unification error from a later pass. Unknown/unresolved types are left
    alone so that resolution errors are not duplicated as spurious incr/decr
    errors. -/
private def checkIncrDecrTargetType (op : IncrDecrOp) (target : VariableMd)
    (source : FileRange) : ResolveM Unit := do
  match (← incrDecrTargetType target) with
  | none => pure ()
  | some ty =>
    let s ← get
    let baseTy := underlyingBaseType s 100 ty
    -- Allowlist: `++`/`--` lower to `x := x + 1` with an *int* literal, so only `int`
    -- (and int-based constrained types, which peel to `TInt`) are supported. `Unknown`
    -- is left alone so an unresolved target does not get a spurious incr/decr error on
    -- top of its real resolution error. Everything else (`real`, `float64`, `bv`,
    -- `string`, composites, …) is rejected here with a clear message rather than leaking
    -- a raw Core unification error from a later pass.
    match baseTy with
    | .TInt | .Unknown => pure ()
    | _ =>
      let opName := match op with
        | .Incr => "increment ('++')"
        | .Decr => "decrement ('--')"
      let tyName := highTypeDisplayName baseTy
      let diag := diagnosticFromSource source
        s!"The {opName} operator is only supported on 'int' and int-based \
           constrained types (e.g. 'nat'), but the operand has type '{tyName}'. \
           Use an explicit assignment instead, e.g. 'x := x + 1'."
      modify fun s => { s with errors := s.errors.push diag }

/-- Emit a diagnostic if a compound-assignment operator is applied to an unsupported
    target element type, per `compoundAssignAccepts`. Checks only the *target*; the RHS
    is type-checked by the `Check.resolveStmtExpr` call in `Synth.compoundAssign`. -/
private def checkCompoundAssignTargetType (op : Operation) (target : VariableMd)
    (source : FileRange) : ResolveM Unit := do
  match (← incrDecrTargetType target) with
  | none => pure ()
  | some ty =>
    let s ← get
    let baseTy := underlyingBaseType s 100 ty
    let opTok := match op with
      | .Add => "+=" | .Sub => "-=" | .Mul => "*=" | .Div => "/="
      | .Mod => "%=" | .StrConcat => "^=" | _ => "(compound assignment)"
    if !(compoundAssignAccepts op baseTy) then
      let allowed := match op with
        | .StrConcat => "'string'"
        | .Mod => "'int' and int-based constrained types (e.g. 'nat')"
        | _ => "'int', int-based constrained types (e.g. 'nat'), and 'real'"
      let tyName := highTypeDisplayName baseTy
      let diag := diagnosticFromSource source
        s!"The '{opTok}' operator is only supported on {allowed}, but the operand has \
           type '{tyName}'. Use an explicit assignment instead, e.g. 'x := x {opTok.dropEnd 1} e'."
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
rules* index in `LaurelUserGuide.lean`:

- Literals — `Synth.litInt`, `Synth.litBool`, `Synth.litString`, `Synth.litDecimal`
- Variables — `Synth.varLocal`, `Synth.varField`, `Check.varDeclare`
- Control flow — `Check.while`, `Check.exit`, `Check.return`,
  `Check.block`, `Check.ifThenElse`
- Verification statements — `Check.assert`, `Check.assume`
- Assignment — `Synth.assign`, `Check.assign`
- Calls — `Synth.staticCall`, `Synth.instanceCall` (operators included: `x + y`
  is a call to the built-in `$add` wrapper, so it resolves as an overload)
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

/-- Shared guard for Decl-Synth (`Synth.declInfer`/`Check.declInfer`): the
    initializer's synthesized type must be a *value* type to be adopted for
    the binding. `TVoid` (a void procedure call, a `while`, an `if` without
    `else`, …) and `MultiValuedExpr` (a multi-output call) carry no single
    value to bind, so they are diagnosed and the binding falls back to
    `Unknown`, suppressing cascades on later uses of the variable. -/
private def declInferValueType (name : Identifier) (initSource : FileRange)
    (valueTy : HighTypeMd) : ResolveM HighTypeMd := do
  match valueTy.val with
  | .TVoid =>
    let diag := diagnosticFromSource initSource
      s!"cannot infer a type for '{name.text}': the initializer yields no value (type 'void')"
    modify fun s => { s with errors := s.errors.push diag }
    pure { val := .Unknown, source := valueTy.source }
  | .MultiValuedExpr _ =>
    let diag := diagnosticFromSource initSource
      "multi-output call cannot be used as a value here; it returns multiple values. Unpack it into separate variables first"
    modify fun s => { s with errors := s.errors.push diag }
    pure { val := .Unknown, source := valueTy.source }
  | _ => pure valueTy

/-- (Decl-Synth over multi-assign) Component types each target adopts from a
    synthesized multi-valued RHS; all `none` on a non-multi-valued RHS.
    Shared by `Synth.assign`/`Check.assign`. `inferInfo` is `some` only when
    at least one target is an unannotated `Declare`, so for a fully-annotated
    multi-assign this returns all `none` and never diagnoses — the ordinary
    push-in check reports any mismatch there.

    When the RHS *is* multi-valued but its arity doesn't match the target
    count, no component can be adopted. That mismatch is diagnosed here —
    "tried to unpack N values into M variables" — naming the actual cause,
    and `arityError = true` tells the caller to skip the tuple-level Sub
    check, which would only restate the same problem as an opaque
    `expected '(Unknown, …)'` tuple mismatch built from the fallback
    bindings. The targets still bind `Unknown`, suppressing cascades on
    later uses. -/
private def componentTypes (targets : List VariableMd)
    (inferInfo : Option (StmtExprMd × HighTypeMd))
    : ResolveM (List (Option HighTypeMd) × Bool) := do
  match inferInfo with
  | some (value', valueTy) =>
    match valueTy.val with
    | .MultiValuedExpr tys =>
      if tys.length == targets.length then
        pure (tys.map some, false)
      else
        let diag := diagnosticFromSource value'.source
          s!"tried to unpack {tys.length} values into {targets.length} variables"
        modify fun s => { s with errors := s.errors.push diag }
        pure (targets.map fun _ => none, true)
    | _ => pure (targets.map fun _ => none, false)
  | none => pure (targets.map fun _ => none, false)

/-- Whether `pred`, the guard of a `catch <binding> when pred`, provably holds
    for every value of type `ty` — i.e. that clause definitely catches `ty`.

    Conservative: it only reports an absorption it can prove, so an unknown guard
    keeps the type (a `catch` binding stays broad, never wrongly narrowed). -/
private def catchGuardCatches (lattice : TypeLattice) (binding : Identifier)
    (pred : StmtExprMd) (ty : HighTypeMd) : Bool :=
  -- `_h` names the discriminant equation so the termination proof can relate a
  -- disjunct's size back to `pred` (used only there, hence the `_` prefix).
  match _h : pred.val with
  | .LiteralBool true => true
  | .IsType target guardTy =>
    match target.val with
    | .Var (.Local n) => n.text == binding.text && isSubtype lattice ty guardTy
    | _ => false
  -- A disjunction of type tests catches a type when either side does. Both spellings
  -- count: `|` is `$or` and `||` is the short-circuiting `$orElse` (see
  -- `Operation.procName`). Neither wrapper is overloaded, and this runs during
  -- resolution — before `UniqueOverloadNames` — so matching on the callee text is safe.
  | .StaticCall callee [p1, p2] =>
    match Operation.ofProcName? callee.text with
    | some .Or | some .OrElse =>
      catchGuardCatches lattice binding p1 ty || catchGuardCatches lattice binding p2 ty
    | _ => false
  | _ => false
  termination_by sizeOf pred
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt pred; rw [_h] at hsz)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

/-- Whether a `catch` clause definitely catches every value of type `ty`.
    An absent guard is a catch-all. -/
private def clauseCatches (lattice : TypeLattice) (c : CatchClause) (ty : HighTypeMd) : Bool :=
  match c.predicate with
  | none => true
  | some p => catchGuardCatches lattice c.binding p ty

/-- Name-keyed adapter over `catchGuardCatches`, for the phase that works in type
    *names* rather than resolved types: `collectThrownTypeNames` runs while the
    `catch` binding's own type is still being computed, so a nested `try` must not
    leak the types its own catches already absorb into an outer binding's
    least-common-ancestor. Only the binding's text and the named type matter to
    the guard analysis, so this wraps them and delegates rather than repeating the
    recursion. -/
private def catchGuardCatchesName (lattice : TypeLattice) (binding : String)
    (pred : StmtExprMd) (tyName : String) : Bool :=
  catchGuardCatches lattice (mkId binding) pred
    { val := .UserDefined (mkId tyName), source := .unknown }

/-- Whether a `catch` clause provably absorbs a thrown value of the composite
    named `tyName`: the name-keyed adapter over `clauseCatches`. -/
private def clauseCatchesName (lattice : TypeLattice) (c : CatchClause) (tyName : String) : Bool :=
  clauseCatches lattice c { val := .UserDefined (mkId tyName), source := .unknown }

/-- Over-approximate the composite type *names* thrown within `expr`: the
    operand types of direct `throw`s plus the declared `throws` type of any
    procedure it calls. Used to type a `catch` binding at the least common
    ancestor of these (so `e#field` type-checks against the shared supertype
    without a downcast).

    `throw` operands are read structurally — `new T`/`(x as T)` give `T`
    directly; a `Var` local/parameter is looked up (inner-block declarations via
    the threaded `env`, outer names via the current scope). Callee `throws` is
    available because `preRegisterTopLevel` stores each procedure's full
    signature in scope before any body is resolved. Operands whose type cannot
    be determined contribute nothing (the join is over what is known). -/
private def collectThrownTypeNames (env : Std.HashMap String String) (expr : StmtExprMd)
    : ResolveM (List String) := do
  let operandName (op : StmtExprMd) : ResolveM (Option String) := do
    match op.val with
    | .New ref => pure (some ref.text)
    | .AsType _ ty => pure (match ty.val with | .UserDefined r => some r.text | _ => none)
    | .Var (.Local id) =>
      match env.get? id.text with
      | some n => pure (some n)
      | none =>
        match (← get).scope.get? id.text with
        | some (_, node) => pure (match node.getType.val with | .UserDefined r => some r.text | _ => none)
        | none => pure none
    | _ => pure none
  let calleeThrowsName (callee : Identifier) : ResolveM (Option String) := do
    match (← get).scope.get? callee.text with
    | some (_, .staticProcedure p) | some (_, .instanceProcedure _ p) =>
      pure (p.throwsType.bind fun t => match t.val with | .UserDefined r => some r.text | _ => none)
    | _ => pure none
  -- Recursive descents go through `attach` (and named discriminant equations) so
  -- each child carries the membership/shape proof the termination argument needs.
  match _h : expr.val with
  | .Throw op => pure ((← operandName op).toList ++ (← collectThrownTypeNames env op))
  | .StaticCall callee args =>
    let rs ← args.attach.mapM (fun ⟨a, _⟩ => collectThrownTypeNames env a)
    pure ((← calleeThrowsName callee).toList ++ rs.flatten)
  | .InstanceCall target callee args =>
    let rs ← args.attach.mapM (fun ⟨a, _⟩ => collectThrownTypeNames env a)
    pure ((← calleeThrowsName callee).toList ++ (← collectThrownTypeNames env target) ++ rs.flatten)
  | .IfThenElse c t el =>
    let ee ← match _hel : el with | some x => collectThrownTypeNames env x | none => pure []
    pure ((← collectThrownTypeNames env c) ++ (← collectThrownTypeNames env t) ++ ee)
  | .While c _ _ b _ => pure ((← collectThrownTypeNames env c) ++ (← collectThrownTypeNames env b))
  | .Assign targets v =>
    -- A `Field` target carries an arbitrary object expression (`mk()#x := 1`), so
    -- a throw reached through it must contribute to the enclosing binding's join
    -- too. The generic traversals in `MapStmtExpr` walk these; the hand-written
    -- descents here have to match them.
    let ts ← targets.attach.mapM (fun ⟨t, _⟩ =>
      match _ht : t.val with
      | .Field obj _ => collectThrownTypeNames env obj
      | _ => pure [])
    pure (ts.flatten ++ (← collectThrownTypeNames env v))
  | .Return (some v) => collectThrownTypeNames env v
  | .ProveBy v pf => pure ((← collectThrownTypeNames env v) ++ (← collectThrownTypeNames env pf))
  | .Try body catches finally? =>
    let ff ← match _hf : finally? with | some f => collectThrownTypeNames env f | none => pure []
    let cc ← catches.attach.mapM (fun ⟨c, _⟩ => collectThrownTypeNames env c.body)
    let bodyThrows ← collectThrownTypeNames env body
    -- Only what escapes this nested `try` can reach an outer `catch` binding, so
    -- drop the body throws its own catches provably absorb (mirroring
    -- `exceptionEscapes`); otherwise an inner-handled type would pollute the
    -- outer binding's least-common-ancestor and could spuriously report "no
    -- common ancestor". Handler and `finally` throws still escape outward.
    let lattice := (← get).typeLattice
    let residual := bodyThrows.filter fun n => !catches.any (fun c => clauseCatchesName lattice c n)
    pure (residual ++ cc.flatten ++ ff)
  | .Block stmts _ =>
    let (_, acc) ← stmts.attach.foldlM (init := (env, ([] : List String))) fun (st) ⟨s, _⟩ => do
      let (env', acc) := st
      let more ← collectThrownTypeNames env' s
      -- A local declaration contributes its declared type name so a later
      -- `catch e when e is T` guard can be resolved against it. The annotation is
      -- optional (`Parameter?`), and an unannotated declaration contributes
      -- nothing: there is no name to record, and the binding's type is inferred
      -- elsewhere.
      let noteDeclaredType (param : Parameter?) (e : Std.HashMap String String)
          : Std.HashMap String String :=
        match param.type with
        | some ty => match ty.val with
          | .UserDefined r => e.insert param.name.text r.text
          | _ => e
        | none => e
      let env'' := match s.val with
        | .Var (.Declare param) => noteDeclaredType param env'
        | .Assign [⟨.Declare param, _⟩] _ => noteDeclaredType param env'
        | _ => env'
      pure (env'', acc ++ more)
    pure acc
  | _ => pure []
  termination_by sizeOf expr
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt expr; rw [_h] at hsz)
    all_goals (try have hcatch := CatchClause.sizeOf_body_lt ‹_›)
    all_goals (try term_by_mem)
    -- Descent into a `Field` assignment target's object expression: the target is
    -- a member of `targets` and the object is smaller than the target.
    all_goals (try (
      have hobj := Variable.sizeOf_field_target_lt_of_eq _ht
      have hmem := List.sizeOf_lt_of_mem ‹_›
      simp at hsz
      omega))
    all_goals (try (simp_all; omega))

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
  | .CompoundAssign op target rhs =>
    Synth.compoundAssign exprMd op target rhs source (by rw [h_node])
  | .Var (.Field target fieldName) =>
    Synth.varField exprMd target fieldName source (by rw [h_node])
  -- (Decl-Synth) `var x := e`: a sole unannotated declaration target with an
  -- initializer is handled specially so the binding's type is recovered from
  -- the synthesized RHS. All other assignment shapes go to `Synth.assign`.
  | .Assign [⟨.Declare ⟨name, none⟩, vs⟩] value =>
    Synth.declInfer exprMd name vs value source (by rw [h_node])
  | .Assign targets value =>
    Synth.assign exprMd targets value source (by rw [h_node])
  | .PureFieldUpdate target fieldName newVal =>
    Synth.pureFieldUpdate exprMd target fieldName newVal (by rw [h_node])
  | .StaticCall callee args =>
    Synth.staticCall exprMd callee args source (by rw [h_node])
  | .New ref typeArgs => Synth.new ref typeArgs source
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
  | .Assert condExpr summary => do
    let r ← Check.assert exprMd condExpr summary source (by rw [h_node])
    return (r, ⟨ .TVoid, source ⟩)
  | .Assume cond => do
    let r ← Check.assume exprMd cond source (by rw [h_node])
    return (r, ⟨ .TVoid, source ⟩)
  | .Throw value => do
    let r ← Check.throw exprMd value source (by rw [h_node])
    return (r, ⟨ .TVoid, source ⟩)
  | .Try body catches finally? => do
    let r ← Check.tryCatch exprMd body catches finally? source (by rw [h_node])
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
  -- (Decl-Synth, check mode) sole unannotated initialized declaration —
  -- see `Synth.resolveStmtExpr`.
  | .Assign [⟨.Declare ⟨name, none⟩, vs⟩] value =>
    Check.declInfer exprMd name vs value expected source (by rw [h_node])
  | .Assign targets value =>
    Check.assign exprMd targets value expected source (by rw [h_node])
  | .Hole det none => pure (Check.holeNone det expected source)
  | .Hole det (some ty) => Check.holeSome det ty expected source
  | .Old val =>
    Check.old exprMd val expected source (by rw [h_node])
  | .ProveBy val proof =>
    Check.proveBy exprMd val proof expected source (by rw [h_node])
  | _ =>
    -- Subsumption fallback `[⇐] Sub`: synth, then check `actual <: expected` AND
    -- realize the coercion witness onto the term. This chokepoint covers call
    -- arguments, return values, functional bodies, and primitive-op subsumption —
    -- every check-mode boundary without a bespoke rule funnels here.
    let (e', actual) ← Synth.resolveStmtExpr exprMd
    -- Truthiness (bool context): when the slot expects `TBool` but the actual type is not
    -- bool-coercible by `coerce`, apply the caller's `toBool` hook. Truthiness is a
    -- boolean-context coercion, not subtyping, so it is deliberately not part of `coerce`; the
    -- hook fires only here, where the slot is known to be bool. Otherwise fall back to the
    -- normal subsumption.
    let ctx ← (do pure (← get).typeLattice)
    -- Refl-gate for the truthiness hook: fire `toBool` when the slot is `TBool`, the actual is
    -- not already bool, and `coerce` yields either no witness (there is no `int <: bool`) or only
    -- a spurious gradual `refl` — i.e. a gradual-registered `UserDefined` that the gradual-top
    -- fallback declares consistent-with-bool, which would otherwise let the raw value land in the bool
    -- slot. A real `inject`/`project`/`upcast` witness (e.g. `Any → bool`) is not diverted: it
    -- flows through `coerceTo`. Truthiness is a boolean-context coercion, not subtyping.
    --
    -- The "not already bool" clause is load-bearing and tested against the UNFOLDED actual:
    -- `coerce TBool TBool` returns `some .refl` (via `highEq`), so without this guard an operand
    -- that is already `bool` (or a phantom `UserDefined "bool"` that `unfold` canonicalizes to
    -- `TBool`) would spuriously route through `toBool` and get wrapped in a redundant truthiness
    -- call whenever a frontend installs the hook. Native Laurel (`toBool = none`) is unaffected
    -- either way, but the Python frontend's `Any_to_bool` must not double-wrap native `bool`s.
    let actualStripped := stripTrailingErrors actual
    let fireToBool := expected.val == .TBool &&
      (ctx.unfold actualStripped).val != .TBool &&
      (match coerce ctx actualStripped expected with | none => true | some .refl => true | _ => false)
    if fireToBool then
      match ctx.toBool with
      | some mk => pure (mk actualStripped.val e')
      | none => coerceTo source expected actual e'
    else
      coerceTo source expected actual e'
  termination_by (exprMd, 3)
  decreasing_by all_goals first
    | (apply Prod.Lex.left; term_by_mem)
    | (try subst_eqs; apply Prod.Lex.right; decide)
    | (try subst h_node; apply Prod.Lex.right; decide)
    | (apply Prod.Lex.right; decide)

-- ### Literals

/-- `Γ ⊢ LiteralInt n ⇒ TInt` -/
def Synth.litInt (v : Int) (source : FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralInt v, { val := .TInt, source := source })

/-- `Γ ⊢ LiteralBool b ⇒ TBool` -/
def Synth.litBool (v : Bool) (source : FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralBool v, { val := .TBool, source := source })

/-- `Γ ⊢ LiteralString s ⇒ TString` -/
def Synth.litString (v : String) (source : FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralString v, { val := .TString, source := source })

/-- `Γ ⊢ LiteralDecimal d ⇒ TReal` -/
def Synth.litDecimal (v : StrataDDM.Decimal) (source : FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralDecimal v, { val := .TReal, source := source })

/-- `Γ ⊢ LiteralBv v (width := n) ⇒ TBv n` — a bitvector literal's type is
    fixed by its declared width. -/
def Synth.litBv (v : Nat) (width : Nat) (source : FileRange) : StmtExpr × HighTypeMd :=
  (.LiteralBv v width, { val := .TBv width, source := source })

-- ### Variables

/-- (Var-Local)
    ```
    Γ(x) = T
    ──────────────────────
    Γ ⊢ Var (.Local x) ⇒ T
    ```
    Resolves `ref` against the lexical scope and reads its declared type. -/
def Synth.varLocal (ref : Identifier) (source : FileRange) :
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
    (target : StmtExprMd) (fieldName : Identifier) (source : FileRange)
    (h : exprMd.val = .Var (.Field target fieldName)) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', holderTy) ← Synth.resolveStmtExpr target
  let fieldName' ← resolveFieldRef target' fieldName source (holderTy? := holderTy)
  -- Concretize the field's `.TVar` against the holder's instantiation. `holderTy` is
  -- the synthesized holder type — already concretized for a nested `g#inner` because
  -- that read came through this same rule — so chains concretize transitively.
  let ty ← concretizeFieldType holderTy fieldName'
  pure (.Var (.Field target' fieldName'), ty)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    term_by_mem

/-- (Var-Declare)
    ```
    x ∉ dom(Γ)                                       (annotated, type = some T_x)
    ────────────────────────────────────────────────────
    Γ ⊢ Var (.Declare x (some T_x)) ⇒ TVoid ⊣ Γ, x : T_x

    x ∉ dom(Γ)                                       (Var-Declare-Infer, type = none)
    ────────────────────────────────────────────────────
    Γ ⊢ Var (.Declare x none) ⇒ TVoid ⊣ Γ, x : Unknown
    ```
    `⊣ Γ, x : T_x` records that the surrounding scope is extended with
    the new binding for the remainder of the enclosing block. The
    declaration itself does no work other than registering `x : T_x`,
    and yields no value, so it synthesizes `TVoid`.

    When the annotation is absent (`type = none`, i.e. surface `var x`),
    there is *neither* an annotation *nor* an initializer to read a type
    from — `var x := e` is handled in `Synth.declInfer`/`Check.declInfer` by
    synthesizing `e` — so this rule emits a "cannot infer a type"
    diagnostic (binding `x : Unknown`, so that later uses of `x` do not
    cascade further type errors). Either way the node is rewritten to a
    fully-typed `Declare x (some T)`, so no `none` annotation survives
    resolution.

    `x ∉ dom(Γ)` is a soft side condition, not a hard premise: when `x`
    is already bound in the current scope, `defineNameCheckDup` emits a
    `"Duplicate definition '<x>' is already defined in this scope"`
    diagnostic and still extends the scope — but with an *unresolved*
    placeholder rather than `x : T_x`, so later uses of `x` do not
    cascade further type errors. -/
def Check.varDeclare (param : Parameter?) (source : FileRange) :
    ResolveM StmtExprMd := do
  let ty' ← match param.type with
    | some ty => resolveHighType ty
    | none =>
      let unknown : HighTypeMd := { val := .Unknown, source := source }
      typeMismatch source none
        s!"cannot infer a type for '{param.name.text}': a declaration with neither a type annotation nor an initializer has no type to read off; add an annotation (`var {param.name.text} : T`) or an initializer (`var {param.name.text} := e`)"
        unknown
      pure unknown
  let name' ← defineNameCheckDup param.name (.var param.name ty')
  pure { val := .Var (.Declare ⟨name', some ty'⟩), source := source }

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
    (source : FileRange)
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
def Check.exit (target : String) (source : FileRange) :
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
    (val : Option StmtExprMd) (source : FileRange)
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
def Synth.emptyBlock (source : FileRange) : HighTypeMd :=
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
    (expected : HighTypeMd) (source : FileRange)
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
      let nextSource : FileRange :=
        match init'[i + 1]? with
        | some next => next.source
        | none      => (stmts.getLast?.map (·.source)).getD source
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
    propagates through nested `Block` / `IfThenElse` / `Hole`
    constructs that have their own check rules.

    Without an `else`, the implicit branch is an empty block of type
    `TVoid`, so the rule degenerates to require `TVoid <: T` — the
    standard \[⇐\] Sub boundary check that `Resolution.Synth.emptyBlock`
    composes with for an empty block. -/
def Check.ifThenElse (exprMd : StmtExprMd)
    (cond thenBr : StmtExprMd) (elseBr : Option StmtExprMd)
    (expected : HighTypeMd) (source : FileRange)
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
    a gradual corner where `join` is `none`, for which the result
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
    (source : FileRange)
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
    -- A branch ending in a heap-threading assign synthesizes the plumbing type `Heap`, while a
    -- sibling branch with no field-write stays `void`. These are not incompatible: in statement
    -- position both branches run for effect, and the `Heap` value is the threaded heap, not a
    -- user value. Treat `Heap` as void-like for this join only (not the shared `isVoidLikeHT`,
    -- which gates coercion).
    let isStmtBranchTy (t : HighType) : Bool :=
      isVoidLikeHT t || (match t with | .UserDefined id => id.text == "Heap" | _ => false)
    let ty ←
      -- Primary: the shared `join` (handles Unknown/TVoid/equal — e.g. an `int`/`void`
      -- branch pair joins to `void`). Fallback: the frontend tolerances an `.err`-grade
      -- `(T, Error)` body or a heap-threading branch needs (strip trailing Error; treat
      -- Heap as void-like for this join only).
      match join ctx thenTy elseTy with
      | some joined => pure joined
      | none =>
        if isConsistent ctx (stripTrailingErrors thenTy) (stripTrailingErrors elseTy) ||
            isVoidLikeHT (stripTrailingErrors thenTy).val && isVoidLikeHT (stripTrailingErrors elseTy).val ||
            isStmtBranchTy (stripTrailingErrors thenTy).val && isStmtBranchTy (stripTrailingErrors elseTy).val then
          pure ((join ctx (stripTrailingErrors thenTy) (stripTrailingErrors elseTy)).getD (stripTrailingErrors thenTy))
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
    (source : FileRange)
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
      let nextSource : FileRange :=
        match init'[i + 1]? with
        | some next => next.source
        | none      => (stmts.getLast?.map (·.source)).getD source
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
    (condExpr : StmtExprMd) (summary : Option String)
    (source : FileRange)
    (h : exprMd.val = .Assert condExpr summary) :
    ResolveM StmtExprMd := do
  let cond' ← Check.resolveStmtExpr condExpr { val := .TBool, source := condExpr.source }
  pure { val := .Assert cond' summary, source := source }
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
    (cond : StmtExprMd) (source : FileRange)
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

/-- (Throw)
    ```
    Γ ⊢ value ⇒ T
    ──────────────────────────────────
    Γ ⊢ Throw value ⇒ TVoid
    ```
    `throw`'s operand is only synthesized: there is no synthesized exception
    root, so a `throw` places no upper bound on its operand's type. The thrown
    types are instead reconciled at each enclosing `catch` binding or a `throwsOn` case, whose
    binding is typed at the least common ancestor of everything that can reach
    it (see `Check.tryCatch`). `throw` is a statement: it yields no value, so it
    synthesizes `TVoid`. -/
def Check.throw (exprMd : StmtExprMd)
    (value : StmtExprMd) (source : FileRange)
    (h : exprMd.val = .Throw value) :
    ResolveM StmtExprMd := do
  -- There is no synthesized exception root, so `throw` places no upper bound on
  -- its operand's type; the thrown types are reconciled at each enclosing
  -- `catch` binding or a `throwsOn` case by typing the binding at their least common ancestor.
  -- `throw` is a statement (yields `TVoid`).
  let (value', _) ← Synth.resolveStmtExpr value
  pure { val := .Throw value', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    simp only [StmtExpr.Throw.sizeOf_spec] at hsz
    omega

/-- (Try)
    The `try` body, each `catch` body, and the `finally` arm are statements
    (checked in statement position, against `Unknown`). Each `catch` clause
    opens a fresh scope in which its binding is bound to the caught value, typed
    at the least common ancestor of the exception types thrown in the body (see
    the body below); the optional guard predicate is checked against
    `TBool`. `try` is a statement: it synthesizes `TVoid`. See the
    Exceptions section of the Laurel User Guide. -/
def Check.tryCatch (exprMd : StmtExprMd)
    (body : StmtExprMd) (catches : List CatchClause) (finally? : Option StmtExprMd)
    (source : FileRange)
    (h : exprMd.val = .Try body catches finally?) :
    ResolveM StmtExprMd := do
  let body' ← Check.resolveStmtExpr body { val := .Unknown, source := body.source }
  -- Type each catch binding at the least common ancestor of the exception types
  -- that can reach it — the operand types of direct `throw`s plus the declared
  -- `throws` of procedures called in the body. `e#field` then type-checks
  -- against the shared supertype without a downcast, so a front end can use its
  -- own exception hierarchy directly. A non-empty set with no common ancestor
  -- (or an ambiguous join under multiple inheritance) is a hard error; an
  -- undeterminable/empty set falls back to `Unknown` (gradual).
  let thrownNames ← collectThrownTypeNames {} body
  let bindTy : HighTypeMd ← match thrownNames with
    | [] => pure { val := .Unknown, source := body.source }
    | _ =>
      match (← get).typeLattice.commonAncestor thrownNames with
      | some anc => resolveHighType { val := .UserDefined (mkId anc), source := source }
      | none =>
        let names := ", ".intercalate thrownNames.eraseDups
        modify fun s => { s with errors := s.errors.push (diagnosticFromSource source
          s!"the exception types thrown in this `try` block ({names}) have no common ancestor; a `catch` binding needs a single least-common-ancestor type") }
        pure { val := .Unknown, source := body.source }
  let catches' ← catches.attach.mapM fun ⟨c, _⟩ => withScope do
    let binding' ← defineNameCheckDup c.binding (.var c.binding bindTy)
    let predicate' ← c.predicate.attach.mapM fun ⟨p, _⟩ =>
      Check.resolveStmtExpr p { val := .TBool, source := p.source }
    let cbody' ← Check.resolveStmtExpr c.body { val := .Unknown, source := c.body.source }
    pure ({ binding := binding', predicate := predicate', body := cbody', bindingType := bindTy } : CatchClause)
  let finally'? ← finally?.attach.mapM fun ⟨fexpr, _⟩ =>
    Check.resolveStmtExpr fexpr { val := .Unknown, source := fexpr.source }
  pure { val := .Try body' catches' finally'?, source := source }
  termination_by (exprMd, 0)
  decreasing_by
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      rw [h] at hsz
      simp only [StmtExpr.Try.sizeOf_spec] at hsz
      try (have := List.sizeOf_lt_of_mem ‹_ ∈ catches›)
      try (have := CatchClause.sizeOf_body_lt ‹_›)
      try (have hpr := CatchClause.sizeOf_predicate_lt ‹_›)
      try (rw [Option.mem_def.mp ‹_ ∈ c.predicate›, Option.some.sizeOf_spec] at hpr)
      try (rw [Option.mem_def.mp ‹_ ∈ finally?›, Option.some.sizeOf_spec] at hsz)
      omega

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
    (targets : List VariableMd) (value : StmtExprMd) (source : FileRange)
    (h : exprMd.val = .Assign targets value) :
    ResolveM (StmtExpr × HighTypeMd) := do
  -- (Decl-Synth over multi-assign) A sole unannotated initialized declaration
  -- (`var x := e`) is routed to `Synth.declInfer` by the dispatcher *before*
  -- reaching here, so an unannotated `Declare` here comes from a multi-target
  -- `assign var x, y, var z := call()`. In that case the RHS is synthesized
  -- *first* and each unannotated target adopts its corresponding component of
  -- the synthesized tuple (the callee's declared output); the RHS/target
  -- compatibility is then enforced by a tuple-level Sub check at the end
  -- instead of the usual push-in.
  let inferInfo ← if targets.any (fun t => t.val matches .Declare ⟨_, none⟩) then
      some <$> Synth.resolveStmtExpr value
    else pure none
  let (compTys, arityError) ← componentTypes targets inferInfo
  -- Resolve each target AND its type in one pass: a `.Field` target's holder type
  -- is the synth result of resolving its receiver (`Synth.resolveStmtExpr`, the
  -- authoritative synthesizer), so the field type is concretized against it directly
  -- rather than re-derived by a separate, weaker pass.
  let targetsWithTy ← (targets.attach.zip compTys).mapM fun (⟨v, hv⟩, compTy) => do
    have := hv
    let ⟨vv, vs⟩ := v
    match vv with
    | .Local ref =>
      let ref' ← resolveRef ref source
      pure ((⟨.Local ref', vs⟩ : VariableMd), ← getVarType ref)
    | .Field target fieldName =>
      let (target', holderTy) ← Synth.resolveStmtExpr target
      let fieldName' ← resolveFieldRef target' fieldName source (holderTy? := holderTy)
      pure ((⟨.Field target' fieldName', vs⟩ : VariableMd), ← concretizeFieldType holderTy fieldName')
    | .Declare param =>
      let ty' ← match param.type with
        | some ty => resolveHighType ty
        | none =>
          -- Unannotated multi-assign target: adopt the RHS component type.
          -- When the RHS provides no matching component (arity mismatch, or a
          -- non-multi-valued RHS), bind `Unknown` — `componentTypes` or the
          -- tuple check below reports the single mismatch diagnostic, and the
          -- gradual binding suppresses cascades on later uses.
          match compTy with
          | some t => declInferValueType param.name vs t
          | none => pure { val := .Unknown, source := vs }
      let name' ← defineNameCheckDup param.name (.var param.name ty')
      pure ((⟨.Declare ⟨name', some ty'⟩, vs⟩ : VariableMd), ty')
  let targets' := targetsWithTy.map (·.1)
  let targetTys := targetsWithTy.map (·.2)
  let expectedTy : HighTypeMd := match targetTys with
    | [single] => single
    | _        => { val := .MultiValuedExpr targetTys, source := source }
  match inferInfo with
  | some (value', valueTy) =>
    -- RHS already synthesized for inference; enforce the boundary tuple-wise
    -- (unless `componentTypes` already reported an arity mismatch, which the
    -- tuple check would only restate against the `Unknown` fallback bindings).
    unless arityError do
      checkSubtype value'.source expectedTy valueTy
    pure (.Assign targets' value', expectedTy)
  | none =>
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
    (expected : HighTypeMd) (source : FileRange)
    (h : exprMd.val = .Assign targets value) : ResolveM StmtExprMd := do
  -- Reuse `Synth.assign` for the target/value/expectedTy work (identical), then add the
  -- [⇐] Sub boundary check. The call is on the SAME `exprMd`, so termination is by the
  -- lexicographic tag (2 > 1 = Synth.assign's), not a subterm decrease.
  let (synthExpr, expectedTy) ← Synth.assign exprMd targets value source h
  unless expected.val matches .TVoid do
    checkSubtype source expected expectedTy
  pure { val := synthExpr, source := source }
  termination_by (exprMd, 2)
  decreasing_by
    all_goals (apply Prod.Lex.right; omega)

/-- (Decl-Synth, synth mode)
    ```
    x ∉ dom(Γ)    Γ ⊢ e ⇒ T
    ──────────────────────────────────────────────
    Γ ⊢ (var x := e) ⇒ T ⊣ Γ, x : T
    ```
    `var x := e`, an *unannotated* declaration (`Declare x none`) with an
    initializer. With no annotation to push into the RHS, we *synthesize* the
    initializer's type `T` and adopt it for the binding. The node is rewritten
    to `Assign [⟨.Declare x (some T)⟩] e`, so no `none` annotation survives
    resolution. This rule handles the sole-target form; unannotated declared
    targets of a *multi-target* `assign var x, y := call()` are recovered
    component-wise inside `Synth.assign`/`Check.assign`. The synthesized type
    is `T`, matching `Synth.assign`'s single-target case.

    Scoping: the initializer is synthesized *before* `defineNameCheckDup`
    introduces the binding, so `e` cannot see the `x` being declared — a
    self-referential `var x := x + 1` reports "'x' is not defined" (or reads
    an outer `x` if one is in scope). This is asymmetric with the *annotated*
    path, which resolves targets first: `var x : int := x + 1` accepts the
    self-reference, reading the fresh (uninitialized) binding. Pinned by
    `selfRefNoOuter`/`selfRefOuterShadow` in `ResolutionTypeCheckTests`. -/
def Synth.declInfer (exprMd : StmtExprMd)
    (name : Identifier) (vs : FileRange) (value : StmtExprMd)
    (source : FileRange)
    (h : exprMd.val = .Assign [⟨.Declare ⟨name, none⟩, vs⟩] value) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (value', valueTy) ← Synth.resolveStmtExpr value
  let bindTy ← declInferValueType name value'.source valueTy
  let name' ← defineNameCheckDup name (.var name bindTy)
  pure (.Assign [⟨.Declare ⟨name', some bindTy⟩, vs⟩] value', bindTy)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    simp only [StmtExpr.Assign.sizeOf_spec] at hsz
    omega

/-- (Decl-Synth, check mode) `var x := e` (`Declare x none` with initializer)
    where a type `A` is expected (e.g. as the value-producing last statement of
    a checked block). Synthesizes the initializer's type and adopts it for the
    binding (see `Synth.declInfer`), then runs the standard \[⇐\] Sub boundary
    check `T <: A` against the surrounding `expected` — *unless* `A = TVoid`
    (statement position), exactly as in `Check.assign`. -/
def Check.declInfer (exprMd : StmtExprMd)
    (name : Identifier) (vs : FileRange) (value : StmtExprMd)
    (expected : HighTypeMd) (source : FileRange)
    (h : exprMd.val = .Assign [⟨.Declare ⟨name, none⟩, vs⟩] value) :
    ResolveM StmtExprMd := do
  let (value', valueTy) ← Synth.resolveStmtExpr value
  let bindTy ← declInferValueType name value'.source valueTy
  let name' ← defineNameCheckDup name (.var name bindTy)
  unless expected.val matches .TVoid do
    checkSubtype source expected bindTy
  pure { val := .Assign [⟨.Declare ⟨name', some bindTy⟩, vs⟩] value', source := source }
  termination_by (exprMd, 0)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    simp only [StmtExpr.Assign.sizeOf_spec] at hsz
    omega

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
    from the later `EliminateIncrDecrAndCompoundAssign` lowering. Used in expression position
    (`var y := ++x`, `if x++ > 0`, `f(x++)`); in statement position the
    yielded value is discarded by `Check.statement`. -/
def Synth.incrDecr (exprMd : StmtExprMd)
    (mode : IncrDecrMode) (op : IncrDecrOp) (target : VariableMd)
    (source : FileRange)
    (h : exprMd.val = .IncrDecr mode op target) :
    ResolveM (StmtExpr × HighTypeMd) := do
  -- Resolve the target and compute its (concretized) type together, so a `.Field`
  -- target's holder type comes from the authoritative synthesizer.
  let (target', resultTy) ← match h_tgt : target.val with
    | .Local ref =>
      let ref' ← resolveRef ref source
      pure ((⟨.Local ref', target.source⟩ : VariableMd), ← getVarType ref)
    | .Field tgt fieldName =>
      let (tgt', holderTy) ← Synth.resolveStmtExpr tgt
      let fieldName' ← resolveFieldRef tgt' fieldName source (holderTy? := holderTy)
      pure ((⟨.Field tgt' fieldName', target.source⟩ : VariableMd), ← concretizeFieldType holderTy fieldName')
    | .Declare param =>
      -- Should not occur — the translator rejects a declaration target;
      -- treat conservatively by resolving its type only.
      let ty' ← match param.type with
        | some ty => resolveHighType ty
        | none => pure { val := .Unknown, source := target.source }
      pure ((⟨.Declare ⟨param.name, some ty'⟩, target.source⟩ : VariableMd), ty')
  checkIncrDecrTargetType op target' source
  pure (.IncrDecr mode op target', resultTy)
  termination_by (exprMd, 1)
  decreasing_by
    apply Prod.Lex.left
    have hsz := exprMd.sizeOf_val_lt
    rw [h] at hsz
    have hsz2 := target.sizeOf_val_lt
    rw [h_tgt] at hsz2
    term_by_mem

/-- (CompoundAssign)
    ```
    Γ ⊢ target ⇒ T    T accepts op    Γ ⊢ rhs ⇐ T
    ─────────────────────────────────────────────
    Γ ⊢ CompoundAssign op target rhs ⇒ T
    ```
    `x op= e` reads and writes its target, so it synthesizes the target's own type
    `T` and checks the RHS against it. Reviewable by analogy to two existing rules:
    target resolution is identical to `Synth.incrDecr` (including the conservative
    `.Declare` arm — unlike `Synth.assign`, the target is never *introduced*, so no
    `defineNameCheckDup`); the RHS is then checked against the single target type with
    `Check.resolveStmtExpr`, as `Synth.assign` does for its (here always single) target.
    The element type is checked by `checkCompoundAssignTargetType`. Used in expression
    position (`var y := (x += 2)`); in statement position the value is discarded by
    `Check.statement`. -/
def Synth.compoundAssign (exprMd : StmtExprMd)
    (op : Operation) (target : VariableMd) (rhs : StmtExprMd)
    (source : FileRange)
    (h : exprMd.val = .CompoundAssign op target rhs) :
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
      let ty' ← match param.type with
        | some ty => resolveHighType ty
        | none => pure { val := .Unknown, source := target.source }
      pure (⟨.Declare ⟨param.name, some ty'⟩, target.source⟩ : VariableMd)
  checkCompoundAssignTargetType op target' source
  let resultTy ← match target'.val with
    | .Local ref => getVarType ref
    | .Declare param => pure (param.type.getD { val := .Unknown, source := target.source })
    | .Field _ fieldName => getVarType fieldName
  let rhs' ← Check.resolveStmtExpr rhs resultTy
  pure (.CompoundAssign op target' rhs', resultTy)
  termination_by (exprMd, 1)
  decreasing_by
    -- Two recursive calls, two obligations. `Check rhs` (rhs is a direct subterm)
    -- needs only the CompoundAssign step; `Synth tgt` (the `.Field` arm, where `tgt`
    -- is nested inside `target`) also needs the `target` step — hence the `try`.
    -- This is `Synth.incrDecr`'s proof generalised with `all_goals` to also cover
    -- the rhs obligation, using mainline's `term_by_mem` to close.
    all_goals
      apply Prod.Lex.left
      have hsz := exprMd.sizeOf_val_lt
      rw [h] at hsz
      try (have hsz2 := target.sizeOf_val_lt
           rw [h_tgt] at hsz2)
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
    (callee : Identifier) (args : List StmtExprMd) (source : FileRange)
    (h : exprMd.val = .StaticCall callee args) :
    ResolveM (StmtExpr × HighTypeMd) := do

  -- Overload-failure marker: `UniqueOverloadNames` rewrites failed call sites to
  -- this reserved prefix. Resolve arguments (so errors inside them still surface),
  -- then return Unknown silently — the real diagnostic was already emitted.
  if callee.text.startsWith overloadFailurePrefix then
    let args' ← args.attach.mapM (fun ⟨a, hMem⟩ => do
      have := hMem
      Prod.fst <$> Synth.resolveStmtExpr a)
    return (.StaticCall { callee with uniqueId := none } args',
            { val := .Unknown, source := callee.source })

  -- Equality is polymorphic, but Laurel has no polymorphic types, so the `$eq` /
  -- `$neq` wrappers are declared over placeholder `int` parameters. Checking
  -- arguments against that signature would reject every comparison of anything
  -- but an int — including the `Box` / `Composite` / `Field` / `Map` comparisons
  -- that `ModifiesClauses` builds. So instead of the usual argument check,
  -- require only that the two operand types are *consistent* (`~`, the symmetric
  -- gradual relation, under which `Unknown` matches anything), and give the call
  -- type `TBool`. Equality therefore has no privileged operand direction.
  if callee.text == Operation.Eq.procName || callee.text == Operation.Neq.procName then
    -- Report as the operator the user wrote (`==` / `!=`), not the wrapper name.
    let opName := if callee.text == Operation.Eq.procName then "==" else "!="
    let callee' ← resolveRef callee source
    let resolved ← args.attach.mapM (fun ⟨a, hMem⟩ => do
      have := hMem
      Synth.resolveStmtExpr a)
    let args' := resolved.map (·.1)
    let argTys := resolved.map (·.2)
    let boolTy : HighTypeMd := { val := .TBool, source := source }
    -- A `MultiValuedExpr` operand is a multi-output call used in value position.
    -- It is an internal pseudo-type with no Core lowering, so it must never
    -- reach an operand slot — letting it through crashes a later pass as a
    -- `StrataBug`. Report it per operand and skip the consistency check, whose
    -- diagnostic would only cascade.
    let mut hasMulti := false
    for (a, aTy) in args'.zip argTys do
      if aTy.val matches .MultiValuedExpr _ then
        let diag := diagnosticFromSource a.source
          "multi-output call cannot be used as a value here; it returns multiple values. Unpack it into separate variables first"
        modify fun s => { s with errors := s.errors.push diag }
        hasMulti := true
    if hasMulti then
      return (.StaticCall callee' args', boolTy)
    match argTys with
    | [lhsTy, rhsTy] =>
      let ctx := (← get).typeLattice
      -- `TVoid ~ TVoid` holds in `isConsistent` (it is `highEq` on equal
      -- constructors), but a void expression carries no value to compare,
      -- so a void operand is rejected even when both sides agree.
      let voidOperand :=
        lhsTy.val matches .TVoid || rhsTy.val matches .TVoid
      if voidOperand || !isConsistent ctx lhsTy rhsTy then
        let diag := diagnosticFromSource source
          s!"cannot compare '{formatType lhsTy}' with '{formatType rhsTy}' using '{opName}'"
        modify fun s => { s with errors := s.errors.push diag }
    | _ => pure ()
    return (.StaticCall callee' args', boolTy)

  -- The map primitives `select`/`update`/`const` carry concrete `int` placeholder
  -- signatures (see `CoreDefinitionsForLaurel`), not type parameters, so they can't be
  -- checked against those signatures. Instead, infer the result type structurally from
  -- the resolved arguments, keeping a concrete `HighType` flowing into Core:
  --   * `select(map, key)`     ⇒ the map's value type
  --   * `update(map, key, val)` ⇒ the map type itself
  --   * `mapConst(val)`        ⇒ `Map _ (typeof val)` (key type is not recoverable)
  if callee.text == "select" || callee.text == "update" || callee.text == "mapConst" then
    let callee' ← resolveRef callee source
    let resolved ← args.attach.mapM (fun ⟨a, hMem⟩ => do
      have := hMem
      Synth.resolveStmtExpr a)
    let args' := resolved.map (·.1)
    let argTys := resolved.map (·.2)
    let resultTy : HighTypeMd ←
      match callee.text, argTys with
      | "select", mapTy :: _ =>
        match mapTy.val with
        | .TMap _ valueTy => pure valueTy
        | _ => pure ⟨ .Unknown, source ⟩
      | "update", mapTy :: _ => pure mapTy
      -- `mapConst(val) : Map _ val` — the key type is genuinely not recoverable from
      -- the single value argument, so the key is the gradual `Unknown` (the dynamic
      -- type, consistent with any concrete key). The result flows into a declared
      -- `Map K V` binding (`Unknown ~ K`) while value strictness is preserved
      -- (`Map _ bool` vs `Map int int` still fails on the value leaf). A fabricated
      -- concrete key (e.g. `TypeTag`) would be rejected against the declared key —
      -- `.UserDefined` is a strict participant in the consistency relation. The
      -- Core-side key annotation is recovered separately from the binding's declared
      -- type in `LaurelToCoreSchemaPass` (`expectedType`), defaulting to `TypeTag`.
      | "mapConst", valTy :: _ => pure ⟨ .TMap ⟨.Unknown, source⟩ valTy, source ⟩
      | _, _ => pure ⟨ .Unknown, source ⟩
    return (.StaticCall callee' args', resultTy)

  -- Overloaded static procedure: more than one procedure is registered under
  -- this name. The flat `scope` only remembers the last one, so the normal
  -- single-definition path below can't pick the right one. Instead synthesize
  -- the argument types once and collect every overload whose parameters accept
  -- them (`selectOverloads`):
  --   * exactly one match  → the resolved callee, stamped with its own id;
  --   * no match           → "no overload matches" error;
  --   * two or more matches → an ambiguous call. Registration only rejects
  --     pairwise-overlapping signatures, which does not preclude a call that
  --     matches two non-overlapping overloads (a common descendant under
  --     multiple inheritance, or a gradual `Unknown` argument that matches
  --     all). Rather than silently pick the first declaration, this is
  --     reported so the ambiguity is visible at the call site.
  -- A non-overloaded name has at most one candidate and falls through.
  let candidates := (← get).overloads.getD callee.text []
  if candidates.length > 1 then
    let resolved ← args.attach.mapM (fun ⟨a, hMem⟩ => do
      have := hMem
      Synth.resolveStmtExpr a)
    let args' := resolved.map (·.1)
    let argTys := resolved.map (·.2)
    let ctx := (← get).typeLattice
    -- An argument may synthesize to `.Unknown` (an untyped hole `<?>`, an
    -- undefined identifier, an `if`-`then`-`else` whose branches are Unknown,
    -- …). `.Unknown` is a consistent subtype of every parameter type, so it
    -- cannot *discriminate* between overloads — but the other arguments still
    -- can. So we always run the selection and only treat an unresolved result as
    -- benign when an `Unknown` argument is what made it unresolved: reporting
    -- "no overload matches" / "ambiguous call" there would be a spurious error
    -- stacked on top of (or masking) the argument's own real error.
    --
    -- Selecting on the informative arguments alone is what lets `1 + <?>` still
    -- resolve to the `int` overload of `$add` — which in turn lets
    -- `InferHoleTypes` read that overload's parameter types and give the hole a
    -- type instead of leaving it `Unknown`.
    --
    -- Suppression has to ask whether the `Unknown` is *why* selection failed, not
    -- merely whether one is present. A concrete argument that no candidate accepts
    -- rules out every overload on its own, and it does so whether or not a hole
    -- sits beside it: blaming the hole there hides the operand that is actually
    -- wrong. `1 + <?>` stays silent because `1` is accepted by the `int` overload,
    -- so no argument is individually to blame; `<?> + "hello"` reports, because
    -- `"hello"` is rejected by every overload of `$add`.
    let hasUnknownArg := argTys.any (·.val matches .Unknown)
    let culpritArg : Bool :=
      (argTys.zipIdx.any fun (argTy, i) =>
        !(argTy.val matches .Unknown) &&
        candidates.all fun (_, proc) =>
          match proc.inputs[i]? with
          | some p => !isConsistentSubtype ctx argTy p.type
          -- An arity mismatch is not this argument's fault; leave the blame to
          -- another position (or to `hasUnknownArg` if there is none).
          | none => false)
    -- Stay quiet only when a hole is present *and* no concrete argument is to
    -- blame — then the argument's own diagnostic already covers the failure.
    let suppressDiagnostic := hasUnknownArg && !culpritArg
    match selectOverloads ctx candidates argTys with
    | [(id, proc)] =>
      let callee' := { callee with uniqueId := some id }
      return (.StaticCall callee' args', procReturnType callee proc)
    | [] =>
      unless suppressDiagnostic do
        let diag := diagnosticFromSource source
          s!"no overload of '{callee}' matches the argument types"
        modify fun s => { s with errors := s.errors.push diag }
      return (.StaticCall { callee with uniqueId := none } args',
              { val := .Unknown, source := callee.source })
    | _ =>
      -- Genuinely ambiguous. When an `Unknown` argument is the reason several
      -- overloads still match, that is not a user-visible ambiguity — it is
      -- missing information — so report nothing and degrade to `Unknown`, as
      -- the single-definition path does.
      unless suppressDiagnostic do
        let diag := diagnosticFromSource source
          s!"ambiguous call to '{callee}': the argument types match more than one overload"
        modify fun s => { s with errors := s.errors.push diag }
      return (.StaticCall { callee with uniqueId := none } args',
              { val := .Unknown, source := callee.source })

  let callee' ← resolveRef callee source
    (expected := #[.parameter, .staticProcedure, .datatypeConstructor, .datatypeDestructor, .constant])
  let (retTy, paramTypes) ← getCallInfo callee
  -- A datatype constructor call is type-checked here, at resolution time, rather
  -- than deferred to Core: each argument is checked against its declared field
  -- type. `getCallInfo` reports no parameter types for a constructor (its result
  -- is the datatype itself), so the field types are read off the constructor's
  -- own node. The one slot that cannot be checked is a field whose type is one of
  -- the datatype's type parameters: that is a genuine (erased) type variable,
  -- satisfied by an argument of any type, so there is nothing to check against at
  -- the call site — the argument is synthesized but left unconstrained. Argument
  -- arity is checked in full. (A tester like `Foo..isBar` resolves to a
  -- `.staticProcedure`, never a `.datatypeConstructor`, so it takes the ordinary
  -- procedure path below.)
  let ctorNode? := (← get).scope.get? callee.text
  if let some (_, .datatypeConstructor typeName ctor) := ctorNode? then
    -- The datatype's own type parameters (empty for a non-generic datatype).
    let typeParams : List String := match (← get).scope.get? typeName.text with
      | some (_, .datatypeDefinition dt) => dt.typeArgs.map (·.text)
      | _ => []
    if args.length != ctor.args.length then
      let diag := diagnosticFromSource source
        s!"constructor '{callee}' expects {ctor.args.length} argument(s) but {args.length} were provided"
      modify fun s => { s with errors := s.errors.push diag }
    let ctx := (← get).typeLattice
    -- Pad with `Unknown` so a surplus argument (arity already reported) is still
    -- resolved — surfacing any error inside it; a missing one is dropped by `zip`.
    -- Each pad carries the surplus argument's own source, so any diagnostic from
    -- resolving it points at that argument.
    let fieldTys : List HighTypeMd :=
      ctor.args.map (·.type)
        ++ (args.drop ctor.args.length).map (fun a => { val := .Unknown, source := a.source })
    let args' ← (args.attach.zip fieldTys).mapM (fun (⟨a, hMem⟩, fieldTy) => do
      have := hMem
      -- A field is a *polymorphic slot* when its declared type mentions one of the
      -- datatype's own type parameters anywhere — `T`, but equally `Map int T` or
      -- `Option<T>`. The parameter is erased, so checking the argument against the
      -- declared type would compare a concrete instantiation against a phantom
      -- parameter and fail at every construction site; instead the argument is
      -- synthesized and the deep check is Core's. A field type with no parameter in
      -- it (a concrete primitive, constrained, composite, or closed generic
      -- application) is checked here as usual. See `mentionsTypeParam` for why the
      -- datatype's own `typeParams` list is the reliable source rather than a
      -- scope lookup at this call site.
      let isTypeParamSlot : Bool := mentionsTypeParam ctx typeParams fieldTy
      if isTypeParamSlot then
        let (a', _) ← Synth.resolveStmtExpr a
        pure a'
      else
        Check.resolveStmtExpr a fieldTy)
    return (.StaticCall callee' args', retTy)
  -- Surplus arguments (an arity error, reported below) have no declared
  -- parameter type. Pad with `.Unknown` carrying each surplus argument's own
  -- source, so diagnostics point at the offending argument.
  let expectedTys : List HighTypeMd :=
    paramTypes ++ (args.drop paramTypes.length).map (fun a => { val := .Unknown, source := a.source })
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
    (source : FileRange)
    (h : exprMd.val = .InstanceCall target callee args) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let (target', targetTy) ← Synth.resolveStmtExpr target
  -- An instance procedure is registered under the container-scoped key
  -- `TypeName$method` (see `preRegisterTopLevel` / `resolveInstanceProcedure`),
  -- matching the lifted top-level static procedure that `LiftInstanceProcedures`
  -- produces. Look the method up under that key, derived from the receiver's
  -- type; fall back to the bare callee name when the target's type can't be
  -- determined (an unresolved name, which already reported its own error).
  -- A legitimate `obj#method(…)` has a COMPOSITE receiver, so `targetTypeName` yields
  -- `some TypeName` and we look the method up under the container-scoped key `TypeName$method`
  -- (the lifted static proc). When it yields `none` the receiver is NOT a composite — either an
  -- already-errored target (type `.Unknown`, stay quiet — it reported its own error) or a
  -- resolved NON-composite (`z : int`), which has no methods. REJECT the latter: without this,
  -- the bare-`callee` fallback below would silently bind `z#sideEffect(…)` to an unrelated
  -- top-level static procedure `sideEffect`, and since `LiftInstanceProcedures`/`ContractPass`
  -- only handle `.InstanceCall` whose callee is an instance proc, the call's precondition is
  -- dropped and it mis-verifies (a silent unsound accept).
  let lookupKey ← match (← targetTypeName target') with
    | some tyName => pure (containerScopedName (mkId tyName) callee)
    | none =>
      unless targetTy.val matches .Unknown | .TVoid do
        modify fun s => { s with errors := s.errors.push (diagnosticFromSource source
          s!"'{callee.text}' is called with '#' on a non-composite receiver; instance-method calls require a composite receiver") }
      pure callee
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
  -- As in `Synth.staticCall`: pad surplus arguments with `.Unknown` carrying
  -- the argument's own source so diagnostics point at the offending argument.
  let expectedTys : List HighTypeMd :=
    callParamTypes
      ++ (args.drop callParamTypes.length).map (fun a => { val := .Unknown, source := a.source })
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
    `UserDefined ref` — or, for an explicit instantiation `new C<τ…>`, the
    applied type `Applied (UserDefined ref) [τ…]`, so the type checker and
    `MonomorphizeComposites` see the concrete instantiation (mirroring
    `computeExprType`'s `.New` arm). A bare `new C` carries no type args and
    keeps the plain `UserDefined` type. The `Unknown` fallback fires *only*
    when `ref` resolves to a present definition whose kind is neither
    composite nor datatype (e.g. a variable or procedure name); this
    suppresses cascading errors after the kind diagnostic has already fired.
    An *unresolved* `ref`, or one absent from scope, takes the `UserDefined`
    branch instead — `resolveRef` has already reported the name, so
    re-flagging it here would only duplicate that diagnostic. The explicit
    type args are resolved (so a `.TVar` inside is reclassified and a bad
    arg reported) and their count is checked against the composite's
    declared type-arg arity. -/
def Synth.new (ref : Identifier) (typeArgs : List HighTypeMd) (source : FileRange) :
    ResolveM (StmtExpr × HighTypeMd) := do
  let ref' ← resolveRef ref source
    (expected := #[.compositeType, .datatypeDefinition])
  -- Resolve explicit instantiation arguments (`new Box<int>`) so their type names
  -- get uniqueIds, exactly as `appliedType` does in type position. Empty for a
  -- bare `new C` (the common, pre-existing case).
  let typeArgs' ← typeArgs.mapM resolveHighType
  let s ← get
  -- Arity-check explicit `new C<τ…>` against C's declared type params. `parentExprMap`
  -- holds only COMPOSITES, so this covers a composite `new`; a generic DATATYPE `new`
  -- (`new Bx<int,bool>`) hits the `none` branch and is instead caught downstream fail-loud
  -- (a re-resolution `.StrataBug` after monomorphization), never a wrong-accept. Bare `new C`
  -- carries no args (unchecked — the var's declared type drives it). Without this, surplus
  -- args are silently dropped by the
  -- monomorphizer's `zip`, so `new Box<int,bool>` for `Box<T>` would be over-accepted here.
  unless typeArgs'.isEmpty do
    match s.typeLattice.parentExprMap.get? ref.text with
    | some (declParams, _) =>
      checkTypeArgArity source ref.text declParams.length typeArgs'.length
    | none => pure ()  -- datatype/unresolved: arity deferred to Core
  let kindOk : Bool := match s.scope.get? ref.text with
    | some (_, node) => node.kind == .unresolved ||
        (#[ResolvedNodeKind.compositeType, .datatypeDefinition].contains node.kind)
    | none => true
  -- Applied type so mono sees the instantiation; mirrors `computeExprType`'s `.New` arm.
  let ty :=
    if !kindOk then { val := HighType.Unknown, source := source }
    else if typeArgs'.isEmpty then { val := HighType.UserDefined ref', source := source }
    else { val := HighType.Applied { val := .UserDefined ref', source := source } typeArgs', source := source }
  pure (.New ref' typeArgs', ty)

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
    (target : StmtExprMd) (ty : HighTypeMd) (source : FileRange)
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
    reference equality is meaningless on primitives. They must also be
    mutually CONSISTENT (`isConsistent`, symmetric), which for two
    `UserDefined` types is NAME equality (not subtyping): `Cat` and `Dog`
    are rejected, and even `Cat`/`Animal` (subtype) is rejected — only an
    `Unknown` operand flows freely against the other via the gradual wildcard. -/
def Synth.refEq (exprMd : StmtExprMd) (expr : StmtExpr)
    (lhs rhs : StmtExprMd) (source : FileRange)
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
  let fieldName' ← resolveFieldRef target' fieldName target.source (holderTy? := targetTy)
  -- Concretize against the holder's instantiation.
  let fieldTy ← concretizeFieldType targetTy fieldName'
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
    (trigger : Option StmtExprMd) (body : StmtExprMd) (source : FileRange)
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
    (name : StmtExprMd) (source : FileRange)
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
    (val : StmtExprMd) (expected : HighTypeMd) (source : FileRange)
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
    (val : StmtExprMd) (source : FileRange)
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
    (val : StmtExprMd) (source : FileRange)
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
    (val proof : StmtExprMd) (expected : HighTypeMd) (source : FileRange)
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
    (val proof : StmtExprMd) (source : FileRange)
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
def Synth.this (source : FileRange) :
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
def Synth.abstract (source : FileRange) : StmtExpr × HighTypeMd :=
  (.Abstract, { val := .Unknown, source := source })

/-- `Γ ⊢ All ⇒ Unknown` -/
def Synth.all (source : FileRange) : StmtExpr × HighTypeMd :=
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
    (ty : ContractType) (fn : StmtExprMd) (source : FileRange)
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
    | .Reads | .Modifies => .TSet { val := .Unknown, source := fn.source }
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
    (source : FileRange) : ResolveM StmtExprMd := do
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
def Check.holeNone (det : Bool) (expected : HighTypeMd) (source : FileRange) :
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
private def resolveModifiesTargets (mods : List StmtExprMd) : ResolveM (List StmtExprMd) := do
  let resolved ← mods.mapM resolveModifiesEntry
  return resolved.filterMap id

/-- Resolve the modifies groups of an `Opaque` body: each group's targets go
    through `resolveModifiesTargets`, its guard (pass-generated; `none` for user
    syntax) is checked at `TBool`. Groups are never dropped: a group with no
    targets (authored, or emptied because none were heap-relevant) still claims
    "nothing changes" — under its guard, or unconditionally — which is a frame,
    not a no-op. Opaque procedures with no `modifies` clause rely on exactly
    that group for their default frame. -/
private def resolveModifies (mods : List ModifiesGroup) : ResolveM (List ModifiesGroup) := do
  mods.mapM fun g => do
    let targets' ← resolveModifiesTargets g.targets
    let guard' ← g.guard.mapM (fun c =>
      Check.resolveStmtExpr c { val := .TBool, source := c.source })
    pure ({ g with targets := targets', guard := guard' } : ModifiesGroup)

/-- Resolve a parameter: assign a fresh ID and add to scope. -/
def resolveParameter (param : Parameter) : ResolveM Parameter := do
  let ty' ← resolveHighType param.type
  let name' ← defineNameCheckDup param.name (.parameter ⟨param.name, ty'⟩)
  return ⟨name', ty'⟩

/-- Resolve a procedure's output params (inputs already in scope). FIRST output sharing an
    input's name = inout (e.g. `$heap`), resolved as a ref to that input; a SECOND is a real
    duplicate routed through `resolveParameter` so `defineNameCheckDup` flags it, else two
    Core outputs share a name and mis-verify. -/
private def resolveOutputParameters (inputNames : List String) (outputs : List Parameter)
    : ResolveM (List Parameter) := do
  let (outputsRev, _) ← outputs.foldlM
    (fun (acc : List Parameter × List String) param => do
      let seenOutputs := acc.2
      let p' ←
        if inputNames.contains param.name.text && !seenOutputs.contains param.name.text then do
          let ty' ← resolveHighType param.type
          let name' ← resolveRef param.name
          pure (⟨name', ty'⟩ : Parameter)
        else resolveParameter param
      pure (p' :: acc.1, param.name.text :: seenOutputs))
    ([], [])
  return outputsRev.reverse

/-- Scope a generic entity's type params as `.typeParameter`s so `T`→`.TVar` in
    its signature/fields/body. Run BEFORE resolving the signature. -/
private def scopeTypeParams (typeArgs : List Identifier) : ResolveM (List Identifier) :=
  typeArgs.mapM (fun tv => defineNameCheckDup tv (.typeParameter tv))

/-- Resolve a procedure body by synthesizing its body (if any).
    Bodies without an body (`Abstract`, `External`) resolve
    postconditions only. -/
def resolveBody (body : Body) : ResolveM Body := do
  match body with
  | .Transparent b =>
    let (b', _) ← Synth.resolveStmtExpr b
    return .Transparent b'
  | .Opaque posts impl mods =>
    -- Postconditions are boolean: check against `TBool` (like preconditions and loop
    -- invariants) so a non-bool `ensures` errors instead of silently synthesizing, and
    -- the truthiness coercion is inserted for an `Any`-typed condition.
    let posts' ← posts.mapM (·.mapM (fun c =>
      Check.resolveStmtExpr c { val := .TBool, source := c.source }))
    let impl' ← impl.mapM Synth.resolveStmtExpr
    let mods' ← resolveModifies mods
    return .Opaque posts' (impl'.map (fun t => t.1)) mods'
  | .Abstract posts =>
    let posts' ← posts.mapM (·.mapM (fun c =>
      Check.resolveStmtExpr c { val := .TBool, source := c.source }))
    return .Abstract posts'
  | .External => return .External

/-- Resolve a procedure's exceptional contract: the optional `throws` type (any
    type in the front end's own hierarchy), the name it binds for the thrown
    value, and the `throwsOn` behavior cases.

    Scoping follows the meaning of a case (`C ==> (isBad ∧ P)`). The guard `C` is
    a pre-state predicate, resolved at `bool` like a precondition and *without*
    the thrown value in scope — there is no exception yet when the guard is
    evaluated. Each postcondition `P` is resolved at `bool` with the thrown value
    bound at the declared `throws` type, so a case can state what it threw.

    Because the binding is scoped to the block postconditions, mentioning it in a
    `requires` or a top-level `ensures` resolves to "not defined" without needing
    a bespoke check. The declared type itself is not re-stated as a clause here:
    `EliminateExceptions` derives `isBad ==> err is T` straight from `throwsType`.
    See the Exceptions section of the Laurel User Guide. -/
-- Not `private`: `ResolutionProps.resolveExceptionalContract_clean` unfolds this to
-- prove the `throwsOn` half of `CleanProcFields`, and a private definition is not
-- visible from that module.
def resolveExceptionalContract (proc : Procedure)
    : ResolveM (Option HighTypeMd × Option Identifier × List ThrowsOnBlock) := do
  -- No upper-bound check: a front end may declare `throws T` for any type in its
  -- own hierarchy.
  let throwsType' ← proc.throwsType.mapM resolveHighType
  -- The thrown value is typed at the declared `throws` type when present, else
  -- left `Unknown` (gradual).
  let excBindTy : HighTypeMd := throwsType'.getD { val := .Unknown, source := .unknown }
  let throwsOn' ← proc.throwsOn.mapM fun blk => do
    let guard' ← Check.resolveStmtExpr blk.guard { val := .TBool, source := blk.guard.source }
    let postconditions' ← withScope do
      match proc.throwsBinding with
      | some b => do
        let _ ← defineNameCheckDup b (.var b excBindTy)
        blk.postconditions.mapM (·.mapM fun p =>
          Check.resolveStmtExpr p { val := .TBool, source := p.source })
      | none =>
        blk.postconditions.mapM (·.mapM fun p =>
          Check.resolveStmtExpr p { val := .TBool, source := p.source })
    -- A case's frame: resolve each target like an ordinary (body) modifies
    -- reference — a Composite reference in scope.
    let modifies' ← blk.modifies.mapM resolveStmtExpr
    pure ({ guard := guard', postconditions := postconditions',
            modifies := modifies' } : ThrowsOnBlock)
  pure (throwsType', proc.throwsBinding, throwsOn')

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
  -- Recover this overload's own id. `resolveRef` reads the flat `scope`, which
  -- for an overloaded name only remembers the last overload; `defIdForProcedure`
  -- matches on the signature to find the id `preRegisterStaticProcedure`
  -- assigned to *this* procedure. Falls back to `resolveRef` for names with no
  -- overload entry (e.g. datatype testers registered via `defineNameCheckDup`).
  let procName' ← match ← defIdForProcedure proc with
    | some id => pure { proc.name with uniqueId := some id }
    | none => resolveRef proc.name
  withScope do
    -- Scope type params first, so `T` in inputs/outputs/body resolves to `.TVar`.
    let typeArgs' ← scopeTypeParams proc.typeArgs
    let inputs' ← proc.inputs.mapM resolveParameter
    let inputNames := inputs'.map (·.name.text)
    -- `f<T>(b: Box<T>)` is NOT pre-rejected — procedure monomorphization handles it, and an
    -- instantiation it still can't handle fails loud later.
    let outputs' ← resolveOutputParameters inputNames proc.outputs
    -- Preconditions are boolean: check the condition against `TBool` so the
    -- coercion (`Any_to_bool` via the frontend realizer) is inserted when the
    -- condition is an `Any`-typed expression (a Python `assert` → `PLt(...) : Any`
    -- lifted into a `bool`-returning `$pre` function). The elaborator no longer
    -- coerces; the resolver owns it.
    let pres' ← proc.preconditions.mapM (·.mapM (fun c =>
      Check.resolveStmtExpr c { val := .TBool, source := c.source }))
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let savedAnswer := (← get).answerType
    modify fun s => { s with answerType := some (outputs'.map (·.type)) }
    let body' ← resolveBody proc.body
    modify fun s => { s with answerType := savedAnswer }
    -- Transparent (static) procedure bodies are supported (#1215): the
    -- TransparencyPass derives a functional `$asFunction` copy, and the
    -- LaurelToCore translator rejects the genuinely-unsupported constructs
    -- (e.g. destructive assignments) inside a transparent body. So there is
    -- no transparent-body rejection here, unlike `resolveInstanceProcedure`.
    let invokeOn' ← proc.invokeOn.mapM resolveStmtExpr
    let axioms' ← proc.axioms.mapM resolveStmtExpr
    let (throwsType', throwsBinding', throwsOn') ← resolveExceptionalContract proc
    return { name := procName', typeArgs := typeArgs', inputs := inputs', outputs := outputs',
             preconditions := pres', decreases := dec',
             invokeOn := invokeOn',
             isInterpretEntry := proc.isInterpretEntry,
             axioms := axioms',
             throwsType := throwsType', throwsBinding := throwsBinding',
             throwsOn := throwsOn',
             body := body' }

/-- Resolve a field: define its name under the qualified key (OwnerType.fieldName) and resolve its type. -/
def resolveField (ownerName : Identifier) (field : Field) : ResolveM Field := do
  let ty' ← resolveHighType field.type
  -- No `.Applied` field-type guard here: a generic COMPOSITE field (`Box<int>`) is monomorphized
  -- away by `MonomorphizeComposites` before HeapParam, and a generic DATATYPE field (`Bx<int>`) is
  -- boxed by HeapParam's `.Applied` arm per instantiation (#1394). A generic-typed file-scope
  -- GLOBAL — which monomorphization does not reach through its initializer — is rejected in the
  -- globals validation layer (`validateGlobalTypes`), not here, keeping this function (and its
  -- `resolveField_clean` proof) identical to upstream.
  let qualifiedName := ownerName.text ++ "." ++ field.name.text
  let resolved ← resolveRef qualifiedName
  -- Keep the original field name text; only take the uniqueId from resolution.
  -- resolveRef returns text = "Owner.field" (the qualified lookup key), but the
  -- field's own name should stay unqualified.
  let name' := { field.name with uniqueId := resolved.uniqueId }
  let init' ← field.initializer.mapM (Check.resolveStmtExpr · ty')
  return { name := name', isMutable := field.isMutable, type := ty', initializer := init' }

/-- Resolve an instance procedure on a composite type. -/
def resolveInstanceProcedure (typeName : Identifier) (proc : Procedure) : ResolveM Procedure := do
  let scopedKey := containerScopedName typeName proc.name
  let resolved ← resolveRef scopedKey
  let procName' := { proc.name with uniqueId := resolved.uniqueId }
  withScope do
    let savedInstType := (← get).instanceTypeName
    modify fun s => { s with instanceTypeName := some typeName.text }
    -- Scope the method's OWN type params (`id2<U>`); the composite's `T` is already in
    -- scope from `resolveTypeDefinition`'s `withScope`.
    let typeArgs' ← scopeTypeParams proc.typeArgs
    let inputs' ← proc.inputs.mapM resolveParameter
    let inputNames := inputs'.map (·.name.text)
    let outputs' ← resolveOutputParameters inputNames proc.outputs
    -- Preconditions are boolean: check the condition against `TBool` so the
    -- coercion (`Any_to_bool` via the frontend realizer) is inserted when the
    -- condition is an `Any`-typed expression (a Python `assert` → `PLt(...) : Any`
    -- lifted into a `bool`-returning `$pre` function). The elaborator no longer
    -- coerces; the resolver owns it.
    let pres' ← proc.preconditions.mapM (·.mapM (fun c =>
      Check.resolveStmtExpr c { val := .TBool, source := c.source }))
    let dec' ← proc.decreases.mapM resolveStmtExpr
    let savedAnswer := (← get).answerType
    modify fun s => { s with answerType := some (outputs'.map (·.type)) }
    let body' ← resolveBody proc.body
    modify fun s => { s with answerType := savedAnswer }
    let invokeOn' ← proc.invokeOn.mapM resolveStmtExpr
    modify fun s => { s with instanceTypeName := savedInstType }
    let axioms' ← proc.axioms.mapM resolveStmtExpr
    let (throwsType', throwsBinding', throwsOn') ← resolveExceptionalContract proc
    return { name := procName', typeArgs := typeArgs', inputs := inputs', outputs := outputs',
             preconditions := pres', decreases := dec',
             invokeOn := invokeOn',
             isInterpretEntry := proc.isInterpretEntry,
             axioms := axioms',
             throwsType := throwsType', throwsBinding := throwsBinding',
             throwsOn := throwsOn',
             body := body' }

/-- Resolve a type definition. -/
def resolveTypeDefinition (td : TypeDefinition) : ResolveM TypeDefinition := do
  match td with
  | .Composite ct =>
    let ctName' ← resolveRef ct.name
    -- Scope the type params; the monomorphizer later concretizes `Box<τ>`/`extends Base<T>`.
    let (extending', fields', instProcs') ← withScope do
      let _ ← scopeTypeParams ct.typeArgs
      let extending' ← ct.extending.mapM resolveHighType
      -- Kind-check parents: each peeled base must be composite (`extends T`/`extends int` rejected).
      -- `resolveHighType` accepts any type, so this re-check emits the "expected composite type" diagnostic.
      for parent in extending' do
        match highBaseName? parent.val with
        | some pbase =>
          let _ ← resolveRef pbase parent.source (expected := #[.compositeType])
        | none =>
          modify fun s => { s with errors := s.errors.push (diagnosticFromSource parent.source
            "a composite type can only extend another composite type") }
      let fields' ← ct.fields.mapM (resolveField ctName')
      -- Build the per-type scope BEFORE instance procedures, so `self.field` resolves in methods.
      let s ← get
      let mut typeScope : Scope := {}
      for parent in extending' do
        -- Inherit the parent's field scope by base name (`Base<T>` shares `Base`'s fields).
        match highBaseName? parent.val with
        | some pname =>
          match s.typeScopes.get? pname.text with
          | some parentScope =>
            for (k, v) in parentScope do
              typeScope := typeScope.insert k v
          | none => pure ()
        | none => pure ()
      -- Add own fields (these override inherited ones with the same name)
      for field in fields' do
        let qualifiedKey := ctName'.text ++ "." ++ field.name.text
        match s.scope.get? qualifiedKey with
        | some entry => typeScope := typeScope.insert field.name.text entry
        | none => pure ()
      modify fun s => { s with typeScopes := s.typeScopes.insert ctName'.text typeScope }
      let instProcs' ← ct.instanceProcedures.mapM (resolveInstanceProcedure ctName')
      pure (extending', fields', instProcs')
    return .Composite { name := ctName', typeArgs := ct.typeArgs, extending := extending',
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
    let typeParamNames := dt.typeArgs.map (·.text)
    -- Reject duplicate type parameters (e.g. `datatype Foo<T, T>`): both would
    -- otherwise enter the translation scope and Core would receive a repeated
    -- type variable.
    let dupParams := (typeParamNames.filter (fun n => typeParamNames.count n > 1)).eraseDups
    unless dupParams.isEmpty do
      let diag := diagnosticFromSource dt.name.source
        s!"duplicate type parameter(s): {", ".intercalate dupParams}"
      modify fun s => { s with errors := s.errors.push diag }
    -- Resolve the constructors with the datatype's type parameters registered in
    -- a fresh scope, so a reference to a parameter in a field type resolves to a
    -- `.typeParameter` (a type variable) through the normal path — like any other
    -- type name — instead of being reported "not defined". The scope is discarded
    -- afterwards, so parameters don't leak to sibling declarations, and a
    -- parameter shadows a same-named outer type while inside this datatype.
    -- Unlike composites, generic datatypes do NOT monomorphize — they map to
    -- native Core parametric datatypes, so the `.TVar`s survive `translateType`
    -- as sort args.
    let ctors' ← withScope do
      for tp in dt.typeArgs do
        let _ ← defineName tp (.typeParameter tp)
      dt.constructors.mapM fun ctor => do
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
    -- Scope the alias's type params; `TypeAliasElim`/`unfold` later binds them to the instantiation args.
    let target' ← withScope do
      let _ ← scopeTypeParams ta.typeArgs
      resolveHighType ta.target
    let taName' ← resolveRef ta.name
    return .Alias { name := taName', typeArgs := ta.typeArgs, target := target' }

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
  let src := dt.name.source
  let inputParam : Parameter := {
    name := mkId "value"
    type := { val := .UserDefined dt.name, source := src }
  }
  let outputParam : Parameter := {
    name := mkId "$result"
    type := { val := .TBool, source := src }
  }
  { name := mkId tName
    inputs := [inputParam]
    outputs := [outputParam]
    preconditions := []
    decreases := none
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
  | .Intersection tys => tys.foldl collectHighType map
  | .MultiValuedExpr tys => tys.foldl collectHighType map
  | _ => map

private def collectStmtExpr (map : Std.HashMap Nat ResolvedNode) (expr : StmtExprMd)
    : Std.HashMap Nat ResolvedNode :=
  foldStmtExpr (fun e map =>
    match e.val with
    | .Var (.Declare param) =>
      -- Post-resolution every `Declare` is annotated; default to `Unknown`.
      let ty := param.type.getD { val := .Unknown, source := param.name.source }
      let map := register map param.name (.var param.name ty)
      collectHighType map ty
    | .Assign targets _ =>
      targets.foldl (fun map t =>
        match t.val with
        | .Declare param =>
          let ty := param.type.getD { val := .Unknown, source := param.name.source }
          let map := register map param.name (.var param.name ty)
          collectHighType map ty
        | _ => map) map
    | .Quantifier _ param _ _ =>
      let map := register map param.name (.quantifierVar param.name param.type)
      collectHighType map param.type
    | .AsType _ ty => collectHighType map ty
    | .IsType _ ty => collectHighType map ty
    -- Register each `catch` binding so references to it in the guard/body
    -- resolve during Core translation. Its type is the join (least common
    -- ancestor of the `try` body's thrown types) computed by `Check.tryCatch`
    -- and carried on the clause as `bindingType`; the `EliminateExceptions` pass
    -- reads it to type the per-`try` `$exc_<i>` local. Recursion into the arms
    -- is handled by `foldStmtExpr`.
    | .Try _ catches _ =>
      catches.foldl (fun map c =>
        register map c.binding (.var c.binding c.bindingType)) map
    | _ => map) map expr

private def collectBody (map : Std.HashMap Nat ResolvedNode) (body : Body)
    : Std.HashMap Nat ResolvedNode :=
  match body with
  | .Transparent b => collectStmtExpr map b
  | .Opaque posts impl mods =>
    let map := posts.foldl (fun map c => collectStmtExpr map c.condition) map
    let map := match impl with | some i => collectStmtExpr map i | none => map
    mods.foldl (fun map g =>
      let map := g.targets.foldl collectStmtExpr map
      match g.guard with | some c => collectStmtExpr map c | none => map) map
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
  -- Covers the `throwsOn` cases' guards, postconditions and frame targets, which
  -- `procedureSpecificationExprs` enumerates alongside the other specification fields.
  let map := procedureSpecificationExprs proc |>.foldl collectStmtExpr map
  -- The thrown-value binding is a *declaration*, not an expression, so the fold above
  -- cannot reach it. Register it here so references to it inside a `throwsOn`
  -- postcondition resolve during Core translation, typed at the declared `throws` type
  -- (else `Unknown`), matching `resolveExceptionalContract`.
  let excBindTy : HighTypeMd := proc.throwsType.getD ⟨.Unknown, .unknown⟩
  let map := match proc.throwsBinding with
    | some b => register map b (.var b excBindTy)
    | none => map
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
      -- Register the tester function in the refToDef map. Use `ctor.testerName`
      -- (which carries its resolution-assigned uniqueId) as the procedure name.
      let testerProc := { mkTesterProcedure dt ctor with name := ctor.testerName }
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
def canReachField (model : SemanticModel) (typeName : Identifier) (fieldName : Identifier) : Except String Bool := do
  match model.get fieldName with
  | .field owner _ =>
    let ancestors ← computeAncestors model typeName
    let found ← ancestors.anyM (fun t => owner.sameId t.name)
    pure found
  | _ => pure false -- recover from a resolution error

/--
Check if a field is inherited through multiple parent paths (diamond inheritance).
Returns true if more than one direct parent of the given type can reach the field.
-/
def isDiamondInheritedField (model : SemanticModel) (typeName : Identifier) (fieldName : Identifier) : Except String Bool := do
  match model.get typeName with
  | .compositeType ct =>
    -- If the field is directly declared on this type, it's not a diamond
    let directlyDeclared ← ct.fields.anyM (fun f => fieldName.sameId f.name)
    if directlyDeclared then pure false
    else do
      -- Count how many direct parents can reach this field. Peel each parent type to
      -- its base name; `extending` is `List HighTypeMd`.
      let parentNames := ct.extending.filterMap (fun e => highBaseName? e.val)
      let count ← parentNames.foldlM (init := 0) fun count parent => do
        let reaches ← canReachField model parent fieldName
        pure (if reaches then count + 1 else count)
      pure (count > 1)
  | _ => pure false

/--
Check whether accessing `fieldName` on `target` is a diamond-inherited field access,
and if so return a diagnostic error using the given `source` range.
-/
private def checkDiamondFieldAccess (model : SemanticModel) (target : StmtExprMd)
    (fieldName : Identifier) (source : FileRange) : List Message :=
  -- Peel the receiver to its base name so a generic receiver `D<int>` (`.Applied`) is
  -- checked too; otherwise it slips to mono and surfaces as a `.StrataBug`, not this diagnostic.
  match highBaseName? (computeExprType model target).val with
  | some typeName =>
    match isDiamondInheritedField model typeName fieldName with
    | .ok true =>
      [Message.withRange source s!"fields that are inherited multiple times can not be accessed."]
    | .ok false => []
    | .error e => [Message.fromString e .strataBug]
  | _ => []

/-- Check `e` itself for a diamond-inherited field access; the caller's traversal supplies recursion. -/
private def collectDiamondFieldAt (model : SemanticModel) (e : StmtExprMd) :
    StateM (List Message) StmtExprMd := do
  match e.val with
  | .Var (.Field target fieldName) =>
    modify (· ++ checkDiamondFieldAccess model target fieldName e.source)
  | .Assign targets _ =>
    for t in targets do
      match t.val with
      | .Field target fieldName =>
        modify (· ++ checkDiamondFieldAccess model target fieldName t.source)
      | _ => pure ()
  | .IncrDecr _ _ target =>
    match target.val with
    | .Field tgt fieldName =>
      modify (· ++ checkDiamondFieldAccess model tgt fieldName target.source)
    | _ => pure ()
  | .CompoundAssign _ target _ =>
    -- `CompoundAssign` is new on mainline; the caller's traversal visits `rhs` and any
    -- nested field subtree, so only the direct `.Field` target introduces a field access here.
    match target.val with
    | .Field tgt fieldName =>
      modify (· ++ checkDiamondFieldAccess model tgt fieldName target.source)
    | _ => pure ()
  | .PureFieldUpdate target fieldName _ =>
    modify (· ++ checkDiamondFieldAccess model target fieldName e.source)
  | _ => pure ()
  pure e

/-- One `Message` per diamond-inherited field access — a field reached via >1
    direct-parent path (see `isDiamondInheritedField`).
    The total `mapProgramProceduresM ∘ mapProcedureM ∘ mapStmtExprM` drives a `StateM`
    collector, so coverage can't silently regress: every procedure position (body,
    preconditions, decreases, invokeOn, axioms) across static AND instance procedures, and
    every sub-expression (quantifiers, `old`, `as`/`is`, ref-equality).
    Not covered: `constrained`-type constraint/witness and constant initializers —
    non-procedure positions that fail loud as `.strataBug` (no silent accept). Promoting to
    `.userError` needs bound-variable scoping verified first. -/
private def validateDiamondFieldAccesses (model : SemanticModel) (program : Program) : List Message :=
  ((mapProgramProceduresM (mapProcedureM (mapStmtExprM (collectDiamondFieldAt model))) program).run []).2

/-! ## Pre-registration: populate scope with all top-level names before resolving bodies -/



/-- A default ResolvedNode used as a placeholder during pre-registration.
    It will be overwritten with the real node when the definition is fully resolved. -/
private def placeholderNode : ResolvedNode :=
  .var "$placeholder" { val := .TVoid, source := { file := .file "Strata/Languages/Laurel/Resolution.lean", range := SourceRange.none } }

/-- Rewrite each `.UserDefined n` with `n ∈ params` to `.TVar n`, so a generic entity's STORED
    signature/fields match the `.TVar` form `resolveHighType` produces in scope. NEEDED: the #1121
    checker reads types from `preRegisterTopLevel`'s maps off RAW nodes, where a param is still
    `.UserDefined "T"` — else the `.TVar` wildcard never fires (spurious mismatch). No-op if empty. -/
private def tvarizeType (params : List String) (ty : HighTypeMd) : HighTypeMd :=
  mapHighTypeNames (fun ctor n => if params.contains n.text then .TVar n else ctor n) ty

/-- Tvarize a `Parameter`'s type over `params`. -/
private def tvarizeParam (params : List String) (p : Parameter) : Parameter :=
  { p with type := tvarizeType params p.type }

/-- Tvarize the parts of a procedure's SIGNATURE that another procedure reads out
    of scope, over the given type params. Exactly the three fields a call site
    consults on a scope-resident callee:
    - `inputs`  — argument checking (`getCallInfo`/`overloadAccepts`);
    - `outputs` — the call's result type (`procReturnType`);
    - `throwsType` — the `try`/`catch` binding type (`calleeThrowsName`, which
      matches `.UserDefined`, so a raw `.UserDefined "T"` here makes the CALLER
      collect the bare name `T` and fail to resolve it: "'T' is not defined").
    A callee's `throwsOn`/`throwsBinding`/`preconditions`/body are read only when
    resolving the callee's OWN body (in its own type-param scope), never
    cross-procedure, so they are deliberately left alone. Keeping this in one
    place means adding a signature field can't tvarize one caller-visible slot
    and forget another. No-op when `params` is empty (a monomorphic proc). -/
private def tvarizeProcSignature (params : List String) (proc : Procedure) : Procedure :=
  { proc with
    inputs := proc.inputs.map (tvarizeParam params),
    outputs := proc.outputs.map (tvarizeParam params),
    throwsType := proc.throwsType.map (tvarizeType params) }

/-- Pre-register all top-level names into scope so that declaration order doesn't matter.
    This assigns fresh IDs and adds placeholder scope entries for:
    - Type names (composite, constrained, datatype) and their constructors/destructors/fields
    - Constant names
    - Static procedure names -/
private def preRegisterDefinitions (types : List TypeDefinition)
    (constants : List Constant) (staticFields : List Field)
    (procs : List Procedure) : ResolveM Unit := do
  for td in types do
    match td with
    | .Composite ct =>
      -- Tvarize field types over the composite's type params (see `tvarizeType`).
      let ctParams := ct.typeArgs.map (·.text)
      let _ ← defineNameCheckDup ct.name (.compositeType ct)
      for field in ct.fields do
        let qualifiedName := ct.name.text ++ "." ++ field.name.text
        let field := { field with type := tvarizeType ctParams field.type }
        let _ ← defineNameCheckDup field.name (.field ct.name field) (some qualifiedName)
      for proc in ct.instanceProcedures do
        let scopedKey := (containerScopedName ct.name proc.name).text
        -- Tvarize over the composite's type params AND the method's own (`id2<U>` adds `U`),
        -- so the stored `.instanceProcedure` carries `.TVar` across its whole signature.
        let methodParams := ctParams ++ proc.typeArgs.map (·.text)
        let proc := tvarizeProcSignature methodParams proc
        let _ ← defineNameCheckDup proc.name (.instanceProcedure ct.name proc)
                                   (some scopedKey)
    | .Constrained ct =>
      let _ ← defineNameCheckDup ct.name (.constrainedType ct)
    | .Datatype dt =>
      let _ ← defineNameCheckDup dt.name (.datatypeDefinition dt)
      for ctor in dt.constructors do
        let _ ← defineNameCheckDup ctor.name (.datatypeConstructor dt.name ctor)
        let testerProc := mkTesterProcedure dt ctor
        let _ ← defineNameCheckDup (mkId (dt.testerName ctor))
          (.staticProcedure testerProc) (some (dt.testerName ctor))
        for p in ctor.args do
          let pName ← defineNameCheckDup p.name (.datatypeDestructor dt.name p) (some (dt.destructorName p))
          let _ ← defineNameCheckDup pName (.datatypeDestructor dt.name p) (some (dt.unsafeDestructorName p))
    | .Alias ta =>
      let _ ← defineNameCheckDup ta.name (.typeAlias ta)
  for c in constants do
    let _ ← defineNameCheckDup c.name (.constant c)
  -- Register both lookup forms for each file-scope global with one definition ID.
  -- Only the user-facing bare name participates in duplicate diagnostics.
  for field in staticFields do
    let qualifiedName := "$static." ++ field.name.text
    let fieldName ← defineNameCheckDup field.name (.field "$static" field)
    if !(← get).currentScopeNames.contains qualifiedName then
      let _ ← defineNameCheckDup fieldName (.field "$static" field) (some qualifiedName)
  -- Pre-register static procedures via upstream's overload-aware registration,
  -- but first tvarize each proc's signature over its own type params (#1394: `T`
  -- in `procedure f<T>` → `.TVar`; see `tvarizeProcSignature`). Monomorphic procs
  -- (empty `typeArgs`) are unchanged, so this is a no-op for them.
  for proc in procs do
    let procParams := proc.typeArgs.map (·.text)
    preRegisterStaticProcedure (tvarizeProcSignature procParams proc)

private def preRegisterTopLevel (program : Program) : ResolveM Unit :=
  preRegisterDefinitions program.types program.constants program.staticFields
    program.staticProcedures

/-! ## Exception-escape enforcement

/-- Collect a "nested `old(...)` has no effect" warning for every `Old` node
    inside `operand` (the operand of an enclosing `old`). An `old` nested
    directly inside another `old` is always redundant. -/
private def nestedOldWarnings (operand : StmtExprMd) : List Message :=
  (mapStmtExprM (m := StateM (List Message))
    (fun n => do
      match n.val with
      | .Old _ =>
        modify (· ++ [diagnosticFromSource n.source "nested `old(...)` has no effect" .warning])
        pure n
      | _ => pure n)
    operand |>.run []).2
Static "check, don't trust" analysis: a procedure
that does not declare `throws` must not let any exception escape, and one that
declares `throws T` must only let exceptions whose type is a subtype of `T`
escape.

`exceptionEscapes` over-approximates the set of exception types that can leave a
statement uncaught. A `try` removes a body type only when some `catch` clause
*provably* handles it — a catch-all, or an `x is T` guard (or a disjunction of
such guards) with the type a subtype of `T`. Any other guard is treated as
catching nothing, so the analysis stays sound: it never claims an escape is
impossible when it might not be.

It runs from `resolve` on **every** resolution (NOT gated on
`existingModel.isNone`, unlike the sibling `validateException*` guards). The
initial resolution checks the program as the user wrote it, where `throw`
operands and concrete `throws` types carry their real types. A poly `throws
(e:T)` is DEFERRED there (`exceptionEscapes` drops any escaping type that mentions
a type var, via `mentionsTVar`) because `T` is not concrete yet — exactly as
a poly RETURN flows gradually through `isConsistent`. The deferred case is caught
at the post-`MonomorphizeComposites` re-resolution, where the clone's throws type
is concrete (`g$a1$int` throws `int`) and a genuine `int </: bool` escape is a
real subtype violation. A concrete escape already reported at the initial resolve
is deduped by the caller's `newErrors` filter, so it is reported once. Once
`EliminateExceptions` sets `throwsType := none` and erases `throw`/`try`, the
check is a no-op on later re-resolutions. Instance procedures are not lifted at
the initial resolve, so the check walks them inside their composites; a
method→method `throws` still resolves because `calleeThrows` reads
`.instanceProcedure` from the model as well as `.staticProcedure`. -/

/-- Whether `stmt` *definitely* completes abruptly — every path through it ends
    in a `return`, a `throw`, or an `exit` that leaves it — so a completion left
    pending by a `try` body or handler cannot survive past it (Java JLS §14.20.2 /
    C#: the `finally`'s own abrupt completion supersedes it, which is what
    `EliminateExceptions` lowers).

    A sound under-approximation: anything it cannot prove abrupt is `false`, so
    the caller stays conservative. `opened` carries the labels of blocks opened
    within `stmt`, which is what distinguishes an `exit` that leaves it from one
    that merely jumps ahead inside it; the top-level entry point starts empty. -/
private def alwaysCompletesAbruptlyIn (opened : List String) (stmt : StmtExprMd) : Bool :=
  match _h : stmt.val with
  | .Return _ => true
  | .Throw _ => true
  -- An `exit` completes the statement abruptly only when it *leaves* it: a jump
  -- to a label opened inside just skips ahead within it. (`EliminateExceptions`
  -- unwinds a leaving `exit` through the `finally` arms it crosses, dropping the
  -- pending completion exactly as a `return`/`throw` would.)
  | .Exit label => !opened.contains label
  -- Statements after an unconditional terminator are unreachable, so a block is
  -- abrupt as soon as any of its statements is.
  | .Block stmts label =>
    let inner := match label with | some l => l :: opened | none => opened
    stmts.attach.any (fun ⟨s, _⟩ => alwaysCompletesAbruptlyIn inner s)
  | .IfThenElse _ t (some e) =>
    alwaysCompletesAbruptlyIn opened t && alwaysCompletesAbruptlyIn opened e
  | _ => false
  termination_by sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt stmt; rw [_h] at hsz)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

private def alwaysCompletesAbruptly (stmt : StmtExprMd) : Bool :=
  alwaysCompletesAbruptlyIn [] stmt

/-- Over-approximate the exception types (each with a source location) that can
    escape `expr` uncaught. A type that MENTIONS a type variable (a poly `throws
    (e:T)` or `throws Box<T>`, via `mentionsTVar`) is dropped here: at the initial
    resolution `T` is not concrete, so — exactly as a poly RETURN flows gradually
    through `isConsistent`'s recursive `.TVar` wildcard — the escape is deferred to
    the post-mono re-resolution, where the clone's throws type is concrete and
    genuinely checkable (the un-gated `validateExceptionEscapes` in `resolve`). -/
private def exceptionEscapes (model : SemanticModel) (lattice : TypeLattice)
    (expr : StmtExprMd) : List (HighTypeMd × FileRange) :=
  let calleeThrows (callee : Identifier) : List (HighTypeMd × FileRange) :=
    match model.get callee with
    | .staticProcedure p | .instanceProcedure _ p =>
      match p.throwsType with
      | some t => if mentionsTVar t.val then [] else [(t, expr.source)]
      | none => []
    | _ => []
  -- Recursive descents go through `attach` (and named discriminant equations) so
  -- each child carries the membership/shape proof the termination argument needs.
  match _h : expr.val with
  | .Throw e =>
    -- Every `throw` is on the exceptional channel (there is no root type to
    -- gate on); the thrown value's type is what may escape. Also recurse into
    -- the operand: a throwing call inside it (e.g. `throw f()` where `f` throws)
    -- escapes too. A thrown value of poly type (`throw x` where `x : T`) is
    -- dropped like a poly `throws` type — deferred to the post-mono re-check.
    let thrownTy := computeExprType model e
    (if mentionsTVar thrownTy.val then [] else [(thrownTy, expr.source)])
      ++ exceptionEscapes model lattice e
  | .StaticCall callee args =>
    calleeThrows callee ++ args.attach.flatMap (fun ⟨a, _⟩ => exceptionEscapes model lattice a)
  | .InstanceCall target callee args =>
    calleeThrows callee ++ exceptionEscapes model lattice target
      ++ args.attach.flatMap (fun ⟨a, _⟩ => exceptionEscapes model lattice a)
  | .Try body catches finally? =>
    let bodyEsc := exceptionEscapes model lattice body
    let uncaught := bodyEsc.filter (fun p => !catches.any (fun c => clauseCatches lattice c p.1))
    let handlersEsc := catches.attach.flatMap (fun ⟨c, _⟩ => exceptionEscapes model lattice c.body)
    let finallyEsc := match _hf : finally? with
      | some f => exceptionEscapes model lattice f
      | none => []
    -- A `finally` that definitely completes abruptly *supersedes* whatever the
    -- body or a handler left pending, so nothing from them escapes through it
    -- (only the `finally`'s own throws do). Without this the check reports a
    -- spurious escape for e.g. `try { throw e } finally { return }`, whose
    -- `return` provably swallows the exception, and rejects a legal program.
    let finallyAbrupt := match finally? with
      | some f => alwaysCompletesAbruptly f
      | none => false
    if finallyAbrupt then finallyEsc
    else uncaught ++ handlersEsc ++ finallyEsc
  | .Block stmts _ => stmts.attach.flatMap (fun ⟨s, _⟩ => exceptionEscapes model lattice s)
  | .IfThenElse c t e =>
    exceptionEscapes model lattice c ++ exceptionEscapes model lattice t
      ++ (match _he : e with | some eb => exceptionEscapes model lattice eb | none => [])
  | .While c _ _ b _ =>
    exceptionEscapes model lattice c ++ exceptionEscapes model lattice b
  | .Assign targets value =>
    -- A `Field` target's object expression (`mk()#x := 1`) can throw or call a
    -- throwing procedure, so it escapes exactly like the assigned value does.
    targets.attach.flatMap (fun ⟨t, _⟩ =>
      match _ht : t.val with
      | .Field obj _ => exceptionEscapes model lattice obj
      | _ => [])
      ++ exceptionEscapes model lattice value
  | .Return (some v) => exceptionEscapes model lattice v
  | .ProveBy v pf => exceptionEscapes model lattice v ++ exceptionEscapes model lattice pf
  | _ => []
  termination_by sizeOf expr
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt expr; rw [_h] at hsz)
    all_goals (try have hcatch := CatchClause.sizeOf_body_lt ‹_›)
    all_goals (try term_by_mem)
    -- Descent into a `Field` assignment target's object expression: the target is
    -- a member of `targets` and the object is smaller than the target.
    all_goals (try (
      have hobj := Variable.sizeOf_field_target_lt_of_eq _ht
      have hmem := List.sizeOf_lt_of_mem ‹_›
      simp at hsz
      omega))
    all_goals (try (simp_all; omega))

/-- Guard: reject a `try` whose escaping exception cannot be copied into the region
    it propagates into.

    `EliminateExceptions` gives each `try` an exception variable typed at its
    least-common-ancestor type `ti`, and on the escaping edge copies it into the
    enclosing region's variable, typed `tp`: a widening when `ti <: tp`, an assumed
    checked downcast when `tp <: ti`. When the two are unrelated there is no legal
    copy at all — even `ti as tp` is rejected as a cast between unrelated types — so
    the lowering emits nothing and the enclosing variable is left unassigned, which
    then fails the procedure's own `throwsOn` case with a misleading *postcondition
    could not be proved*.

    Under single inheritance that case cannot arise with anything actually escaping.
    But a composite may extend several parents, and then a common subtype of two
    otherwise unrelated types can legally escape: with `composite C extends A, B`, a
    `try` whose types join at `B`, inside a `throws A` procedure, escapes a `C`.
    Reject that shape here instead of lowering it into an unassigned variable.

    `parentTy` is the type of the region the statement propagates into — the
    enclosing `try`'s binding type, or the procedure's declared `throws` type at the
    top level. A `finally`-only `try` introduces no variable of its own (it shares
    the enclosing one), so it passes `parentTy` through unchanged, mirroring the
    lowering. Only a `try` that something actually escapes is checked, so a fully
    handled `try` with an unrelated binding type stays legal. -/
private def checkPropagationEdges (model : SemanticModel) (lattice : TypeLattice)
    (parentTy : Option HighTypeMd) (stmt : StmtExprMd) : List Message :=
  match _h : stmt.val with
  | .Try body catches finally? =>
    let thisTy : Option HighTypeMd := catches.head?.map (fun c => c.bindingType)
    let edgeError : List Message :=
      match thisTy, parentTy with
      | some ti, some tp =>
        if !(exceptionEscapes model lattice stmt).isEmpty
            && !isSubtype lattice ti tp && !isSubtype lattice tp ti then
          [diagnosticFromSource stmt.source
            s!"an exception escaping this `try` is not yet supported here: the `try`'s exception type '{formatType ti}' is unrelated to '{formatType tp}', the type it must propagate into, so the lowering has no legal copy between the two (this can happen when a composite extends several parents). Catch it inside the `try`, or relate the two types."
            MessageKind.notYetImplemented]
        else []
      | _, _ => []
    edgeError
      ++ checkPropagationEdges model lattice (match thisTy with
           | some _ => thisTy
           | none => parentTy) body
      ++ catches.attach.flatMap (fun ⟨c, _⟩ =>
           checkPropagationEdges model lattice parentTy c.body)
      ++ (match _hf : finally? with
          | some f => checkPropagationEdges model lattice parentTy f
          | none => [])
  | .Block stmts _ =>
    stmts.attach.flatMap (fun ⟨s, _⟩ => checkPropagationEdges model lattice parentTy s)
  | .IfThenElse _ t e =>
    checkPropagationEdges model lattice parentTy t
      ++ (match _he : e with
          | some eb => checkPropagationEdges model lattice parentTy eb
          | none => [])
  | .While _ _ _ b _ => checkPropagationEdges model lattice parentTy b
  | _ => []
  termination_by sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt stmt; rw [_h] at hsz)
    all_goals (try have hcatch := CatchClause.sizeOf_body_lt ‹_›)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

/-- Stable substrings that identify the two `checkProcedureThrows` escape
    diagnostics. Referenced BOTH by the producer below (woven into each message)
    and by the pipeline's re-resolution classifier (`isExceptionContract` in
    `LaurelCompilationPipeline`), which must recognize a deferred poly-throws
    escape surfacing post-monomorphization and pass it through as the user error
    it is rather than wrapping it as an internal `strata-bug`. Sharing the
    literal makes that cross-module match a compile-time guarantee: rewording a
    message can't silently desync the classifier (the alternative — matching by
    `MessageKind` — can't work, since a genuine dangling-ref error is also a
    `.userError`). Both fragments are interpolation-free, so they survive changes
    to the surrounding prose. -/
def escapeUndeclaredMarker : String := "may let an exception of type"
def escapeNotSubtypeMarker : String := "is not a subtype of its declared"

/-- Check one procedure's body against its `throws` declaration:
    no-escape when nothing is declared, subtype upper-bound when `throws T` is. -/
private def checkProcedureThrows (model : SemanticModel) (lattice : TypeLattice)
    (displayName : String) (proc : Procedure) : List Message :=
  let body? := match proc.body with
    | .Transparent b => some b
    | .Opaque _ (some impl) _ => some impl
    | _ => none
  match body? with
  | none => []
  | some body =>
    let escs := exceptionEscapes model lattice body
    match proc.throwsType with
    | none =>
      escs.map (fun (ty, src) =>
        diagnosticFromSource src
          s!"procedure '{displayName}' {escapeUndeclaredMarker} '{formatType ty}' escape; catch it with a `try`/`catch` or declare a `throws` clause"
          MessageKind.userError)
    | some declared =>
      escs.filterMap (fun (ty, src) =>
        if isSubtype lattice ty declared then none
        else some (diagnosticFromSource src
          s!"procedure '{displayName}' may throw '{formatType ty}', which {escapeNotSubtypeMarker} `throws` type '{formatType declared}'"
          MessageKind.userError))

/-- Validate the whole program's exception contracts. `procs` pairs each procedure
    with the name to show the user: static procedures by their own name, and a
    composite's instance procedure as `Composite.method` (they are still un-lifted
    when this runs — from `resolve`, on the initial resolution — so the owning type
    has to be supplied here rather than read off a lifted `Composite$method`
    name). A method→method `throws` still resolves, because `calleeThrows` reads
    `.instanceProcedure` from the model as well as `.staticProcedure`. -/
private def validateExceptionEscapes (model : SemanticModel) (lattice : TypeLattice)
    (procs : List (String × Procedure)) : List Message :=
  procs.flatMap (fun (displayName, proc) =>
    checkProcedureThrows model lattice displayName proc)

/-! ## Exception-lowering guards

`EliminateExceptions` does not yet handle two source shapes; each would otherwise
surface downstream as an internal `strata-bug` or a silent miscompile, so they are
rejected here — from `resolve`, alongside the escape check, before the lowering —
with a clear "not yet supported" diagnostic.

(An `exit` leaving a `try`/`finally` needs no guard: the lowering unwinds it
through the crossed `finally` arms.) -/

/-- Whether `callee` names a procedure that declares `throws`. -/
private def procDeclaresThrows (model : SemanticModel) (callee : Identifier) : Bool :=
  match model.get callee with
  | .staticProcedure p | .instanceProcedure _ p => p.throwsType.isSome
  | _ => false

/-- Sources of every call to a `throws` procedure anywhere in `e`. The lowering
    only handles a throwing call as a whole statement or the whole RHS of an
    assignment/return; anywhere else (nested in an operator, a call argument, a
    condition, a `throw` operand) is unsupported, so those calls are flagged. -/
private def throwingCallSources (model : SemanticModel) (e : StmtExprMd) : List FileRange :=
  collectStmtExprList (fun n =>
    match n.val with
    | .StaticCall callee _ | .InstanceCall _ callee _ =>
      if procDeclaresThrows model callee then [n.source] else []
    | _ => []) e

/-- Guard: flag a `throws` call in a disallowed (nested) expression
    position. A whole-statement call and a whole-RHS call (assignment or return
    payload — `EliminateValueInReturns` turns the latter into an assignment) are
    the only positions the lowering handles; their *arguments* are still nested. -/
private def checkThrowingCallPositions (model : SemanticModel) (stmt : StmtExprMd)
    : List FileRange :=
  -- A value expression bound whole (assignment RHS / return payload): a call at
  -- its head is fine, but its arguments are nested value expressions.
  let checkValue (v : StmtExprMd) : List FileRange :=
    match v.val with
    | .StaticCall _ args | .InstanceCall _ _ args => args.flatMap (throwingCallSources model)
    | _ => throwingCallSources model v
  match _h : stmt.val with
  | .Block stmts _ =>
    stmts.attach.flatMap (fun ⟨s, _⟩ => checkThrowingCallPositions model s)
  | .IfThenElse c t e =>
    throwingCallSources model c ++ checkThrowingCallPositions model t
      ++ (match _he : e with | some eb => checkThrowingCallPositions model eb | none => [])
  | .While c _ _ b _ => throwingCallSources model c ++ checkThrowingCallPositions model b
  | .Try body catches finally? =>
    checkThrowingCallPositions model body
      ++ catches.attach.flatMap (fun ⟨c, _⟩ =>
           (match c.predicate with | some p => throwingCallSources model p | none => [])
             ++ checkThrowingCallPositions model c.body)
      ++ (match _hf : finally? with | some f => checkThrowingCallPositions model f | none => [])
  | .Assign targets value =>
    -- Only the assigned *value* is a whole-RHS position. A `Field` target's object
    -- expression (`mk()#x := 1`) is nested, so a throwing call anywhere inside it
    -- is flagged — including at its head.
    targets.flatMap (fun t =>
      match t.val with
      | .Field obj _ => throwingCallSources model obj
      | _ => [])
      ++ checkValue value
  | .Return (some v) => checkValue v
  | .Throw op => throwingCallSources model op
  | .StaticCall _ args | .InstanceCall _ _ args => args.flatMap (throwingCallSources model)
  | _ => throwingCallSources model stmt
  termination_by sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt stmt; rw [_h] at hsz)
    all_goals (try have hcatch := CatchClause.sizeOf_body_lt ‹_›)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

/-- Guard: flag a `catch` handler that re-declares its own exception
    binding. The binding snapshot in `EliminateExceptions` substitutes by textual
    name and is not scope-aware, so an inner re-declaration of the binding name is
    miscompiled. Returns each offending source paired with the binding name. -/
private def checkCatchBindingShadowing (stmt : StmtExprMd)
    : List (FileRange × String) :=
  match _h : stmt.val with
  | .Try body catches finally? =>
    let declaresBinding (binding : String) (b : StmtExprMd) : List (FileRange × String) :=
      collectStmtExprList (fun n =>
        match n.val with
        | .Var (.Declare p) => if p.name.text == binding then [(n.source, binding)] else []
        | .Assign targets _ =>
          targets.filterMap (fun t => match t.val with
            | .Declare p => if p.name.text == binding then some (n.source, binding) else none
            | _ => none)
        | _ => []) b
    (catches.attach.flatMap (fun ⟨c, _⟩ => declaresBinding c.binding.text c.body))
      ++ checkCatchBindingShadowing body
      ++ catches.attach.flatMap (fun ⟨c, _⟩ => checkCatchBindingShadowing c.body)
      ++ (match _hf : finally? with | some f => checkCatchBindingShadowing f | none => [])
  | .Block stmts _ => stmts.attach.flatMap (fun ⟨s, _⟩ => checkCatchBindingShadowing s)
  | .IfThenElse _ t e =>
    checkCatchBindingShadowing t
      ++ (match _he : e with | some eb => checkCatchBindingShadowing eb | none => [])
  | .While _ _ _ b _ => checkCatchBindingShadowing b
  | _ => []
  termination_by sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt stmt; rw [_h] at hsz)
    all_goals (try have hcatch := CatchClause.sizeOf_body_lt ‹_›)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

/-- Whether `proc` uses the exceptional channel in its authored form: it declares
    a `throws` type or any exceptional clause, or its body contains a `throw` or a
    `try`. This mirrors the condition `EliminateExceptions` uses to decide whether
    to inject the `Result` datatype. A program that only *calls* a throwing
    procedure is covered too, because that callee is itself a procedure of the
    program and declares `throws`. -/
private def procUsesExceptions (proc : Procedure) : Bool :=
  proc.throwsType.isSome
    || !proc.throwsOn.isEmpty
    || (match proc.body with
        | .Transparent b => bodyThrowsOrTries b
        | .Opaque _ (some impl) _ => bodyThrowsOrTries impl
        | _ => false)
where
  bodyThrowsOrTries (b : StmtExprMd) : Bool :=
    anyStmtExpr (fun n => match n.val with
      | .Throw _ | .Try .. => true
      | _ => false) b

/-- Reject a `throwsOn` behavior case on a procedure that declares no `throws`
    type, and reject a value output referenced from inside one.

    A case describes the throwing exit, and without a `throws` type there is none:
    the case cannot be honored, and it is not lowered either — `EliminateExceptions`
    only rewrites the cases of a procedure it gives a `Result` to, and
    `ModifiesClauses` only builds exceptional frames for such a procedure — so it
    would be silently ignored rather than checked.

    A value output does not exist on the throwing path either. The lowering
    replaces it with a single `Result` whose `Bad` arm carries only the exception,
    so a case mentioning it would read `Result..value($result)` off a `Bad` result:
    an underspecified postcondition rather than a diagnosable error. Inout
    parameters are exempt — they survive as outputs of the lowered procedure.

    Runs only on the initial resolution, like the other exception checks: the
    lowering clears `throws` while deliberately *keeping* the cases' frames for
    `ModifiesClauses`, so re-running this on lowered output would report every
    exceptional frame in the program. -/
private def validateExceptionalClausesNeedThrows
    (procs : List (String × Procedure)) : List Message :=
  procs.flatMap fun (displayName, proc) =>
    let needsThrows :=
      if proc.throwsType.isSome then []
      else proc.throwsOn.map fun blk =>
        diagnosticFromSource blk.guard.source
          s!"a `throwsOn` case describes the exceptional exit, so procedure '{displayName}' must declare a `throws` type; without one it has no exceptional exit and the case would be silently ignored"
          MessageKind.userError
    let inputNames := proc.inputs.map (·.name.text)
    let valueOutputs := (proc.outputs.filter (fun o => !inputNames.contains o.name.text)).map (·.name.text)
    let valueOutputRefs := proc.throwsOn.flatMap fun blk =>
      blk.postconditions.flatMap fun c =>
        let referenced := foldStmtExpr (fun n acc => match n.val with
          | .Var (.Local id) => if valueOutputs.contains id.text then acc.insert id.text else acc
          | _ => acc) (∅ : Std.HashSet String) c.condition
        referenced.toList.map fun name =>
          diagnosticFromSource c.condition.source
            s!"a `throwsOn` case of procedure '{displayName}' refers to the value output '{name}', which does not exist on the throwing path: a throwing procedure returns a single result whose exceptional arm carries only the thrown value"
            MessageKind.userError
    needsThrows ++ valueOutputRefs

/-- Test membership by resolved procedure identity. -/
private def containsProcId (ids : Std.HashSet Nat) (name : Identifier) : Bool :=
  match name.uniqueId with
  | some id => ids.contains id
  | none => false

/-- True when `e` reads heap state, reusing the shared heap-effect analysis so
    this stays consistent with how `HeapParameterization` classifies expressions.
    An expression reads the heap when it either accesses a composite field
    (`x#f`) directly, or calls a procedure that (transitively) reads the heap.
    The latter uses the `heapReaders` set precomputed on the `SemanticModel`, so
    e.g. `old(f(x))` is recognized as meaningful when `f` reads the heap. -/
private def containsHeapRead (heapReaders : Std.HashSet Nat) (e : StmtExprMd) : Bool :=
  let result := ((collectExprMd e).run {}).2
  result.readsHeapDirectly || result.callees.any fun c =>
    match c.uniqueId with
    | some id => heapReaders.contains id
    | none => false

/-- Reject the exception source shapes `EliminateExceptions` does not yet handle
    (each would otherwise miscompile or hit a `strata-bug`). Run from `resolve` on
    the initial resolution, alongside `validateExceptionEscapes`; `procs` is every
    procedure in the program (static plus composite instance procedures, which are
    not yet lifted at that point), and `types` is every type it declares. -/
private def validateExceptionLowerability (model : SemanticModel)
    (types : List TypeDefinition) (procs : List Procedure) : List Message :=
  -- `EliminateExceptions` prepends the `Result` datatype to a program that uses
  -- exceptions, so the name is reserved for such a program. Without this check the
  -- collision surfaces only after the pass, as a *duplicate definition* reported
  -- by the re-resolution and then a cascade of type errors against the wrong
  -- `Result` — all of them internal-error diagnostics pointing at synthesized
  -- nodes, none of them naming the user's own declaration.
  let reservedTypeErrors :=
    if procs.any procUsesExceptions then
      types.filterMap fun td =>
        if td.name.text == exnResultDatatypeName then
          some (diagnosticFromSource td.name.source
            s!"a program that uses exceptions may not declare a type named '{exnResultDatatypeName}': exception lowering injects a datatype of that name to carry a throwing procedure's outcome, and the two would collide. Rename this type."
            MessageKind.notYetImplemented)
        else none
    else []
  reservedTypeErrors ++ procs.flatMap (fun proc =>
    -- A `throwsOn` guard is defined as a *pre-state* predicate, but the lowering
    -- reads it in the post-state: `EliminateExceptions` splices the guard verbatim
    -- into the forcing claim (`C ==> Result..isBad($result)`) and into each case
    -- postcondition's antecedent, and `ModifiesClauses` splices it into the
    -- exhaustiveness disjunct — all of them postconditions, none of them wrapped
    -- to capture the pre-state. A guard over parameters alone is unaffected,
    -- because an input binding holds the same value in both states, which is why
    -- the promise has held so far. A guard that reads the heap silently means
    -- "held on exit" instead, and that is wrong in both directions: a body that
    -- clears the guarded field before throwing fails exhaustiveness even though it
    -- throws exactly when the guard held on entry, and a body that lets the guard
    -- hold on entry and then clears it *without* throwing verifies — letting a
    -- caller prove from the contract that the call throws when it does not.
    -- Reject the shape until guards are captured in the pre-state; a caller of a
    -- bodiless procedure reasons from these cases too, so this is checked on the
    -- contract rather than only where there is an implementation.
    let heapGuardErrors := proc.throwsOn.filterMap (fun blk =>
      if containsHeapRead model.heapReaders blk.guard then
        some (diagnosticFromSource blk.guard.source
          "a `throwsOn` guard that reads the heap is not yet supported: a guard is evaluated in the pre-state by definition, but the lowering reads it in the post-state, so a guard naming a field (`x#f`) or calling a heap-reading procedure would silently mean \"held on exit\". Restrict the guard to parameters."
          MessageKind.notYetImplemented)
      else none)
    let body? := match proc.body with
      | .Transparent b => some b
      | .Opaque _ (some impl) _ => some impl
      | _ => none
    heapGuardErrors ++ match body? with
    | none => []
    | some body =>
      checkPropagationEdges model (TypeLattice.ofTypes types) proc.throwsType body
      ++ (checkThrowingCallPositions model body).map (fun src =>
        diagnosticFromSource src
          "a call to a procedure that `throws` is not yet supported in this expression position; bind it to a variable first (e.g. `var t := f(); … t …`)"
          MessageKind.notYetImplemented)
      ++ (checkCatchBindingShadowing body).map (fun (src, name) =>
        diagnosticFromSource src
          s!"re-declaring the `catch` binding '{name}' inside its handler is not yet supported (it shadows the exception binding and would miscompile); rename the inner variable"
          MessageKind.notYetImplemented))

/-! ## Entry point -/

/-- Collect a "nested `old(...)` has no effect" warning for every `Old` node
    inside `operand` (the operand of an enclosing `old`). An `old` nested
    directly inside another `old` is always redundant. -/
private def nestedOldWarnings (operand : StmtExprMd) : List Message :=
  (mapStmtExprM (m := StateM (List Message))
    (fun n => do
      match n.val with
      | .Old _ =>
        modify (· ++ [diagnosticFromSource n.source "nested `old(...)` has no effect" .warning])
        pure n
      | _ => pure n)
    operand |>.run []).2

/-- True when `e` references one of `inoutNames` (an inout parameter), in which
    case `old(e)` captures the parameter's distinct pre-state and is not a no-op. -/
private def mentionsInout (inoutNames : List String) (e : StmtExprMd) : Bool :=
  anyStmtExpr (fun n => match n.val with
    | .Var (.Local name) => inoutNames.contains name.text
    | _ => false) e

/-- Collect no-op `old(...)` warnings for one procedure. `writesHeap` says
    whether the enclosing procedure (transitively) writes the heap.

    An `old(e)` is a no-op — and warned — when it captures no state that can
    differ between the pre- and post-state. That is the case when BOTH:
    - the enclosing procedure does not write the heap AND `e` references no inout
      parameter (so there is no pre/post distinction to capture), or
    - `e` reads no heap state AND references no inout parameter (so its value is
      identical pre and post).

    Inout parameters matter because their input value is the pre-state and their
    output value is the post-state (see the language definition), so `old(x)`
    over an inout `x` is meaningful regardless of heap effects.

    Additionally, any `old` nested inside another `old` is redundant. These are
    the warnings `PushOldInward` used to emit; they live here so resolution is
    the single source of user-program diagnostics. The two notions stay in sync
    because both classify "writes the heap" / "reads the heap" via the shared
    `HeapAnalysis` and inout membership via the same input/output name match. -/
private def oldWarningsForProc (heapReaders : Std.HashSet Nat) (writesHeap : Bool)
    (proc : Procedure) : List Message :=
  match procInoutNames proc with
  | .error e => [Message.fromString e .strataBug]
  | .ok inoutNames =>
  let visit (n : StmtExprMd) : StateM (List Message) (Option StmtExprMd) := do
    match n.val with
    | .Old inner =>
      -- Warn on any `old` nested within this one's operand.
      modify (· ++ nestedOldWarnings inner)
      let refsInout := mentionsInout inoutNames inner
      if !writesHeap && !refsInout then
        modify (· ++ [diagnosticFromSource n.source
          "`old(...)` has no effect: the enclosing procedure does not modify the heap" .warning])
      else if !containsHeapRead heapReaders inner && !refsInout then
        modify (· ++ [diagnosticFromSource n.source
          "`old(...)` has no effect: expression contains no heap reads" .warning])
      -- Return the node unchanged and stop further descent (nested olds were
      -- already handled above), matching `PushOldInward`'s pre-order handling.
      pure (some n)
    | _ => pure none
  (mapProcedureM (m := StateM (List Message))
    (fun e => mapStmtExprPrePostM visit pure e) proc |>.run []).2

/-- Diagnose no-op `old(...)` usage across a program. This is a property of the
    user's *source* program (it does not depend on the heap-parameterized form),
    so `resolve` runs it only on the initial resolution. Heap read/write status
    comes from the `SemanticModel`, whose `heapReaders`/`heapWriters` sets are
    computed over all procedures (static plus composite instance procedures) so
    the call-graph analysis matches `HeapParameterization`, which runs after
    instance procedures have been lifted into the static list. -/
def validateOldUsage (model : SemanticModel) (program : Program) : List Message :=
  let instanceProcs := program.types.flatMap fun
    | .Composite ct => ct.instanceProcedures
    | _ => []
  let allProcs := program.staticProcedures ++ instanceProcs
  allProcs.flatMap fun proc =>
    let writesHeap := match proc.name.uniqueId with
      | some id => model.heapWriters.contains id
      | none => false
    oldWarningsForProc model.heapReaders writesHeap proc

private structure InitialEffectAnalysis where
  allProcs : List Procedure
  globals : GlobalEffectsByProcId

private def analyzeInitialEffects (model : SemanticModel)
    (program : Program) : InitialEffectAnalysis :=
  let instanceProcs := program.types.flatMap fun
    | .Composite ct => ct.instanceProcedures
    | _ => []
  let allProcs := program.staticProcedures ++ instanceProcs
  { allProcs
    globals := computeGlobalEffectsByProcId model allProcs program.staticFields }

/-- Names containing `$` are reserved for compiler-generated variables used
    by later lowering passes. Reject them at the source boundary rather than
    risking capture or silent state corruption. -/
private def resolvedNodeName? : ResolvedNode → Option Identifier
  | .var name _ | .quantifierVar name _ | .typeParameter name => some name
  | .parameter parameter | .datatypeDestructor _ parameter => some parameter.name
  | .staticProcedure proc | .instanceProcedure _ proc => some proc.name
  | .field _ field => some field.name
  | .compositeType type => some type.name
  | .constrainedType type => some type.name
  | .datatypeDefinition type => some type.name
  | .datatypeConstructor _ constructor => some constructor.name
  | .typeAlias alias => some alias.name
  | .constant constant => some constant.name
  | .unresolved _ => none

/-- Names in compiler-generated namespaces cannot be user binders: generated
    qualified global references are re-resolved after constrained-type lowering. -/
private def validateGlobalNames (program : Program) : List Message :=
  let globalErrors := program.staticFields.filterMap fun field =>
    if field.name.text.contains '$' then
      some (diagnosticFromSource field.name.source
        s!"file-scope global name '{field.name.text}' is reserved for compiler-generated variables"
        MessageKind.userError)
    else none
  let staticOwnerErrors := program.types.filterMap fun type =>
    if type.name.text == "$static" then
      some (diagnosticFromSource type.name.source
        "type name '$static' is reserved for file-scope global variables"
        MessageKind.userError)
    else none
  let binderErrors := (buildRefToDef program).toList.filterMap fun (_, node) => do
    let name ← resolvedNodeName? node
    if !name.text.startsWith "$static." then none
    else if let .field owner _ := node then
      if owner.text == "$static" then none else some (diagnosticFromSource name.source
        s!"name '{name.text}' is reserved for compiler-generated variables"
        MessageKind.userError)
    else some (diagnosticFromSource name.source
      s!"name '{name.text}' is reserved for compiler-generated variables"
      MessageKind.userError)
  let constrainedBinderErrors := program.types.filterMap fun
    | .Constrained type =>
        if type.valueName.text.startsWith "$static." then
          some (diagnosticFromSource type.valueName.source
            s!"name '{type.valueName.text}' is reserved for compiler-generated variables"
            MessageKind.userError)
        else none
    | _ => none
  globalErrors ++ staticOwnerErrors ++ binderErrors ++ constrainedBinderErrors

/-- Reject a file-scope global with a generic (`.Applied`) type. A generic composite/datatype
    FIELD is supported by #1394 (monomorphization for composites, HeapParam `.Applied` boxing for
    datatypes), but monomorphization does not reach a global's initializer, so a generic-typed
    global would reach Core un-monomorphized. This lives in the globals validation layer (not in
    the shared `resolveField`) so `resolveField` stays identical to upstream. -/
private def validateGlobalTypes (program : Program) : List Message :=
  program.staticFields.filterMap fun field =>
    match field.type.val with
    | .Applied base _ =>
      let baseName := match base.val with | .UserDefined n => n.text | _ => "?"
      some (diagnosticFromSource field.type.source
        s!"a generic datatype instantiation ('{baseName}<…>') is not yet supported as a file-scope global type"
        MessageKind.userError)
    | _ => none

private def globalEffectIdsFor (effects : Std.HashMap Nat (Std.HashSet Nat))
    (field : Field) : Std.HashSet Nat :=
  match field.name.uniqueId with
  | some id => effects.getD id {}
  | none => {}

private def globalReaderIds (program : Program) (analysis : InitialEffectAnalysis)
    : Std.HashSet Nat :=
  program.staticFields.foldl (init := {}) fun ids field =>
    ids.union (globalEffectIdsFor analysis.globals.readers field)

private def globalWriterIds (program : Program) (analysis : InitialEffectAnalysis)
    : Std.HashSet Nat :=
  program.staticFields.foldl (init := {}) fun ids field =>
    ids.union (globalEffectIdsFor analysis.globals.writers field)

private def calleeProcedure (model : SemanticModel) (callee : Identifier)
    : Option Procedure :=
  match model.get? callee with
  | some (.staticProcedure proc) | some (.instanceProcedure _ proc) => some proc
  | _ => none

private def parameterIsInout (proc : Procedure) (parameter : Parameter) : Bool :=
  parameter.name.uniqueId.isSome &&
    proc.inputs.any (·.name.uniqueId == parameter.name.uniqueId) &&
    proc.outputs.any (·.name.uniqueId == parameter.name.uniqueId)

private def hasExplicitInout (model : SemanticModel) (callee : Identifier) : Bool :=
  (calleeProcedure model callee).any fun proc => proc.inputs.any (parameterIsInout proc)

private def ordinaryOutputCount (model : SemanticModel) (callee : Identifier) : Nat :=
  (calleeProcedure model callee).map (fun proc =>
    proc.outputs.countP fun output => !parameterIsInout proc output) |>.getD 0

private def isGlobalRef (model : SemanticModel) (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .Var (.Local name) => match model.get? name with
      | some (.field owner _) => owner.text == "$static"
      | _ => false
  | _ => false

private def containsGlobalRef (model : SemanticModel) (expr : StmtExprMd) : Bool :=
  anyStmtExpr (isGlobalRef model) expr

private def isGlobalTarget (model : SemanticModel) (target : VariableMd) : Bool :=
  match target.val with
  | .Local name => match model.get? name with
      | some (.field owner _) => owner.text == "$static"
      | _ => false
  | .Field _ _ | .Declare _ => false


private def globalDependentIds (program : Program) (analysis : InitialEffectAnalysis) : Std.HashSet Nat :=
  (globalReaderIds program analysis).union (globalWriterIds program analysis)

private def isGlobalUse (model : SemanticModel) (dependentIds : Std.HashSet Nat)
    (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .Var _ => isGlobalRef model expr
  | .Assign targets _ => targets.any (isGlobalTarget model)
  | .IncrDecr _ _ target | .CompoundAssign _ target _ => isGlobalTarget model target
  | .StaticCall callee _ | .InstanceCall _ callee _ => containsProcId dependentIds callee
  | _ => false

private def firstGlobalUseSource (model : SemanticModel) (dependentIds : Std.HashSet Nat)
    (expr : StmtExprMd) : Option FileRange :=
  (foldStmtExprM (m := StateM (Option FileRange)) (fun node => do
    if (← get).isNone && isGlobalUse model dependentIds node then
      set (some node.source)) expr |>.run none).2
/-- Constrained predicates and witnesses are compiled into helper procedures
    before global lowering; those helpers cannot acquire hidden global state. -/
private def validateConstrainedTypeGlobalUse (model : SemanticModel)
    (program : Program) (analysis : InitialEffectAnalysis) : List Message :=
  let dependentIds := globalDependentIds program analysis
  let errorsIn (expr : StmtExprMd) : List Message :=
    match firstGlobalUseSource model dependentIds expr with
    | some source => [diagnosticFromSource source
        "file-scope globals are not yet supported in constrained type predicates or witnesses"
        MessageKind.userError]
    | none => []
  program.types.flatMap fun
    | .Constrained ct => errorsIn ct.constraint ++ errorsIn ct.witness
    | _ => []

/-- Constants have no procedure context through which global lowering can thread
    hidden state, so any direct or transitive global dependency is unsupported. -/
private def validateConstantInitializerGlobalUse (model : SemanticModel)
    (program : Program) (analysis : InitialEffectAnalysis) : List Message :=
  let dependentIds := globalDependentIds program analysis
  program.constants.filterMap fun constant => do
    let initializer ← constant.initializer
    let source ← firstGlobalUseSource model dependentIds initializer
    some (diagnosticFromSource source
      s!"constant initializer '{constant.name.text}' cannot depend on file-scope globals"
      MessageKind.userError)


/-- Visit each expression node exactly once while tracking whether it occurs in
    a contract-like context. Loop conditions and annotations, quantifiers, and
    `old` operands become restricted; ordinary loop bodies retain their
    surrounding context. -/
private def foldRestrictedStmtExprM [Monad m]
    (f : Bool → StmtExprMd → m Unit) (restricted : Bool)
    (expr : StmtExprMd) : m Unit := do
  f restricted expr
  match _h : expr.val with
  | .IfThenElse cond th el =>
    foldRestrictedStmtExprM f restricted cond; foldRestrictedStmtExprM f restricted th
    el.attach.forM fun ⟨e, _⟩ => foldRestrictedStmtExprM f restricted e
  | .Block stmts _ =>
    stmts.attach.forM fun ⟨e, _⟩ => foldRestrictedStmtExprM f restricted e
  | .While cond invs dec body _ =>
    foldRestrictedStmtExprM f true cond
    invs.attach.forM fun ⟨e, _⟩ => foldRestrictedStmtExprM f true e
    dec.attach.forM fun ⟨e, _⟩ => foldRestrictedStmtExprM f true e
    foldRestrictedStmtExprM f restricted body
  | .Return value => value.attach.forM fun ⟨e, _⟩ => foldRestrictedStmtExprM f restricted e
  | .Assign targets value =>
    targets.attach.forM fun ⟨target, _⟩ => match target with
      | ⟨.Field receiver _, _⟩ => foldRestrictedStmtExprM f restricted receiver
      | ⟨.Local _, _⟩ | ⟨.Declare _, _⟩ => pure ()
    foldRestrictedStmtExprM f restricted value
  | .Var (.Field target _) => foldRestrictedStmtExprM f restricted target
  | .IncrDecr _ _ target => match target with
    | ⟨.Field receiver _, _⟩ => foldRestrictedStmtExprM f restricted receiver
    | ⟨.Local _, _⟩ | ⟨.Declare _, _⟩ => pure ()
  | .CompoundAssign _ target rhs =>
    match target with
    | ⟨.Field receiver _, _⟩ => foldRestrictedStmtExprM f restricted receiver
    | ⟨.Local _, _⟩ | ⟨.Declare _, _⟩ => pure ()
    foldRestrictedStmtExprM f restricted rhs
  | .PureFieldUpdate target _ value => foldRestrictedStmtExprM f restricted target; foldRestrictedStmtExprM f restricted value
  | .StaticCall _ args =>
    args.attach.forM fun ⟨e, _⟩ => foldRestrictedStmtExprM f restricted e
  | .ReferenceEquals lhs rhs => foldRestrictedStmtExprM f restricted lhs; foldRestrictedStmtExprM f restricted rhs
  | .AsType target _ => foldRestrictedStmtExprM f restricted target
  | .IsType target _ => foldRestrictedStmtExprM f restricted target
  | .InstanceCall target _ args =>
    foldRestrictedStmtExprM f restricted target
    args.attach.forM fun ⟨e, _⟩ => foldRestrictedStmtExprM f restricted e
  | .Quantifier _ _ trigger body =>
    trigger.attach.forM fun ⟨e, _⟩ => foldRestrictedStmtExprM f true e
    foldRestrictedStmtExprM f true body
  | .Assigned name => foldRestrictedStmtExprM f restricted name
  | .Fresh name => foldRestrictedStmtExprM f restricted name
  | .Old value => foldRestrictedStmtExprM f true value
  | .Assert cond _ => foldRestrictedStmtExprM f true cond
  | .Assume cond => foldRestrictedStmtExprM f true cond
  | .Throw value => foldRestrictedStmtExprM f restricted value
  | .Try body catches finally? =>
    foldRestrictedStmtExprM f restricted body
    catches.attach.forM fun ⟨clause, _⟩ => do
      clause.predicate.attach.forM fun ⟨predicate, _⟩ =>
        foldRestrictedStmtExprM f true predicate
      foldRestrictedStmtExprM f restricted clause.body
    finally?.attach.forM fun ⟨body, _⟩ => foldRestrictedStmtExprM f restricted body
  | .ProveBy value proof =>
    foldRestrictedStmtExprM f restricted value
    foldRestrictedStmtExprM f true proof
  | .ContractOf _ func => foldRestrictedStmtExprM f restricted func
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _
  | .LiteralDecimal _ | .LiteralBv _ _ | .Var (.Local _)
  | .Var (.Declare _) | .New .. | .This | .Abstract | .All | .Hole .. => pure ()
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try have := CatchClause.sizeOf_body_lt ‹_›)
  all_goals (try have := CatchClause.sizeOf_predicate_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals (revert expr; intro x; cases x; simp_all; omega)

/-- Collect values from nodes on expression result paths. Discarded block
    prefixes, conditions, triggers, and proof expressions are not result paths. -/
private def collectResultPathStmtExprList {β : Type} (f : StmtExprMd → List β)
    (expr : StmtExprMd) : List β :=
  match _h : expr.val with
  | .Block stmts _ =>
      match stmts.attach.getLast? with
      | some ⟨result, _hmem⟩ => collectResultPathStmtExprList f result
      | none => []
  | .IfThenElse _ thenBranch elseBranch =>
      let thenResults := collectResultPathStmtExprList f thenBranch
      match elseBranch with
      | some elseExpr => thenResults ++ collectResultPathStmtExprList f elseExpr
      | none => thenResults
  | .ProveBy value _ => collectResultPathStmtExprList f value
  | .Old value => collectResultPathStmtExprList f value
  | .Fresh value => collectResultPathStmtExprList f value
  | .Assigned value => collectResultPathStmtExprList f value
  | .AsType value _ => collectResultPathStmtExprList f value
  | .Assign _ value | .CompoundAssign _ _ value | .Throw value =>
      collectResultPathStmtExprList f value
  | .Try body catches _ =>
      collectResultPathStmtExprList f body ++ catches.attach.flatMap fun ⟨clause, _⟩ =>
        collectResultPathStmtExprList f clause.body
  | _ => f expr
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try have := CatchClause.sizeOf_body_lt ‹_›)
  all_goals (try have := CatchClause.sizeOf_predicate_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals (revert expr; intro x; cases x; simp_all; omega)

private structure GlobalCallValidationContext where
  model : SemanticModel
  writerIds : Std.HashSet Nat
  dependentIds : Std.HashSet Nat

private def containsArgumentMutation (ctx : GlobalCallValidationContext)
    (expr : StmtExprMd) : Bool :=
  anyStmtExpr (fun node => match node.val with
    | .Assign _ _ | .IncrDecr _ _ _ | .CompoundAssign _ _ _ => true
    | .StaticCall callee _ | .InstanceCall _ callee _ =>
        containsProcId ctx.writerIds callee || hasExplicitInout ctx.model callee
    | _ => false) expr

private def passesGlobalToInout (ctx : GlobalCallValidationContext)
    (callee : Identifier) (args : List StmtExprMd) : Bool :=
  (calleeProcedure ctx.model callee).any fun proc =>
    (proc.inputs.zip args).any fun (parameter, arg) =>
      parameterIsInout proc parameter && containsGlobalRef ctx.model arg

private def isVariableActual (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .Var (.Local _) | .Block [⟨.Var (.Local _), _⟩] _ => true
  | _ => false

private def hasInvalidInoutActual (ctx : GlobalCallValidationContext)
    (callee : Identifier) (args : List StmtExprMd) : Bool :=
  (calleeProcedure ctx.model callee).any fun proc =>
    (proc.inputs.zip args).any fun (parameter, arg) =>
      parameterIsInout proc parameter && !isVariableActual arg

private abbrev GlobalValidationM := StateM (List Message)

private def validateGlobalCall (ctx : GlobalCallValidationContext) (restricted : Bool)
    (callee : Identifier) (args : List StmtExprMd) : GlobalValidationM Unit := do
  let dependsOnGlobal := containsProcId ctx.dependentIds callee
  let writesGlobal := containsProcId ctx.writerIds callee
  let explicitInout := hasExplicitInout ctx.model callee
  let mutatingGlobalInout :=
    !writesGlobal && dependsOnGlobal && explicitInout && args.any (containsArgumentMutation ctx)
  if dependsOnGlobal && hasInvalidInoutActual ctx callee args && !mutatingGlobalInout then
    modify (· ++ [diagnosticFromSource callee.source
      s!"explicit inout arguments to '{callee.text}' must be variable references"
      MessageKind.userError])
  if passesGlobalToInout ctx callee args then
    modify (· ++ [diagnosticFromSource callee.source
      s!"passing file-scope globals to explicit inout parameters of '{callee.text}' is not yet supported"
      MessageKind.userError])
  if writesGlobal then
    if explicitInout then
      modify (· ++ [diagnosticFromSource callee.source
        s!"calls to global-writing procedure '{callee.text}' with explicit inout outputs are not yet supported"
        MessageKind.userError])
    else if restricted then
      modify (· ++ [diagnosticFromSource callee.source
        s!"calls to global-writing procedure '{callee.text}' are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions"
        MessageKind.userError])
  if mutatingGlobalInout then
    modify (· ++ [diagnosticFromSource callee.source
      s!"mutating arguments to global-dependent procedure '{callee.text}' with explicit inout outputs are not yet supported"
      MessageKind.userError])

private def blockTupleCall (ctx : GlobalCallValidationContext)
    (expr : StmtExprMd) : Option Identifier :=
  match expr.val with
  | .Block _ _ | .IfThenElse _ _ _ | .ProveBy _ _ | .Old _ | .Fresh _
  | .Assigned _ | .AsType _ _ | .Assign _ _ | .CompoundAssign _ _ _ =>
      (collectResultPathStmtExprList (fun node => match node.val with
        | .StaticCall callee _ | .InstanceCall _ callee _ => [callee]
        | _ => []) expr).find? fun callee =>
          containsProcId ctx.dependentIds callee &&
            ordinaryOutputCount ctx.model callee > 1
  | _ => none

private def effectfulTupleCall (ctx : GlobalCallValidationContext)
    (expr : StmtExprMd) : Option Identifier :=
  let candidate := match expr.val with
    | .StaticCall callee args => some (callee, args)
    | .InstanceCall target callee args => some (callee, target :: args)
    | _ => none
  candidate.bind fun (callee, args) =>
    if containsProcId ctx.dependentIds callee &&
        ordinaryOutputCount ctx.model callee > 1 &&
        args.any (containsArgumentMutation ctx)
    then some callee else none

private def tupleCallNeedingBlock (ctx : GlobalCallValidationContext)
    (expr : StmtExprMd) : Option Identifier :=
  (blockTupleCall ctx expr).orElse fun _ => effectfulTupleCall ctx expr

private def globalCallErrors (ctx : GlobalCallValidationContext)
    (initialRestricted : Bool) (expr : StmtExprMd) : List Message :=
  let mutationError (source : FileRange) : GlobalValidationM Unit :=
    modify (· ++ [diagnosticFromSource source
      "global mutations are not yet supported in contracts, loop conditions or annotations, quantifiers, or old expressions"
      MessageKind.userError])
  (foldRestrictedStmtExprM (m := GlobalValidationM)
    (fun restricted node => do
      match node.val with
      | .StaticCall callee args => validateGlobalCall ctx restricted callee args
      | .InstanceCall target callee args =>
          validateGlobalCall ctx restricted callee (target :: args)
      | .Assign targets rhs => do
          if targets.length > 1 then
            if let some callee := tupleCallNeedingBlock ctx rhs then
              modify (· ++ [diagnosticFromSource callee.source
                s!"multi-output calls to global-dependent procedure '{callee.text}' that require block-valued lowering are not yet supported"
                MessageKind.userError])
          if restricted && targets.any (isGlobalTarget ctx.model) then mutationError node.source
      | .IncrDecr _ _ target | .CompoundAssign _ target _ =>
          if restricted && isGlobalTarget ctx.model target then mutationError node.source
      | _ => pure ()) initialRestricted expr |>.run []).2

private def resultUseGlobalCallErrors (ctx : GlobalCallValidationContext)
    (expr : StmtExprMd) : List Message :=
  let tupleLocations := collectStmtExprList (fun node => match node.val with
    | .Assign targets rhs =>
        if targets.length > 1 then
          match tupleCallNeedingBlock ctx rhs with
          | some callee => if containsProcId ctx.writerIds callee then [callee.source] else []
          | none => []
        else []
    | _ => []) expr
  (mapStmtExprUsedM (m := GlobalValidationM) (fun resultUsed node => do
    match node.val with
    | .StaticCall callee _ | .InstanceCall _ callee _ =>
        if resultUsed then
          if containsProcId ctx.writerIds callee &&
              ordinaryOutputCount ctx.model callee > 1 &&
              !tupleLocations.contains callee.source then
            modify (· ++ [diagnosticFromSource callee.source
              s!"calls to global-writing procedure '{callee.text}' with more than one ordinary output are not yet supported"
              MessageKind.userError])
        else if containsProcId ctx.dependentIds callee && hasExplicitInout ctx.model callee then
          modify (· ++ [diagnosticFromSource callee.source
            s!"bare calls to global-dependent procedure '{callee.text}' with explicit inout outputs are not yet supported"
            MessageKind.userError])
    | _ => pure ()
    return node) false expr |>.run []).2

private def contractExpressions (proc : Procedure) : List StmtExprMd :=
  proc.preconditions.map (·.condition) ++ proc.decreases.toList ++
    proc.invokeOn.toList ++ proc.axioms ++ match proc.body with
    | .Opaque postconditions _ modifies =>
      postconditions.map (·.condition) ++
        modifies.flatMap (fun g => g.targets ++ g.guard.toList)
    | .Abstract postconditions => postconditions.map (·.condition)
    | .Transparent _ | .External => []

private def bodyExpressions (proc : Procedure) : List StmtExprMd :=
  match proc.body with
  | .Transparent body => [body]
  | .Opaque _ implementation _ => implementation.toList
  | .Abstract _ | .External => []

/-- Reject `old(...)` operands that directly or transitively depend on globals. -/
private def oldGlobalErrorsInExpr (model : SemanticModel)
    (dependentIds : Std.HashSet Nat) (expr : StmtExprMd) : List Message :=
  let visit (node : StmtExprMd) : StateM (List Message) (Option StmtExprMd) := do
    if let .Old operand := node.val then
      if let some source := firstGlobalUseSource model dependentIds operand then
        modify (· ++ [diagnosticFromSource source
          "file-scope globals are not yet supported inside `old(...)`"
          MessageKind.userError])
      return some node
    return none
  (mapStmtExprPrePostM (m := StateM (List Message)) visit pure expr |>.run []).2

/-- Reject call shapes that cannot preserve global state and source evaluation
    order during parameterization. -/
private def validateUnsupportedGlobalCalls (model : SemanticModel)
    (program : Program) (analysis : InitialEffectAnalysis) : List Message :=
  let writerIds := globalWriterIds program analysis
  let dependentIds := writerIds.union (globalReaderIds program analysis)
  let ctx : GlobalCallValidationContext := { model, writerIds, dependentIds }
  let errorsIn (restricted checkUsedResults : Bool) (expr : StmtExprMd) :=
    let oldErrors := oldGlobalErrorsInExpr model dependentIds expr
    if !oldErrors.isEmpty then oldErrors
    else globalCallErrors ctx restricted expr ++
      if checkUsedResults then resultUseGlobalCallErrors ctx expr else []
  analysis.allProcs.flatMap fun proc =>
    (contractExpressions proc).flatMap (errorsIn true false) ++
      (bodyExpressions proc).flatMap (errorsIn false true)


/-- Without an implementation there is no source statement from which to infer
    whether a postcondition's global denotes a write. Reject that ambiguous
    post-state contract instead of silently lowering it as an input-only read. -/
private def validateBodilessGlobalPostconditions (model : SemanticModel)
    (program : Program) (analysis : InitialEffectAnalysis) : List Message :=
  let dependentIds := globalDependentIds program analysis
  let usesGlobal (expr : StmtExprMd) : Bool :=
    anyStmtExpr (fun node => match node.val with
      | .Var _ => isGlobalRef model node
      | .StaticCall callee _ | .InstanceCall _ callee _ =>
          containsProcId dependentIds callee
      | _ => false) expr
  let isOutputRef (proc : Procedure) (expr : StmtExprMd) : Bool :=
    match expr.val with
    | .Var (.Local name) => proc.outputs.any (·.name.uniqueId == name.uniqueId)
    | _ => false
  let containsOutputRef (proc : Procedure) (expr : StmtExprMd) : Bool :=
    anyStmtExpr (fun node => isOutputRef proc node) expr
  let definesOutputFromGlobal (proc : Procedure) (expr : StmtExprMd) : Bool :=
    match expr.val with
    | .StaticCall callee [lhs, rhs] =>
        callee.text == Operation.Eq.procName &&
          ((isOutputRef proc lhs && usesGlobal rhs && !containsOutputRef proc rhs) ||
           (isOutputRef proc rhs && usesGlobal lhs && !containsOutputRef proc lhs))
    | _ => false
  let writerIds := program.staticFields.foldl (init := {}) fun ids field =>
    ids.union (globalEffectIdsFor analysis.globals.writers field)
  let hasWriterCall (expr : StmtExprMd) : Bool :=
    anyStmtExpr (fun node => match node.val with
      | .StaticCall callee _ | .InstanceCall _ callee _ =>
          containsProcId writerIds callee
      | _ => false) expr
  analysis.allProcs.filterMap fun proc =>
    let postconditions := match proc.body with
      | .Opaque posts none _ => posts
      | .Abstract posts => posts
      | .Opaque _ (some _) _ | .Transparent _ | .External => []
    postconditions.find? (fun post =>
      usesGlobal post.condition && !definesOutputFromGlobal proc post.condition &&
        !hasWriterCall post.condition) |>.map fun post =>
      diagnosticFromSource post.condition.source
        s!"global references in postconditions of procedure '{proc.name.text}' without an implementation are not yet supported"
        MessageKind.userError

private def firstInitializerEffectSource (model : SemanticModel)
    (expr : StmtExprMd) : Option FileRange :=
  let isEffect (node : StmtExprMd) : Bool :=
    match node.val with
    | .Assign _ _ | .IncrDecr _ _ _ | .CompoundAssign _ _ _
    | .Var (.Declare _) => true
    | .StaticCall callee _ | .InstanceCall _ callee _ =>
        containsProcId model.heapReaders callee || containsProcId model.heapWriters callee
    | _ => false
  (foldStmtExprM (m := StateM (Option FileRange)) (fun node => do
    if (← get).isNone && isEffect node then
      set (some node.source)) expr |>.run none).2

private def validateGlobalInitializers (model : SemanticModel)
    (program : Program) (analysis : InitialEffectAnalysis) : List Message :=
  let dependentIds := globalDependentIds program analysis
  program.staticFields.flatMap fun field =>
    match field.initializer with
    | none => [diagnosticFromSource field.name.source
        s!"file-scope global '{field.name.text}' must declare an initializer: 'var {field.name.text}: <type> := <value>'"
        MessageKind.userError]
    | some initializer =>
      (match firstGlobalUseSource model dependentIds initializer with
        | some source => [diagnosticFromSource source
            s!"the initializer of file-scope global '{field.name.text}' cannot depend on file-scope globals"
            MessageKind.userError]
        | none => []) ++
      (match firstInitializerEffectSource model initializer with
        | some source => [diagnosticFromSource source
            s!"the initializer of file-scope global '{field.name.text}' must be effect-free (no assignments or declarations, and no calls to heap-reading or heap-writing procedures)"
            MessageKind.userError]
        | none => [])

private def entryUsedGlobals (program : Program) (analysis : InitialEffectAnalysis)
    (proc : Procedure) : List Field :=
  program.staticFields.filter fun field =>
    containsProcId (globalEffectIdsFor analysis.globals.readers field) proc.name ||
    containsProcId (globalEffectIdsFor analysis.globals.writers field) proc.name

private def entryContractExpressions (proc : Procedure) : List StmtExprMd :=
  contractExpressions proc ++ proc.throwsOn.flatMap fun blk =>
    blk.guard :: (blk.postconditions.map (·.condition) ++ blk.modifies)

private def validateEntryContractGlobalUse (model : SemanticModel)
    (program : Program) (analysis : InitialEffectAnalysis) : List Message :=
  let dependentIds := globalDependentIds program analysis
  analysis.allProcs.flatMap fun proc =>
    if !proc.isInterpretEntry then [] else
    (entryContractExpressions proc).filterMap fun expr => do
      let source ← firstGlobalUseSource model dependentIds expr
      some (diagnosticFromSource source
        s!"the contract of entry procedure '{proc.name.text}' cannot use file-scope globals: an entry procedure initializes its globals as locals inside its body, which contracts cannot see"
        MessageKind.userError)

private def validateCallsToGlobalEntryProcedures (program : Program)
    (analysis : InitialEffectAnalysis) : List Message :=
  let globalEntryIds : Std.HashSet Nat :=
    analysis.allProcs.foldl (init := {}) fun ids proc =>
      if proc.isInterpretEntry && !(entryUsedGlobals program analysis proc).isEmpty then
        match proc.name.uniqueId with
        | some id => ids.insert id
        | none => ids
      else ids
  if globalEntryIds.isEmpty then [] else
  let errorsIn (expr : StmtExprMd) : List Message :=
    collectStmtExprList (fun node => match node.val with
      | .StaticCall callee _ | .InstanceCall _ callee _ =>
        if containsProcId globalEntryIds callee then
          [diagnosticFromSource node.source
            s!"entry procedure '{callee.text}' cannot be called here: it uses file-scope globals, which it initializes as locals rather than accepting as the hidden parameters this call would pass"
            MessageKind.userError]
        else []
      | _ => []) expr
  analysis.allProcs.flatMap fun proc =>
    (entryContractExpressions proc ++ bodyExpressions proc).flatMap errorsIn

private def validateEntryConstrainedGlobalUse (program : Program)
    (analysis : InitialEffectAnalysis) : List Message :=
  let constrainedNames : Std.HashSet String :=
    program.types.foldl (init := {}) fun names td =>
      match td with
      | .Constrained ct => names.insert ct.name.text
      | _ => names
  if constrainedNames.isEmpty then [] else
  let isConstrained (field : Field) : Bool :=
    match field.type.val with
    | .UserDefined name => constrainedNames.contains name.text
    | _ => false
  analysis.allProcs.filterMap fun proc =>
    if !proc.isInterpretEntry then none else
    let constrained := (entryUsedGlobals program analysis proc).filter isConstrained
    constrained.head?.map fun field =>
      diagnosticFromSource proc.name.source
        s!"entry procedure '{proc.name.text}' cannot use constrained-typed global '{field.name.text}': the global's type constraint is enforced through hidden-parameter contracts, which entry procedures do not receive"
        MessageKind.userError

/-- An `invokeOn` procedure may not declare outputs: the auto-invocation axiom
    `ContractPass` generates is quantified over the procedure's inputs only, so an
    output would be unbound. Reported here so resolution stays the single source
    of user-program diagnostics. Composite instance procedures are included
    because this runs at initial resolution, before `LiftInstanceProcedures`
    moves them into the static list — the old post-lift `ContractPass` check saw
    them, so scanning static procedures only would miss an instance `invokeOn`
    procedure with an output. -/
def validateInvokeOnOutputRefs (program : Program) : List Message :=
  let instanceProcs := program.types.flatMap fun
    | .Composite ct => ct.instanceProcedures
    | _ => []
  (program.staticProcedures ++ instanceProcs).filterMap fun proc =>
    if proc.invokeOn.isSome && !proc.outputs.isEmpty then
      some (diagnosticFromSource proc.name.source
        s!"'invokeOn' procedure '{proc.name.text}' may not have output parameters; the auto-invocation axiom is quantified over inputs only."
        MessageKind.userError)
    else none

/-- Effective output count of a procedure, counting the implicit heap output a
    heap-writing procedure gains during heap parameterization: a writer gains a
    `$heap` output (`HeapParameterization` inserts it after existing inouts), so
    its effective output count is
    one more than declared. A procedure is "multi-output" when this count is
    ≥ 2 — which is exactly when it cannot be lowered to a single-output Core
    *function* and so cannot (yet) be called from a transparent body or a
    contract.

    `heapWriters` is keyed by resolution `uniqueId` (from `SemanticModel`),
    not name text, so a heap-writing `A.foo` does not contaminate a same-named
    pure `B.foo` in another composite. -/
private def effectiveOutputCount (heapWriters : Std.HashSet Nat)
    (proc : Procedure) : Except String Nat := do
  let id ← Identifier.getUniqueId proc.name
  let writesHeap := heapWriters.contains id
  pure (proc.outputs.length + (if writesHeap then 1 else 0))

/-- Every callee referenced by a `StaticCall`/`InstanceCall` anywhere in `e`,
    in pre-order, paired with the source range of the whole call node (so a
    diagnostic points at the call site). Both call forms carry the callee's
    resolved `uniqueId` (an `InstanceCall`'s is stamped from the container-scoped
    lookup — see `Synth.instanceCall`), which `validateMultiOutputCallContexts`
    uses to resolve the callee to its correctly-scoped procedure. -/
private def calleesOf (e : StmtExprMd) : List (Identifier × FileRange) :=
  collectStmtExprList (fun n => match n.val with
    | .StaticCall callee _ => [(callee, n.source)]
    | .InstanceCall _ callee _ => [(callee, n.source)]
    | _ => []) e

/-- The expressions of a procedure that end up in a transparent body or a
    contract — the two contexts a multi-output call may not (yet) appear in.

    - A `.Transparent` body's whole implementation is transparent (the
      `TransparencyPass` derives a pure `$asFunction` copy of it).
    - Preconditions, postconditions, the `decreases` measure, and the `invokeOn`
      trigger are contract expressions (the `ContractPass` translates
      pre/postconditions into `$pre`/`$post` helpers, and calls inside them are
      redirected to pure `$asFunction` twins).

    An `.Opaque` body's *implementation* is deliberately excluded: it is ordinary
    imperative code (verified as a procedure), so it may call multi-output
    procedures via multi-assignment. Its postconditions are still contracts and
    are included.

    `.Abstract` bodies have no implementation, only postconditions — those are
    contracts and are included. `.External` bodies have neither implementation
    nor postconditions, so nothing is collected. -/
private def restrictedContextExprs (proc : Procedure) : List StmtExprMd :=
  let bodyExprs := match proc.body with
    | .Transparent b => [b]
    | .Opaque posts _impl _mods => posts.map (·.condition)
    | .Abstract posts => posts.map (·.condition)
    | .External => []
  procedureSpecificationExprs proc ++ bodyExprs

/-- Reject calling a multi-output procedure from a transparent procedure or a
    contract. A Core *function* has exactly one output, so a multi-output
    procedure (one declaring ≥ 2 outputs, or a heap writer, which gains an
    implicit `$heap` output — see `effectiveOutputCount`) cannot be lowered to
    the pure `$asFunction` twin that transparent bodies and contracts are
    translated against. Until that is supported, such a call is a user error.

    Only calls in a transparent body or a contract expression are flagged (see
    `restrictedContextExprs`); calls from ordinary opaque implementations are
    fine. Composite instance procedures are included because this runs at
    initial resolution, before `LiftInstanceProcedures` moves them into the
    static list.

    Callees are resolved through the `SemanticModel`'s `refToDef` map by their
    `uniqueId`, so `self#foo()` resolves to the `foo` of the receiver's
    composite — not whichever same-named `foo` a text keying happened to pick.
    Combined with the `uniqueId`-keyed heap-writer set (`model.heapWriters`),
    this makes the check composite-scope correct: no false positive from another
    composite's multi-output `foo`, and no false negative from another
    composite's single-output `foo`. -/
private def validateMultiOutputCallContexts (model : SemanticModel)
    (program : Program) : List Message :=
  let instanceProcs := program.types.flatMap fun
    | .Composite ct => ct.instanceProcedures
    | _ => []
  let allProcs := program.staticProcedures ++ instanceProcs
  let heapWriters := model.heapWriters
  allProcs.flatMap fun proc =>
    (restrictedContextExprs proc).flatMap fun e =>
      (calleesOf e).filterMap fun (callee, callSource) =>
        -- Resolve the callee to its scoped procedure via `refToDef` (keyed by
        -- the `uniqueId` the resolved call site carries), not by name text.
        match model.get? callee with
        | some (.staticProcedure callee')
        | some (.instanceProcedure _ callee') =>
          match effectiveOutputCount heapWriters callee' with
          | .error e => some (Message.fromString
              s!"Internal error: effectiveOutputCount: {e}" .strataBug)
          | .ok count =>
            if count ≥ 2 then
              some (diagnosticFromSource callSource
                s!"calling multi-output procedure '{callee.text}' is not (yet) supported from a transparent procedure or contract"
                MessageKind.userError)
            else none
        | _ => none

/-- Diagnostics for `Declare` nodes at `n` whose type annotation is still
    `none`. Declarations occur in four positions: as a standalone `Var`
    statement, as an `Assign` target, and (per the AST, though not the
    surface syntax) as an `IncrDecr` or `CompoundAssign` target.
    Public so `ResolutionProps` can state per-node cleanliness lemmas. -/
def unannotatedDeclares (n : StmtExprMd) : List Message :=
  let bug (source : FileRange) (name : Identifier) : Message :=
    diagnosticFromSource source
      s!"declaration of '{name.text}' left resolution without a type annotation; resolution rewrites every declaration to carry an explicit type"
      .strataBug
  match n.val with
  | .Var (.Declare ⟨name, none⟩) => [bug n.source name]
  | .Assign targets _ => targets.filterMap fun
      | ⟨.Declare ⟨name, none⟩, src⟩ => some (bug src name)
      | _ => none
  | .IncrDecr _ _ ⟨.Declare ⟨name, none⟩, src⟩ => [bug src name]
  | .CompoundAssign _ ⟨.Declare ⟨name, none⟩, src⟩ _ => [bug src name]
  | _ => []

/-- Enforce the post-resolution invariant that every variable declaration
    carries a type annotation (see the Var-Declare and Decl-Synth rules:
    resolution fills in `some T` for every `Declare` it sees — synthesized
    from the initializer, or `Unknown` plus a user diagnostic for a bare
    `var x` — so no `none` annotation survives). A surviving `none` is a
    Strata bug, not a user error: downstream passes match on
    `Declare ⟨_, some ty⟩` (e.g. `ConstrainedTypeElim.elimNode`) and would
    silently skip an unannotated declaration. Runs on every resolution, so
    the pipeline's re-resolves after each lowering pass also catch a pass
    that constructs an unannotated declaration. -/
def validateFullyAnnotated (program : Program) : List Message :=
  let instanceProcs := program.types.flatMap fun
    | .Composite ct => ct.instanceProcedures
    | _ => []
  -- `mapProcedureM` enumerates every expression tree in a procedure
  -- (preconditions, decreases, body, invokeOn, axioms).
  let procDiags (proc : Procedure) : List Message :=
    (mapProcedureM (m := StateM (List Message))
      (fun e => do modify (· ++ collectStmtExprList unannotatedDeclares e); pure e)
      proc |>.run []).2
  let typeDiags := program.types.flatMap fun
    | .Constrained ct =>
      collectStmtExprList unannotatedDeclares ct.constraint
        ++ collectStmtExprList unannotatedDeclares ct.witness
    | _ => []
  let constantDiags := program.constants.flatMap fun c =>
    c.initializer.toList.flatMap (collectStmtExprList unannotatedDeclares)
  let staticFieldDiags := program.staticFields.flatMap fun f =>
    f.initializer.toList.flatMap (collectStmtExprList unannotatedDeclares)
  (program.staticProcedures ++ instanceProcs).flatMap procDiags
    ++ typeDiags ++ constantDiags ++ staticFieldDiags

/-- A global-writing `invokeOn` needs an unbound hidden output unless its trigger
    already invokes a writer, which source validation rejects separately. -/
private def validateInvokeOnGlobalWrites (program : Program)
    (analysis : InitialEffectAnalysis) : List Message :=
  let writerIds := globalWriterIds program analysis
  let invokeOnCallsWriter (proc : Procedure) : Bool := proc.invokeOn.any fun trigger =>
    anyStmtExpr (fun node => match node.val with
      | .StaticCall callee _ | .InstanceCall _ callee _ => containsProcId writerIds callee
      | _ => false) trigger
  analysis.allProcs.filterMap fun proc =>
    if proc.invokeOn.isNone || !proc.outputs.isEmpty || invokeOnCallsWriter proc then none
    else if containsProcId writerIds proc.name then
      some (diagnosticFromSource proc.name.source
        s!"global-writing 'invokeOn' procedure '{proc.name.text}' is not yet supported because its generated axiom cannot bind the hidden global output state"
        MessageKind.userError)
    else none

/-- Run the full resolution pass on a Laurel program. -/
public def resolve (program : Program) (existingModel: Option SemanticModel := none)
    (gradualTypes : Std.HashSet String := {})
    (realizeCoercion : Option (Coercion → StmtExprMd → StmtExprMd) := none)
    (toBool : Option (HighType → StmtExprMd → StmtExprMd) := none)
    (reservedNames : Std.HashSet String := {}) : ResolutionResult :=
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
  let typeLattice := { TypeLattice.ofTypes program.types with
    gradualTypes := gradualTypes, realizeCoercion := realizeCoercion, toBool := toBool,
    reservedNames := reservedNames }
  let (program', finalState) := phase1.run { nextId := nextId, typeLattice }
  -- Phase 2: build refToDef from the resolved program (all definitions now have UUIDs)
  let refToDef := buildRefToDef program'
  -- Heap-effect classification over all procedures (static plus composite
  -- instance procedures), so the call-graph analysis matches
  -- `HeapParameterization`, which runs after instance procedures are lifted.
  let allProcs := program'.staticProcedures ++ program'.types.flatMap fun
    | .Composite ct => ct.instanceProcedures
    | _ => []
  let heapReadersResult := computeReadsHeap allProcs
  let heapWritersResult := computeWritesHeap allProcs
  let heapReaders := heapReadersResult.toOption.getD {}
  let heapWriters := heapWritersResult.toOption.getD {}
  let semanticModel := {
    compositeCount := program.types.length,
    refToDef := refToDef,
    nextId := finalState.nextId,
    heapReaders := heapReaders
    heapWriters := heapWriters
    conflictingOverloads := finalState.conflictingOverloads
  }
  let heapAnalysisErrors : Array Message :=
    (match heapReadersResult with
      | .error e => #[Message.fromString s!"Internal error: computeReadsHeap: {e}" .strataBug]
      | .ok _ => #[]) ++
    (match heapWritersResult with
      | .error e => #[Message.fromString s!"Internal error: computeWritesHeap: {e}" .strataBug]
      | .ok _ => #[])
  let diamondErrors := validateDiamondFieldAccesses semanticModel program'
  let initialAnalysis :=
    if existingModel.isNone then some (analyzeInitialEffects semanticModel program') else none
  -- No-op `old(...)` warnings only model heap and explicit inout state. Global
  -- dependencies are rejected separately by `validateUnsupportedGlobalCalls`.
  let oldUsageWarnings :=
    if existingModel.isNone && program'.staticFields.isEmpty then
      validateOldUsage semanticModel program'
    else []
  let globalNameErrors :=
    if existingModel.isNone then validateGlobalNames program' else []
  let globalTypeErrors :=
    if existingModel.isNone then validateGlobalTypes program' else []
  let constrainedGlobalErrors :=
    initialAnalysis.map (validateConstrainedTypeGlobalUse semanticModel program') |>.getD []
  let constantGlobalErrors :=
    initialAnalysis.map (validateConstantInitializerGlobalUse semanticModel program') |>.getD []
  let globalCallErrors :=
    initialAnalysis.map (validateUnsupportedGlobalCalls semanticModel program') |>.getD []
  let bodilessGlobalErrors :=
    initialAnalysis.map (validateBodilessGlobalPostconditions semanticModel program') |>.getD []
  let globalInitializerErrors :=
    initialAnalysis.map (validateGlobalInitializers semanticModel program') |>.getD []
  let entryGlobalErrors :=
    initialAnalysis.map (fun analysis =>
      validateEntryContractGlobalUse semanticModel program' analysis ++
      validateCallsToGlobalEntryProcedures program' analysis ++
      validateEntryConstrainedGlobalUse program' analysis) |>.getD []
  -- `invokeOn` procedures may not declare outputs (see `validateInvokeOnOutputRefs`).
  -- Only on the initial resolution, since `ContractPass` clears `invokeOn`.
  let invokeOnErrors : Array Message :=
    match initialAnalysis with
    | some analysis => (validateInvokeOnOutputRefs program' ++
        validateInvokeOnGlobalWrites program' analysis).toArray
    | none => #[]
  -- Multi-output procedures cannot (yet) be called from a transparent body or a
  -- contract (see `validateMultiOutputCallContexts`). This is a property of the
  -- user's *source* program, phrased against the pre-lowering shape (transparent
  -- bodies, contracts, and pre-heap-parameterization output arity augmented by
  -- the heap-writer set), so it runs only on the initial resolution — later
  -- passes rewrite these constructs into forms this check is not phrased against.
  let multiOutputCallErrors :=
    if existingModel.isNone then
      validateMultiOutputCallContexts semanticModel program'
    else []
  -- Every declaration must leave resolution annotated (see
  -- `validateFullyAnnotated`). Unconditional: re-resolutions check that
  -- lowering passes preserve the invariant too.
  let annotationBugs := validateFullyAnnotated program'
  -- Exception contract enforcement: catch-or-declare (`validateExceptionEscapes`)
  -- plus the "not yet lowerable" source-shape guards
  -- (`validateExceptionLowerability`).
  --
  -- The escape check (`validateExceptionEscapes`) runs on EVERY resolution, not
  -- just the initial one. A poly `throws (e:T)` cannot be checked at the initial
  -- resolution — `T` is not concrete, so `exceptionEscapes` defers it (see
  -- `mentionsTVar` there), exactly as a poly RETURN flows gradually. The real
  -- check happens at the post-`MonomorphizeComposites` re-resolution, where the
  -- clone carries a concrete throws type (`g$a1$int`) and a genuine `int </: bool`
  -- escape is caught. Re-running is safe: `EliminateExceptions` sets each proc's
  -- `throwsType := none` and erases `throw`/`try`, so after it runs the check is a
  -- no-op; and a CONCRETE escape already reported at the initial resolve is deduped
  -- away by the caller's `newErrors` filter (it is not a *new* error). Without this
  -- the escape guard would be a permanent no-op for every polymorphic throw — an
  -- unsound hole, since the check reads the callee's declared throws type and never
  -- the call-site type arguments.
  --
  -- The other two guards stay initial-resolution-ONLY: they are properties of the
  -- *authored* program, and `EliminateExceptions` erases the constructs they are
  -- phrased against, so a re-resolution of lowered output must not re-run them (it
  -- would report the same error once per re-resolve, and find nothing after the
  -- lowering). Instance procedures are still inside their composites here (lifting
  -- happens later), so both checks walk `allProcs`, which includes them.
  let namedProcs : List (String × Procedure) :=
    program'.staticProcedures.map (fun p => (p.name.text, p))
      ++ program'.types.flatMap fun
        | .Composite ct => ct.instanceProcedures.map (fun p => (s!"{ct.name.text}.{p.name.text}", p))
        | _ => []
  let exceptionErrors :=
    validateExceptionEscapes semanticModel typeLattice namedProcs
      ++ (if existingModel.isNone then
            validateExceptionalClausesNeedThrows namedProcs
              ++ validateExceptionLowerability semanticModel program'.types allProcs
          else [])
  { program := program',
    model := semanticModel,
    errors := finalState.errors ++ heapAnalysisErrors ++ diamondErrors ++ oldUsageWarnings ++
      globalNameErrors ++ globalTypeErrors ++ constrainedGlobalErrors ++ constantGlobalErrors ++
      globalInitializerErrors ++
      globalCallErrors ++ bodilessGlobalErrors ++ entryGlobalErrors ++ invokeOnErrors ++
      multiOutputCallErrors ++ exceptionErrors ++ annotationBugs
  }

-- `resolve` establishes the invariant that every `Declare` in its output is
-- annotated: see `resolve_fullyAnnotated` in `ResolutionProps.lean`.

/-! ## Resolution for UnorderedCoreWithLaurelTypes -/

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
    (gradualTypes : Std.HashSet String := {})
    (realizeCoercion : Option (Coercion → StmtExprMd → StmtExprMd) := none)
    (toBool : Option (HighType → StmtExprMd → StmtExprMd) := none)
    (reservedNames : Std.HashSet String := {})
    : UnorderedCoreWithLaurelTypes × SemanticModel × Array Message :=
  -- Phase 1: register all top-level names, then resolve references
  let phase1 : ResolveM UnorderedCoreWithLaurelTypes := do
    preRegisterDefinitions
      (additionalTypes ++ uc.datatypes.map .Datatype)
      uc.constants
      []
      (uc.functions ++ uc.coreProcedures)

    -- Build type scopes for additional composite types (for field resolution)
    for td in additionalTypes do
      if let .Composite ct := td then
        let s ← get
        let mut typeScope : Scope := {}
        for parent in ct.extending do
          -- `extending` is `List HighTypeMd`; inherit the parent's field scope by base
          -- name (`Base<T>` shares `Base`'s fields).
          match highBaseName? parent.val with
          | some pname =>
            match s.typeScopes.get? pname.text with
            | some parentScope =>
              for (k, v) in parentScope do
                typeScope := typeScope.insert k v
            | none => pure ()
          | none => pure ()
        for field in ct.fields do
          let qualifiedKey := ct.name.text ++ "." ++ field.name.text
          match s.scope.get? qualifiedKey with
          | some entry => typeScope := typeScope.insert field.name.text entry
          | none => pure ()
        modify fun s => { s with typeScopes := s.typeScopes.insert ct.name.text typeScope }

    -- Resolve datatypes
    let datatypes' ← uc.datatypes.mapM fun dt => do
      match ← resolveTypeDefinition (.Datatype dt) with
      | .Datatype dt' => pure dt'
      | _ => pure dt -- unreachable

    -- Resolve constants
    let constants' ← uc.constants.mapM resolveConstant

    -- Resolve functions and core procedures
    let functions' ← uc.functions.mapM resolveProcedure
    let coreProcedures' ← uc.coreProcedures.mapM resolveProcedure

    return { functions := functions', coreProcedures := coreProcedures',
             datatypes := datatypes', constants := constants' }

  let nextId := existingModel.elim 1 (fun m => m.nextId)
  -- Thread the frontend's gradual type names AND the coercion/truthiness hooks onto the
  -- lattice so consistency/coercion treats them as the dynamic top (e.g. Python `Any`) and
  -- the second resolve pass sees the SAME lattice as the main `resolve` — otherwise the
  -- widen arm (gated on realizeCoercion.isSome) and the toBool truthiness hook silently
  -- differ between passes, producing spurious "resolution introduced this diagnostic".
  let typeLattice := { TypeLattice.ofTypes (uc.datatypes.map .Datatype ++ additionalTypes) with
    gradualTypes := gradualTypes, realizeCoercion := realizeCoercion, toBool := toBool,
    reservedNames := reservedNames }
  let (uc', finalState) := phase1.run { nextId := nextId, typeLattice }

  -- Phase 2: build refToDef from the resolved unordered core
  let program' : Program := {
    staticProcedures := uc'.functions ++ uc'.coreProcedures,
    staticFields := [],
    types := uc'.datatypes.map .Datatype ++ additionalTypes,
    constants := uc'.constants
  }
  let refToDef := buildRefToDef program'

  let model : SemanticModel := {
    compositeCount := additionalTypes.length,
    refToDef := refToDef,
    nextId := finalState.nextId
  }
  (uc', model, finalState.errors)

end -- public section
end Strata.Laurel
