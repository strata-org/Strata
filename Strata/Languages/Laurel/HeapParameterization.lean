/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.HeapAnalysis
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.HeapParameterizationConstants
import Strata.Languages.Laurel.LaurelTypes
import Strata.Util.Tactics
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.EliminateValueInReturns
import Strata.Languages.Laurel.EliminateReturnStatements

/-
Heap Parameterization Pass

Transforms procedures that interact with the heap by adding explicit heap parameters.
The heap is modeled as a `Heap` datatype containing a `data: TotalMap Composite (TotalMap Field $Box)` map
and a `nextReference: int` for allocating new objects. `$Box` is a sum type with constructors for each
primitive type (BoxInt, BoxBool, BoxFloat64, BoxComposite). Composite is a type synonym for int.

1. Procedures that write the heap get an inout heap parameter
   - Input: `heap : Heap`
   - Output: `heap : Heap`
   - Field writes become: `heap := updateField(heap, obj, field, BoxT(value))`

2. Procedures that only read the heap get an in heap parameter
   - Input: `heap : Heap`
   - Field reads become: `$Box..tVal(readField(heap, obj, field))`

3. Procedure calls are transformed:
   - Calls to heap-writing procedures in expressions:
     `f(args...) => (var freshVar: type; freshVar, heapVar := f(args..., heapVar); freshVar)`
   - Calls to heap-writing procedures as statements:
     `f(args...)` => `heap := f(args..., heap)`
   - Calls to heap-reading procedures:
     `f(args...)` => `f(args..., heap)`

The hidden heap argument is passed LAST so that explicit arguments are
evaluated before the heap is sampled: an effectful earlier argument (e.g. a
call that writes the heap) updates `heap` before the trailing heap argument
reads it, and the imperative-lifting pass snapshots any earlier heap reads.
This preserves source-level left-to-right evaluation without a separate
argument-hoisting step in this pass.

The analysis is transitive: if procedure A calls procedure B, and B reads/writes the heap,
then A is also considered to read/write the heap.
-/

public section

namespace Strata.Laurel

-- Heap-effect analysis (`AnalysisResult`, `analyzeProc`, `computeReadsHeap`,
-- `computeWritesHeap`) now lives in `Strata.Languages.Laurel.HeapAnalysis`, so
-- it can be shared with `Resolution` (which uses it to diagnose no-op `old(...)`)
-- without an import cycle.

structure TransformState where
  heapReaders : Std.HashSet Nat
  heapWriters : Std.HashSet Nat
  freshCounter : Nat := 0  -- Counter for generating fresh variable names
  /-- Box constructors used during transformation, collected for datatype generation -/
  usedBoxConstructors : List DatatypeConstructor := []

@[expose] abbrev TransformM := ExceptT String (StateM TransformState)

/-- The name of the heap-model datatype this pass introduces (`Heap`). -/
def heapTypeName : Identifier := "Heap"

/-- The `Heap` type as a `HighTypeMd`, at the given source. -/
private def heapType (source : FileRange) : HighTypeMd := ⟨.UserDefined heapTypeName, source⟩

/-- Check whether a UserDefined type name refers to a Datatype (vs Composite) in the model -/
private def isDatatype (model : SemanticModel) (name : Identifier) : Bool :=
  match model.get name with
  | .datatypeDefinition _ => true
  | _ => false

/-- Check whether a UserDefined type name refers to a composite (heap object)
    type in the model. Unlike `!isDatatype`, this is `false` for a type
    *parameter* (e.g. the `Val` of `Result<Val, Err>`, the field type reported
    for `Result..value!`) or any name not resolved to a composite, so reference
    equality is only applied to genuine heap references. -/
private def isComposite (model : SemanticModel) (name : Identifier) : Bool :=
  match model.get name with
  | .compositeType _ => true
  | _ => false

/-- Check whether a UserDefined type name refers to an opaque type. Like a datatype value
    and unlike a composite, an opaque value is not a heap reference: it needs its own box
    variant carrying its own sort, and it must not attract `Composite..ref!` clauses. -/
private def isOpaque (model : SemanticModel) (name : Identifier) : Bool :=
  match model.get name with
  | .opaqueType _ => true
  | _ => false

/-- An identifier-legal name for a heap-box variant of a GENERIC datatype instantiation,
    so `Bx<int>` and `Bx<bool>` get distinct box constructors/destructors (`Bx$a1$int` vs
    `Bx$a1$bool`) — preserving the instantiation-distinctness the native parametric datatype
    gives us. Shares `instTagCommon` with `MonomorphizeComposites.tyTag` (inlined, not imported,
    to avoid a pass↔pass cycle), so it inherits that kernel's non-injectivity caveat: a `$`-clash
    is caught downstream by the Core type checker, not here. Returns `none` on an un-renderable
    shape (`.Applied` over a non-datatype, a `.TVar` arg), keeping the caller on its loud fallback. -/
private def appliedBoxTag (ty : HighType) : Option String :=
  -- Heap-box naming needs no extra leaf beyond `instTagCommon`'s shared arms (which already
  -- tag `.UserDefined`, `.Applied` datatypes, and `.TMap`/`.TSet`); `none` on TVar/TVoid.
  instTagCommon (fun _ => none) ty

/-- Get the Box destructor name for a given Laurel HighType.
    For UserDefined datatypes, uses "$Box..<datatypeName>Val!";
    for Composite types, uses "$Box..compositeVal!".

    Constrained types do not need resolving here: `ConstrainedTypeElim` runs
    before this pass and has already lowered every constrained type to its base
    type (and removed the constrained type definitions), so `ty` is never a
    constrained-type reference. -/
def boxDestructorName (model : SemanticModel) (ty : HighType) : Identifier :=
  match ty with
  | .TInt => "$Box..intVal!"
  | .TBool => "$Box..boolVal!"
  | .TFloat64 => "$Box..float64Val!"
  | .TReal => "$Box..realVal!"
  | .TString => "$Box..stringVal!"
  | .UserDefined name =>
      if isDatatype model name || isOpaque model name then s!"$Box..{name.text}Val!"
      else "$Box..compositeVal!"
  | .TBv n => s!"$Box..bv{n}Val!"
  -- Generic datatype instantiation `Bx<int>` + built-in `TotalMap`: one box variant per
  -- instantiation, named via `appliedBoxTag`. (`.TSet` is unreachable — LaurelGrammar.st has
  -- only `totalMapType`, no Set production — kept for symmetry with `.TMap`.)
  | .Applied .. | .TMap .. | .TSet .. =>
    match appliedBoxTag ty with
    | some tag => s!"$Box..{tag}Val!"
    | none => dbg_trace f!"BUG, boxDestructorName bad type {ty}"; "boxDestructorNameError"
  | _ => dbg_trace f!"BUG, boxDestructorName bad type {ty}"; "boxDestructorNameError"

/-- Get the Box constructor name for a given Laurel HighType.
    For UserDefined datatypes, uses "Box..<datatypeName>";
    for Composite types, uses "BoxComposite". -/
def boxConstructorName (model : SemanticModel) (ty : HighType) : Identifier :=
  match ty with
  | .TInt => "BoxInt"
  | .TBool => "BoxBool"
  | .TFloat64 => "BoxFloat64"
  | .TReal => "BoxReal"
  | .TString => "BoxString"
  | .UserDefined name =>
      if isDatatype model name || isOpaque model name then s!"Box..{name.text}"
      else "BoxComposite"
  | .TBv n => s!"BoxBv{n}"
  -- Generic datatype instantiation `Bx<int>`, and built-in collections `TotalMap`/`Set`.
  | .Applied .. | .TMap .. | .TSet .. =>
    match appliedBoxTag ty with
    | some tag => s!"Box..{tag}"
    | none => dbg_trace s!"BUG, boxConstructorName bad type: {repr ty}"; "boxConstructorNameError"
  | ty => dbg_trace s!"BUG, boxConstructorName bad type: {repr ty}"; "boxConstructorNameError"

/-- Synthetic source location for compiler-generated Box datatype definitions. -/
private def syntheticSource : FileRange :=
  { file := .file "Strata/Languages/Laurel/HeapParameterization.lean", range := SourceRange.none }

/-- Build the DatatypeConstructor for a Box variant from a HighType, for datatype generation -/
private def boxConstructorDef (model : SemanticModel) (ty : HighType) : Option DatatypeConstructor :=
  match ty with
  | .TInt => some { name := "BoxInt", args := [{ name := "intVal", type := ⟨.TInt, syntheticSource⟩ }] }
  | .TBool => some { name := "BoxBool", args := [{ name := "boolVal", type := ⟨.TBool, syntheticSource⟩ }] }
  | .TReal => some { name := "BoxReal", args := [{ name := "realVal", type := ⟨.TReal, syntheticSource⟩ }] }
  | .TFloat64 => some { name := "BoxFloat64", args := [{ name := "float64Val", type := ⟨.TFloat64, syntheticSource⟩ }] }
  | .TString => some { name := "BoxString", args := [{ name := "stringVal", type := ⟨.TString, syntheticSource⟩ }] }
  | .UserDefined name =>
      if isDatatype model name || isOpaque model name then
        some { name := s!"Box..{name.text}", args := [{ name := s!"{name.text}Val", type := ⟨.UserDefined name, syntheticSource⟩ }] }
      else
        some { name := "BoxComposite", args := [{ name := "compositeVal", type := ⟨.UserDefined "Composite", syntheticSource⟩ }] }
  | .TBv n =>
        some { name := s!"BoxBv{n}", args := [{ name := s!"bv{n}Val", type := ⟨.TBv n, syntheticSource⟩ }] }
  -- `.Applied` generic datatypes + built-in `.TMap`/`.TSet`: the box variant carries the
  -- FULL type, so `translateType` lowers it to the right Core sort (`.tcons "Bx" [int]` for a
  -- datatype, `Core.mapTy k v` for Map) — keeping distinct instantiations in distinct boxes.
  | .Applied .. | .TMap .. | .TSet .. =>
    match appliedBoxTag ty with
    | some tag => some { name := s!"Box..{tag}", args := [{ name := s!"{tag}Val", type := ⟨ty, syntheticSource⟩ }] }
    | none => dbg_trace s!"BUG, boxConstructorDef bad type: {repr ty}"; none
  | ty => dbg_trace s!"BUG, boxConstructorDef bad type: {repr ty}"; none

/-- Record a Box constructor use in the transform state -/
private def recordBoxConstructor (model : SemanticModel) (ty : HighType) : TransformM Unit := do
  let ctorOption := boxConstructorDef model ty
  match ctorOption with
  | some ctor =>
      modify fun s =>
        if s.usedBoxConstructors.any (fun c => c.name.text == ctor.name.text) then s
        else { s with usedBoxConstructors := s.usedBoxConstructors ++ [ctor] }
  | _ => return

def readsHeap (name : Identifier) : TransformM Bool := do
  let uid ← Identifier.getUniqueId name
  return (← get).heapReaders.contains uid

def writesHeap (name : Identifier) : TransformM Bool := do
  let uid ← Identifier.getUniqueId name
  return (← get).heapWriters.contains uid

private def freshVarName : TransformM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$tmp{s.freshCounter}"

/-- Helper to wrap a StmtExpr into StmtExprMd with the given source -/
private def mkMd (e : StmtExpr) (source : FileRange) : StmtExprMd := { val := e, source }
private def mkVarMd (v : Variable) (source : FileRange) : VariableMd := { val := v, source }

/--
Resolve the owning composite type name for a field access by computing the target expression's type.
Returns the qualified field name "DeclaringType.fieldName".
-/
def resolveQualifiedFieldName (model: SemanticModel) (fieldName : Identifier) : Option String :=
  match model.get fieldName with
    | .field owner _ => owner.text ++ "." ++ fieldName.text
    | .unresolved _ => none
    | _ => dbg_trace s!"BUG: resolveQualifiedFieldName {fieldName} did resolved to something other than a field"; none

private def wrapList (source : FileRange) : List StmtExprMd → StmtExprMd
  | [single] => single
  | many => ⟨.Block many none, source⟩

/-- The position a transformed expression occupies, which decides whether lowering may
    introduce an imperative binding here. Two lowerings need one: a heap-threading assignment
    for a heap-writing call (the `.StaticCall` writes-heap arm), and a capture temp for an
    effectful `as`-cast target (`lowerAsTypeNode`). `.executable` admits such bindings;
    `.specification` is a pure position that must stay binding-free (effectful statements are
    rejected upstream at translation, and a spec cannot host a `.Declare` — no local inference
    in specs). -/
inductive HeapTransformContext where
  | executable
  | specification

/-- Lower an `AsType` node `t as T` to `{ assert (t is T); t }`, given the ALREADY-lowered
    target `target'`. The single source of truth for `as`-cast lowering, shared by
    `heapTransformExpr`'s `.AsType` arm and the heap-neutral `lowerAsTypeNodesOnly` path so the
    two can't drift: a single lowering is what keeps an effectful target from being evaluated twice.
    - `.specification`: double-embed `target'` (once in the check, once as the result). This is
      not a soundness hedge but the only representable form here: a spec cannot host a `.Declare`
      temp (no local inference in specs), so capture-once is unavailable — and it is safe because
      an effectful target cannot reach a spec (effectful statements are rejected upstream at
      translation), so `target'` is pure and evaluating it twice is meaning-preserving.
    - `.executable`: capture `target'` into a fresh local ONCE — an effectful target (a
      heap-writing call, or a compound like `{ x := x-1; e }` before imperative lifting) must
      run exactly once. No type annotation on the declare: a generic callee's declared return
      type names unbound type params here; the resolver infers the instantiated type. -/
private def lowerAsTypeNode (target' : StmtExprMd) (ty : HighTypeMd) (source : FileRange)
    (context : HeapTransformContext) : TransformM StmtExprMd := do
  -- The positions differ only in whether the target may be named twice (a pure spec) or must
  -- first be bound into a fresh local (an effectful executable target must run exactly once).
  -- `prelude` holds that binding (empty for specs); `ref` is what the check and result mention.
  let (prelude, ref) ← match context with
    | .specification => pure ([], target')
    | .executable =>
      let result ← freshVarName
      let capture : StmtExprMd := ⟨.Assign [⟨.Declare ⟨result, none⟩, source⟩] target', source⟩
      pure ([capture], ⟨.Var (.Local result), source⟩)
  let check : StmtExprMd := ⟨.Assert ⟨.IsType ref ty, source⟩ none, source⟩
  return ⟨.Block (prelude ++ [check, ref]) none, source⟩

/--
Transform an expression, adding heap parameters where needed.
- `heapVar`: the name of the heap variable to use
- `model`: the semantic model for resolving fields and procedure effects
- `valueUsed`: whether the result value of this expression is used (affects optimization of heap-writing calls)
- `context`: specification contexts remain pure and never gain synthetic assignments
-/
def heapTransformExpr (heapVar : Identifier) (model: SemanticModel) (expr : StmtExprMd)
    (valueUsed : Bool := true) (context : HeapTransformContext := .executable) : TransformM StmtExprMd :=
  recurseOne expr valueUsed
where
  recurseOne (exprMd : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd :=
    wrapList exprMd.source <$> recurse exprMd valueUsed
  termination_by (sizeOf exprMd, 1)
  recurse (exprMd : StmtExprMd) (valueUsed : Bool := true) : TransformM (List StmtExprMd) := do
    let ⟨expr, source⟩ := exprMd
    match _h : expr with
    | .Var (.Field selectTarget fieldName) => do
        let some qualifiedName := resolveQualifiedFieldName model fieldName
          | return [⟨ .Hole, source ⟩]

        let valTy := (model.get fieldName).getType
        let selectTarget' ← recurseOne selectTarget
        let readExpr := ⟨ .StaticCall "readField" [mkMd (.Var (.Local heapVar)) source, selectTarget', mkMd (.StaticCall qualifiedName []) source], source ⟩
        -- Unwrap Box: apply the appropriate destructor
        recordBoxConstructor model valTy.val
        return [mkMd (.StaticCall (boxDestructorName model valTy.val) [readExpr]) source]
    | .StaticCall callee args =>
        let args' ← args.mapM (recurseOne ·)
        -- For `==` and `!=` on Composite types, compare refs instead. These are
        -- calls to the built-in `$eq`/`$neq` wrappers (see `Operation.procName`);
        -- neither is overloaded, so `UniqueOverloadNames` leaves the names alone
        -- and matching on the text is safe.
        --
        -- The guard is `isComposite`, not `!isDatatype`. `.UserDefined` covers three
        -- things, not two: composites (heap references, where `ref!` is right),
        -- datatype values (where it is wrong), and type *parameters* — the `Val` of
        -- `Result<Val, Err>`, which is the type reported for `Result..value!(…)` and
        -- is an ordinary value, often an `int`. A parameter is not a datatype either,
        -- so excluding only datatypes would wrap it in `Composite..ref!` and fail to
        -- unify `(arrow Composite int)` against `(arrow int _)`. Ref-compare genuine
        -- composites and let everything else compare structurally.
        if callee.text == Operation.Eq.procName || callee.text == Operation.Neq.procName then
          match args, args' with
          | [e1, _], [a1, a2] =>
            match (computeExprType model e1).val with
            | .UserDefined name =>
              if isComposite model name then
                let ref1 := mkMd (.StaticCall "Composite..ref!" [a1]) source
                let ref2 := mkMd (.StaticCall "Composite..ref!" [a2]) source
                return [⟨ .StaticCall callee [ref1, ref2], source ⟩]
              return [⟨ .StaticCall callee args', source ⟩]
            | _ => return [⟨ .StaticCall callee args', source ⟩]
          | _, _ => return [⟨ .StaticCall callee args', source ⟩]
        else
        -- No heap threading: handled by `GlobalParameterization` (see `heapGlobalField`).
        return [⟨ .StaticCall callee args', source ⟩]
    | .InstanceCall callTarget callee args =>
        let t ← recurseOne callTarget
        let args' ← args.mapM (recurseOne ·)
        return [⟨ .InstanceCall t callee args', source ⟩]
    | .IfThenElse c t e =>
        let e' ← match e with | some x => some <$> recurseOne x valueUsed | none => pure none
        return [⟨ .IfThenElse (← recurseOne c) (← recurseOne t valueUsed) e', source ⟩]
    | .Block stmts label =>
        let n := stmts.length
        let rec processStmts (idx : Nat) (remaining : List StmtExprMd) : TransformM (List StmtExprMd) := do
          match remaining with
          | [] => pure []
          | s :: rest =>
              let isLast := idx == n - 1
              let s' ← recurse s (isLast && valueUsed)
              let rest' ← processStmts (idx + 1) rest
              pure (s' ++ rest')
          termination_by (sizeOf remaining, 0)
        let stmts' ← processStmts 0 stmts
        return [⟨ .Block stmts' label, source ⟩]
    | .While c invs d b postTest =>
        let invs' ← invs.mapM (recurseOne ·)
        return [⟨ .While (← recurseOne c) invs' d (← recurseOne b false) postTest, source ⟩]
    | .Return v =>
        let v' ← match v with | some x => some <$> recurseOne x | none => pure none
        return [⟨ .Return v', source ⟩]
    | .Assign targets v =>

      -- Process field targets
      let (processedTargets, updateStatements) <-
        targets.attach.foldlM (init := ([], [])) fun (accTargets, accStmts) ⟨t, _⟩ =>
          match _htv : t.val with
          | .Field target fieldName => do
              let some qualifiedName := resolveQualifiedFieldName model fieldName
                -- Unresolved field name = a write to an unmodeled object's attribute. Drop it from the heap
                -- model (retarget to a throwaway local; emit no updateField) — an untracked field write is
                -- unobservable in the heap abstraction.
                | do
                  let discardVar ← freshVarName
                  return (accTargets ++ [mkVarMd (.Declare ⟨discardVar, some ⟨.Unknown, source⟩⟩) source], accStmts)
              let valTy := (model.get fieldName).getType
              recordBoxConstructor model valTy.val
              let freshVar ← freshVarName
              let target' ← recurseOne target
              let boxedVal := mkMd (.StaticCall (boxConstructorName model valTy.val) [mkMd (.Var (.Local freshVar)) source]) source
              let updateStmt : StmtExprMd := ⟨ .Assign [mkVarMd (.Local heapVar) source]
                (mkMd (.StaticCall "updateField" [mkMd (.Var (.Local heapVar)) source, target', mkMd (.StaticCall qualifiedName []) source, boxedVal]) source), source ⟩
              return (accTargets ++ [mkVarMd (.Declare ⟨freshVar, some valTy⟩) source], accStmts ++ [updateStmt])
          | _ => return (accTargets ++ [t], accStmts)

      -- No heap threading here either (see the `StaticCall` arm above).
      let (newAssign, suffixes) ← do
        let v' ← match _hv : v.val with
          | .StaticCall callee args => do
            let args' <- args.mapM recurseOne
            pure ⟨ .StaticCall callee args', v.source ⟩
          | .InstanceCall callTarget _callee args => do
            let _callTarget' ← recurseOne callTarget
            let _args' <- args.mapM recurseOne
            pure ⟨ .InstanceCall _callTarget' _callee _args', v.source ⟩
          | _ =>
            recurseOne v
        let newAssign: AstNode StmtExpr := ⟨ StmtExpr.Assign processedTargets v', source ⟩

        -- Convert a Declare variable to a Local reference (stripping the type).
        -- Non-Declare variables pass through unchanged.
        let variableAsRef(var: Variable): Variable := match var with
          | .Declare param => Variable.Local param.name
          | x => x

        -- Make sure the result of the StmtExpr is still the same
        let suffixes: List (AstNode StmtExpr) := if valueUsed && targets.length == 1
          then
            let targetVar := match processedTargets with
              | t :: _ => variableAsRef t.val
              -- unreachable: targets.length == 1 guarantees processedTargets is non-empty
              | [] => Variable.Local "$bug_empty_targets"
            updateStatements ++ [⟨ StmtExpr.Var targetVar, source⟩]
          else updateStatements
        pure (newAssign, suffixes)
      return newAssign :: suffixes

    | .PureFieldUpdate t f v => return [⟨ .PureFieldUpdate (← recurseOne t) f (← recurseOne v), source ⟩]
    | .New .. => return [exprMd]
    | .ReferenceEquals l r => return [⟨ .ReferenceEquals (← recurseOne l) (← recurseOne r), source ⟩]
    | .AsType target ty =>
        let target' ← recurseOne target true
        return [← lowerAsTypeNode target' ty source context]
    | .IsType t ty => return [⟨ .IsType (← recurseOne t) ty, source ⟩]
    | .Quantifier mode p trigger b =>
      let trigger' ← trigger.attach.mapM fun ⟨t, _⟩ => recurseOne t
      return [⟨.Quantifier mode p trigger' (← recurseOne b), source⟩]
    | .Assigned n => return [⟨ .Assigned (← recurseOne n), source ⟩]
    -- Native pre-state `old`: heap-transform `v`; `pushOldInward` later
    -- distributes the `Old` onto the inout `$heap`.
    | .Old v none => return [⟨ .Old (← recurseOne v) none, source ⟩]
    -- Labeled `old`: read `v` against snapshot `h` instead of the live `$heap`.
    -- Heap-transform `v` (so `s#x` becomes `readField($heap, s, x)`), then substitute
    -- `h` for `$heap` (yielding `readField(h, s, x)`).
    | .Old v (some h) =>
        let v' ← recurseOne v
        return [mapStmtExpr (fun n => match n.val with
          | .Var (.Local x) => if x.text == heapVar.text then { n with val := .Var (.Local h) } else n
          | _ => n) v']
    -- The coroutine two-state markers are lowered to labeled `Old` / `Snapshot`
    | .OldGuarantee _ =>
        throw "oldGuarantee(...) reached heap parameterization; it should have been \
               lowered to a labeled `Old` by YieldElim"
    | .OldRelies _ =>
        throw "oldRelies(...) reached heap parameterization; it should have been \
               lowered to a labeled `Old` by YieldElim"
    -- Capture the live heap into snapshot local `h`: `h := $heap`.
    | .Snapshot h =>
        return [⟨ .Assign [mkVarMd (.Local h) source] (mkMd (.Var (.Local heapVar)) source), source ⟩]
    | .Fresh v => return [⟨ .Fresh (← recurseOne v), source ⟩]
    | .Assert condExpr summary =>
        return [⟨ .Assert (← recurseOne condExpr) summary, source ⟩]
    | .Assume c => return [⟨ .Assume (← recurseOne c), source ⟩]
    | .ProveBy v p => return [⟨ .ProveBy (← recurseOne v) (← recurseOne p), source ⟩]
    | .ContractOf ty f => return [⟨ .ContractOf ty (← recurseOne f), source ⟩]
    -- `Throw`/`Try` are lowered away by `EliminateExceptions` (which runs before
    -- this pass), so they never reach here (no arms needed).
    | _ => return [exprMd]
  termination_by (sizeOf exprMd, 0)
  decreasing_by
    all_goals simp_wf
    all_goals (try have := AstNode.sizeOf_val_lt exprMd)
    all_goals (try have := AstNode.sizeOf_val_lt v)
    all_goals (try term_by_mem)
    all_goals (try (cases exprMd; simp_all; omega))
    -- For field inner expressions in attach-based:
    all_goals (try (
      have := List.sizeOf_lt_of_mem ‹_›
      have := Variable.sizeOf_field_target_lt_of_eq _htv
      omega))
    -- Remaining goals
    all_goals (
      cases exprMd with | mk val src =>
      simp_all
      omega)

/-- Check if `p` is a composite (heap-reference) parameter. A `Heap`-typed
    parameter (a snapshot heap threaded in as an explicit parameter by an
    earlier pass) is not a heap reference: `Heap` is the heap-model datatype
    heap-param itself introduces, so it is absent from the pre-pass model and
    would otherwise be misclassified as composite — yielding a bogus
    `Composite..ref!` well-formedness precondition over a `Heap` value. -/
private def isCompositeParam (model : SemanticModel) (p : Parameter) : Bool :=
  match p.type.val with
  | .UserDefined name => name.text != heapTypeName.text && isComposite model name
  | _ => false

/-! Heap well-formedness conditions below are emitted `free`:
    assumed for reference values appearing *directly* as  parameters/outputs,
    but not for indirectly reachable references (composite fields, set elements).
    Closing that gap needs axioms over custom types. -/

/-- For each composite parameter `p`, the free precondition
    `Composite..ref!(p) < Heap..nextReference!(heapVar)` (`p` is allocated) -/
private def heapWellFormednessPreconds (model : SemanticModel)
    (inputs : List Parameter) (heapVar : Identifier) : List Condition :=
  inputs.filterMap fun p =>
    if isCompositeParam model p then
      let src := p.name.source
      let pRead := { val := .Var (.Local p.name), source := src }
      let pRef := { val := .StaticCall "Composite..ref!" [pRead], source := src }
      let heapRead := { val := .Var (.Local heapVar), source := src }
      let counter := { val := .StaticCall "Heap..nextReference!" [heapRead], source := src }
      let allocated := { val := .StaticCall "$intLt" [pRef, counter], source := src }
      some { condition := allocated, summary := some "input is allocated on the heap", mode := .Assume }
    else none

/-- The free postcondition
    `Heap..nextReference!($heap_in) <= Heap..nextReference!($heap)` -
    the top of heap pointer never decreases. -/
private def heapMonotonicityPostcond (source : FileRange)
    (heapVar : Identifier) : Condition :=
  let heapRead := { val := .Var (.Local heapVar), source }
  let nextRef := { val := .StaticCall "Heap..nextReference!" [heapRead], source }
  let inCounter := { val := .Old nextRef, source }
  let outCounter := nextRef
  { condition := { val := .StaticCall "$intLe" [inCounter, outCounter], source },
    summary := some "monotonic heap pointer", mode := .Assume }

/-- For each composite output `o`, the free postcondition
    `Composite..ref!(o) < Heap..nextReference!($heap)` - a returned
    composite is allocated in the output heap. -/
private def heapOutputAllocationPostconds (model : SemanticModel)
    (outputs : List Parameter) (heapOutVar : Identifier) : List Condition :=
  outputs.filterMap fun o =>
    if isCompositeParam model o then
      let src := o.name.source
      let oRead := { val := .Var (.Local o.name), source := src }
      let oRef := { val := .StaticCall "Composite..ref!" [oRead], source := src }
      let heapRead := { val := .Var (.Local heapOutVar), source := src }
      let counter := { val := .StaticCall "Heap..nextReference!" [heapRead], source := src }
      some { condition := { val := .StaticCall "$intLt" [oRef, counter], source := src },
             summary := some "output is allocated on the heap", mode := .Assume }
    else none

/-- Heap-transform a pure specification expression without introducing
heap-threading assignments for calls to heap-writing procedures. -/
def heapTransformSpecificationExpr (heapName : Identifier) (model : SemanticModel)
    (expr : StmtExprMd) : TransformM StmtExprMd :=
  heapTransformExpr heapName model expr (context := .specification)

/-- Heap-transform a modifies entry. A field target `o#f` is kept symbolic
(only its owner is lowered) so the modifies pass can match it structurally. -/
def heapTransformModifiesEntry (heapName : Identifier) (model : SemanticModel)
    (entry : StmtExprMd) : TransformM StmtExprMd := do
  match entry.val with
  | .Var (.Field target fieldName) =>
      let target' ← heapTransformExpr heapName model target
      return { entry with val := .Var (.Field target' fieldName) }
  | _ => heapTransformExpr heapName model entry

/-- Distinct snapshot-heap locals named by a `Snapshot` or a labeled `Old` in
    `e`, in first-occurrence order. `HeapParameterization` declares each as a
    `Heap` local; see `snapshotLocalDecls`. -/
private def collectSnapshotLocals (e : StmtExprMd) : List Identifier :=
  -- Dedup by name text via a `HashSet` (O(1) membership) while preserving
  -- first-occurrence order: prepend to `acc`, then reverse once at the end.
  let (_, acc) := foldStmtExpr (β := Std.HashSet String × List Identifier)
    (fun n (seen, acc) => match n.val with
      | .Snapshot h | .Old _ (some h) =>
        if seen.contains h.text then (seen, acc) else (seen.insert h.text, h :: acc)
      | _ => (seen, acc)) (∅, []) e
  acc.reverse

/-- `var h : Heap := $heap` declarations for each snapshot local in `impl` that is
    not already a parameter -/
private def snapshotLocalDecls (heapName : Identifier) (params : List Identifier)
    (impl : StmtExprMd) : List StmtExprMd :=
  let heapTy : HighTypeMd := heapType impl.source
  (collectSnapshotLocals impl).filterMap fun h =>
    if params.any (·.text == h.text) then none
    else some ⟨.Assign [⟨.Declare ⟨h, some heapTy⟩, impl.source⟩]
                       ⟨.Var (.Local heapName), impl.source⟩, impl.source⟩

/-- Lower ONLY `AsType` nodes (via the shared `lowerAsTypeNode`), recursing structurally
    and leaving every other node untouched. This is the heap-INDEPENDENT counterpart to
    `heapTransformExpr`'s `.AsType` arm, for the heap-neutral procedure branch: such a
    procedure must NOT receive the heap-dependent rewrites (field access, Composite `==` →
    reference compare — the latter mis-fires on a constrained/`.UserDefined` non-composite
    operand), but it MUST still have its `as` casts lowered or the Core translator hard-fails
    (`NotYetImplemented`). `context` matters even here: an EXECUTABLE body's cast target can be
    effectful (a compound `{ x := x-1; e }`, before imperative lifting), so it must be captured
    once — routing through `lowerAsTypeNode` shares that logic with `heapTransformExpr` rather
    than re-deriving it. `mapStmtExprM` is bottom-up, so nested casts (`(x as A) as B`) lower
    correctly. -/
private def lowerAsTypeNodesOnly (context : HeapTransformContext) (expr : StmtExprMd)
    : TransformM StmtExprMd :=
  mapStmtExprM (fun e => match e.val with
    | .AsType t ty => lowerAsTypeNode t ty e.source context
    | _ => pure e) expr

/-- Transform a procedure body, applying `bodyFn` to the one EXECUTABLE position (the
    transparent body or the opaque implementation) and `specFn` to the pure positions
    (opaque/abstract postconditions and a modifies group's targets and guard). The two
    functions differ because an executable position may host an effectful cast target
    that must run exactly once, whereas spec positions are pure. `mapProcedureBodiesM`
    can't express this — it applies one function everywhere — which is why every branch
    of `heapTransformProcedure` traverses the body shape this way. -/
private def mapBodyWithM (bodyFn specFn : StmtExprMd → TransformM StmtExprMd)
    (body : Body) : TransformM Body := do
  match body with
  | .Transparent bodyExpr => .Transparent <$> bodyFn bodyExpr
  | .Opaque postconds impl modif =>
      let postconds' ← postconds.mapM (·.mapM specFn)
      let impl' ← impl.mapM bodyFn
      let modif' ← modif.mapM fun g => do
        let targets' ← g.targets.mapM specFn
        let guard' ← g.guard.mapM specFn
        pure ({ g with targets := targets', guard := guard' } : ModifiesGroup)
      pure (.Opaque postconds' impl' modif')
  | .Abstract postconds => .Abstract <$> postconds.mapM (·.mapM specFn)
  | .External => pure .External

def heapTransformProcedure (model: SemanticModel) (proc : Procedure) : TransformM Procedure := do
  let heapName := heapVarName
  let uid ← Identifier.getUniqueId proc.name
  let readsHeap := (← get).heapReaders.contains uid
  let writesHeap := (← get).heapWriters.contains uid
  -- Transform every out-of-body spec field (preconditions, decreases, invokeOn, axioms,
  -- throwsOn) at ONE site for all three branches, so no branch can silently skip a field:
  -- heap procedures thread the heap through them; a heap-neutral procedure still has `as`
  -- casts that must be lowered (`lowerAsTypeNodesOnly`) or they hard-fail at
  -- `LaurelToCoreSchemaPass`. The body is NOT transformed here — each branch does that
  -- itself, because the body's implementation is executable (capture an effectful cast
  -- target once) while these spec fields are pure.
  --
  -- Kept before the branches because a `throwsOn` case's frame targets need a
  -- modifies-specific transform rather than the uniform one; the writes-heap branch
  -- below rebuilds the cases from these. (A heap-neutral procedure has no `throwsOn` —
  -- `EliminateExceptions` cleared it upstream — so its spec transform is a no-op there.)
  --
  -- GAP (pre-existing, pipeline-wide): `lowerAsTypeNode` always emits `{ assert (t is T); t }`,
  -- so a cast in a contract-CONDITION field (a precondition, an `invokeOn`/`axioms`
  -- proposition) then hits `LaurelToCoreSchemaPass`'s "asserts are not YET supported in
  -- functions or contracts". Both transforms below share this limitation (the heap one's
  -- `.AsType` arm calls the same `lowerAsTypeNode`); representing the `is`-check as a
  -- proof-obligation predicate instead of an `assert` is a separate follow-up. The poly
  -- feature emits no such casts today, so nothing in the suite exercises the residual gap.
  let originalThrowsOn := proc.throwsOn
  let specTransform :=
    if readsHeap || writesHeap then heapTransformSpecificationExpr heapName model
    else lowerAsTypeNodesOnly .specification
  let proc ← mapProcedureSpecificationsM specTransform proc

  -- Declare the heap write on every heap writer. `GlobalParameterization` infers a
  -- global's effects from the expressions that mention it, which is enough for a
  -- procedure with a body but not for a bodiless one: its frame is the only evidence
  -- that it touches the heap, and the frame only *reads* `old($heap)` and `$heap` to
  -- relate them. Declaring it here keeps `writesGlobals` in agreement with
  -- `heapWriters` by construction -- both come from the same `HeapAnalysis` closure --
  -- so the heap is threaded as an inout for exactly the procedures that write it.
  let proc :=
    if writesHeap && !proc.writesGlobals.any (·.text == heapVarName.text)
    then { proc with writesGlobals := proc.writesGlobals ++ [heapVarName] }
    else proc

  if writesHeap then
    -- `$heap` is not added to `inputs`/`outputs` here; `GlobalParameterization` threads
    -- it, and owns argument evaluation order. The well-formedness contracts below do
    -- still mention it, keyed off the heap-effect analysis: they are heap-specific, and
    -- the reference is bound to the global by the re-resolve that ends the heap trio.
    -- Subjects are the original, untransformed composite inputs.
    --
    -- An entry procedure gets none of them. Its globals are body locals, which a
    -- contract cannot see, and all three are `.Assume` (free) — they inform callers,
    -- and an entry procedure has none.
    let preconditions' :=
      if proc.isInterpretEntry then proc.preconditions
      else heapWellFormednessPreconds model proc.inputs heapName ++ proc.preconditions

    let bodyValueIsUsed := !proc.outputs.isEmpty
    -- Synthesized postconditions: allocation counter is monotone, and every
    -- composite output is allocated in the output heap.
    let wfPostconditions :=
      if proc.isInterpretEntry then []
      else heapMonotonicityPostcond proc.name.source heapName
             :: heapOutputAllocationPostconds model proc.outputs heapName
    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformSpecificationExpr heapName model bodyExpr
          pure (.Transparent bodyExpr')
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformSpecificationExpr heapName model))
          let impl' ← match impl with
            | some implExpr =>
                -- Collect snapshot locals from the *original* impl before the
                -- transform erases the `Snapshot`/labeled-`Old` nodes, then
                -- declare them at the body top (`Heap` did not exist earlier).
                let decls := snapshotLocalDecls heapName (proc.inputs.map (·.name)) implExpr
                let implExpr' ← heapTransformExpr heapName model implExpr bodyValueIsUsed
                pure (some (prependStmts decls implExpr'))
            | none => pure none
          -- Targets keep field refs symbolic (structural matching in `ModifiesClauses`);
          -- a guard is an ordinary pre-state predicate and transforms like one.
          let modif' ← modif.mapM (fun g => do
            let targets' ← g.targets.mapM (heapTransformModifiesEntry heapName model ·)
            let guard' ← g.guard.mapM (heapTransformSpecificationExpr heapName model ·)
            pure ({ g with targets := targets', guard := guard' } : ModifiesGroup))
          pure (.Opaque (wfPostconditions ++ postconds') impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformSpecificationExpr heapName model))
          pure (.Abstract (wfPostconditions ++ postconds'))
      | .External => pure .External

    -- `EliminateExceptions` runs before this pass, so each `throwsOn` case's
    -- postconditions are already lowered into ordinary ones and cleared. Only the
    -- cases' guards and frames survive — kept for `ModifiesClauses`, which builds
    -- the exceptional frames after this pass.
    --
    -- A guard is an ordinary pre-state predicate, so it transforms like a
    -- precondition. A frame target is a Composite reference, so it transforms like
    -- a normal modifies entry — via `heapTransformModifiesEntry`, which keeps a
    -- field target `o#f` symbolic so `ModifiesClauses` can still match it
    -- structurally and build a field-granular exceptional frame.
    -- Transformed from the *original* cases, not from the ones the generic
    -- specification pass above already rewrote: it applies the specification
    -- transform uniformly, which is right for a guard but wrong for a frame target.
    -- A target has to stay structurally matchable — `heapTransformModifiesEntry`
    -- keeps `o#f` symbolic so `ModifiesClauses` can still build a field-granular
    -- exceptional frame — exactly as the body's own `modifies` is handled above.
    let throwsOn' ← originalThrowsOn.mapM fun blk => do
      let guard' ← heapTransformSpecificationExpr heapName model blk.guard
      let modifies' ← blk.modifies.mapM (heapTransformModifiesEntry heapName model ·)
      pure { blk with guard := guard', modifies := modifies' }

    return { proc with
      preconditions := preconditions',
      throwsOn := throwsOn',
      body := body' }

  else if readsHeap then
    -- Read-only: `$heap` is likewise not added as an input here.
    -- `GlobalParameterization` gives a reader the plain input (see above).

    -- Specifications were heap-transformed at the top of this function; prepend
    -- the free heap-well-formedness preconditions over the original inputs. Skipped
    -- for an entry procedure, whose `$heap` is a body local a contract cannot see
    -- (see the heap-writer branch above).
    let preconditions' :=
      if proc.isInterpretEntry then proc.preconditions
      else heapWellFormednessPreconds model proc.inputs heapName ++ proc.preconditions

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformSpecificationExpr heapName model bodyExpr
          pure (.Transparent bodyExpr')
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformSpecificationExpr heapName model))
          let impl' ← impl.mapM (heapTransformExpr heapName model ·)
          -- Targets keep field refs symbolic (structural matching in `ModifiesClauses`);
          -- a guard is an ordinary pre-state predicate and transforms like one.
          let modif' ← modif.mapM (fun g => do
            let targets' ← g.targets.mapM (heapTransformModifiesEntry heapName model ·)
            let guard' ← g.guard.mapM (heapTransformSpecificationExpr heapName model ·)
            pure ({ g with targets := targets', guard := guard' } : ModifiesGroup))
          pure (.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformSpecificationExpr heapName model))
          pure (.Abstract postconds')
      | .External => pure .External

    -- A read-only procedure has no exceptional frame (that implies writing the
    -- heap), and `EliminateExceptions` (before this pass) already cleared
    -- a `throwsOn` case's guard and postconditions, so there is no exceptional contract to transform here.
    return { proc with
      preconditions := preconditions',
      body := body' }

  else
    -- This procedure neither reads nor writes the heap, so it gets NO `$heap` parameter
    -- and none of the heap-dependent rewrites. Its out-of-body spec fields were already
    -- `as`-lowered at the top; only the body remains. The implementation is the one
    -- EXECUTABLE position — an effectful cast target (e.g. a pre-lift compound
    -- `{ x := x-1; e }`) must be captured once — while its postconditions and modifies
    -- frames are pure and double-embed.
    let body' ← mapBodyWithM (lowerAsTypeNodesOnly .executable) (lowerAsTypeNodesOnly .specification) proc.body
    return { proc with body := body' }

/-- The initial heap: nothing allocated, every field slot an arbitrary `$Box`.

    `MkHeap(mapConst(mapConst(<$Box hole>)), 0)`.

    The `$Box` default is a *nondeterministic* typed hole rather than a concrete
    constructor. `$Box`'s constructor list is generated by this pass from the field
    types the program actually uses, so there is no variant that is guaranteed to
    exist (a program with no fields yields none) — and none is needed: with
    `nextReference = 0` no object is allocated, so no slot of this map is reachable
    and which `$Box` it holds is unobservable. The hole says exactly that, and
    `$Box` is a declared type regardless of how many constructors it has.

    See `heapGlobalField` for where this is read. -/
private def emptyHeapInitializer : StmtExprMd :=
  let src := syntheticSource
  let boxHole : StmtExprMd :=
    ⟨.Hole (deterministic := false) (type := some ⟨.UserDefined "$Box", src⟩), src⟩
  let boxTy : HighTypeMd := ⟨.UserDefined "$Box", src⟩
  let innerTy : HighTypeMd := ⟨.TMap ⟨.UserDefined "Field", src⟩ boxTy, src⟩
  let outerTy : HighTypeMd := ⟨.TMap ⟨.UserDefined "Composite", src⟩ innerTy, src⟩
  -- Each `mapConst` is bound to an explicitly typed local, because `mapConst` cannot
  -- express its own key type: `LaurelToCoreSchemaPass` recovers it from the *binding's*
  -- declared type and otherwise defaults to `TypeTag`. Naming each level is what supplies
  -- `Composite` and `Field`.
  --
  -- A block is an expression here, as in `TypeHierarchy.lowerNew`. Its declarations make
  -- this initializer effectful, which is fine: it is synthesized after
  -- `validateGlobalInitializers` runs on user source, and it is only ever spliced into an
  -- entry procedure's body prologue -- a statement context.
  let innerName : Identifier := { text := "$heap$inner", uniqueId := none, source := src }
  let outerName : Identifier := { text := "$heap$outer", uniqueId := none, source := src }
  let bindInner : StmtExprMd :=
    ⟨.Assign [mkVarMd (.Declare ⟨innerName, some innerTy⟩) src]
      (mkMd (.StaticCall "mapConst" [boxHole]) src), src⟩
  let bindOuter : StmtExprMd :=
    ⟨.Assign [mkVarMd (.Declare ⟨outerName, some outerTy⟩) src]
      (mkMd (.StaticCall "mapConst" [mkMd (.Var (.Local innerName)) src]) src), src⟩
  let mkHeap :=
    mkMd (.StaticCall "MkHeap" [mkMd (.Var (.Local outerName)) src, mkMd (.LiteralInt 0) src]) src
  ⟨.Block [bindInner, bindOuter, mkHeap] none, src⟩

/-- `$heap` as a file-scope global, threaded through signatures and call sites by
    `GlobalParameterization` like any other global. -/
private def heapGlobalField : Field :=
  { name := heapVarName
    isMutable := true
    type := ⟨.UserDefined "Heap", syntheticSource⟩
    initializer := some emptyHeapInitializer }

def heapParameterization (model: SemanticModel) (program : Program) : Except String Program := do
  -- Instance procedures are already lifted to `staticProcedures` by an earlier
  -- pass, so they're covered by the calls below.
  let heapReaders ← computeReadsHeap program.staticProcedures
  let heapWriters ← computeWritesHeap program.staticProcedures
  let initState : TransformState := { heapReaders, heapWriters }
  let (result, state1) := (program.staticProcedures.mapM (heapTransformProcedure model)).run.run initState
  let procs' ← match result with
    | .ok ps => pure ps
    | .error e => .error s!"heapParameterization: {e}"
  -- No `Snapshot` or labeled `Old` may survive: both lower only in the
  -- writes-heap branch, so a residual node means a snapshot reached a non-writer.
  let residualSnapshots : List FileRange :=
    (procs'.forM (m := StateM (List FileRange)) (fun p =>
      foldProcedureExprsM (fun e => do
        match e.val with
        | .Snapshot _ | .Old _ (some _) => modify (e.source :: ·)
        | _ => pure ()) p) |>.run []).2
  unless residualSnapshots.isEmpty do
    .error s!"heapParameterization: {residualSnapshots.length} Snapshot/labeled-old \
              node(s) survived the pass — a snapshot reached a procedure not classified \
              as heap-writing, so the snapshot local was never declared"
  -- Collect all qualified field names and generate a Field datatype
  let fieldNames := program.types.foldl (fun acc td =>
    match td with
    | .Composite ct => acc ++ ct.fields.map (fun f => (mkId $ ct.name.text ++ "." ++ f.name.text))
    | _ => acc) ([] : List Identifier)
  let fieldDatatype : TypeDefinition :=
    .Datatype { name := "Field", typeArgs := [], constructors := fieldNames.map fun n => { name := n, args := [] } }
  -- Remove fields from composite types since they are now stored in the heap.
  let types' := program.types.map fun td =>
    match td with
    | .Composite ct => .Composite { ct with fields := [] }
    | other => other
  -- Generate the boxing datatype from all constructors used during transformation.
  -- The name lives in Laurel's reserved `$`-namespace, and the coupling is by hand rather than
  -- derived: the accessors emitted for field reads come from `boxDestructorName`, which spells
  -- the prefix as STRING LITERALS (`"$Box..intVal!"`, `s!"$Box..{tag}Val!"`, …), so renaming
  -- this datatype means editing those literals in lockstep. (The box CONSTRUCTOR names —
  -- `BoxInt`, `BoxComposite`, `Box..<datatype>` — are NOT `$`-prefixed, because they
  -- live in the constructor namespace and so do not clash with a user TYPE named `Box`; they
  -- are not protected against a user CONSTRUCTOR of the same name, which is a smaller and
  -- pre-existing exposure.)
  -- The `$` prefix is what keeps the plain name `Box` available to user programs: a
  -- `datatype Box`, `datatype Box<T>`, `composite Box` or `composite Box<T>` is legal and does
  -- not collide with this type. No filter is needed to protect it: `$Box` is in the reserved
  -- namespace and this pass is its only producer, so there is no synthetic duplicate to drop —
  -- and therefore no risk that a name-based drop removes a user declaration along with it. A
  -- second producer would reintroduce that risk, so it belongs here rather than elsewhere.
  let boxDatatype : TypeDefinition :=
    .Datatype { name := "$Box", typeArgs := [], constructors := state1.usedBoxConstructors }

  let types := fieldDatatype :: boxDatatype :: heapConstants.types ++ types'
  pure { program with
    staticProcedures := heapConstants.staticProcedures ++ procs',
    staticFields := heapGlobalField :: program.staticFields,
    types }

/-- Pipeline pass: heap parameterization. -/
public def heapParameterizationPass : LoweringPass where
  name := "HeapParameterization"
  documentation := "Transforms procedures that interact with the heap by adding explicit heap parameters. The heap is modeled as `TotalMap Composite (TotalMap Field $Box)`. Procedures that write the heap receive both an input and output heap parameter; procedures that only read the heap receive an input heap parameter. Field reads and writes are rewritten to use `readField` and `updateField` functions."
  needsResolves := false -- Only resolve again after completing HeapParam, ModifiesClauses and TypeHierarchy. These are logically one pass.
  run := fun _ p m =>
    match heapParameterization m p with
    | .ok p' => (p', [], {})
    | .error e => (p, [Message.fromString s!"Internal error in HeapParameterization: {e}" .strataBug], {})
  comesAfter := [⟨ eliminateValueInReturnsPass.meta, "eliminate value in returns need to come before any passes that change the amount of output parameters of procedures." ⟩]
  comesBefore := [
    ⟨ liftImperativeExpressionsPass.meta, "the heap parameterization pass introduces assignments (to the heap variables) that need to be lifted."⟩,
    ⟨ eliminateReturnStatementsPass.meta, "the heap parameterization pass introduces helper procedures that use return statements. This dependency could be eliminated if those helpers would assign to the output parameter directly."⟩]

end Strata.Laurel

end -- public section
