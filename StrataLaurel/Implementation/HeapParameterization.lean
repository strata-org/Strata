/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import StrataLaurel.Implementation.Resolution
public import StrataLaurel.Implementation.LaurelPass
public import StrataLaurel.Implementation.HeapAnalysis
import Std.Tactic.BVDecide.Normalize.Prop
import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator
import StrataLaurel.Implementation.MapStmtExpr
import StrataLaurel.Implementation.HeapParameterizationConstants
import StrataLaurel.Implementation.LaurelTypes
import Strata.Util.Tactics
import StrataLaurel.Implementation.LiftImperativeExpressions
import StrataLaurel.Implementation.EliminateValueInReturns
import StrataLaurel.Implementation.EliminateReturnStatements

/-
Heap Parameterization Pass

Transforms procedures that interact with the heap by adding explicit heap parameters.
The heap is modeled as a `Heap` datatype containing a `data: TotalMap int (TotalMap Field $Box)` map,
keyed by the `ref` of a `Composite`, and a `nextReference: int` for allocating new objects. `$Box` is a
sum type with constructors for each primitive type (BoxInt, BoxBool, BoxFloat64, BoxComposite). The
`Field` datatype has one constructor per heap field that `LowerComposite` declared, and `$allocate()`
becomes a read of `nextReference` followed by `increment`.

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
-- `computeWritesHeap`) now lives in `StrataLaurel.Implementation.HeapAnalysis`, so
-- it can be shared with `Resolution` (which uses it to diagnose no-op `old(...)`)
-- without an import cycle.

structure TransformState where
  heapReaders : Std.HashSet Nat
  heapWriters : Std.HashSet Nat
  heapFields : Std.HashMap String HeapField := {}
  freshCounter : Nat := 0  -- Counter for generating fresh variable names
  /-- Box constructors used during transformation, collected for datatype generation -/
  usedBoxConstructors : List DatatypeConstructor := []

abbrev TransformM := ExceptT String (StateM TransformState)

/-- The `Heap` type as a `HighTypeMd`, at the given source. -/
private def heapType (source : FileRange) : HighTypeMd := ⟨.UserDefined heapTypeName, source⟩

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

/-- Heap box constructor name for value-kind `tag`. -/
def boxCtorName (tag : String) : Identifier := s!"Box${tag}"

/-- The `$Box` variant's field leaf for `tag` (shared by the constructor field and destructor). -/
def boxFieldLeaf (tag : String) : String := s!"{tag}Val"

/-- Unsafe selector (destructor) on `$Box` for the box variant of `tag`. -/
def boxDestructorForTag (tag : String) : Identifier := s!"$Box..{boxFieldLeaf tag}!"

/-- Get the Box destructor name for a given Laurel HighType.
    For UserDefined datatypes, uses "$Box..<datatypeName>Val!";
    for Composite types, uses "$Box..compositeVal!".

    Constrained types do not need resolving here: `ConstrainedTypeElim` runs
    before this pass and has already lowered every constrained type to its base
    type (and removed the constrained type definitions), so `ty` is never a
    constrained-type reference. -/
def boxDestructorName (ty : HighType) : Identifier :=
  match ty with
  | .TInt => "$Box..intVal!"
  | .TBool => "$Box..boolVal!"
  | .TFloat64 => "$Box..float64Val!"
  | .TReal => "$Box..realVal!"
  | .TString => "$Box..stringVal!"
  | .UserDefined name =>
      if name.text == compositeTypeName.text then "$Box..compositeVal!"
      else boxDestructorForTag name.text
  | .TBv n => s!"$Box..bv{n}Val!"
  -- Generic datatype instantiation `Bx<int>` + built-in `TotalMap`: one box variant per
  -- instantiation, named via `appliedBoxTag`. (`.TSet` is unreachable — LaurelGrammar.st has
  -- only `totalMapType`, no Set production — kept for symmetry with `.TMap`.)
  | .Applied .. | .TMap .. | .TSet .. =>
    match appliedBoxTag ty with
    | some tag => boxDestructorForTag tag
    | none => dbg_trace f!"BUG, boxDestructorName bad type {ty}"; "boxDestructorNameError"
  | _ => dbg_trace f!"BUG, boxDestructorName bad type {ty}"; "boxDestructorNameError"

/-- Get the Box constructor name for a given Laurel HighType. For datatype/opaque/generic-inst
    types uses `boxCtorName` (`Box$<tag>`); scalars are `BoxInt`/…; composites `BoxComposite`. -/
def boxConstructorName (ty : HighType) : Identifier :=
  match ty with
  | .TInt => "BoxInt"
  | .TBool => "BoxBool"
  | .TFloat64 => "BoxFloat64"
  | .TReal => "BoxReal"
  | .TString => "BoxString"
  | .UserDefined name =>
      if name.text == compositeTypeName.text then "BoxComposite"
      else boxCtorName name.text
  | .TBv n => s!"BoxBv{n}"
  -- Generic datatype instantiation `Bx<int>`, and built-in collections `TotalMap`/`Set`.
  | .Applied .. | .TMap .. | .TSet .. =>
    match appliedBoxTag ty with
    | some tag => boxCtorName tag
    | none => dbg_trace s!"BUG, boxConstructorName bad type: {repr ty}"; "boxConstructorNameError"
  | ty => dbg_trace s!"BUG, boxConstructorName bad type: {repr ty}"; "boxConstructorNameError"

/-- Synthetic source location for compiler-generated Box datatype definitions. -/
private def syntheticSource : FileRange :=
  { file := .file "StrataLaurel/Implementation/HeapParameterization.lean", range := SourceRange.none }

/-- Build the DatatypeConstructor for a Box variant from a HighType, for datatype generation -/
private def boxConstructorDef (ty : HighType) : Option DatatypeConstructor :=
  match ty with
  | .TInt => some { name := "BoxInt", args := [{ name := "intVal", type := ⟨.TInt, syntheticSource⟩ }] }
  | .TBool => some { name := "BoxBool", args := [{ name := "boolVal", type := ⟨.TBool, syntheticSource⟩ }] }
  | .TReal => some { name := "BoxReal", args := [{ name := "realVal", type := ⟨.TReal, syntheticSource⟩ }] }
  | .TFloat64 => some { name := "BoxFloat64", args := [{ name := "float64Val", type := ⟨.TFloat64, syntheticSource⟩ }] }
  | .TString => some { name := "BoxString", args := [{ name := "stringVal", type := ⟨.TString, syntheticSource⟩ }] }
  | .UserDefined name =>
      if name.text == compositeTypeName.text then
        some { name := "BoxComposite", args := [{ name := "compositeVal", type := ⟨.UserDefined compositeTypeName, syntheticSource⟩ }] }
      else
        some { name := boxCtorName name.text, args := [{ name := boxFieldLeaf name.text, type := ⟨.UserDefined name, syntheticSource⟩ }] }
  | .TBv n =>
        some { name := s!"BoxBv{n}", args := [{ name := s!"bv{n}Val", type := ⟨.TBv n, syntheticSource⟩ }] }
  -- `.Applied` generic datatypes + built-in `.TMap`/`.TSet`: the box variant carries the
  -- FULL type, so `translateType` lowers it to the right Core sort (`.tcons "Bx" [int]` for a
  -- datatype, `Core.mapTy k v` for Map) — keeping distinct instantiations in distinct boxes.
  | .Applied .. | .TMap .. | .TSet .. =>
    match appliedBoxTag ty with
    | some tag => some { name := boxCtorName tag, args := [{ name := boxFieldLeaf tag, type := ⟨ty, syntheticSource⟩ }] }
    | none => dbg_trace s!"BUG, boxConstructorDef bad type: {repr ty}"; none
  | ty => dbg_trace s!"BUG, boxConstructorDef bad type: {repr ty}"; none

/-- Record a Box constructor use in the transform state -/
private def recordBoxConstructor (ty : HighType) : TransformM Unit := do
  let ctorOption := boxConstructorDef ty
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

private def freshVarName (namePrefix : String) : TransformM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"{namePrefix}{s.freshCounter}"

/-- Helper to wrap a StmtExpr into StmtExprMd with the given source -/
private def mkMd (e : StmtExpr) (source : FileRange) : StmtExprMd := { val := e, source }
private def mkVarMd (v : Variable) (source : FileRange) : VariableMd := { val := v, source }

private def wrapList (source : FileRange) : List StmtExprMd → StmtExprMd
  | [single] => single
  | many => ⟨.Block many none [] none, source⟩

/--
Transform an expression, adding heap parameters where needed.
- `heapVar`: the name of the heap variable to use
- `valueUsed`: whether the result value of this expression is used (affects optimization of heap-writing calls)
-/
def heapTransformExpr (heapVar : Identifier) (expr : StmtExprMd)
    (valueUsed : Bool := true) : TransformM StmtExprMd :=
  recurseOne expr valueUsed
where
  recurseOne (exprMd : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd :=
    wrapList exprMd.source <$> recurse exprMd valueUsed
  termination_by (sizeOf exprMd, 1)
  recurse (exprMd : StmtExprMd) (valueUsed : Bool := true) : TransformM (List StmtExprMd) := do
    let ⟨expr, source⟩ := exprMd
    match _h : expr with
    | .Var (.Field selectTarget fieldName) => do
        let some heapField := (← get).heapFields[fieldName.text]?
          | return [⟨ .Hole, source ⟩]
        let valTy := heapField.type
        let selectTarget' ← recurseOne selectTarget
        let readExpr := ⟨ .StaticCall readFieldName [mkMd (.Var (.Local heapVar)) source, selectTarget', mkMd (.StaticCall heapField.location.text [] []) source] [], source ⟩
        -- Unwrap Box: apply the appropriate destructor
        recordBoxConstructor valTy.val
        return [mkMd (.StaticCall (boxDestructorName valTy.val) [readExpr] []) source]
    | .StaticCall callee [] _ =>
        if callee.text == allocateProcName then
          let ref ← freshVarName "$allocated"
          let heapRead := mkMd (.Var (.Local heapVar)) source
          let saveRef := mkMd (.Assign [mkVarMd (.Declare ⟨ref, some ⟨.TInt, source⟩⟩) source]
            (mkMd (.StaticCall heapNextReferenceAccessor [heapRead] []) source)) source
          let updateHeap := mkMd (.Assign [mkVarMd (.Local heapVar) source]
            (mkMd (.StaticCall incrementName [heapRead] []) source)) source
          return [mkMd (.Block [saveRef, updateHeap, mkMd (.Var (.Local ref)) source] none [] none) source]
        else
          return [exprMd]
    | .StaticCall callee args tyArgs =>
        let args' ← args.mapM (recurseOne ·)
        -- No heap threading: handled by `GlobalParameterization` (see `heapGlobalField`).
        return [⟨ .StaticCall callee args' tyArgs, source ⟩]
    | .InstanceCall callTarget callee args =>
        let t ← recurseOne callTarget
        let args' ← args.mapM (recurseOne ·)
        return [⟨ .InstanceCall t callee args', source ⟩]
    | .IfThenElse c t e =>
        let e' ← match e with | some x => some <$> recurseOne x valueUsed | none => pure none
        return [⟨ .IfThenElse (← recurseOne c) (← recurseOne t valueUsed) e', source ⟩]
    | .Block stmts label invs d =>
        let invs' ← invs.mapM (recurseOne ·)
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
        return [⟨ .Block stmts' label invs' d, source ⟩]
    | .While c invs d b postTest =>
        let invs' ← invs.mapM (recurseOne ·)
        return [⟨ .While (← recurseOne c) invs' d (← recurseOne b false) postTest, source ⟩]
    | .Return v =>
        let v' ← v.attach.mapM fun ⟨x, _⟩ => recurseOne x
        return [⟨ .Return v', source ⟩]
    | .Assign targets v =>

      -- Process field targets
      let (processedTargets, updateStatements) <-
        targets.attach.foldlM (init := ([], [])) fun (accTargets, accStmts) ⟨t, _⟩ =>
          match _htv : t.val with
          | .Field target fieldName => do
              let some heapField := (← get).heapFields[fieldName.text]?
                -- Unresolved field name = a write to an unmodeled object's attribute. Drop it from the heap
                -- model (retarget to a throwaway local; emit no updateField) — an untracked field write is
                -- unobservable in the heap abstraction.
                | do
                  let discardVar ← freshVarName "$droppedWrite"
                  return (accTargets ++ [mkVarMd (.Declare ⟨discardVar, some ⟨.Unknown, source⟩⟩) source], accStmts)
              let valTy := heapField.type
              recordBoxConstructor valTy.val
              let freshVar ← freshVarName "$writeValue"
              let target' ← recurseOne target
              let boxedVal := mkMd (.StaticCall (boxConstructorName valTy.val) [mkMd (.Var (.Local freshVar)) source] []) source
              let updateStmt : StmtExprMd := ⟨ .Assign [mkVarMd (.Local heapVar) source]
                (mkMd (.StaticCall updateFieldName [mkMd (.Var (.Local heapVar)) source, target', mkMd (.StaticCall heapField.location.text [] []) source, boxedVal] []) source), source ⟩
              return (accTargets ++ [mkVarMd (.Declare ⟨freshVar, some valTy⟩) source], accStmts ++ [updateStmt])
          | _ => return (accTargets ++ [t], accStmts)

      let (newAssign, suffixes) ← do
        let v' ← recurseOne v
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

private def isCompositeParam (p : Parameter) : Bool :=
  match p.type.val with
  | .UserDefined name => name.text == compositeTypeName.text
  | _ => false

/-! Heap well-formedness conditions below are emitted `free`:
    assumed for reference values appearing *directly* as  parameters/outputs,
    but not for indirectly reachable references (composite fields, set elements).
    Closing that gap needs axioms over custom types. -/

/-- For each composite parameter `p`, the free precondition
    `Composite..ref!(p) < Heap..nextReference!(heapVar)` (`p` is allocated) -/
private def heapWellFormednessPreconds
    (inputs : List Parameter) (heapVar : Identifier) : List Condition :=
  inputs.filterMap fun p =>
    if isCompositeParam p then
      let src := p.name.source
      let pRead := { val := .Var (.Local p.name), source := src }
      let pRef := { val := .StaticCall compositeRefAccessor [pRead] [], source := src }
      let heapRead := { val := .Var (.Local heapVar), source := src }
      let counter := { val := .StaticCall heapNextReferenceAccessor [heapRead] [], source := src }
      let allocated := { val := .StaticCall "$intLt" [pRef, counter] [], source := src }
      some { condition := allocated, summary := some "input is allocated on the heap", mode := .Assume }
    else none

/-- The free postcondition
    `Heap..nextReference!($heap_in) <= Heap..nextReference!($heap)` -
    the top of heap pointer never decreases. -/
private def heapMonotonicityPostcond (source : FileRange)
    (heapVar : Identifier) : Condition :=
  let heapRead := { val := .Var (.Local heapVar), source }
  let nextRef := { val := .StaticCall heapNextReferenceAccessor [heapRead] [], source }
  let inCounter := { val := .Old nextRef, source }
  let outCounter := nextRef
  { condition := { val := .StaticCall "$intLe" [inCounter, outCounter] [], source },
    summary := some "monotonic heap pointer", mode := .Assume }

/-- For each composite output `o`, the free postcondition
    `Composite..ref!(o) < Heap..nextReference!($heap)` - a returned
    composite is allocated in the output heap. -/
private def heapOutputAllocationPostconds
    (outputs : List Parameter) (heapOutVar : Identifier) : List Condition :=
  outputs.filterMap fun o =>
    if isCompositeParam o then
      let src := o.name.source
      let oRead := { val := .Var (.Local o.name), source := src }
      let oRef := { val := .StaticCall compositeRefAccessor [oRead] [], source := src }
      let heapRead := { val := .Var (.Local heapOutVar), source := src }
      let counter := { val := .StaticCall heapNextReferenceAccessor [heapRead] [], source := src }
      some { condition := { val := .StaticCall "$intLt" [oRef, counter] [], source := src },
             summary := some "output is allocated on the heap", mode := .Assume }
    else none

/-- Heap-transform a pure specification expression without introducing
heap-threading assignments for calls to heap-writing procedures. -/
def heapTransformSpecificationExpr (heapName : Identifier)
    (expr : StmtExprMd) : TransformM StmtExprMd :=
  heapTransformExpr heapName expr

/-- Heap-transform a modifies entry. A field target `o#f` is kept symbolic
(only its owner is lowered) so the modifies pass can match it structurally. -/
def heapTransformModifiesEntry (heapName : Identifier)
    (entry : StmtExprMd) : TransformM StmtExprMd := do
  match entry.val with
  | .Var (.Field target fieldName) =>
      let target' ← heapTransformExpr heapName target
      let fieldName' := match (← get).heapFields[fieldName.text]? with
        | some heapField => { text := heapField.location.text, source := fieldName.source }
        | none => fieldName
      return { entry with val := .Var (.Field target' fieldName') }
  | _ => heapTransformExpr heapName entry

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

def heapTransformProcedure (proc : Procedure) : TransformM Procedure := do
  let heapName := heapVarName
  let uid ← Identifier.getUniqueId proc.name
  let readsHeap := (← get).heapReaders.contains uid
  let writesHeap := (← get).heapWriters.contains uid
  -- Transform every out-of-body spec field (preconditions, decreases, invokeOn, axioms,
  -- throwsOn) at ONE site for both heap branches, so no branch can silently skip a field.
  -- The body is NOT transformed here — each branch does that itself.
  --
  -- Kept before the branches because a `throwsOn` case's frame targets need a
  -- modifies-specific transform rather than the uniform one; the writes-heap branch
  -- below rebuilds the cases from these. (A heap-neutral procedure has no `throwsOn` —
  -- `EliminateExceptions` cleared it upstream.)
  let originalThrowsOn := proc.throwsOn
  let proc ←
    if readsHeap || writesHeap then mapProcedureSpecificationsM (heapTransformSpecificationExpr heapName) proc
    else pure proc

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
    -- the reference is bound to the global by the re-resolve that ends `ModifiesClauses`.
    -- Subjects are the untransformed `Composite` inputs.
    --
    -- An entry procedure gets none of them. Its globals are body locals, which a
    -- contract cannot see, and all three are `.Assume` (free) — they inform callers,
    -- and an entry procedure has none.
    let preconditions' :=
      if proc.isInterpretEntry then proc.preconditions
      else heapWellFormednessPreconds proc.inputs heapName ++ proc.preconditions

    let bodyValueIsUsed := !proc.outputs.isEmpty
    -- Synthesized postconditions: allocation counter is monotone, and every
    -- composite output is allocated in the output heap.
    let wfPostconditions :=
      if proc.isInterpretEntry then []
      else heapMonotonicityPostcond proc.name.source heapName
             :: heapOutputAllocationPostconds proc.outputs heapName
    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformSpecificationExpr heapName bodyExpr
          pure (.Transparent bodyExpr')
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformSpecificationExpr heapName))
          let impl' ← match impl with
            | some implExpr =>
                -- Collect snapshot locals from the *original* impl before the
                -- transform erases the `Snapshot`/labeled-`Old` nodes, then
                -- declare them at the body top (`Heap` did not exist earlier).
                let decls := snapshotLocalDecls heapName (proc.inputs.map (·.name)) implExpr
                let implExpr' ← heapTransformExpr heapName implExpr bodyValueIsUsed
                pure (some (prependStmts decls implExpr'))
            | none => pure none
          -- Targets keep field refs symbolic (structural matching in `ModifiesClauses`);
          -- a guard is an ordinary pre-state predicate and transforms like one.
          let modif' ← modif.mapM (fun g => do
            let targets' ← g.targets.mapM (heapTransformModifiesEntry heapName ·)
            let guard' ← g.guard.mapM (heapTransformSpecificationExpr heapName ·)
            pure ({ g with targets := targets', guard := guard' } : ModifiesGroup))
          pure (.Opaque (wfPostconditions ++ postconds') impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformSpecificationExpr heapName))
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
      let guard' ← heapTransformSpecificationExpr heapName blk.guard
      let modifies' ← blk.modifies.mapM (heapTransformModifiesEntry heapName ·)
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
      else heapWellFormednessPreconds proc.inputs heapName ++ proc.preconditions

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformSpecificationExpr heapName bodyExpr
          pure (.Transparent bodyExpr')
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformSpecificationExpr heapName))
          let impl' ← impl.mapM (heapTransformExpr heapName ·)
          -- Targets keep field refs symbolic (structural matching in `ModifiesClauses`);
          -- a guard is an ordinary pre-state predicate and transforms like one.
          let modif' ← modif.mapM (fun g => do
            let targets' ← g.targets.mapM (heapTransformModifiesEntry heapName ·)
            let guard' ← g.guard.mapM (heapTransformSpecificationExpr heapName ·)
            pure ({ g with targets := targets', guard := guard' } : ModifiesGroup))
          pure (.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformSpecificationExpr heapName))
          pure (.Abstract postconds')
      | .External => pure .External

    -- A read-only procedure has no exceptional frame (that implies writing the
    -- heap), and `EliminateExceptions` (before this pass) already cleared
    -- a `throwsOn` case's guard and postconditions, so there is no exceptional contract to transform here.
    return { proc with
      preconditions := preconditions',
      body := body' }

  else
    return proc

/-- The initial heap: nothing allocated, contents unspecified.

    `MkHeap(<TotalMap int (TotalMap Field $Box) hole>, 0)`.

    `nextReference = 0` is the part that carries meaning: no object is allocated, so
    no slot of the map is reachable and its contents are unobservable. A
    nondeterministic hole of the map type says exactly that.

    A constant map (`mapConst(mapConst(<$Box hole>))`) states the same thing, but
    `mapConst` is the one map operation with no native SMT encoding — cvc5 rejects
    `(as const ...)` in stable mode — so it carries a universally quantified defining
    axiom instead. A prover instantiates that axiom happily, but cannot build a
    *model* over it, so counterexample search inside a procedure holding such a value
    returns `unknown`: a false assertion then reports "could not be proved" rather
    than "does not hold". A hole carries no axiom, so an `entry` procedure verifies
    the same as any other.

    See `heapGlobalField` for where this is read. -/
private def emptyHeapInitializer : StmtExprMd :=
  let src := syntheticSource
  let boxTy : HighTypeMd := ⟨.UserDefined "$Box", src⟩
  let innerTy : HighTypeMd := ⟨.TMap ⟨.UserDefined "Field", src⟩ boxTy, src⟩
  let outerTy : HighTypeMd := ⟨.TMap ⟨.TInt, src⟩ innerTy, src⟩
  let mapHole : StmtExprMd := ⟨.Hole (deterministic := false) (type := some outerTy), src⟩
  mkMd (.StaticCall heapCtorName [mapHole, mkMd (.LiteralInt 0) src] []) src

/-- `$heap` as a file-scope global, threaded through signatures and call sites by
    `GlobalParameterization` like any other global. -/
private def heapGlobalField : Field :=
  { name := heapVarName
    isMutable := true
    type := ⟨.UserDefined heapTypeName, syntheticSource⟩
    initializer := some emptyHeapInitializer }

def heapParameterization (program : LaurelProgram) : Except String LaurelProgram := do
  -- Instance procedures are already lifted to `staticProcedures` by an earlier
  -- pass, so they're covered by the calls below.
  let heapReaders ← computeReadsHeap program.staticProcedures
  let heapWriters ← computeWritesHeap program.staticProcedures
  let heapFields := program.heapFields.foldl (init := {}) fun acc f => acc.insert f.name.text f
  let initState : TransformState := { heapReaders, heapWriters, heapFields }
  let userProcs := program.staticProcedures.filter (·.name.text != allocateProcName)
  let (result, state1) := (userProcs.mapM heapTransformProcedure).run.run initState
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
  let locations := program.heapFields.foldl (init := ([] : List Identifier)) fun acc f =>
    if acc.any (·.text == f.location.text) then acc
    else acc ++ [{ text := f.location.text, source := f.location.source }]
  let fieldDatatype : TypeDefinition :=
    .Datatype { name := "Field", typeArgs := [], constructors := locations.map fun l =>
      { name := l, args := [] } }
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

  let types := fieldDatatype :: boxDatatype :: heapConstants.types ++ program.types
  pure { program with
    staticProcedures := heapConstants.staticProcedures ++ procs',
    staticFields := heapGlobalField :: program.staticFields,
    heapFields := [],
    types }

/-- Pipeline pass: heap parameterization. -/
public def heapParameterizationPass : LaurelPass := .onUnordered {
  name := "HeapParameterization"
  creates := [
      NodeKind.StmtExpr.StaticCall,
      NodeKind.Procedure.inputs.cons,
      NodeKind.Pseudo.totalMap,
      NodeKind.Pseudo.box,
      NodeKind.Pseudo.heapVar,
      NodeKind.Pseudo.oldExpr,
      NodeKind.Pseudo.generatedReturn,
      NodeKind.Pseudo.statementExpression,
      NodeKind.LaurelProgram.staticFields.cons
    ]
  removes := [
      NodeKind.Pseudo.implicitHeap,
      NodeKind.StmtExpr.Var.var.Field,
      NodeKind.StmtExpr.PureFieldUpdate,
      NodeKind.StmtExpr.Snapshot,
      NodeKind.StmtExpr.Old.label?.some,
      NodeKind.LaurelProgram.heapFields.cons
    ]
  unsupported := [
      NodeKind.TypeDefinition.Composite,
      NodeKind.StmtExpr.New,
      NodeKind.StmtExpr.IsType,
      NodeKind.StmtExpr.AsType,
      NodeKind.TypeDefinition.Constrained,
      NodeKind.StmtExpr.Throw,
      NodeKind.StmtExpr.Try,
      NodeKind.StmtExpr.Return.value.some,
      NodeKind.LaurelProgram.staticFunctions.cons
    ]
  documentation := "Transforms procedures that interact with the heap by adding explicit heap parameters. The heap is modeled as `TotalMap int (TotalMap Field $Box)`, keyed by the reference of a `Composite`. Procedures that write the heap receive both an input and output heap parameter; procedures that only read the heap receive an input heap parameter. Field reads and writes are rewritten to use `readField` and `updateField` functions."
  needsResolves := false -- Only resolve again after completing HeapParam and ModifiesClauses. These are logically one pass.
  }
  fun _ p _ =>
    match heapParameterization p with
    | .ok p' => (p', [], {})
    | .error e => (p, [Message.fromString s!"Internal error in HeapParameterization: {e}" .strataBug], {})

end Strata.Laurel

end -- public section
