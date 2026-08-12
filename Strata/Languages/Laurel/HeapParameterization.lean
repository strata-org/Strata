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
The heap is modeled as a `Heap` datatype containing a `data: Map Composite (Map Field $Box)` map
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
-- without an import cycle. The exceptional-contract heap effects (a case's guard,
-- postconditions and frame) and the `Throw`/`Try` expression cases are
-- handled there.

structure TransformState where
  heapReaders : Std.HashSet Nat
  heapWriters : Std.HashSet Nat
  freshCounter : Nat := 0  -- Counter for generating fresh variable names
  /-- Box constructors used during transformation, collected for datatype generation -/
  usedBoxConstructors : List DatatypeConstructor := []

@[expose] abbrev TransformM := ExceptT String (StateM TransformState)

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

/-- Get the `$Box` destructor name for a given Laurel HighType.
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
      if isDatatype model name then s!"$Box..{name.text}Val!"
      else "$Box..compositeVal!"
  | .TBv n => s!"$Box..bv{n}Val!"
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
      if isDatatype model name then s!"Box..{name.text}"
      else "BoxComposite"
  | .TBv n => s!"BoxBv{n}"
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
      if isDatatype model name then
        some { name := s!"Box..{name.text}", args := [{ name := s!"{name.text}Val", type := ⟨.UserDefined name, syntheticSource⟩ }] }
      else
        some { name := "BoxComposite", args := [{ name := "compositeVal", type := ⟨.UserDefined "Composite", syntheticSource⟩ }] }
  | .TBv n =>
        some { name := s!"BoxBv{n}", args := [{ name := s!"bv{n}Val", type := ⟨.TBv n, syntheticSource⟩ }] }
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


/-- Whether an output is the output side of an existing inout parameter. Core
    emits inout receivers in input order, before output-only receivers. -/
private def isInoutOutput (proc : Procedure) (output : Parameter) : Bool :=
  proc.inputs.any (·.name.text == output.name.text)

/-- Insert the heap output after all existing inout outputs and before ordinary
    outputs. This mirrors Core call-argument order when globals or explicit
    inouts coexist with the hidden heap. -/
private def outputsWithHeap (proc : Procedure) (heapParam : Parameter) : List Parameter :=
  let (inouts, ordinary) := proc.outputs.partition (isInoutOutput proc)
  inouts ++ [heapParam] ++ ordinary

/-- Apply `outputsWithHeap`'s ordering to an assignment's pre-heap targets. -/
private def targetsWithHeap (model : SemanticModel) (callee : Identifier)
    (heapTarget : VariableMd) (targets : List VariableMd) : List VariableMd :=
  let proc? := match model.get callee with
    | .staticProcedure proc | .instanceProcedure _ proc => some proc
    | _ => none
  match proc? with
  | some proc =>
      let paired := proc.outputs.zip targets
      let (inouts, ordinary) := paired.partition fun (output, _) => isInoutOutput proc output
      inouts.map (·.2) ++ [heapTarget] ++ ordinary.map (·.2)
  | none => heapTarget :: targets
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

/-- Whether heap lowering may introduce imperative heap-threading assignments. -/
inductive HeapTransformContext where
  | executable
  | specification

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
        let calleeReadsHeap ← readsHeap callee
        let calleeWritesHeap ← writesHeap callee
        if calleeWritesHeap then
          match context with
          | .specification =>
              -- Specifications are pure. Keep the source-level call shape so the
              -- pure-context validator reports the call itself, rather than a
              -- synthetic heap-threading assignment introduced by this pass.
              return [⟨.StaticCall callee (args' ++ [mkMd (.Var (.Local heapVar)) source]), source⟩]
          | .executable =>
            if valueUsed then
              let freshVar ← freshVarName
              let callWithHeap := ⟨ .Assign
                [mkVarMd (.Local heapVar) source, mkVarMd (.Declare ⟨freshVar, some (computeExprType model exprMd)⟩) source]
                (⟨ .StaticCall callee (args' ++ [mkMd (.Var (.Local heapVar)) source]), source ⟩), source ⟩
              return [callWithHeap, mkMd (.Var (.Local freshVar)) source]
            else
              -- Generate throwaway Declare targets for any non-heap outputs
              let procOutputs := match model.get callee with
                | .staticProcedure proc => proc.outputs
                | .instanceProcedure _ proc => proc.outputs
                | _ => []
              let extraTargets ← procOutputs.mapM fun out => do
                pure (mkVarMd (.Declare ⟨← freshVarName, some out.type⟩) source)
              let allTargets := mkVarMd (.Local heapVar) source :: extraTargets
              return [⟨ .Assign allTargets (⟨ .StaticCall callee (args' ++ [mkMd (.Var (.Local heapVar)) source]), source ⟩), source ⟩]
        else if calleeReadsHeap then
          return [⟨ .StaticCall callee (args' ++ [mkMd (.Var (.Local heapVar)) source]), source ⟩]
        else
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

      -- Process calls to heap mutating procedures
      let (newAssign, suffixes) ← do
        -- Detect calls and add a heap argument if needed
        let (v', addedHeap) <- match _hv : v.val with
          | .StaticCall callee args => do
            let args' <- args.mapM recurseOne
            let calleeWritesHeap ← writesHeap callee
            let calleeReadsHeap ← readsHeap callee
            if calleeWritesHeap then
              pure (⟨ .StaticCall callee (args' ++ [mkMd (.Var (.Local heapVar)) source]), v.source ⟩, true)
            else if calleeReadsHeap then
              pure (⟨ .StaticCall callee (args' ++ [mkMd (.Var (.Local heapVar)) source]), v.source ⟩, false)
            else
              pure (⟨ .StaticCall callee args', v.source ⟩, false)
          | .InstanceCall callTarget _callee args => do
            let _callTarget' ← recurseOne callTarget
            let _args' <- args.mapM recurseOne
            pure (⟨ .InstanceCall _callTarget' _callee _args', v.source ⟩, false)
          | _ =>
            pure (<- recurseOne v, false)
        let allTargets := if addedHeap
          then
            let heapTarget := mkVarMd (.Local heapVar) v.source
            match v.val with
            | .StaticCall callee _ => targetsWithHeap model callee heapTarget processedTargets
            | _ => heapTarget :: processedTargets
          else processedTargets
        let newAssign: AstNode StmtExpr := ⟨ StmtExpr.Assign allTargets v', source ⟩

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

      -- Return the list of statements directly (flattened into enclosing block)
      return newAssign :: suffixes

    | .PureFieldUpdate t f v => return [⟨ .PureFieldUpdate (← recurseOne t) f (← recurseOne v), source ⟩]
    | .New _ => return [exprMd]
    | .ReferenceEquals l r => return [⟨ .ReferenceEquals (← recurseOne l) (← recurseOne r), source ⟩]
    | .AsType target ty =>
        let target' ← recurseOne target true
        match context with
        | .specification =>
          -- Specifications are pure, so the target can be evaluated twice; a
          -- declared temp is not resolvable here (no inference in specs).
          let check : StmtExprMd := ⟨.Assert ⟨.IsType target' ty, source⟩ none, source⟩
          return [⟨.Block [check, target'] none, source⟩]
        | .executable =>
          -- Capture the target once: it is used both by the type check and as
          -- the result, and an effectful target (e.g. a heap-writing call)
          -- must run exactly once. No type annotation: the declared return
          -- type of a generic callee (e.g. `Result..err : Result<Val, Err> →
          -- Err`) names type parameters that are unbound here; the resolver
          -- infers the instantiated type.
          let result ← freshVarName
          let resultRef : StmtExprMd := ⟨.Var (.Local result), source⟩
          let capture : StmtExprMd := ⟨.Assign
            [⟨.Declare ⟨result, none⟩, source⟩] target', source⟩
          let check : StmtExprMd :=
            ⟨.Assert ⟨.IsType resultRef ty, source⟩ none, source⟩
          return [⟨.Block [capture, check, resultRef] none, source⟩]
    | .IsType t ty => return [⟨ .IsType (← recurseOne t) ty, source ⟩]
    | .Quantifier mode p trigger b =>
      let trigger' ← trigger.attach.mapM fun ⟨t, _⟩ => recurseOne t
      return [⟨.Quantifier mode p trigger' (← recurseOne b), source⟩]
    | .Assigned n => return [⟨ .Assigned (← recurseOne n), source ⟩]
    | .Old v => return [⟨ .Old (← recurseOne v), source ⟩]
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

/-- Check if `p` is a composite (heap-reference) parameter. -/
private def isCompositeParam (model : SemanticModel) (p : Parameter) : Bool :=
  match p.type.val with
  | .UserDefined name => !isDatatype model name
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

def heapTransformProcedure (model: SemanticModel) (proc : Procedure) : TransformM Procedure := do
  let heapName := heapVarName
  let uid ← Identifier.getUniqueId proc.name
  let readsHeap := (← get).heapReaders.contains uid
  let writesHeap := (← get).heapWriters.contains uid
  -- Kept before the generic specification pass because a `throwsOn` case's frame
  -- targets need a modifies-specific transform rather than the uniform one; the
  -- writes-heap branch below rebuilds the cases from these.
  let originalThrowsOn := proc.throwsOn
  let proc ← if readsHeap || writesHeap then
    mapProcedureSpecificationsM (heapTransformSpecificationExpr heapName model) proc
  else
    pure proc

  if writesHeap then
    -- This procedure writes the heap — $heap appears in both inputs and outputs
    -- (true inout). Core's two-state semantics provide `old $heap` automatically.
    -- The heap goes LAST in the inputs so explicit arguments evaluate before the
    -- heap is sampled at call sites (see the module docs). In the outputs it
    -- follows all pre-existing inouts (globals and explicit inout parameters)
    -- and precedes output-only values, matching Core's receiver order.
    let heapParam : Parameter := { name := heapName, type := ⟨.UserDefined "Heap", proc.name.source⟩ }

    let inputs' := proc.inputs ++ [heapParam]
    let outputs' := outputsWithHeap proc heapParam

    -- `proc` already had its specification expressions (preconditions,
    -- relies/guarantees) heap-transformed at the top of this function. Prepend
    -- the free heap-well-formedness preconditions (subjects are the original,
    -- untransformed composite inputs).
    let preconditions' := heapWellFormednessPreconds model proc.inputs heapName ++ proc.preconditions

    let bodyValueIsUsed := !proc.outputs.isEmpty
    -- Synthesized postconditions: allocation counter is monotone, and every
    -- composite output is allocated in the output heap.
    let wfPostconditions :=
      heapMonotonicityPostcond proc.name.source heapName
        :: heapOutputAllocationPostconds model proc.outputs heapName
    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformSpecificationExpr heapName model bodyExpr
          pure (.Transparent bodyExpr')
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformSpecificationExpr heapName model))
          let impl' ← match impl with
            | some implExpr =>
                let implExpr' ← heapTransformExpr heapName model implExpr bodyValueIsUsed
                pure (some implExpr')
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
      inputs := inputs',
      outputs := outputs',
      preconditions := preconditions',
      throwsOn := throwsOn',
      body := body' }

  else if readsHeap then
    -- This procedure only reads the heap - add $heap as input only.
    -- Use the prelude `Heap` datatype for the parameter type (see the
    -- writes-heap branch above for rationale).
    let heapParam : Parameter := { name := heapName, type := ⟨.UserDefined "Heap", proc.name.source⟩ }
    let inputs' := proc.inputs ++ [heapParam]

    -- Specifications were heap-transformed at the top of this function; prepend
    -- the free heap-well-formedness preconditions over the original inputs.
    let preconditions' := heapWellFormednessPreconds model proc.inputs heapName ++ proc.preconditions

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
      inputs := inputs',
      preconditions := preconditions',
      body := body' }

  else
    -- This procedure doesn't read or write the heap - no changes needed
    return proc

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
  -- Generate the `$Box` datatype from all constructors used during transformation.
  -- It replaces the `$Box` placeholder from CoreDefinitionsForLaurel.lean, so it
  -- must carry the same name: `select`/`update`/`mapConst` are declared to return
  -- `$Box`, and those references are re-resolved after this pass. The reserved `$`
  -- prefix keeps it distinct from a user-declared `Box`.
  let boxDatatype : TypeDefinition :=
    .Datatype { name := "$Box", typeArgs := [], constructors := state1.usedBoxConstructors }

  let types := fieldDatatype :: boxDatatype :: heapConstants.types ++
    -- The filter is a hack to deal with another hack,
    -- the `$Box` placeholder that was added in CoreDefinitionsForLaurel.lean
    -- because Laurel does not support polymorphism yet. The `$Box` generated
    -- just above replaces it; a user-declared `Box` is a distinct type and
    -- must not be dropped here.
    types'.filter (fun td => td.name.text != "$Box")
  pure { program with
    staticProcedures := heapConstants.staticProcedures ++ procs',
    types }

/-- Pipeline pass: heap parameterization. -/
public def heapParameterizationPass : LoweringPass where
  name := "HeapParameterization"
  documentation := "Transforms procedures that interact with the heap by adding explicit heap parameters. The heap is modeled as `Map Composite (Map Field $Box)`. Procedures that write the heap receive both an input and output heap parameter; procedures that only read the heap receive an input heap parameter. Field reads and writes are rewritten to use `readField` and `updateField` functions."
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
