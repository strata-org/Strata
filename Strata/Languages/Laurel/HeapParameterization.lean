/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.Util.Tactics

/-
Heap Parameterization Pass

Transforms procedures that interact with the heap by adding explicit heap parameters.
The heap is modeled as a `Heap` datatype containing a `data: Map Composite (Map Field Box)` map
and a `nextReference: int` for allocating new objects. Box is a sum type with constructors for each
primitive type (BoxInt, BoxBool, BoxFloat64, BoxComposite). Composite is a type synonym for int.

1. Procedures that write the heap get an inout heap parameter
   - Input: `heap : THeap`
   - Output: `heap : THeap`
   - Field writes become: `heap := updateField(heap, obj, field, BoxT(value))`

2. Procedures that only read the heap get an in heap parameter
   - Input: `heap : THeap`
   - Field reads become: `Box..tVal(readField(heap, obj, field))`

3. Procedure calls are transformed:
   - Calls to heap-writing procedures in expressions:
     `f(args...) => (var freshVar: type; heapVar, freshVar := f(heapVar, args...); freshVar)`
   - Calls to heap-writing procedures as statements:
     `f(args...)` => `heap := f(heap, args...)`
   - Calls to heap-reading procedures:
     `f(args...)` => `f(heap, args...)`

The analysis is transitive: if procedure A calls procedure B, and B reads/writes the heap,
then A is also considered to read/write the heap.
-/

public section

namespace Strata.Laurel

structure AnalysisResult where
  readsHeapDirectly : Bool := false
  writesHeapDirectly : Bool := false
  callees : List Identifier := []


mutual
def collectExprMd (expr : StmtExprMd) : StateM AnalysisResult Unit := collectExpr expr.val
  termination_by sizeOf expr
  decreasing_by cases expr; term_by_mem

def collectExpr (expr : StmtExpr) : StateM AnalysisResult Unit := do
  match _: expr with
  | .FieldSelect target _ _ =>
      modify fun s => { s with readsHeapDirectly := true }; collectExprMd target
  | .InstanceCall target _ args => collectExprMd target; for a in args do collectExprMd a
  | .StaticCall callee args => modify fun s => { s with callees := callee :: s.callees }; for a in args do collectExprMd a
  | .IfThenElse c t e => collectExprMd c; collectExprMd t; if let some x := e then collectExprMd x
  | .Block stmts _ => for s in stmts do collectExprMd s
  | .LocalVariable _ _ i => if let some x := i then collectExprMd x
  | .While c invs d b => collectExprMd c; collectExprMd b; for inv in invs do collectExprMd inv; if let some x := d then collectExprMd x
  | .Return v => if let some x := v then collectExprMd x
  | .Assign assignTargets v =>
      -- Check if any target is a field assignment (heap write)
      for ⟨assignTarget, _⟩ in assignTargets.attach do
        match assignTarget.val with
        | .FieldSelect _ _ _ =>
            modify fun s => { s with writesHeapDirectly := true }
        | _ => pure ()
        collectExprMd assignTarget
      collectExprMd v
  | .PureFieldUpdate t _ v => collectExprMd t; collectExprMd v
  | .PrimitiveOp _ args => for a in args do collectExprMd a
  | .New _ => modify fun s => { s with writesHeapDirectly := true }
  | .ReferenceEquals l r => collectExprMd l; collectExprMd r
  | .AsType t _ => collectExprMd t
  | .IsType t _ => collectExprMd t
  | .Quantifier _ _ trigger b => if let some t := trigger then collectExprMd t; collectExprMd b
  | .Assigned n => collectExprMd n
  | .Old v => collectExprMd v
  | .Fresh v => collectExprMd v
  | .Assert ⟨c, _⟩ => collectExprMd c
  | .Assume c => collectExprMd c
  | .ProveBy v p => collectExprMd v; collectExprMd p
  | .ContractOf _ f => collectExprMd f
  | _ => pure ()
  termination_by sizeOf expr
  decreasing_by all_goals (simp_wf; try term_by_mem)
end

def analyzeProc (proc : Procedure) : AnalysisResult :=
  let bodyResult := match proc.body with
    | .Transparent b => (collectExprMd b).run {} |>.2
    | .Opaque postconds impl modif =>
        if impl.isNone && !modif.isEmpty then
          { readsHeapDirectly := true, writesHeapDirectly := true, callees := [] }
        else
          let r1 := postconds.foldl (fun (acc : AnalysisResult) (pc : Condition) =>
            let r := (collectExprMd pc.condition).run {} |>.2
            { readsHeapDirectly := acc.readsHeapDirectly || r.readsHeapDirectly,
              writesHeapDirectly := acc.writesHeapDirectly || r.writesHeapDirectly,
              callees := acc.callees ++ r.callees }) {}
          let r2 := match impl with
            | some e => (collectExprMd e).run {} |>.2
            | none => {}
          { readsHeapDirectly := r1.readsHeapDirectly || r2.readsHeapDirectly,
            writesHeapDirectly := r1.writesHeapDirectly || r2.writesHeapDirectly,
            callees := r1.callees ++ r2.callees }
    | .Abstract postconds => (postconds.forM (collectExprMd ·.condition)).run {} |>.2
    | .External => {}
  -- Also analyze preconditions
  let precondResult := (proc.preconditions.forM (collectExprMd ·.condition)).run {} |>.2
  { readsHeapDirectly := bodyResult.readsHeapDirectly || precondResult.readsHeapDirectly,
    writesHeapDirectly := bodyResult.writesHeapDirectly || precondResult.writesHeapDirectly,
    callees := bodyResult.callees ++ precondResult.callees }

def computeReadsHeap (procs : List Procedure) : List Identifier :=
  let info := procs.map fun p => (p.name, analyzeProc p)
  let direct := info.filterMap fun (n, r) => if r.readsHeapDirectly then some n else none
  let rec fixpoint (fuel : Nat) (current : List Identifier) : List Identifier :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let next := info.filterMap fun (n, r) =>
        if current.contains n then some n
        else if r.callees.any current.contains then some n
        else none
      if next.length == current.length then current else fixpoint fuel' next
  fixpoint procs.length direct

def computeWritesHeap (procs : List Procedure) : List Identifier :=
  let info := procs.map fun p => (p.name, analyzeProc p)
  let direct := info.filterMap fun (n, r) => if r.writesHeapDirectly then some n else none
  let rec fixpoint (fuel : Nat) (current : List Identifier) : List Identifier :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let next := info.filterMap fun (n, r) =>
        if current.contains n then some n
        else if r.callees.any current.contains then some n
        else none
      if next.length == current.length then current else fixpoint fuel' next
  fixpoint procs.length direct

structure TransformState where
  heapReaders : List Identifier
  heapWriters : List Identifier
  freshCounter : Nat := 0  -- Counter for generating fresh variable names
  /-- Box constructors used during transformation, collected for datatype generation -/
  usedBoxConstructors : List DatatypeConstructor := []
  usedDynamicField : List String := []

@[expose] abbrev TransformM := StateM TransformState

/-- Check whether a UserDefined type name refers to a Datatype (vs Composite) in the model -/
private def isDatatype (model : SemanticModel) (name : Identifier) : Bool :=
  match model.get name with
  | .datatypeDefinition _ => true
  | _ => false

/-- Get the Box destructor name for a given Laurel HighType.
    For UserDefined datatypes, uses "Box..<datatypeName>Val!";
    for Composite types, uses "Box..compositeVal!". -/
def boxDestructorName (model : SemanticModel) (ty : HighType) : Identifier :=
  match ty with
  | .TInt => "Box..intVal!"
  | .TBool => "Box..boolVal!"
  | .TFloat64 => "Box..float64Val!"
  | .TReal => "Box..realVal!"
  | .TString => "Box..stringVal!"
  | .UserDefined name =>
      if isDatatype model name then s!"Box..{name.text}Val!"
      else "Box..compositeVal!"
  | .TCore name => s!"Box..{name}Val!"
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
  | .TCore name => s!"Box..{name}"
  | ty => dbg_trace s!"BUG, boxConstructorName bad type: {repr ty}"; "boxConstructorNameError"

/-- Build the DatatypeConstructor for a Box variant from a HighType, for datatype generation -/
private def boxConstructorDef (model : SemanticModel) (ty : HighType) : Option DatatypeConstructor :=
  match ty with
  | .TInt => some { name := "BoxInt", args := [{ name := "intVal", type := ⟨.TInt, none⟩ }] }
  | .TBool => some { name := "BoxBool", args := [{ name := "boolVal", type := ⟨.TBool, none⟩ }] }
  | .TReal => some { name := "BoxReal", args := [{ name := "realVal", type := ⟨.TReal, none⟩ }] }
  | .TFloat64 => some { name := "BoxFloat64", args := [{ name := "float64Val", type := ⟨.TFloat64, none⟩ }] }
  | .TString => some { name := "BoxString", args := [{ name := "stringVal", type := ⟨.TString, none⟩ }] }
  | .UserDefined name =>
      if isDatatype model name then
        some { name := s!"Box..{name.text}", args := [{ name := s!"{name.text}Val", type := ⟨.UserDefined name, none⟩ }] }
      else
        some { name := "BoxComposite", args := [{ name := "compositeVal", type := ⟨.UserDefined "Composite", none⟩ }] }
  | .TCore name =>
        some { name := s!"Box..{name}", args := [{ name := s!"{name}Val", type := ⟨.TCore name, none⟩ }] }
  | ty => dbg_trace s!"BUG, boxConstructorDef bad type: {repr ty}"; none

/-- Record a Box constructor use in the transform state -/
private def recordBoxConstructor (model : SemanticModel) (ty : HighType) : TransformM Unit := do
  let ctorOption := boxConstructorDef model ty
  match ctorOption with
  | some ctor =>
      modify fun s =>
        if s.usedBoxConstructors.any (fun c => c.name == ctor.name) then s
        else { s with usedBoxConstructors := s.usedBoxConstructors ++ [ctor] }
  | _ => return

/-- Record a Box constructor use in the transform state -/
private def recordDynamicField (fieldName : String) : TransformM Unit := do
  modify fun s =>
    if fieldName ∈  s.usedDynamicField then s
        else { s with usedDynamicField := s.usedDynamicField ++ [fieldName] }


def readsHeap (name : Identifier) : TransformM Bool := do
  return (← get).heapReaders.contains name

def writesHeap (name : Identifier) : TransformM Bool := do
  return (← get).heapWriters.contains name

def freshVarName : TransformM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$tmp{s.freshCounter}"

/-- Helper to wrap a StmtExpr into StmtExprMd with empty metadata -/
private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }

/--
Resolve the owning composite type name for a field access by computing the target expression's type.
Returns the qualified field name "DeclaringType.fieldName".
-/
def resolveQualifiedFieldName (model: SemanticModel) (fieldName : Identifier) : Option String :=
  match model.get fieldName with
    | .field owner _ => owner.text ++ "." ++ fieldName.text
    | .unresolved _ => none
    | _ => dbg_trace s!"BUG: resolveQualifiedFieldName {fieldName} did resolved to something other than a field"; none

/--
Transform an expression, adding heap parameters where needed.
- `heapVar`: the name of the heap variable to use
- `env`: the type environment for resolving field owners
- `valueUsed`: whether the result value of this expression is used (affects optimization of heap-writing calls)
-/
def heapTransformExpr (heapVar : Identifier) (model: SemanticModel) (expr : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd :=
  recurse expr valueUsed
where
  recurse (exprMd : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd := do
    let ⟨expr, source⟩ := exprMd
    match _h : expr with
    | .FieldSelect selectTarget fieldName fieldTy => do
        let (qualifiedName, ty) ← do match fieldTy with
        | none =>
          let some qualifiedName := resolveQualifiedFieldName model fieldName
            | return ⟨ .Hole, source ⟩
          let valTy := (model.get fieldName).getType.val
          pure (qualifiedName, valTy)
        | some fieldTy =>
          let qualifiedName := s!"@DynamicField.{fieldName.text}"
          recordDynamicField fieldName.text
          pure (qualifiedName, fieldTy.val)
        recordBoxConstructor model ty
        let readExpr := ⟨ .StaticCall "readField" [mkMd (.Identifier heapVar), selectTarget, mkMd (.StaticCall qualifiedName [])], source ⟩
        return mkMd <| .StaticCall (boxDestructorName model ty) [readExpr]
    | .StaticCall callee args =>
        let args' ← args.mapM (recurse ·)
        let calleeReadsHeap ← readsHeap callee
        let calleeWritesHeap ← writesHeap callee
        if calleeWritesHeap then
          if valueUsed then
            let freshVar ← freshVarName
            let varDecl := mkMd (.LocalVariable freshVar (computeExprType model exprMd) none)
            let callWithHeap := ⟨ .Assign
              [mkMd (.Identifier heapVar), mkMd (.Identifier freshVar)]
              (⟨ .StaticCall callee (mkMd (.Identifier heapVar) :: args'), source ⟩), source ⟩
            return ⟨ .Block [varDecl, callWithHeap, mkMd (.Identifier freshVar)] none, source ⟩
          else
            return ⟨ .Assign [mkMd (.Identifier heapVar)] (⟨ .StaticCall callee (mkMd (.Identifier heapVar) :: args'), source ⟩), source ⟩
        else if calleeReadsHeap then
          return ⟨ .StaticCall callee (mkMd (.Identifier heapVar) :: args'), source ⟩
        else
          return ⟨ .StaticCall callee args', source ⟩
    | .InstanceCall callTarget callee args =>
        let t ← recurse callTarget
        let args' ← args.mapM (recurse ·)
        return ⟨ .InstanceCall t callee args', source ⟩
    | .IfThenElse c t e =>
        let e' ← match e with | some x => some <$> recurse x valueUsed | none => pure none
        return ⟨ .IfThenElse (← recurse c) (← recurse t valueUsed) e', source ⟩
    | .Block stmts label =>
        let n := stmts.length
        let rec processStmts (idx : Nat) (remaining : List StmtExprMd) : TransformM (List StmtExprMd) := do
          match remaining with
          | [] => pure []
          | s :: rest =>
              let isLast := idx == n - 1
              let s' ← recurse s (isLast && valueUsed)
              let rest' ← processStmts (idx + 1) rest
              pure (s' :: rest')
          termination_by sizeOf remaining
        let stmts' ← processStmts 0 stmts
        return ⟨ .Block stmts' label, source ⟩
    | .LocalVariable n ty i =>
        let i' ← match i with | some x => some <$> recurse x | none => pure none
        return ⟨ .LocalVariable n ty i', source ⟩
    | .While c invs d b =>
        let invs' ← invs.mapM (recurse ·)
        return ⟨ .While (← recurse c) invs' d (← recurse b false), source ⟩
    | .Return v =>
        let v' ← match v with | some x => some <$> recurse x | none => pure none
        return ⟨ .Return v', source ⟩
    | .Assign targets v =>
        match targets with
        | [⟨.FieldSelect target fieldName fieldTy, _⟩] =>
          let (qualifiedName, ty) ← do match fieldTy with
            | none =>
              let some qualifiedName := resolveQualifiedFieldName model fieldName
                | return ⟨ .Hole, source ⟩
              let valTy := (model.get fieldName).getType.val
              pure (qualifiedName, valTy)
            | some fieldTy =>
              let qualifiedName := s!"@DynamicField.{fieldName.text}"
              recordDynamicField fieldName.text
              pure (qualifiedName, fieldTy.val)
          recordBoxConstructor model ty
          let target' ← recurse target
          let v' ← recurse v
          let boxedVal := mkMd <| .StaticCall (boxConstructorName model ty) [v']
          let heapAssign := ⟨ .Assign [mkMd (.Identifier heapVar)]
              (mkMd (.StaticCall "updateField" [mkMd (.Identifier heapVar), target', mkMd (.StaticCall qualifiedName []), boxedVal])), source⟩
          if valueUsed then
            return ⟨ .Block [heapAssign, v'] none, source⟩
          else
            return heapAssign
        | [fieldSelectMd] =>
          let tgt' ← recurse fieldSelectMd
          return ⟨ .Assign [tgt'] (← recurse v), source ⟩
        | [] =>
            return ⟨ .Assign [] (← recurse v), source ⟩
        | tgt :: rest =>
            let tgt' ← recurse tgt
            let targets' ← rest.mapM (recurse ·)
            return ⟨ .Assign (tgt' :: targets') (← recurse v), source ⟩
    | .PureFieldUpdate t f v => return ⟨ .PureFieldUpdate (← recurse t) f (← recurse v), source ⟩
    | .PrimitiveOp op args =>
      let args' ← args.mapM (recurse ·)
      -- For == and != on Composite types, compare refs instead
      match op, args with
      | .Eq, [e1, _e2] =>
        let ty := (computeExprType model e1).val
        match ty with
        | .UserDefined _ =>
          let ref1 := mkMd (.StaticCall "Composite..ref!" [args'[0]!])
          let ref2 := mkMd (.StaticCall "Composite..ref!" [args'[1]!])
          return ⟨ .PrimitiveOp .Eq [ref1, ref2], source ⟩
        | _ => return ⟨ .PrimitiveOp op args', source ⟩
      | .Neq, [e1, _e2] =>
        let ty := (computeExprType model e1).val
        match ty with
        | .UserDefined _ =>
          let ref1 := mkMd (.StaticCall "Composite..ref!" [args'[0]!])
          let ref2 := mkMd (.StaticCall "Composite..ref!" [args'[1]!])
          return ⟨ .PrimitiveOp .Neq [ref1, ref2], source ⟩
        | _ => return ⟨ .PrimitiveOp op args', source ⟩
      | _, _ => return ⟨ .PrimitiveOp op args', source ⟩
    | .New _ => return exprMd
    | .ReferenceEquals l r => return ⟨ .ReferenceEquals (← recurse l) (← recurse r), source ⟩
    | .AsType t ty =>
        let t' ← recurse t valueUsed
        let isCheck := ⟨ .IsType t' ty, source ⟩
        let assertStmt := ⟨ .Assert { condition := isCheck }, source ⟩
        return ⟨ .Block [assertStmt, t'] none, source ⟩
    | .IsType t ty => return ⟨ .IsType (← recurse t) ty, source ⟩
    | .Quantifier mode p trigger b =>
      let trigger' ← trigger.attach.mapM fun ⟨t, _⟩ => recurse t
      return ⟨.Quantifier mode p trigger' (← recurse b), source⟩
    | .Assigned n => return ⟨ .Assigned (← recurse n), source ⟩
    | .Old v => return ⟨ .Old (← recurse v), source ⟩
    | .Fresh v => return ⟨ .Fresh (← recurse v), source ⟩
    | .Assert ⟨condExpr, summary⟩ =>
        return ⟨ .Assert { condition := ← recurse condExpr, summary }, source ⟩
    | .Assume c => return ⟨ .Assume (← recurse c), source ⟩
    | .ProveBy v p => return ⟨ .ProveBy (← recurse v) (← recurse p), source ⟩
    | .ContractOf ty f => return ⟨ .ContractOf ty (← recurse f), source ⟩
    | _ => return exprMd
    termination_by sizeOf exprMd

def heapTransformProcedure (model: SemanticModel) (proc : Procedure) : TransformM Procedure := do
  let heapName : Identifier := "$heap"
  let heapInName : Identifier := "$heap_in"
  let readsHeap := (← get).heapReaders.contains proc.name
  let writesHeap := (← get).heapWriters.contains proc.name

  if writesHeap then
    -- This procedure writes the heap - add $heap_in as input and $heap as output
    -- At the start, assign $heap_in to $heap, then use $heap throughout
    let heapInParam : Parameter := { name := heapInName, type := ⟨.THeap, none⟩ }
    let heapOutParam : Parameter := { name := heapName, type := ⟨.THeap, none⟩ }

    let inputs' := heapInParam :: proc.inputs
    let outputs' := heapOutParam :: proc.outputs

    -- Preconditions use $heap_in (the input state)
    let preconditions' ← proc.preconditions.mapM (·.mapM (heapTransformExpr heapInName model))

    let bodyValueIsUsed := !proc.outputs.isEmpty
    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          -- First assign $heap_in to $heap, then transform body using $heap
          let assignHeap := mkMd (.Assign [mkMd (.Identifier heapName)] (mkMd (.Identifier heapInName)))
          let bodyExpr' ← heapTransformExpr heapName model bodyExpr bodyValueIsUsed
          pure (.Transparent (mkMd (.Block [assignHeap, bodyExpr'] none)))
      | .Opaque postconds impl modif =>
          -- Postconditions use $heap (the output state)
          let postconds' ← postconds.mapM (·.mapM (heapTransformExpr heapName model))
          let impl' ← match impl with
            | some implExpr =>
                let assignHeap := mkMd (.Assign [mkMd (.Identifier heapName)] (mkMd (.Identifier heapInName)))
                let implExpr' ← heapTransformExpr heapName model implExpr bodyValueIsUsed
                pure (some (mkMd (.Block [assignHeap, implExpr'] none)))
            | none => pure none
          let modif' ← modif.mapM (heapTransformExpr heapName model ·)
          pure (.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformExpr heapName model))
          pure (.Abstract postconds')
      | .External => pure .External

    return { proc with
      inputs := inputs',
      outputs := outputs',
      preconditions := preconditions',
      body := body' }

  else if readsHeap then
    -- This procedure only reads the heap - add $heap as input only
    let heapParam : Parameter := { name := heapName, type := ⟨.THeap, none⟩ }
    let inputs' := heapParam :: proc.inputs

    let preconditions' ← proc.preconditions.mapM (·.mapM (heapTransformExpr heapName model))

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformExpr heapName model bodyExpr
          pure (.Transparent bodyExpr')
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformExpr heapName model))
          let impl' ← impl.mapM (heapTransformExpr heapName model ·)
          let modif' ← modif.mapM (heapTransformExpr heapName model ·)
          pure (.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (·.mapM (heapTransformExpr heapName model))
          pure (.Abstract postconds')
      | .External => pure .External

    return { proc with
      inputs := inputs',
      preconditions := preconditions',
      body := body' }

  else
    -- This procedure doesn't read or write the heap - no changes needed
    return proc

def heapParameterization (model: SemanticModel) (program : Program) : Program :=
  let program := { program with
    types := program.types
    staticProcedures := program.staticProcedures }
  let instanceProcs := program.types.foldl (fun acc td =>
    match td with
    | .Composite ct => acc ++ ct.instanceProcedures
    | _ => acc) ([] : List Procedure)
  let allProcs := program.staticProcedures ++ instanceProcs
  let heapReaders := computeReadsHeap allProcs
  let heapWriters := computeWritesHeap allProcs
  let initState : TransformState := { heapReaders, heapWriters }
  let (procs', state1) := (program.staticProcedures.mapM (heapTransformProcedure model)).run initState

  -- Remove fields from composite types since they are now stored in the heap
  -- Also transform instance procedures, accumulating used Box constructors
  let (types', state2) := program.types.foldl (fun (accTypes, accState) td =>
    match td with
    | .Composite ct =>
      let (instProcs', s') := (ct.instanceProcedures.mapM (heapTransformProcedure model)).run accState
      (accTypes ++ [.Composite { ct with fields := [], instanceProcedures := instProcs' }], s')
    | other => (accTypes ++ [other], accState))
    ([], state1)

  -- Collect all qualified field names and generate a Field datatype
  let dynamicFieldConstructors := state2.usedDynamicField.map fun fieldName => { name := s!"@DynamicField.{fieldName}", args := [] }
  let fieldNames := program.types.foldl (fun acc td =>
    match td with
    | .Composite ct => acc ++ ct.fields.map (fun f => (mkId $ ct.name.text ++ "." ++ f.name.text))
    | _ => acc) ([] : List Identifier)
  let fieldDatatype : TypeDefinition :=
    .Datatype { name := "Field", typeArgs := [], constructors := dynamicFieldConstructors ++ fieldNames.map fun n => { name := n, args := [] } }

  -- Generate Box datatype from all constructors used during transformation
  let boxDatatype : TypeDefinition :=
    .Datatype { name := "Box", typeArgs := [], constructors := state2.usedBoxConstructors }
  { program with
    staticProcedures := heapConstants.staticProcedures ++ procs',
    types := fieldDatatype :: boxDatatype :: heapConstants.types ++ types' }

end Strata.Laurel

end -- public section
