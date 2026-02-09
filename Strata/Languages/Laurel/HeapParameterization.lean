/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat

/-
Heap Parameterization Pass

Transforms procedures that interact with the heap by adding explicit heap parameters:

1. Procedures that write the heap get an inout heap parameter
   - Input: `heap : THeap`
   - Output: `heap : THeap`
   - Field writes become: `heap := heapStore(heap, obj, field, value)`

2. Procedures that only read the heap get an in heap parameter
   - Input: `heap : THeap`
   - Field reads become: `heapRead(heap, obj, field)`

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

namespace Strata.Laurel

structure AnalysisResult where
  readsHeapDirectly : Bool := false
  writesHeapDirectly : Bool := false
  callees : List Identifier := []

def collectExpr (expr : StmtExpr) : StateM AnalysisResult Unit := do
  match _: expr with
  | .FieldSelect target _ =>
      modify fun s => { s with readsHeapDirectly := true }; collectExpr target
  | .InstanceCall target _ args => collectExpr target; for a in args do collectExpr a
  | .StaticCall callee args => modify fun s => { s with callees := callee :: s.callees }; for a in args do collectExpr a
  | .IfThenElse c t e => collectExpr c; collectExpr t; if let some x := e then collectExpr x
  | .Block stmts _ => for s in stmts do collectExpr s
  | .LocalVariable _ _ i => if let some x := i then collectExpr x
  | .While c i d b => collectExpr c; collectExpr b; if let some x := i then collectExpr x; if let some x := d then collectExpr x
  | .Return v => if let some x := v then collectExpr x
  | .Assign assignTargets v _ =>
      -- Check if any target is a field assignment (heap write)
      for ⟨assignTarget, ht⟩ in assignTargets.attach do
        match teq: assignTarget with
        | .FieldSelect selectTarget _ =>
            modify fun s => { s with writesHeapDirectly := true }
            have h: sizeOf selectTarget < sizeOf assignTargets := by (have := List.sizeOf_lt_of_mem ht; simp_all; try omega)
            collectExpr selectTarget
        | _ => collectExpr assignTarget
      collectExpr v
  | .PureFieldUpdate t _ v => collectExpr t; collectExpr v
  | .PrimitiveOp _ args => for a in args do collectExpr a
  | .ReferenceEquals l r => collectExpr l; collectExpr r
  | .AsType t _ => collectExpr t
  | .IsType t _ => collectExpr t
  | .Forall _ _ b => collectExpr b
  | .Exists _ _ b => collectExpr b
  | .Assigned n => collectExpr n
  | .Old v => collectExpr v
  | .Fresh v => collectExpr v
  | .Assert c _ => collectExpr c
  | .Assume c _ => collectExpr c
  | .ProveBy v p => collectExpr v; collectExpr p
  | .ContractOf _ f => collectExpr f
  | _ => pure ()
  decreasing_by
    all_goals (simp_wf; try omega)
    all_goals (try subst_vars; try (rename_i x_in; have := List.sizeOf_lt_of_mem x_in); omega)

def analyzeProc (proc : Procedure) : AnalysisResult :=
  let bodyResult := match proc.body with
    | .Transparent b => (collectExpr b).run {} |>.2
    | .Opaque postcond impl _ =>
        let r1 := (collectExpr postcond).run {} |>.2
        let r2 := match impl with
          | some e => (collectExpr e).run {} |>.2
          | none => {}
        { readsHeapDirectly := r1.readsHeapDirectly || r2.readsHeapDirectly,
          writesHeapDirectly := r1.writesHeapDirectly || r2.writesHeapDirectly,
          callees := r1.callees ++ r2.callees }
    | .Abstract postcond => (collectExpr postcond).run {} |>.2
  -- Also analyze precondition
  let precondResult := (collectExpr proc.precondition).run {} |>.2
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
  fieldConstants : List Constant := []
  heapReaders : List Identifier
  heapWriters : List Identifier
  fieldTypes : List (Identifier × HighType) := []  -- Maps field names to their value types
  freshCounter : Nat := 0  -- Counter for generating fresh variable names

abbrev TransformM := StateM TransformState

def addFieldConstant (name : Identifier) (valueType : HighType) : TransformM Unit :=
  modify fun s => if s.fieldConstants.any (·.name == name) then s
    else { s with fieldConstants := { name := name, type := .TTypedField valueType } :: s.fieldConstants }

def lookupFieldType (name : Identifier) : TransformM (Option HighType) := do
  return (← get).fieldTypes.find? (·.1 == name) |>.map (·.2)

def readsHeap (name : Identifier) : TransformM Bool := do
  return (← get).heapReaders.contains name

def writesHeap (name : Identifier) : TransformM Bool := do
  return (← get).heapWriters.contains name

def freshVarName : TransformM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$tmp{s.freshCounter}"

/--
Transform an expression, adding heap parameters where needed.
- `heapVar`: the name of the heap variable to use
- `valueUsed`: whether the result value of this expression is used (affects optimization of heap-writing calls)
-/
def heapTransformExpr (heapVar : Identifier) (expr : StmtExpr) (valueUsed : Bool := true) : TransformM StmtExpr :=
  recurse expr valueUsed
where
  recurse (expr : StmtExpr) (valueUsed : Bool := true) : TransformM StmtExpr := do
    match _: expr with
    | .FieldSelect selectTarget fieldName =>
        let fieldType ← lookupFieldType fieldName
        match fieldType with
        | some ty => addFieldConstant fieldName ty
        | none => addFieldConstant fieldName .TInt
        return .StaticCall "heapRead" [.Identifier heapVar, ← recurse selectTarget, .Identifier fieldName]
    | .StaticCall callee args =>
        let args' ← args.mapM recurse
        let calleeReadsHeap ← readsHeap callee
        let calleeWritesHeap ← writesHeap callee
        if calleeWritesHeap then
          if valueUsed then
            let freshVar ← freshVarName
            let varDecl := StmtExpr.LocalVariable freshVar .TInt none
            let callWithHeap := StmtExpr.Assign
              [.Identifier heapVar, .Identifier freshVar]
              (.StaticCall callee (StmtExpr.Identifier heapVar :: args'))
              .empty
            return .Block [varDecl, callWithHeap, .Identifier freshVar] none
          else
            return .Assign [.Identifier heapVar] (.StaticCall callee (StmtExpr.Identifier heapVar :: args')) .empty
        else if calleeReadsHeap then
          return .StaticCall callee (StmtExpr.Identifier heapVar :: args')
        else
          return .StaticCall callee args'
    | .InstanceCall callTarget callee args =>
        let t ← recurse callTarget
        let args' ← args.mapM recurse
        return .InstanceCall t callee args'
    | .IfThenElse c t e =>
        let e' ← match e with | some x => some <$> recurse x valueUsed | none => pure none
        return .IfThenElse (← recurse c) (← recurse t valueUsed) e'
    | .Block stmts label =>
        let n := stmts.length
        let rec processStmts (idx : Nat) (remaining : List StmtExpr) : TransformM (List StmtExpr) := do
          match remaining with
          | [] => pure []
          | s :: rest =>
              let isLast := idx == n - 1
              let s' ← recurse s (isLast && valueUsed)
              let rest' ← processStmts (idx + 1) rest
              pure (s' :: rest')
        termination_by SizeOf.sizeOf remaining
        let stmts' ← processStmts 0 stmts
        return .Block stmts' label
    | .LocalVariable n ty i =>
        let i' ← match i with | some x => some <$> recurse x | none => pure none
        return .LocalVariable n ty i'
    | .While c i d b =>
        let i' ← match i with | some x => some <$> recurse x | none => pure none
        let d' ← match d with | some x => some <$> recurse x | none => pure none
        return .While (← recurse c) i' d' (← recurse b false)
    | .Return v =>
        let v' ← match v with | some x => some <$> recurse x | none => pure none
        return .Return v'
    | .Assign targets v md =>
        match targets with
        | [StmtExpr.FieldSelect target fieldName] =>
            let fieldType ← lookupFieldType fieldName
            match fieldType with
            | some ty => addFieldConstant fieldName ty
            | none => addFieldConstant fieldName .TInt
            let target' ← recurse target
            let v' ← recurse v
            let heapAssign := StmtExpr.Assign [StmtExpr.Identifier heapVar] (.StaticCall "heapStore" [.Identifier heapVar, target', .Identifier fieldName, v']) md
            if valueUsed then
              return .Block [heapAssign, v'] none
            else
              return heapAssign
        | [] =>
            return .Assign [] (← recurse v) md
        | tgt :: rest =>
            let tgt' ← recurse tgt
            let targets' ← rest.mapM recurse
            return .Assign (tgt' :: targets') (← recurse v) md
    | .PureFieldUpdate t f v => return .PureFieldUpdate (← recurse t) f (← recurse v)
    | .PrimitiveOp op args =>
      let args' ← args.mapM recurse
      return .PrimitiveOp op args'
    | .ReferenceEquals l r => return .ReferenceEquals (← recurse l) (← recurse r)
    | .AsType t ty => return .AsType (← recurse t) ty
    | .IsType t ty => return .IsType (← recurse t) ty
    | .Forall n ty b => return .Forall n ty (← recurse b)
    | .Exists n ty b => return .Exists n ty (← recurse b)
    | .Assigned n => return .Assigned (← recurse n)
    | .Old v => return .Old (← recurse v)
    | .Fresh v => return .Fresh (← recurse v)
    | .Assert c md => return .Assert (← recurse c) md
    | .Assume c md => return .Assume (← recurse c) md
    | .ProveBy v p => return .ProveBy (← recurse v) (← recurse p)
    | .ContractOf ty f => return .ContractOf ty (← recurse f)
    | other => return other
  termination_by sizeOf expr
  decreasing_by
    all_goals (simp_wf; try subst_vars)
    all_goals (try (rename_i h_in; have := List.sizeOf_lt_of_mem h_in; omega))
    all_goals(try omega)
    rename_i h_in _; have := List.sizeOf_lt_of_mem h_in; omega

def heapTransformProcedure (proc : Procedure) : TransformM Procedure := do
  let heapInName := "$heap_in"
  let heapOutName := "$heap_out"
  let readsHeap := (← get).heapReaders.contains proc.name
  let writesHeap := (← get).heapWriters.contains proc.name

  if writesHeap then
    -- This procedure writes the heap - add heap_in as input and heap_out as output
    -- At the start, assign heap_in to heap_out, then use heap_out throughout
    let heapInParam : Parameter := { name := heapInName, type := .THeap }
    let heapOutParam : Parameter := { name := heapOutName, type := .THeap }

    let inputs' := heapInParam :: proc.inputs
    let outputs' := heapOutParam :: proc.outputs

    -- Precondition uses heap_in (the input state)
    let precondition' ← heapTransformExpr heapInName proc.precondition

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          -- First assign heap_in to heap_out, then transform body using heap_out
          let assignHeapOut := StmtExpr.Assign [StmtExpr.Identifier heapOutName] (StmtExpr.Identifier heapInName) .empty
          let bodyExpr' ← heapTransformExpr heapOutName bodyExpr
          pure (.Transparent (.Block [assignHeapOut, bodyExpr'] none))
      | .Opaque postcond impl modif =>
          -- Postcondition uses heap_out (the output state)
          let postcond' ← heapTransformExpr heapOutName postcond
          let impl' ← match impl with
            | some implExpr =>
                let assignHeapOut := StmtExpr.Assign [StmtExpr.Identifier heapOutName] (StmtExpr.Identifier heapInName) .empty
                let implExpr' ← heapTransformExpr heapOutName implExpr
                pure (some (.Block [assignHeapOut, implExpr'] none))
            | none => pure none
          let modif' ← modif.mapM (heapTransformExpr heapOutName)
          pure (.Opaque postcond' impl' modif')
      | .Abstract postcond =>
          let postcond' ← heapTransformExpr heapOutName postcond
          pure (.Abstract postcond')

    return { proc with
      inputs := inputs',
      outputs := outputs',
      precondition := precondition',
      body := body' }

  else if readsHeap then
    -- This procedure only reads the heap - add heap_in as input only
    let heapInParam : Parameter := { name := heapInName, type := .THeap }
    let inputs' := heapInParam :: proc.inputs

    let precondition' ← heapTransformExpr heapInName proc.precondition

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformExpr heapInName bodyExpr
          pure (.Transparent bodyExpr')
      | .Opaque postcond impl modif =>
          let postcond' ← heapTransformExpr heapInName postcond
          let impl' ← impl.mapM (heapTransformExpr heapInName)
          let modif' ← modif.mapM (heapTransformExpr heapInName)
          pure (.Opaque postcond' impl' modif')
      | .Abstract postcond =>
          let postcond' ← heapTransformExpr heapInName postcond
          pure (.Abstract postcond')

    return { proc with
      inputs := inputs',
      precondition := precondition',
      body := body' }

  else
    -- This procedure doesn't read or write the heap - no changes needed
    return proc

def heapParameterization (program : Program) : Program :=
  let heapReaders := computeReadsHeap program.staticProcedures
  let heapWriters := computeWritesHeap program.staticProcedures
  -- Extract field types from composite type definitions
  let fieldTypes := program.types.foldl (fun acc typeDef =>
    match typeDef with
    | .Composite ct => acc ++ ct.fields.map (fun f => (f.name, f.type))
    | .Constrained _ => acc) []
  -- Debug: print heap readers and writers
  dbg_trace s!"Heap readers: {heapReaders}"
  dbg_trace s!"Heap writers: {heapWriters}"
  let (procs', finalState) := (program.staticProcedures.mapM heapTransformProcedure).run { heapReaders, heapWriters, fieldTypes }
  { program with staticProcedures := procs', constants := program.constants ++ finalState.fieldConstants }

end Strata.Laurel
