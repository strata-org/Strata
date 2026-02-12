/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat
import Strata.Util.Tactics

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


mutual
def collectExprMd (expr : StmtExprMd) : StateM AnalysisResult Unit := collectExpr expr.val
  termination_by sizeOf expr
  decreasing_by cases expr; term_by_mem

def collectExpr (expr : StmtExpr) : StateM AnalysisResult Unit := do
  match _: expr with
  | .FieldSelect target _ =>
      modify fun s => { s with readsHeapDirectly := true }; collectExprMd target
  | .InstanceCall target _ args => collectExprMd target; for a in args do collectExprMd a
  | .StaticCall callee args => modify fun s => { s with callees := callee :: s.callees }; for a in args do collectExprMd a
  | .IfThenElse c t e => collectExprMd c; collectExprMd t; if let some x := e then collectExprMd x
  | .Block stmts _ => for s in stmts do collectExprMd s
  | .LocalVariable _ _ i => if let some x := i then collectExprMd x
  | .While c i d b => collectExprMd c; collectExprMd b; if let some x := i then collectExprMd x; if let some x := d then collectExprMd x
  | .Return v => if let some x := v then collectExprMd x
  | .Assign assignTargets v =>
      -- Check if any target is a field assignment (heap write)
      for ⟨assignTarget, _⟩ in assignTargets.attach do
        match assignTarget.val with
        | .FieldSelect _ _ =>
            modify fun s => { s with writesHeapDirectly := true }
        | _ => pure ()
        collectExprMd assignTarget
      collectExprMd v
  | .PureFieldUpdate t _ v => collectExprMd t; collectExprMd v
  | .PrimitiveOp _ args => for a in args do collectExprMd a
  | .ReferenceEquals l r => collectExprMd l; collectExprMd r
  | .AsType t _ => collectExprMd t
  | .IsType t _ => collectExprMd t
  | .Forall _ _ b => collectExprMd b
  | .Exists _ _ b => collectExprMd b
  | .Assigned n => collectExprMd n
  | .Old v => collectExprMd v
  | .Fresh v => collectExprMd v
  | .Assert c => collectExprMd c
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
    | .Opaque postcond impl _ =>
        let r1 := (collectExprMd postcond).run {} |>.2
        let r2 := match impl with
          | some e => (collectExprMd e).run {} |>.2
          | none => {}
        { readsHeapDirectly := r1.readsHeapDirectly || r2.readsHeapDirectly,
          writesHeapDirectly := r1.writesHeapDirectly || r2.writesHeapDirectly,
          callees := r1.callees ++ r2.callees }
    | .Abstract postcond => (collectExprMd postcond).run {} |>.2
  -- Also analyze precondition
  let precondResult := (collectExprMd proc.precondition).run {} |>.2
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
  fieldTypes : List (Identifier × HighTypeMd) := []  -- Maps field names to their value types
  freshCounter : Nat := 0  -- Counter for generating fresh variable names

abbrev TransformM := StateM TransformState

def addFieldConstant (name : Identifier) (valueType : HighTypeMd) : TransformM Unit :=
  modify fun s => if s.fieldConstants.any (·.name == name) then s
    else { s with fieldConstants := { name := name, type := ⟨.TTypedField valueType, #[] ⟩ } :: s.fieldConstants }

def lookupFieldType (name : Identifier) : TransformM (Option HighTypeMd) := do
  return (← get).fieldTypes.find? (·.1 == name) |>.map (·.2)

def readsHeap (name : Identifier) : TransformM Bool := do
  return (← get).heapReaders.contains name

def writesHeap (name : Identifier) : TransformM Bool := do
  return (← get).heapWriters.contains name

def freshVarName : TransformM Identifier := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  return s!"$tmp{s.freshCounter}"

/-- Helper to wrap a StmtExpr into StmtExprMd with empty metadata -/
def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, #[]⟩

/--
Transform an expression, adding heap parameters where needed.
- `heapVar`: the name of the heap variable to use
- `valueUsed`: whether the result value of this expression is used (affects optimization of heap-writing calls)
-/
def heapTransformExpr (heapVar : Identifier) (expr : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd :=
  recurse expr valueUsed
where
  recurse (expr : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd := do
    let md := expr.md
    match _h : expr.val with
    | .FieldSelect selectTarget fieldName =>
        let fieldType ← lookupFieldType fieldName
        addFieldConstant fieldName fieldType.get!
        let selectTarget' ← recurse selectTarget
        return ⟨ .StaticCall "heapRead" [mkMd (.Identifier heapVar), selectTarget', mkMd (.Identifier fieldName)], md ⟩
    | .StaticCall callee args =>
        let args' ← args.mapM (recurse ·)
        let calleeReadsHeap ← readsHeap callee
        let calleeWritesHeap ← writesHeap callee
        if calleeWritesHeap then
          if valueUsed then
            let freshVar ← freshVarName
            let varDecl := mkMd (.LocalVariable freshVar ⟨.TInt, #[]⟩ none)
            let callWithHeap := ⟨ .Assign
              [mkMd (.Identifier heapVar), mkMd (.Identifier freshVar)]
              (⟨ .StaticCall callee (mkMd (.Identifier heapVar) :: args'), md ⟩), md ⟩
            return ⟨ .Block [varDecl, callWithHeap, mkMd (.Identifier freshVar)] none, md ⟩
          else
            return ⟨ .Assign [mkMd (.Identifier heapVar)] (⟨ .StaticCall callee (mkMd (.Identifier heapVar) :: args'), md ⟩), md ⟩
        else if calleeReadsHeap then
          return ⟨ .StaticCall callee (mkMd (.Identifier heapVar) :: args'), md ⟩
        else
          return ⟨ .StaticCall callee args', md ⟩
    | .InstanceCall callTarget callee args =>
        let t ← recurse callTarget
        let args' ← args.mapM (recurse ·)
        return ⟨ .InstanceCall t callee args', md ⟩
    | .IfThenElse c t e =>
        let e' ← match e with | some x => some <$> recurse x valueUsed | none => pure none
        return ⟨ .IfThenElse (← recurse c) (← recurse t valueUsed) e', md ⟩
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
        return ⟨ .Block stmts' label, md ⟩
    | .LocalVariable n ty i =>
        let i' ← match i with | some x => some <$> recurse x | none => pure none
        return ⟨ .LocalVariable n ty i', md ⟩
    | .While c i d b =>
        let i' ← match i with | some x => some <$> recurse x | none => pure none
        return ⟨ .While (← recurse c) i' d (← recurse b false), md ⟩
    | .Return v =>
        let v' ← match v with | some x => some <$> recurse x | none => pure none
        return ⟨ .Return v', md ⟩
    | .Assign targets v =>
        match targets with
        | [fieldSelectMd] =>
          match _h2 : fieldSelectMd.val with
          | .FieldSelect target fieldName =>
            let fieldType ← lookupFieldType fieldName
            match fieldType with
            | some ty => addFieldConstant fieldName ty
            | none => addFieldConstant fieldName ⟨.TInt, #[]⟩
            let target' ← recurse target
            let v' ← recurse v
            let heapAssign := ⟨ .Assign [mkMd (.Identifier heapVar)] (mkMd (.StaticCall "heapStore" [mkMd (.Identifier heapVar), target', mkMd (.Identifier fieldName), v'])), md ⟩
            if valueUsed then
              return ⟨ .Block [heapAssign, v'] none, md ⟩
            else
              return heapAssign
          | _ =>
            let tgt' ← recurse fieldSelectMd
            return ⟨ .Assign [tgt'] (← recurse v), md ⟩
        | [] =>
            return ⟨ .Assign [] (← recurse v), md ⟩
        | tgt :: rest =>
            let tgt' ← recurse tgt
            let targets' ← rest.mapM (recurse ·)
            return ⟨ .Assign (tgt' :: targets') (← recurse v), md ⟩
    | .PureFieldUpdate t f v => return ⟨ .PureFieldUpdate (← recurse t) f (← recurse v), md ⟩
    | .PrimitiveOp op args =>
      let args' ← args.mapM (recurse ·)
      return ⟨ .PrimitiveOp op args', md ⟩
    | .ReferenceEquals l r => return ⟨ .ReferenceEquals (← recurse l) (← recurse r), md ⟩
    | .AsType t ty => return ⟨ .AsType (← recurse t) ty, md ⟩
    | .IsType t ty => return ⟨ .IsType (← recurse t) ty, md ⟩
    | .Forall n ty b => return ⟨ .Forall n ty (← recurse b), md ⟩
    | .Exists n ty b => return ⟨ .Exists n ty (← recurse b), md ⟩
    | .Assigned n => return ⟨ .Assigned (← recurse n), md ⟩
    | .Old v => return ⟨ .Old (← recurse v), md ⟩
    | .Fresh v => return ⟨ .Fresh (← recurse v), md ⟩
    | .Assert c => return ⟨ .Assert (← recurse c), md ⟩
    | .Assume c => return ⟨ .Assume (← recurse c), md ⟩
    | .ProveBy v p => return ⟨ .ProveBy (← recurse v) (← recurse p), md ⟩
    | .ContractOf ty f => return ⟨ .ContractOf ty (← recurse f), md ⟩
    | _ => return expr
    termination_by sizeOf expr
    decreasing_by
      all_goals simp_wf
      all_goals
        have hval := WithMetadata.sizeOf_val_lt expr
        rw [_h] at hval; simp at hval
        first
          | term_by_mem
          | -- For the FieldSelect-inside-Assign case: target < fieldSelectMd < expr
            (have hfs := WithMetadata.sizeOf_val_lt fieldSelectMd; term_by_mem)

def heapTransformProcedure (proc : Procedure) : TransformM Procedure := do
  let heapInName := "$heap_in"
  let heapOutName := "$heap_out"
  let readsHeap := (← get).heapReaders.contains proc.name
  let writesHeap := (← get).heapWriters.contains proc.name

  if writesHeap then
    -- This procedure writes the heap - add heap_in as input and heap_out as output
    -- At the start, assign heap_in to heap_out, then use heap_out throughout
    let heapInParam : Parameter := { name := heapInName, type := ⟨.THeap, #[]⟩ }
    let heapOutParam : Parameter := { name := heapOutName, type := ⟨.THeap, #[]⟩ }

    let inputs' := heapInParam :: proc.inputs
    let outputs' := heapOutParam :: proc.outputs

    -- Precondition uses heap_in (the input state)
    let precondition' ← heapTransformExpr heapInName proc.precondition

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          -- First assign heap_in to heap_out, then transform body using heap_out
          let assignHeapOut := mkMd (.Assign [mkMd (.Identifier heapOutName)] (mkMd (.Identifier heapInName)))
          let bodyExpr' ← heapTransformExpr heapOutName bodyExpr
          pure (.Transparent (mkMd (.Block [assignHeapOut, bodyExpr'] none)))
      | .Opaque postcond impl modif =>
          -- Postcondition uses heap_out (the output state)
          let postcond' ← heapTransformExpr heapOutName postcond
          let impl' ← match impl with
            | some implExpr =>
                let assignHeapOut := mkMd (.Assign [mkMd (.Identifier heapOutName)] (mkMd (.Identifier heapInName)))
                let implExpr' ← heapTransformExpr heapOutName implExpr
                pure (some (mkMd (.Block [assignHeapOut, implExpr'] none)))
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
    let heapInParam : Parameter := { name := heapInName, type := ⟨.THeap, #[]⟩ }
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
