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

private theorem StmtExprMd.sizeOf_val_lt (e : StmtExprMd) : sizeOf e.val < sizeOf e := by
  cases e
  rename_i val md
  show sizeOf val < 1 + sizeOf val + sizeOf md
  omega

mutual
def collectExprMd (expr : StmtExprMd) : StateM AnalysisResult Unit := collectExpr expr.val
  termination_by sizeOf expr
  decreasing_by
    simp_wf
    have := StmtExprMd.sizeOf_val_lt expr
    omega

def collectExpr (expr : StmtExpr) : StateM AnalysisResult Unit := do
  match _: expr with
  | .FieldSelect target _ =>
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
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := StmtExprMd.sizeOf_val_lt ‹_›; omega)
      | (subst_vars; rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega)
end

def analyzeProc (proc : Procedure) : AnalysisResult :=
  let bodyResult := match proc.body with
    | .Transparent b => (collectExprMd b).run {} |>.2
    | .Opaque postconds impl modif =>
        let r1 := postconds.foldl (fun (acc : AnalysisResult) p =>
          let r := (collectExprMd p).run {} |>.2
          { readsHeapDirectly := acc.readsHeapDirectly || r.readsHeapDirectly,
            writesHeapDirectly := acc.writesHeapDirectly || r.writesHeapDirectly,
            callees := acc.callees ++ r.callees }) {}
        let r2 := match impl with
          | some e => (collectExprMd e).run {} |>.2
          | none => {}
        let r3 := match modif with
          | some e => (collectExprMd e).run {} |>.2
          | none => {}
        { readsHeapDirectly := r1.readsHeapDirectly || r2.readsHeapDirectly || r3.readsHeapDirectly,
          writesHeapDirectly := r1.writesHeapDirectly || r2.writesHeapDirectly || r3.writesHeapDirectly,
          callees := r1.callees ++ r2.callees ++ r3.callees }
    | .Abstract postconds =>
        postconds.foldl (fun (acc : AnalysisResult) p =>
          let r := (collectExprMd p).run {} |>.2
          { readsHeapDirectly := acc.readsHeapDirectly || r.readsHeapDirectly,
            writesHeapDirectly := acc.writesHeapDirectly || r.writesHeapDirectly,
            callees := acc.callees ++ r.callees }) {}
  -- Also analyze preconditions
  let precondResult := proc.preconditions.foldl (fun (acc : AnalysisResult) p =>
    let r := (collectExprMd p).run {} |>.2
    { readsHeapDirectly := acc.readsHeapDirectly || r.readsHeapDirectly,
      writesHeapDirectly := acc.writesHeapDirectly || r.writesHeapDirectly,
      callees := acc.callees ++ r.callees }) {}
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
  procedures : List Procedure := []  -- All procedures, for looking up return types

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

def lookupCalleeReturnType (callee : Identifier) : TransformM HighTypeMd := do
  let procs := (← get).procedures
  match procs.find? (·.name == callee) with
  | some proc =>
    match proc.outputs with
    | [single] => return single.type
    | _ => return ⟨.TInt, #[]⟩
  | none => return ⟨.TInt, #[]⟩

/-- Helper to wrap a StmtExpr into StmtExprMd, preserving source metadata from the original expression -/
def mkMd (md : Imperative.MetaData Core.Expression) (e : StmtExpr) : StmtExprMd := ⟨e, md⟩

/--
Transform an expression, adding heap parameters where needed.
- `heapVar`: the name of the heap variable to use
- `valueUsed`: whether the result value of this expression is used (affects optimization of heap-writing calls)
-/
partial def heapTransformExpr (heapVar : Identifier) (expr : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd :=
  recurse expr valueUsed
where
  recurse (expr : StmtExprMd) (valueUsed : Bool := true) : TransformM StmtExprMd := do
    let md := expr.md
    match expr.val with
    | .FieldSelect selectTarget fieldName =>
        let fieldType ← lookupFieldType fieldName
        addFieldConstant fieldName (fieldType.getD ⟨.TInt, #[]⟩)
        let selectTarget' ← recurse selectTarget
        return ⟨ .StaticCall "heapRead" [mkMd md (.Identifier heapVar), selectTarget', mkMd md (.Identifier fieldName)], md ⟩
    | .StaticCall callee args =>
        let args' ← args.mapM recurse
        let calleeReadsHeap ← readsHeap callee
        let calleeWritesHeap ← writesHeap callee
        if calleeWritesHeap then
          if valueUsed then
            let freshVar ← freshVarName
            let retType ← lookupCalleeReturnType callee
            let varDecl := mkMd md (.LocalVariable freshVar retType none)
            let callWithHeap := ⟨ .Assign
              [mkMd md (.Identifier heapVar), mkMd md (.Identifier freshVar)]
              (⟨ .StaticCall callee (mkMd md (.Identifier heapVar) :: args'), md ⟩), md ⟩
            return ⟨ .Block [varDecl, callWithHeap, mkMd md (.Identifier freshVar)] none, md ⟩
          else
            return ⟨ .Assign [mkMd md (.Identifier heapVar)] (⟨ .StaticCall callee (mkMd md (.Identifier heapVar) :: args'), md ⟩), md ⟩
        else if calleeReadsHeap then
          return ⟨ .StaticCall callee (mkMd md (.Identifier heapVar) :: args'), md ⟩
        else
          return ⟨ .StaticCall callee args', md ⟩
    | .InstanceCall callTarget callee args =>
        let t ← recurse callTarget
        let args' ← args.mapM recurse
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
        let stmts' ← processStmts 0 stmts
        return ⟨ .Block stmts' label, md ⟩
    | .LocalVariable n ty i =>
        let i' ← match i with | some x => some <$> recurse x | none => pure none
        return ⟨ .LocalVariable n ty i', md ⟩
    | .While c invs d b =>
        let invs' ← invs.mapM recurse
        let d' ← match d with | some x => some <$> recurse x | none => pure none
        return ⟨ .While (← recurse c) invs' d' (← recurse b false), md ⟩
    | .Return v =>
        let v' ← match v with | some x => some <$> recurse x | none => pure none
        return ⟨ .Return v', md ⟩
    | .Assign targets v =>
        match targets with
        | [fieldSelectMd] =>
          match fieldSelectMd.val with
          | .FieldSelect target fieldName =>
            let fieldType ← lookupFieldType fieldName
            match fieldType with
            | some ty => addFieldConstant fieldName ty
            | none => addFieldConstant fieldName ⟨.TInt, #[]⟩
            let target' ← recurse target
            let v' ← recurse v
            let heapAssign := ⟨ .Assign [mkMd md (.Identifier heapVar)] (mkMd md (.StaticCall "heapStore" [mkMd md (.Identifier heapVar), target', mkMd md (.Identifier fieldName), v'])), md ⟩
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
            let targets' ← rest.mapM recurse
            return ⟨ .Assign (tgt' :: targets') (← recurse v), md ⟩
    | .PureFieldUpdate t f v => return ⟨ .PureFieldUpdate (← recurse t) f (← recurse v), md ⟩
    | .PrimitiveOp op args =>
      let args' ← args.mapM recurse
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

    -- Preconditions use heap_in (the input state)
    let preconditions' ← proc.preconditions.mapM (heapTransformExpr heapInName)

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          -- First assign heap_in to heap_out, then transform body using heap_out
          let bmd := bodyExpr.md
          let assignHeapOut := mkMd bmd (.Assign [mkMd bmd (.Identifier heapOutName)] (mkMd bmd (.Identifier heapInName)))
          let bodyExpr' ← heapTransformExpr heapOutName bodyExpr false
          pure (.Transparent (mkMd bmd (.Block [assignHeapOut, bodyExpr'] none)))
      | .Opaque postconds impl modif =>
          -- Postconditions use heap_out (the output state)
          let postconds' ← postconds.mapM (heapTransformExpr heapOutName)
          let impl' ← match impl with
            | some implExpr =>
                let imd := implExpr.md
                let assignHeapOut := mkMd imd (.Assign [mkMd imd (.Identifier heapOutName)] (mkMd imd (.Identifier heapInName)))
                let implExpr' ← heapTransformExpr heapOutName implExpr false
                pure (some (mkMd imd (.Block [assignHeapOut, implExpr'] none)))
            | none => pure none
          let modif' ← modif.mapM (heapTransformExpr heapOutName)
          pure (.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (heapTransformExpr heapOutName)
          pure (.Abstract postconds')

    return { proc with
      inputs := inputs',
      outputs := outputs',
      preconditions := preconditions',
      body := body' }

  else if readsHeap then
    -- This procedure only reads the heap - add heap_in as input only
    let heapInParam : Parameter := { name := heapInName, type := ⟨.THeap, #[]⟩ }
    let inputs' := heapInParam :: proc.inputs

    let preconditions' ← proc.preconditions.mapM (heapTransformExpr heapInName)

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformExpr heapInName bodyExpr false
          pure (.Transparent bodyExpr')
      | .Opaque postconds impl modif =>
          let postconds' ← postconds.mapM (heapTransformExpr heapInName)
          let impl' ← impl.mapM (heapTransformExpr heapInName · false)
          let modif' ← modif.mapM (heapTransformExpr heapInName)
          pure (.Opaque postconds' impl' modif')
      | .Abstract postconds =>
          let postconds' ← postconds.mapM (heapTransformExpr heapInName)
          pure (.Abstract postconds')

    return { proc with
      inputs := inputs',
      preconditions := preconditions',
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
  let (procs', finalState) := (program.staticProcedures.mapM heapTransformProcedure).run { heapReaders, heapWriters, fieldTypes, procedures := program.staticProcedures }
  { program with staticProcedures := procs', constants := program.constants ++ finalState.fieldConstants }

end Strata.Laurel
