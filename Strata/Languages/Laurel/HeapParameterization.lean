/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat

/-
Heap Parameterization Pass

Transforms procedures that interact with the heap using a global `$heap` variable:

1. All procedures that read or write fields use the global `$heap` variable
   - Field reads are translated to calls to `heapRead($heap, <fieldConstant>)`
   - Field writes are translated to assignments to `$heap` via `heapStore`

2. No heap parameters are added to procedure signatures
   - The heap is accessed as a global variable
   - Procedure calls don't pass or receive heap values

The analysis is transitive: if procedure A calls procedure B, and B reads/writes the heap,
then A is also considered to read/write the heap.
-/

namespace Strata.Laurel

structure AnalysisResult where
  readsHeapDirectly : Bool := false
  writesHeapDirectly : Bool := false
  callees : List Identifier := []

partial def collectExpr (expr : StmtExpr) : StateM AnalysisResult Unit := do
  match expr with
  | .FieldSelect target _ =>
      modify fun s => { s with readsHeapDirectly := true }; collectExpr target
  | .InstanceCall target _ args => collectExpr target; for a in args do collectExpr a
  | .StaticCall callee args => modify fun s => { s with callees := callee :: s.callees }; for a in args do collectExpr a
  | .IfThenElse c t e => collectExpr c; collectExpr t; if let some x := e then collectExpr x
  | .Block stmts _ => for s in stmts do collectExpr s
  | .LocalVariable _ _ i => if let some x := i then collectExpr x
  | .While c i d b => collectExpr c; collectExpr b; if let some x := i then collectExpr x; if let some x := d then collectExpr x
  | .Return v => if let some x := v then collectExpr x
  | .Assign t v _ =>
      -- Check if this is a field assignment (heap write)
      match t with
      | .FieldSelect target _ =>
          modify fun s => { s with writesHeapDirectly := true }
          collectExpr target
      | _ => collectExpr t
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

partial def heapTransformExpr (heapVar : Identifier) (expr : StmtExpr) : TransformM StmtExpr := do
  match expr with
  | .FieldSelect target fieldName =>
      let fieldType ← lookupFieldType fieldName
      match fieldType with
      | some ty => addFieldConstant fieldName ty
      | none => addFieldConstant fieldName .TInt  -- Fallback to int if type unknown
      let t ← heapTransformExpr heapVar target
      return .StaticCall "heapRead" [.Identifier heapVar, t, .Identifier fieldName]
  | .StaticCall callee args =>
      let args' ← args.mapM (heapTransformExpr heapVar)
      -- Heap is global, so no need to pass it as parameter
      return .StaticCall callee args'
  | .InstanceCall target callee args =>
      let t ← heapTransformExpr heapVar target
      let args' ← args.mapM (heapTransformExpr heapVar)
      return .InstanceCall t callee args'
  | .IfThenElse c t e => return .IfThenElse (← heapTransformExpr heapVar c) (← heapTransformExpr heapVar t) (← e.mapM (heapTransformExpr heapVar))
  | .Block stmts label => return .Block (← stmts.mapM (heapTransformExpr heapVar)) label
  | .LocalVariable n ty i => return .LocalVariable n ty (← i.mapM (heapTransformExpr heapVar))
  | .While c i d b => return .While (← heapTransformExpr heapVar c) (← i.mapM (heapTransformExpr heapVar)) (← d.mapM (heapTransformExpr heapVar)) (← heapTransformExpr heapVar b)
  | .Return v => return .Return (← v.mapM (heapTransformExpr heapVar))
  | .Assign t v md =>
      match t with
      | .FieldSelect target fieldName =>
          let fieldType ← lookupFieldType fieldName
          match fieldType with
          | some ty => addFieldConstant fieldName ty
          | none => addFieldConstant fieldName .TInt  -- Fallback to int if type unknown
          let target' ← heapTransformExpr heapVar target
          let v' ← heapTransformExpr heapVar v
          -- Assign to global heap variable
          return .Assign (.Identifier heapVar) (.StaticCall "heapStore" [.Identifier heapVar, target', .Identifier fieldName, v']) md
      | _ => return .Assign (← heapTransformExpr heapVar t) (← heapTransformExpr heapVar v) md
  | .PureFieldUpdate t f v => return .PureFieldUpdate (← heapTransformExpr heapVar t) f (← heapTransformExpr heapVar v)
  | .PrimitiveOp op args => return .PrimitiveOp op (← args.mapM (heapTransformExpr heapVar))
  | .ReferenceEquals l r => return .ReferenceEquals (← heapTransformExpr heapVar l) (← heapTransformExpr heapVar r)
  | .AsType t ty => return .AsType (← heapTransformExpr heapVar t) ty
  | .IsType t ty => return .IsType (← heapTransformExpr heapVar t) ty
  | .Forall n ty b => return .Forall n ty (← heapTransformExpr heapVar b)
  | .Exists n ty b => return .Exists n ty (← heapTransformExpr heapVar b)
  | .Assigned n => return .Assigned (← heapTransformExpr heapVar n)
  | .Old v => return .Old (← heapTransformExpr heapVar v)
  | .Fresh v => return .Fresh (← heapTransformExpr heapVar v)
  | .Assert c md => return .Assert (← heapTransformExpr heapVar c) md
  | .Assume c md => return .Assume (← heapTransformExpr heapVar c) md
  | .ProveBy v p => return .ProveBy (← heapTransformExpr heapVar v) (← heapTransformExpr heapVar p)
  | .ContractOf ty f => return .ContractOf ty (← heapTransformExpr heapVar f)
  | other => return other

def heapTransformProcedure (proc : Procedure) : TransformM Procedure := do
  let heapName := "$heap"
  let readsHeap := (← get).heapReaders.contains proc.name
  let writesHeap := (← get).heapWriters.contains proc.name

  if readsHeap || writesHeap then
    -- This procedure reads or writes the heap - transform to use global $heap
    let precondition' ← heapTransformExpr heapName proc.precondition

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          let bodyExpr' ← heapTransformExpr heapName bodyExpr
          pure (.Transparent bodyExpr')
      | .Opaque postcond impl modif =>
          let postcond' ← heapTransformExpr heapName postcond
          let impl' ← impl.mapM (heapTransformExpr heapName)
          let modif' ← modif.mapM (heapTransformExpr heapName)
          pure (.Opaque postcond' impl' modif')
      | .Abstract postcond =>
          let postcond' ← heapTransformExpr heapName postcond
          pure (.Abstract postcond')

    return { proc with
      precondition := precondition',
      body := body' }

  else
    -- This procedure doesn't read or write the heap
    -- Still transform contracts in case they reference fields
    let precondition' ← heapTransformExpr heapName proc.precondition

    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          pure (.Transparent bodyExpr)
      | .Opaque postcond impl modif =>
          let postcond' ← heapTransformExpr heapName postcond
          pure (.Opaque postcond' impl modif)
      | .Abstract postcond =>
          let postcond' ← heapTransformExpr heapName postcond
          pure (.Abstract postcond')

    return { proc with
      precondition := precondition',
      body := body' }

def heapParameterization (program : Program) : Program × List Identifier :=
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
  ({ program with staticProcedures := procs', constants := program.constants ++ finalState.fieldConstants }, heapWriters)

end Strata.Laurel
