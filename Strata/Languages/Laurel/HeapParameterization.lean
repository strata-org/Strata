/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat

/-
Heap Parameterization Pass

Transforms transparent procedures that read fields (or call procedures that read the heap)
by adding an explicit `heap: Heap` parameter. Field reads are translated to calls to
`read(heap, <fieldConstant>)`.
-/

namespace Strata.Laurel

structure AnalysisResult where
  readsHeapDirectly : Bool := false
  callees : List Identifier := []

partial def collectExpr (expr : StmtExpr) : StateM AnalysisResult Unit := do
  match expr with
  | .FieldSelect target _ =>
      modify fun s => { s with readsHeapDirectly := true }; collectExpr target
  | .InstanceCall target _ args => modify fun s => { s with readsHeapDirectly := true }; collectExpr target; for a in args do collectExpr a
  | .StaticCall callee args => modify fun s => { s with callees := callee :: s.callees }; for a in args do collectExpr a
  | .IfThenElse c t e => collectExpr c; collectExpr t; if let some x := e then collectExpr x
  | .Block stmts _ => for s in stmts do collectExpr s
  | .LocalVariable _ _ i => if let some x := i then collectExpr x
  | .While c i d b => collectExpr c; collectExpr b; if let some x := i then collectExpr x; if let some x := d then collectExpr x
  | .Return v => if let some x := v then collectExpr x
  | .Assign t v _ => collectExpr t; collectExpr v
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
  match proc.body with
  | .Transparent b =>
      dbg_trace s!"Analyzing proc {proc.name} body: {Std.Format.pretty (Std.ToFormat.format b)}"
      (collectExpr b).run {} |>.2
  | _ => {}

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

structure TransformState where
  fieldConstants : List Constant := []
  heapReaders : List Identifier

abbrev TransformM := StateM TransformState

def addFieldConstant (name : Identifier) : TransformM Unit :=
  modify fun s => if s.fieldConstants.any (·.name == name) then s
    else { s with fieldConstants := { name := name, type := .TField } :: s.fieldConstants }

def readsHeap (name : Identifier) : TransformM Bool := do
  return (← get).heapReaders.contains name

partial def heapTransformExpr (heap : Identifier) (expr : StmtExpr) : TransformM StmtExpr := do
  match expr with
  | .FieldSelect target fieldName =>
      addFieldConstant fieldName
      let t ← heapTransformExpr heap target
      return .StaticCall "heapRead" [.Identifier heap, t, .Identifier fieldName]
  | .StaticCall callee args =>
      let args' ← args.mapM (heapTransformExpr heap)
      return if ← readsHeap callee then .StaticCall callee (.Identifier heap :: args') else .StaticCall callee args'
  | .InstanceCall target callee args =>
      let t ← heapTransformExpr heap target
      let args' ← args.mapM (heapTransformExpr heap)
      return .InstanceCall t callee (.Identifier heap :: args')
  | .IfThenElse c t e => return .IfThenElse (← heapTransformExpr heap c) (← heapTransformExpr heap t) (← e.mapM (heapTransformExpr heap))
  | .Block stmts label => return .Block (← stmts.mapM (heapTransformExpr heap)) label
  | .LocalVariable n ty i => return .LocalVariable n ty (← i.mapM (heapTransformExpr heap))
  | .While c i d b => return .While (← heapTransformExpr heap c) (← i.mapM (heapTransformExpr heap)) (← d.mapM (heapTransformExpr heap)) (← heapTransformExpr heap b)
  | .Return v => return .Return (← v.mapM (heapTransformExpr heap))
  | .Assign t v md =>
      match t with
      | .FieldSelect target fieldName =>
          addFieldConstant fieldName
          let target' ← heapTransformExpr heap target
          let v' ← heapTransformExpr heap v
          -- heap := heapStore(heap, target, field, value)
          return .Assign (.Identifier heap) (.StaticCall "heapStore" [.Identifier heap, target', .Identifier fieldName, v']) md
      | _ => return .Assign (← heapTransformExpr heap t) (← heapTransformExpr heap v) md
  | .PureFieldUpdate t f v => return .PureFieldUpdate (← heapTransformExpr heap t) f (← heapTransformExpr heap v)
  | .PrimitiveOp op args => return .PrimitiveOp op (← args.mapM (heapTransformExpr heap))
  | .ReferenceEquals l r => return .ReferenceEquals (← heapTransformExpr heap l) (← heapTransformExpr heap r)
  | .AsType t ty => return .AsType (← heapTransformExpr heap t) ty
  | .IsType t ty => return .IsType (← heapTransformExpr heap t) ty
  | .Forall n ty b => return .Forall n ty (← heapTransformExpr heap b)
  | .Exists n ty b => return .Exists n ty (← heapTransformExpr heap b)
  | .Assigned n => return .Assigned (← heapTransformExpr heap n)
  | .Old v => return .Old (← heapTransformExpr heap v)
  | .Fresh v => return .Fresh (← heapTransformExpr heap v)
  | .Assert c md => return .Assert (← heapTransformExpr heap c) md
  | .Assume c md => return .Assume (← heapTransformExpr heap c) md
  | .ProveBy v p => return .ProveBy (← heapTransformExpr heap v) (← heapTransformExpr heap p)
  | .ContractOf ty f => return .ContractOf ty (← heapTransformExpr heap f)
  | other => return other

def heapTransformProcedure (proc : Procedure) : TransformM Procedure := do
  if (← get).heapReaders.contains proc.name then
    match proc.body with
    | .Transparent bodyExpr =>
        let body' ← heapTransformExpr "heap" bodyExpr
        return { proc with inputs := { name := "heap", type := .THeap } :: proc.inputs, body := .Transparent body' }
    | _ => return proc
  else return proc

def heapParameterization (program : Program) : Program :=
  let heapReaders := computeReadsHeap program.staticProcedures
  dbg_trace s!"Heap readers: {heapReaders}"
  let (procs', finalState) := (program.staticProcedures.mapM heapTransformProcedure).run { heapReaders }
  dbg_trace s!"Field constants: {finalState.fieldConstants.map (·.name)}"
  { program with staticProcedures := procs', constants := program.constants ++ finalState.fieldConstants }

end Strata.Laurel
