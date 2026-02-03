/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelFormat

/-
Heap Parameterization Pass

Transforms procedures that interact with the heap using a global `$heap` variable.
-/

namespace Strata.Laurel

structure AnalysisResult where
  readsHeapDirectly : Bool := false
  writesHeapDirectly : Bool := false
  callees : List Identifier := []

partial def collectExpr (expr : StmtExprMd) : StateM AnalysisResult Unit := do
  match expr.val with
  | .FieldSelect target _ =>
      modify fun s => { s with readsHeapDirectly := true }; collectExpr target
  | .InstanceCall target _ args => collectExpr target; for a in args do collectExpr a
  | .StaticCall callee args => modify fun s => { s with callees := callee :: s.callees }; for a in args do collectExpr a
  | .IfThenElse c t e => collectExpr c; collectExpr t; if let some x := e then collectExpr x
  | .Block stmts _ => for s in stmts do collectExpr s
  | .LocalVariable _ _ i => if let some x := i then collectExpr x
  | .While c invs d b => collectExpr c; for i in invs do collectExpr i; if let some x := d then collectExpr x; collectExpr b
  | .Return v => if let some x := v then collectExpr x
  | .Assign t v =>
      match t.val with
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
  | .Assert c => collectExpr c
  | .Assume c => collectExpr c
  | .ProveBy v p => collectExpr v; collectExpr p
  | .ContractOf _ f => collectExpr f
  | _ => pure ()

def analyzeProc (proc : Procedure) : AnalysisResult :=
  let bodyResult := match proc.body with
    | .Transparent b => (collectExpr b).run {} |>.2
    | .Opaque postconds impl _ _ =>
        let r1 : AnalysisResult := postconds.foldl (fun acc p =>
          let r := (collectExpr p).run {} |>.2
          { readsHeapDirectly := acc.readsHeapDirectly || r.readsHeapDirectly,
            writesHeapDirectly := acc.writesHeapDirectly || r.writesHeapDirectly,
            callees := acc.callees ++ r.callees }) {}
        let r2 := match impl with
          | some e => (collectExpr e).run {} |>.2
          | none => {}
        { readsHeapDirectly := r1.readsHeapDirectly || r2.readsHeapDirectly,
          writesHeapDirectly := r1.writesHeapDirectly || r2.writesHeapDirectly,
          callees := r1.callees ++ r2.callees }
    | .Abstract postconds =>
        postconds.foldl (fun (acc : AnalysisResult) p =>
          let r := (collectExpr p).run {} |>.2
          { readsHeapDirectly := acc.readsHeapDirectly || r.readsHeapDirectly,
            writesHeapDirectly := acc.writesHeapDirectly || r.writesHeapDirectly,
            callees := acc.callees ++ r.callees }) {}
  let precondResult : AnalysisResult := proc.preconditions.foldl (fun acc p =>
    let r := (collectExpr p).run {} |>.2
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

abbrev TransformM := StateM TransformState

def addFieldConstant (name : Identifier) : TransformM Unit :=
  modify fun s => if s.fieldConstants.any (·.name == name) then s
    else { s with fieldConstants := { name := name, type := ⟨.TField, {}⟩ } :: s.fieldConstants }

partial def heapTransformExpr (heapVar : Identifier) (expr : StmtExprMd) : TransformM StmtExprMd := do
  let md := expr.md
  let val' ← match expr.val with
  | .FieldSelect target fieldName =>
      addFieldConstant fieldName
      let t ← heapTransformExpr heapVar target
      pure <| .StaticCall "heapRead" [⟨.Identifier heapVar, md⟩, t, ⟨.Identifier fieldName, md⟩]
  | .StaticCall callee args =>
      let args' ← args.mapM (heapTransformExpr heapVar)
      pure <| .StaticCall callee args'
  | .InstanceCall target callee args =>
      let t ← heapTransformExpr heapVar target
      let args' ← args.mapM (heapTransformExpr heapVar)
      pure <| .InstanceCall t callee args'
  | .IfThenElse c t e =>
      pure <| .IfThenElse (← heapTransformExpr heapVar c) (← heapTransformExpr heapVar t) (← e.mapM (heapTransformExpr heapVar))
  | .Block stmts label =>
      pure <| .Block (← stmts.mapM (heapTransformExpr heapVar)) label
  | .LocalVariable n ty i =>
      pure <| .LocalVariable n ty (← i.mapM (heapTransformExpr heapVar))
  | .While c invs d b =>
      pure <| .While (← heapTransformExpr heapVar c) (← invs.mapM (heapTransformExpr heapVar)) (← d.mapM (heapTransformExpr heapVar)) (← heapTransformExpr heapVar b)
  | .Return v =>
      pure <| .Return (← v.mapM (heapTransformExpr heapVar))
  | .Assign t v =>
      match t.val with
      | .FieldSelect target fieldName =>
          addFieldConstant fieldName
          let target' ← heapTransformExpr heapVar target
          let v' ← heapTransformExpr heapVar v
          pure <| .Assign ⟨.Identifier heapVar, md⟩ ⟨.StaticCall "heapStore" [⟨.Identifier heapVar, md⟩, target', ⟨.Identifier fieldName, md⟩, v'], md⟩
      | _ => pure <| .Assign (← heapTransformExpr heapVar t) (← heapTransformExpr heapVar v)
  | .PureFieldUpdate t f v =>
      pure <| .PureFieldUpdate (← heapTransformExpr heapVar t) f (← heapTransformExpr heapVar v)
  | .PrimitiveOp op args =>
      pure <| .PrimitiveOp op (← args.mapM (heapTransformExpr heapVar))
  | .ReferenceEquals l r =>
      pure <| .ReferenceEquals (← heapTransformExpr heapVar l) (← heapTransformExpr heapVar r)
  | .AsType t ty => pure <| .AsType (← heapTransformExpr heapVar t) ty
  | .IsType t ty => pure <| .IsType (← heapTransformExpr heapVar t) ty
  | .Forall n ty b => pure <| .Forall n ty (← heapTransformExpr heapVar b)
  | .Exists n ty b => pure <| .Exists n ty (← heapTransformExpr heapVar b)
  | .Assigned n => pure <| .Assigned (← heapTransformExpr heapVar n)
  | .Old v => pure <| .Old (← heapTransformExpr heapVar v)
  | .Fresh v => pure <| .Fresh (← heapTransformExpr heapVar v)
  | .Assert c => pure <| .Assert (← heapTransformExpr heapVar c)
  | .Assume c => pure <| .Assume (← heapTransformExpr heapVar c)
  | .ProveBy v p => pure <| .ProveBy (← heapTransformExpr heapVar v) (← heapTransformExpr heapVar p)
  | .ContractOf ty f => pure <| .ContractOf ty (← heapTransformExpr heapVar f)
  | other => pure other
  pure ⟨val', md⟩

def heapTransformProcedure (proc : Procedure) : TransformM Procedure := do
  let heapName := "$heap"
  let readsHeap := (← get).heapReaders.contains proc.name
  let writesHeap := (← get).heapWriters.contains proc.name

  if readsHeap || writesHeap then
    let preconditions' ← proc.preconditions.mapM (heapTransformExpr heapName)
    let body' ← match proc.body with
      | .Transparent bodyExpr =>
          pure (.Transparent (← heapTransformExpr heapName bodyExpr))
      | .Opaque postconds impl det modif =>
          let postconds' ← postconds.mapM (heapTransformExpr heapName)
          let impl' ← impl.mapM (heapTransformExpr heapName)
          let modif' ← modif.mapM (heapTransformExpr heapName)
          pure (.Opaque postconds' impl' det modif')
      | .Abstract postconds =>
          pure (.Abstract (← postconds.mapM (heapTransformExpr heapName)))
    return { proc with preconditions := preconditions', body := body' }
  else
    let preconditions' ← proc.preconditions.mapM (heapTransformExpr heapName)
    let body' ← match proc.body with
      | .Transparent bodyExpr => pure (.Transparent bodyExpr)
      | .Opaque postconds impl det modif =>
          let postconds' ← postconds.mapM (heapTransformExpr heapName)
          pure (.Opaque postconds' impl det modif)
      | .Abstract postconds =>
          pure (.Abstract (← postconds.mapM (heapTransformExpr heapName)))
    return { proc with preconditions := preconditions', body := body' }

def heapParameterization (program : Program) : Program × List Identifier :=
  let heapReaders := computeReadsHeap program.staticProcedures
  let heapWriters := computeWritesHeap program.staticProcedures
  let (procs', finalState) := (program.staticProcedures.mapM heapTransformProcedure).run { heapReaders, heapWriters }
  ({ program with staticProcedures := procs', constants := program.constants ++ finalState.fieldConstants }, heapWriters)

end Strata.Laurel
