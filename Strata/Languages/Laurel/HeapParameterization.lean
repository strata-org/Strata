/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel

/-
Heap Parameterization Pass

Transforms transparent procedures that read fields (or call procedures that read the heap)
by adding an explicit `heap: Heap` parameter. Field reads are translated to calls to
`read(heap, <fieldConstant>)`.
-/

namespace Strata.Laurel

structure HeapParamState where
  readsHeap : Bool := false
  fieldConstants : List Constant := []
  proceduresReadingHeap : List Identifier := []

abbrev HeapParamM := StateM HeapParamState

def HeapParamM.markReadsHeap : HeapParamM Unit :=
  modify fun s => { s with readsHeap := true }

def HeapParamM.addFieldConstant (name : Identifier) : HeapParamM Unit :=
  modify fun s =>
    if s.fieldConstants.any (·.name == name) then s
    else { s with fieldConstants := { name := name, type := .TField } :: s.fieldConstants }

def HeapParamM.resetReadsHeap : HeapParamM Unit :=
  modify fun s => { s with readsHeap := false }

def HeapParamM.getReadsHeap : HeapParamM Bool := do
  return (← get).readsHeap

def HeapParamM.procedureReadsHeap (name : Identifier) : HeapParamM Bool := do
  return (← get).proceduresReadingHeap.contains name

def HeapParamM.markProcedureReadsHeap (name : Identifier) : HeapParamM Unit :=
  modify fun s => { s with proceduresReadingHeap := name :: s.proceduresReadingHeap }

mutual
partial def analyzeExpr (expr : StmtExpr) : HeapParamM Unit := do
  match expr with
  | .FieldSelect target _ =>
      HeapParamM.markReadsHeap
      analyzeExpr target
  | .StaticCall callee args =>
      if ← HeapParamM.procedureReadsHeap callee then HeapParamM.markReadsHeap
      for arg in args do analyzeExpr arg
  | .InstanceCall target _ args =>
      HeapParamM.markReadsHeap
      analyzeExpr target
      for arg in args do analyzeExpr arg
  | .IfThenElse cond thenB elseB =>
      analyzeExpr cond; analyzeExpr thenB
      if let some e := elseB then analyzeExpr e
  | .Block stmts _ => for s in stmts do analyzeExpr s
  | .LocalVariable _ _ init => if let some i := init then analyzeExpr i
  | .While cond inv dec body =>
      analyzeExpr cond; analyzeExpr body
      if let some i := inv then analyzeExpr i
      if let some d := dec then analyzeExpr d
  | .Return v => if let some val := v then analyzeExpr val
  | .Assign t v _ => analyzeExpr t; analyzeExpr v
  | .PureFieldUpdate t _ v => analyzeExpr t; analyzeExpr v
  | .PrimitiveOp _ args => for a in args do analyzeExpr a
  | .ReferenceEquals l r => analyzeExpr l; analyzeExpr r
  | .AsType t _ => analyzeExpr t
  | .IsType t _ => analyzeExpr t
  | .Forall _ _ b => analyzeExpr b
  | .Exists _ _ b => analyzeExpr b
  | .Assigned n => analyzeExpr n
  | .Old v => analyzeExpr v
  | .Fresh v => analyzeExpr v
  | .Assert c _ => analyzeExpr c
  | .Assume c _ => analyzeExpr c
  | .ProveBy v p => analyzeExpr v; analyzeExpr p
  | .ContractOf _ f => analyzeExpr f
  | _ => pure ()

partial def analyzeBody (body : Body) : HeapParamM Unit :=
  match body with
  | .Transparent b => analyzeExpr b
  | _ => pure ()
end

partial def transformExpr (heapIdent : Identifier) (expr : StmtExpr) : HeapParamM StmtExpr := do
  match expr with
  | .FieldSelect target fieldName =>
      HeapParamM.addFieldConstant fieldName
      let target' ← transformExpr heapIdent target
      return .StaticCall "read" [.Identifier heapIdent, target', .Identifier fieldName]
  | .StaticCall callee args =>
      let args' ← args.mapM (transformExpr heapIdent)
      if ← HeapParamM.procedureReadsHeap callee then
        return .StaticCall callee (.Identifier heapIdent :: args')
      else
        return .StaticCall callee args'
  | .InstanceCall target callee args =>
      let target' ← transformExpr heapIdent target
      let args' ← args.mapM (transformExpr heapIdent)
      return .InstanceCall target' callee (.Identifier heapIdent :: args')
  | .IfThenElse cond thenB elseB =>
      let cond' ← transformExpr heapIdent cond
      let thenB' ← transformExpr heapIdent thenB
      let elseB' ← elseB.mapM (transformExpr heapIdent)
      return .IfThenElse cond' thenB' elseB'
  | .Block stmts label =>
      let stmts' ← stmts.mapM (transformExpr heapIdent)
      return .Block stmts' label
  | .LocalVariable name ty init =>
      let init' ← init.mapM (transformExpr heapIdent)
      return .LocalVariable name ty init'
  | .While cond inv dec body =>
      let cond' ← transformExpr heapIdent cond
      let body' ← transformExpr heapIdent body
      let inv' ← inv.mapM (transformExpr heapIdent)
      let dec' ← dec.mapM (transformExpr heapIdent)
      return .While cond' inv' dec' body'
  | .Return v =>
      let v' ← v.mapM (transformExpr heapIdent)
      return .Return v'
  | .Assign t v md =>
      let t' ← transformExpr heapIdent t
      let v' ← transformExpr heapIdent v
      return .Assign t' v' md
  | .PureFieldUpdate t f v =>
      let t' ← transformExpr heapIdent t
      let v' ← transformExpr heapIdent v
      return .PureFieldUpdate t' f v'
  | .PrimitiveOp op args =>
      let args' ← args.mapM (transformExpr heapIdent)
      return .PrimitiveOp op args'
  | .ReferenceEquals l r =>
      let l' ← transformExpr heapIdent l
      let r' ← transformExpr heapIdent r
      return .ReferenceEquals l' r'
  | .AsType t ty =>
      let t' ← transformExpr heapIdent t
      return .AsType t' ty
  | .IsType t ty =>
      let t' ← transformExpr heapIdent t
      return .IsType t' ty
  | .Forall n ty b =>
      let b' ← transformExpr heapIdent b
      return .Forall n ty b'
  | .Exists n ty b =>
      let b' ← transformExpr heapIdent b
      return .Exists n ty b'
  | .Assigned n =>
      let n' ← transformExpr heapIdent n
      return .Assigned n'
  | .Old v =>
      let v' ← transformExpr heapIdent v
      return .Old v'
  | .Fresh v =>
      let v' ← transformExpr heapIdent v
      return .Fresh v'
  | .Assert c md =>
      let c' ← transformExpr heapIdent c
      return .Assert c' md
  | .Assume c md =>
      let c' ← transformExpr heapIdent c
      return .Assume c' md
  | .ProveBy v p =>
      let v' ← transformExpr heapIdent v
      let p' ← transformExpr heapIdent p
      return .ProveBy v' p'
  | .ContractOf ty f =>
      let f' ← transformExpr heapIdent f
      return .ContractOf ty f'
  | other => return other

def transformProcedure (proc : Procedure) : HeapParamM Procedure := do
  match proc.body with
  | .Transparent bodyExpr =>
      HeapParamM.resetReadsHeap
      analyzeExpr bodyExpr
      if ← HeapParamM.getReadsHeap then
        HeapParamM.markProcedureReadsHeap proc.name
        let heapParam : Parameter := { name := "heap", type := .THeap }
        let bodyExpr' ← transformExpr "heap" bodyExpr
        return { proc with
          inputs := heapParam :: proc.inputs
          body := .Transparent bodyExpr'
        }
      else
        return proc
  | _ => return proc

def heapParameterization (program : Program) : Program :=
  let (procs', finalState) := (program.staticProcedures.mapM transformProcedure).run {}
  { program with
    staticProcedures := procs'
    constants := program.constants ++ finalState.fieldConstants
  }

end Strata.Laurel
