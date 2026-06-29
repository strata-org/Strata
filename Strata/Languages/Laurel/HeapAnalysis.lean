/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Util.Tactics

/-!
# Heap-Effect Analysis

Determines, for each procedure, whether it reads and/or writes the heap. A
procedure reads the heap when it accesses a composite field (`x#f`) and writes
the heap when it assigns a field, creates an object (`new`), or has an opaque
body with a non-empty modifies clause. The analysis is transitive over static
calls: if `A` calls `B` and `B` reads/writes the heap, then so does `A`.

This is the single source of truth for heap-effect classification. It lives in
its own module (importing only the AST and the generic `MapStmtExpr` traversal)
so that both `HeapParameterization` (which uses it to inject `$heap` parameters)
and `Resolution` (which uses it to diagnose no-op `old(...)` usage) can share it
without an import cycle.
-/

public section

namespace Strata.Laurel

/-- Direct heap effects of a single expression/procedure, plus the static
    callees needed to propagate effects transitively. -/
structure AnalysisResult where
  readsHeapDirectly : Bool := false
  writesHeapDirectly : Bool := false
  callees : List Identifier := []

/-- Collect the direct heap effects of an expression (and the static callees
    needed to propagate them transitively). Recursion into child nodes is handled
    by `foldStmtExprM`; the visitor only flags the constructors that directly
    read (`x#f`), write (field assignment, `new`), or call. -/
def collectExprMd (expr : StmtExprMd) : StateM AnalysisResult Unit :=
  foldStmtExprM (fun e => do
    match e.val with
    | .Var (.Field _ _) => modify fun s => { s with readsHeapDirectly := true }
    | .StaticCall callee _ => modify fun s => { s with callees := callee :: s.callees }
    | .New _ => modify fun s => { s with writesHeapDirectly := true }
    | .Assign assignTargets _ =>
        for ⟨assignTarget, _⟩ in assignTargets.attach do
          match assignTarget.val with
          | .Field _ _fieldName => modify fun s => { s with writesHeapDirectly := true }
          | .Local _ | .Declare _ => pure ()
    | _ => pure ()) expr

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

end Strata.Laurel

end -- public section
