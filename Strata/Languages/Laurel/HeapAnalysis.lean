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
body with a non-empty modifies clause. The analysis is transitive over calls
(both static and instance calls): if `A` calls `B` and `B` reads/writes the
heap, then so does `A`.

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

/-- Collect the direct heap effects of an expression (and the callees needed to
    propagate them transitively). Recursion into child nodes is handled by
    `foldStmtExprM`; the visitor only flags the constructors that directly read
    (`x#f`), write (field assignment, `new`), or call.

    Both `StaticCall` and `InstanceCall` callees are recorded: this analysis runs
    at initial resolution, *before* `LiftInstanceProcedures` rewrites
    `obj#method(...)` (an `InstanceCall`) into a static call. Dropping
    `InstanceCall` callees would misclassify a procedure whose only heap effect is
    through an instance call as non-heap-writing. Callee identifiers compare by
    name, and the lifted procedure keeps the same method name, so the pre-lift
    callee still matches the procedure in the call graph. -/
def collectExprMd (expr : StmtExprMd) : StateM AnalysisResult Unit :=
  foldStmtExprM (fun e => do
    match e.val with
    | .Var (.Field _ _) => modify fun s => { s with readsHeapDirectly := true }
    | .StaticCall callee _ => modify fun s => { s with callees := callee :: s.callees }
    | .InstanceCall _ callee _ => modify fun s => { s with callees := callee :: s.callees }
    | .New _ => modify fun s => { s with writesHeapDirectly := true }
    | .Assign assignTargets _ =>
        for ⟨assignTarget, _⟩ in assignTargets.attach do
          match assignTarget.val with
          | .Field _ _fieldName => modify fun s => { s with writesHeapDirectly := true }
          | .Local _ | .Declare _ => pure ()
    -- `c#f++` / `c#f--` mutate a field just like `.Assign` with a `.Field`
    -- target. This analysis runs at initial resolution, before
    -- `EliminateIncrDecrAndCompoundAssign` lowers `IncrDecr` to `.Assign .Field`, so the
    -- `IncrDecr` form must be recognized here too.
    | .IncrDecr _ _ target =>
        match target.val with
        | .Field _ _fieldName => modify fun s => { s with writesHeapDirectly := true }
        | .Local _ | .Declare _ => pure ()
    -- `c#f += e` mutates a field just like `c#f++`; recognized here for the same
    -- reason (analysis runs before `EliminateIncrDecrAndCompoundAssign` lowers it).
    | .CompoundAssign _ target _ =>
        match target.val with
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

/-- Per-procedure input to `transitiveEffectClosure`: the procedure `name`,
    whether it has the effect `directly`, and its static `callees`. -/
structure ProcEffectInfo (α : Type) where
  name : α
  directly : Bool
  callees : List α

/-- Transitive call-graph closure of a direct effect, shared by the reads-heap
    and writes-heap analyses. Given, per procedure, its `name`, whether it has
    the effect `directly`, and its static `callees`, returns the set of
    procedures that have the effect directly or transitively: a procedure is in
    the set if it has the effect directly, or it calls a procedure that is in
    the set. Iterated to a fixpoint (bounded by the number of procedures, which
    is a safe upper bound on the longest propagation chain).

    Generic over the name type `α` (needs `BEq`/`Hashable` for the `HashSet`),
    so the two heap-effect analyses share one engine instead of duplicating the
    fixpoint. -/
def transitiveEffectClosure {α : Type} [BEq α] [Hashable α]
    (info : List (ProcEffectInfo α)) : Std.HashSet α :=
  let direct := info.filterMap fun i => if i.directly then some i.name else none
  let rec fixpoint (fuel : Nat) (current : Std.HashSet α) : Std.HashSet α :=
    match fuel with
    | 0 => current
    | fuel' + 1 =>
      let next := info.foldl (fun acc i =>
        if current.contains i.name || i.callees.any current.contains then acc.insert i.name else acc)
        current
      if next.size == current.size then current else fixpoint fuel' next
  fixpoint info.length (Std.HashSet.ofList direct)

def computeReadsHeap (procs : List Procedure) : Except String (Std.HashSet Nat) := do
  let info ← procs.mapM fun p => do
    let name ← Identifier.getUniqueId p.name
    let r := analyzeProc p
    -- Callees are reference-position: unresolved ones (uniqueId = none) come
    -- from failed name resolution (already reported as a diagnostic). They
    -- can't match any procedure in the set, so filtering them is sound.
    let callees := r.callees.filterMap (·.uniqueId)
    pure { name, directly := r.readsHeapDirectly, callees : ProcEffectInfo Nat }
  pure (transitiveEffectClosure info)

def computeWritesHeap (procs : List Procedure) : Except String (Std.HashSet Nat) := do
  let info ← procs.mapM fun p => do
    let name ← Identifier.getUniqueId p.name
    let r := analyzeProc p
    -- Callees are reference-position: unresolved ones (uniqueId = none) come
    -- from failed name resolution (already reported as a diagnostic). They
    -- can't match any procedure in the set, so filtering them is sound.
    let callees := r.callees.filterMap (·.uniqueId)
    pure { name, directly := r.writesHeapDirectly, callees : ProcEffectInfo Nat }
  pure (transitiveEffectClosure info)

end Strata.Laurel

end -- public section
