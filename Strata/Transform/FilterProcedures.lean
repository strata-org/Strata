/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import Std.Data.HashMap.AdditionalOperations

/-! # Erase procedures satisfying specific criteria -/

public section

namespace Core
namespace FilterProcedures

open Transform

/-- Statistics keys tracked by the filter procedures transformation. -/
inductive Stats where
  | visitedProcedures
  | erasedProcedures

#derive_prefixed_toString Stats "FilterProcedures"

/--
Filter program to keep only target procedures, applying the specified transform
to them and pruning away all other procedures.
Caches the updated CallGraph (which is just dropping unreachable procedure
entries from the HashMap) to save computation.

When `respectNoFilter` is true (default), procedures with `noFilter := true`
are always retained. Set to false for post-transform passes where only
explicitly listed targets and their call-graph dependencies should survive.
-/
def run (prog : Program) (targetProcs : List String)
    (respectNoFilter : Bool := true) :
    CoreTransformM Program := do
  let cg := match (← get).cachedAnalyses.callGraph with
    | .some cg => cg
    | .none => prog.toProcedureCG
  let allNeededProcs := (targetProcs ++ cg.getAllCalleesClosure targetProcs).dedup
  let neededProcsSet := allNeededProcs.toArray.qsort (· < ·)
  let isNeededProc (procName : String) :=
    neededProcsSet.binSearch procName (· < ·) |>.isSome

  -- Create a program with target procedures + dependencies.
  let numProcsBefore := prog.decls.countP (fun | .proc _ _ => true | _ => false)
  let prunedDecls := prog.decls.filter (fun decl =>
    match decl with
    | .proc p _ => (respectNoFilter && p.header.noFilter) || isNeededProc (CoreIdent.toPretty p.header.name)
    | _ => true) -- Keep all non-procedure declarations
  let numProcsAfter := prunedDecls.countP (fun | .proc _ _ => true | _ => false)
  incrementStat s!"{Stats.visitedProcedures}" numProcsBefore
  incrementStat s!"{Stats.erasedProcedures}" (numProcsBefore - numProcsAfter)

  -- Update CallGraph so that filtered out procedures do not appear anymore
  let filter_cg (m : Std.HashMap String (Std.HashMap String Nat)) :=
    let m := m.filter (fun k _ => isNeededProc k)
    m.map (fun _ v => v.filter (fun k _ => isNeededProc k))
  let cg_new:CallGraph := {
    callees := filter_cg cg.callees
    callers := filter_cg cg.callers
  }

  modify (fun σ => { σ with
    cachedAnalyses := { σ.cachedAnalyses with callGraph := .some cg_new }})

  return { prog with decls := prunedDecls }

end FilterProcedures

/-- FilterProcedures pipeline phase: restricts the program to the target
    procedures and their transitive callees. Model-preserving because it
    only removes procedures without changing the semantics of the
    remaining ones. -/
def filterProceduresPipelinePhase (procs : List String)
    (respectNoFilter : Bool := true) : PipelinePhase :=
  modelPreservingPipelinePhase "FilterProcedures" fun prog => do
    let filtered ← FilterProcedures.run prog procs (respectNoFilter := respectNoFilter)
    return (true, filtered)

end Core

end -- public section
