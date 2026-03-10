/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.CoreTransform

/-! # Erase procedures satisfying specific criteria -/

namespace Core
namespace FilterProcedures

open Transform

/--
Filter program to keep only target procedures, applying the specified transform
to them and pruning away all other procedures.
Caches the updated CallGraph (which is just dropping unreachable procedure
entries from the HashMap) to save computation.
-/
def run (prog : Program) (targetProcs : List String) :
    CoreTransformM Program := do
  let cg := match (← get).cachedAnalyses.callGraph with
    | .some cg => cg
    | .none => prog.toProcedureCG
  let allNeededProcs := (targetProcs ++ cg.getAllCalleesClosure targetProcs).dedup
  let neededProcsSet := allNeededProcs.toArray.qsort (· < ·)
  let isNeededProc (procName : String) :=
    neededProcsSet.binSearch procName (· < ·) |>.isSome

  -- Create a program with target procedures + dependencies.
  let prunedDecls := prog.decls.filter (fun decl =>
    match decl with
    | .proc p _ => p.header.noFilter || isNeededProc (CoreIdent.toPretty p.header.name)
    | _ => true) -- Keep all non-procedure declarations

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
end Core
