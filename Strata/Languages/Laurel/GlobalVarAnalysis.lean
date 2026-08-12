/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.SemanticModel
import Strata.Languages.Laurel.HeapAnalysis
import Strata.Languages.Laurel.MapStmtExpr

/-!
# Global-Variable Effect Analysis

Computes the procedures that transitively read or write each file-scope global.
Bare global references are syntactically local, so classification uses the
`SemanticModel`: only references resolved to `$static` fields count. This keeps
local shadowing correct. Call effects use `transitiveEffectClosure`.
-/

public section

namespace Strata.Laurel


/-- Direct global effects and callees for one procedure. Global identities are
    resolution-assigned IDs; `Identifier` deliberately has no hash equality. -/
private structure GlobalAnalysisResult where
  readsGlobalsDirectly  : Std.HashSet Nat := {}
  writesGlobalsDirectly : Std.HashSet Nat := {}
  callees               : List Identifier := []

private def globalOfLocalRef (model : SemanticModel) (globals : Std.HashSet Nat)
    (name : Identifier) : Option Nat :=
  match model.get? name with
  | some (.field owner field) =>
      if owner.text != "$static" then none
      else field.name.uniqueId.bind fun id => if globals.contains id then some id else none
  | _ => none

private abbrev GlobalAnalysisM := StateM GlobalAnalysisResult

private def recordGlobalRead (global : Nat) : GlobalAnalysisM Unit :=
  modify fun result =>
    { result with readsGlobalsDirectly := result.readsGlobalsDirectly.insert global }

private def recordGlobalWrite (global : Nat) : GlobalAnalysisM Unit :=
  modify fun result =>
    { result with writesGlobalsDirectly := result.writesGlobalsDirectly.insert global }

private def recordGlobalReadWrite (global : Nat) : GlobalAnalysisM Unit := do
  recordGlobalRead global
  recordGlobalWrite global

private def recordGlobalRef (model : SemanticModel) (globals : Std.HashSet Nat)
    (name : Identifier) (record : Nat → GlobalAnalysisM Unit) : GlobalAnalysisM Unit :=
  match globalOfLocalRef model globals name with
  | some global => record global
  | none => pure ()

private def recordGlobalTarget (model : SemanticModel) (globals : Std.HashSet Nat)
    (target : VariableMd) (record : Nat → GlobalAnalysisM Unit) : GlobalAnalysisM Unit :=
  match target.val with
  | .Local name => recordGlobalRef model globals name record
  | .Field _ _ | .Declare _ => pure ()

private def recordCallee (callee : Identifier) : GlobalAnalysisM Unit :=
  modify fun result => { result with callees := callee :: result.callees }

/-- Collect direct effects from one expression node. -/
private def collectGlobalNode (model : SemanticModel) (globals : Std.HashSet Nat)
    (expr : StmtExprMd) : GlobalAnalysisM Unit :=
  match expr.val with
  | .Var (.Local name) => recordGlobalRef model globals name recordGlobalRead
  | .StaticCall callee _ | .InstanceCall _ callee _ => recordCallee callee
  | .Assign targets _ =>
      targets.forM fun target => recordGlobalTarget model globals target recordGlobalWrite
  | .IncrDecr _ _ target | .CompoundAssign _ target _ =>
      recordGlobalTarget model globals target recordGlobalReadWrite
  | _ => pure ()

/-- Collect direct effects. Assignment targets count only as writes; the shared
    traversal still visits expressions used as field-target bases. -/
private def collectGlobalExprMd (model : SemanticModel) (globals : Std.HashSet Nat)
    (expr : StmtExprMd) : GlobalAnalysisM Unit :=
  foldStmtExprM (collectGlobalNode model globals) expr

/-- Collect effects from every expression-bearing part of a procedure. -/
private def analyzeProcGlobals (model : SemanticModel) (globals : Std.HashSet Nat)
    (proc : Procedure) : GlobalAnalysisResult :=
  let collect (expr : StmtExprMd) : StateM GlobalAnalysisResult StmtExprMd := do
    collectGlobalExprMd model globals expr
    return expr
  (mapProcedureM collect proc |>.run {}).2

private def analyzeAllProcs (model : SemanticModel) (globals : Std.HashSet Nat)
    (procs : List Procedure) : List (Procedure × GlobalAnalysisResult) :=
  procs.map fun proc => (proc, analyzeProcGlobals model globals proc)

structure GlobalEffectsByProcId where
  readers : Std.HashMap Nat (Std.HashSet Nat)
  writers : Std.HashMap Nat (Std.HashSet Nat)

private def computeReadersOfByProcId
    (analyzed : List (Procedure × GlobalAnalysisResult))
    (globalId : Nat) : Std.HashSet Nat :=
  transitiveEffectClosure (analyzed.filterMap fun (proc, result) =>
    proc.name.uniqueId.map fun id =>
      { name := id
        directly := result.readsGlobalsDirectly.contains globalId
        callees := result.callees.filterMap (·.uniqueId) })

private def computeWritersOfByProcId
    (analyzed : List (Procedure × GlobalAnalysisResult))
    (globalId : Nat) : Std.HashSet Nat :=
  transitiveEffectClosure (analyzed.filterMap fun (proc, result) =>
    proc.name.uniqueId.map fun id =>
      { name := id
        directly := result.writesGlobalsDirectly.contains globalId
        callees := result.callees.filterMap (·.uniqueId) })

/-- Definition-ID keyed effects for diagnostics that run before instance
    procedures are lifted to qualified static names. Globals that lack IDs are
    already associated with a resolution diagnostic and cannot match a resolved
    reference, so they are omitted. -/
def computeGlobalEffectsByProcId (model : SemanticModel) (procs : List Procedure)
    (globals : List Field) : GlobalEffectsByProcId :=
  let globalIds := globals.filterMap (·.name.uniqueId)
  let globalSet := Std.HashSet.ofList globalIds
  let analyzed := analyzeAllProcs model globalSet procs
  globalIds.foldl (init := { readers := {}, writers := {} }) fun effects globalId =>
    { readers := effects.readers.insert globalId
        (computeReadersOfByProcId analyzed globalId)
      writers := effects.writers.insert globalId
        (computeWritersOfByProcId analyzed globalId) }

end Strata.Laurel

end -- public section
