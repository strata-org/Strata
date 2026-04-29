/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
public import Strata.Util.Statistics

/-!
# Deterministic Hole Elimination

Replace each deterministic typed `.Hole` with a call to a freshly generated
uninterpreted function whose parameters mirror the enclosing callable's inputs.

This pass assumes `inferHoleTypes` has already annotated every `Hole` with a
type. It works uniformly for both procedures and functions.

After this pass the program contains only non-deterministic `Hole` nodes.
-/

namespace Strata
namespace Laurel

public section

private def emptyMd : Imperative.MetaData Core.Expression := #[]
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, none, emptyMd⟩

structure ElimHoleState where
  counter : Nat := 0
  currentInputs : List Parameter := []
  generatedFunctions : List Procedure := []

private abbrev ElimHoleM := StateM ElimHoleState

/-- Generate a fresh uninterpreted function for a typed hole and return a call to it. -/
private def mkHoleCall (holeType : HighTypeMd) : ElimHoleM StmtExprMd := do
  let s ← get
  let n := s.counter
  modify fun s => { s with counter := n + 1 }
  let holeName : Identifier := s!"$hole_{n}"
  let inputs := s.currentInputs
  let holeProc : Procedure := {
    name := holeName
    inputs := inputs
    outputs := [{ name := "$result", type := holeType }]
    preconditions := []
    decreases := none
    isFunctional := true
    body := .Opaque [] none []
  }
  modify fun s => { s with generatedFunctions := s.generatedFunctions ++ [holeProc] }
  return bare (.StaticCall holeName (inputs.map (fun p => bare (.Identifier p.name))))

/-- Replace a deterministic `.Hole` with a call to a fresh uninterpreted function.
    Non-hole nodes pass through unchanged; recursion is handled by `mapStmtExprM`. -/
private def elimHoleNode (expr : StmtExprMd) : ElimHoleM StmtExprMd := do
  match expr.val with
  | .Hole true (some ty) => mkHoleCall ty
  | .Hole true none => mkHoleCall ⟨.Unknown, expr.source, expr.md⟩
  | .Hole false _ => return expr -- Non-deterministic holes are preserved
  | _ => return expr

private def elimProcedure (proc : Procedure) : ElimHoleM Procedure := do
  modify fun s => { s with currentInputs := proc.inputs }
  mapProcedureBodiesM (mapStmtExprM elimHoleNode) proc

inductive ElimHoleStats where
  /-- Number of deterministic holes replaced with calls to uninterpreted functions. -/
  | holesEliminated

#derive_prefixed_toString ElimHoleStats "EliminateHoles"

/--
Replace every deterministic `.Hole` in the program with a call to a freshly
generated uninterpreted function. Works uniformly for both procedures and
functions.
After this pass the program contains only non-deterministic `Hole` nodes.

Assumes `inferHoleTypes` has already annotated holes with types.
-/
def eliminateHoles (program : Program) : Program × Statistics :=
  let initState : ElimHoleState := {}
  let (procs, finalState) := (program.staticProcedures.mapM elimProcedure).run initState
  let stats := ({} : Statistics)
    |>.increment s!"{ElimHoleStats.holesEliminated}" finalState.counter
  ({ program with staticProcedures := finalState.generatedFunctions ++ procs }, stats)

end -- public section
end Laurel
