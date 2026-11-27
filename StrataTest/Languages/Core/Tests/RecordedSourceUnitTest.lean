/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Core.Tests.CounterexampleTestUtils
meta import Strata.Languages.Core.PipelinePhase

/-! # The unit a recorded linked carrier lifts at (`RuntimeBackLink.withPrograms`)

`runTransformsWithBackLinks` records each phase's carrier through `withPrograms`: a
non-empty unit the phase's `buildBackLink` supplies is kept, and an empty supplied unit
is replaced by the unit `Program.sourceUnitFor` picks in the phase's input and output
programs.  Two identity phases on a program with a two-statement procedure `P`: one
supplies a one-statement unit, the other the default empty unit.  At the obligation
`tgt` of `P`, the first recorded carrier lifts at the supplied unit (length 1) and the
second at `P`'s unit (length 2). -/

meta section

namespace RecordedSourceUnitTest

open Core Lambda Imperative
open Core.CexTestUtils

private def id (name : String) : CoreIdent := ⟨name, ()⟩

private def setY : Statement :=
  .cmd (.cmd (.set (id "y") (.det (int 1)) md))
private def assertTgt : Statement :=
  .cmd (.cmd (.assert "tgt" (.eq default (v "y") (int 1)) md))

/-- `P() { y := 1; assert tgt (y == 1); }`. -/
private def procP : Procedure := {
  header := { name := id "P", typeArgs := [], inputs := [], outputs := [] }
  spec := { preconditions := [], postconditions := [] }
  body := .structured [setY, assertTgt] false }

private def prog : Program := { decls := [.proc procP md] }

/-- An identity phase whose linked carrier supplies the unit `su`. -/
private def customPhase (su : Target → Option String → List Statement) : PipelinePhase where
  transform := fun p => pure (false, p)
  phase.name := "custom"
  buildBackLink := fun _ _ => .linked (fun _ _ _ => { name := "custom", lift := fun _ o => o }) su

/-- The length of the unit each recorded carrier lifts at, for target `tgt` and procedure
    `P`. -/
private def recordedUnitLengths (phases : List PipelinePhase) : IO (List Nat) := do
  let (_, _, links) ← (runTransformsWithBackLinks prog phases).toIO
    fun _ => IO.userError "pipeline failed"
  pure <| links.map fun
    | .linked _ su _ => (su (.assert { label := "tgt", md := md }) (some "P")).length
    | .unavailable _ => 0

/-- info: [1, 2] -/
#guard_msgs in
#eval recordedUnitLengths [customPhase (fun _ _ => [setY]), customPhase (fun _ _ => [])]

end RecordedSourceUnitTest

end -- meta section
