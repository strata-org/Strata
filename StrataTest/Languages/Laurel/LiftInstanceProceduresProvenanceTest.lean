/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that `liftInstanceProcedures` preserves the source provenance of lifted
instance procedure names.
-/

meta import Strata.Languages.Laurel.LiftInstanceProcedures

meta section

open Strata Strata.Laurel

private def methodSource : FileRange :=
  ⟨.file "Counter.lr", SourceRange.none⟩

private def resetProc : Procedure :=
  { name := { text := "reset", source := some methodSource }
    inputs := [{ name := mkId "self",
                 type := { val := .UserDefined (mkId "Counter"), source := none } }]
    outputs := [], preconditions := [], decreases := none,
    isFunctional := false, body := .Opaque [] none [] }

private def counterComposite : CompositeType :=
  { name := mkId "Counter", extending := [],
    fields := [{ name := mkId "count", isMutable := true,
                 type := { val := .TInt, source := none } }],
    instanceProcedures := [resetProc] }

private def program : Program :=
  { staticProcedures := [], staticFields := [],
    types := [.Composite counterComposite], constants := [] }

private def liftedReset : Option Procedure :=
  (liftInstanceProcedures (resolve program).model program).staticProcedures.find?
    (·.name.text == "Counter$reset")

#guard resetProc.name.source == some methodSource
#guard liftedReset.isSome
#guard (liftedReset.bind (·.name.source)) == some methodSource
