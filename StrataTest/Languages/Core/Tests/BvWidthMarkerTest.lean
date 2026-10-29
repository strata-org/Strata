/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Core.DDMTransform.Translate

/-! Negative tests for the width-parameterized bitvector type `bv W`.

A bitvector type is written `bv W8`, where `W1 … W128` are width markers that are
only meaningful as the single argument to `bv`. `translateLMonoTy` rejects a width
marker used on its own and rejects `bv` applied to anything other than a marker.
An undeclared name under `bv` (e.g. `bv FOO`) is rejected earlier, by DDM name
resolution.
-/

open Strata Strata.Core

/-- Collect the translation errors for a program. -/
private def transErrors (p : StrataDDM.Program) : Array String :=
  (TransM.run Inhabited.default (translateProgram p)).snd

/-- A bare width marker in type position is rejected. -/
private def bareMarkerPgm : StrataDDM.Program :=
#strata
program Core;
const x : W8;
#end

/-- info: true -/
#guard_msgs in
#eval (transErrors bareMarkerPgm).any
  (·.startsWith "bitvector width marker used outside `bv`")

/-- A width marker as a type argument to another constructor is rejected. -/
private def mapMarkerPgm : StrataDDM.Program :=
#strata
program Core;
const m : Map W8 int;
#end

/-- info: true -/
#guard_msgs in
#eval (transErrors mapMarkerPgm).any
  (·.startsWith "bitvector width marker used outside `bv`")

/-- `bv` applied to a non-marker type is rejected. -/
private def bvNonMarkerPgm : StrataDDM.Program :=
#strata
program Core;
const x : bv int;
#end

/-- info: true -/
#guard_msgs in
#eval (transErrors bvNonMarkerPgm).any
  (·.startsWith "`bv` expects a width marker")

/-- A valid `bv W8` type translates without error. -/
private def validBvPgm : StrataDDM.Program :=
#strata
program Core;
const x : bv W8;
#end

/-- info: true -/
#guard_msgs in
#eval (transErrors validBvPgm).isEmpty
