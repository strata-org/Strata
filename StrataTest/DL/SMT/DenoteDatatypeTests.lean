/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.SMT.Denote
import all Strata.DL.SMT.DenoteDatatypes
import all Strata.Languages.Core.SMTEncoder

/-! # Denotation of datatype operations

A query over a datatype now has a denotation: its sorts denote the generic
carrier (`DT.Carrier`), constructors build well-sorted values, testers compare
the constructor, and selectors read fields back. These tests check that the
denotation exists for such queries, and what it says.
-/

namespace Strata.SMT.DT.Test

open Strata.SMT Strata.SMT.DT

/-- `datatype Color { Red, Green }` and `datatype IntBox { Box(v : int) }`. -/
private def colorBox : Decls :=
  [ ("Color", [⟨"Red", []⟩, ⟨"Green", []⟩]),
    ("IntBox", [⟨"Box", [("IntBox..v", .prim .int)]⟩]) ]

private def sctx : SortContext := { dts := colorBox }

/-- The sorts of the datatypes denote. -/
example : (denoteSort sctx (.constr "Color" [])).isSome := by decide
example : (denoteSort sctx (.constr "IntBox" [])).isSome := by decide

/-- The carrier of `Color` has `Red` as a value, and `Red` is not `Green`. -/
private def red : Carrier colorBox (dtSorted sctx ⟨[], ⟨rfl, nofun⟩⟩) "Color" :=
  ⟨.mk "Red" [], .mk (.head _) (.head _) .nil⟩

example : tester "Red" red := rfl
example : ¬ tester "Green" red := by simp [tester, red, DVal.ctor]

/-- Every field sort of these datatypes can be held by the carrier. -/
example : dtFieldsDenotable sctx = true := by decide

/-- A selector's unspecified value is an uninterpreted function of the argument. -/
example : dtUnspecUFs colorBox =
    [{ id := "IntBox..v$unspec", args := [.constr "IntBox" []], out := .prim .int }] := rfl

end Strata.SMT.DT.Test
