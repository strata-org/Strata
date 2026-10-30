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

/-! ## Queries over datatypes have a denotation

The declarations are passed as the plain list the kernel can reduce. -/

private def redT : Term := .app (.datatype_op .constructor "Red") [] (.constr "Color" [])
private def isRedT : Term := .app (.datatype_op .tester "Red") [redT] (.prim .bool)

/-- The term denotations, with the selector functions declared and no other symbol. -/
private noncomputable def denoteColorBox (t : Term) : Option Prop :=
  (denoteBoolTermFromContext [] [] (dtUnspecUFs colorBox) [] t colorBox).map PLift.down

example : (denoteColorBox isRedT).isSome := by rfl

-- A compound term such as `IntBox..v(Box(3)) = 3` does not reduce under `rfl` in the
-- elaborator (true of every binary application in `denoteTerm`, not only datatypes), so
-- the pieces the selector case relies on are checked on their own; the end-to-end check
-- comes with the VC-to-Lean translation of datatypes.
example : dtSameSort (.prim .int) (.prim .int) = true := by simp [dtSameSort]
example : dtSameSort (.constr "Color" []) (.constr "IntBox" []) = false := by simp [dtSameSort]
example : findSel [⟨"Box", [("IntBox..v", .prim .int)]⟩] "IntBox..v"
    = some (⟨"Box", [("IntBox..v", .prim .int)]⟩, 0, .prim .int) := by rfl
example : findSel [⟨"Box", [("IntBox..v", .prim .int)]⟩] "IntBox..w" = none := by rfl

/-- A tester with a constructor of another datatype has no denotation. -/
private def isBoxRed : Term := .app (.datatype_op .tester "Box") [redT] (.prim .bool)
example : (denoteColorBox isBoxRed).isNone := by rfl

/-- A datatype without a value, or with a field the carrier cannot hold, is refused. -/
example : (denoteQuery {} [] isRedT
    (some [("Inf", [⟨"C", [("Inf..x", .constr "Inf" [])]⟩])])).isNone := by rfl
example : (denoteQuery {} [] isRedT
    (some [("RBox", [⟨"B", [("RBox..r", .prim .real)]⟩])])).isNone := by rfl

end Strata.SMT.DT.Test
