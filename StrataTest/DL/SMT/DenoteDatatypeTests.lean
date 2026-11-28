/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.SMT.Denote
import all Strata.DL.SMT.DenoteDatatypes
import all Strata.DL.SMT.TermType
import all Strata.DL.SMT.Term
import all Strata.DL.SMT.Op
import all Strata.Languages.Core.SMTEncoder
import all Strata.Util.OrderedSet
import all Strata.Util.OrderedSetProps

/-! # Denotation of datatype operations

A query over a datatype has a denotation: its sorts denote the generic carrier
(`DT.Carrier`), constructors build well-sorted values, testers compare the
constructor, and selectors read fields back. These tests check what the
denotation says on such queries, and which queries and declarations it refuses.
-/

namespace Strata.SMT.DT.Test

open Strata.SMT Strata.SMT.DT

/-! ## The carrier -/

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
  ⟨.mk "Red" [], .mk rfl rfl .nil⟩

example : tester "Red" red := rfl
example : ¬ tester "Green" red := by simp [tester, red, DVal.ctor]

/-- Positive binary numbers and naturals over them, as Boole declares them. -/
private def posNat : Decls :=
  [ ("pos", [⟨"xH", []⟩, ⟨"xO", [("pos..xO_h", .constr "pos" [])]⟩,
             ⟨"xI", [("pos..xI_h", .constr "pos" [])]⟩]),
    ("nat", [⟨"N0", []⟩, ⟨"Npos", [("nat..p", .constr "pos" [])]⟩]) ]

private abbrev noPayload : Sorted Empty := ⟨fun p _ => p.elim⟩

private def xH : Carrier posNat noPayload "pos" := ⟨.mk "xH" [], .mk rfl rfl .nil⟩
private def xO (p : Carrier posNat noPayload "pos") : Carrier posNat noPayload "pos" :=
  ⟨.mk "xO" [.dt p.1], .mk rfl rfl (.dt rfl p.2 .nil)⟩
private def Npos (p : Carrier posNat noPayload "pos") : Carrier posNat noPayload "nat" :=
  ⟨.mk "Npos" [.dt p.1], .mk rfl rfl (.dt rfl p.2 .nil)⟩

example : tester "xO" (xO xH) := rfl
example : ¬ tester "xH" (xO xH) := by simp [tester, xO, DVal.ctor]
example : tester "Npos" (Npos (xO xH)) := rfl

/-- The selector of `xO` reads its argument back from a value `xO` built, and has no
field to read on a value another constructor built. -/
example : selField (ctorsOf posNat "pos" |>.getD []) (xO xH).1 "pos..xO_h"
    = some (.dt xH.1, .constr "pos" []) := rfl
example : selField (ctorsOf posNat "pos" |>.getD []) (xO xH).1 "pos..xI_h" = none := rfl

/-! ## The checks on declarations -/

/-- Every field sort of these datatypes can be held by the carrier. -/
example : dtFieldsDenotable sctx = true := by decide

/-- A selector's unspecified value is an uninterpreted function of the argument. -/
example : dtUnspecUFs colorBox =
    [{ id := "IntBox..v$unspec", args := [.constr "IntBox" []], out := .prim .int }] := rfl

/-- Each name is declared once. -/
example : dtNamesDistinct sctx = true := by decide
example : dtNamesDistinct { dts := posNat } = true := by decide

/-- A datatype declared twice, a constructor declared twice (in one datatype or in two),
and a selector declared twice are refused. -/
example : dtNamesDistinct { dts := [("T", [⟨"A", []⟩]), ("T", [⟨"B", []⟩])] } = false := by decide
example : dtNamesDistinct { dts := [("T", [⟨"A", []⟩, ⟨"A", []⟩])] } = false := by decide
example : dtNamesDistinct { dts := [("T", [⟨"A", []⟩]), ("U", [⟨"A", []⟩])] } = false := by decide
example : dtNamesDistinct { dts :=
    [("pos", [⟨"xH", []⟩, ⟨"xO", [("pos..p", .constr "pos" [])]⟩,
              ⟨"xI", [("pos..p", .constr "pos" [])]⟩])] } = false := by decide

/-- A datatype under the name of an uninterpreted sort, or of a sort alias, is refused. -/
example : dtNamesDistinct { uss := [⟨"T", 0⟩], dts := [("T", [⟨"A", []⟩])] } = false := by decide
example : dtNamesDistinct { iss := [("T", .prim .int)], dts := [("T", [⟨"A", []⟩])] } = false := by
  decide

/-- Inhabitation: a recursive datatype whose base constructor comes last has a value;
one with no base constructor has none, alone or through another datatype. -/
example : dtAllInhabited { dts := [("L", [⟨"Cons", [("L..tl", .constr "L" [])]⟩, ⟨"Nil", []⟩])] }
    = true := by decide
example : dtAllInhabited { dts := [("Inf", [⟨"C", [("Inf..x", .constr "Inf" [])]⟩])] }
    = false := by decide
example : dtAllInhabited { dts :=
    [("A", [⟨"MkA", [("A..b", .constr "B" [])]⟩]), ("B", [⟨"MkB", [("B..a", .constr "A" [])]⟩])] }
    = false := by decide

/-- Fields of real, uninterpreted, array or option sort cannot be held by the carrier. -/
example : dtFieldsDenotable { dts := [("R", [⟨"MkR", [("R..r", .prim .real)]⟩])] } = false := by
  decide
example : dtFieldsDenotable { uss := [⟨"U", 0⟩], dts := [("R", [⟨"MkR", [("R..u", .constr "U" [])]⟩])] }
    = false := by decide
example : dtFieldsDenotable { dts :=
    [("R", [⟨"MkR", [("R..a", .constr "Array" [.prim .int, .prim .int])]⟩])] } = false := by decide
example : dtFieldsDenotable { dts := [("R", [⟨"MkR", [("R..o", .option (.prim .int))]⟩])] }
    = false := by decide

/-- The checks together, and the name of a selector's unspecified value: a function of
the query under that name is refused. -/
example : dtDeclsOK sctx [] = true := by decide
example : dtDeclsOK sctx ["f", "IntBox..v"] = true := by decide
example : dtDeclsOK sctx ["f", "IntBox..v$unspec"] = false := by decide

/-- A sort alias in a field sort is replaced by the sort it stands for, as in the terms. -/
example : dtSubstituteIS [("MyInt", .prim .int)]
      [("W", [⟨"MkW", [("W..v", .constr "MyInt" [])]⟩])]
    = [("W", [⟨"MkW", [("W..v", .prim .int)]⟩])] := by rfl

/-! ## Terms over datatypes

The declarations are passed as the plain list the kernel can reduce. -/

private def ctorT (d c : String) (args : List Term) : Term :=
  .app (.datatype_op .constructor c) args (.constr d [])
private def testerT (c : String) (a : Term) : Term :=
  .app (.datatype_op .tester c) [a] (.prim .bool)
private def selT (sel : String) (a : Term) (ty : TermType) : Term :=
  .app (.datatype_op .selector sel) [a] ty
private def eqT (a b : Term) : Term := .app .eq [a, b] (.prim .bool)

private def redT : Term := ctorT "Color" "Red" []
private def box3 : Term := ctorT "IntBox" "Box" [.prim (.int 3)]

/-- The term denotations, with the selector functions declared and no other symbol. -/
private noncomputable def denoteColorBox (t : Term) : Option Prop :=
  (denoteBoolTermFromContext [] [] (dtUnspecUFs colorBox) [] t colorBox).map PLift.down

/-- A tester on a constructor without fields, and on one with a field. -/
example : ∃ P, denoteColorBox (testerT "Red" redT) = some P ∧ P := by
  refine ⟨_, rfl, ?_⟩; intro _ _ _; rfl
example : ∃ P, denoteColorBox (testerT "Box" box3) = some P ∧ P := by
  refine ⟨_, rfl, ?_⟩; intro _ _ _; rfl
example : ∃ P, denoteColorBox (testerT "Green" redT) = some P ∧ ¬ P := by
  refine ⟨_, rfl, ?_⟩
  intro h
  have := h (fun _ => 0) (fun _ => 0) (fun _ => 0)
  simp [tester, DVal.ctor] at this

/-- A selector on its own constructor reads the field back: `IntBox..v(Box(3)) = 3`
denotes `3 = 3`, whatever the selector's value on other constructors. -/
example : denoteColorBox (eqT (selT "IntBox..v" box3 (.prim .int)) (.prim (.int 3)))
    = some (∀ (_divByZero _modByZero : Int → Int)
        (_ : Carrier colorBox (dtSorted sctx ⟨[], ⟨rfl, nofun⟩⟩) "IntBox" → Int),
        (3 : Int) = 3) := by
  rfl

/-- `datatype T { A(x : int), B }`. -/
private def ab : Decls := [("T", [⟨"A", [("T..x", .prim .int)]⟩, ⟨"B", []⟩])]

private noncomputable def denoteAB (t : Term) : Option Prop :=
  (denoteBoolTermFromContext [] [] (dtUnspecUFs ab) [] t ab).map PLift.down

private def abCtx : SortContext := { dts := ab }

/-- The value `B`. -/
private def bVal : Carrier ab (dtSorted abCtx ⟨[], ⟨rfl, nofun⟩⟩) "T" :=
  ⟨.mk "B" [], .mk rfl rfl .nil⟩

/-- A selector on another constructor has an unspecified value: `T..x(B) = 0` says that
the function the denotation quantifies over is `0` at `B`. That holds of no query-given
function, so the denotation is false, as the query is invalid for a solver. -/
example : denoteAB (eqT (selT "T..x" (ctorT "T" "B" []) (.prim .int)) (.prim (.int 0)))
    = some (∀ (_divByZero _modByZero : Int → Int)
        (unspec : Carrier ab (dtSorted abCtx ⟨[], ⟨rfl, nofun⟩⟩) "T" → Int),
        unspec bVal = 0) := by
  rfl

example : ¬ ∀ (_divByZero _modByZero : Int → Int)
    (unspec : Carrier ab (dtSorted abCtx ⟨[], ⟨rfl, nofun⟩⟩) "T" → Int),
    unspec bVal = 0 :=
  fun h => absurd (h (fun _ => 0) (fun _ => 0) fun _ => 1) (by decide)

/-- Ill-formed applications have no denotation: a tester with a constructor of another
datatype, a constructor with too few or too many arguments or with an argument of another
sort, a constructor of an undeclared datatype, an unknown selector, and a selector at a
sort other than its field's. -/
example : (denoteColorBox (testerT "Box" redT)).isNone := by rfl
example : (denoteColorBox (testerT "Box" (ctorT "IntBox" "Box" []))).isNone := by rfl
example : (denoteColorBox (testerT "Box"
    (ctorT "IntBox" "Box" [.prim (.int 1), .prim (.int 2)]))).isNone := by rfl
example : (denoteColorBox (testerT "Box" (ctorT "IntBox" "Box" [.prim (.bool true)]))).isNone := by
  rfl
example : (denoteColorBox (testerT "C" (ctorT "Other" "C" []))).isNone := by rfl
example : (denoteColorBox
    (eqT (selT "IntBox..w" box3 (.prim .int)) (.prim (.int 3)))).isNone := by rfl
example : (denoteColorBox (selT "IntBox..v" box3 (.prim .bool))).isNone := by rfl

/-! ## Queries

`denoteQuery` runs the checks on the declarations before it denotes the term. The encoder
context holds its symbols in sets the kernel does not reduce, so the empty ones are
rewritten first. -/

macro "query_rfl" : tactic =>
  `(tactic| (simp (disch := decide) only [denoteQuery, Strata.Util.OrderedSet.toList_empty,
      Strata.Util.OrderedKeyedSet.toList_empty, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, List.reverse_nil, List.map_nil, List.append_nil]; rfl))

/-- The query `is-Red(Red)` over `Color` and `IntBox` has a denotation. -/
example : (denoteQuery {} [] (testerT "Red" redT) (some colorBox)).isSome := by query_rfl

/-- The same query is refused once a declaration fails a check: a datatype without a
value, a field the carrier cannot hold, or a name declared twice. -/
example : (denoteQuery {} [] (testerT "Red" redT)
    (some (colorBox ++ [("Inf", [⟨"C", [("Inf..x", .constr "Inf" [])]⟩])]))).isNone := by query_rfl
example : (denoteQuery {} [] (testerT "Red" redT)
    (some (colorBox ++ [("RBox", [⟨"B", [("RBox..r", .prim .real)]⟩])]))).isNone := by query_rfl
example : (denoteQuery {} [] (testerT "Red" redT)
    (some (colorBox ++ [("Color", [⟨"Blue", []⟩])]))).isNone := by query_rfl

end Strata.SMT.DT.Test
