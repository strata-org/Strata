/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.LTyMatch

/-! ## Tests for one-way type matching -/

meta section
namespace Lambda
open Std (ToFormat Format format)
open LTy.Syntax
open Strata.Util (HMap)

/-- The bindings that matching `pats` against `tys` gives the type variables `params`, starting
    from the bindings `init` and sorted by name, or `no match`. -/
private def showMatch (params : List TyIdentifier) (pats tys : LMonoTys)
    (init : SubstOne := HMap.empty) : Format :=
  match LMonoTys.matchTys? params init pats tys with
  | some S => format (S.toList.mergeSort (fun x y => x.1 ≤ y.1))
  | none => "no match"

-- Each parameter binds to the type at its position.
/-- info: [(a, int), (b, bool)] -/
#guard_msgs in
#eval showMatch ["a", "b"] [mty[Map %a %b]] [mty[Map int bool]]

-- A parameter used twice binds once when both positions agree.
/-- info: [(a, int)] -/
#guard_msgs in
#eval showMatch ["a"] [mty[%a], mty[%a]] [mty[int], mty[int]]

-- A parameter that would need two types does not match.
/-- info: no match -/
#guard_msgs in
#eval showMatch ["a"] [mty[%a], mty[%a]] [mty[int], mty[bool]]

-- Different type constructors do not match.
/-- info: no match -/
#guard_msgs in
#eval showMatch ["a"] [mty[Map %a int]] [mty[int]]

-- A constant argument of the pattern must equal the type's.
/-- info: no match -/
#guard_msgs in
#eval showMatch ["a"] [mty[Map %a int]] [mty[Map bool bool]]

-- Bit-vector types of equal widths match.
/-- info: [(a, int)] -/
#guard_msgs in
#eval showMatch ["a"] [mty[%a], .bitvec 32] [mty[int], .bitvec 32]

-- Bit-vector types of different widths do not match.
/-- info: no match -/
#guard_msgs in
#eval showMatch ["a"] [mty[%a], .bitvec 32] [mty[int], .bitvec 64]

-- A type variable of the matched type is a constant, even with the parameter's name.
/-- info: [(a, a)] -/
#guard_msgs in
#eval showMatch ["a"] [mty[%a]] [mty[%a]]

-- A type variable of the pattern that is not a parameter is a constant.
/-- info: no match -/
#guard_msgs in
#eval showMatch ["a"] [mty[%b]] [mty[int]]

-- Swapped parameters bind to each other's names.
/-- info: [(a, b), (b, a)] -/
#guard_msgs in
#eval showMatch ["a", "b"] [mty[%a], mty[%b]] [mty[%b], mty[%a]]

-- Empty lists match with no bindings.
/-- info: [] -/
#guard_msgs in
#eval showMatch ["a"] [] []

-- Lists of different lengths do not match.
/-- info: no match
no match -/
#guard_msgs in
#eval do
  IO.println (showMatch ["a"] [mty[%a]] [mty[int], mty[bool]])
  IO.println (showMatch ["a"] [mty[%a], mty[%a]] [mty[int]])

-- Parameters inside nested arrows bind to the types at their positions.
/-- info: [(a, int), (b, bool)] -/
#guard_msgs in
#eval showMatch ["a", "b"] [mty[(%a → %b) → %a]] [mty[(int → bool) → int]]

-- A parameter used at two types inside nested arrows does not match.
/-- info: no match -/
#guard_msgs in
#eval showMatch ["a", "b"] [mty[(%a → %b) → %a]] [mty[(int → bool) → bool]]

-- A binding already in the initial map is kept, and later bindings extend it.
/-- info: [(a, int), (b, bool)] -/
#guard_msgs in
#eval showMatch ["a", "b"] [mty[%a]] [mty[int]] (HMap.empty.insert "b" mty[bool])

-- A parameter already bound in the initial map must match the same type.
/-- info: no match -/
#guard_msgs in
#eval showMatch ["a"] [mty[%a]] [mty[int]] (HMap.empty.insert "a" mty[bool])

end Lambda
end
