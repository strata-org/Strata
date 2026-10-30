/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Ropes

A rope is a list represented by a tree of concatenations, so that concatenation takes constant
time (`Rope.app`); its elements are read off in order by one traversal with an explicit work
list (`Rope.toList`), with no recursion on the depth of the tree. The elements of the empty,
one-element and concatenated ropes are in `Strata.Util.RopeProps`.

Key definitions: `Rope`, `Rope.app`, `Rope.ofList`, `Rope.toList`. -/

namespace Strata.Util

public section

/-- A rope: concatenation in O(1). -/
inductive Rope (α : Type) where
  | nil
  | one (a : α)
  | cat (a b : Rope α)
  deriving Inhabited

/-- Concatenation, dropping empty operands. -/
@[expose] def Rope.app {α : Type} : Rope α → Rope α → Rope α
  | .nil, b => b
  | a, .nil => a
  | a, b => .cat a b

/-- Is the rope built only from `nil`? (`Rope.app` keeps every nonempty rope free of `nil`.) -/
@[expose] def Rope.isNil {α : Type} : Rope α → Bool
  | .nil => true
  | _ => false

/-- The rope of a list. -/
@[expose] def Rope.ofList {α : Type} : List α → Rope α
  | [] => .nil
  | a :: as => Rope.app (.one a) (Rope.ofList as)

/-- The number of constructors of a rope. -/
@[expose] def Rope.size {α : Type} : Rope α → Nat
  | .nil | .one _ => 1
  | .cat a b => Rope.size a + Rope.size b + 1

/-- The total number of constructors of the ropes of a work list. -/
@[expose] def Rope.workSize {α : Type} : List (Rope α) → Nat
  | [] => 0
  | s :: st => Rope.size s + Rope.workSize st

/-- The elements of the ropes of a work list (the first rope rightmost), prepended to `acc`;
    an explicit work list, no recursion on the depth of the rope. -/
@[expose] def Rope.toListAux {α : Type} : List (Rope α) → List α → List α
  | [], acc => acc
  | .nil :: st, acc => Rope.toListAux st acc
  | .one a :: st, acc => Rope.toListAux st (a :: acc)
  | .cat a b :: st, acc => Rope.toListAux (b :: a :: st) acc
  termination_by st => Rope.workSize st
  decreasing_by
    all_goals simp only [Rope.workSize, Rope.size]
    all_goals omega

/-- The elements of a rope, in order. -/
@[expose] def Rope.toList {α : Type} (s : Rope α) : List α := Rope.toListAux [s] []

end -- public section

end Strata.Util
