/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Plausible.Sampleable
import Plausible.DeriveArbitrary
import Plausible.Attr

/-! ## Helpers for using Plausible with Chamelean generated instances.

This entire file may be removed, if a dependency is added on https://github.com/codyroux/plausible (or that fork is merged with upstream)

-/

namespace TestGen

open Plausible

class ArbitrarySizedSuchThat (α : Type) (P : α → Prop) where
  arbitrarySizedST : Nat → Gen α

/-- The `DecOpt` class encodes partial decidability:
     - It takes a `nat` argument as fuel
     - It fails, if it can't decide (e.g. because it runs out of fuel)
     - It returns `ok true/false` if it can.
     - These are intended to be monotonic, in the
       sense that if they ever return `ok b` for
       some fuel, they will also do so for higher
       fuel values.
-/
class DecOpt (P : Prop) where
  decOpt : Nat → Except GenError Bool

/-- All `Prop`s that have a `Decidable` instance (this includes `DecidableEq`)
    can be automatically given a `DecOpt` instance -/
instance [Decidable P] : DecOpt P where
  decOpt := fun _ => .ok (decide P)

namespace DecOpt

/-- `checkerBacktrack` takes a list of (thunked) sub-checkers  and returns:
    - `ok true` if *any* sub-checker does so
    - `ok false` if *all* sub-checkers do so
    - `error` otherwise
    (see section 2 of "Computing Correctly with Inductive Relations") -/
def checkerBacktrack (checkers : List (Unit → Except GenError Bool)) : Except GenError Bool :=
  let rec aux (l : List (Unit → Except GenError Bool)) (b : Bool) : Except GenError Bool :=
    let err := .genError "DecOpt.checkerBacktrack failure."
    match l with
    | c :: cs =>
      match c () with
      | .ok true => .ok true
      | .ok false => aux cs b
      | .error _ => aux cs true
    | [] => if b then throw err else .ok false
  aux checkers false

/-- Conjunction lifted to work over `Option Bool`
    (corresponds to the `.&&` infix operator in section 2 of "Computing Correctly with Inductive Relations") -/
def andOpt (a : Except GenError Bool) (b : Except GenError Bool) : Except GenError Bool :=
  match a with
  | .ok true => b
  | _ => a

/-- Folds an optional conjunction operation `andOpt` over a list of `Except _ Bool`s,
    returning the resultant `Except _ Bool` -/
def andOptList (bs : List (Except GenError Bool)) : Except GenError Bool :=
  List.foldl andOpt (.ok true) bs

end DecOpt


namespace GeneratorCombinators

/-- `pick default xs n` chooses a weight & a generator `(k, gen)` from the list `xs` such that `n < k`.
    If `xs` is empty, the `default` generator with weight 0 is returned. -/
def pick (default : Gen α) (xs : List (Nat × Gen α)) (n : Nat) : Nat × Gen α :=
  match xs with
  | [] => (0, default)
  | (k, x) :: xs =>
    if n < k then
      (k, x)
    else
      pick default xs (n - k)


/-- `pickDrop xs n` returns a weight & its generator `(k, gen)` from the list `xs`
     such that `n < k`, and also returns the other elements of the list after `(k, gen)` -/
def pickDrop (xs : List (Nat × Gen α)) (n : Nat) : Nat × Gen α × List (Nat × Gen α) :=
  let fail : GenError := .genError "Plausible.Chamelean.GeneratorCombinators: failure."
  match xs with
  | [] => (0, throw fail, [])
  | (k, x) :: xs =>
    if n < k then
      (k, x, xs)
    else
      let (k', x', xs') := pickDrop xs (n - k)
      (k', x', (k, x)::xs')

/-- Sums all the weights in an association list containing `Nat`s and `α`s -/
def sumFst (gs : List (Nat × α)) : Nat := List.sum <| List.map Prod.fst gs

/-- Picks one of the generators in `gs` at random, returning the `default` generator
    if `gs` is empty.

    (This is a more ergonomic version of Plausible's `Gen.oneOf` which doesn't
    require the caller to supply a proof that the list index is in bounds.) -/
def oneOfWithDefault (default : Gen α) (gs : List (Gen α)) : Gen α :=
  match gs with
  | [] => default
  | _ => do
    let idx ← Gen.choose Nat 0 (gs.length - 1) (by omega)
    List.getD gs idx.val default

/-- `frequency` picks a generator from the list `gs` according to the weights in `gs`.
    If `gs` is empty, the `default` generator is returned.  -/
def frequency (default : Gen α) (gs : List (Nat × Gen α)) : Gen α := do
  let total := sumFst gs
  let n ← Gen.choose Nat 0 (total - 1) (by omega)
  (pick default gs n).snd

/-- `sized f` constructs a generator that depends on its `size` parameter -/
def sized (f : Nat → Gen α) : Gen α :=
  Gen.getSize >>= f

/-- Helper function for `backtrack` which picks one out of `total` generators with some initial amount of `fuel` -/
def backtrackFuel (fuel : Nat) (total : Nat) (gs : List (Nat × Gen α)) : Gen α :=
  match fuel with
  | .zero => throw Gen.outOfFuel
  | .succ fuel' => do
    let n ← Gen.choose Nat 0 (total - 1) (by omega)
    let (k, g, gs') := pickDrop gs n
    -- Try to generate a value using `g`, if it fails, backtrack with `fuel'`
    -- and pick one out of the `total - k` remaining generators
    tryCatch g (fun _ => backtrackFuel fuel' (total - k) gs')

/-- Tries all generators until one returns a `Some` value or all the generators failed once with `None`.
   The generators are picked at random according to their weights (like `frequency` in Haskell QuickCheck),
   and each generator is run at most once. -/
def backtrack (gs : List (Nat × Gen α)) : Gen α :=
  backtrackFuel (gs.length) (sumFst gs) gs

/-- Delays the evaluation of a generator by taking in a function `f : Unit → Gen α` -/
def thunkGen (f : Unit → Gen α) : Gen α :=
  f ()

/-- `elementsWithDefault` constructs a generator from a list `xs` and a `default` element.
    If `xs` is non-empty, the generator picks an element from `xs` uniformly; otherwise it returns the `default` element.

    Remarks:
    - this is a version of Plausible's `Gen.elements` where the caller doesn't have
      to supply a proof that the list index is in bounds
    - This is a version of QuickChick's `elems_` combinator -/
def elementsWithDefault [Inhabited α] (default : α) (xs : List α) : Gen α :=
  match xs with
  | [] => return default
  | _ => do
    let i ← Subtype.val <$> Gen.choose Nat 0 (xs.length - 1) (by omega)
    return xs[i]!

end GeneratorCombinators
