/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Kernel-checkable duplicate check for string lists

`decide +kernel` on `List.Nodup` of `n` strings compares every pair of
strings, which is slow for a few hundred names. These functions let the kernel
instead map each string to a number built from its UTF-8 bytes, sort the
numbers, and compare neighbors: about `n log n` comparisons of numbers, which
the kernel does natively. The sort is structural (bounded by fuel) because the
kernel does not reduce `List.mergeSort`, which is defined by well-founded
recursion.

Key definitions: `byteCode`, `sortFuel`, `strictlyIncreasing`. -/

public section

namespace Strata.StringNodup

/-- A number built from the UTF-8 bytes of `s`, most significant first. -/
def byteCode (s : String) : Nat :=
  s.toByteArray.data.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Merges two lists in at most `fuel` steps. When the fuel runs out, the
    remaining elements are appended unsorted. -/
def mergeFuel : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys =>
    bif Nat.ble x y then x :: mergeFuel n xs (y :: ys)
    else y :: mergeFuel n (x :: xs) ys

/-- Splits a list into its elements at even and at odd positions. -/
def splitAlt : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: t => match splitAlt t with
    | (a, b) => (x :: b, a)

/-- Merge sort with recursion depth at most `fuel`. With too little fuel the
    result is a permutation of the input but may be unsorted. -/
def sortFuel : Nat → List Nat → List Nat
  | 0, l => l
  | n + 1, l => match splitAlt l with
    | ([], b) => b
    | (a, []) => a
    | (a, b) => mergeFuel l.length (sortFuel n a) (sortFuel n b)

/-- Whether each element of the list is smaller than the next. -/
def strictlyIncreasing : List Nat → Bool
  | a :: b :: t => Nat.blt a b && strictlyIncreasing (b :: t)
  | _ => true

end Strata.StringNodup

end -- public section
