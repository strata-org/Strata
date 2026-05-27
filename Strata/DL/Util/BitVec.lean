/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

@[expose, inline] public def BitVec.width {n : Nat} (_ : BitVec n) : Nat := n

@[expose] public def BitVec.signedMin (n : Nat) : Int := - 2 ^ (n-1)

@[expose] public def BitVec.signedMax (n : Nat) : Int := 2 ^ (n-1) - 1

@[expose] public def BitVec.overflows (n : Nat) (i : Int) : Bool :=
  i < (BitVec.signedMin n) ||
  i > (BitVec.signedMax n)

/-- Unsigned negation overflow: true iff x ≠ 0 (since -x wraps for all non-zero unsigned). -/
public def BitVec.unegOverflow {n : Nat} (x : BitVec n) : Bool :=
  x != 0
