/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

@[inline] def BitVec.width {n : Nat} (_ : BitVec n) : Nat := n

def BitVec.signedMin (n : Nat) : Int := - 2 ^ (n-1)

def BitVec.signedMax (n : Nat) : Int := 2 ^ (n-1) - 1

def BitVec.overflows (n : Nat) (i : Int) : Bool :=
  i < (BitVec.signedMin n) ||
  i > (BitVec.signedMax n)
