/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

@[inline] public def BitVec.width {n : Nat} (_ : BitVec n) : Nat := n

def BitVec.signedMin (n : Nat) : Int := - 2 ^ (n-1)

def BitVec.signedMax (n : Nat) : Int := 2 ^ (n-1) - 1

public def BitVec.overflows (n : Nat) (i : Int) : Bool :=
  i < (BitVec.signedMin n) ||
  i > (BitVec.signedMax n)
