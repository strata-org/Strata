/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.LTy

/-!
# IEEE 754 operations for the Cortex interpreter

Functions over binary32 and binary64 values for frontends whose source language has
`float` and `double`, such as Java bytecode. A value is its IEEE 754 bit pattern: a
binary64 value is a `bv64` and a binary32 value a `bv32`, so there is no floating-point
type or constant, and a frontend writes a constant as its bits.

For `W` in `32` and `64`:

* `FpW.Add`, `FpW.Sub`, `FpW.Mul`, `FpW.Div`: the IEEE operations, rounding to nearest
  with ties to even.
* `FpW.TruncRem`: the remainder of the division truncated toward zero, as C's `fmod`
  computes it, not IEEE's `remainder`, which rounds the quotient to nearest. It has the
  sign of the dividend and is exact.
* `FpW.Neg`: the value with its sign inverted, also for a zero and a NaN.
* `FpW.Lt`, `FpW.Le`, `FpW.Gt`, `FpW.Ge`, `FpW.Eq`: the IEEE comparisons, as Core's
  `Real.Lt` and `BvW.SLt` are comparisons. Each is false when either value is a NaN, and
  the two zeros are equal.
* `FpW.OfBv32`, `FpW.OfBv64`: the value nearest to a signed integer.
* `FpW.ToBv32Sat`, `FpW.ToBv64Sat`: the signed integer that the value rounds to toward
  zero, saturating: a NaN gives 0, and a value out of range gives the least or the
  greatest integer.

`Fp32.ToFp64` widens a binary32 value, which is exact, and `Fp64.ToFp32` rounds a
binary64 value to the nearest binary32 one. A conversion from an integer is named in the
`FpW` namespace, since `BvW.` names are Core's bitvector operators.

An operation that computes a NaN gives the quiet NaN with a positive sign and no payload.
`FpW.Neg` and `FpW.TruncRem` with an infinite divisor return their operand's bits instead.

The arithmetic is Lean's `Float` and `Float32`, which the compiler implements with the
host's binary64 and binary32 operations. The kernel cannot evaluate them, so a property
of these functions is tested by running them, not proved. `FpW.TruncRem` and `FpW.Neg` are
computed on the bits.

Only the Cortex interpreter and its type checker know these functions. Core's factory
does not have them, so the route to Core rejects a program that uses them.

The bit patterns are the representation for the interpreter, not for verification. A
route to Core or SMT should give `float` and `double` a floating-point type of their own:
over bits, every operation would need a side condition fixing the bits of its NaN result,
since a floating-point sort has one NaN and the bits have many. The type checker does not
tell the bits of a float from those of an integer either: `Bv32.Add` or `==` on them type
checks, so a frontend must keep the two apart itself.
-/

namespace Cortex.FloatFactory

open Lambda

private def toFloat (b : BitVec 64) : Float := Float.ofBits (UInt64.ofBitVec b)
/-- The bits of `x`, and of a NaN the quiet NaN with a positive sign and no payload, since the
host's operations may give a NaN other bits. -/
private def ofFloat (x : Float) : BitVec 64 :=
  if x.isNaN then 0x7FF8000000000000#64 else x.toBits.toBitVec
private def toFloat32 (b : BitVec 32) : Float32 := Float32.ofBits (UInt32.ofBitVec b)
/-- The bits of `x`, and of a NaN the quiet NaN with a positive sign and no payload. -/
private def ofFloat32 (x : Float32) : BitVec 32 :=
  if x.isNaN then 0x7FC00000#32 else x.toBits.toBitVec

private def lift64 (op : Float → Float → Float) (a b : BitVec 64) : BitVec 64 :=
  ofFloat (op (toFloat a) (toFloat b))

private def lift32 (op : Float32 → Float32 → Float32) (a b : BitVec 32) : BitVec 32 :=
  ofFloat32 (op (toFloat32 a) (toFloat32 b))

/-- The bits of `x rem y` for two values of the format with `expBits` exponent bits and
`manBits` mantissa bits. A finite value is a whole number of units of the least positive
value, so the remainder of the two whole numbers is the exact result, and it is less than
the divisor, so it is a value of the format. -/
private def remBits (expBits manBits : Nat) (x y : Nat) : Nat :=
  let maxExp := 2 ^ expBits - 1
  let hidden := 2 ^ manBits
  let exp := fun (v : Nat) => (v >>> manBits) % 2 ^ expBits
  let man := fun (v : Nat) => v % hidden
  let isNaN := fun (v : Nat) => exp v == maxExp && man v != 0
  let isInf := fun (v : Nat) => exp v == maxExp && man v == 0
  let units := fun (v : Nat) => if exp v == 0 then man v else (man v + hidden) <<< (exp v - 1)
  if isNaN x || isNaN y || isInf x || units y == 0 then (maxExp <<< manBits) + hidden / 2
  else if isInf y then x
  else
    let r := units x % units y
    let sign := (x >>> (expBits + manBits)) <<< (expBits + manBits)
    if r < hidden then sign + r
    else
      let e := r.log2 - manBits + 1
      sign + (e <<< manBits) + ((r >>> (e - 1)) - hidden)

private def rem64 (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (remBits 11 52 a.toNat b.toNat)
private def rem32 (a b : BitVec 32) : BitVec 32 := BitVec.ofNat 32 (remBits 8 23 a.toNat b.toNat)

private def neg64 (a : BitVec 64) : BitVec 64 := a ^^^ 0x8000000000000000#64
private def neg32 (a : BitVec 32) : BitVec 32 := a ^^^ 0x80000000#32

private def pred64 (p : Float → Float → Bool) (a b : BitVec 64) : Bool :=
  p (toFloat a) (toFloat b)

private def pred32 (p : Float32 → Float32 → Bool) (a b : BitVec 32) : Bool :=
  p (toFloat32 a) (toFloat32 b)

public section

abbrev Func := WFLFunc Core.CoreLParams

def add64 : Func := binaryOp (InValTy := BitVec 64) "Fp64.Add" (lift64 (· + ·))
def sub64 : Func := binaryOp (InValTy := BitVec 64) "Fp64.Sub" (lift64 (· - ·))
def mul64 : Func := binaryOp (InValTy := BitVec 64) "Fp64.Mul" (lift64 (· * ·))
def div64 : Func := binaryOp (InValTy := BitVec 64) "Fp64.Div" (lift64 (· / ·))
def truncRem64 : Func := binaryOp (InValTy := BitVec 64) "Fp64.TruncRem" rem64
def neg64Func : Func := unaryOp (InValTy := BitVec 64) "Fp64.Neg" neg64
def lt64 : Func := binaryOp (InValTy := BitVec 64) (OutValTy := Bool) "Fp64.Lt" (pred64 (decide <| · < ·))
def le64 : Func := binaryOp (InValTy := BitVec 64) (OutValTy := Bool) "Fp64.Le" (pred64 (decide <| · ≤ ·))
def gt64 : Func := binaryOp (InValTy := BitVec 64) (OutValTy := Bool) "Fp64.Gt" (pred64 (decide <| · > ·))
def ge64 : Func := binaryOp (InValTy := BitVec 64) (OutValTy := Bool) "Fp64.Ge" (pred64 (decide <| · ≥ ·))
def eq64 : Func := binaryOp (InValTy := BitVec 64) (OutValTy := Bool) "Fp64.Eq" (pred64 (· == ·))

def add32 : Func := binaryOp (InValTy := BitVec 32) "Fp32.Add" (lift32 (· + ·))
def sub32 : Func := binaryOp (InValTy := BitVec 32) "Fp32.Sub" (lift32 (· - ·))
def mul32 : Func := binaryOp (InValTy := BitVec 32) "Fp32.Mul" (lift32 (· * ·))
def div32 : Func := binaryOp (InValTy := BitVec 32) "Fp32.Div" (lift32 (· / ·))
def truncRem32 : Func := binaryOp (InValTy := BitVec 32) "Fp32.TruncRem" rem32
def neg32Func : Func := unaryOp (InValTy := BitVec 32) "Fp32.Neg" neg32
def lt32 : Func := binaryOp (InValTy := BitVec 32) (OutValTy := Bool) "Fp32.Lt" (pred32 (decide <| · < ·))
def le32 : Func := binaryOp (InValTy := BitVec 32) (OutValTy := Bool) "Fp32.Le" (pred32 (decide <| · ≤ ·))
def gt32 : Func := binaryOp (InValTy := BitVec 32) (OutValTy := Bool) "Fp32.Gt" (pred32 (decide <| · > ·))
def ge32 : Func := binaryOp (InValTy := BitVec 32) (OutValTy := Bool) "Fp32.Ge" (pred32 (decide <| · ≥ ·))
def eq32 : Func := binaryOp (InValTy := BitVec 32) (OutValTy := Bool) "Fp32.Eq" (pred32 (· == ·))

def fp32ToFp64 : Func :=
  unaryOp (InValTy := BitVec 32) "Fp32.ToFp64" fun a => ofFloat (toFloat32 a).toFloat
def fp64ToFp32 : Func :=
  unaryOp (InValTy := BitVec 64) "Fp64.ToFp32" fun a => ofFloat32 (toFloat a).toFloat32

def fp64OfBv32 : Func :=
  unaryOp (InValTy := BitVec 32) "Fp64.OfBv32" fun a => ofFloat (Int32.ofBitVec a).toFloat
def fp64OfBv64 : Func :=
  unaryOp (InValTy := BitVec 64) "Fp64.OfBv64" fun a => ofFloat (Int64.ofBitVec a).toFloat
def fp32OfBv32 : Func :=
  unaryOp (InValTy := BitVec 32) "Fp32.OfBv32" fun a => ofFloat32 (Int32.ofBitVec a).toFloat32
def fp32OfBv64 : Func :=
  unaryOp (InValTy := BitVec 64) "Fp32.OfBv64" fun a => ofFloat32 (Int64.ofBitVec a).toFloat32

def fp64ToBv32Sat : Func :=
  unaryOp (InValTy := BitVec 64) "Fp64.ToBv32Sat" fun a => (toFloat a).toInt32.toBitVec
def fp64ToBv64Sat : Func :=
  unaryOp (InValTy := BitVec 64) "Fp64.ToBv64Sat" fun a => (toFloat a).toInt64.toBitVec
def fp32ToBv32Sat : Func :=
  unaryOp (InValTy := BitVec 32) "Fp32.ToBv32Sat" fun a => (toFloat32 a).toInt32.toBitVec
def fp32ToBv64Sat : Func :=
  unaryOp (InValTy := BitVec 32) "Fp32.ToBv64Sat" fun a => (toFloat32 a).toInt64.toBitVec

/-- The floating-point functions of the Cortex interpreter. -/
def functions : List (LFunc Core.CoreLParams) :=
  [add64, sub64, mul64, div64, truncRem64, neg64Func, lt64, le64, gt64, ge64, eq64,
   add32, sub32, mul32, div32, truncRem32, neg32Func, lt32, le32, gt32, ge32, eq32,
   fp32ToFp64, fp64ToFp32, fp64OfBv32, fp64OfBv64, fp32OfBv32, fp32OfBv64,
   fp64ToBv32Sat, fp64ToBv64Sat, fp32ToBv32Sat, fp32ToBv64Sat].map (·.func)

def factory : Lambda.Factory Core.CoreLParams := .ofArray functions.toArray

end

end Cortex.FloatFactory
