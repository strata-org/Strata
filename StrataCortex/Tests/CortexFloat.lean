/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataCortex.Implementation.Pipeline
meta import StrataCortex.Implementation.Interpret

/-!
# Floating point in Cortex

The functions of `Cortex.FloatFactory` on bit patterns, then wire programs that use them: run
on the Cortex interpreter, and rejected by the route to Core.
-/

open Strata Cortex.Wire

namespace Cortex.FloatTest

open Cortex.FloatFactory

/-- The result of `f` on one argument, or `none` when `f` does not evaluate or its result is
not `n` bits wide. -/
meta def un (f : Func) {m n : Nat} (a : BitVec m) : Option (BitVec n) := do
  let eval ← f.func.concreteEval
  let r ← eval default none [Lambda.LExpr.bitvecConst default m a]
  Lambda.LExpr.denoteBitVec n r

/-- The result of the comparison `f` on two arguments, or `none` when it does not evaluate. -/
meta def cmp (f : Func) {m : Nat} (a b : BitVec m) : Option Bool := do
  let eval ← f.func.concreteEval
  let r ← eval default none [Lambda.LExpr.bitvecConst default m a, Lambda.LExpr.bitvecConst default m b]
  Lambda.LExpr.denoteBool r

/-- The result of `f` on two arguments, as `un` gives it. -/
meta def bin (f : Func) {m n : Nat} (a b : BitVec m) : Option (BitVec n) := do
  let eval ← f.func.concreteEval
  let r ← eval default none [Lambda.LExpr.bitvecConst default m a, Lambda.LExpr.bitvecConst default m b]
  Lambda.LExpr.denoteBitVec n r

meta def zero : BitVec 64 := 0x0000000000000000#64
meta def negZero : BitVec 64 := 0x8000000000000000#64
meta def one : BitVec 64 := 0x3FF0000000000000#64
meta def two : BitVec 64 := 0x4000000000000000#64
meta def inf : BitVec 64 := 0x7FF0000000000000#64
meta def negInf : BitVec 64 := 0xFFF0000000000000#64
meta def nan : BitVec 64 := 0x7FF8000000000000#64
meta def tenth : BitVec 64 := 0x3FB999999999999A#64

meta def one32 : BitVec 32 := 0x3F800000#32
meta def inf32 : BitVec 32 := 0x7F800000#32
meta def nan32 : BitVec 32 := 0x7FC00000#32

/-! ## binary64 arithmetic -/

-- 0.1 + 0.2 = 0.30000000000000004, and 1.0 - 0.9 = 0.09999999999999998.
#guard bin add64 tenth 0x3FC999999999999A#64 == some 0x3FD3333333333334#64
#guard bin sub64 one 0x3FECCCCCCCCCCCCD#64 == some 0x3FB9999999999998#64
-- 0.1 * 3.0 = 0.30000000000000004, and 1e300 / 3.0.
#guard bin mul64 tenth 0x4008000000000000#64 == some 0x3FD3333333333334#64
#guard bin div64 0x7E37E43C8800759C#64 0x4008000000000000#64 == some 0x7E1FDAFB60009CD0#64
-- Overflow gives an infinity, and a division by zero an infinity with the sign of the quotient.
#guard bin mul64 0x7FEFFFFFFFFFFFFF#64 two == some inf
#guard bin div64 one zero == some inf
#guard bin div64 one negZero == some negInf
-- 0.0 / 0.0 and Infinity - Infinity are the one NaN, as is every operation on a NaN, whatever
-- its sign and payload.
#guard bin div64 zero zero == some nan
#guard bin sub64 inf inf == some nan
#guard bin add64 0xFFF8000000000123#64 one == some nan
-- The sum of the two zeros is +0.0, and -0.0 + -0.0 is -0.0.
#guard bin add64 zero negZero == some zero
#guard bin add64 negZero negZero == some negZero
-- The least positive value halves to zero: ties round to even.
#guard bin div64 0x0000000000000001#64 two == some zero

/-! ## Negation -/

#guard un neg64Func one == some 0xBFF0000000000000#64
#guard un neg64Func zero == some negZero
#guard un neg64Func negZero == some zero
#guard un neg64Func inf == some negInf
#guard un neg32Func one32 == some 0xBF800000#32
#guard un neg32Func 0x00000000#32 == some 0x80000000#32

/-! ## Comparison -/

#guard cmp lt64 one two == some true
#guard cmp lt64 two one == some false
#guard cmp lt64 one one == some false
#guard cmp le64 one one == some true
#guard cmp le64 two one == some false
#guard cmp gt64 two one == some true
#guard cmp gt64 one one == some false
#guard cmp ge64 one one == some true
#guard cmp ge64 one two == some false
#guard cmp eq64 one one == some true
#guard cmp eq64 one two == some false
#guard cmp lt64 negInf inf == some true
-- The two zeros are equal, though their bits differ.
#guard cmp eq64 zero negZero == some true
#guard cmp lt64 negZero zero == some false
#guard cmp le64 zero negZero == some true
-- A NaN is unordered, also with itself: every comparison with one is false.
#guard cmp eq64 nan nan == some false
#guard cmp lt64 nan one == some false
#guard cmp le64 one nan == some false
#guard cmp gt64 nan one == some false
#guard cmp ge64 nan nan == some false
#guard cmp lt32 one32 inf32 == some true
#guard cmp eq32 0x00000000#32 0x80000000#32 == some true
#guard cmp eq32 nan32 nan32 == some false
#guard cmp ge32 nan32 one32 == some false
#guard cmp le32 one32 one32 == some true
#guard cmp gt32 inf32 one32 == some true

/-! ## Remainder -/

-- 5.5 rem 2.0 = 1.5; the result has the sign of the dividend.
#guard bin truncRem64 0x4016000000000000#64 two == some 0x3FF8000000000000#64
#guard bin truncRem64 0xC016000000000000#64 two == some 0xBFF8000000000000#64
#guard bin truncRem64 0x4016000000000000#64 0xC000000000000000#64 == some 0x3FF8000000000000#64
-- 0.3 rem 0.1 = 0.09999999999999998, and 1e300 rem 3.0 = 0.0: exact, whatever the quotient.
#guard bin truncRem64 0x3FD3333333333333#64 tenth == some 0x3FB9999999999998#64
#guard bin truncRem64 0x7E37E43C8800759C#64 0x4008000000000000#64 == some zero
-- A zero result keeps the sign of the dividend.
#guard bin truncRem64 0xC01C000000000000#64 0x401C000000000000#64 == some negZero
#guard bin truncRem64 negZero one == some negZero
-- An infinite dividend, a zero divisor and a NaN give a NaN.
#guard bin truncRem64 inf one == some nan
#guard bin truncRem64 one zero == some nan
#guard bin truncRem64 one negZero == some nan
#guard bin truncRem64 nan one == some nan
#guard bin truncRem64 one 0xFFF8000000000001#64 == some nan
-- An infinite divisor leaves a finite dividend as it is.
#guard bin truncRem64 one inf == some one
#guard bin truncRem64 0xC016000000000000#64 negInf == some 0xC016000000000000#64
-- Subnormal values: 1.0 rem 4.9e-324 = 0.0, and 4.9e-324 rem 3.0 = 4.9e-324.
#guard bin truncRem64 one 0x0000000000000001#64 == some zero
#guard bin truncRem64 0x0000000000000001#64 0x4008000000000000#64 == some 0x0000000000000001#64
-- binary32: 5.5f rem 2.0f = 1.5f, and Infinity rem 1.0f is the NaN.
#guard bin truncRem32 0x40B00000#32 0x40000000#32 == some 0x3FC00000#32
#guard bin truncRem32 0xC0B00000#32 0x40000000#32 == some 0xBFC00000#32
#guard bin truncRem32 inf32 one32 == some nan32

/-! ## binary32 arithmetic -/

-- 0.1f + 0.2f = 0.3f, rounded as binary32 and not as binary64.
#guard bin add32 0x3DCCCCCD#32 0x3E4CCCCD#32 == some 0x3E99999A#32
-- 16777216f + 1f = 16777216f: the sum is a tie and rounds to even.
#guard bin add32 0x4B800000#32 one32 == some 0x4B800000#32
#guard bin sub32 one32 one32 == some 0x00000000#32
#guard bin mul32 0x7F7FFFFF#32 0x40000000#32 == some inf32
#guard bin div32 0x00000000#32 0x00000000#32 == some nan32
#guard bin div32 one32 0x40400000#32 == some 0x3EAAAAAB#32

/-! ## Conversions between the formats -/

-- 0.1f widens exactly, to a value that is not 0.1.
#guard un fp32ToFp64 0x3DCCCCCD#32 == some 0x3FB99999A0000000#64
#guard un fp32ToFp64 0x00000001#32 == some 0x36A0000000000000#64
#guard un fp32ToFp64 inf32 == some inf
#guard un fp32ToFp64 0xFFC00001#32 == some nan
-- 0.1 rounds to 0.1f, the greatest binary64 value to Infinity, and 1e-310 to 0.0f.
#guard un fp64ToFp32 tenth == some 0x3DCCCCCD#32
#guard un fp64ToFp32 0x7FEFFFFFFFFFFFFF#64 == some inf32
#guard un fp64ToFp32 0x000012688B70E62B#64 == some 0x00000000#32
#guard un fp64ToFp32 negZero == some 0x80000000#32
#guard un fp64ToFp32 nan == some nan32

/-! ## Conversions from integers -/

#guard un fp64OfBv32 100#32 == some 0x4059000000000000#64
#guard un fp64OfBv32 (-1#32) == some 0xBFF0000000000000#64
#guard un fp64OfBv32 0x80000000#32 == some 0xC1E0000000000000#64
-- 2^53 + 1 is a tie and rounds to 2^53; the greatest `bv64` integer rounds to 2^63.
#guard un fp64OfBv64 9007199254740993#64 == some 0x4340000000000000#64
#guard un fp64OfBv64 0x7FFFFFFFFFFFFFFF#64 == some 0x43E0000000000000#64
#guard un fp64OfBv64 (-1#64) == some 0xBFF0000000000000#64
-- 16777217 is a tie and rounds to 16777216f.
#guard un fp32OfBv32 16777217#32 == some 0x4B800000#32
#guard un fp32OfBv32 100#32 == some 0x42C80000#32
#guard un fp32OfBv64 0x7FFFFFFFFFFFFFFF#64 == some 0x5F000000#32
#guard un fp32OfBv64 (-1#64) == some 0xBF800000#32

/-! ## Conversions to integers -/

-- 3.99 and -3.99 round toward zero.
#guard un fp64ToBv32Sat 0x400FEB851EB851EC#64 == some 3#32
#guard un fp64ToBv32Sat 0xC00FEB851EB851EC#64 == some (-3#32)
#guard un fp64ToBv32Sat negZero == some 0#32
-- A NaN gives 0; Infinity, -Infinity, 1e10 and -1e30 give the nearest integer of the width.
#guard un fp64ToBv32Sat nan == some 0#32
#guard un fp64ToBv32Sat inf == some 0x7FFFFFFF#32
#guard un fp64ToBv32Sat negInf == some 0x80000000#32
#guard un fp64ToBv32Sat 0x4202A05F20000000#64 == some 0x7FFFFFFF#32
#guard un fp64ToBv32Sat 0xC6293E5939A08CEA#64 == some 0x80000000#32
#guard un fp64ToBv64Sat 0x4202A05F20000000#64 == some 10000000000#64
#guard un fp64ToBv64Sat nan == some 0#64
#guard un fp64ToBv64Sat inf == some 0x7FFFFFFFFFFFFFFF#64
#guard un fp64ToBv64Sat 0xC6293E5939A08CEA#64 == some 0x8000000000000000#64
#guard un fp32ToBv32Sat 0xC0200000#32 == some (-2#32)
#guard un fp32ToBv32Sat nan32 == some 0#32
#guard un fp32ToBv32Sat inf32 == some 0x7FFFFFFF#32
#guard un fp32ToBv64Sat 0x5F000000#32 == some 0x7FFFFFFFFFFFFFFF#64
#guard un fp32ToBv64Sat 0xFF800000#32 == some 0x8000000000000000#64

/-! ## The functions' types -/

-- A result of another width than the function's is not read.
#guard (bin add64 one one : Option (BitVec 32)) == none
#guard (un fp64ToBv32Sat one : Option (BitVec 64)) == none
#guard FloatFactory.functions.length == 32
#guard (FloatFactory.functions.map (·.name.name)).eraseDups.length == 32
-- Core's factory has none of them.
#guard FloatFactory.functions.all fun f => (Core.Factory.get? f.name.name).isNone

/-! ## Wire programs -/

meta def at_ (n : Nat) : FileRange := { file := .file "T.java", range := { start := ⟨n⟩, stop := ⟨n + 1⟩ } }

meta def blk (label : String) (cmds : List Cmd) (t : Transfer) : Block := { label, cmds, transfer := t }

meta def bv32 : Ty := .bv 32
meta def bv64 : Ty := .bv 64

meta def dbl (bits : BitVec 64) : Wire.Expr := .bv 64 bits.toNat

meta def program (procedures : List Wire.Procedure) : Wire.Program :=
  { composites := [{ name := "Object", extending := [], fields := [] }],
    constrained := [],
    arrayParents := ["Object"],
    procedures }

meta def interpret (p : Wire.Program) : IO Unit :=
  match Cortex.interpretWire p 1000 with
  | .error e => IO.println s!"error: {e}"
  | .ok outcome => do
    for m in outcome.diagnostics do
      IO.println s!"{m.fileRange.range.start.byteIdx}: {m.message}"
    for (name, reason) in outcome.errors do
      IO.println s!"stopped: '{name}': {reason}"

meta def isTrue (label : String) (cond : Wire.Expr) (n : Nat) : Cmd := .assert label cond none (at_ n)

/-- `half(x)` is `x / 2.0`. -/
meta def half : Wire.Procedure :=
  { name := "half", inputs := [{ name := "x", ty := bv64 }], outputs := [{ name := "r", ty := bv64 }],
    throws := none, requires := [], entry := false, source := at_ 0,
    body := some { entry := "b0", handlers := [], blocks := [
      blk "b0" [.set "r" (some (.op "Fp64.Div" [.var "x", dbl two])) (at_ 0)] (.finish (at_ 0))] } }

/-! A loop adds 0.1 ten times, leaving when the sum is no longer less than 0.95, which
`Fp64.Lt` decides. The sum is 0.9999999999999999, less than 1.0. A call passes and returns
a `bv64`, a new array holds +0.0, and an element keeps the bits written to it. The
assertions at offsets 20 to 23 state the opposite of those before them and fail, so the ones
before them are checked. -/

meta def sums : Wire.Procedure :=
  { name := "sums", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 0,
    body := some { entry := "b0", handlers := [], blocks := [
      blk "b0" [.init "s" bv64 (some (dbl zero)) (at_ 1), .init "n" .int (some (.int 0)) (at_ 1),
                .init "h" bv64 none (at_ 1), .init "a" (.array bv64) none (at_ 1),
                .init "e" bv64 none (at_ 1), .init "i" bv32 none (at_ 1)] (.goto "head" (at_ 1)),
      blk "head" []
        (.condGoto (.op "Fp64.Lt" [.var "s", dbl 0x3FEE666666666666#64]) "body" "exit" (at_ 2)),
      blk "body" [.set "s" (some (.op "Fp64.Add" [.var "s", dbl tenth])) (at_ 3),
                  .set "n" (some (.op "Int.Add" [.var "n", .int 1])) (at_ 3)] (.goto "head" (at_ 3)),
      blk "exit" [
        .call ["h"] "half" [.var "s"] (at_ 4),
        .newArray "a" bv64 (.int 2) (at_ 5),
        .readElem "e" (.var "a") (.int 1) bv64 (at_ 5),
        .set "i" (some (.op "Fp64.ToBv32Sat" [.op "Fp64.Mul" [.var "s", dbl 0x4059000000000000#64]])) (at_ 6),
        isTrue "iterations" (.eq (.var "n") (.int 10)) 10,
        isTrue "sum" (.eq (.var "s") (dbl 0x3FEFFFFFFFFFFFFF#64)) 11,
        isTrue "belowOne" (.op "Fp64.Lt" [.var "s", dbl one]) 12,
        isTrue "halved" (.eq (.var "h") (dbl 0x3FDFFFFFFFFFFFFF#64)) 13,
        isTrue "elementDefault" (.eq (.var "e") (dbl zero)) 14,
        isTrue "truncated" (.eq (.var "i") (.bv 32 99)) 15,
        .writeElem (.var "a") (.int 1) (.op "Fp64.Neg" [.var "e"]) bv64 (at_ 16),
        .readElem "e" (.var "a") (.int 1) bv64 (at_ 16),
        isTrue "elementWritten" (.eq (.var "e") (dbl negZero)) 17,
        isTrue "zerosCompareEqual" (.op "Fp64.Eq" [.var "e", dbl zero]) 18,
        isTrue "sumIsOne" (.eq (.var "s") (dbl one)) 20,
        isTrue "notBelowOne" (.op "Fp64.Ge" [.var "s", dbl one]) 21,
        isTrue "sameBits" (.eq (.var "e") (dbl zero)) 22,
        isTrue "rounded" (.eq (.var "i") (.bv 32 100)) 23] (.finish (at_ 30))] } }

/--
info: 20: assertion does not hold
21: assertion does not hold
22: assertion does not hold
23: assertion does not hold
-/
#guard_msgs in
#eval interpret (program [half, sums])

/-! binary32 values are `bv32`: 16777217 converts to 16777216f, which widens to the same
binary64 value as 16777216 converts to. -/

meta def floats : Wire.Procedure :=
  { name := "floats", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 0,
    body := some { entry := "b0", handlers := [], blocks := [
      blk "b0" [
        .init "f" bv32 (some (.op "Fp32.OfBv32" [.bv 32 16777217])) (at_ 1),
        .init "d" bv64 (some (.op "Fp32.ToFp64" [.var "f"])) (at_ 2),
        isTrue "rounded" (.eq (.var "f") (.bv 32 0x4B800000)) 3,
        isTrue "widened" (.eq (.var "d") (.op "Fp64.OfBv32" [.bv 32 16777216])) 4,
        isTrue "narrowed" (.eq (.op "Fp64.ToFp32" [.var "d"]) (.var "f")) 5,
        isTrue "exact" (.eq (.var "d") (.op "Fp64.OfBv32" [.bv 32 16777217])) 10] (.finish (at_ 20))] } }

/--
info: 10: assertion does not hold
-/
#guard_msgs in
#eval interpret (program [floats])

/-! The type checker knows the functions' types: a `bv32` is not an argument of `Fp64.Add`. -/

meta def illTyped : Wire.Procedure :=
  { name := "illTyped", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 0,
    body := some { entry := "b0", handlers := [], blocks := [
      blk "b0" [.init "s" bv64 (some (.op "Fp64.Add" [dbl one, .bv 32 1])) (at_ 1)] (.finish (at_ 2))] } }

/--
info: stopped: 'illTyped': type error: procedure illTyped: Impossible to unify (arrow bv64 bv64) with (arrow bv32 $__ty1).
First mismatch: bv64 with bv32.
-/
#guard_msgs in
#eval interpret (program [illTyped])

/-! Core's factory does not have the functions, so the Core program that the route to Core
gives for a program that uses one does not type check. The same program with a function of
Core's factory in its place does. -/

meta def adds : Wire.Procedure :=
  { name := "adds", inputs := [{ name := "x", ty := bv64 }], outputs := [{ name := "r", ty := bv64 }],
    throws := none, requires := [], entry := false, source := at_ 0,
    body := some { entry := "b0", handlers := [], blocks := [
      blk "b0" [.set "r" (some (.op "Fp64.Add" [.var "x", dbl one])) (at_ 1)] (.finish (at_ 2))] } }

/-- `adds` with Core's `Bv64.Add` in the place of `Fp64.Add`. -/
meta def addsBits : Wire.Procedure :=
  { adds with body := some { entry := "b0", handlers := [], blocks := [
      blk "b0" [.set "r" (some (.op "Bv64.Add" [.var "x", dbl one])) (at_ 1)] (.finish (at_ 2))] } }

meta def toCore (p : Wire.Program) : IO Unit :=
  match Cortex.wireToCortex p >>= (Cortex.toCoreProgram ·) with
  | .error e => IO.println s!"Cortex lowering failed: {e}"
  | .ok core => match Core.typeCheck .quiet core with
    -- The message lists the names of every function Core knows before the reason.
    | .error e => IO.println s!"Core type checking failed: {((s!"{e}").splitOn "] ").getLast?.getD ""}"
    | .ok _ => IO.println "Core type checking succeeded"

/--
info: Core type checking failed: Cannot infer the type of this operation: `Fp64.Add`
-/
#guard_msgs in
#eval toCore { composites := [], constrained := [], procedures := [adds] }

/--
info: Core type checking succeeded
-/
#guard_msgs in
#eval toCore { composites := [], constrained := [], procedures := [addsBits] }

end Cortex.FloatTest
