/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Wire

/-!
# The Java prelude

Cortex procedures for the JVM operations that can fail, for frontends that
translate Java bytecode: arithmetic that must not overflow, division and
remainder that throw `java.lang.ArithmeticException` on a zero divisor, and
narrowing conversions whose value must fit. `int` values are `bv32` and `long`
values `bv64`, so the operations themselves are Core's bit-vector ones, which
wrap as the JVM's do. The checks are preconditions, reported at the call.

A frontend that lists `"java"` among a program's preludes calls these as
`java$iadd` and so on; `Wire.Program.withPreludes` adds the ones it calls. A
program that calls a division helper must declare `java.lang.ArithmeticException`.
-/

namespace Cortex.JavaPrelude

public section


def arithmeticException : String := "java.lang.ArithmeticException"

def noLocation : Strata.FileRange := { file := .file "", range := { start := ⟨0⟩, stop := ⟨0⟩ } }

def bvTy (w : Nat) : Wire.Ty := .bv w

def var (n : String) : Wire.Expr := .var n

def bvOp (w : Nat) (op : String) (args : List Wire.Expr) : Wire.Expr := .op s!"Bv{w}.{op}" args

def inRange (e : Wire.Expr) (lo hi : Int) : Wire.Expr :=
  .op "Bool.And" [.op "Int.Le" [.int lo, e], .op "Int.Le" [e, .int hi]]

def block (label : String) (cmds : List Wire.Cmd) (t : Wire.Transfer) : Wire.Block := { label, cmds, transfer := t }

def helper (name : String) (inputs : List (String × Nat)) (outW : Nat) (pres : List Wire.Precondition)
    (blocks : List Wire.Block) (throws : Option String := none) : Wire.Procedure :=
  { name := s!"java${name}", inputs := inputs.map fun (n, w) => { name := n, ty := bvTy w },
    outputs := [{ name := "r", ty := bvTy outW }], throws, requires := pres, entry := false, source := noLocation,
    body := some { entry := "b0", blocks, handlers := [] } }

def returns (e : Wire.Expr) : List Wire.Block := [block "b0" [.set "r" (some e) noLocation] (.finish noLocation)]

/-- `x <op> y` on `w`-bit values, which must not overflow. -/
def checkedBinary (name : String) (w : Nat) (op overflow symbol : String) : Wire.Procedure :=
  helper name [("x", w), ("y", w)] w
    [{ cond := .op "Bool.Not" [bvOp w overflow [var "x", var "y"]],
       summary := some s!"no {if w == 64 then "long" else "int"} overflow on '{symbol}'" }]
    (returns (bvOp w op [var "x", var "y"]))

def checkedNeg (name : String) (w : Nat) : Wire.Procedure :=
  helper name [("x", w)] w
    [{ cond := .op "Bool.Not" [bvOp w "SNegOverflow" [var "x"]],
       summary := some s!"no {if w == 64 then "long" else "int"} overflow on '-'" }]
    (returns (bvOp w "Neg" [var "x"]))

/-- `x <op> y` on `w`-bit values, throwing `ArithmeticException` when `y` is zero. -/
def division (name : String) (w : Nat) (op : String) : Wire.Procedure :=
  helper name [("x", w), ("y", w)] w []
    [block "b0" [.init "e" (.named arithmeticException) none noLocation]
       (.condGoto (.eq (var "y") (.bv w 0)) "zero" "ok" noLocation),
     block "zero" [.new "e" arithmeticException noLocation, .throw (var "e") none noLocation] (.finish noLocation),
     block "ok" [.set "r" (some (bvOp w op [var "x", var "y"])) noLocation] (.finish noLocation)]
    (throws := some arithmeticException)

/-- A narrowing of an `int` to `bits` bits, sign- or zero-extended back, whose value must fit. -/
def narrowing (name target : String) (bits : Nat) (signed : Bool) (lo hi : Int) : Wire.Procedure :=
  let x := bvOp 32 "ToInt" [var "x"]
  let truncated := Wire.Expr.op s!"Int.ToBv{bits}" [x]
  let extended := Wire.Expr.op (if signed then s!"Bv{bits}.ToInt" else s!"Bv{bits}.ToUInt") [truncated]
  helper name [("x", 32)] 32 [{ cond := inRange x lo hi, summary := some s!"cast from int32 to {target}" }]
    (returns (.op "Int.ToBv32" [extended]))

def procedures : List Wire.Procedure :=
  [checkedBinary "iadd" 32 "Add" "SAddOverflow" "+", checkedBinary "isub" 32 "Sub" "SSubOverflow" "-",
   checkedBinary "imul" 32 "Mul" "SMulOverflow" "*", checkedNeg "ineg" 32,
   checkedBinary "ladd" 64 "Add" "SAddOverflow" "+", checkedBinary "lsub" 64 "Sub" "SSubOverflow" "-",
   checkedBinary "lmul" 64 "Mul" "SMulOverflow" "*", checkedNeg "lneg" 64,
   division "idiv" 32 "SDiv", division "irem" 32 "SMod", division "ldiv" 64 "SDiv", division "lrem" 64 "SMod",
   narrowing "i2b" "int8" 8 true (-128) 127, narrowing "i2s" "int16" 16 true (-32768) 32767,
   narrowing "i2c" "char" 16 false 0 65535,
   helper "l2i" [("x", 64)] 32
     [{ cond := inRange (bvOp 64 "ToInt" [var "x"]) (-2147483648) 2147483647, summary := some "cast from int64 to int32" }]
     (returns (.op "Int.ToBv32" [bvOp 64 "ToInt" [var "x"]]))]

end

end Cortex.JavaPrelude

namespace Cortex.Wire

public section

def preludeProcedures : String → Option (List Procedure)
  | "java" => some JavaPrelude.procedures
  | _ => none

def Cmd.calls : Cmd → List String
  | .call _ p _ _ => [p]
  | _ => []

/-- The program with the procedures of its preludes that it calls. -/
def Program.withPreludes (p : Program) : Except String Program := do
  let mut available : List Procedure := []
  for name in p.preludes do
    match preludeProcedures name with
    | some ps => available := available ++ ps
    | none => throw s!"unknown prelude '{name}'"
  let called : List String := p.procedures.flatMap fun proc => match proc.body with
    | some b => b.blocks.flatMap fun blk => blk.cmds.flatMap Cmd.calls
    | none => []
  let defined := p.procedures.map (·.name)
  let added := available.filter fun q => called.contains q.name && !defined.contains q.name
  return { p with procedures := p.procedures ++ added }

end

end Cortex.Wire
