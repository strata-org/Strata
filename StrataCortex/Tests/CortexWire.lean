/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataCortex.Implementation.Pipeline
meta import StrataCortex.Implementation.Interpret

open Strata Cortex.Wire

namespace Cortex.WireTest

meta def at_ (n : Nat) : FileRange := { file := .file "T.java", range := { start := ⟨n⟩, stop := ⟨n + 1⟩ } }

meta def int32 : Constrained :=
  { name := "int32", base := .int, binder := "$v",
    constraint := .op "Bool.And" [.op "Int.Le" [.int (-2147483648), .var "$v"], .op "Int.Le" [.var "$v", .int 2147483647]],
    witness := some (.int 0) }

meta def i32 : Ty := .named "int32"

meta def blk (label : String) (cmds : List Cmd) (t : Transfer) : Block := { label, cmds, transfer := t }

meta def program : Wire.Program :=
  { composites := [
      { name := "Throwable", extending := [], fields := [] },
      { name := "Exn", extending := ["Throwable"], fields := [] },
      { name := "Box", extending := [], fields := [{ name := "v", ty := i32 }] }],
    constrained := [int32],
    procedures := [
      { name := "add", inputs := [{ name := "a", ty := i32 }, { name := "b", ty := i32 }],
        outputs := [{ name := "r", ty := i32 }], throws := none, requires := [], entry := false, source := at_ 1,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "r" (some (.op "Int.Add" [.var "a", .var "b"])) (at_ 2)] (.finish (at_ 3))] } },
      { name := "loop", inputs := [], outputs := [], throws := none, requires := [], entry := false, source := at_ 10,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "i" i32 (some (.int 0)) (at_ 11)] (.goto "head" (at_ 11)),
          blk "head" [] (.condGoto (.op "Int.Lt" [.var "i", .int 10]) "body" "exit" (at_ 12)),
          blk "body" [.set "i" (some (.op "Int.Add" [.var "i", .int 1])) (at_ 13)] (.goto "head" (at_ 13)),
          blk "exit" [.assert "a1" (.op "Int.Ge" [.var "i", .int 0]) none (at_ 14),
                      .assert "a2" (.eq (.var "i") (.int 3)) none (at_ 15)] (.finish (at_ 16))] } },
      { name := "heap", inputs := [], outputs := [], throws := none, requires := [], entry := false, source := at_ 20,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "x" (.named "Box") none (at_ 21), .new "x" "Box" (at_ 21),
                    .writeField (.var "x") "Box" "v" (.int 7) (at_ 22),
                    .init "t" i32 none (at_ 23),
                    .readField "t" (.var "x") "Box" "v" (at_ 23),
                    .assert "a3" (.eq (.var "t") (.int 7)) none (at_ 24)] (.finish (at_ 25))] } },
      { name := "exc", inputs := [], outputs := [], throws := none, requires := [], entry := false, source := at_ 30,
        body := some { entry := "b0", handlers := [{ covered := ["b0"], catchType := some "Exn", binder := "e", target := "h", source := at_ 31 }], blocks := [
            blk "b0" [.init "e" (.named "Exn") none (at_ 32), .init "x" (.named "Exn") none (at_ 32), .new "x" "Exn" (at_ 32), .throw (.var "x") none (at_ 33)] (.finish (at_ 34)),
            blk "h" [.assert "a4" (.bool true) (some "handler reached") (at_ 35)] (.finish (at_ 36))] } }] }

meta def run (p : Wire.Program) : IO Unit := do
  let options : Laurel.LaurelVerifyOptions := { verifyOptions := Core.VerifyOptions.quiet }
  for m in ← Cortex.verifyWireToMessages p options do
    IO.println s!"{m.fileRange.range.start.byteIdx}: {m.message}"

/--
info: 15: assertion does not hold
1: assertion does not hold
13: assertion does not hold
-/
#guard_msgs in
#eval run program

meta def entryProgram : Wire.Program :=
  { composites := [], constrained := [int32],
    procedures := [
      { name := "lib", inputs := [], outputs := [{ name := "r", ty := i32 }], throws := none, requires := [], body := none,
        entry := false, source := at_ 40 },
      { name := "run", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 41,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "x" i32 (some (.int 2)) (at_ 42),
                    .set "x" (some (.op "Int.Add" [.var "x", .int 1])) (at_ 43),
                    .assert "ok" (.eq (.var "x") (.int 3)) none (at_ 44),
                    .assert "bad" (.eq (.var "x") (.int 4)) none (at_ 45)] (.finish (at_ 46))] } },
      { name := "callsLib", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 50,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" i32 none (at_ 51), .call ["y"] "lib" [] (at_ 52)] (.finish (at_ 53))] } }] }

meta def interpret (p : Wire.Program) : IO Unit :=
  match Cortex.interpretWire p 1000 with
  | .error e => IO.println s!"error: {e}"
  | .ok (diags, errors) => do
    for m in diags do
      IO.println s!"{m.fileRange.range.start.byteIdx}: {m.message}"
    for e in errors do
      IO.println s!"stopped: {e}"

/--
info: 45: assertion does not hold
stopped: 'callsLib': call to procedure lib, which has no body
-/
#guard_msgs in
#eval interpret entryProgram

meta def noLoc : FileRange := { file := .file "", range := { start := ⟨0⟩, stop := ⟨0⟩ } }

meta def inInt32 (e : Wire.Expr) : Wire.Expr :=
  .op "Bool.And" [.op "Int.Le" [.int (-2147483648), e], .op "Int.Le" [e, .int 2147483647]]

meta def helperProgram : Wire.Program :=
  { composites := [{ name := "Throwable", extending := [], fields := [] },
                   { name := "Arith", extending := ["Throwable"], fields := [] }],
    constrained := [int32],
    procedures := [
      { name := "add", inputs := [{ name := "x", ty := i32 }, { name := "y", ty := i32 }],
        outputs := [{ name := "r", ty := i32 }], throws := none, entry := false, source := noLoc,
        requires := [{ cond := inInt32 (.op "Int.Add" [.var "x", .var "y"]), summary := some "no int overflow on '+'" }],
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "r" (some (.op "Int.Add" [.var "x", .var "y"])) noLoc] (.finish noLoc)] } },
      { name := "div", inputs := [{ name := "x", ty := i32 }, { name := "y", ty := i32 }],
        outputs := [{ name := "r", ty := i32 }], throws := some "Arith", requires := [], entry := false, source := noLoc,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "e" (.named "Arith") none noLoc] (.condGoto (.eq (.var "y") (.int 0)) "thr" "ok" noLoc),
          blk "thr" [.new "e" "Arith" noLoc, .throw (.var "e") none noLoc] (.finish noLoc),
          blk "ok" [.set "r" (some (.op "Int.DivT" [.var "x", .var "y"])) noLoc] (.finish noLoc)] } },
      { name := "overflows", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 60,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "z" i32 (some (.int 0)) (at_ 61),
                    .call ["z"] "add" [.int 2147483647, .int 1] (at_ 62)] (.finish (at_ 63))] } },
      { name := "fine", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 64,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "z" i32 (some (.int 0)) (at_ 65),
                    .call ["z"] "add" [.int 2, .int 1] (at_ 66),
                    .assert "three" (.eq (.var "z") (.int 3)) none (at_ 67)] (.finish (at_ 68))] } },
      { name := "divByZero", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 70,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "z" i32 (some (.int 0)) (at_ 71),
                    .call ["z"] "div" [.int 1, .int 0] (at_ 72)] (.finish (at_ 73))] } }] }

/--
info: 62: no int overflow on '+' does not hold
72: uncaught exception 'Arith' is not thrown does not hold
-/
#guard_msgs in
#eval interpret helperProgram

/--
info: 82: no int overflow on '+' does not hold
-/
#guard_msgs in
#eval run { helperProgram with procedures := helperProgram.procedures.take 1 ++
  [{ name := "caller", inputs := [{ name := "a", ty := i32 }], outputs := [], throws := none, requires := [],
     entry := false, source := at_ 80,
     body := some { entry := "b0", handlers := [], blocks := [
       blk "b0" [.init "z" i32 (some (.int 0)) (at_ 81),
                 .call ["z"] "add" [.var "a", .int 1] (at_ 82)] (.finish (at_ 83))] } }] }

meta def arityCaller (lhs : List String) (args : List Wire.Expr) : Wire.Program :=
  { helperProgram with procedures := helperProgram.procedures.take 1 ++
    [{ name := "caller", inputs := [], outputs := [], throws := none, requires := [], entry := false,
       source := at_ 84,
       body := some { entry := "b0", handlers := [], blocks := [
         blk "b0" [.init "z" i32 (some (.int 0)) (at_ 85), .call lhs "add" args (at_ 86)] (.finish (at_ 87))] } }] }

/--
info: 0: invalid Cortex program: 'caller': call to 'add' passes 1 arguments, but it takes 2
-/
#guard_msgs in
#eval run (arityCaller ["z"] [.int 1])

/--
info: 0: invalid Cortex program: 'caller': call to 'add' assigns 0 results, but it returns 1
-/
#guard_msgs in
#eval run (arityCaller [] [.int 1, .int 2])

meta def assignsInput : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "dec", inputs := [{ name := "x", ty := .int }], outputs := [], throws := none, entry := false,
        source := noLoc, requires := [{ cond := .op "Int.Gt" [.var "x", .int 0], summary := some "x is positive" }],
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "x" (some (.op "Int.Sub" [.var "x", .int 1])) noLoc] (.finish noLoc)] } },
      { name := "caller", inputs := [], outputs := [], throws := none, requires := [], entry := false,
        source := at_ 88,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.call [] "dec" [.int 1] (at_ 89), .call [] "dec" [.int 0] (at_ 90)] (.finish (at_ 91))] } }] }

/--
info:

Obligation callElimAssert_requires_0_3: failed!

Result obtained during evaluation.
90: x is positive does not hold
-/
#guard_msgs in
#eval run assignsInput

meta def ae : String := "java.lang.ArithmeticException"

meta def preludeProgram : Wire.Program :=
  { composites := [{ name := ae, extending := [], fields := [] }], constrained := [], preludes := ["java"],
    procedures := [
      { name := "overflow", inputs := [], outputs := [], throws := none, requires := [], entry := true,
        source := at_ 90,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "z" (.bv 32) none (at_ 91),
                    .call ["z"] "java$iadd" [.bv 32 2147483647, .bv 32 1] (at_ 92)] (.finish (at_ 93))] } },
      { name := "divide", inputs := [], outputs := [], throws := none, requires := [], entry := true,
        source := at_ 94,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "z" (.bv 32) none (at_ 95),
                    .call ["z"] "java$idiv" [.bv 32 (-2147483648), .bv 32 (-1)] (at_ 96),
                    .assert "wraps" (.eq (.var "z") (.bv 32 (-2147483648))) none (at_ 97),
                    .call ["z"] "java$i2b" [.bv 32 200] (at_ 98),
                    .call ["z"] "java$idiv" [.bv 32 1, .bv 32 0] (at_ 99)] (.finish (at_ 100))] } }] }

/--
info: 92: no int overflow on '+' does not hold
98: cast from int32 to int8 does not hold
99: uncaught exception 'java.lang.ArithmeticException' is not thrown does not hold
-/
#guard_msgs in
#eval interpret preludeProgram

end Cortex.WireTest
