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

/-! Globals: an entry procedure starts from the initializers; any other procedure starts with
arbitrary values. A flag-guarded initializer is seen by the caller only when it is inlined. -/

meta def i32v (n : Int) : Wire.Expr := .int n

meta def globalsProgram : Wire.Program :=
  { composites := [], constrained := [int32],
    globals := [{ name := "C:x", ty := i32, init := some (i32v 0), source := at_ 60 },
                { name := "C:ready", ty := .bool, init := some (.bool false), source := at_ 61 }],
    procedures := [
      { name := "C:<clinit>", inputs := [], outputs := [], throws := none, requires := [], entry := false,
        source := at_ 62,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "C:x" (some (i32v 5)) (at_ 63)] (.finish (at_ 63))] } },
      { name := "reader", inputs := [], outputs := [{ name := "r", ty := i32 }], throws := none, requires := [],
        entry := false, source := at_ 70,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [] (.condGoto (.var "C:ready") "use" "init" (at_ 71)),
          blk "init" [.set "C:ready" (some (.bool true)) (at_ 72), .call [] "C:<clinit>" [] (at_ 72),
                      .set "C:ready" (some (.bool true)) (at_ 72)] (.goto "use" (at_ 72)),
          blk "use" [.set "r" (some (.var "C:x")) (at_ 73),
                     .assert "arbitrary" (.eq (.var "C:x") (i32v 5)) none (at_ 74)] (.finish (at_ 75))] } },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 80,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.assert "fromInit" (.eq (.var "C:x") (i32v 0)) none (at_ 81)]
            (.condGoto (.var "C:ready") "use" "init" (at_ 82)),
          blk "init" [.set "C:ready" (some (.bool true)) (at_ 83), .call [] "C:<clinit>" [] (at_ 83),
                      .set "C:ready" (some (.bool true)) (at_ 83)] (.goto "use" (at_ 83)),
          blk "use" [.assert "initialized" (.eq (.var "C:x") (i32v 5)) none (at_ 84)] (.finish (at_ 85))] } }] }

-- Without inlining, the caller knows nothing about `C:x` after the call.
/--
info: 74: assertion does not hold
84: assertion does not hold
-/
#guard_msgs in
#eval run globalsProgram

meta def runInlining (p : Wire.Program) (inline : List String) : IO Unit := do
  let options : Laurel.LaurelVerifyOptions := { verifyOptions := Core.VerifyOptions.quiet }
  for m in ← Cortex.verifyWireToMessages p options inline do
    IO.println s!"{m.fileRange.range.start.byteIdx}: {m.message}"

-- With the initializer inlined, the entry procedure sees the value it assigns; `reader` still
-- starts with an arbitrary `C:x` and an arbitrary flag.
/--
info: 74: assertion does not hold
-/
#guard_msgs in
#eval runInlining globalsProgram ["C:<clinit>"]

-- The interpreter starts the entry procedure from the initializers.
/--
info: 84: assertion does not hold
-/
#guard_msgs in
#eval interpret { globalsProgram with
  procedures := globalsProgram.procedures.filter (·.name != "reader") |>.map fun q =>
    if q.name != "main" then q else
    { q with body := q.body.map fun b => { b with blocks := b.blocks.map fun blk =>
        if blk.label != "use" then blk else
        { blk with cmds := [.assert "initialized" (.eq (.var "C:x") (i32v 6)) none (at_ 84)] } } } }

meta def entryLabelledGlobalsEntry : Wire.Program :=
  { globalsProgram with procedures := globalsProgram.procedures.map fun q =>
      if q.name != "main" then q else
      { q with body := q.body.map fun b => { b with entry := "$globalsEntry", blocks := b.blocks.map fun blk =>
          if blk.label == "b0" then { blk with label := "$globalsEntry" } else blk } } }

/--
info: 74: assertion does not hold
84: assertion does not hold
-/
#guard_msgs in
#eval run entryLabelledGlobalsEntry

#guard_msgs in
#eval interpret entryLabelledGlobalsEntry

meta def callResultClash : Wire.Program :=
  { composites := [], constrained := [int32],
    globals := [{ name := "g", ty := i32, init := some (i32v 0), source := at_ 90 }],
    procedures := [
      { name := "f", inputs := [], outputs := [{ name := "r", ty := i32 }], throws := none, requires := [], entry := false,
        source := at_ 91,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "g" (some (i32v 5)) (at_ 92), .set "r" (some (i32v 8)) (at_ 92)] (.finish (at_ 92))] } },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 93,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "$callResult" i32 (some (i32v 1)) (at_ 94), .init "$callResult0" i32 (some (i32v 1)) (at_ 94),
                    .call ["g"] "f" [] (at_ 95),
                    .assert "kept" (.eq (.var "$callResult") (i32v 1)) none (at_ 96),
                    .assert "result" (.eq (.var "g") (i32v 8)) none (at_ 97)] (.finish (at_ 98))] } }] }

/--
info: 97: assertion does not hold
-/
#guard_msgs in
#eval run callResultClash

#guard_msgs in
#eval interpret callResultClash

-- `dec` has a precondition. Without inlining, Core checks it at the call, and the caller knows
-- nothing about `y` afterwards.
meta def requiresProgram : Wire.Program :=
  { composites := [], constrained := [int32],
    procedures := [
      { name := "dec", inputs := [{ name := "x", ty := i32 }], outputs := [{ name := "r", ty := i32 }], throws := none,
        requires := [{ cond := .op "Int.Lt" [i32v 0, .var "x"], summary := some "x is positive" }], entry := false,
        source := at_ 100,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "r" (some (.op "Int.Add" [.var "x", i32v (-1)])) (at_ 101)] (.finish (at_ 101))] } },
      { name := "good", inputs := [], outputs := [], throws := none, requires := [], entry := false, source := at_ 102,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" i32 none (at_ 103), .call ["y"] "dec" [i32v 3] (at_ 103),
                    .assert "dec3" (.eq (.var "y") (i32v 2)) none (at_ 104)] (.finish (at_ 105))] } },
      { name := "bad", inputs := [], outputs := [], throws := none, requires := [], entry := false, source := at_ 106,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" i32 none (at_ 107), .call ["y"] "dec" [i32v 0] (at_ 107)] (.finish (at_ 108))] } }] }

/--
info: 104: assertion does not hold
107: x is positive does not hold
-/
#guard_msgs in
#eval run requiresProgram

-- With `dec` inlined, its precondition is still checked at the call, and `good` sees the body.
/--
info: 107: x is positive does not hold
-/
#guard_msgs in
#eval runInlining requiresProgram ["dec"]

-- A precondition may mention a global the body does not use.
meta def requiresGlobal : Wire.Program :=
  { composites := [], constrained := [int32],
    globals := [{ name := "g", ty := i32, init := some (i32v 0), source := at_ 120 }],
    procedures := [
      { name := "f", inputs := [], outputs := [{ name := "r", ty := i32 }], throws := none,
        requires := [{ cond := .op "Int.Lt" [i32v 0, .var "g"], summary := some "g is positive" }], entry := false,
        source := at_ 121,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "r" (some (i32v 1)) (at_ 122)] (.finish (at_ 122))] } },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 123,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" i32 none (at_ 124), .call ["y"] "f" [] (at_ 124),
                    .set "g" (some (i32v 1)) (at_ 125), .call ["y"] "f" [] (at_ 126)] (.finish (at_ 127))] } }] }

/--
info: 124: g is positive does not hold
-/
#guard_msgs in
#eval run requiresGlobal

/--
info: 124: g is positive does not hold
-/
#guard_msgs in
#eval runInlining requiresGlobal ["f"]

-- Lowering matches variables to globals by name, so a parameter or local may not have a global's name.
meta def paramClash : Wire.Program :=
  { composites := [], constrained := [int32],
    globals := [{ name := "g", ty := i32, init := some (i32v 0), source := at_ 110 }],
    procedures := [
      { name := "f", inputs := [{ name := "g", ty := i32 }], outputs := [{ name := "r", ty := i32 }], throws := none,
        requires := [], entry := false, source := at_ 111,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "r" (some (.var "g")) (at_ 112)] (.finish (at_ 112))] } }] }

/--
info: 0: invalid Cortex program: 'f': parameter 'g' has the name of a global
-/
#guard_msgs in
#eval run paramClash

/--
info: 0: invalid Cortex program: 'f': local 'g' has the name of a global
-/
#guard_msgs in
#eval run { paramClash with procedures := paramClash.procedures.map fun q =>
  { q with inputs := [], body := q.body.map fun b => { b with blocks := b.blocks.map fun blk =>
      { blk with cmds := .init "g" i32 (some (i32v 1)) (at_ 112) :: blk.cmds } } } }

-- An initializer may read only the globals declared before it.
meta def orderedInit : Wire.Program :=
  { composites := [], constrained := [int32],
    globals := [{ name := "b", ty := i32, init := some (i32v 2), source := at_ 130 },
                { name := "a", ty := i32, init := some (.op "Int.Add" [.var "b", i32v 1]), source := at_ 131 }],
    procedures := [
      { name := "main", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 132,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.assert "a3" (.eq (.var "a") (i32v 3)) none (at_ 133)] (.finish (at_ 134))] } }] }

#guard_msgs in
#eval run orderedInit

#guard_msgs in
#eval interpret orderedInit

/--
info: 0: invalid Cortex program: global 'a': initializer refers to 'b', which is not a global declared before it
-/
#guard_msgs in
#eval run { orderedInit with globals := orderedInit.globals.reverse }

-- A call that throws assigns none of its results, also when the callee is inlined.
meta def throwingResult (expected : Int) : Wire.Program :=
  { composites := [{ name := "Throwable", extending := [], fields := [] },
                   { name := "Exn", extending := ["Throwable"], fields := [] }],
    constrained := [int32],
    procedures := [
      { name := "f", inputs := [], outputs := [{ name := "r", ty := i32 }], throws := some "Exn", requires := [],
        entry := false, source := at_ 140,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "r" (some (i32v 8)) (at_ 141), .init "x" (.named "Exn") none (at_ 142), .new "x" "Exn" (at_ 142),
                    .throw (.var "x") none (at_ 143)] (.finish (at_ 144))] } },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 145,
        body := some { entry := "b0", handlers := [{ covered := ["b0"], catchType := some "Exn", binder := "e", target := "h", source := at_ 146 }], blocks := [
            blk "b0" [.init "e" (.named "Exn") none (at_ 147), .init "y" i32 (some (i32v 1)) (at_ 147),
                      .call ["y"] "f" [] (at_ 148)] (.finish (at_ 149)),
            blk "h" [.assert "kept" (.eq (.var "y") (i32v expected)) none (at_ 150)] (.finish (at_ 151))] } }] }

#guard_msgs in
#eval runInlining (throwingResult 1) ["f"]

#guard_msgs in
#eval interpret (throwingResult 1)

/--
info: 150: assertion does not hold
-/
#guard_msgs in
#eval runInlining (throwingResult 8) ["f"]

/--
info: 150: assertion does not hold
-/
#guard_msgs in
#eval interpret (throwingResult 8)

-- A failed precondition is reported once: the inlined body has the precondition as a fact.
meta def requiresAssumed : Wire.Program :=
  { composites := [], constrained := [int32],
    procedures := [
      { name := "f", inputs := [{ name := "x", ty := i32 }], outputs := [], throws := none,
        requires := [{ cond := .op "Int.Lt" [i32v 0, .var "x"], summary := some "x is positive" }], entry := false,
        source := at_ 160,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.assert "nonzero" (.op "Bool.Not" [.eq (.var "x") (i32v 0)]) none (at_ 161)] (.finish (at_ 162))] } },
      { name := "caller", inputs := [{ name := "a", ty := i32 }], outputs := [], throws := none, requires := [],
        entry := false, source := at_ 163,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.call [] "f" [.var "a"] (at_ 164)] (.finish (at_ 165))] } }] }

/--
info: 164: x is positive does not hold
-/
#guard_msgs in
#eval runInlining requiresAssumed ["f"]

-- An entry procedure's precondition is assumed, like any procedure's; one over a global is refused.
/--
info: 0: invalid Cortex program: 'main': the precondition of an entry procedure reads global 'g', which starts at its initializer there
-/
#guard_msgs in
#eval run { requiresGlobal with procedures := requiresGlobal.procedures.map fun q =>
  if q.name != "main" then q else
  { q with requires := [{ cond := .op "Int.Le" [i32v 0, .var "g"], summary := none }] } }

meta def entryInputPrecondition : Wire.Program :=
  { composites := [], constrained := [int32],
    procedures := [
      { name := "main", inputs := [{ name := "a", ty := i32 }], outputs := [], throws := none,
        requires := [{ cond := .op "Int.Le" [i32v 0, .var "a"], summary := none }], entry := true, source := at_ 190,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.assert "nonneg" (.op "Int.Le" [i32v 0, .var "a"]) none (at_ 191)] (.finish (at_ 192))] } }] }

#guard_msgs in
#eval run entryInputPrecondition

-- A value of a constrained type over a composite is a reference: a fresh allocation is not it.
meta def constrainedComposite : Wire.Program :=
  { composites := [{ name := "Box", extending := [], fields := [{ name := "v", ty := i32 }] },
                   { name := "Holder", extending := [], fields := [{ name := "b", ty := .named "NB" }] }],
    constrained := [int32, { name := "NB", base := .named "Box", binder := "$v", constraint := .bool true, witness := none }],
    procedures := [
      { name := "mk", inputs := [], outputs := [{ name := "r", ty := .named "NB" }], throws := none, requires := [],
        entry := false, source := at_ 170, body := none },
      { name := "input", inputs := [{ name := "x", ty := .named "NB" }], outputs := [], throws := none, requires := [],
        entry := false, source := at_ 171,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" (.named "Box") none (at_ 172), .new "y" "Box" (at_ 172),
                    .assert "fresh" (.op "Bool.Not" [.eq (.var "x") (.var "y")]) none (at_ 173)] (.finish (at_ 174))] } },
      { name := "fieldRead", inputs := [], outputs := [], throws := none, requires := [],
        entry := false, source := at_ 175,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "h" (.named "Holder") none (at_ 175), .new "h" "Holder" (at_ 175),
                    .init "t" (.named "NB") none (at_ 176), .readField "t" (.var "h") "Holder" "b" (at_ 176),
                    .init "y" (.named "Box") none (at_ 177), .new "y" "Box" (at_ 177),
                    .assert "fresh" (.op "Bool.Not" [.eq (.var "t") (.var "y")]) none (at_ 178)] (.finish (at_ 179))] } },
      { name := "callOut", inputs := [], outputs := [], throws := none, requires := [],
        entry := false, source := at_ 180,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "t" (.named "NB") none (at_ 181), .call ["t"] "mk" [] (at_ 181),
                    .init "y" (.named "Box") none (at_ 182), .new "y" "Box" (at_ 182),
                    .assert "fresh" (.op "Bool.Not" [.eq (.var "t") (.var "y")]) none (at_ 183)] (.finish (at_ 184))] } }] }

#guard_msgs in
#eval run constrainedComposite

end Cortex.WireTest
