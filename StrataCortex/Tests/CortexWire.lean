/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataCortex.Implementation.Pipeline
meta import StrataCortex.Implementation.Interpret
meta import StrataCortex.Implementation.Cli
meta import StrataCortex.Tests.Util.TestCortex
meta import StrataDDM.Util.Ion

open Strata Cortex.Wire
open Cortex.TestCortex (at_ blk noLoc proc)

namespace Cortex.WireTest

meta def int32 : Constrained :=
  { name := "int32", base := .int, binder := "$v",
    constraint := .op "Bool.And" [.op "Int.Le" [.int (-2147483648), .var "$v"], .op "Int.Le" [.var "$v", .int 2147483647]],
    witness := some (.int 0) }

meta def i32 : Ty := .named "int32"

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

/-- Translate `p` to Core, whose procedure bodies are CFGs, and type-check the
Core program. Print which step rejected `p`, or that the type check passed. -/
meta def typeCheck (p : Wire.Program) : IO Unit :=
  match Cortex.checkWire p with
  | .error e => IO.println e
  | .ok () => IO.println "Core type checking succeeded."

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck program

meta def entryProgram : Wire.Program :=
  { composites := [{ name := "Box", extending := [], fields := [{ name := "v", ty := i32 }] }],
    constrained := [int32],
    procedures := [
      { name := "lib", inputs := [], outputs := [{ name := "r", ty := i32 }], throws := none, requires := [], body := none,
        entry := false, source := at_ 40 },
      { name := "libBox", inputs := [], outputs := [{ name := "b", ty := .named "Box" }], throws := none, requires := [],
        body := none, entry := false, source := at_ 40 },
      { name := "run", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 41,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "x" i32 (some (.int 2)) (at_ 42),
                    .set "x" (some (.op "Int.Add" [.var "x", .int 1])) (at_ 43),
                    .assert "ok" (.eq (.var "x") (.int 3)) none (at_ 44),
                    .assert "bad" (.eq (.var "x") (.int 4)) none (at_ 45)] (.finish (at_ 46))] } },
      { name := "callsLib", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 50,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" i32 none (at_ 51), .call ["y"] "lib" [] (at_ 52),
                    .assert "libResult" (.eq (.var "y") (.int 0)) none (at_ 53),
                    .init "b" (.named "Box") none (at_ 54), .call ["b"] "libBox" [] (at_ 55),
                    .writeField (.var "b") "Box" "v" (.int 7) (at_ 56),
                    .init "t" i32 none (at_ 57),
                    .readField "t" (.var "b") "Box" "v" (at_ 57),
                    .assert "written" (.eq (.var "t") (.int 7)) none (at_ 58),
                    .assert "afterCalls" (.eq (.var "t") (.int 8)) none (at_ 59)] (.finish (at_ 60))] } }] }

meta def interpret (p : Wire.Program) : IO Unit :=
  match Cortex.interpretWire p 1000 with
  | .error e => IO.println s!"error: {e}"
  | .ok outcome => do
    for m in outcome.diagnostics do
      IO.println s!"{m.fileRange.range.start.byteIdx}: {m.message}"
    for (name, reason) in outcome.errors do
      IO.println s!"stopped: '{name}': {reason}"

/--
info: 45: assertion does not hold
52: the interpreter fails here: a call to 'lib', which has no body to run
stopped: 'callsLib': a call to 'lib', which has no body to run
-/
#guard_msgs in
#eval interpret entryProgram

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck entryProgram

/-- `p` with every procedure that takes no input marked as an entry. -/
meta def runParameterless (p : Wire.Program) : Wire.Program :=
  { p with procedures := p.procedures.map fun q => { q with entry := q.inputs.isEmpty } }

/-- `p` with exactly the procedures in `names` marked as entries. -/
meta def runOnly (names : List String) (p : Wire.Program) : Wire.Program :=
  { p with procedures := p.procedures.map fun q => { q with entry := names.contains q.name } }

/--
info: 15: assertion does not hold
-/
#guard_msgs in
#eval interpret (runParameterless program)

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
72: call does not throw an uncaught 'Arith' does not hold
stopped: 'overflows': assertion does not hold, at a check with no source location
-/
#guard_msgs in
#eval interpret helperProgram

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck helperProgram

/-- Reads a field through a variable that refers to no object, at `r`. -/
meta def readsNoObject (r : FileRange) : List Cmd :=
  [.init "x" (.named "Box") none r, .init "t" i32 none r, .readField "t" (.var "x") "Box" "v" r]

/-- An interpreter error is also reported where it happened: at the command or transfer that raised it (`deref`),
in a callee too (`viaCallee`), or, when that command has no source location, at the first located call
on the way out (`viaForwarder`). A failed check (`unlocated`) or an uncaught exception (`throwsNowhere`) without a
source location is never dropped, which would end the run with no diagnostic, as a pass: it ends the entry as an
error, once however often it fails. -/
meta def stopsProgram : Wire.Program :=
  { composites := [{ name := "Box", extending := [], fields := [{ name := "v", ty := i32 }] },
                   { name := "Exn", extending := [], fields := [] }],
    constrained := [int32],
    procedures := [
      proc "deref" (at_ 70) (readsNoObject (at_ 73)),
      proc "derefAt" (at_ 76) (entry := false) (readsNoObject (at_ 77)),
      proc "viaCallee" (at_ 78) [.call [] "derefAt" [] (at_ 79)],
      proc "unlocated" (at_ 75)
        [.assert "u1" (.eq (.int 1) (.int 2)) none noLoc, .assert "u2" (.eq (.int 1) (.int 2)) none noLoc],
      proc "throwsNowhere" (at_ 88)
        [.init "e" (.named "Exn") none (at_ 89), .new "e" "Exn" (at_ 89), .throw (.var "e") none noLoc],
      proc "fwd" noLoc (entry := false) (readsNoObject noLoc),
      proc "viaForwarder" (at_ 91) [.call [] "fwd" [] (at_ 92)]] }

/--
info: 73: the interpreter fails here: an expression did not evaluate
77: the interpreter fails here: an expression did not evaluate
92: the interpreter fails here: an expression did not evaluate
stopped: 'deref': an expression did not evaluate
stopped: 'viaCallee': an expression did not evaluate
stopped: 'unlocated': assertion does not hold, at a check with no source location
stopped: 'throwsNowhere': uncaught exception is not thrown does not hold, at a check with no source location
stopped: 'viaForwarder': an expression did not evaluate
-/
#guard_msgs in
#eval interpret stopsProgram

meta def branchesOnInt : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "branchOnInt", inputs := [], outputs := [], throws := none, requires := [], entry := true,
        source := at_ 86, body := some { entry := "b0", handlers := [],
                                         blocks := [blk "b0" [] (.condGoto (.int 1) "b0" "b0" (at_ 87))] } }] }

/--
info: stopped: 'branchOnInt': type error: procedure branchOnInt: expression 1 has type int, expected bool: Impossible to unify int with bool.
-/
#guard_msgs in
#eval interpret branchesOnInt

meta def arityCaller (lhs : List String) (args : List Wire.Expr) : Wire.Program :=
  { helperProgram with procedures := helperProgram.procedures.take 1 ++
    [{ name := "caller", inputs := [], outputs := [], throws := none, requires := [], entry := false,
       source := at_ 84,
       body := some { entry := "b0", handlers := [], blocks := [
         blk "b0" [.init "z" i32 (some (.int 0)) (at_ 85), .call lhs "add" args (at_ 86)] (.finish (at_ 87))] } }] }

/--
info: invalid Cortex program: 'caller': call to 'add' passes 1 arguments, but it takes 2
-/
#guard_msgs in
#eval typeCheck (arityCaller ["z"] [.int 1])

/--
info: invalid Cortex program: 'caller': call to 'add' assigns 0 results, but it returns 1
-/
#guard_msgs in
#eval typeCheck (arityCaller [] [.int 1, .int 2])

meta def assignsInput : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "dec", inputs := [{ name := "x", ty := .int }], outputs := [], throws := none, entry := false,
        source := noLoc, requires := [{ cond := .op "Int.Gt" [.var "x", .int 0], summary := some "x is positive" }],
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "x" (some (.op "Int.Sub" [.var "x", .int 1])) noLoc] (.finish noLoc)] } },
      { name := "caller", inputs := [], outputs := [], throws := none, requires := [], entry := true,
        source := at_ 88,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.call [] "dec" [.int 1] (at_ 89), .call [] "dec" [.int 0] (at_ 90)] (.finish (at_ 91))] } }] }

/--
info: 90: x is positive does not hold
-/
#guard_msgs in
#eval interpret assignsInput

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck assignsInput

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
99: call does not throw an uncaught 'java.lang.ArithmeticException' does not hold
-/
#guard_msgs in
#eval interpret preludeProgram

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck preludeProgram

/-! Globals: an entry procedure starts from the initializers, and sees what the procedures it
calls write. -/

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

-- `main` and `reader` each start from the initializers and run the flag-guarded initializer.
#guard_msgs in
#eval interpret (runOnly ["main", "reader"] globalsProgram)

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck globalsProgram

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
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck entryLabelledGlobalsEntry

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
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck callResultClash

#guard_msgs in
#eval interpret callResultClash

-- `dec` has a precondition, which is checked at each call.
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
info: 107: x is positive does not hold
-/
#guard_msgs in
#eval interpret (runParameterless requiresProgram)

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck requiresProgram

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
#eval interpret requiresGlobal

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck requiresGlobal

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
info: invalid Cortex program: 'f': parameter 'g' has the name of a global
-/
#guard_msgs in
#eval typeCheck paramClash

/--
info: invalid Cortex program: 'f': local 'g' has the name of a global
-/
#guard_msgs in
#eval typeCheck { paramClash with procedures := paramClash.procedures.map fun q =>
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

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck orderedInit

#guard_msgs in
#eval interpret orderedInit

/--
info: invalid Cortex program: global 'a': initializer refers to 'b', which is not a global declared before it
-/
#guard_msgs in
#eval typeCheck { orderedInit with globals := orderedInit.globals.reverse }

-- A call that throws assigns none of its results.
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
#eval interpret (throwingResult 1)

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck (throwingResult 1)

/--
info: 150: assertion does not hold
-/
#guard_msgs in
#eval interpret (throwingResult 8)

-- An entry procedure's precondition over a global is refused.
/--
info: invalid Cortex program: 'main': the precondition of an entry procedure reads global 'g', which starts at its initializer there
-/
#guard_msgs in
#eval typeCheck { requiresGlobal with procedures := requiresGlobal.procedures.map fun q =>
  if q.name != "main" then q else
  { q with requires := [{ cond := .op "Int.Le" [i32v 0, .var "g"], summary := none }] } }

meta def entryInputPrecondition : Wire.Program :=
  { composites := [], constrained := [int32],
    procedures := [
      { name := "main", inputs := [{ name := "a", ty := i32 }], outputs := [], throws := none,
        requires := [{ cond := .op "Int.Le" [i32v 0, .var "a"], summary := none }], entry := true, source := at_ 190,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.assert "nonneg" (.op "Int.Le" [i32v 0, .var "a"]) none (at_ 191)] (.finish (at_ 192))] } }] }

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck entryInputPrecondition

-- The interpreter has no value for the input of an entry procedure, so it stops there.
/--
info: stopped: 'main': an assertion could not be evaluated
-/
#guard_msgs in
#eval interpret entryInputPrecondition

-- A value of a constrained type over a composite is a reference: a fresh allocation is not it.
meta def constrainedComposite : Wire.Program :=
  { composites := [{ name := "Box", extending := [], fields := [{ name := "v", ty := i32 }] },
                   { name := "Holder", extending := [], fields := [{ name := "b", ty := .named "NB" }] }],
    constrained := [int32, { name := "NB", base := .named "Box", binder := "$v", constraint := .bool true, witness := none }],
    procedures := [
      { name := "mk", inputs := [], outputs := [{ name := "r", ty := .named "NB" }], throws := none, requires := [],
        entry := false, source := at_ 170,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.new "r" "Box" (at_ 170)] (.finish (at_ 170))] } },
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

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck constrainedComposite

#guard_msgs in
#eval interpret (runOnly ["fieldRead", "callOut"] constrainedComposite)

-- An entry procedure cannot be called, also one that uses only the heap.
meta def callsEntry : Wire.Program :=
  { composites := [{ name := "Box", extending := [], fields := [{ name := "v", ty := i32 }] }],
    constrained := [int32],
    procedures := [
      { name := "a", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 220,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "b" (.named "Box") none (at_ 221), .new "b" "Box" (at_ 221),
                    .writeField (.var "b") "Box" "v" (i32v 1) (at_ 222)] (.finish (at_ 223))] } },
      { name := "b", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 224,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.call [] "a" [] (at_ 225),
                    .assert "unreached" (.bool false) none (at_ 226)] (.finish (at_ 227))] } }] }

/--
info: error: lowering: EntriesNotCalled: call of 'a': entry procedures cannot be called
-/
#guard_msgs in
#eval interpret callsEntry

/--
info: Cortex lowering failed: EntriesNotCalled: call of 'a': entry procedures cannot be called
-/
#guard_msgs in
#eval typeCheck callsEntry

meta def callsSelected : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "helper", inputs := [], outputs := [], throws := none, requires := [], entry := false, source := at_ 9,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.assert "fails" (.bool false) none (at_ 10)] (.finish (at_ 11))] } },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 12,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.call [] "helper" [] (at_ 13)] (.finish (at_ 14))] } }] }

/--
info: 10: assertion does not hold
-/
#guard_msgs in
#eval match Cortex.Cli.selectWireEntry callsSelected "helper" with
  | .ok p => interpret p
  | .error e => IO.println s!"selectWireEntry: {e}"

meta def selectedRequires (isEntry : Bool) : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "run", inputs := [], outputs := [], throws := none,
        requires := [{ cond := .bool false, summary := none }], entry := isEntry, source := at_ 59,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.assert "fails" (.bool false) none (at_ 60)] (.finish (at_ 61))] } }] }

/--
info: 60: assertion does not hold
-/
#guard_msgs in
#eval interpret (selectedRequires true)

/--
info: 60: assertion does not hold
-/
#guard_msgs in
#eval match Cortex.Cli.selectWireEntry (selectedRequires false) "run" with
  | .ok p => interpret p
  | .error e => IO.println s!"selectWireEntry: {e}"

meta def virtualCallsEntry : Wire.Program :=
  { composites := [{ name := "Base", extending := [], fields := [] },
                   { name := "Box", extending := [], fields := [{ name := "v", ty := i32 }] }],
    constrained := [int32],
    procedures := [
      { name := "Base$get", inputs := [{ name := "this", ty := .named "Base" }], outputs := [{ name := "r", ty := i32 }],
        throws := none, requires := [], entry := true, source := at_ 230,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "b" (.named "Box") none (at_ 231), .new "b" "Box" (at_ 231),
                    .set "r" (some (i32v 1)) (at_ 232)] (.finish (at_ 233))] } },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ 234,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "o" (.named "Base") none (at_ 235), .new "o" "Base" (at_ 235),
                    .init "r" i32 none (at_ 236), .virtualCall ["r"] "Base" "get" [.var "o"] (at_ 236),
                    .assert "unreached" (.bool false) none (at_ 237)] (.finish (at_ 238))] } }] }

/--
info: error: lowering: EntriesNotCalled: call of 'Base$get': entry procedures cannot be called
-/
#guard_msgs in
#eval interpret virtualCallsEntry

/--
info: Cortex lowering failed: EntriesNotCalled: call of 'Base$get': entry procedures cannot be called
-/
#guard_msgs in
#eval typeCheck virtualCallsEntry

/-! ## The `external` field

`external` is optional on the wire: a procedure written without it, as by a front end that
predates the field, is not external. -/

/-- A program with one procedure `ext` without a body, with the extra struct fields `extra`. -/
meta def externalIon (extra : Array (String × Ion.Ion String)) : Ion.Ion String :=
  let pos (n : Int) : Ion.Ion String := .struct #[("byteIdx", .int n)]
  .struct #[("composites", .list #[]), ("constrained", .list #[]),
    ("procedures", .list #[.struct (#[
      ("name", .string "ext"), ("inputs", .list #[]), ("outputs", .list #[]), ("throws", .null),
      ("requires", .list #[]), ("body", .null), ("entry", .bool false),
      ("source", .struct #[("file", .struct #[("_0", .string "T.java")]),
        ("range", .struct #[("start", pos 0), ("stop", pos 1)])])] ++ extra)])]

/-- Whether the procedures of the program that `ion` encodes are external. -/
meta def externals (ion : Ion.Ion String) : IO Unit :=
  match readProgram (Ion.internAndSerialize [ion]) with
  | .error e => IO.println s!"error: {e}"
  | .ok p => IO.println s!"{p.procedures.map (·.external)}"

/-- info: [false] -/
#guard_msgs in
#eval externals (externalIon #[])

/-- info: [true] -/
#guard_msgs in
#eval externals (externalIon #[("external", .bool true)])

/-! ## Postconditions -/

/-- `dec` assigns its input `x`; its postconditions read `x` at entry, so `below`
holds and `wrong` does not. `caller` calls it. -/
meta def ensuresProgram : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "dec", inputs := [{ name := "x", ty := .int }],
        outputs := [{ name := "r", ty := .int }], throws := none, requires := [], entry := false,
        source := at_ 110,
        ensures := [{ label := "below", cond := .op "Int.Lt" [.var "r", .var "x"], summary := none,
                      source := at_ 114 },
                    { label := "wrong", cond := .eq (.var "r") (.var "x"), summary := none,
                      source := at_ 115 }],
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "x" (some (.op "Int.Sub" [.var "x", .int 1])) (at_ 111),
                    .set "r" (some (.var "x")) (at_ 112)] (.finish (at_ 113))] } },
      { name := "caller", inputs := [], outputs := [], throws := none, requires := [],
        entry := true, source := at_ 116,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" .int none (at_ 117),
                    .call ["y"] "dec" [.int 5] (at_ 117)] (.finish (at_ 118))] } }] }

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck ensuresProgram

/-- `half` throws when `x` is `0`, with `r` still `0`, and returns `1` otherwise. Its
postconditions hold only on a normal return: `pos` holds, and `two` does not. `caller`
calls it with `1`. -/
meta def throwingEnsuresProgram : Wire.Program :=
  { composites := [{ name := "Throwable", extending := [], fields := [] },
                   { name := "Arith", extending := ["Throwable"], fields := [] }],
    constrained := [],
    procedures := [
      { name := "half", inputs := [{ name := "x", ty := .int }],
        outputs := [{ name := "r", ty := .int }], throws := some "Arith", requires := [],
        entry := false, source := at_ 120,
        ensures := [{ label := "pos", cond := .op "Int.Gt" [.var "r", .int 0], summary := none,
                      source := at_ 121 },
                    { label := "two", cond := .eq (.var "r") (.int 2), summary := none,
                      source := at_ 122 }],
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "e" (.named "Arith") none noLoc, .set "r" (some (.int 0)) noLoc]
            (.condGoto (.eq (.var "x") (.int 0)) "thr" "ok" noLoc),
          blk "thr" [.new "e" "Arith" noLoc, .throw (.var "e") none noLoc] (.finish noLoc),
          blk "ok" [.set "r" (some (.int 1)) noLoc] (.finish noLoc)] } },
      { name := "caller", inputs := [], outputs := [], throws := none, requires := [],
        entry := true, source := at_ 123,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" .int none (at_ 124),
                    .call ["y"] "half" [.int 1] (at_ 124)] (.finish (at_ 125))] } }] }

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck throwingEnsuresProgram

/-- `dec` returns `x - 1`, which its postcondition `wrong` contradicts, and its
precondition rejects the argument `main` passes. `main` ends with a postcondition that is
false. -/
meta def contractProgram : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "dec", inputs := [{ name := "x", ty := .int }],
        outputs := [{ name := "r", ty := .int }], throws := none, entry := false,
        source := at_ 130,
        requires := [{ cond := .op "Int.Le" [.int 0, .var "x"],
                       summary := some "x is not negative" }],
        ensures := [{ label := "wrong", cond := .eq (.var "r") (.var "x"),
                      summary := some "dec keeps its input", source := at_ 132 }],
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "r" (some (.op "Int.Sub" [.var "x", .int 1])) (at_ 133)]
            (.finish (at_ 134))] } },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [],
        entry := true, source := at_ 140,
        ensures := [{ label := "never", cond := .bool false, summary := some "main returns well",
                      source := at_ 141 }],
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "t" .int (some (.int (-1))) (at_ 142),
                    .init "u" .int none (at_ 143),
                    .call ["u"] "dec" [.var "t"] (at_ 144)] (.finish (at_ 145))] } }] }

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck contractProgram

/-- `lib` has no body and a postcondition over its output. -/
meta def bodilessEnsures : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "lib", inputs := [], outputs := [{ name := "r", ty := .int }], throws := none,
        requires := [], body := none, entry := false, source := at_ 150,
        ensures := [{ label := "positive", cond := .op "Int.Lt" [.int 0, .var "r"],
                      summary := some "lib returns a positive number", source := at_ 151 }] },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [],
        entry := true, source := at_ 152,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" .int none (at_ 153),
                    .call ["y"] "lib" [] (at_ 153)] (.finish (at_ 154))] } }] }

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck bodilessEnsures

/-- `inc` has no body and its postcondition relates its result to its argument. -/
meta def bodilessEnsuresInc : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "inc", inputs := [{ name := "x", ty := .int }],
        outputs := [{ name := "r", ty := .int }], throws := none, requires := [], body := none,
        entry := false, source := at_ 160,
        ensures := [{ label := "successor", summary := some "inc returns x+1",
                      cond := .eq (.var "r") (.op "Int.Add" [.var "x", .int 1]),
                      source := at_ 161 }] },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [],
        entry := true, source := at_ 162,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" .int none (at_ 163),
                    .call ["y"] "inc" [.int 4] (at_ 163)] (.finish (at_ 164))] } }] }

/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck bodilessEnsuresInc

/-- The label and outcome of each obligation of the Core program that the wire program `p`
lowers to, verified by symbolic execution. -/
meta def verifyWire (p : Wire.Program) : IO Unit := do
  let m ← IO.ofExcept ((wireToCortex p).mapError (s!"invalid Cortex program: {·}"))
  let core ← IO.ofExcept ((toCoreProgram m).mapError (s!"Cortex lowering failed: {·}"))
  let opts := { Core.VerifyOptions.quiet with symExec := some .default }
  let rs ← EIO.toIO (fun e => IO.Error.userError (toString e)) (Core.verifyProgram core opts)
  IO.println s!"obligations: {rs.toList.map (·.obligation.label)}"
  for r in rs do IO.println s!"{r.obligation.label}: {r.formatOutcome}"

-- A procedure without a body is abstract in Core: its postconditions are its contract, assumed
-- at each call and never checked, so `lib`'s `positive` gives no obligation.
/-- info: obligations: [] -/
#guard_msgs in
#eval verifyWire bodilessEnsures

/-- `bodilessEnsuresInc` with `main` asserting `five`, which follows from `inc`'s contract. -/
meta def bodilessIncFive : Wire.Program :=
  { bodilessEnsuresInc with procedures := bodilessEnsuresInc.procedures.map fun q =>
    if q.name != "main" then q else
    { q with body := some { entry := "b0", handlers := [], blocks := [
      blk "b0" [.init "y" .int none (at_ 163), .call ["y"] "inc" [.int 4] (at_ 163),
                .assert "five" (.eq (.var "y") (.int 5)) none (at_ 165)] (.finish (at_ 164))] } } }

-- The call to the bodiless `inc` assumes `successor`, so `five` holds, and `successor` itself
-- gives no obligation.
/--
info: obligations: [five]
five: ✅ pass
-/
#guard_msgs in
#eval verifyWire bodilessIncFive

-- An entry procedure's postcondition over a global is refused, as its precondition is.
/--
info: invalid Cortex program: 'main': the postcondition of an entry procedure reads global 'g', which is a local of its body there
-/
#guard_msgs in
#eval typeCheck { requiresGlobal with procedures := requiresGlobal.procedures.map fun q =>
  if q.name != "main" then q else
  { q with ensures := [{ label := "gPositive", cond := .op "Int.Lt" [i32v 0, .var "g"],
                         summary := none, source := at_ 129 }] } }

/--
info: invalid Cortex program: 'main': the postcondition of an entry procedure reads the entry value of global 'g', which is a local of its body there
-/
#guard_msgs in
#eval typeCheck { requiresGlobal with procedures := requiresGlobal.procedures.map fun q =>
  if q.name != "main" then q else
  { q with ensures := [{ label := "gKept", cond := .eq (.var "old g") (i32v 0),
                         summary := none, source := at_ 130 }] } }

-- Only a global has an entry value: a postcondition may not read `old` of a parameter.
meta def oldParam : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "f", inputs := [{ name := "x", ty := .int }],
        outputs := [{ name := "r", ty := .int }], throws := none, requires := [],
        entry := false, source := at_ 170,
        ensures := [{ label := "kept", cond := .eq (.var "r") (.var "old x"), summary := none,
                      source := at_ 171 }],
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.set "r" (some (.var "x")) (at_ 172)] (.finish (at_ 173))] } }] }

/--
info: invalid Cortex program: 'f': the postcondition reads the entry value of 'x', but only a global has one
-/
#guard_msgs in
#eval typeCheck oldParam

/-- `f`'s postcondition reads `v`. A name that is neither a parameter nor a global, such as
a misspelled one or a local of the body, is out of scope there and refused. -/
meta def postScope (v : String) : Wire.Program :=
  { composites := [], constrained := [],
    procedures := [
      { name := "f", inputs := [{ name := "x", ty := .int }],
        outputs := [{ name := "r", ty := .int }], throws := none, requires := [],
        entry := false, source := at_ 180,
        ensures := [{ label := "bound", cond := .op "Int.Le" [.var v, .var "r"], summary := none,
                      source := at_ 181 }],
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "t" .int (some (.int 0)) (at_ 182), .set "r" (some (.var "x")) (at_ 182)]
            (.finish (at_ 183))] } },
      { name := "main", inputs := [], outputs := [], throws := none, requires := [],
        entry := true, source := at_ 184,
        body := some { entry := "b0", handlers := [], blocks := [
          blk "b0" [.init "y" .int none (at_ 185), .call ["y"] "f" [.int 4] (at_ 185)]
            (.finish (at_ 186))] } }] }

/--
info: invalid Cortex program: 'f': the postcondition reads 'typo', which is not a parameter or a global
-/
#guard_msgs in
#eval typeCheck (postScope "typo")

/--
info: invalid Cortex program: 'f': the postcondition reads 't', which is not a parameter or a global
-/
#guard_msgs in
#eval typeCheck (postScope "t")

-- The same postcondition over the input is in scope.
/--
info: Core type checking succeeded.
-/
#guard_msgs in
#eval typeCheck (postScope "x")

end Cortex.WireTest
