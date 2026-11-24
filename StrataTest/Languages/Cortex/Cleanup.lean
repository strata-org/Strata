/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Cortex.CleanupHelpers

/-!
# The Cortex cleanup, end to end

The tests run `Cleanup.pass`, which repeats copy propagation, copy coalescing
and dead-store elimination and then removes the unused declarations. They pin
the cleaned program, check its shape, and compare what the Cortex interpreter
observes before and after.
-/

meta section

namespace Cortex.CleanupTest

open Cortex.CleanupHelpers

def binary (name op : String) : Wire.Procedure :=
  proc name [("a", int), ("b", int)] [("r", int)]
    [blk "b0" [.set "r" (some (.op op [v "a", v "b"])) (at_ 90)] (.finish (at_ 91))]

def throwProc : Wire.Procedure :=
  proc "fail" [] [("r", int)] [blk "b0" [.init "x" (.named "Exn") none (at_ 80), .new "x" "Exn" (at_ 81),
    .throw (v "x") none (at_ 82)] (.finish (at_ 83))]

/-- `a + b * 2` in the shape a stack-machine frontend emits: every push and
pop is a copy. -/
def arith : Wire.Procedure :=
  proc "arith" [("arg0", int), ("arg1", int)] [("result", int)]
    [blk "entry" [decl "l0" 1, decl "s0" 2, decl "l1" 3, decl "s1" 4, decl "s2" 5,
                  .set "l0" (some (v "arg0")) (at_ 6), .set "l1" (some (v "arg1")) (at_ 7)] (.goto "b0" (at_ 8)),
     blk "b0" [.set "s0" (some (v "l0")) (at_ 9), .set "s1" (some (v "l1")) (at_ 10),
               .set "s2" (some (.int 2)) (at_ 11), .call ["s1"] "mul" [v "s1", v "s2"] (at_ 12),
               .call ["s0"] "add" [v "s0", v "s1"] (at_ 13), .set "result" (some (v "s0")) (at_ 14)]
       (.finish (at_ 15))]

/-- An entry with a check that holds and a check that fails. -/
def checks : Wire.Procedure :=
  proc "checks" [] [("r", int)] (entry := true)
    [blk "b0" [decl "t" 20, decl "u" 21, .call ["t"] "arith" [.int 3, .int 4] (at_ 22),
               .set "u" (some (v "t")) (at_ 23),
               .assert "holds" (.eq (v "u") (.int 11)) none (at_ 24),
               .assert "fails" (.eq (v "u") (.int 12)) none (at_ 25),
               .set "r" (some (v "u")) (at_ 26)] (.finish (at_ 27))]

/-- An entry whose handler reads `a` and `x` after the call in `b1` throws. -/
def catching : Wire.Procedure :=
  proc "catching" [] [("r", int)] (entry := true)
    [blk "b0" [decl "a" 30, decl "t" 31, decl "x" 32, .init "e" (.named "Exn") none (at_ 33),
               .set "x" (some (.int 5)) (at_ 34)] (.goto "b1" (at_ 35)),
     blk "b1" [.set "a" (some (.int 1)) (at_ 36), .call ["t"] "fail" [] (at_ 37),
               .set "x" (some (v "t")) (at_ 38), .set "a" (some (.int 2)) (at_ 39)] (.goto "b2" (at_ 40)),
     blk "b2" [.set "r" (some (.op "Int.Add" [v "a", v "x"])) (at_ 41)] (.finish (at_ 42)),
     blk "h" [.set "r" (some (.op "Int.Add" [v "a", v "x"])) (at_ 43)] (.finish (at_ 44))]
    [handler ["b1"] "e" "h"]

/-- An entry that ends in an uncaught exception. -/
def uncaught : Wire.Procedure :=
  proc "uncaught" [] [("r", int)] (entry := true)
    [blk "b0" [decl "t" 50, .set "t" (some (.int 1)) (at_ 51), .call ["r"] "fail" [] (at_ 52)] (.finish (at_ 53))]

def all : Except String UnorderedProgram :=
  program [arith, checks, catching, uncaught, binary "add" "Int.Add", binary "mul" "Int.Mul", throwProc]

/-! `arith` shrinks from 17 lines to 7: the parameters and the literal reach
the calls, the second call writes `result` directly, and four of the five
locals go. In `checks` the copy `u` goes and the two `assert`s read the call's
result `t`; the `assert`s read `t` before `r := t`, so the call keeps writing
to `t`. In `catching` the handler reads `a` and `x`, so `a := 1` and `x := t`
stay and the call keeps writing to `t`. In `uncaught` the dead store and its
local go, and the call stays. -/

/--
info: procedure arith(arg0: int, arg1: int) returns (result: int)
entry:
  var s1: int := 0  @4
  goto b0  @8
b0:
  call s1 := mul(arg1, 2)  @12
  call result := add(arg0, s1)  @13
  finish  @15
procedure checks() returns (r: int)
b0:
  var t: int := 0  @20
  call t := arith(3, 4)  @22
  assert holds: t == 11  @24
  assert fails: t == 12  @25
  r := t  @26
  finish  @27
procedure catching() returns (r: int)
b0:
  var a: int := 0  @30
  var t: int := 0  @31
  var x: int := 0  @32
  var e: Exn  @33
  x := 5  @34
  goto b1  @35
b1:
  a := 1  @36
  call t := fail()  @37
  x := t  @38
  a := 2  @39
  goto b2  @40
b2:
  r := int.add(a, x)  @41
  finish  @42
h:
  r := int.add(a, x)  @43
  finish  @44
handler [b1] catch * as e goto h
procedure uncaught() returns (r: int)
b0:
  call r := fail()  @52
  finish  @53
procedure add(a: int, b: int) returns (r: int)
b0:
  r := int.add(a, b)  @90
  finish  @91
procedure mul(a: int, b: int) returns (r: int)
b0:
  r := int.mul(a, b)  @90
  finish  @91
procedure fail() returns (r: int)
b0:
  var x: Exn  @80
  x := new Exn  @81
  throw x  @82
  finish  @83
-/
#guard_msgs in
#eval showAfter Cleanup.pass all

/-! The interpreter observes the same before and after the cleanup: the same
failed check at the same offset, the same outputs, and the same uncaught
exception at the same offset. -/

/-- Print what the interpreter observes on `prog`, without and with the
cleanup. -/
def observeBoth (prog : Except String UnorderedProgram) : IO Unit :=
  match prog >>= fun prog => (prog, ·) <$> Cleanup.run prog with
  | .error e => IO.println s!"error: {e}"
  | .ok (before, after) => do
    IO.println s!"without cleanup:\n{observe before}"
    IO.println s!"with cleanup:\n{observe after}"

/--
info: without cleanup:
checks: assertion fails  @25; returns r = 11
catching: returns r = 6
uncaught: call does not throw an uncaught 'Exn' fails  @52; returns r = 0
with cleanup:
checks: assertion fails  @25; returns r = 11
catching: returns r = 6
uncaught: call does not throw an uncaught 'Exn' fails  @52; returns r = 0
-/
#guard_msgs in
#eval observeBoth all

/-! A dead division stays through the whole cleanup, so a run that stops at a
division by zero still stops there. -/

/--
info: procedure divides() returns ()
b0:
  var t: int := 0  @2
  t := int.safeDiv(7, 0)  @3
  finish  @5
without cleanup:
divides: stopped
with cleanup:
divides: stopped
-/
#guard_msgs in
#eval do
  let prog := program [proc "divides" [] [] (entry := true)
    [blk "b0" [decl "y" 1, decl "t" 2, .set "t" (some (.op "Int.SafeDiv" [.int 7, v "y"])) (at_ 3),
               .set "t" (some (.int 1)) (at_ 4)] (.finish (at_ 5))]]
  showAfter Cleanup.pass prog
  observeBoth prog

/-! The number of rounds of the repeated passes per procedure. The last round
of each changes nothing. -/

/--
info: arith: 2
checks: 2
catching: 1
uncaught: 2
add: 1
mul: 1
fail: 1
-/
#guard_msgs in
#eval match all with
  | .error e => IO.println s!"error: {e}"
  | .ok prog => for p in prog.procedures do
      IO.println s!"{p.name}: {(Cleanup.cleanupProcedure prog p).2}"

/-! The cleanup leaves a program without bodies, and a body that needs no
cleanup, as they are. -/

/--
info: procedure extern(a: int) returns (r: int)
procedure tidy(a: int) returns (r: int)
b0:
  r := a  @1
  finish  @2
-/
#guard_msgs in
#eval showAfter Cleanup.pass <| program [
  { name := "extern", inputs := [{ name := "a", ty := int }], outputs := [{ name := "r", ty := int }],
    throws := none, requires := [], body := none, entry := false, source := at_ 0 },
  proc "tidy" [("a", int)] [("r", int)] [blk "b0" [.set "r" (some (v "a")) (at_ 1)] (.finish (at_ 2))]]

def rethrow : Wire.Procedure :=
  proc "rethrow" [] [("r", int)]
    [blk "b0" [.init "e" (.named "Exn") none (at_ 60)] (.goto "b1" (at_ 61)),
     blk "b1" [.call ["r"] "fail" [] (at_ 62)] (.finish (at_ 63)),
     blk "h" [.throw (v "e") none (at_ 64)] (.finish (at_ 65))]
    [{ covered := ["b1"], catchType := some "Exn", binder := "e", target := "h", source := at_ 0 }]

/--
info: without cleanup:
callsRethrow: call does not throw an uncaught 'Exn' fails  @71; returns r = 0
with cleanup:
callsRethrow: call does not throw an uncaught 'Exn' fails  @71; returns r = 0
-/
#guard_msgs in
#eval observeBoth <| program [throwProc, rethrow,
  proc "callsRethrow" [] [("r", int)] (entry := true)
    [blk "b0" [.call ["r"] "rethrow" [] (at_ 71)] (.finish (at_ 72))]]

def fAB : Wire.Procedure :=
  proc "fAB" [("c", .bool)] [("r", int)]
    [blk "b0" [] (.condGoto (v "c") "bA" "bB" (at_ 20)),
     blk "bA" [.init "a" (.named "A") none (at_ 21), .new "a" "A" (at_ 22), .throw (v "a") none (at_ 23)]
       (.finish (at_ 24)),
     blk "bB" [.init "b" (.named "B") none (at_ 25), .new "b" "B" (at_ 26), .throw (v "b") none (at_ 27)]
       (.finish (at_ 28))]

def gCatchA : Wire.Procedure :=
  proc "gCatchA" [("c", .bool)] [("r", int)]
    [blk "b0" [.init "e" (.named "A") none (at_ 30)] (.goto "b1" (at_ 30)),
     blk "b1" [.call ["r"] "fAB" [v "c"] (at_ 31)] (.finish (at_ 32)),
     blk "h" [] (.finish (at_ 33))]
    [{ covered := ["b1"], catchType := some "A", binder := "e", target := "h", source := at_ 0 }]

def mainCatchB : Wire.Procedure :=
  proc "mainCatchB" [] [("r", int)] (entry := true)
    [blk "b0" [.init "e" (.named "B") none (at_ 40)] (.goto "b1" (at_ 40)),
     blk "b1" [.call ["r"] "gCatchA" [.bool false] (at_ 41), .assert "after" (.bool false) none (at_ 42)]
       (.finish (at_ 43)),
     blk "h" [.assert "inHandler" (.bool false) none (at_ 44)] (.finish (at_ 45))]
    [{ covered := ["b1"], catchType := some "B", binder := "e", target := "h", source := at_ 0 }]

/--
info: without cleanup:
mainCatchB: assertion fails  @44; returns r = 0
with cleanup:
mainCatchB: assertion fails  @44; returns r = 0
-/
#guard_msgs in
#eval observeBoth <| Wire.Program.toCortex
  { composites := composites ++ [{ name := "A", extending := [], fields := [] },
                                 { name := "B", extending := [], fields := [] }],
    constrained := [], procedures := [fAB, gCatchA, mainCatchB] }

def fB2 : Wire.Procedure :=
  proc "fB2" [] [("r", int)]
    [blk "b0" [.init "b" (.named "B") none (at_ 100), .new "b" "B" (at_ 101), .throw (v "b") none (at_ 102)]
       (.finish (at_ 103))]

def fAB2 : Wire.Procedure :=
  proc "fAB2" [("c", .bool)] [("r", int)]
    [blk "b0" [] (.condGoto (v "c") "bA" "bB" (at_ 110)),
     blk "bA" [.init "a" (.named "A") none (at_ 111), .new "a" "A" (at_ 112), .throw (v "a") none (at_ 113)]
       (.finish (at_ 114)),
     blk "bB" [.call ["r"] "fB2" [] (at_ 115)] (.finish (at_ 116))]

def gCatchA2 : Wire.Procedure :=
  proc "gCatchA2" [("c", .bool)] [("r", int)]
    [blk "b0" [.init "e" (.named "A") none (at_ 120)] (.goto "b1" (at_ 120)),
     blk "b1" [.call ["r"] "fAB2" [v "c"] (at_ 121)] (.finish (at_ 122)),
     blk "h" [] (.finish (at_ 123))]
    [{ covered := ["b1"], catchType := some "A", binder := "e", target := "h", source := at_ 0 }]

def mainCatchB2 : Wire.Procedure :=
  proc "mainCatchB2" [] [("r", int)] (entry := true)
    [blk "b0" [.init "e" (.named "B") none (at_ 130)] (.goto "b1" (at_ 130)),
     blk "b1" [.call ["r"] "gCatchA2" [.bool false] (at_ 131), .assert "after" (.bool false) none (at_ 132)]
       (.finish (at_ 133)),
     blk "h" [.assert "inHandler" (.bool false) none (at_ 134)] (.finish (at_ 135))]
    [{ covered := ["b1"], catchType := some "B", binder := "e", target := "h", source := at_ 0 }]

/--
info: without cleanup:
mainCatchB2: assertion fails  @134; returns r = 0
with cleanup:
mainCatchB2: assertion fails  @134; returns r = 0
-/
#guard_msgs in
#eval observeBoth <| Wire.Program.toCortex
  { composites := composites ++ [{ name := "A", extending := [], fields := [] },
                                 { name := "B", extending := [], fields := [] }],
    constrained := [], procedures := [fB2, fAB2, gCatchA2, mainCatchB2] }

def quiet : Wire.Procedure :=
  proc "quiet" [] [("r", int)]
    [blk "b0" [.set "r" (some (.int 1)) (at_ 140)] (.finish (at_ 141))]

def twoHandlers : Wire.Procedure :=
  proc "twoHandlers" [] [("r", int)]
    [blk "b0" [.init "e" (.named "Exn") none (at_ 142)] (.goto "b1" (at_ 143)),
     blk "b1" [.call ["r"] "quiet" [] (at_ 144)] (.goto "b2" (at_ 145)),
     blk "b2" [.call ["r"] "fail" [] (at_ 146)] (.finish (at_ 147)),
     blk "hA" [] (.finish (at_ 148)),
     blk "hB" [.throw (v "e") none (at_ 149)] (.finish (at_ 150))]
    [{ covered := ["b1"], catchType := some "A", binder := "e", target := "hA", source := at_ 0 },
     { covered := ["b2"], catchType := some "Exn", binder := "e", target := "hB", source := at_ 0 }]

def mainTwoHandlers : Wire.Procedure :=
  proc "mainTwoHandlers" [] [("r", int)] (entry := true)
    [blk "b0" [.init "e" (.named "Exn") none (at_ 70)] (.goto "b1" (at_ 71)),
     blk "b1" [.call ["r"] "twoHandlers" [] (at_ 73), .assert "after" (.bool false) none (at_ 72)]
       (.finish (at_ 76)),
     blk "h" [.assert "inHandler" (.bool false) none (at_ 74)] (.finish (at_ 75))]
    [{ covered := ["b1"], catchType := some "Exn", binder := "e", target := "h", source := at_ 0 }]

/--
info: without cleanup:
mainTwoHandlers: assertion fails  @74; returns r = 0
with cleanup:
mainTwoHandlers: assertion fails  @74; returns r = 0
-/
#guard_msgs in
#eval observeBoth <| Wire.Program.toCortex
  { composites := composites ++ [{ name := "A", extending := [], fields := [] }],
    constrained := [], procedures := [throwProc, quiet, twoHandlers, mainTwoHandlers] }

end Cortex.CleanupTest

end
