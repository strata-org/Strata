/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Cortex.CleanupHelpers

/-!
# Unused-variable elimination on Cortex

Each test prints a small procedure after `UnusedVarElim`.
-/

meta section

namespace Cortex.UnusedVarElimTest

open Cortex.CleanupHelpers

def show_ (procedures : List Wire.Procedure) (constrained : List Wire.Constrained := []) : IO Unit :=
  showAfter UnusedVarElim.pass (program procedures constrained)

def throwProc : Wire.Procedure :=
  proc "fail" [] [] [blk "b0" [.init "x" (.named "Exn") none (at_ 80), .new "x" "Exn" (at_ 81),
    .throw (v "x") none (at_ 82)] (.finish (at_ 83))]

/-! `u` and `w` are never mentioned, so their declarations go. `a` is read,
`t` is assigned by a call, and `c` is read by the transfer, so theirs stay. -/

/--
info: procedure unused(x: int) returns (r: int)
b0:
  var a: int := 0  @2
  var t: int := 0  @4
  var c: bool := false  @5
  call t := id(x)  @6
  r := a  @7
  if c goto b0 else b1  @8
b1:
  finish  @9
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval show_ [proc "unused" [("x", int)] [("r", int)]
  [blk "b0" [decl "u" 1, decl "a" 2, .init "w" int none (at_ 3), decl "t" 4,
             .init "c" .bool (some (.bool false)) (at_ 5), .call ["t"] "id" [v "x"] (at_ 6),
             .set "r" (some (v "a")) (at_ 7)] (.condGoto (v "c") "b0" "b1" (at_ 8)),
   blk "b1" [] (.finish (at_ 9))],
  proc "id" [("a", int)] [("r", int)] [blk "b0" [.set "r" (some (v "a")) (at_ 90)] (.finish (at_ 91))]]

/-! A handler binder counts as a mention: nothing reads `e`, but the handler
assigns it. -/

/--
info: procedure binder() returns ()
b0:
  var e: Exn  @1
  call fail()  @2
  finish  @3
h:
  finish  @4
handler [b0] catch * as e goto h
procedure fail() returns ()
b0:
  var x: Exn  @80
  x := new Exn  @81
  throw x  @82
  finish  @83
-/
#guard_msgs in
#eval show_ [proc "binder" [] []
  [blk "b0" [.init "e" (.named "Exn") none (at_ 1), .call [] "fail" [] (at_ 2)] (.finish (at_ 3)),
   blk "h" [] (.finish (at_ 4))]
  [handler ["b0"] "e" "h"], throwProc]

/-! An unused declaration whose initializer has an operator with a
precondition stays: evaluating `Int.SafeDiv(x, y)` checks that `y` is not
zero. The unused `u`, with the total `Int.Add`, goes. -/

/--
info: procedure partial(x: int, y: int) returns ()
b0:
  var t: int := int.safeDiv(x, y)  @1
  finish  @3
-/
#guard_msgs in
#eval show_ [proc "partial" [("x", int), ("y", int)] []
  [blk "b0" [.init "t" int (some (.op "Int.SafeDiv" [v "x", v "y"])) (at_ 1),
             .init "u" int (some (.op "Int.Add" [v "x", v "y"])) (at_ 2)] (.finish (at_ 3))]]

/-! The unused declaration of a variable of a constrained type stays, since
`LowerCTE` checks its initializer. -/

/--
info: procedure constrained() returns ()
b0:
  var n: nat := int.sub(0, 1)  @1
  finish  @2
-/
#guard_msgs in
#eval show_ [proc "constrained" [] []
  [blk "b0" [.init "n" (.named "nat") (some (.op "Int.Sub" [.int 0, .int 1])) (at_ 1)] (.finish (at_ 2))]]
  [{ name := "nat", base := int, binder := "x", constraint := .op "Int.Ge" [v "x", .int 0], witness := some (.int 0) }]

end Cortex.UnusedVarElimTest

end
