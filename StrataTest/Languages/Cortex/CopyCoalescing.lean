/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Cortex.CleanupHelpers

/-!
# Copy coalescing on Cortex

Each test prints a small procedure after `CopyCoalescing`. The offsets show
that the defining command stays where it was, with its own source location,
and that only the copy is deleted.
-/

meta section

namespace Cortex.CopyCoalescingTest

open Cortex.CleanupHelpers

def show_ (procedures : List Wire.Procedure) : IO Unit :=
  showAfter CopyCoalescing.pass (program procedures)

def idProc : Wire.Procedure :=
  proc "id" [("a", int)] [("r", int)] [blk "b0" [.set "r" (some (v "a")) (at_ 90)] (.finish (at_ 91))]

def throwProc : Wire.Procedure :=
  proc "fail" [] [("r", int)] [blk "b0" [.init "x" (.named "Exn") none (at_ 80), .new "x" "Exn" (at_ 81),
    .throw (v "x") none (at_ 82)] (.finish (at_ 83))]

/-! The result of a call, a `new`, a field read and an `instanceOf` is written
straight to the variable it was copied to. The copies at offsets 6, 8, 11 and
13 are gone, and each defining command keeps its offset. A command between
the two that mentions neither variable does not prevent the rewrite. -/

/--
info: procedure direct(x: int) returns (r: int, s: int, b: bool)
b0:
  var t: int := 0  @1
  var o: Box  @2
  var p: Box  @3
  var c: bool := false  @4
  call r := id(x)  @5
  p := new Box  @7
  p.Box.val := x  @9
  s := p.Box.val  @10
  c := true  @12
  b := p instanceof Box  @14
  finish  @15
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval show_ [proc "direct" [("x", int)] [("r", int), ("s", int), ("b", .bool)]
  [blk "b0" [decl "t" 1, .init "o" (.named "Box") none (at_ 2), .init "p" (.named "Box") none (at_ 3),
             .init "c" .bool (some (.bool false)) (at_ 4),
             .call ["t"] "id" [v "x"] (at_ 5), .set "r" (some (v "t")) (at_ 6),
             .new "o" "Box" (at_ 7), .set "p" (some (v "o")) (at_ 8),
             .writeField (v "p") "Box" "val" (v "x") (at_ 9),
             .readField "t" (v "p") "Box" "val" (at_ 10), .set "s" (some (v "t")) (at_ 11),
             .set "c" (some (.bool true)) (at_ 12),
             .instanceOf "c" (v "p") "Box" (at_ 14), .set "b" (some (v "c")) (at_ 13)] (.finish (at_ 15))],
  idProc]

/-! `x` is live into the handler that covers `b1`. If the call throws, the
handler must see the old `x`, so the call must not write to `x`. -/

/--
info: procedure covered() returns (r: int)
b0:
  var t: int := 0  @1
  var x: int := 0  @2
  var e: Exn  @3
  goto b1  @4
b1:
  call t := fail()  @5
  x := t  @6
  goto b2  @7
b2:
  r := x  @8
  finish  @9
h:
  r := x  @10
  finish  @11
handler [b1] catch * as e goto h
procedure fail() returns (r: int)
b0:
  var x: Exn  @80
  x := new Exn  @81
  throw x  @82
  finish  @83
-/
#guard_msgs in
#eval show_ [proc "covered" [] [("r", int)]
  [blk "b0" [decl "t" 1, decl "x" 2, .init "e" (.named "Exn") none (at_ 3)] (.goto "b1" (at_ 4)),
   blk "b1" [.call ["t"] "fail" [] (at_ 5), .set "x" (some (v "t")) (at_ 6)] (.goto "b2" (at_ 7)),
   blk "b2" [.set "r" (some (v "x")) (at_ 8)] (.finish (at_ 9)),
   blk "h" [.set "r" (some (v "x")) (at_ 10)] (.finish (at_ 11))]
  [handler ["b1"] "e" "h"], throwProc]

/-! The same block when the handler does not read `x`: the rewrite applies. -/

/--
info: procedure coveredDead() returns (r: int)
b0:
  var t: int := 0  @1
  var x: int := 0  @2
  var e: Exn  @3
  goto b1  @4
b1:
  call x := fail()  @5
  goto b2  @7
b2:
  r := x  @8
  finish  @9
h:
  r := 0  @10
  finish  @11
handler [b1] catch * as e goto h
procedure fail() returns (r: int)
b0:
  var x: Exn  @80
  x := new Exn  @81
  throw x  @82
  finish  @83
-/
#guard_msgs in
#eval show_ [proc "coveredDead" [] [("r", int)]
  [blk "b0" [decl "t" 1, decl "x" 2, .init "e" (.named "Exn") none (at_ 3)] (.goto "b1" (at_ 4)),
   blk "b1" [.call ["t"] "fail" [] (at_ 5), .set "x" (some (v "t")) (at_ 6)] (.goto "b2" (at_ 7)),
   blk "b2" [.set "r" (some (v "x")) (at_ 8)] (.finish (at_ 9)),
   blk "h" [.set "r" (some (.int 0)) (at_ 10)] (.finish (at_ 11))]
  [handler ["b1"] "e" "h"], throwProc]

/-! The rewrite does not apply when the source is read after the copy
(`sourceLive`), when a command between the two reads the target
(`targetRead`), when the types differ (`types`), or when the target is an
input (`input`). -/

/--
info: procedure sourceLive(x: int) returns (r: int, s: int)
b0:
  var t: int := 0  @1
  call t := id(x)  @2
  r := t  @3
  s := t  @4
  finish  @5
procedure targetRead(x: int) returns (r: int, s: int)
b0:
  var t: int := 0  @1
  call t := id(x)  @2
  s := r  @3
  r := t  @4
  finish  @5
procedure types(x: int) returns (r: bool)
b0:
  var t: int := 0  @1
  call t := id(x)  @2
  r := t  @3
  finish  @4
procedure input(x: int) returns (r: int)
b0:
  var t: int := 0  @1
  call t := id(x)  @2
  x := t  @3
  r := x  @4
  finish  @5
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval show_ [
  proc "sourceLive" [("x", int)] [("r", int), ("s", int)]
    [blk "b0" [decl "t" 1, .call ["t"] "id" [v "x"] (at_ 2), .set "r" (some (v "t")) (at_ 3),
               .set "s" (some (v "t")) (at_ 4)] (.finish (at_ 5))],
  proc "targetRead" [("x", int)] [("r", int), ("s", int)]
    [blk "b0" [decl "t" 1, .call ["t"] "id" [v "x"] (at_ 2), .set "s" (some (v "r")) (at_ 3),
               .set "r" (some (v "t")) (at_ 4)] (.finish (at_ 5))],
  proc "types" [("x", int)] [("r", .bool)]
    [blk "b0" [decl "t" 1, .call ["t"] "id" [v "x"] (at_ 2), .set "r" (some (v "t")) (at_ 3)] (.finish (at_ 4))],
  proc "input" [("x", int)] [("r", int)]
    [blk "b0" [decl "t" 1, .call ["t"] "id" [v "x"] (at_ 2), .set "x" (some (v "t")) (at_ 3),
               .set "r" (some (v "x")) (at_ 4)] (.finish (at_ 5))],
  idProc]

end Cortex.CopyCoalescingTest

end
