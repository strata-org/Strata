/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Cortex.CleanupHelpers

/-!
# Copy propagation on Cortex

Each test prints a small procedure after `CopyPropagation`. The pass rewrites
reads and deletes nothing, so every command is still there, at its offset.
-/

meta section

namespace Cortex.CopyPropagationTest

open Cortex.CleanupHelpers

def show_ (procedures : List Wire.Procedure) : IO Unit :=
  showAfter CopyPropagation.pass (program procedures)

def idProc : Wire.Procedure :=
  proc "id" [("a", int)] [("r", int)] [blk "b0" [.set "r" (some (v "a")) (at_ 90)] (.finish (at_ 91))]

/-! A chain of copies of a local: each read becomes the first source. `t` is
assigned by a call, so it is not a copy of a parameter. -/

/--
info: procedure chain(x: int) returns (r: int)
b0:
  var t: int := 0  @1
  var a: int := 0  @2
  var b: int := 0  @3
  call t := id(x)  @4
  a := t  @5
  b := t  @6
  r := t  @7
  finish  @8
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval show_ [proc "chain" [("x", int)] [("r", int)]
  [blk "b0" [decl "t" 1, decl "a" 2, decl "b" 3, .call ["t"] "id" [v "x"] (at_ 4),
             .set "a" (some (v "t")) (at_ 5), .set "b" (some (v "a")) (at_ 6),
             .set "r" (some (v "b")) (at_ 7)] (.finish (at_ 8))], idProc]

/-! A literal is propagated like a copy, into an `assert`, a call argument and
a compound expression. -/

/--
info: procedure literal() returns (r: int)
b0:
  var a: int := 0  @1
  a := 2  @2
  assert positive: int.gt(2, 0)  @3
  call r := id(2)  @4
  r := int.add(r, 2)  @5
  finish  @6
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval show_ [proc "literal" [] [("r", int)]
  [blk "b0" [decl "a" 1, .set "a" (some (.int 2)) (at_ 2),
             .assert "positive" (.op "Int.Gt" [v "a", .int 0]) none (at_ 3),
             .call ["r"] "id" [v "a"] (at_ 4),
             .set "r" (some (.op "Int.Add" [v "r", v "a"])) (at_ 5)] (.finish (at_ 6))], idProc]

/-! An assignment to the source or to the target ends the fact: `r := a` must
read `a`, which still holds the old `t`, and `s := b` must read the new `b`. -/

/--
info: procedure reassigned(x: int) returns (r: int, s: int)
b0:
  var t: int := 0  @1
  var a: int := 0  @2
  var b: int := 0  @3
  call t := id(x)  @4
  a := t  @5
  b := t  @6
  call t := id(t)  @7
  call b := id(x)  @8
  r := a  @9
  s := b  @10
  finish  @11
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval show_ [proc "reassigned" [("x", int)] [("r", int), ("s", int)]
  [blk "b0" [decl "t" 1, decl "a" 2, decl "b" 3, .call ["t"] "id" [v "x"] (at_ 4),
             .set "a" (some (v "t")) (at_ 5), .set "b" (some (v "t")) (at_ 6),
             .call ["t"] "id" [v "a"] (at_ 7), .call ["b"] "id" [v "x"] (at_ 8),
             .set "r" (some (v "a")) (at_ 9), .set "s" (some (v "b")) (at_ 10)] (.finish (at_ 11))], idProc]

/-! Facts do not cross a block boundary, and a branch condition is rewritten
like any other read. -/

/--
info: procedure blocks(x: int, c: bool) returns (r: int)
b0:
  var t: int := 0  @1
  var a: int := 0  @2
  var d: bool := false  @4
  call t := id(x)  @5
  a := t  @6
  d := c  @7
  if c goto b1 else b2  @8
b1:
  r := a  @9
  finish  @10
b2:
  r := t  @11
  finish  @12
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval show_ [proc "blocks" [("x", int), ("c", .bool)] [("r", int)]
  [blk "b0" [decl "t" 1, decl "a" 2, .init "d" .bool (some (.bool false)) (at_ 4), .call ["t"] "id" [v "x"] (at_ 5),
             .set "a" (some (v "t")) (at_ 6), .set "d" (some (v "c")) (at_ 7)]
     (.condGoto (v "d") "b1" "b2" (at_ 8)),
   blk "b1" [.set "r" (some (v "a")) (at_ 9)] (.finish (at_ 10)),
   blk "b2" [.set "r" (some (v "t")) (at_ 11)] (.finish (at_ 12))], idProc]

/-! A local that is only a copy of a never-assigned input is replaced by the
input in every block. -/

/--
info: procedure parameter(x: int) returns (r: int)
b0:
  var l: int := 0  @1
  l := x  @2
  goto b1  @3
b1:
  r := x  @4
  finish  @5
-/
#guard_msgs in
#eval show_ [proc "parameter" [("x", int)] [("r", int)]
  [blk "b0" [decl "l" 1, .set "l" (some (v "x")) (at_ 2)] (.goto "b1" (at_ 3)),
   blk "b1" [.set "r" (some (v "l")) (at_ 4)] (.finish (at_ 5))]]

/-! The copy of a parameter is not propagated across blocks when the input is
assigned (`assignedInput`), when the local has a second assignment
(`assignedTwice`), when the entry block is a loop head (`loopHead`), or when a
command that may throw precedes the copy (`afterCall`). -/

/--
info: procedure assignedInput(x: int) returns (r: int)
b0:
  var l: int := 0  @1
  l := x  @2
  goto b1  @3
b1:
  x := 1  @4
  r := l  @5
  finish  @6
procedure assignedTwice(x: int) returns (r: int)
b0:
  var l: int := 0  @1
  l := x  @2
  goto b1  @3
b1:
  r := l  @4
  l := 1  @5
  finish  @6
procedure loopHead(x: int, c: bool) returns (r: int)
b0:
  var l: int := x  @1
  if c goto b0 else b1  @2
b1:
  r := l  @3
  finish  @4
procedure afterCall(x: int) returns (r: int)
b0:
  var l: int := 0  @1
  call r := id(x)  @2
  l := x  @3
  goto b1  @4
b1:
  r := l  @5
  finish  @6
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval show_ [
  proc "assignedInput" [("x", int)] [("r", int)]
    [blk "b0" [decl "l" 1, .set "l" (some (v "x")) (at_ 2)] (.goto "b1" (at_ 3)),
     blk "b1" [.set "x" (some (.int 1)) (at_ 4), .set "r" (some (v "l")) (at_ 5)] (.finish (at_ 6))],
  proc "assignedTwice" [("x", int)] [("r", int)]
    [blk "b0" [decl "l" 1, .set "l" (some (v "x")) (at_ 2)] (.goto "b1" (at_ 3)),
     blk "b1" [.set "r" (some (v "l")) (at_ 4), .set "l" (some (.int 1)) (at_ 5)] (.finish (at_ 6))],
  proc "loopHead" [("x", int), ("c", .bool)] [("r", int)]
    [blk "b0" [.init "l" int (some (v "x")) (at_ 1)] (.condGoto (v "c") "b0" "b1" (at_ 2)),
     blk "b1" [.set "r" (some (v "l")) (at_ 3)] (.finish (at_ 4))],
  proc "afterCall" [("x", int)] [("r", int)]
    [blk "b0" [decl "l" 1, .call ["r"] "id" [v "x"] (at_ 2), .set "l" (some (v "x")) (at_ 3)]
       (.goto "b1" (at_ 4)),
     blk "b1" [.set "r" (some (v "l")) (at_ 5)] (.finish (at_ 6))],
  idProc]

/-! A global is neither replaced nor used as a replacement: the call may
assign it. -/

/--
info: procedure global() returns (r: int, s: int)
b0:
  var a: int := 0  @1
  a := g  @2
  g := 5  @3
  call r := id(a)  @4
  r := a  @5
  s := g  @6
  finish  @7
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval showAfter CopyPropagation.pass <|
  (program [proc "global" [] [("r", int), ("s", int)]
    [blk "b0" [decl "a" 1, .set "a" (some (v "g")) (at_ 2), .set "g" (some (.int 5)) (at_ 3),
               .call ["r"] "id" [v "a"] (at_ 4), .set "r" (some (v "a")) (at_ 5),
               .set "s" (some (v "g")) (at_ 6)] (.finish (at_ 7))], idProc]).map
    fun prog => { prog with globals := [(⟨"g", ()⟩, Wire.Ty.toLTy int)] }

end Cortex.CopyPropagationTest

end
