/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Cortex.CleanupHelpers

/-!
# Dead-store elimination on Cortex

Each test prints a small procedure after `DeadStoreElim`. The offsets show
which commands were deleted and that the others kept their source locations.
-/

meta section

namespace Cortex.DeadStoreElimTest

open Cortex.CleanupHelpers

def show_ (procedures : List Wire.Procedure) (constrained : List Wire.Constrained := []) : IO Unit :=
  showAfter DeadStoreElim.pass (program procedures constrained)

def idProc : Wire.Procedure :=
  proc "id" [("a", int)] [("r", int)] [blk "b0" [.set "r" (some (v "a")) (at_ 90)] (.finish (at_ 91))]

/-- A procedure that always throws. -/
def throwProc : Wire.Procedure :=
  proc "fail" [] [] [blk "b0" [.init "x" (.named "Exn") none (at_ 80), .new "x" "Exn" (at_ 81),
    .throw (v "x") none (at_ 82)] (.finish (at_ 83))]

/-! The stores at offsets 3 and 4 are overwritten before `a` is read, and the
havoc at offset 7 and the self-copy at offset 8 are dead too. The store to the
output `r` is live at `finish`. -/

/--
info: procedure dead(x: int) returns (r: int)
b0:
  var a: int := 0  @1
  var b: int := 0  @2
  a := x  @5
  r := a  @6
  finish  @9
-/
#guard_msgs in
#eval show_ [proc "dead" [("x", int)] [("r", int)]
  [blk "b0" [decl "a" 1, decl "b" 2, .set "a" (some (.int 1)) (at_ 3), .set "a" none (at_ 4),
             .set "a" (some (v "x")) (at_ 5), .set "r" (some (v "a")) (at_ 6),
             .set "b" none (at_ 7), .set "r" (some (v "r")) (at_ 8)] (.finish (at_ 9))]]

/-! A store that one of the branches reads is live (`a := 1` and `r := 5`),
and so is a store that only a later loop iteration reads (`i`). Nothing reads
`j`, so the store to it goes. -/

/--
info: procedure branches(c: bool) returns (r: int)
b0:
  var a: int := 0  @1
  var i: int := 0  @2
  var j: int := 0  @11
  a := 1  @3
  r := 5  @4
  if c goto b1 else b2  @5
b1:
  r := a  @6
  i := int.add(i, 1)  @7
  if c goto b1 else b2  @9
b2:
  finish  @10
-/
#guard_msgs in
#eval show_ [proc "branches" [("c", .bool)] [("r", int)]
  [blk "b0" [decl "a" 1, decl "i" 2, decl "j" 11, .set "a" (some (.int 1)) (at_ 3), .set "r" (some (.int 5)) (at_ 4)]
     (.condGoto (v "c") "b1" "b2" (at_ 5)),
   blk "b1" [.set "r" (some (v "a")) (at_ 6), .set "i" (some (.op "Int.Add" [v "i", .int 1])) (at_ 7),
             .set "j" (some (v "i")) (at_ 8)]
     (.condGoto (v "c") "b1" "b2" (at_ 9)),
   blk "b2" [] (.finish (at_ 10))]]

/-! `b1` is covered by a handler that reads `a`. The store `a := 1` is
overwritten before the block ends, but the call after it may throw, so the
handler can observe it and it stays. The store `b := 1` stays for the same
reason. `c` is not read by the handler, so `c := 1` goes. -/

/--
info: procedure covered() returns (r: int)
b0:
  var a: int := 0  @1
  var b: int := 0  @2
  var c: int := 0  @3
  var e: Exn  @4
  goto b1  @5
b1:
  a := 1  @6
  b := 1  @7
  call fail()  @9
  a := 2  @10
  goto b2  @11
b2:
  r := a  @12
  finish  @13
h:
  r := int.add(a, b)  @14
  finish  @15
handler [b1] catch * as e goto h
procedure fail() returns ()
b0:
  var x: Exn  @80
  x := new Exn  @81
  throw x  @82
  finish  @83
-/
#guard_msgs in
#eval show_ [proc "covered" [] [("r", int)]
  [blk "b0" [decl "a" 1, decl "b" 2, decl "c" 3, .init "e" (.named "Exn") none (at_ 4)] (.goto "b1" (at_ 5)),
   blk "b1" [.set "a" (some (.int 1)) (at_ 6), .set "b" (some (.int 1)) (at_ 7), .set "c" (some (.int 1)) (at_ 8),
             .call [] "fail" [] (at_ 9), .set "a" (some (.int 2)) (at_ 10)] (.goto "b2" (at_ 11)),
   blk "b2" [.set "r" (some (v "a")) (at_ 12)] (.finish (at_ 13)),
   blk "h" [.set "r" (some (.op "Int.Add" [v "a", v "b"])) (at_ 14)] (.finish (at_ 15))]
  [handler ["b1"] "e" "h"], throwProc]

/-! The same block without a command that may throw between the two stores:
the handler cannot observe `a := 1`, so it goes. Without a handler, the call
does not keep it either. -/

/--
info: procedure coveredNoThrow() returns (r: int)
b0:
  var a: int := 0  @1
  var e: Exn  @2
  goto b1  @3
b1:
  a := 2  @5
  call fail()  @6
  goto b2  @7
b2:
  r := a  @8
  finish  @9
h:
  r := a  @10
  finish  @11
handler [b1] catch * as e goto h
procedure uncovered() returns (r: int)
b0:
  var a: int := 0  @1
  call fail()  @3
  a := 2  @4
  r := a  @5
  finish  @6
procedure fail() returns ()
b0:
  var x: Exn  @80
  x := new Exn  @81
  throw x  @82
  finish  @83
-/
#guard_msgs in
#eval show_ [proc "coveredNoThrow" [] [("r", int)]
  [blk "b0" [decl "a" 1, .init "e" (.named "Exn") none (at_ 2)] (.goto "b1" (at_ 3)),
   blk "b1" [.set "a" (some (.int 1)) (at_ 4), .set "a" (some (.int 2)) (at_ 5),
             .call [] "fail" [] (at_ 6)] (.goto "b2" (at_ 7)),
   blk "b2" [.set "r" (some (v "a")) (at_ 8)] (.finish (at_ 9)),
   blk "h" [.set "r" (some (v "a")) (at_ 10)] (.finish (at_ 11))]
  [handler ["b1"] "e" "h"],
  proc "uncovered" [] [("r", int)]
  [blk "b0" [decl "a" 1, .set "a" (some (.int 1)) (at_ 2), .call [] "fail" [] (at_ 3),
             .set "a" (some (.int 2)) (at_ 4), .set "r" (some (v "a")) (at_ 5)] (.finish (at_ 6))],
  throwProc]

/-! Only `set` commands are deleted. A call, a `new`, a field read, an
`instanceOf`, a field write, an `assert` and an `assume` stay even when their
result is dead, and so does a declaration. -/

/--
info: procedure effects(x: int) returns ()
b0:
  var t: int := 0  @1
  var o: Box  @2
  var c: bool := false  @3
  call t := id(x)  @4
  o := new Box  @5
  o.Box.val := x  @6
  t := o.Box.val  @7
  c := o instanceof Box  @8
  assert positive: int.gt(x, 0)  @9
  assume positive: int.gt(x, 0)  @10
  finish  @11
procedure id(a: int) returns (r: int)
b0:
  r := a  @90
  finish  @91
-/
#guard_msgs in
#eval show_ [proc "effects" [("x", int)] []
  [blk "b0" [decl "t" 1, .init "o" (.named "Box") none (at_ 2), .init "c" .bool (some (.bool false)) (at_ 3),
             .call ["t"] "id" [v "x"] (at_ 4), .new "o" "Box" (at_ 5),
             .writeField (v "o") "Box" "val" (v "x") (at_ 6), .readField "t" (v "o") "Box" "val" (at_ 7),
             .instanceOf "c" (v "o") "Box" (at_ 8),
             .assert "positive" (.op "Int.Gt" [v "x", .int 0]) none (at_ 9),
             .assume "positive" (.op "Int.Gt" [v "x", .int 0]) (at_ 10)] (.finish (at_ 11))], idProc]

/-! A dead store whose right-hand side has an operator with a precondition
stays: evaluating `Int.SafeDiv(x, y)` checks that `y` is not zero. The dead
store at offset 4 uses the total `Int.Add`, so it goes. -/

/--
info: procedure partial(x: int, y: int) returns ()
b0:
  var t: int := 0  @1
  t := int.safeDiv(x, y)  @2
  t := int.add(1, int.safeMod(x, y))  @3
  finish  @5
-/
#guard_msgs in
#eval show_ [proc "partial" [("x", int), ("y", int)] []
  [blk "b0" [decl "t" 1, .set "t" (some (.op "Int.SafeDiv" [v "x", v "y"])) (at_ 2),
             .set "t" (some (.op "Int.Add" [.int 1, .op "Int.SafeMod" [v "x", v "y"]])) (at_ 3),
             .set "t" (some (.op "Int.Add" [v "x", v "y"])) (at_ 4)] (.finish (at_ 5))]]

/-! A dead store to a variable of a constrained type stays, since `LowerCTE`
checks the stored value. -/

/--
info: procedure constrained() returns ()
b0:
  var n: nat := 0  @1
  n := 1  @2
  finish  @4
-/
#guard_msgs in
#eval show_ [proc "constrained" [] []
  [blk "b0" [.init "n" (.named "nat") (some (.int 0)) (at_ 1), .set "n" (some (.int 1)) (at_ 2)]
     (.finish (at_ 4))]]
  [{ name := "nat", base := int, binder := "x", constraint := .op "Int.Ge" [v "x", .int 0], witness := some (.int 0) }]

/-! A dead store to a global stays, since the callers read the global. -/

/--
info: procedure global() returns ()
b0:
  g := 1  @1
  finish  @2
-/
#guard_msgs in
#eval showAfter DeadStoreElim.pass <|
  (program [proc "global" [] [] [blk "b0" [.set "g" (some (.int 1)) (at_ 1)] (.finish (at_ 2))]]).map
    fun prog => { prog with globals := [(⟨"g", ()⟩, Wire.Ty.toLTy int)] }

end Cortex.DeadStoreElimTest

end
