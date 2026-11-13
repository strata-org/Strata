/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Cortex.CleanupHelpers

/-!
# Live variables of Cortex procedure bodies

Each test prints, per block, the variables that are live on entry, live after
the transfer, and live into the handlers that cover the block.
-/

meta section

namespace Cortex.LivenessTest

open Cortex.CleanupHelpers Cortex.Liveness

def showSet (s : VarSet) : String := s!"{s.toList.mergeSort}"

/-- Print the liveness facts of the first procedure of `procedures`. -/
def showLive (procedures : List Wire.Procedure) : IO Unit :=
  match program procedures with
  | .error e => IO.println s!"error: {e}"
  | .ok prog =>
    match prog.procedures.head? >>= fun p => p.body.map (p, ·) with
    | none => IO.println "error: no body"
    | some (p, b) => do
      let info := analyze p b
      for (l, _) in b.cfg.blocks do
        IO.println s!"{l}: in {showSet (info.liveInOf l)} out {showSet (info.liveOutOf l)} handlers {showSet (info.handlerLiveOf l)}"

def throwProc : Wire.Procedure :=
  proc "fail" [] [] [blk "b0" [.init "x" (.named "Exn") none (at_ 80), .new "x" "Exn" (at_ 81),
    .throw (v "x") none (at_ 82)] (.finish (at_ 83))]

/-! The outputs are live at `finish`, so `r` is live out of `b2`. An input
that is read later is live from the entry on, and a loop keeps `i` live around
the back edge. -/

/--
info: b0: in [n, r] out [i, n, r] handlers []
b1: in [i, n, r] out [i, n, r] handlers []
b2: in [r] out [r] handlers []
-/
#guard_msgs in
#eval showLive [proc "loop" [("n", int)] [("r", int)]
  [blk "b0" [decl "i" 1] (.goto "b1" (at_ 2)),
   blk "b1" [.set "i" (some (.op "Int.Add" [v "i", .int 1])) (at_ 3)]
     (.condGoto (.op "Int.Lt" [v "i", v "n"]) "b1" "b2" (at_ 4)),
   blk "b2" [] (.finish (at_ 5))]]

/-! The handler `h` reads `a` and its binder `e`. `a` is live into the handler
that covers `b1`, and so it is live on entry to `b1`, although the block
assigns `a` before its transfer: the call in between may throw. The binder is
assigned on entry to the handler, so it is not live in `b1`. `b2` is not
covered, so nothing is live into a handler there. -/

/--
info: b0: in [] out [a] handlers []
b1: in [a] out [a] handlers [a]
b2: in [a] out [r] handlers []
h: in [a, e] out [r] handlers []
-/
#guard_msgs in
#eval showLive [proc "covered" [] [("r", int)]
  [blk "b0" [decl "a" 1, .init "e" (.named "Exn") none (at_ 2), .init "o" (.named "Exn") none (at_ 3)]
     (.goto "b1" (at_ 4)),
   blk "b1" [.call [] "fail" [] (at_ 5), .set "a" (some (.int 2)) (at_ 6)] (.goto "b2" (at_ 7)),
   blk "b2" [.set "r" (some (v "a")) (at_ 8)] (.finish (at_ 9)),
   blk "h" [.set "o" (some (v "e")) (at_ 10), .set "r" (some (v "a")) (at_ 11)] (.finish (at_ 12))]
  [handler ["b1"] "e" "h"], throwProc]

/-! A block that the handler covers but that has no command that may throw
does not make the handler's variables live on entry to it. -/

/--
info: b0: in [] out [r] handlers [a]
h: in [a] out [r] handlers []
-/
#guard_msgs in
#eval showLive [proc "noThrow" [] [("r", int)]
  [blk "b0" [decl "a" 1, .init "e" (.named "Exn") none (at_ 2), .set "r" (some (.int 1)) (at_ 3)] (.finish (at_ 4)),
   blk "h" [.set "r" (some (v "a")) (at_ 5)] (.finish (at_ 6))]
  [handler ["b0"] "e" "h"]]

/-! An array command reads the variables of its operands and assigns its result. In `b1`
the array `a`, the index `i` and the stored value `x` are read, so they are live on entry;
`n`, `t` and `r` are assigned before they are read, so they are not. `newArray` reads its length
and assigns `a`. -/

/--
info: b0: in [i, k, x] out [a, i, x] handlers []
b1: in [a, i, x] out [r] handlers []
-/
#guard_msgs in
#eval showLive [proc "arrays" [("k", int), ("i", int), ("x", int)] [("r", int)]
  [blk "b0" [.init "a" (.named "Ints") none (at_ 1), decl "n" 2, decl "t" 3,
             .newArray "a" "Ints" (v "k") (at_ 4)] (.goto "b1" (at_ 5)),
   blk "b1" [.writeElem (v "a") (v "i") (v "x") int (at_ 6), .arrayLength "n" (v "a") (at_ 7),
             .readElem "t" (v "a") (v "i") int (at_ 8),
             .set "r" (some (.op "Int.Add" [v "n", v "t"])) (at_ 9)] (.finish (at_ 10))]]

end Cortex.LivenessTest

end
