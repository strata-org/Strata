/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Cortex.HandBuilt

/-!
# The `CopyAssignedInputs` pass, on hand-built programs

Each test builds a one-procedure Cortex program by hand, runs
`CopyAssignedInputs` on it, and prints the result as a Core program with CFG
bodies, which has the blocks and the parameters of the Cortex program. Both
routes to Core then type-check the result.
-/

meta section

namespace Cortex.CopyAssignedInputsTest

open Imperative Lambda Cortex.HandBuilt

/-- `report` on `prog` after `Ordering` and `CopyAssignedInputs`, printing the
Core program of the CFG route. -/
def reportCopied (prog : UnorderedProgram) : IO Unit :=
  report (passes := [Ordering.pass, CopyAssignedInputs.pass]) (print := true) prog

/-! ## Where the copies go

The procedures assign their input `x`, so the input becomes `x$in` and the body
starts by copying it into the local `x`. -/

/-! No block transfers to the entry `E`: the copy is prepended to `E`. -/

/--
info: structured: type check ok
program Core;

procedure prepend (x$in : int, out r : int)
cfg E {
  E: {
    var x : int := x$in;
    x := 1;
    r := x;
    return;
  }
};

cfg: type check ok
-/
#guard_msgs in
#eval reportCopied <| mkProg "prepend" [("x", .int)] [("r", .int)] "E"
  [("E", blk [setI "x" 1, setV "r" "x"] fin)]

/-! The entry `E` is a loop header: the copy runs in a new entry block, so that
the loop does not repeat it. -/

/--
info: structured: type check ok
program Core;

procedure entryInLoop (x$in : int, c : bool, out r : int)
cfg $inputCopy {
  $inputCopy: {
    var x : int := x$in;
    goto E;
  }
  E: {
    x := 1;
    r := x;
    branch (c) goto E else goto X;
  }
  X: {
    return;
  }
};

cfg: type check ok
-/
#guard_msgs in
#eval reportCopied <| mkProg "entryInLoop" [("x", .int), ("c", .bool)] [("r", .int)] "E"
  [("E", blk [setI "x" 1, setV "r" "x"] (br "c" "E" "X")), ("X", blk [] fin)]

/-! The label of the new entry block avoids the labels of the body. -/

/--
info: structured: type check ok
program Core;

procedure labelTaken (x$in : int, c : bool, out r : int)
cfg $inputCopy$ {
  $inputCopy$: {
    var x : int := x$in;
    goto $inputCopy;
  }
  $inputCopy: {
    x := 1;
    r := x;
    branch (c) goto $inputCopy else goto X;
  }
  X: {
    return;
  }
};

cfg: type check ok
-/
#guard_msgs in
#eval reportCopied <| mkProg "labelTaken" [("x", .int), ("c", .bool)] [("r", .int)] "$inputCopy"
  [("$inputCopy", blk [setI "x" 1, setV "r" "x"] (br "c" "$inputCopy" "X")), ("X", blk [] fin)]

/-! ## Which inputs are copied

Only an input that the body assigns and that is not an output is copied: `y` is
only read, and `z` is also an output, which a Core body may assign. -/

/--
info: structured: type check ok
program Core;

procedure selective (x$in : int, y : int, inout z : int)
cfg E {
  E: {
    var x : int := x$in;
    x := y;
    z := x;
    return;
  }
};

cfg: type check ok
-/
#guard_msgs in
#eval reportCopied <| mkProg "selective" [("x", .int), ("y", .int), ("z", .int)] [("z", .int)] "E"
  [("E", blk [setV "x" "y", setV "z" "x"] fin)]

/-! ## Name clashes

The renamed input avoids the names in use. -/

/-! Both inputs are assigned, and the second one is named `x$in`: `x` becomes
`x$in$`, and `x$in` becomes `x$in$in`. -/

/--
info: structured: type check ok
program Core;

procedure inputTaken (x$in$ : int, x$in$in : int, out r : int)
cfg E {
  E: {
    var x : int := x$in$;
    var x$in : int := x$in$in;
    x := 1;
    x$in := 2;
    r := x;
    return;
  }
};

cfg: type check ok
-/
#guard_msgs in
#eval reportCopied <| mkProg "inputTaken" [("x", .int), ("x$in", .int)] [("r", .int)] "E"
  [("E", blk [setI "x" 1, setI "x$in" 2, setV "r" "x"] fin)]

/-! The body declares a local named `x$in`. -/

/--
info: structured: type check ok
program Core;

procedure localTaken (x$in$ : int, out r : int)
cfg E {
  E: {
    var x : int := x$in$;
    var x$in : int := 0;
    x := x$in;
    r := x;
    return;
  }
};

cfg: type check ok
-/
#guard_msgs in
#eval reportCopied <| mkProg "localTaken" [("x", .int)] [("r", .int)] "E"
  [("E", blk [initI "x$in" 0, setV "x" "x$in", setV "r" "x"] fin)]

/-! An output is named `x$in`. -/

/--
info: structured: type check ok
program Core;

procedure outputTaken (x$in$ : int, out x$in : int)
cfg E {
  E: {
    var x : int := x$in$;
    x := 1;
    x$in := x;
    return;
  }
};

cfg: type check ok
-/
#guard_msgs in
#eval reportCopied <| mkProg "outputTaken" [("x", .int)] [("x$in", .int)] "E"
  [("E", blk [setI "x" 1, setV "x$in" "x"] fin)]

/-! ## Handlers

The pass refuses a body whose handlers are not lowered: the handler enters the
entry `E` without a transfer. -/

/--
info: CopyAssignedInputs: exception handlers must be lowered before CopyAssignedInputs
-/
#guard_msgs in
#eval reportCopied <| mkProgOfBody "handled" [("x", .int)] []
  { cfg := { entry := "E", blocks := [("E", blk [setI "x" 1] fin)] },
    handlers := [{ covered := ["E"], catchType := none, binder := "e",
                   target := "E", md := .empty }] }

/-! ## Without the pass

Neither route to Core accepts a procedure that assigns an input. -/

/--
info: structured: translation error: procedure 'skipped' assigns its input 'x': the CopyAssignedInputs pass must run before Core
cfg: translation error: procedure 'skipped' assigns its input 'x': the CopyAssignedInputs pass must run before Core
-/
#guard_msgs in
#eval report <| mkProg "skipped" [("x", .int)] [("r", .int)] "E"
  [("E", blk [setI "x" 1, setV "r" "x"] fin)]

end Cortex.CopyAssignedInputsTest

end
