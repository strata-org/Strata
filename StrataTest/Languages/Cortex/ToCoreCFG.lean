/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Cortex.HandBuilt

/-!
# Cortex to unstructured Core, on hand-built programs

Each test builds a one-procedure Cortex program by hand and prints what the
structured route (`ToCore.programToCore`) and the CFG route
(`ToCore.programToCoreCFG`) make of it. Hand-built programs reach control flow
and declaration placements that Laurel does not produce.
-/

meta section

namespace Cortex.ToCoreCFGTest

open Imperative Lambda Cortex.HandBuilt

/-! ## Irreducible control flow

The entry branches into either block of the cycle `A ⇄ B`, so the cycle has two
entries. The structured route cannot rebuild it; the CFG route keeps it. -/

/--
info: structured: translation error: irreducible control flow: edge B → A
program Core;

procedure irreducible (c : bool, out r : int)
cfg E {
  E: {
    branch (c) goto A else goto B;
  }
  A: {
    r := 1;
    goto B;
  }
  B: {
    r := 2;
    branch (c) goto A else goto X;
  }
  X: {
    return;
  }
};

cfg: type check ok
-/
#guard_msgs in
#eval report (print := true) <| mkProg "irreducible" [("c", .bool)] [("r", .int)] "E"
  [("E", blk [] (br "c" "A" "B")), ("A", blk [setI "r" 1] (.goto "B")),
   ("B", blk [setI "r" 2] (br "c" "A" "X")), ("X", blk [] fin)]

/-! ## A declaration in a loop body

Block `B` is on the cycle `H ⇄ B` and declares `t`. The structured route scopes
`t` to the loop body; Core's CFG type checker rejects a declaration on a cycle. -/

/--
info: structured: type check ok
cfg: type check: [loopInit]: a CFG-local is declared in a block that lies on a cycle; a loop-carried declaration would be re-initialized on re-entry.
-/
#guard_msgs in
#eval report <| mkProg "loopInit" [("c", .bool)] [("r", .int)] "E"
  [("E", blk [] (.goto "H")), ("H", blk [] (br "c" "B" "X")),
   ("B", blk [initI "t" 0, setV "r" "t"] (.goto "H")), ("X", blk [] fin)]

/-! ## A dead block

No transfer reaches block `D`, which reads the local `t` of the entry block. The
CFG route maps `D` like any other block, and Core's CFG type checker rejects it,
since an unreachable block has no dominator whose locals it could see.
`PruneUnreachable` drops `D`. -/

def deadBlock : UnorderedProgram := mkProg "dead" [] [("r", .int)] "E"
  [("E", blk [initI "t" 0, setV "r" "t"] fin), ("D", blk [setV "r" "t"] (.goto "E"))]

/--
info: structured: type check ok
program Core;

procedure dead (out r : int)
cfg E {
  E: {
    var t : int := 0;
    r := t;
    return;
  }
  D: {
    r := t;
    goto E;
  }
};

cfg: type check: [r := t] No free variables are allowed here!
Free Variables: [t]
-/
#guard_msgs in
#eval report (print := true) deadBlock

/--
info: structured: type check ok
program Core;

procedure dead (out r : int)
cfg E {
  E: {
    var t : int := 0;
    r := t;
    return;
  }
};

cfg: type check ok
-/
#guard_msgs in
#eval report (passes := [PruneUnreachable.pass, Ordering.pass]) (print := true) deadBlock

/-! `PruneUnreachable` refuses a body whose handlers are not lowered: block `H`
is entered through the handler table only. -/

/--
info: PruneUnreachable: exception handlers must be lowered before PruneUnreachable
-/
#guard_msgs in
#eval report (passes := [PruneUnreachable.pass, Ordering.pass]) <| mkProgOfBody "handled" [] []
  { cfg := { entry := "E", blocks := [("E", blk [] fin), ("H", blk [] fin)] },
    handlers := [{ covered := ["E"], catchType := none, binder := "e",
                   target := "H", md := .empty }] }

end Cortex.ToCoreCFGTest

end
