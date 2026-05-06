/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Core.Verifier
import Strata.SimpleAPI

/-! # Tests for CFG (unstructured) procedure parsing -/

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

private def parseCoreText (input : String) : IO Core.Program := do
  let inputCtx := Strata.Parser.stringInputContext "inline" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Strata.Core]
  let strataProgram ← parseStrataProgramFromDialect dialects Strata.Core.name inputCtx
  match genericToCore strataProgram with
  | .ok program => pure program
  | .error msg => throw (IO.userError msg)

/-! ## Deterministic CFG with conditional branch -/

/--
info: Procedure: Max
  CFG entry: entry, 4 blocks
  Block 'entry': 0 cmds
  Block 'then_branch': 1 cmds
  Block 'else_branch': 1 cmds
  Block 'done': 0 cmds
-/
#guard_msgs in
#eval do
  let prog ← parseCoreText "
procedure Max(x : int, y : int, out m : int)
spec {
  ensures (m >= x);
  ensures (m >= y);
}
cfg entry {
  entry: {
    branch (x >= y) goto then_branch else else_branch;
  }
  then_branch: {
    m := x;
    goto done;
  }
  else_branch: {
    m := y;
    goto done;
  }
  done: {
    return;
  }
};
"
  for d in prog.decls do
    match d with
    | .proc p _ =>
      IO.println s!"Procedure: {Core.CoreIdent.toPretty p.header.name}"
      match p.body with
      | .cfg c =>
        IO.println s!"  CFG entry: {c.entry}, {c.blocks.length} blocks"
        for (lbl, blk) in c.blocks do
          IO.println s!"  Block '{lbl}': {blk.cmds.length} cmds"
      | .structured _ => IO.println "  ERROR: expected CFG body"
    | _ => pure ()

/-! ## Nondeterministic CFG with multi-target goto -/

/--
info: Procedure: NondetChoice
  CFG entry: entry, 4 blocks
  Block 'entry': 0 cmds, branch → left/right
  Block 'left': 1 cmds, goto done
  Block 'right': 1 cmds, goto done
  Block 'done': 0 cmds, return
-/
#guard_msgs in
#eval do
  let prog ← parseCoreText "
procedure NondetChoice(out y : int)
cfg entry {
  entry: {
    goto left, right;
  }
  left: {
    y := 1;
    goto done;
  }
  right: {
    y := 2;
    goto done;
  }
  done: {
    return;
  }
};
"
  for d in prog.decls do
    match d with
    | .proc p _ =>
      IO.println s!"Procedure: {Core.CoreIdent.toPretty p.header.name}"
      match p.body with
      | .cfg c =>
        IO.println s!"  CFG entry: {c.entry}, {c.blocks.length} blocks"
        for (lbl, blk) in c.blocks do
          let transferDesc := match blk.transfer with
            | .condGoto _ l1 l2 _ => if l1 == l2 then s!"goto {l1}" else s!"branch → {l1}/{l2}"
            | .finish _ => "return"
          IO.println s!"  Block '{lbl}': {blk.cmds.length} cmds, {transferDesc}"
      | .structured _ => IO.println "  ERROR: expected CFG body"
    | _ => pure ()

/-! ## CFG loop pattern -/

/--
info: Procedure: CountUp
  CFG entry: entry, 4 blocks
  Block 'entry': 1 cmds, goto loop
  Block 'loop': 0 cmds, branch → body/done
  Block 'body': 1 cmds, goto loop
  Block 'done': 0 cmds, return
-/
#guard_msgs in
#eval do
  let prog ← parseCoreText "
procedure CountUp(n : int, out y : int)
spec {
  requires (n >= 0);
}
cfg entry {
  entry: {
    y := 0;
    goto loop;
  }
  loop: {
    branch (y < n) goto body else done;
  }
  body: {
    y := y + 1;
    goto loop;
  }
  done: {
    return;
  }
};
"
  for d in prog.decls do
    match d with
    | .proc p _ =>
      IO.println s!"Procedure: {Core.CoreIdent.toPretty p.header.name}"
      match p.body with
      | .cfg c =>
        IO.println s!"  CFG entry: {c.entry}, {c.blocks.length} blocks"
        for (lbl, blk) in c.blocks do
          let transferDesc := match blk.transfer with
            | .condGoto _ l1 l2 _ => if l1 == l2 then s!"goto {l1}" else s!"branch → {l1}/{l2}"
            | .finish _ => "return"
          IO.println s!"  Block '{lbl}': {blk.cmds.length} cmds, {transferDesc}"
      | .structured _ => IO.println "  ERROR: expected CFG body"
    | _ => pure ()

/-! ## Empty block (just a transfer) -/

/--
info: Procedure: Trivial
  CFG entry: start, 1 blocks
  Block 'start': 0 cmds, return
-/
#guard_msgs in
#eval do
  let prog ← parseCoreText "
procedure Trivial()
cfg start {
  start: {
    return;
  }
};
"
  for d in prog.decls do
    match d with
    | .proc p _ =>
      IO.println s!"Procedure: {Core.CoreIdent.toPretty p.header.name}"
      match p.body with
      | .cfg c =>
        IO.println s!"  CFG entry: {c.entry}, {c.blocks.length} blocks"
        for (lbl, blk) in c.blocks do
          let transferDesc := match blk.transfer with
            | .condGoto _ l1 l2 _ => if l1 == l2 then s!"goto {l1}" else s!"branch → {l1}/{l2}"
            | .finish _ => "return"
          IO.println s!"  Block '{lbl}': {blk.cmds.length} cmds, {transferDesc}"
      | .structured _ => IO.println "  ERROR: expected CFG body"
    | _ => pure ()
