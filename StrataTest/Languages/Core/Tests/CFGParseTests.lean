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

/-! ## End-to-end: type-checking rejects CFG procedures

Regression test for PR #1132: the verifier pipeline (which includes type
checking) should reject CFG bodies with a clear diagnostic rather than
silently producing wrong results. The current rejection comes from
`checkModificationRights`, which calls `Body.getStructured` on a CFG body. -/

/--
info: type-check rejected CFG procedure: expected structured body, got CFG
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
  match Core.typeCheck .quiet prog with
  | .error dm => IO.println s!"type-check rejected CFG procedure: {dm.message}"
  | .ok _ => IO.println "ERROR: expected type-check to fail for CFG procedure"

/-! ## End-to-end: parsed CFG body is preserved, not collapsed

Regression test for PR #1132: there was a bug where the procedure body was
always stored as `.structured annotated_body` after type checking, erasing
CFG bodies to `.structured []`. The fix preserves `.cfg` bodies. This test
confirms that after parsing, a CFG procedure's body is `.cfg` (not
`.structured []`), guarding against regression in the parser or DDM layer. -/

/--
info: Procedure: Max
  body.isCfg = true
  body.isStructured = false
  CFG preserved: entry=entry, 4 blocks
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
      IO.println s!"  body.isCfg = {p.body.isCfg}"
      IO.println s!"  body.isStructured = {p.body.isStructured}"
      match p.body with
      | .cfg c =>
        IO.println s!"  CFG preserved: entry={c.entry}, {c.blocks.length} blocks"
      | .structured ss =>
        IO.println s!"  ERROR: body collapsed to .structured with {ss.length} statements"
    | _ => pure ()
