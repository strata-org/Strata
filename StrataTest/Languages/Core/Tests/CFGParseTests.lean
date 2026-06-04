/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init
import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Core.Verifier
import Strata.SimpleAPI

/-! # Tests for CFG (unstructured) procedure parsing -/

open Strata
open StrataDDM.Elab (parseStrataProgramFromDialect)

private def parseCoreText (input : String) : IO Core.Program := do
  let inputCtx := StrataDDM.Parser.stringInputContext "inline" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[StrataDDM.initDialect, Strata.Core]
  let strataProgram ← parseStrataProgramFromDialect dialects Strata.Core.name inputCtx
  let (program, errors) := Core.getProgram strataProgram inputCtx
  if errors.isEmpty then
    pure program
  else
    throw (IO.userError s!"Core DDM translation errors:\n{String.intercalate "\n" errors.toList}")

private def printCFGProcInfo (prog : Core.Program) : IO Unit := do
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

/-! ## Deterministic CFG with conditional branch -/

/--
info: Procedure: Max
  CFG entry: entry, 4 blocks
  Block 'entry': 0 cmds, branch → then_branch/else_branch
  Block 'then_branch': 1 cmds, goto done
  Block 'else_branch': 1 cmds, goto done
  Block 'done': 0 cmds, return
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
    branch (x >= y) goto then_branch else goto else_branch;
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
  printCFGProcInfo prog

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
  printCFGProcInfo prog

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
    branch (y < n) goto body else goto done;
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
  printCFGProcInfo prog

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
  printCFGProcInfo prog

/-! ## End-to-end: type-checking accepts well-formed CFG procedures -/

/--
info: type-check accepted CFG procedure
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
  | .error dm => IO.println s!"ERROR: type-check rejected CFG procedure: {dm.message}"
  | .ok _ => IO.println "type-check accepted CFG procedure"

/-! ## End-to-end: type-checking accepts Max (branches + assignments) -/

/--
info: type-check accepted Max with CFG body preserved (4 blocks)
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
    branch (x >= y) goto then_branch else goto else_branch;
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
  match Core.typeCheck .quiet prog with
  | .error dm => IO.println s!"ERROR: {dm.message}"
  | .ok prog' =>
    for d in prog'.decls do
      match d with
      | .proc p _ =>
        match p.body with
        | .cfg c =>
          IO.println s!"type-check accepted Max with CFG body preserved ({c.blocks.length} blocks)"
        | .structured ss =>
          IO.println s!"ERROR: body collapsed to .structured with {ss.length} statements"
      | _ => pure ()

/-! ## End-to-end: type-checking accepts CountUp (loop pattern with init) -/

/--
info: type-check accepted CountUp
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
    branch (y < n) goto body else goto done;
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
  match Core.typeCheck .quiet prog with
  | .error dm => IO.println s!"ERROR: {dm.message}"
  | .ok _ => IO.println "type-check accepted CountUp"

/-! ## Error: duplicate block labels -/

/--
info: rejected: Duplicate block labels in CFG
-/
#guard_msgs in
#eval do
  let prog ← parseCoreText "
procedure Bad()
cfg start {
  start: { return; }
  start: { return; }
};
"
  match Core.typeCheck .quiet prog with
  | .error dm =>
    if dm.message.contains "Duplicate block labels" then
      IO.println "rejected: Duplicate block labels in CFG"
    else
      IO.println s!"ERROR: unexpected message: {dm.message}"
  | .ok _ => IO.println "ERROR: expected type-check to fail"

/-! ## Error: unknown target label -/

/--
info: rejected: branches to unknown label
-/
#guard_msgs in
#eval do
  let prog ← parseCoreText "
procedure Bad(out y : int)
cfg start {
  start: {
    y := 0;
    goto nonexistent;
  }
};
"
  match Core.typeCheck .quiet prog with
  | .error dm =>
    if dm.message.contains "branches to unknown label" then
      IO.println "rejected: branches to unknown label"
    else
      IO.println s!"ERROR: unexpected message: {dm.message}"
  | .ok _ => IO.println "ERROR: expected type-check to fail"

/-! ## Error: type mismatch in CFG command -/

/--
info: rejected: type error in CFG command
-/
#guard_msgs in
#eval do
  let prog ← parseCoreText "
procedure Bad(x : bool, out y : int)
cfg start {
  start: {
    y := x;
    return;
  }
};
"
  match Core.typeCheck .quiet prog with
  | .error _ =>
    IO.println "rejected: type error in CFG command"
  | .ok _ => IO.println "ERROR: expected type-check to fail"

/-! ## Error: modification rights violation in CFG -/

/--
info: rejected: modifies disallowed variable
-/
#guard_msgs in
#eval do
  let prog ← parseCoreText "
procedure Bad(x : int)
cfg start {
  start: {
    x := 42;
    return;
  }
};
"
  match Core.typeCheck .quiet prog with
  | .error dm =>
    if dm.message.contains "modifies variables" then
      IO.println "rejected: modifies disallowed variable"
    else
      IO.println s!"ERROR: unexpected message: {dm.message}"
  | .ok _ => IO.println "ERROR: expected type-check to fail"

/-! ## Multiple nondet gotos get distinct condition variables -/

open Std (format) in
private def getTransferCondStr (blk : Imperative.DetBlock String Core.Command Core.Expression)
    : Option String :=
  match blk.transfer with
  | .condGoto cond l1 l2 _ =>
    if l1 != l2 then some (toString (format cond)) else none
  | _ => none

/--
info: nondet condition names are distinct across blocks
-/
#guard_msgs in
#eval do
  let prog ← parseCoreText "
procedure MultiNondet(out y : int)
cfg entry {
  entry: {
    goto a, b;
  }
  a: {
    goto c, d;
  }
  b: {
    y := 1;
    goto done;
  }
  c: {
    y := 2;
    goto done;
  }
  d: {
    y := 3;
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
      match p.body with
      | .cfg cfg =>
        let condNames := cfg.blocks.filterMap fun (pair : String × _) => getTransferCondStr pair.2
        if condNames.length == 2 && condNames.Nodup then
          IO.println "nondet condition names are distinct across blocks"
        else
          IO.println s!"ERROR: expected 2 distinct nondet conditions, got {condNames}"
      | .structured _ => IO.println "ERROR: expected CFG body"
    | _ => pure ()
