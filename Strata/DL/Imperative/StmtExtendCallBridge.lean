/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.CmdCallFormals

/-! # A call-free bridge between extended and base Imperative statements

For any expression language `P`, the extended command layer `CmdExt P` adds a
procedure `call` on top of the base command `Cmd P`.  When a program makes no
calls, its extended statements `Imperative.Stmt P (CmdExt P)` are exactly the
base imperative statements `Imperative.Stmt P (Cmd P)` with each command wrapped
in `CmdExt.cmd`.

This module provides the *definitions* that make that observation precise and
reusable, generically over `P`; their properties (inversion, round trips,
injectivity, analysis commutation, and the native event-step/star correspondence)
live in `Strata.DL.Imperative.StmtExtendCallBridgeProps`.  Everything here is
purely structural, so no expression type classes are required.

The current consumer is `Core.NondetElim.overapproximatesTraces`.
`NondetElim`'s generic correctness proof operates on the base command language,
while Strata Core uses `CmdExt` to add procedure calls. The bridge lets the Core
proof project its call-free source to base commands, apply the generic proof,
and embed the result back without duplicating the structural traversal.

* `embedStmt` / `embedStmts` / `embedConfig` inject base statements and
  configurations into the extended dialect by wrapping every command with
  `CmdExt.cmd`.  The injection is total and structure-preserving.
* `embedCFG` / `embedCFGConfig` do the same for deterministic CFGs and their
  small-step configurations.
* `projectStmt` / `projectStmts` recover the base statements from an extended
  statement, returning `none` exactly when a `call` is present.

No trace information is discarded by the bridge: `embedConfig` preserves the
command carried by each `.cmd`, so the emitted event of every command — and
hence the whole trace — is identical on both sides.

A dialect such as Strata Core obtains this bridge at its own expression type by
specializing these generic definitions and theorems. -/

namespace Imperative

open Imperative

public section

variable {P : PureExpr}

/-! ## Embedding base statements into the extended dialect -/

/-- Embed a base command into an extended command by marking it as not-a-call. -/
@[expose] def embedCommand (c : Cmd P) : CmdExt P := CmdExt.cmd c

/-- Embed a base deterministic block into an extended one by wrapping every body
command with `CmdExt.cmd`. -/
@[expose] def embedDetBlock (b : DetBlock String (Cmd P) P) :
    DetBlock String (CmdExt P) P :=
  { cmds := b.cmds.map embedCommand, transfer := b.transfer }

/-- Embed a base CFG into an extended CFG, block by block; labels and the entry
are unchanged. -/
@[expose] def embedCFG (cfg : CFG String (DetBlock String (Cmd P) P)) :
    CFG String (DetBlock String (CmdExt P) P) :=
  { entry := cfg.entry, blocks := cfg.blocks.map (fun lb => (lb.1, embedDetBlock lb.2)) }

mutual
/-- Embed a base statement into an extended statement, wrapping each command with
    `CmdExt.cmd` and recursing structurally. -/
@[expose] def embedStmt (s : Stmt P (Cmd P)) : Stmt P (CmdExt P) :=
  match s with
  | .cmd c => .cmd (CmdExt.cmd c)
  | .block label ss md => .block label (embedStmts ss) md
  | .ite cond tss ess md => .ite cond (embedStmts tss) (embedStmts ess) md
  | .loop guard measure invariant body md =>
      .loop guard measure invariant (embedStmts body) md
  | .exit label md => .exit label md
  | .typeDecl tc md => .typeDecl tc md

/-- Embed a list of base statements into extended statements. -/
@[expose] def embedStmts (ss : List (Stmt P (Cmd P))) : List (Stmt P (CmdExt P)) :=
  match ss with
  | [] => []
  | s :: rest => embedStmt s :: embedStmts rest
end

/-- Embed a base configuration into an extended configuration.  The execution
    environment `Env P` does not mention the command type, so it is carried
    unchanged. -/
@[expose] def embedConfig (c : Config P (Cmd P)) : Config P (CmdExt P) :=
  match c with
  | .stmt s ρ => .stmt (embedStmt s) ρ
  | .stmts ss ρ => .stmts (embedStmts ss) ρ
  | .terminal ρ => .terminal ρ
  | .exiting label ρ => .exiting label ρ
  | .block label σ inner => .block label σ (embedConfig inner)
  | .seq inner ss => .seq (embedConfig inner) (embedStmts ss)

/-- Embed a base CFG configuration into an extended one, wrapping each residual
command with `CmdExt.cmd` and carrying the (command-independent) transfer and
environment unchanged. -/
@[expose] def embedCFGConfig :
    CFGConfig String (Cmd P) P → CFGConfig String (CmdExt P) P
  | .atBlock cfg l ρ => .atBlock (embedCFG cfg) l ρ
  | .inBlock cfg l cmds tr ρ => .inBlock (embedCFG cfg) l (cmds.map embedCommand) tr ρ
  | .terminal ρ => .terminal ρ

/-! ## Projecting extended statements back to base statements

Projection targets `Option`: a procedure `call` has no base image, so it yields
`none`. -/

/-- Project an extended command to a base command; a procedure `call` has no base
    image, so it returns `none`. -/
@[expose] def projectCommand : CmdExt P → Option (Cmd P)
  | .cmd c => some c
  | .call .. => none

mutual
/-- Project an extended statement to a base statement, returning `none` if any
    `call` is reachable. -/
@[expose] def projectStmt (s : Stmt P (CmdExt P)) : Option (Stmt P (Cmd P)) :=
  match s with
  | .cmd c => (projectCommand c).map Stmt.cmd
  | .block label ss md => (projectStmts ss).map (fun ss' => .block label ss' md)
  | .ite cond tss ess md =>
      match projectStmts tss, projectStmts ess with
      | some tss', some ess' => some (.ite cond tss' ess' md)
      | _, _ => none
  | .loop guard measure invariant body md =>
      (projectStmts body).map (fun body' => .loop guard measure invariant body' md)
  | .exit label md => some (.exit label md)
  | .typeDecl tc md => some (.typeDecl tc md)

/-- Project a list of extended statements, returning `none` if any `call` is
    reachable. -/
@[expose] def projectStmts (ss : List (Stmt P (CmdExt P))) : Option (List (Stmt P (Cmd P))) :=
  match ss with
  | [] => some []
  | s :: rest =>
      match projectStmt s, projectStmts rest with
      | some s', some rest' => some (s' :: rest')
      | _, _ => none
end

end
end Imperative
