/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Parser
import Lean.Parser.Command
import Lean.Parser.Module
import Lean.Elab.Import

/-! # Module Purity Checker

Determines whether elaborating a Lean module could potentially perform I/O.

Uses a conservative allowlist approach: commands whose elaboration is known to
be pure are on the allowlist; everything else is treated as potentially impure.

## Usage

  lake exe purityCheck [--impure-only] <file1.lean> [file2.lean ...]

Prints each file with its purity status. With `--impure-only`, only prints
files that might perform I/O (useful for cache invalidation).
-/

open Lean Parser

/-- Commands whose elaboration is known to be pure (no I/O side effects). -/
private def pureCommandKinds : Std.HashSet SyntaxNodeKind := .ofList [
  -- Top-level declarations (elaborate types/terms but don't execute them)
  ``Command.declaration,
  ``Command.«deriving»,

  -- Structural / scoping
  ``Command.«section»,
  ``Command.«namespace»,
  ``Command.«end»,
  ``Command.«variable»,
  ``Command.«universe»,
  ``Command.«open»,
  ``Command.«export»,
  ``Command.«import»,
  ``Command.«mutual»,
  ``Command.«in»,
  ``Command.«include»,
  ``Command.«omit»,
  ``Command.withWeakNamespace,
  ``Command.withExporting,

  -- Options and attributes (pure metadata)
  ``Command.«set_option»,
  ``Command.«attribute»,

  -- Inspection commands (pure — only print/check, no execution)
  ``Command.check,
  ``Command.check_failure,
  ``Command.print,
  ``Command.printSig,
  ``Command.printAxioms,
  ``Command.printEqns,
  ``Command.printTacTags,
  ``Command.«where»,
  ``Command.version,
  ``Command.synth,

  -- Assertions about the environment (pure checks)
  ``Command.assertNotExists,
  ``Command.assertNotImported,
  ``Command.checkAssertions,

  -- Documentation
  ``Command.moduleDoc,
  ``Command.addDocString,

  -- Misc pure commands
  ``Command.«register_tactic_tag»,
  ``Command.«tactic_extension»,
  ``Command.«recommended_spelling»,
  ``Command.genInjectiveTheorems,
  ``Command.registerErrorExplanationStx,
  ``Command.«init_quot»,
  ``Command.exit,
  ``Command.eoi
]

/-- Command kind prefixes known to be pure (syntax/notation/macro definitions). -/
private def pureCommandPrefixes : Array Name := #[
  `Lean.Parser.Command.syntax,
  `Lean.Parser.Command.syntaxCat,
  `Lean.Parser.Command.notation,
  `Lean.Parser.Command.macro,
  `Lean.Parser.Command.macro_rules,
  `Lean.Parser.Command.elab,
  `Lean.Parser.Command.elab_rules,
  `Lean.Parser.Command.«scoped»,
  `Lean.Parser.Command.«local»,
  `Lean.Parser.Command.simproc,
  `Lean.Parser.Command.builtin_simproc,
  `Lean.Parser.Command.dsimproc,
  `Lean.Parser.Command.builtin_dsimproc,
  `Lean.Parser.Command.register_simp_attr,
  `Lean.Parser.Command.register_option,
  `Lean.Parser.Command.register_builtin_option,
  `Lean.Parser.Command.register_label_attr,
  `Lean.Parser.Command.«infix»,
  `Lean.Parser.Command.«infixl»,
  `Lean.Parser.Command.«infixr»,
  `Lean.Parser.Command.«prefix»,
  `Lean.Parser.Command.«postfix»,
  `Lean.Parser.Command.declare_syntax_cat,
  `Lean.Parser.Command.declare_config_elab,
  `Lean.Parser.Command.declare_command_config_elab,
  `Lean.Parser.Command.declare_config_getter,
  `Lean.Parser.Command.declare_simp_like_tactic,
  `Lean.Parser.Command.declare_tagged_region
]

/-- Check if a command syntax node kind is known to be pure. -/
private def isPureCommand (kind : SyntaxNodeKind) : Bool :=
  pureCommandKinds.contains kind ||
  pureCommandPrefixes.any (fun pfx => pfx.isPrefixOf kind) ||
  kind == nullKind

/-- Parse a .lean file and check all top-level commands for purity.
Returns the list of impure command kind names (empty = pure module). -/
def checkFilePurity (contents : String) (fileName : String := "<input>") :
    IO (List (SyntaxNodeKind × String.Pos.Raw)) := do
  let inputCtx := mkInputContext contents fileName
  let (header, parserState, msgs) ← parseHeader inputCtx
  let (env, _msgs) ← Elab.processHeader header {} msgs inputCtx
  let pmctx : ParserModuleContext := { env, options := {} }
  let mut reasons : List (SyntaxNodeKind × String.Pos.Raw) := []
  let mut mps := parserState
  let mut messages := MessageLog.empty
  let mut done := false
  while !done do
    let (cmd, mps', msgs') := parseCommand inputCtx pmctx mps messages
    mps := mps'
    messages := msgs'
    if isTerminalCommand cmd then
      done := true
    else
      let kind := cmd.getKind
      if !isPureCommand kind then
        reasons := (kind, cmd.getPos?.getD 0) :: reasons
  return reasons.reverse

def main (args : List String) : IO UInt32 := do
  let impureOnly := args.contains "--impure-only"
  let files := args.filter (fun a => !a.startsWith "--")
  if files.isEmpty then
    IO.eprintln "Usage: purityCheck [--impure-only] <file1.lean> [file2.lean ...]"
    return 1
  let mut exitCode : UInt32 := 0
  for file in files do
    let contents ← IO.FS.readFile file
    let reasons ← checkFilePurity contents file
    if reasons.isEmpty then
      unless impureOnly do
        IO.println s!"PURE:   {file}"
    else
      IO.println s!"IMPURE: {file}"
      for (kind, pos) in reasons do
        IO.println s!"  - {kind} at byte {pos}"
      exitCode := 1
  return exitCode
