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
  `Lean.Parser.Command.syntaxAbbrev,
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
  `Lean.Parser.Command.declare_tagged_region,
  `Lean.Parser.Command.mixfix,
  `Lean.Parser.Command.grindPattern,
  `Lean.Parser.Command.binderPredicate
]

/-- Check if a command syntax node kind is known to be pure. -/
private def isPureCommand (kind : SyntaxNodeKind) : Bool :=
  pureCommandKinds.contains kind ||
  pureCommandPrefixes.any (fun pfx => pfx.isPrefixOf kind) ||
  kind == nullKind

/-- An impure command found during purity checking. -/
structure ImpureCommand where
  kind : SyntaxNodeKind
  line : Nat
  col  : Nat

/-- Parse a .lean file and check all top-level commands for purity.
Returns the list of impure commands found (empty = pure module). -/
def checkFilePurity (contents : String) (fileName : String := "<input>") :
    IO (List ImpureCommand) := do
  let inputCtx := mkInputContext contents fileName
  let (header, parserState, msgs) ← parseHeader inputCtx
  let (env, _msgs) ← Elab.processHeader header {} msgs inputCtx
  let pmctx : ParserModuleContext := { env, options := {} }
  let mut reasons : List ImpureCommand := []
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
        let pos := inputCtx.fileMap.toPosition (cmd.getPos?.getD 0)
        reasons := { kind, line := pos.line, col := pos.column } :: reasons
  return reasons.reverse

/-- Recursively collect all .lean files under a directory. -/
partial def collectLeanFiles (path : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  if ← path.isDir then
    for entry in ← path.readDir do
      let sub ← collectLeanFiles entry.path
      result := result ++ sub
  else if path.extension == some "lean" then
    result := result.push path
  return result

/-- Resolve arguments: expand directories into .lean files. -/
def resolveInputs (inputs : List String) : IO (Array System.FilePath) := do
  let mut files := #[]
  for input in inputs do
    let path : System.FilePath := input
    if ← path.isDir then
      files := files ++ (← collectLeanFiles path)
    else
      files := files.push path
  return files

def purityCheckMain (args : List String) : IO UInt32 := do
  let impureOnly := args.contains "--impure-only"
  -- Parse --output <file>
  let rec findOutput : List String → Option String
    | "--output" :: v :: _ => some v
    | _ :: rest => findOutput rest
    | [] => none
  let outputFile := findOutput args
  -- Collect non-flag arguments as inputs
  let mut inputs : List String := []
  let mut skipNext := false
  for arg in args do
    if skipNext then
      skipNext := false
    else if arg == "--output" then
      skipNext := true
    else if !arg.startsWith "--" then
      inputs := arg :: inputs
  let inputPaths := inputs.reverse
  if inputPaths.isEmpty then
    IO.eprintln "Usage: purityCheck [--impure-only] [--output <file>] <path> [path ...]"
    IO.eprintln "  <path> can be a .lean file or a directory (recursively scanned)"
    return 1
  let files ← resolveInputs inputPaths
  let mut exitCode : UInt32 := 0
  let mut outputLines : Array String := #[]
  for file in files.toList.mergeSort (·.toString < ·.toString) do
    let contents ← IO.FS.readFile file
    let reasons ← checkFilePurity contents file.toString
    if reasons.isEmpty then
      unless impureOnly do
        IO.println s!"PURE:   {file}"
    else
      let line := s!"IMPURE: {file}"
      IO.println line
      outputLines := outputLines.push file.toString
      for r in reasons do
        IO.println s!"  - {r.kind} at {r.line}:{r.col}"
      exitCode := 1
  if let some outPath := outputFile then
    IO.FS.writeFile outPath (outputLines.toList.map (· ++ "\n") |>.foldl (· ++ ·) "")
    IO.eprintln s!"Wrote {outputLines.size} impure files to {outPath}"
  return exitCode
