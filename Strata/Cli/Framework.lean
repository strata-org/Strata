/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashMap.Basic

/-! # Shared CLI framework

Exit codes, flag parsing, command dispatch, and help-printing for the
Strata family of CLI executables. Used by the unified `strata` binary
in `Strata-CLI`, among possibly many other tools. -/

public section

/-! ## Exit codes

All Strata CLI executables use a common exit code scheme:

| Code | Category           | Meaning                                                   |
|------|--------------------|-----------------------------------------------------------|
| 0    | Success            | Analysis passed, inconclusive, or `--no-solve` completed.  |
| 1    | User error         | Bad input: invalid arguments, malformed source, etc.      |
| 2    | Failures found     | Analysis completed and found failures.                    |
| 3    | Internal error     | SMT encoding failure, solver crash, or translation bug.   |
| 4    | Known limitation   | Intentionally unsupported language construct.             |

Codes 1–2 are **user-actionable** (fix the input or the code under analysis).
Codes 3–4 are **tool-side** (report as a bug or wait for support).
Exit 0 covers success, inconclusive results, and solver timeouts. -/

namespace ExitCode
  def userError        : UInt8 := 1
  def failuresFound    : UInt8 := 2
  def internalError    : UInt8 := 3
  def knownLimitation  : UInt8 := 4
end ExitCode

def exitFailure {α} (message : String) (hint : String := "strata --help") : IO α := do
  IO.eprintln s!"Exception: {message}\n\nRun {hint} for additional help."
  IO.Process.exit ExitCode.userError

/-- Exit with code 1 for user errors (bad input, malformed source, etc.). -/
def exitUserError {α} (message : String) : IO α := do
  IO.eprintln s!"❌ {message}"
  IO.Process.exit ExitCode.userError

/-- Exit with code 2 for analysis failures found. -/
def exitFailuresFound {α} (message : String) : IO α := do
  IO.eprintln s!"Failures found: {message}"
  IO.Process.exit ExitCode.failuresFound

/-- Exit with code 3 for internal errors (tool limitations or crashes). -/
def exitInternalError {α} (message : String) : IO α := do
  IO.eprintln s!"Exception: {message}"
  IO.Process.exit ExitCode.internalError

/-- Exit with code 4 for known limitations (unsupported constructs). -/
def exitKnownLimitation {α} (message : String) : IO α := do
  IO.eprintln s!"Known limitation: {message}"
  IO.Process.exit ExitCode.knownLimitation

/-- Like `exitFailure` but tailors the help hint to a specific subcommand. -/
def exitCmdFailure {α} (cmdName : String) (message : String) : IO α :=
  exitFailure message (hint := s!"strata {cmdName} --help")

/-! ## Flags and parsed args -/

/-- How a flag consumes arguments. -/
inductive FlagArg where
  | none              -- boolean flag, e.g. --verbose
  | arg (name : String)    -- takes one value, e.g. --output <file>
  | repeat (name : String) -- takes one value, may appear multiple times, e.g. --include <path>

/-- A flag that a command accepts. -/
structure Flag where
  name : String         -- flag name without "--", used as lookup key
  help : String
  takesArg : FlagArg := .none

/-- Parsed flags from the command line.  Stored as an ordered array so that
    command-line position is preserved (needed by `transform` to bind
    `--procedures`/`--functions` to the preceding `--pass`).
    For `.arg` flags that appear more than once, `getString` returns the
    **last** occurrence (last-writer-wins). -/
structure ParsedFlags where
  entries : Array (String × Option String) := #[]

namespace ParsedFlags

def getBool (pf : ParsedFlags) (name : String) : Bool :=
  pf.entries.any (·.1 == name)

def getString (pf : ParsedFlags) (name : String) : Option String :=
  -- Scan from the end so last occurrence wins.
  match pf.entries.findRev? (·.1 == name) with
  | some (_, some v) => some v
  | _ => Option.none

def getRepeated (pf : ParsedFlags) (name : String) : Array String :=
  pf.entries.foldl (init := #[]) fun acc (n, v) =>
    if n == name then match v with | some s => acc.push s | none => acc else acc

def insert (pf : ParsedFlags) (name : String) (value : Option String) : ParsedFlags :=
  { pf with entries := pf.entries.push (name, value) }

end ParsedFlags

/-! ## Commands -/

structure Command where
  name : String
  args : List String
  flags : List Flag := []
  help : String
  callback : Vector String args.length → ParsedFlags → IO Unit

def includeFlag : Flag :=
  { name := "include", help := "Add a dialect search path.", takesArg := .repeat "path" }

structure CommandGroup where
  name : String
  commands : List Command
  commonFlags : List Flag := []

/-! ## Help-printing -/

/-- Print a string word-wrapped to `width` columns with `indent` spaces of indentation. -/
private def printIndented (indent : Nat) (s : String) (width : Nat := 80) : IO Unit := do
  let pad := "".pushn ' ' indent
  let words := s.splitOn " " |>.filter (!·.isEmpty)
  let mut line := pad
  let mut first := true
  for word in words do
    if first then
      line := line ++ word
      first := false
    else if line.length + 1 + word.length > width then
      IO.println line
      line := pad ++ word
    else
      line := line ++ " " ++ word
  unless line.length ≤ indent do
    IO.println line

/-- Print a single flag's name and help text at the given indentation. -/
private def printFlag (indent : Nat) (flag : Flag) : IO Unit := do
  let pad := "".pushn ' ' indent
  match flag.takesArg with
  | .arg argName | .repeat argName =>
    IO.println s!"{pad}--{flag.name} <{argName}>  {flag.help}"
  | .none =>
    IO.println s!"{pad}--{flag.name}  {flag.help}"

/-- Print help for all command groups. -/
def printGlobalHelp (groups : List CommandGroup) : IO Unit := do
  IO.println "Usage: strata <command> [flags]...\n"
  IO.println "Command-line utilities for working with Strata.\n"
  for group in groups do
    IO.println s!"{group.name}:"
    for cmd in group.commands do
      let cmdLine := cmd.args.foldl (init := cmd.name) fun s a => s!"{s} <{a}>"
      IO.println s!"  {cmdLine}"
      printIndented 4 cmd.help
      let perCmdFlags := cmd.flags.filter fun f =>
        !group.commonFlags.any fun cf => cf.name == f.name
      if !perCmdFlags.isEmpty then
        IO.println ""
        IO.println "    Flags:"
        for flag in perCmdFlags do
          printFlag 6 flag
      IO.println ""
    if !group.commonFlags.isEmpty then
      IO.println "  Common flags:"
      for flag in group.commonFlags do
        printFlag 4 flag
      IO.println ""

/-- Print help for a single command. -/
def printCommandHelp (cmd : Command) : IO Unit := do
  let cmdLine := cmd.args.foldl (init := s!"strata {cmd.name}") fun s a => s!"{s} <{a}>"
  let flagSummary := cmd.flags.foldl (init := "") fun s f =>
    match f.takesArg with
    | .arg argName | .repeat argName => s!"{s} [--{f.name} <{argName}>]"
    | .none => s!"{s} [--{f.name}]"
  IO.println s!"Usage: {cmdLine}{flagSummary}\n"
  printIndented 0 cmd.help
  if !cmd.flags.isEmpty then
    IO.println "\nFlags:"
    for flag in cmd.flags do
      printFlag 2 flag

/-! ## Argument parsing -/

/-- Parse interleaved flags and positional arguments. Returns the collected
    positional arguments and parsed flags. -/
private partial def parseArgs (cmdName : String)
    (flagMap : Std.HashMap String Flag)
    (acc : Array String) (pflags : ParsedFlags)
    (cmdArgs : List String) : IO (Array String × ParsedFlags) := do
  match cmdArgs with
  | arg :: cmdArgs =>
    if arg.startsWith "--" then
      let raw := (arg.drop 2).toString
      -- Support --flag=value syntax by splitting on first '='
      let (flagName, inlineValue) ← match raw.splitOn "=" with
        | name :: value :: rest =>
          if !rest.isEmpty then
            exitCmdFailure cmdName s!"Invalid option format: {arg}. Values must not contain '='."
          pure (name, some value)
        | _ => pure (raw, none)
      match flagMap[flagName]? with
      | some flag =>
        match flag.takesArg with
        | .none =>
          parseArgs cmdName flagMap acc (pflags.insert flagName Option.none) cmdArgs
        | .arg _ =>
          match inlineValue with
          | some value =>
            parseArgs cmdName flagMap acc (pflags.insert flagName (some value)) cmdArgs
          | none =>
            let value :: cmdArgs := cmdArgs
              | exitCmdFailure cmdName s!"Expected value after {arg}."
            parseArgs cmdName flagMap acc (pflags.insert flagName (some value)) cmdArgs
        | .repeat _ =>
          match inlineValue with
          | some value =>
            parseArgs cmdName flagMap acc (pflags.insert flagName (some value)) cmdArgs
          | none =>
            let value :: cmdArgs := cmdArgs
              | exitCmdFailure cmdName s!"Expected value after {arg}."
            parseArgs cmdName flagMap acc (pflags.insert flagName (some value)) cmdArgs
      | none =>
        exitCmdFailure cmdName s!"Unknown option {arg}."
    else
      parseArgs cmdName flagMap (acc.push arg) pflags cmdArgs
  | [] =>
    pure (acc, pflags)

/-- Run a single command directly (for per-command executables).
    Parses `args` against the command's flag set, then invokes the callback. -/
def runCommand (cmd : Command) (args : List String) : IO Unit := do
  try do
    if args.contains "--help" then
      printCommandHelp cmd
      return
    let flagMap : Std.HashMap String Flag :=
      cmd.flags.foldl (init := {}) fun m f => m.insert f.name f
    let (parsed, pflags) ← parseArgs cmd.name flagMap #[] {} args
    if p : parsed.size = cmd.args.length then
      cmd.callback ⟨parsed, p⟩ pflags
    else
      exitCmdFailure cmd.name s!"{cmd.name} expects {cmd.args.length} argument(s)."
  catch e =>
    exitFailure e.toString

/-- Dispatch CLI arguments against a command map. This is the shared entry point
    used by the unified `strata` binary. -/
def runCommandMap (map : Std.HashMap String Command)
    (groups : List CommandGroup) (args : List String) : IO Unit := do
  try do
    match args with
    | ["--help"] => printGlobalHelp groups
    | cmd :: args =>
      match map[cmd]? with
      | none => exitFailure s!"Expected subcommand, got {cmd}."
      | some cmd =>
        if args.contains "--help" then
          printCommandHelp cmd
          return
        let flagMap : Std.HashMap String Flag :=
          cmd.flags.foldl (init := {}) fun m f => m.insert f.name f
        let (args, pflags) ← parseArgs cmd.name flagMap #[] {} args
        if p : args.size = cmd.args.length then
          cmd.callback ⟨args, p⟩ pflags
        else
          exitCmdFailure cmd.name s!"{cmd.name} expects {cmd.args.length} argument(s)."
    | [] => do
      exitFailure "Expected subcommand."
  catch e =>
    exitFailure e.toString

end -- public section
