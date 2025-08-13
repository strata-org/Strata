/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable with utilities for working with Strata files.
import Strata.DDM.Elab
import Strata.DDM.Ion

def exitFailure (message : String) : IO α := do
  IO.eprintln (message  ++ "\n\nRun strata --help for additional help.")
  IO.Process.exit 1

def ByteArray.startsWith (a pre : ByteArray) :=
  if isLt : a.size < pre.size then
    false
  else
    pre.size.all fun i _ => a[i] = pre[i]

namespace Strata

inductive Encoding
| ion
| text


abbrev FileMap := Std.HashMap DialectName (IO.FS.SystemTime × Encoding × System.FilePath)

namespace FileMap

def strata_dialect_ext : String := ".dialect.st"

def strata_ion_dialect_ext : String := ".dialect.st.ion"

def matchExt (path : String) (ext : String) : Option String :=
  if path.endsWith ext then
    some (path.dropRight ext.length)
  else
    none

def addEntry (m : FileMap) (stem : DialectName) (enc : Encoding) (path : System.FilePath) : BaseIO FileMap := do
  -- TODO: Check stem is a legal dialect name
  let modTime ←
    match ← path.metadata |>.toBaseIO with
    | .error _ => return m
    | .ok md => pure md.modified
  pure <| m.alter stem fun o =>
    let isNewer :=
          match o with
          | none => true
          | some (prevTime, _) => modTime > prevTime
    if isNewer then
      some (modTime, enc, path)
    else
      o

def add (m : FileMap) (dir : System.FilePath) : EIO String FileMap := do
  let entries ←
    match ← dir.readDir |>.toBaseIO with
    | .error e => throw s!"Could not read {dir}: {e}"
    | .ok e => pure e
  entries.foldlM (init := m) fun m entry => do
    if let some stem := matchExt entry.fileName strata_dialect_ext then
      m.addEntry stem .text entry.path
    else if let some stem := matchExt entry.fileName strata_ion_dialect_ext then
      m.addEntry stem .ion entry.path
    else do
      let _ ← IO.eprintln s!"Skipping {dir / entry.fileName}" |>.toBaseIO
      pure m

def ofDirs (dirs : Array System.FilePath) : EIO String FileMap :=
  dirs.foldlM (init := {}) fun m dir => m.add dir

end FileMap

def asText [Monad m] [MonadExcept String m] (path : System.FilePath) (bytes : ByteArray) : m String :=
  match String.fromUTF8? bytes with
  | some s =>
    pure s
  | none =>
    throw s!"{path} is not an Ion file and contains non UTF-8 data"


def mkErrorReport (path : System.FilePath) (errors : Array (Lean.Syntax × Lean.Message)) : BaseIO String := do
  let msg : String := s!"{errors.size} error(s) reading {path}:\n"
  let msg ← errors.foldlM (init := msg) fun msg (_, e) =>
    return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"
  return toString msg

mutual

partial def recordDialect (searchMap : FileMap) (env : Lean.Environment) (d : Dialect) (stk : Array DialectName) : ExceptT String (StateT Elab.LoadedDialects BaseIO) Unit := do
  let stk := stk.push d.name
  d.imports.forM fun i => do
    let _ ← loadDialect searchMap env stk i
    pure ()
  modify (·.addDialect! d)

partial def loadDialect (searchMap : FileMap) (env : Lean.Environment) (stk : Array DialectName) (name : Strata.DialectName) :
    ExceptT String (StateT Elab.LoadedDialects BaseIO) Strata.Dialect := do
  if let some d := (← get).dialects[name]? then
    return d

  let (_, _, path) ←
        match searchMap[name]? with
        | none => throw s!"Unknown dialect {name}: {searchMap.keys}"
        | some path => pure path
  let bytes ←
    match ← IO.FS.readBinFile path |>.toBaseIO with
    | .error _ =>
      throw s!"Error reading {path}."
    | .ok c =>
      pure c
  let stk := stk.push name
  if bytes.startsWith Ion.binaryVersionMarker then
    let d ← FromIonM.deserializeValue bytes FromIon.fromIon
    recordDialect searchMap env d stk
    pure d
  else
    let contents ← asText path bytes
    readDialectTextfile searchMap env path contents stk

partial def readDialectTextfile (searchMap : FileMap) (leanEnv : Lean.Environment) (input : System.FilePath) (contents : String) (stk : Array DialectName := #[]) : ExceptT String (StateT Elab.LoadedDialects BaseIO) Dialect := do
  let inputContext := Strata.Parser.stringInputContext contents
  let (header, errors, startPos) := Elab.elabHeader leanEnv inputContext
  if errors.size > 0 then
    throw  (← mkErrorReport input errors)
  match header with
  | .program stx _ =>
    let pos := stx.getPos? |>.getD 0
    throw s!"{pos}: Expected dialect."
  | .dialect stx dialect =>
    let stk := stk.push dialect
    fun ld => do
      let (d, s, loaded) ← Elab.elabDialectRest leanEnv (loadDialect searchMap leanEnv stk) ld
            inputContext stx dialect startPos
      if s.errors.size > 0 then
        let msg ← mkErrorReport input s.errors
        pure (.error (toString msg), loaded)
      else
        pure (.ok d, loaded.addDialect! d)

end

inductive DialectOrProgram
| dialect (d : Dialect)
| program (pgm : Program)

end Strata

def readStrataText (searchPath : Strata.FileMap) (input : System.FilePath) (bytes : ByteArray) : IO (Strata.DialectOrProgram × Strata.Elab.LoadedDialects) := do
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let contents ←
    match Strata.asText input bytes with
    | Except.ok c => pure c
    | Except.error msg => exitFailure msg
  let inputContext := Strata.Parser.stringInputContext contents
  let (header, errors, startPos) := Strata.Elab.elabHeader leanEnv inputContext
  if errors.size > 0 then
    exitFailure  (← Strata.mkErrorReport input errors)
  match header with
  | .program stx dialect =>
    let dialects ←
      match ← Strata.loadDialect searchPath leanEnv #[] dialect .builtin with
      | (.ok _, dialects) => pure dialects
      | (.error msg, _) => exitFailure msg
    match Strata.Elab.elabProgramRest dialects leanEnv inputContext stx dialect startPos with
    | .ok program => pure (.program program, dialects)
    | .error errors =>     exitFailure  (← Strata.mkErrorReport input errors)
  | .dialect stx dialect =>
    let (d, s, loaded) ←
      Strata.Elab.elabDialectRest leanEnv (Strata.loadDialect searchPath leanEnv #[])
        .builtin inputContext stx dialect startPos
    if s.errors.size > 0 then
      exitFailure (← Strata.mkErrorReport input s.errors)
    pure (.dialect d, loaded.addDialect! d)


def readStrataIon (searchPath : Strata.FileMap) (bytes : ByteArray) : IO (Strata.DialectOrProgram × Strata.Elab.LoadedDialects) := do
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let act v := do
    let ⟨args, _⟩ ← .asList v
    let .isTrue ne := inferInstanceAs (Decidable (args.size ≥ 1))
      | throw s!"Expected header"
    return (← read, ← Strata.Header.fromIon args[0], args)
  match Strata.FromIonM.deserializeValue bytes act with
  | .error msg =>
    exitFailure msg
  | .ok (ionCtx, hdr, args) =>
    match hdr with
    | .dialect dialect =>
      match Strata.Dialect.fromIonDecls dialect args (start := 1) ionCtx with
      | .error msg =>
        exitFailure msg
      | .ok d =>
        match ← Strata.recordDialect searchPath leanEnv d #[] .builtin with
        | (.ok (), dialects) =>
          pure (.dialect d, dialects)
        | (.error msg, dialects) =>
          exitFailure msg
    | .program dialect => do
      let dialects ←
        match ← Strata.loadDialect searchPath leanEnv #[] dialect .builtin with
        | (.ok _, loaded) => pure loaded
        | (.error msg, loaded) => exitFailure msg
      match Strata.Program.fromIonDecls dialects.dialects dialect args (start := 1) ionCtx with
      | .ok pgm =>
        pure (.program pgm, dialects)
      | .error msg =>
        exitFailure msg

def readFile (searchPath : Strata.FileMap) (path : System.FilePath) : IO (Strata.DialectOrProgram × Strata.Elab.LoadedDialects) := do
  let bytes ←
    match ← IO.FS.readBinFile path |>.toBaseIO with
    | .error _ =>
      exitFailure s!"Error reading {path}."
    | .ok c => pure c
  if bytes.startsWith Ion.binaryVersionMarker then
    readStrataIon searchPath bytes
  else
    readStrataText searchPath path bytes

structure Command where
  name : String
  args : List String
  help : String
  callback : Strata.FileMap → Vector String args.length → IO Unit

def checkCommand : Command where
  name := "check"
  args := [ "file" ]
  help := "Check a dialect or program file."
  callback := fun fm v => do
    let _ ← readFile fm v[0]
    pure ()

def toIonCommand : Command where
  name := "toIon"
  args := [ "input", "output" ]
  help := "Read a Strata text file and translate into Ion."
  callback := fun searchPath v => do
    let (pd, _) ← readFile searchPath v[0]
    match pd with
    | .dialect d =>
      IO.FS.writeBinFile v[1] d.toIon
    | .program pgm =>
      IO.FS.writeBinFile v[1] pgm.toIon

def printCommand : Command where
  name := "print"
  args := [ "file" ]
  help := "Write a Strata text or Ion file to standard output."
  callback := fun searchPath v => do
    let (pd, ld) ← readFile searchPath v[0]
    match pd with
    | .dialect d =>
      IO.print <| d.format ld.dialects
    | .program pgm =>
      IO.print <| toString pgm

def commandList : List Command := [
      checkCommand,
      toIonCommand,
      printCommand,
    ]

def commandMap : Std.HashMap String Command := commandList.foldl (init := {}) fun m c => m.insert c.name c

def main (args : List String) : IO Unit := do
  match args with
  | ["--help"] => do
    IO.println "Usage: strata <command> [flags]...\n"
    for cmd in commandList do
      let args := cmd.args.foldl (init := s!"  {cmd.name}") fun s a => s!"{s} <{a}>"
      IO.println s!"  {args}: {cmd.help}"
    IO.println "\nFlags:"
    IO.println "  --include path: Adds a path to Strata for searching for dialects."
  | cmd :: args =>
    match commandMap[cmd]? with
    | none => exitFailure s!"Unknown command {cmd}"
    | some cmd =>
      let expectedArgs := cmd.args.length
      let rec process (sp : Strata.FileMap) args (cmdArgs : List String) : IO _ := do
            match cmdArgs with
            | cmd :: cmdArgs =>
              match cmd with
              | "--include" =>
                let path :: cmdArgs := cmdArgs
                  | exitFailure s!"Expected path after --path."
                match ← sp.add path |>.toBaseIO with
                | .error msg => exitFailure msg
                | .ok sp => process sp args cmdArgs
              | _ =>
                if cmd.startsWith "--" then
                  exitFailure s!"Unknown option {cmd}."
                process sp (args.push cmd) cmdArgs
            | [] =>
              pure (sp, args)
      let (sp, args) ← process {} #[] args
      if p : args.size = cmd.args.length then
        cmd.callback sp ⟨args, p⟩
      else
        exitFailure s!"{cmd.name} expects {expectedArgs} argument(s)."
  | [] => do
    exitFailure "Expected subcommand."
