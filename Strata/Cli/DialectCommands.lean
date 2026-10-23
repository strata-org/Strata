/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Cli.Framework
public import StrataDDM

public section

open StrataDDM.Elab (LoadedDialects)

namespace ParsedFlags

def buildDialectFileMap (pflags : ParsedFlags) (preloaded : LoadedDialects) :
    IO StrataDDM.DialectFileMap := do
  let mut sp ← StrataDDM.DialectFileMap.new preloaded
  for path in pflags.getRepeated "include" do
    match ← sp.add path |>.toBaseIO with
    | .error msg => exitFailure msg
    | .ok sp' => sp := sp'
  return sp

end ParsedFlags

namespace Strata.Cli

def checkCommand (dialects : LoadedDialects) : Command where
  name := "check"
  args := [ "file" ]
  flags := [includeFlag]
  help := "Parse and validate a Strata file (text or Ion). Reports errors and exits."
  callback := fun v pflags => do
    let fm ← pflags.buildDialectFileMap dialects
    let _ ← StrataDDM.readStrataFile fm v[0]

def toIonCommand (dialects : LoadedDialects) : Command where
  name := "toIon"
  args := [ "input", "output" ]
  flags := [includeFlag]
  help := "Convert a Strata text file to Ion binary format."
  callback := fun v pflags => do
    let searchPath ← pflags.buildDialectFileMap dialects
    let pd ← StrataDDM.readStrataFile searchPath v[0]
    match pd with
    | .dialect d =>
      IO.FS.writeBinFile v[1] d.toIon
    | .program pgm =>
      IO.FS.writeBinFile v[1] pgm.toIon

def printCommand (dialects : LoadedDialects) : Command where
  name := "print"
  args := [ "file" ]
  flags := [includeFlag]
  help := "Pretty-print a Strata file (text or Ion) to stdout."
  callback := fun v pflags => do
    let searchPath ← pflags.buildDialectFileMap dialects
    -- Special case for already loaded dialects.
    let ld ← searchPath.getLoaded
    if mem : v[0] ∈ ld.dialects then
      IO.print <| ld.dialects.format v[0] mem
      return
    let pd ← StrataDDM.readStrataFile searchPath v[0]
    match pd with
    | .dialect d =>
      let ld ← searchPath.getLoaded
      let .isTrue mem := (inferInstance : Decidable (d.name ∈ ld.dialects))
        | exitInternalError "Internal error reading file."
      IO.print <| ld.dialects.format d.name mem
    | .program pgm =>
      IO.print <| toString pgm

def diffCommand (dialects : LoadedDialects) : Command where
  name := "diff"
  args := [ "file1", "file2" ]
  flags := [includeFlag]
  help := "Compare two program files for syntactic equality. Reports the first difference found."
  callback := fun v pflags => do
    let fm ← pflags.buildDialectFileMap dialects
    let p1 ← StrataDDM.readStrataFile fm v[0]
    let p2 ← StrataDDM.readStrataFile fm v[1]
    match p1, p2 with
    | .program p1, .program p2 =>
      if p1.dialect != p2.dialect then
        exitFailure s!"Dialects differ: {p1.dialect} and {p2.dialect}"
      let Decidable.isTrue eq := (inferInstance : Decidable (p1.commands.size = p2.commands.size))
        | exitFailure s!"Number of commands differ {p1.commands.size} and {p2.commands.size}"
      for (c1, c2) in Array.zip p1.commands p2.commands do
        if c1 != c2 then
          exitFailure s!"Commands differ: {repr c1} and {repr c2}"
    | _, _ =>
      exitFailure "Cannot compare dialect def with another dialect/program."

end Strata.Cli

end -- public section
