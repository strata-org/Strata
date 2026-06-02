/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataPython
import StrataPython.PyFactory
import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline

open StrataPython

def main (args : List String) : IO UInt32 := do
  let mut filePath := ""
  let mut dispatchModules : Array String := #[]
  let mut pyspecModules : Array String := #[]
  let mut specDir := "."
  let mut rest := args
  while h : !rest.isEmpty do
    have : rest ≠ [] := by simp_all
    let arg := rest.head this
    rest := rest.tail
    if arg == "--dispatch" then
      match rest with
      | [] => IO.eprintln "--dispatch requires an argument"; return 1
      | val :: rest' => dispatchModules := dispatchModules.push val; rest := rest'
    else if arg == "--pyspec" then
      match rest with
      | [] => IO.eprintln "--pyspec requires an argument"; return 1
      | val :: rest' => pyspecModules := pyspecModules.push val; rest := rest'
    else if arg == "--spec-dir" then
      match rest with
      | [] => IO.eprintln "--spec-dir requires an argument"; return 1
      | val :: rest' => specDir := val; rest := rest'
    else if arg == "--help" then
      IO.println "Usage: PyAnalyzeLaurelToGoto <file> [--dispatch <module>]... [--pyspec <module>]... [--spec-dir <dir>]"
      return 0
    else if arg.startsWith "--" then
      IO.eprintln s!"Unknown flag: {arg}"; return 1
    else
      filePath := arg
  if filePath.isEmpty then
    IO.eprintln "Error: no input file specified"
    return 1
  unless ← System.FilePath.isDir specDir do
    IO.eprintln s!"Error: spec-dir '{specDir}' does not exist or is not a directory"
    return 1
  let (coreProgram, _) ←
    match ← pyTranslateLaurel filePath dispatchModules pyspecModules (specDir := specDir) |>.toBaseIO with
    | .ok r => pure r
    | .error msg => IO.eprintln s!"Error: {msg}"; return 1
  let baseName := deriveBaseName filePath
  match ← Strata.inlineCoreToGotoFiles coreProgram baseName
            (factory := PythonFactory) |>.toBaseIO with
  | .ok () => return 0
  | .error msg => IO.eprintln s!"Error: {msg}"; return 1

where
  deriveBaseName (path : String) : String :=
    let bn := System.FilePath.fileStem ⟨path⟩ |>.getD path
    let bn := if bn.endsWith ".python.st" then bn.dropRight 10
              else if bn.endsWith ".py" then bn.dropRight 3
              else if bn.endsWith ".st" then bn.dropRight 3
              else bn
    bn
