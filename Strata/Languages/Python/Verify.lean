/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Ion
import Strata.Util.IO
import Strata.Languages.Python.Python
import Strata.Languages.Boogie.Verifier
import StrataTest.Transform.ProcedureInlining

namespace Strata.Languages.Python

structure CommandFlags where
  verbose : Bool := false
  noinline : Bool := false

def exitFailure {α} (message : String) : IO α := do
  IO.eprintln (message  ++ "\n\nRun strata --help for additional help.")
  IO.Process.exit 1

def readPythonStrata (path : String) : IO Strata.Program := do
  let bytes ← Strata.Util.readBinInputSource path
  if ! bytes.startsWith Ion.binaryVersionMarker then
    exitFailure s!"pyAnalyze expected Ion file"
  match Strata.Program.fromIon Strata.Python.Python_map Strata.Python.Python.name bytes with
  | .ok p => pure p
  | .error msg => exitFailure msg

def pyTranslate (path : String) : IO Unit := do
  let pgm ← readPythonStrata path
  let preludePgm := Strata.Python.Internal.Boogie.prelude
  let bpgm := Strata.pythonToBoogie pgm
  let newPgm : Boogie.Program := { decls := preludePgm.decls ++ bpgm.decls }
  IO.print newPgm

def pyAnalyze (path : String) (flags : CommandFlags) : IO Unit := do
  let verbose := flags.verbose
  let inline := !flags.noinline
  let pgm ← readPythonStrata path
  if verbose then
    IO.print pgm
  let preludePgm := Strata.Python.Internal.Boogie.prelude
  let bpgm := Strata.pythonToBoogie pgm
  let newPgm : Boogie.Program := { decls := preludePgm.decls ++ bpgm.decls }
  if verbose then
    IO.print newPgm
  let newPgm := if inline then runInlineCall newPgm else newPgm
  if verbose && inline then
    IO.println "Inlined: "
    IO.print newPgm
  let vcResults ← EIO.toIO (fun f => IO.Error.userError (toString f))
                      (Boogie.verify "z3" newPgm { Options.default with stopOnFirstError := false,
                                                                        verbose,
                                                                        removeIrrelevantAxioms := true }
                                               (moreFns := Strata.Python.ReFactory))
  let mut s := ""
  for vcResult in vcResults do
    s := s ++ s!"\n{vcResult.obligation.label}: {Std.format vcResult.result}\n"
  IO.println s

end Strata.Languages.Python
