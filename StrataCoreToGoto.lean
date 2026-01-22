/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Data.Json

import StrataTest.Backends.CBMC.SimpleAdd.SimpleAdd

def main (args : List String) : IO Unit := do
  match args with
  | ["writeFiles"] =>
    CoreToGOTO.writeToGotoJson (programName := "simpleAdd")
      (symTabFileName := "StrataTest/Backends/CBMC/SimpleAdd/simpleAdd.symtab.json")
      (gotoFileName := "StrataTest/Backends/CBMC/SimpleAdd/simpleAdd.goto.json")
      Strata.simpleAdd
    IO.println "Written JSON files in StrataTest/Backends/CBMC/SimpleAdd/"
  | _ => IO.println "Bad usage of StrataCoreToGoto"
