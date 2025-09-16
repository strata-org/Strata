/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Data.Json

import StrataTest.Backends.CBMC.SimpleAddUnsigned.SimpleAddUnsigned

def main (args : List String) : IO Unit := do
  match args with
  | ["writeFile"] =>
    BoogieToGOTO.writeToGotoJson
      "StrataTest/Backends/CBMC/SimpleAddUnsigned/function.json"
      "simpleAddUnsigned"
      Strata.simpleAddUnsigned
    IO.println "Written file: StrataTest/Backends/CBMC/SimpleAddUnsigned/function.json"
  | _ => IO.println "Bad usage of BoogieToGoto"
