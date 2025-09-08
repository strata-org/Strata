/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Data.Json

import Strata.Backends.CBMC.StrataToCBMC

def main (args : List String) : IO Unit := do
  match args with
  | ["test"] => IO.println testSymbols
  | [filename] =>
    let content ← IO.FS.readFile filename
    match Lean.Json.parse content with
    | .ok json =>
      match json.getArr? with
      | .ok arr =>
        let symbols := arr.filterMap fun j =>
          match Lean.fromJson? j with
          | .ok (s : CBMCSymbol) => some s
          | .error _ => none
        IO.println s!"Successfully parsed {symbols.size} symbols"
        for symbol in symbols do
          IO.println s!"Symbol: {symbol.name} (type: {symbol.prettyType})"
      | .error e => IO.println s!"Error getting array: {e}"
    | .error e => IO.println s!"Error parsing JSON: {e}"
  | _ => IO.println "Usage: StrataToCBMC filename or StrataToCBMC test"
