import Strata.Languages.TypeScript.js_ast
import Strata.Languages.TypeScript.TSStrataEval

def main (args : List String) : IO Unit := do
  -- Need to use the Lean-compatible JSON format
  match args with
  | [filename] =>
    let ast ← loadJsonFile filename
    TSStrata.run_full_ts_file ast
  | _ => IO.println "Usage: Executable filename"
