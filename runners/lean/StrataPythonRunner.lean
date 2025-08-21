import Strata.Languages.Python.python_ast
import Strata.Languages.Python.PythonStrataEval

def main (args : List String) : IO Unit := do
  -- Need to use the Lean-compatible JSON format
  match args with
  | [filename] =>
    let ast ← loadJsonFile filename
    PythonStrata.run_full_python_program ast
  | _ => IO.println "Usage: Executable filename"
