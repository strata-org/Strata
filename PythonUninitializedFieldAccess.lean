import Strata.Languages.Python.python_ast
import Strata.Languages.Python.Python_to_Strata
import Strata.Analysis.UninitializedFieldAccess.UninitializedFieldAccess

open UninitializedFieldAccess

def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    let ast ← loadJsonFile filename
    -- Translate Python to Strata CallHeap
    let (translationCtx, strataStmts) := PythonStrata.translate_full_program ast

    -- Run the uninitialized field access analysis on CallHeap statements
    let result := analyzeCallHeapProgram translationCtx strataStmts

    -- Convert to JSON string
    let jsonStr := Lean.toJson result |>.pretty

    -- Write to file for VS Code extension to read
    IO.FS.writeFile "/tmp/uninit_field_result.json" jsonStr

    -- Also output to stdout for command line usage
    IO.println jsonStr

  | _ => IO.println "Usage: PythonUninitializedFieldAccess filename"
