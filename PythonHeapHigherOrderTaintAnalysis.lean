import Strata.Languages.Python.python_ast
import Strata.Languages.HeapHigherOrderPython.Python_to_Strata
import Strata.DL.HeapHigherOrder.HeapHigherOrderDataFlow
import Strata.Analysis.TaintAnalysis.TaintAnalysis

open TaintAnalysis

def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    let ast ← loadJsonFile filename
    -- Translate Python to Strata CallHeapHigherOrder
    let (translationCtx, strataStmts) := PythonHeapHigherOrderStrata.translate_full_module ast

    -- Run the taint analysis on CallHeapHigherOrder expressions with context
    let result := analyzeGenericProgram translationCtx strataStmts

    -- Convert to JSON string
    let jsonStr := Lean.toJson result |>.pretty

    -- Write to file for VS Code extension to read
    IO.FS.writeFile "/tmp/analysis_result.json" jsonStr

    -- Also output to stdout for command line usage
    IO.println jsonStr

  | _ => IO.println "Usage: PythonHeapHigherOrderTaintAnalysis filename"
