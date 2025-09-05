import Strata.Languages.Python.python_ast
import Strata.Languages.Python.Python_to_Strata
import Strata.DL.CallHeap.CallHeapDataFlow
import Strata.Analysis.TaintAnalysis.TaintAnalysis

open TaintAnalysis

def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    let ast ← loadJsonFile filename
    -- Translate Python to Strata HeapStrata
    let (translationCtx, strataStmts) := PythonStrata.translate_full_program ast

    -- Run the taint analysis on HeapStrata expressions
    let result := analyzeDataFlows strataStmts

    -- Convert to JSON string
    let jsonStr := Lean.toJson result |>.pretty

    -- Write to file for VS Code extension to read
    IO.FS.writeFile "/tmp/analysis_result.json" jsonStr

    -- Also output to stdout for command line usage
    IO.println jsonStr

  | _ => IO.println "Usage: PythonTaintAnalysis filename"
