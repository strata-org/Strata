import Strata.Languages.TypeScript.js_ast
import Strata.Languages.TypeScript.TS_to_Strata
import Strata.Analysis.ValueValidation.ValueValidation

open ValueValidation

def main (args : List String) : IO Unit := do
  match args with
  | [filename] =>
    let ast ← loadJsonFile filename
    -- Translate TypeScript to Strata CallHeap
    let (translationCtx, strataStmts) := TSStrata.translate_full_ts_program ast

    -- Run the value validation analysis on CallHeap statements
    let result := analyzeCallHeapProgram translationCtx strataStmts

    -- Convert to JSON string
    let jsonStr := Lean.toJson result |>.pretty

    -- Write to file for VS Code extension to read
    IO.FS.writeFile "/tmp/validation_result.json" jsonStr

    -- Also output to stdout for command line usage
    IO.println jsonStr

  | _ => IO.println "Usage: TypeScriptValueValidation filename"
