/-
TypeScript Strata Evaluator: TypeScript-specific evaluation using CallHeap evaluator
-/

import Strata.Languages.TypeScript.TSStrataStatement
import Strata.Languages.TypeScript.TS_to_Strata
import Strata.DL.CallHeap.CallHeapEvaluator
import Strata.DL.Heap.HState
import Strata.DL.Lambda.LState

---------------------------------------------------------------------

namespace TSStrata

open Heap
open CallHeap
open Lambda (LState)

-- Simple runner for testing with statement list
def run_ts_program (statements: List TS_Statement) : IO Unit := do
  let (translationCtx, tsStrataStatements) := translate_program statements
  IO.println s!"Translated {tsStrataStatements.length} statements"
  IO.println s!"Found {translationCtx.functionCount} functions"
  IO.println "=== TSStrata Statements ==="
  for (stmt, i) in tsStrataStatements.zip (List.range tsStrataStatements.length) do
    IO.println s!"[{i}] {describeTSStrataStatement stmt}"
  
  -- Use the generic CallHeap evaluator with translation context
  let final_ctx := evalCallHeapTranslatedProgram translationCtx tsStrataStatements
  
  -- Show results
  IO.println "\n=== Execution Results ==="
  IO.println s!"Final heap size: {final_ctx.hstate.heap.size}"
  IO.println s!"Variables: {final_ctx.hstate.heapVars.size} heap vars"
  
  -- Print heap variable values
  for (name, (ty, value)) in final_ctx.hstate.heapVars.toList do
    IO.println s!"  {name}: {repr value}"
  
  -- Print lambda state variables
  let knownVars := final_ctx.hstate.lambdaState.knownVars
  for name in knownVars do
    match Heap.HState.getVar final_ctx.hstate name with
    | some value => IO.println s!"  {name}: {repr value}"
    | none => continue

-- Simple runner for testing with full Program
def run_full_ts_program (prog: TS_Program) : IO Unit := do
  run_ts_program prog.body.toList

-- Simple runner for testing with full TS_File
def run_full_ts_file (file: TS_File) : IO Unit := do
  run_full_ts_program file.program

-- TODO: Add JSON output functions similar to Python version

end TSStrata
