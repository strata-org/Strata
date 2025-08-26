/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

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

-- Simple runner for testing with statement list (uses shared CallHeap JSON output)
def run_ts_program (statements: List TS_Statement) : IO Unit := do
  let (translationCtx, tsStrataStatements) := translate_program statements
  -- Use the shared CallHeap JSON output function
  runCallHeapAndShowJSONWithTranslation translationCtx tsStrataStatements

-- Simple runner for testing with full Program
def run_full_ts_program (prog: TS_Program) : IO Unit := do
  run_ts_program prog.body.toList

-- Simple runner for testing with full TS_File
def run_full_ts_file (file: TS_File) : IO Unit := do
  run_full_ts_program file.program

-- TODO: Add JSON output functions similar to Python version

end TSStrata
