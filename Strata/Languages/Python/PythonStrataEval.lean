/-
Python Strata Evaluator: Python-specific evaluation using CallHeap evaluator
-/

import Strata.Languages.Python.PythonStrataStatement
import Strata.Languages.Python.Python_to_Strata
import Strata.DL.CallHeap.CallHeapEvaluator
import Strata.DL.Heap.HState
import Strata.DL.Lambda.LState

---------------------------------------------------------------------

namespace PythonStrata

open Heap
open CallHeap
open Lambda (LState)

-- Simple runner for testing with statement list
def run_python_program (statements: List Py_Statement) : IO Unit := do
  let (translationCtx, pythonStrataStatements) := translate_program statements
  -- Use the shared CallHeap JSON output function
  runCallHeapAndShowJSONWithTranslation translationCtx pythonStrataStatements

-- Simple runner for testing with full PyModule
def run_full_python_program (module: Py_Module) : IO Unit := do
  run_python_program module.body.toList

-- TODO: Add JSON output functions similar to MIDI version
-- TODO: Add function context support when we implement function translation

end PythonStrata
