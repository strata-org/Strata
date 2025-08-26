/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/- Authors(s):
Your Name <your.email@example.com>
-/

import Strata.DL.Heap.Heap

---------------------------------------------------------------------

namespace Heap.Examples

/-! ## Heap Dialect Examples

Simple examples demonstrating the heap dialect functionality.
-/

-- Example 1: Simple object allocation with arbitrary field indices
def example1 : HExpr :=
  HExpr.allocSimple [(5, HExpr.int 42), (2, HExpr.int 24)]

-- Example 2: Field access
def example2 : HExpr :=
  let obj := HExpr.allocSimple [(10, HExpr.int 100)]
  HExpr.deref obj 10

-- Example 3: Field update
def example3 : HExpr :=
  let obj := HExpr.allocSimple [(0, HExpr.int 0)]
  HExpr.assign obj 0 (HExpr.int 1)

-- Example 4: Nested objects with arbitrary indices
def example4 : HExpr :=
  let inner := HExpr.allocSimple [(7, HExpr.int 42)]
  HExpr.allocSimple [(3, inner), (1, HExpr.true)]

-- Test evaluation
#eval do
  let (state1, result1) := eval example1
  IO.println s!"Example 1 result: {repr result1}"

  let (state2, result2) := eval example2
  IO.println s!"Example 2 result: {repr result2}"

  let (state3, result3) := eval example3
  IO.println s!"Example 3 result: {repr result3}"

  return ()

-- Helper function to run a heap expression and print results
def runExample (name : String) (expr : HExpr) : IO Unit := do
  let (state, result) := eval expr
  IO.println s!"{name}:"
  IO.println s!"  Expression: {repr expr}"
  IO.println s!"  Result: {repr result}"
  IO.println s!"  Heap state: {state.heapToString}"
  IO.println ""

-- Run all examples
def runAllExamples : IO Unit := do
  IO.println "=== Heap Dialect Examples ==="
  IO.println ""

  runExample "Simple Allocation" example1
  runExample "Field Access" example2
  runExample "Field Update" example3
  runExample "Nested Objects" example4

end Heap.Examples

#eval Heap.Examples.runAllExamples
