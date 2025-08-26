/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Heap.HTy
import Strata.DL.Heap.HExpr
import Strata.DL.Heap.HState
import Strata.DL.Heap.HEval
import Strata.DL.Heap.HeapDataFlow
import Strata.DL.Imperative.Stmt
import Strata.DL.Generic.TranslationContext
---------------------------------------------------------------------

namespace Heap

/-! ## Heap Dialect

A simple heap dialect for Strata that extends the Lambda dialect with:
- Address types for heap references
- Object types with numeric field indices
- Allocation, field access, and field update operations
- Object-centric heap memory management

## Basic Usage

```lean
-- Create a simple object with arbitrary field indices
let obj := HExpr.allocSimple [(5, HExpr.int 42), (2, HExpr.int 24)]

-- Evaluate the allocation
let (state, result) := eval obj

-- Access a field
let access := HExpr.access obj 5
let (state2, fieldResult) := eval access state
```
-/
-- Define our expression system using Heap dialect
abbrev HeapStrataExpression : Imperative.PureExpr := {
  Ident := String,                    -- Simple string identifiers
  Expr := Heap.HExpr,                -- Heap expressions
  Ty := Heap.HMonoTy,                -- Heap types
  TyEnv := Map String Heap.HMonoTy,   -- Type environment
  EvalEnv := Heap.HState,            -- Heap state for evaluation
  EqIdent := inferInstance           -- DecidableEq for String
}

-- Statements parameterized by our heap expressions (pure Imperative commands only)
abbrev HeapStrataStatement := Imperative.Stmt HeapStrataExpression (Imperative.Cmd HeapStrataExpression)
abbrev HeapStrataStatements := List HeapStrataStatement
abbrev HeapStrataCommand := Imperative.Cmd HeapStrataExpression


-- We shouldn't be doing this in Strata anymore because Function calls are gonna be separate
-- Function definitions in the heap dialect (using generic StrataFunction)
--abbrev HeapStrataFunction := Generic.StrataFunction HeapStrataStatement Heap.HMonoTy
-- Translation context for heap functions (using generic TranslationContext)
--abbrev TranslationContext := Generic.TranslationContext HeapStrataStatement Heap.HMonoTy

end Heap
