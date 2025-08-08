/-
CallHeap Strata Statement: Generic statements combining Call and Heap dialects in Strata
-/

import Strata.DL.Call.CallCmd
import Strata.DL.Heap.HExpr
import Strata.DL.Heap.HEval
import Strata.DL.Heap.Heap
import Strata.DL.Heap.HState
import Strata.DL.Heap.HTy
import Strata.DL.Imperative.Stmt
import Strata.DL.Generic.TranslationContext

---------------------------------------------------------------------

namespace CallHeap

open Heap
open Call
open Std (ToFormat Format format)

-- Define our expression system using Heap dialect
abbrev CallHeapStrataExpression : Imperative.PureExpr := HeapStrataExpression

-- Generic statements that combine Call dialect with Heap expressions
-- This is the target that languages like Python and TypeScript translate down to
abbrev CallHeapStrataStatement := Imperative.Stmt HeapStrataExpression (CallCmd HeapStrataExpression)
abbrev CallHeapStrataStatements := List CallHeapStrataStatement
abbrev CallHeapStrataCommand := CallCmd HeapStrataExpression

-- CallHeap-specific function and translation context using the generic framework
abbrev CallHeapStrataFunction := Generic.StrataFunction CallHeapStrataStatement Heap.HMonoTy
abbrev CallHeapTranslationContext := Generic.TranslationContext CallHeapStrataStatement Heap.HMonoTy

end CallHeap
