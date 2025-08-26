import Strata.DL.CallHeap.CallHeapStrataStatement
import Strata.DL.CallHigherOrder.CallHigherOrder

namespace CallHeapHigherOrder

-- Import the specific types we need from each Call-enabled dialect
open CallHeap (CallHeapStrataStatement CallHeapStrataCommand)
open CallHigherOrder (CallHigherOrderStrataStatement CallHigherOrderStrataCommand)

-- Combined statement type that can represent both CallHeap and CallHigherOrder operations
inductive CallHeapHigherOrderStrataStatement where
  | callHeap : CallHeapStrataStatement → CallHeapHigherOrderStrataStatement
  | callHigherOrder : CallHigherOrderStrataStatement → CallHeapHigherOrderStrataStatement

abbrev CallHeapHigherOrderStrataStatements := List CallHeapHigherOrderStrataStatement
-- Combined command type
inductive CallHeapHigherOrderStrataCommand where
  | callHeap : CallHeapStrataCommand → CallHeapHigherOrderStrataCommand
  | callHigherOrder : CallHigherOrderStrataCommand → CallHeapHigherOrderStrataCommand

-- Combined type system (use Heap types as base)
abbrev CallHeapHigherOrderTy := Heap.HMonoTy

-- Combined translation context
abbrev CallHeapHigherOrderTranslationContext := Generic.TranslationContext CallHeapHigherOrderStrataStatement CallHeapHigherOrderTy

end CallHeapHigherOrder
