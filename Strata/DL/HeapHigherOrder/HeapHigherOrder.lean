import Strata.DL.Heap.Heap
import Strata.DL.HigherOrder.HigherOrder

namespace HeapHigherOrder

-- Combined statement type that can handle both Heap and HigherOrder operations
inductive HeapHigherOrderStatement where
  | heapStmt : Heap.HeapStrataStatement → HeapHigherOrderStatement
  | higherOrderStmt : HigherOrder.HigherOrderStrataStatement → HeapHigherOrderStatement

end HeapHigherOrder
