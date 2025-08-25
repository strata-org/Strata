import Strata.DL.HeapHigherOrder.HeapHigherOrder
import Strata.DL.Heap.HeapStrataDataFlow
import Strata.DL.HigherOrder.HigherOrderDataFlow
import Strata.DL.DataFlow

namespace HeapHigherOrder

open DataFlow

-- Extract data flows from HeapHigherOrderStatement
def extractStatementDataFlows (stmt : HeapHigherOrderStatement) : List DataFlow :=
  match stmt with
  | .heapStmt heapStmt => 
    -- Delegate to Heap dialect DataFlow
    Heap.extractStatementDataFlows heapStmt
  | .higherOrderStmt hoStmt =>
    -- Delegate to HigherOrder dialect DataFlow  
    HigherOrder.extractStatementDataFlows hoStmt

-- DataFlowCapable instance for HeapHigherOrderStatement
instance : DataFlowCapable HeapHigherOrderStatement where
  getDataFlows := extractStatementDataFlows

  getExternalCalls := fun stmt =>
    match stmt with
    | .heapStmt heapStmt =>
      -- Delegate to Heap dialect external call detection
      DataFlowCapable.getExternalCalls heapStmt
    | .higherOrderStmt hoStmt =>
      -- Delegate to HigherOrder dialect external call detection
      DataFlowCapable.getExternalCalls hoStmt

end HeapHigherOrder
