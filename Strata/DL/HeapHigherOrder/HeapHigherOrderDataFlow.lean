import Strata.DL.HeapHigherOrder.HeapHigherOrder
import Strata.DL.CallHeap.CallHeapDataFlow
import Strata.DL.CallHigherOrder.CallHigherOrderDataFlow
import Strata.DL.DataFlow

namespace CallHeapHigherOrder

def getDataFlowsForCallHeapHigherOrderStatement (stmt: CallHeapHigherOrderStrataStatement) : List DataFlow.DataFlow :=
  match stmt with
    | .callHeap callHeapStmt => CallHeap.extractCallHeapStatementDataFlows callHeapStmt
    | .callHigherOrder callHOStmt => CallHigherOrder.extractStatementDataFlows callHOStmt

-- Combined dialect implements DataFlowCapable by delegating to the constituent dialects
instance : DataFlow.DataFlowCapable CallHeapHigherOrderStrataStatement where
  getDataFlows := getDataFlowsForCallHeapHigherOrderStatement

  getExternalCalls stmt := match stmt with
    | .callHeap callHeapStmt => DataFlow.DataFlowCapable.getExternalCalls callHeapStmt  
    | .callHigherOrder callHOStmt => DataFlow.DataFlowCapable.getExternalCalls callHOStmt

end CallHeapHigherOrder
