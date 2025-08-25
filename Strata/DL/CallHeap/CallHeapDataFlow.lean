import Strata.DL.CallHeap.CallHeapStrataStatement
import Strata.DL.Call.CallDataFlow
import Strata.DL.Heap.HeapStrataDataFlow
import Strata.DL.DataFlow

namespace CallHeap

open DataFlow Heap Call

-- Extract data flows from CallHeapStrataStatement by delegating to constituent dialects
def extractCallHeapStatementDataFlows (stmt : CallHeapStrataStatement) : List DataFlow :=
  match stmt with
  | .cmd cmd =>
    match cmd with
    | .imperativeCmd imperativeCmd =>
      -- Pure imperative commands (init, set, havoc) - delegate to Heap dialect
      Heap.extractCommandDataFlows imperativeCmd
    | .directCall lhs funcName args =>
      -- Function calls - delegate to Call dialect
      Call.extractCallCommandDataFlows cmd
  | .ite cond thenBlock elseBlock _ =>
    -- Conditional statements - just extract flows from condition for now
    DataFlowCapable.getDataFlows cond
  | _ =>
    -- TODO: Implement loop handling
    panic! "data flow analysis not implemented yet"

-- Implementation of DataFlowCapable for CallHeapStrataStatement
instance : DataFlowCapable CallHeapStrataStatement where
  getDataFlows := extractCallHeapStatementDataFlows

  getExternalCalls stmt := match stmt with
    | .cmd cmd => DataFlowCapable.getExternalCalls cmd
    | _ => []

end CallHeap
