import Strata.DL.CallHigherOrder.CallHigherOrder
import Strata.DL.HigherOrder.HigherOrderDataFlow
import Strata.DL.DataFlow

namespace CallHigherOrder

def extractStatementDataFlows (stmt: CallHigherOrderStrataStatement) : List DataFlow.DataFlow :=
  match stmt with
  | .cmd (.directCall lhs funcName args) =>
    -- Function call: extract flows from arguments and create flows to results
    let argFlows := args.flatMap (fun arg => DataFlow.DataFlowCapable.getDataFlows arg)
    let resultFlows := lhs.map (fun varName =>
      DataFlow.DataFlow.mk
        (DataFlow.DataLocation.functionResult funcName)
        (DataFlow.DataLocation.variable varName)
        "function_call_result"
    )
    argFlows ++ resultFlows
  | .cmd (.imperativeCmd imperativeCmd) =>
    -- Delegate to HigherOrder DataFlow for imperative commands
    let hoStmt : HigherOrder.HigherOrderStrataStatement := Imperative.Stmt.cmd imperativeCmd
    HigherOrder.extractStatementDataFlows hoStmt
  | _ => []

-- DataFlowCapable instance for CallHigherOrder statements
instance : DataFlow.DataFlowCapable CallHigherOrderStrataStatement where
  getDataFlows := extractStatementDataFlows

  getExternalCalls := fun stmt =>
    match stmt with
    | .cmd (.directCall lhs funcName args) =>
      -- Direct function call
      let argLocations := args.map HigherOrder.HOExpr.extractDataLocation
      let resultLocations := lhs.map DataFlow.DataLocation.variable
      [(funcName, argLocations, resultLocations)]
    | .cmd (.imperativeCmd imperativeCmd) =>
      -- Delegate to HigherOrder for imperative commands
      let hoStmt : HigherOrder.HigherOrderStrataStatement := Imperative.Stmt.cmd imperativeCmd
      DataFlow.DataFlowCapable.getExternalCalls hoStmt
    | _ => []

end CallHigherOrder
