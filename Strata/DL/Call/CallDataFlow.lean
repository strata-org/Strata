import Strata.DL.Call.CallCmd
import Strata.DL.DataFlow
import Strata.DL.Imperative.Stmt

namespace Call

open DataFlow

-- Extract data flows from CallCmd
def extractCallCommandDataFlows {P : Imperative.PureExpr} (cmd : CallCmd P) : List DataFlow :=
  match cmd with
  | .imperativeCmd imperativeCmd =>
    -- Delegate to imperative command handling (no data flows for basic commands)
    []
  | .directCall lhs funcName args =>
    -- Function call: lhs := funcName(args)
    -- Arguments flow to function parameters
    let argFlows := args.mapIdx (fun idx arg =>
      DataFlow.mk
        (DataLocation.external "unknown_arg")  -- Simplified for now
        (DataLocation.functionParam funcName idx)
        "function_argument")
    -- Function results flow to LHS variables
    let resultFlows := lhs.map (fun varName =>
      DataFlow.mk
        (DataLocation.functionResult funcName)
        (DataLocation.variable varName)
        "function_result")
    argFlows ++ resultFlows

-- Implementation of DataFlowCapable for CallCmd
instance {P : Imperative.PureExpr} : DataFlowCapable (CallCmd P) where
  getDataFlows := extractCallCommandDataFlows
  getExternalCalls cmd := match cmd with
    | .directCall lhs funcName args =>
      -- Return external call information
      let argLocs := args.map (fun _ => DataLocation.external "unknown_arg")
      let resultLocs := lhs.map (fun varName => DataLocation.variable varName)
      [(funcName, argLocs, resultLocs)]
    | _ => []

end Call
