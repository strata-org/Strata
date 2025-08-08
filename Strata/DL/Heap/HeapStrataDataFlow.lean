import Strata.DL.Heap.HeapStrataEval
import Strata.DL.Heap.HeapDataFlow
import Strata.DL.DataFlow

/-! ## HeapStrataStatement DataFlow Implementation

Implementation of the DataFlow interface for HeapStrataStatement.
This handles statement-level data flows including external function calls.
-/

namespace Heap

open DataFlow

-- Helper function to remap generic DataFlow variable names to actual variable names
def remapDataFlowTargets (flows : List DataFlow) (actualTargetVar : String) : List DataFlow :=
  flows.map (fun flow =>
    match flow.target with
    | DataLocation.variable genericName =>
      -- Map generic names to actual variable name
      if genericName.startsWith "binary_op_result" ||
         genericName.startsWith "operation_result" ||
         genericName.startsWith "app_result" ||
         genericName.startsWith "deferred_op_result" ||
         genericName.startsWith "field_access_result" then
        { flow with target := DataLocation.variable actualTargetVar }
      else flow
    | _ => flow
  )

-- Helper function to remap object names in DataFlows for allocation operations
def remapObjectNames (flows : List DataFlow) (actualObjectName : String) : List DataFlow :=
  flows.map (fun flow =>
    match flow.target with
    | DataLocation.heapField objName fieldIndex =>
      if objName == "allocated_obj" then
        { flow with target := DataLocation.heapField actualObjectName fieldIndex }
      else flow
    | _ => flow
  )

-- Extract data flows from HeapStrataCommand
def extractCommandDataFlows (cmd : HeapStrataCommand) : List DataFlow :=
  match cmd with
  | .init name _ expr _ =>
    -- Variable initialization: let x = expr
    -- Data flows from expression to variable
    let exprFlows := DataFlowCapable.getDataFlows expr
    let remappedExprFlows := remapDataFlowTargets exprFlows name
    let objectRemappedFlows := remapObjectNames remappedExprFlows name
    let initFlow := DataFlow.mk
      (extractDataLocation expr)
      (DataLocation.variable name)
      "variable_init"
    initFlow :: objectRemappedFlows

  | .set name expr _ =>
    -- Variable assignment: x = expr
    -- Data flows from expression to variable
    let exprFlows := DataFlowCapable.getDataFlows expr
    let remappedExprFlows := remapDataFlowTargets exprFlows name
    let objectRemappedFlows := remapObjectNames remappedExprFlows name
    let assignFlow := DataFlow.mk
      (extractDataLocation expr)
      (DataLocation.variable name)
      "variable_assignment"
    assignFlow :: objectRemappedFlows

  | _ => []

-- TODO: Function calls now handled at language level, not in pure Imperative.Stmt
-- Extract data flows from function calls
-- def extractCallDataFlows (lhs : List String) (funcName : String) (args : List HExpr) : List DataFlow :=
--   -- Arguments flow to function parameters
--   let argFlows := args.mapIdx (fun idx arg =>
--     DataFlow.mk
--       (extractDataLocation arg)
--       (DataLocation.functionParam funcName idx)
--       "function_argument")

--   -- Function results flow to LHS variables
--   let resultFlows := lhs.map (fun varName =>
--     DataFlow.mk
--       (DataLocation.functionResult funcName)
--       (DataLocation.variable varName)
--       "function_result")

--   argFlows ++ resultFlows

-- Extract data flows from conditional statements
def extractConditionalDataFlows (cond : HExpr) (thenBlock elseBlock : Imperative.Block HeapStrataExpression (Imperative.Cmd HeapStrataExpression)) : List DataFlow :=
  -- For now, just extract flows from the condition
  -- Block-level flows would need more complex analysis
  DataFlowCapable.getDataFlows cond

-- Helper to extract data locations from HeapStrataStatement
def extractStatementDataFlows (stmt : HeapStrataStatement) : List DataFlow :=
  match stmt with
  | .cmd cmd => extractCommandDataFlows cmd
  -- TODO: Calls removed from pure Imperative.Stmt - handled at language level
  -- | .call lhs funcName args _ => extractCallDataFlows lhs funcName args
  | .ite cond thenBlock elseBlock _ => extractConditionalDataFlows cond thenBlock elseBlock
  | _ => []


-- Implementation of DataFlowCapable for HeapStrataStatement
instance : DataFlowCapable HeapStrataStatement where
  getDataFlows := extractStatementDataFlows

  getExternalCalls (stmt : HeapStrataStatement) : List (String × List DataLocation × List DataLocation) :=
    match stmt with
    -- TODO: Calls are now handled at language level, not in pure Imperative.Stmt
    -- Function calls will be handled by language-specific command types
    | _ => []

end Heap
