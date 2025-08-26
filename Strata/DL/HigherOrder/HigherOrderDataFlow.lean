import Strata.DL.HigherOrder.HigherOrder
import Strata.DL.DataFlow

namespace HigherOrder

open DataFlow

-- Helper function to remap generic DataFlow variable names to actual variable names
def remapDataFlowTargets (flows : List DataFlow) (actualTargetVar : String) : List DataFlow :=
  flows.map (fun flow =>
    match flow.target with
    | DataLocation.variable genericName =>
      -- Map generic names to actual variable name
      if genericName.startsWith "app_result" ||
         genericName.startsWith "arith_" ||
         genericName.startsWith "ite_result" then
        { flow with target := DataLocation.variable actualTargetVar }
      else flow
    | _ => flow
  )

-- Helper function to find function references in an expression and create flows from their results
def extractFunctionResultFlows (expr : HOExpr) (targetVar : String) : List DataFlow :=
  match expr with
  | HOExpr.lambda (Lambda.LExpr.fvar funcName _) =>
    -- Direct function reference - create flow from its result
    [DataFlow.mk
      (DataLocation.functionResult funcName)
      (DataLocation.variable targetVar)
      "function_result_flow"]
  | HOExpr.app func arg =>
    -- Nested application - extract flows from both function and argument
    let funcFlows := extractFunctionResultFlows func targetVar
    let argFlows := extractFunctionResultFlows arg targetVar
    funcFlows ++ argFlows
  | _ => []

-- Implementation of DataFlowCapable for HigherOrder expressions
instance : DataFlowCapable HOExpr where
  getDataFlows (expr : HOExpr) : List DataFlow :=
    match expr with
    | .lambda _ =>
      -- Lambda expressions don't create data flows by themselves
      []
    | .app func arg =>
      -- Function application: f(arg) - handled at statement level
      []
    | .arith op left right =>
      -- Arithmetic operations: left op right
      -- Data flows from both operands to result
      [
        DataFlow.mk
          (HOExpr.extractDataLocation left)
          (DataLocation.variable s!"arith_{op}_result")
          s!"arithmetic_{op}",
        DataFlow.mk
          (HOExpr.extractDataLocation right)
          (DataLocation.variable s!"arith_{op}_result")
          s!"arithmetic_{op}"
      ]
    | .ite cond thenExpr elseExpr =>
      -- Conditional expression: if cond then thenExpr else elseExpr
      -- Data flows from both branches to result
      [
        DataFlow.mk
          (HOExpr.extractDataLocation thenExpr)
          (DataLocation.variable "ite_result")
          "conditional_then",
        DataFlow.mk
          (HOExpr.extractDataLocation elseExpr)
          (DataLocation.variable "ite_result")
          "conditional_else"
      ]

  getExternalCalls (expr : HOExpr) : List (String × List DataLocation × List DataLocation) :=
    -- HigherOrder expressions don't directly represent external calls
    -- They would be handled at the HigherOrderStrataStatement level
    []

-- Extract function name from HOExpr
def extractFunctionName (expr : HOExpr) : Option String :=
  match expr with
  | .lambda (Lambda.LExpr.fvar name _) => some name
  | .app funcExpr _ => extractFunctionName funcExpr
  | _ => none

-- Extract function calls from expressions
def extractFunctionCallFromExpr (expr : HOExpr) (resultVar : String) : List (String × List DataLocation × List DataLocation) :=
  match expr with
  | .app (HOExpr.lambda (Lambda.LExpr.fvar funcName _)) arg =>
    dbg_trace s!"[DEBUG] Simple function call: {funcName} -> {resultVar}"
    [(funcName, [HOExpr.extractDataLocation arg], [DataLocation.variable resultVar])]
  | .app funcExpr arg =>
    match funcExpr with
    | HOExpr.lambda (Lambda.LExpr.fvar funcName _) =>
      dbg_trace s!"[DEBUG] Function call with lambda: {funcName} -> {resultVar}"
      [(funcName, [HOExpr.extractDataLocation arg], [DataLocation.variable resultVar])]
    | _ =>
      dbg_trace s!"[DEBUG] Complex function application - trying to extract function name"
      []
  | HOExpr.lambda (Lambda.LExpr.fvar funcName _) =>
    -- Direct function reference (no arguments)
    dbg_trace s!"[DEBUG] Direct function reference: {funcName} -> {resultVar}"
    [(funcName, [], [DataLocation.variable resultVar])]
  | _ =>
    dbg_trace s!"[DEBUG] Expression is not a function call"
    []

-- Extract data flows from HigherOrderStrataCommand
def extractCommandDataFlows (cmd : HigherOrderStrataCommand) : List DataFlow :=
  match cmd with
  | .init name _ expr _ =>
    -- Variable initialization: let x = expr
    let exprFlows := DataFlowCapable.getDataFlows expr
    let remappedExprFlows := remapDataFlowTargets exprFlows name

    -- For function applications, create flows from function results (not arguments)
    let functionFlows := match expr with
      | .app func arg =>
        dbg_trace s!"[DEBUG] Function application assignment: {name} = f(...)"
        -- Look for function references in the expression and create flows from their results
        let flows := extractFunctionResultFlows expr name
        flows.map (fun flow =>
          dbg_trace s!"[DEBUG] Creating flow from function result: {flow.source.toString} -> {name}"
          flow
        )
      | _ => []

    let initFlow := DataFlow.mk
      (HOExpr.extractDataLocation expr)
      (DataLocation.variable name)
      "variable_init"

    initFlow :: remappedExprFlows ++ functionFlows

  | .set name expr _ =>
    -- Variable assignment: x = expr
    let exprFlows := DataFlowCapable.getDataFlows expr
    let remappedExprFlows := remapDataFlowTargets exprFlows name

    -- For function applications, create flows from function results (not arguments)
    let functionFlows := match expr with
      | .app func arg =>
        dbg_trace s!"[DEBUG] Function application assignment: {name} = f(...)"
        -- Look for function references in the expression and create flows from their results
        let flows := extractFunctionResultFlows expr name
        flows.map (fun flow =>
          dbg_trace s!"[DEBUG] Creating flow from function result: {flow.source.toString} -> {name}"
          flow
        )
      | _ => []

    let assignFlow := DataFlow.mk
      (HOExpr.extractDataLocation expr)
      (DataLocation.variable name)
      "variable_assignment"

    assignFlow :: remappedExprFlows ++ functionFlows

  | _ => []

-- Extract data flows from HigherOrderStrataStatement
def extractStatementDataFlows (stmt : HigherOrderStrataStatement) : List DataFlow :=
  match stmt with
  | .cmd cmd => extractCommandDataFlows cmd
  | _ => []

-- DataFlowCapable instance for HigherOrderStrataStatement
instance : DataFlowCapable HigherOrderStrataStatement where
  getDataFlows := extractStatementDataFlows
  
  getExternalCalls := fun stmt =>
    match stmt with
    | .cmd cmd =>
      dbg_trace s!"[DEBUG] Checking command for function calls"
      -- Check if the command contains function calls
      match cmd with
      | .init varName _ expr _ =>
        dbg_trace s!"[DEBUG] Checking init command for variable: {varName}"
        extractFunctionCallFromExpr expr varName
      | .set varName expr _ =>
        dbg_trace s!"[DEBUG] Checking set command for variable: {varName}"
        extractFunctionCallFromExpr expr varName
      | _ =>
        dbg_trace s!"[DEBUG] Command is not an init/set (assignment)"
        []
    | _ =>
      dbg_trace s!"[DEBUG] Statement is not a command"
      []

end HigherOrder
