import Strata.DL.HigherOrder.HigherOrder
import Strata.DL.HigherOrder.HOState
import Strata.DL.Lambda.LExprEval

namespace HigherOrder

open Lambda

-- Evaluation context for HigherOrder dialect
structure HOEvalContext where
  hostate : HOState
  functions : List HigherOrderStrataFunction := []

def HOEvalContext.empty : HOEvalContext :=
  { hostate := HOState.empty, functions := [] }

-- Helper to extract numeric value from HOExpr
def extractNumericValue (expr : HOExpr) : Option Int :=
  match expr with
  | .lambda (LExpr.const value _) => value.toInt?
  | _ => none

-- Helper to extract boolean value from HOExpr
def extractBooleanValue (expr : HOExpr) : Option Bool :=
  match expr with
  | .lambda (LExpr.const "true" _) => some true
  | .lambda (LExpr.const "false" _) => some false
  | .lambda (LExpr.const value _) =>
    match value.toInt? with
    | some 0 => some false
    | some _ => some true
    | none => none
  | _ => none

-- Main evaluator for HOExpr
mutual

partial def evalHOExprWithContext (ctx : HOEvalContext) (expr : HOExpr) : HOEvalContext × HOExpr :=
  match expr with
  | .lambda (LExpr.fvar name _) =>
    -- Variable reference - look up in state
    match HOState.getVar ctx.hostate name with
    | some lexpr => (ctx, .lambda lexpr)
    | none => (ctx, .const s!"undefined_variable_{name}")

  | .lambda lexpr =>
    -- Other lambda expressions - delegate to Lambda evaluator
    let fuel := 1000
    let evaluatedLExpr := LExpr.eval fuel ctx.hostate.lambdaState lexpr
    (ctx, .lambda evaluatedLExpr)

  | .app func arg =>
    -- Function application: f(arg)
    let (ctx1, funcResult) := evalHOExprWithContext ctx func
    let (ctx2, argResult) := evalHOExprWithContext ctx1 arg
    let (finalCtx, appResult) := evalApplicationWithContext ctx2 funcResult argResult
    (finalCtx, appResult)

  | .arith op left right =>
    -- Arithmetic operations
    let (ctx1, leftResult) := evalHOExprWithContext ctx left
    let (ctx2, rightResult) := evalHOExprWithContext ctx1 right
    let (finalCtx, arithResult) := evalArithmeticWithContext ctx2 op leftResult rightResult
    (finalCtx, arithResult)

  | .ite cond thenExpr elseExpr =>
    -- Conditional expression
    let (ctx1, condResult) := evalHOExprWithContext ctx cond
    let (finalCtx, iteResult) := evalConditionalWithContext ctx1 condResult thenExpr elseExpr
    (finalCtx, iteResult)

-- Function application evaluation
partial def evalApplicationWithContext (ctx : HOEvalContext) (funcExpr : HOExpr) (argExpr : HOExpr) : HOEvalContext × HOExpr :=
  match funcExpr with
  | .lambda (LExpr.abs _ body) =>
    -- Lambda abstraction: (λx. body) arg
    match argExpr with
    | .lambda argLExpr =>
      -- Perform β-reduction using Lambda dialect's substitution
      let substitutedBody := LExpr.subst argLExpr body
      -- Evaluate the substituted body
      evalHOExprWithContext ctx (.lambda substitutedBody)
    | _ =>
      (ctx, .const "error_invalid_argument_type")
  | _ =>
    (ctx, .const "error_not_a_function")

-- Arithmetic operation evaluation
partial def evalArithmeticWithContext (ctx : HOEvalContext) (op : String) (left : HOExpr) (right : HOExpr) : HOEvalContext × HOExpr :=
  let leftVal := extractNumericValue left
  let rightVal := extractNumericValue right
  match leftVal, rightVal with
  | some l, some r =>
    let result := match op with
      | "add" => l + r
      | "sub" => l - r
      | "mul" => l * r
      | "div" => if r != 0 then l / r else 0
      | "eq" => if l == r then 1 else 0
      | "lt" => if l < r then 1 else 0
      | "gt" => if l > r then 1 else 0
      | _ => 0
    (ctx, .const (toString result))
  | _, _ =>
    (ctx, .const "error_arithmetic_type_mismatch")

-- Conditional evaluation
partial def evalConditionalWithContext (ctx : HOEvalContext) (condExpr : HOExpr) (thenExpr : HOExpr) (elseExpr : HOExpr) : HOEvalContext × HOExpr :=
  let condVal := extractBooleanValue condExpr
  match condVal with
  | some true => evalHOExprWithContext ctx thenExpr
  | some false => evalHOExprWithContext ctx elseExpr
  | none => (ctx, .const "error_invalid_condition")

end

-- Evaluate a HigherOrder statement
def evalStatementWithContext (stmt : HigherOrderStrataStatement) (ctx : HOEvalContext) : HOEvalContext :=
  match stmt with
  | .cmd (.init name ty expr _) =>
    -- Initialize a new variable
    let (newCtx, value) := evalHOExprWithContext ctx expr
    match value with
    | .lambda lexpr =>
      let fuel := 1000
      let fullyEvaluated := LExpr.eval fuel newCtx.hostate.lambdaState lexpr
      let finalState := HOState.setVar newCtx.hostate name fullyEvaluated
      { newCtx with hostate := finalState }
    | _ => newCtx

  | .cmd (.set name expr _) =>
    -- Set an existing variable
    let (newCtx, value) := evalHOExprWithContext ctx expr
    match value with
    | .lambda lexpr =>
      let finalState := HOState.setVar newCtx.hostate name lexpr
      { newCtx with hostate := finalState }
    | _ => newCtx

  | _ => ctx

-- Evaluate a list of statements
def evalStatements (statements : List HigherOrderStrataStatement) (ctx : HOEvalContext) : HOEvalContext :=
  statements.foldl (fun acc stmt => evalStatementWithContext stmt acc) ctx

end HigherOrder
