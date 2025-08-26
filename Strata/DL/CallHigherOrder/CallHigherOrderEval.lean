import Strata.DL.CallHigherOrder.CallHigherOrder
import Strata.DL.HigherOrder.HigherOrderEval

namespace CallHigherOrder

open HigherOrder

-- Evaluation context for CallHigherOrder operations
structure CallHigherOrderEvalContext where
  higherOrderContext : HigherOrder.HOEvalContext

def CallHigherOrderEvalContext.empty : CallHigherOrderEvalContext :=
  { higherOrderContext := HigherOrder.HOEvalContext.empty }

mutual
-- Function call evaluation
partial def evalFunctionCall (funcName : String) (args : List HOExpr) (lhs : List String) (ctx : CallHigherOrderEvalContext) : CallHigherOrderEvalContext :=
  match ctx.higherOrderContext.functions.find? (fun f => f.name == funcName) with
  | none =>
    -- External function - store symbolic results in HOState
    let resultValue := s!"{funcName}_result"
    let newHOState := lhs.foldl (fun state varName => 
      HOState.setVar state varName (Lambda.LExpr.const resultValue none)
    ) ctx.higherOrderContext.hostate
    { ctx with higherOrderContext := { ctx.higherOrderContext with hostate := newHOState } }
  | some func =>
    -- Internal function - would need full evaluation (simplified for now)
    let resultValue := s!"{funcName}_internal_result"
    let newHOState := lhs.foldl (fun state varName => 
      HOState.setVar state varName (Lambda.LExpr.const resultValue none)
    ) ctx.higherOrderContext.hostate
    { ctx with higherOrderContext := { ctx.higherOrderContext with hostate := newHOState } }

-- Evaluate CallHigherOrder command
partial def evalCallHigherOrderCommand (cmd : CallHigherOrderStrataCommand) (ctx : CallHigherOrderEvalContext) : CallHigherOrderEvalContext :=
  match cmd with
  | .directCall lhs funcName args =>
    -- Direct function call
    evalFunctionCall funcName args lhs ctx
  | .imperativeCmd imperativeCmd =>
    -- Delegate to HigherOrder evaluator
    let stmt := Imperative.Stmt.cmd imperativeCmd
    let newHOContext := HigherOrder.evalStatementWithContext stmt ctx.higherOrderContext
    { ctx with higherOrderContext := newHOContext }

-- Evaluate CallHigherOrder statement
partial def evalCallHigherOrderStatement (stmt : CallHigherOrderStrataStatement) (ctx : CallHigherOrderEvalContext) : CallHigherOrderEvalContext :=
  match stmt with
  | .cmd cmd => evalCallHigherOrderCommand cmd ctx
  | .block _label body =>
    -- Evaluate block body
    body.ss.foldl (fun acc stmt => evalCallHigherOrderStatement stmt acc) ctx
  | _ =>
    -- Skip other statement types for now
    ctx

end

-- Evaluate a list of CallHigherOrder statements
def evalCallHigherOrderStatements (statements : List CallHigherOrderStrataStatement) (ctx : CallHigherOrderEvalContext) : CallHigherOrderEvalContext :=
  statements.foldl (fun acc stmt => evalCallHigherOrderStatement stmt acc) ctx

end CallHigherOrder
