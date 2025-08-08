/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Call.CallCmd

namespace Call

/-! ## Call Dialect Evaluator

Generic evaluator for the Call dialect. This provides the structure for
evaluating calls, but the actual call semantics are provided by the
specific dialect that uses Call (e.g., Heap dialect).
-/

-- Typeclass for dialects that can handle function calls
class CallEvaluator (State : Type) (P : Imperative.PureExpr) where
  -- Evaluate a direct function call
  evalDirectCall : (lhs : List String) → (funcName : String) → (args : List P.Expr) → State → State
  
  -- Evaluate an imperative command (delegate to the base dialect)
  evalImperativeCmd : Imperative.Cmd P → State → State

-- Generic evaluator for CallCmd
def evalCallCmd [CallEvaluator State P] (cmd : CallCmd P) (state : State) : State :=
  match cmd with
  | .imperativeCmd imperativeCmd =>
    -- Delegate to the base dialect evaluator
    CallEvaluator.evalImperativeCmd imperativeCmd state
  | .directCall lhs funcName args =>
    -- Use the dialect-specific call evaluator
    CallEvaluator.evalDirectCall lhs funcName args state

-- Generic evaluator for CallStatement
def evalCallStatement [CallEvaluator State P] (stmt : CallStatement P) (state : State) : State :=
  match stmt with
  | .cmd cmd => evalCallCmd cmd state
  | .ite cond thenBlock elseBlock =>
    -- For control flow, we need the dialect to provide condition evaluation
    -- This is a limitation - control flow evaluation is dialect-specific
    -- For now, we'll just skip this (each dialect should provide its own statement evaluator)
    state
  | .loop guard measure invariant body =>
    -- Similar issue - loop evaluation is dialect-specific
    state
  | .block _label body =>
    -- Evaluate block body
    body.ss.foldl (fun acc stmt => evalCallStatement stmt acc) state
  | .goto _label =>
    -- Goto is not handled in this simple evaluator
    state

-- Evaluate a list of call statements
def evalCallProgram [CallEvaluator State P] (statements : List (CallStatement P)) (initialState : State) : State :=
  statements.foldl (fun acc stmt => evalCallStatement stmt acc) initialState

end Call
