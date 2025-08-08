/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Call.CallCmd
import Strata.DL.Heap.HExpr

namespace Call

/-! ## CallCapable Typeclass

Typeclass for statement types that can handle function calls.
This allows generic analyses and operations to work across different
languages that support calls.
-/

-- Typeclass for statements that support function calls
class CallCapable (Stmt : Type) where
  -- Create a simple function call (no return value)
  simpleCall : String → List Heap.HExpr → Stmt
  
  -- Create a function call with return values
  call : List String → String → List Heap.HExpr → Stmt
  
  -- Inspection methods for analyses
  getCallInfo : Stmt → Option (List String × String × List Heap.HExpr)  -- (lhs, funcName, args)
  
  -- Check if this statement is a call
  isCall : Stmt → Bool
  
  -- Extract the underlying imperative statement if possible
  asImperativeStmt : Stmt → Option (Imperative.Stmt (Imperative.Cmd Heap.HExpr))

-- Default implementation for Call dialect statements
instance : CallCapable (CallStatement Heap.HExpr) where
  simpleCall funcName args := 
    CallStatement.simpleCall funcName args
    
  call lhs funcName args := 
    CallStatement.call lhs funcName args
    
  getCallInfo stmt := match stmt with
    | .cmd (.directCall lhs funcName args) => some (lhs, funcName, args)
    | _ => none
    
  isCall stmt := match stmt with
    | .cmd (.directCall _ _ _) => true
    | _ => false
    
  asImperativeStmt stmt := match stmt with
    | .cmd (.imperativeCmd cmd) => some (.cmd cmd)
    | .ite cond thenb elseb => 
      -- Convert blocks by filtering out calls (for now)
      let thenStmts := thenb.ss.filterMap (fun s => match s with
        | .cmd (.imperativeCmd cmd) => some (.cmd cmd)
        | _ => none)
      let elseStmts := elseb.ss.filterMap (fun s => match s with  
        | .cmd (.imperativeCmd cmd) => some (.cmd cmd)
        | _ => none)
      some (.ite cond ⟨thenStmts⟩ ⟨elseStmts⟩)
    | .while cond body =>
      let bodyStmts := body.ss.filterMap (fun s => match s with
        | .cmd (.imperativeCmd cmd) => some (.cmd cmd)
        | _ => none)
      some (.while cond ⟨bodyStmts⟩)
    | .block label body =>
      let bodyStmts := body.ss.filterMap (fun s => match s with
        | .cmd (.imperativeCmd cmd) => some (.cmd cmd)
        | _ => none)
      some (.block label ⟨bodyStmts⟩)
    | _ => none

end Call
