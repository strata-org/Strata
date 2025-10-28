/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Heap.HState
import Strata.DL.Heap.HExpr
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprEval

---------------------------------------------------------------------

namespace Heap

open Lambda (LExpr)

/-! ## Heap Expression Evaluation

Simple evaluator for heap expressions with numeric field indices.
Handles allocation, field access, and field updates.
Returns HExpr directly, following the Lambda dialect pattern.
-/

-- Heap expression evaluator with numeric field indices
mutual

partial def evalHExpr (state : HState) (expr : HExpr) : HState × HExpr :=
  match expr with
  | .lambda lexpr =>
    -- Special handling for variable references (fvar)
    match lexpr with
    | .fvar varName _ =>
      -- Check heap variables first (addresses, objects, mixed expressions)
      match state.getHeapVarValue varName with
      | some heapValue => (state, heapValue)
      | none =>
        -- Fall back to Lambda evaluation (will check lambdaState)
        let fuel := 100
        let evaluatedLExpr := LExpr.eval fuel state.lambdaState lexpr
        (state, .lambda evaluatedLExpr)
    | _ =>
      -- Other Lambda expressions - delegate to Lambda evaluator
      let fuel := 100
      let evaluatedLExpr := LExpr.eval fuel state.lambdaState lexpr
      (state, .lambda evaluatedLExpr)

  | .alloc objTy fields =>
    -- Simple allocation with the provided field mappings
    let (newState, addr) := state.alloc fields
    (newState, .address addr)

  | .deref addrExpr field =>
    -- First evaluate the address expression
    let (state1, addrResult) := evalHExpr state addrExpr
    match addrResult with
    | .address addr =>
      -- Get field value from the heap
      match state1.getField addr field with
      | some value => (state1, value)
      | none => (state1, .lambda (LExpr.const s!"error_field_{field}_not_found" none))
    | .null =>
      -- Null pointer dereference
      (state1, .lambda (LExpr.const "error_null_dereference" none))
    | _ =>
      -- Invalid address type
      (state1, .lambda (LExpr.const "error_invalid_address" none))

  | .assign addrExpr field valueExpr =>
    -- First evaluate the address expression
    let (state1, addrResult) := evalHExpr state addrExpr
    -- Then evaluate the value expression
    let (state2, valueResult) := evalHExpr state1 valueExpr

    match addrResult with
    | .address addr =>
      -- Update field in the heap
      match state2.setField addr field valueResult with
      | some newState => (newState, valueResult)
      | none => (state2, .lambda (LExpr.const s!"error_cannot_update_field_{field}" none))
    | .null =>
      -- Null pointer assignment
      (state2, .lambda (LExpr.const "error_null_assignment" none))
    | _ =>
      -- Invalid address type
      (state2, .lambda (LExpr.const "error_invalid_address_assignment" none))

  | .address addr =>
    -- Address values are already evaluated
    (state, expr)

  | .null =>
    -- Null is already evaluated
    (state, expr)

  | .deferredOp _ _ =>
    -- Deferred operations by themselves are canonical values (like Lambda's .op)
    (state, expr)

  | .app e1 e2 =>
    -- Handle application (including deferred operations)
    evalApp state expr e1 e2

  | .deferredIte guard consequent alternate =>
    -- Evaluate the guard first
    let (state1, guardVal) := evalHExpr state guard
    -- Try to short-circuit based on guard value
    match guardVal with
    | .lambda (LExpr.const "true" _) =>
      -- Guard is true, evaluate consequent
      evalHExpr state1 consequent
    | .lambda (LExpr.const "false" _) =>
      -- Guard is false, evaluate alternate
      evalHExpr state1 alternate
    | _ =>
      -- Guard isn't a simple boolean, try Lambda delegation
      let (state2, consVal) := evalHExpr state1 consequent
      let (state3, altVal) := evalHExpr state2 alternate
      match guardVal.toLambda?, consVal.toLambda?, altVal.toLambda? with
      | some g, some c, some a =>
        -- All parts can be converted to Lambda, delegate to Lambda evaluator
        let lambdaIte := LExpr.ite g c a
        let fuel := 100
        let result := LExpr.eval fuel state3.lambdaState lambdaIte
        (state3, .lambda result)
      | _, _, _ =>
        -- Some parts can't be converted to Lambda, keep as deferred
        (state3, .deferredIte guardVal consVal altVal)

-- Evaluate application expressions (following Lambda's evalApp pattern)
partial def evalApp (state : HState) (originalExpr e1 e2 : HExpr) : HState × HExpr :=
  let (state1, e1') := evalHExpr state e1
  let (state2, e2') := evalHExpr state1 e2
  match e1' with
  | .deferredOp "DynamicFieldAccess" _ =>
    -- First application to DynamicFieldAccess - return partially applied
    (state2, .app (.deferredOp "DynamicFieldAccess" none) e2')
  | .app (.deferredOp "DynamicFieldAccess" _) objExpr =>
    -- Second application to DynamicFieldAccess - now we can evaluate
    -- This handles obj[field] where field is dynamic
    evalDynamicFieldAccess state2 objExpr e2'
  | .deferredOp "DynamicFieldAssign" _ =>
    -- First application to DynamicFieldAssign - return partially applied
    (state2, .app (.deferredOp "DynamicFieldAssign" none) e2')
  | .app (.deferredOp "DynamicFieldAssign" _) objExpr =>
    -- Second application to DynamicFieldAssign - return partially applied
    (state2, .app (.app (.deferredOp "DynamicFieldAssign" none) objExpr) e2')
  | .app (.app (.deferredOp "DynamicFieldAssign" _) objExpr) fieldExpr =>
    -- Third application to DynamicFieldAssign - now we can evaluate
    -- This handles obj[field] = value where field is dynamic
    evalDynamicFieldAssign state2 objExpr fieldExpr e2'
  | .deferredOp "StringFieldAccess" _ =>
    -- First application to StringFieldAccess - return partially applied
    (state2, .app (.deferredOp "StringFieldAccess" none) e2')
  | .app (.deferredOp "StringFieldAccess" _) objExpr =>
    -- Second application to StringFieldAccess - return partially applied
    -- This handles str.fieldName where fieldName is a string literal
    evalStringFieldAccess state2 objExpr e2'
  | .deferredOp op _ =>
    -- First application to a deferred operation - return partially applied
    (state2, .app (.deferredOp op none) e2')
  | .app (.deferredOp op _) arg1 =>
    -- Second application to a binary operation - now we can evaluate
    evalBinaryOp state2 op arg1 e2'
  | .lambda (LExpr.abs _ body) =>
    -- Lambda abstraction application - delegate to Lambda evaluator
    match e2'.toLambda? with
    | some lambdaArg =>
      let lambdaApp := LExpr.app (LExpr.abs none body) lambdaArg
      let fuel := 100
      let result := LExpr.eval fuel state2.lambdaState lambdaApp
      (state2, .lambda result)
    | none =>
      -- Can't convert argument to Lambda
      (state2, .app e1' e2')
  | _ =>
    -- Other applications - keep as application
    (state2, .app e1' e2')

-- Handle dynamic field access: obj[field] where field is dynamic
partial def evalDynamicFieldAccess (state : HState) (objExpr fieldExpr : HExpr) : HState × HExpr :=
  -- First try to extract a numeric field index from the field expression
  match extractFieldIndex fieldExpr with
  | some fieldIndex =>
    -- We have a numeric field index, use regular deref
    evalHExpr state (.deref objExpr fieldIndex)
  | none =>
    -- Can't extract a numeric field index, return error
    (state, .lambda (LExpr.const "error_dynamic_field_access_failed" none))

-- Handle dynamic field assignment: obj[field] = value where field is dynamic
partial def evalDynamicFieldAssign (state : HState) (objExpr fieldExpr valueExpr : HExpr) : HState × HExpr :=
  -- First try to extract a numeric field index from the field expression
  match extractFieldIndex fieldExpr with
  | some fieldIndex =>
    -- We have a numeric field index, use regular assign
    evalHExpr state (.assign objExpr fieldIndex valueExpr)
  | none =>
    -- Can't extract a numeric field index, return error
    (state, .lambda (LExpr.const "error_dynamic_field_assign_failed" none))

-- Handle string field access: str.fieldName where fieldName is a string literal
partial def evalStringFieldAccess (state : HState) (objExpr fieldExpr : HExpr) : HState × HExpr :=
  match fieldExpr with
  | .lambda (LExpr.const key _) =>
    if key == "length" then
      -- Handle string length property
      match objExpr with
      | .lambda (LExpr.const s _) =>
        let len := s.length
        (state, .lambda (LExpr.const (toString len) (some Lambda.LMonoTy.int)))
      | _ =>
        -- Not a string value
        (state, .lambda (LExpr.const "error_not_a_string" none))
    else
      -- Unknown string property
      (state, .lambda (LExpr.const "error_unknown_string_property" none))
  | _ =>
    -- Field is not a string literal
    (state, .lambda (LExpr.const "error_non_literal_string_field" none))

-- Extract a numeric field index from an expression
partial def extractFieldIndex (expr : HExpr) : Option Nat :=
  match expr with
  | .lambda (LExpr.const s _) =>
    -- Try to parse the string as a natural number
    s.toNat?
  | _ => none

-- Handle fully applied binary operations
partial def evalBinaryOp (state : HState) (op : String) (arg1 arg2 : HExpr) : HState × HExpr :=
  match arg1.toLambda?, arg2.toLambda? with
  | some l1, some l2 =>
    -- Both arguments can be converted to Lambda - delegate to Lambda evaluator
    let lambdaOp := LExpr.app (LExpr.app (LExpr.op op none) l1) l2
    let fuel := 100
    let result := LExpr.eval fuel state.lambdaState lambdaOp
    (state, .lambda result)
  | _, _ =>
    -- Partial evaluation - keep as deferred operation
    (state, .app (.app (.deferredOp op none) arg1) arg2)

end

-- Convenience function for evaluation
def eval (expr : HExpr) (state : HState := HState.empty) : HState × HExpr :=
  evalHExpr state expr

-- Helper to create simple test expressions
namespace HExpr

-- Create a simple object allocation
def allocSimple (fields : List (Nat × HExpr)) : HExpr :=
  .alloc (HMonoTy.mkObj fields.length HMonoTy.int) fields

end HExpr

end Heap
