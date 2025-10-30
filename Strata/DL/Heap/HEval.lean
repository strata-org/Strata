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
  | .deferredOp "LengthAccess" _ =>
    -- First application to LengthAccess - return partially applied
    (state2, .app (.deferredOp "LengthAccess" none) e2')
  | .app (.deferredOp "LengthAccess" _) objExpr =>
    -- Second application to LengthAccess - evaluate
    evalLengthAccess state2 objExpr e2'
  | .deferredOp "FieldDelete" _ =>
    -- First application to FieldDelete - return partially applied
    (state2, .app (.deferredOp "FieldDelete" none) e2')
  | .app (.deferredOp "FieldDelete" _) objExpr =>
    -- Second application to FieldDelete - now we can evaluate
    -- This handles delete obj[field] where field is dynamic
    evalFieldDelete state2 objExpr e2'

  -- ArraySlice(obj, start?, end?) handling
  | .deferredOp "ArraySlice" _ =>
    -- First application: capture the array object
    (state2, .app (.deferredOp "ArraySlice" none) e2')
  | .app (.deferredOp "ArraySlice" _) objExpr =>
    -- Second application: capture start
    (state2, .app (.app (.deferredOp "ArraySlice" none) objExpr) e2')
  | .app (.app (.deferredOp "ArraySlice" _) objExpr) startExpr =>
    -- Third application: we have obj, start, and end -> evaluate
    evalArraySlice state2 objExpr startExpr e2'

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

-- Handle field deletion: delete obj[field]
partial def evalFieldDelete (state : HState) (objExpr fieldExpr : HExpr) : HState × HExpr :=
  -- First try to extract a numeric field index from the field expression
  match extractFieldIndex fieldExpr with
  | some fieldIndex =>
    -- We have a numeric field index, delete the field
    match objExpr with
    | .address addr =>
      -- Delete field from the object at this address
      match state.deleteField addr fieldIndex with
      | some newState => (newState, objExpr)  -- Return the object address
      | none => (state, .lambda (LExpr.const s!"error_cannot_delete_field_{fieldIndex}" none))
    | _ =>
      -- First evaluate the object expression to get an address
      let (state1, objVal) := evalHExpr state objExpr
      match objVal with
      | .address addr =>
        match state1.deleteField addr fieldIndex with
        | some newState => (newState, objVal)
        | none => (state1, .lambda (LExpr.const s!"error_cannot_delete_field_{fieldIndex}" none))
      | _ =>
        (state1, .lambda (LExpr.const "error_invalid_address_for_delete" none))
  | none =>
    -- Can't extract a numeric field index, return error
    (state, .lambda (LExpr.const "error_field_delete_failed" none))

-- Handle Array.prototype.slice semantics
partial def evalArraySlice (state : HState) (objExpr startExpr endExpr : HExpr) : HState × HExpr :=
  -- Ensure we have an address for the array object
  let (state1, objVal) := evalHExpr state objExpr
  -- Evaluate start/end arguments to simplify (handle negatives, computed exprs)
  let (state2, startVal) := evalHExpr state1 startExpr
  let (state3, endVal) := evalHExpr state2 endExpr
  let someAddr? : Option Nat := match objVal with
    | .address addr => some addr
    | _ => none
  match someAddr? with
  | none => (state3, .lambda (LExpr.const "error_array_slice_invalid_object" none))
  | some addr =>
    match state3.heap.get? addr with
    | none => (state3, .lambda (LExpr.const "error_array_slice_invalid_address" none))
    | some obj =>
      let len : Nat := obj.size
      -- Helper to extract integer from Lambda const
      let extractInt : HExpr → Option Int := fun e =>
        match e with
        | .lambda (LExpr.const s _) => s.toInt?
        | _ => none
      let resolveIndex (arg : HExpr) (defaultVal : Int) : Nat :=
        let i : Int := match arg with
          | .null => defaultVal
          | _ => (extractInt arg).getD defaultVal
        let i' : Int := if i < 0 then i + Int.ofNat len else i
        let clamped : Int :=
          if i' < 0 then 0
          else if i' > Int.ofNat len then Int.ofNat len
          else i'
        Int.toNat clamped
      let startIdx : Nat := resolveIndex startVal 0
      let endIdx   : Nat := resolveIndex endVal (Int.ofNat len)
      let finalStart := startIdx
      let finalEnd := if endIdx < startIdx then startIdx else endIdx
      -- Collect values in [finalStart, finalEnd) and reindex from 0
      let rec collect (j : Nat) (i : Nat) (acc : List (Nat × HExpr)) : List (Nat × HExpr) :=
        if i ≥ finalEnd then acc.reverse
        else
          match state3.getField addr i with
          | some v => collect (j+1) (i+1) ((j, v) :: acc)
          | none   => collect j (i+1) acc
      let outFields := collect 0 finalStart []
      -- Allocate a new array with these fields
      evalHExpr state3 (.alloc (HMonoTy.mkObj outFields.length HMonoTy.int) outFields)

-- Handle length access for both strings and arrays
partial def evalLengthAccess (state : HState) (objExpr fieldExpr : HExpr) : HState × HExpr :=
  match fieldExpr with
  | .lambda (LExpr.const key _) =>
    if key == "length" then
      match objExpr with
      | .lambda (LExpr.const s _) =>
        -- String length
        let len := s.length
        (state, .lambda (LExpr.const (toString len) (some Lambda.LMonoTy.int)))
      | .address addr =>
        -- Array length
        match state.heap.get? addr with
        | some obj =>
          let len := obj.size
          (state, .lambda (LExpr.const (toString len) (some Lambda.LMonoTy.int)))
        | none =>
          (state, .lambda (LExpr.const "error_invalid_address" none))
      | _ =>
        (state, .lambda (LExpr.const "error_not_string_or_array" none))
    else
      (state, .lambda (LExpr.const "error_unknown_length_property" none))
  | _ =>
    (state, .lambda (LExpr.const "error_non_literal_field" none))

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
