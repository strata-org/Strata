import Strata.DL.Heap.HExpr
import Strata.DL.DataFlow
import Strata.DL.Lambda.LExpr

/-! ## HeapStrata DataFlow Implementation

Implementation of the DataFlow interface for the HeapStrata dialect.
This translates heap-specific operations (field access, assignment, allocation)
into abstract data flows that analyses can work with generically.
-/

namespace Heap

open DataFlow
open Lambda (LExpr)

-- Helper function to extract object name from HExpr
def extractObjectName (expr : HExpr) : String :=
  match expr with
  | .lambda (.fvar name _) => name
  | _ => "unknown_obj"

-- Helper function to extract data location from any HExpr
def extractDataLocation (expr : HExpr) : DataLocation :=
  match expr with
  | .lambda (.fvar name _) => DataLocation.variable name
  | .lambda (.const value _) => DataLocation.literal value
  | .deref objExpr fieldIndex =>
    let objName := extractObjectName objExpr
    DataLocation.heapField objName fieldIndex
  | .address addr => DataLocation.literal (toString addr)
  | .null => DataLocation.literal "null"
  | _ => DataLocation.literal "unknown"

-- Helper function to extract variable name from lambda expression
def extractVariableName (expr : HExpr) : Option String :=
  match expr with
  | .lambda (.fvar name _) => some name
  | _ => none

-- Implementation of DataFlowCapable for HeapStrata
instance : DataFlowCapable HExpr where
  getDataFlows (expr : HExpr) : List DataFlow :=
    match expr with
    | .deref objExpr fieldIndex =>
      -- Static field access: obj[5]
      -- Data flows from heap field to result
      let objName := extractObjectName objExpr
      [DataFlow.mk
        (DataLocation.heapField objName fieldIndex)
        (DataLocation.variable "field_access_result")
        "field_access"]

    | .assign objExpr fieldIndex valueExpr =>
      -- Field assignment: obj[5] = value
      -- Data flows from value to heap field
      let objName := extractObjectName objExpr
      let valueLoc := extractDataLocation valueExpr
      [DataFlow.mk
        valueLoc
        (DataLocation.heapField objName fieldIndex)
        "field_assignment"]

    | .alloc _ fields =>
      -- Object allocation: {1: value1, 2: value2, ...}
      -- Data flows from field values to heap fields
      fields.map (fun (fieldIndex, valueExpr) =>
        DataFlow.mk
          (extractDataLocation valueExpr)
          (DataLocation.heapField "allocated_obj" fieldIndex)
          "object_allocation")

    | .app e1 e2 =>
      -- Application (could be operations or deferred operations)
      -- Check for special deferred operations
      match e1 with
      | .deferredOp "DynamicFieldAccess" _ =>
        -- Dynamic field access: obj[variable]
        let objName := extractObjectName e2
        [DataFlow.mk
          (DataLocation.dynamicField objName "dynamic_key")
          (DataLocation.variable "dynamic_access_result")
          "dynamic_field_access"]
      | .app (.deferredOp "DynamicFieldAccess" _) objExpr =>
        -- Fully applied dynamic field access: DynamicFieldAccess(obj, key)
        let objName := extractObjectName objExpr
        let keyName := match extractVariableName e2 with
          | some name => name
          | none => "unknown_key"
        [DataFlow.mk
          (DataLocation.dynamicField objName keyName)
          (DataLocation.variable "dynamic_access_result")
          "dynamic_field_access"]
      | .app (.app (.deferredOp "DynamicFieldAssign" _) objExpr) indexExpr =>
        -- Dynamic field assignment: DynamicFieldAssign(obj, index, value)
        let objName := extractObjectName objExpr
        let keyName := match extractVariableName indexExpr with
          | some name => name
          | none => "unknown_key"
        let valueLoc := extractDataLocation e2
        [DataFlow.mk
          valueLoc
          (DataLocation.dynamicField objName keyName)
          "dynamic_field_assignment"]
      | .deferredOp opName _ =>
        -- Arithmetic and other operations: op(operand)
        -- Data flows from operand to result
        let operandLoc := extractDataLocation e2
        [DataFlow.mk
          operandLoc
          (DataLocation.variable "operation_result")
          s!"operation_{opName}"]
      | .app (.deferredOp opName _) leftOperand =>
        -- Binary operations: op(left, right)
        -- Data flows from both operands to result
        let leftLoc := extractDataLocation leftOperand
        let rightLoc := extractDataLocation e2
        [DataFlow.mk
          leftLoc
          (DataLocation.variable "binary_op_result")
          s!"binary_op_{opName}",
         DataFlow.mk
          rightLoc
          (DataLocation.variable "binary_op_result")
          s!"binary_op_{opName}"]
      | _ =>
        -- Regular application - data flows from both operands to result
        [DataFlow.mk
          (extractDataLocation e1)
          (DataLocation.variable "app_result")
          "application",
         DataFlow.mk
          (extractDataLocation e2)
          (DataLocation.variable "app_result")
          "application"]

    | .lambda lexpr =>
      -- Lambda expressions don't create data flows by themselves
      []

    | .address _ | .null =>
      -- Address literals don't create data flows
      []

    | .deferredOp opName _ =>
      -- Deferred operations that haven't been applied yet
      -- These will create data flows when they get applied in .app cases above
      -- But some operations might be used directly, so create a placeholder flow
      match opName with
      | "DynamicFieldAccess" | "DynamicFieldAssign" =>
        -- These are handled specially in .app cases
        []
      | _ =>
        -- Other operations might be used directly
        [DataFlow.mk
          (DataLocation.literal "operation_input")
          (DataLocation.variable "deferred_op_result")
          s!"deferred_{opName}"]

    | .deferredIte guard consequent alternate =>
      -- Conditional expression - data flows from branches to result
      [DataFlow.mk
        (extractDataLocation consequent)
        (DataLocation.variable "ite_result")
        "conditional_then",
       DataFlow.mk
        (extractDataLocation alternate)
        (DataLocation.variable "ite_result")
        "conditional_else"]

  getExternalCalls (expr : HExpr) : List (String × List DataLocation × List DataLocation) :=
    -- HeapStrata doesn't directly represent external calls
    -- They would be handled at the HeapStrataStatement level
    []

end Heap
