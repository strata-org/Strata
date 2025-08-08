import Lean

/-! ## DataFlow Interface

Generic interface for representing data flow between storage locations.
This abstracts away dialect-specific storage mechanisms (heap fields, function parameters, etc.)
and provides a uniform way for analyses to track data movement.
-/

namespace DataFlow

-- DataLocation abstracts storage locations across different dialects
inductive DataLocation where
  | variable : String → DataLocation                    -- Variable: x
  | heapField : String → Nat → DataLocation           -- Heap field: obj[5]  
  | dynamicField : String → String → DataLocation     -- Dynamic field: obj[key]
  | functionParam : String → Nat → DataLocation       -- Function parameter: func.param[0]
  | functionResult : String → DataLocation            -- Function return value: func.result
  | external : String → DataLocation                  -- External source: getUserInput()
  | literal : String → DataLocation                   -- Literal value: 42, "hello"
  deriving Repr, BEq

-- DataFlow represents movement of data from source to target
structure DataFlow where
  source : DataLocation
  target : DataLocation
  operation : String  -- "field_access", "assignment", "function_call", etc.
  deriving Repr

-- Core interface that dialects implement to expose their data flows
class DataFlowCapable (D : Type) where
  getDataFlows : D → List DataFlow
  getExternalCalls : D → List (String × List DataLocation × List DataLocation)  -- (funcName, args, results)

-- Helper functions for working with DataLocation
def DataLocation.toString : DataLocation → String
  | .variable name => s!"var:{name}"
  | .heapField objName fieldIndex => s!"heap:{objName}[{fieldIndex}]"
  | .dynamicField objName keyName => s!"heap:{objName}[{keyName}]"
  | .functionParam funcName paramIndex => s!"param:{funcName}[{paramIndex}]"
  | .functionResult funcName => s!"result:{funcName}"
  | .external funcName => s!"external:{funcName}"
  | .literal value => s!"literal:{value}"

def DataFlow.toString (df : DataFlow) : String :=
  s!"{df.source.toString} --{df.operation}--> {df.target.toString}"

end DataFlow
