import Strata.DL.Heap.HState
import Strata.DL.Heap.HEval
import Strata.DL.Lambda.LState
import Strata.DL.Heap.Heap

---------------------------------------------------------------------


namespace Heap
open Lambda (LState)

/-! ## HeapStrata Statement Evaluator

Simple evaluator for HeapStrata statements.
Handles variable declarations and assignments using the extended HState.
Now includes function definition storage and function call evaluation.
-/

-- Extended evaluation context with function storage
structure HeapEvalContext where
  hstate : HState

def HeapEvalContext.empty : HeapEvalContext :=
  { hstate := HState.empty }


mutual

-- Evaluate a single HeapStrata statement with context
partial def evalStatementWithContext (stmt : HeapStrataStatement) (ctx : HeapEvalContext) : HeapEvalContext :=
  match stmt with
  | .cmd (.init name ty expr _) =>
    -- Initialize a new variable
    dbg_trace s!"[DEBUG] Executing init: {name} : {repr ty} = {repr expr}"
    let (newState, value) := Heap.evalHExpr ctx.hstate expr
    dbg_trace s!"[DEBUG] Evaluated init expr to: {repr value}"
    let finalState := HState.setHeapVar newState name ty value
    { ctx with hstate := finalState }

  | .cmd (.set name expr _) =>
    -- Set an existing variable (or create if doesn't exist)
    dbg_trace s!"[DEBUG] Executing set: {name} = {repr expr}"
    let (newState, value) := Heap.evalHExpr ctx.hstate expr
    dbg_trace s!"[DEBUG] Evaluated set expr to: {repr value}"
    -- Try to get existing type, otherwise default to int
    let ty := match HState.getHeapVarType newState name with
      | some existingTy => existingTy
      | none => HMonoTy.int  -- Default fallback
    let finalState := HState.setHeapVar newState name ty value
    dbg_trace s!"[DEBUG] Set {name} to {repr value}"
    { ctx with hstate := finalState }

  -- TODO: Calls are now handled at language level, not in pure Imperative.Stmt
  -- | .call lhs funcName args _ =>
  --   -- Function call
  --   evalFunctionCall funcName args lhs ctx

  | .ite cond thenBlock elseBlock _ =>
    -- Conditional statement - evaluate condition and choose branch
    let (newState, condValue) := Heap.evalHExpr ctx.hstate cond
    -- Check if condition is true (simplified boolean evaluation)
    let conditionIsTrue := match condValue with
      | .lambda (.const "true" _) => true
      | .lambda (.const "false" _) => false
      | _ => false

    -- Execute the appropriate branch
    let newCtx := { ctx with hstate := newState }
    if conditionIsTrue then
      evalProgramWithContext thenBlock.ss newCtx
    else
      evalProgramWithContext elseBlock.ss newCtx

  | _ =>
    -- For other statement types, handle them directly in the context
    match stmt with
    | .cmd (.havoc name _) =>
      -- Havoc operation - set variable to unknown value (we'll use 0 as default)
      let finalState := HState.setHeapVar ctx.hstate name HMonoTy.int (HExpr.int 0)
      { ctx with hstate := finalState }
    | .cmd (.assert _ _ _) =>
      -- Assertion - for now, just ignore (assume it passes)
      ctx
    | .cmd (.assume _ _ _) =>
      -- Assumption - for now, just ignore
      ctx
    | .block _ _ _ =>
      -- Block statement - would need to handle nested statements
      -- For now, skip
      ctx
    | .goto _ _ =>
      -- Goto statement - not relevant for straight-line code
      ctx
    | _ =>
      -- Unknown statement type
      ctx

-- Evaluate a list of HeapStrata statements with context
partial def evalProgramWithContext (stmts : List HeapStrataStatement) (ctx : HeapEvalContext) : HeapEvalContext :=
  stmts.foldl (fun context stmt => evalStatementWithContext stmt context) ctx
  -- Evaluate a single PythonMidi statement

end

-- Convenience function to evaluate with empty initial state


-- Helper to get all Lambda variable names from LState
def getLambdaVarNames (lambdaState : LState String) : List String :=
  -- Collect variable names from all scopes
  lambdaState.state.foldl (fun acc scope =>
    acc ++ scope.keys
  ) []

-- Helper to lookup a variable in Lambda state (duplicate from HState for access)
def lookupInLambdaState (lambdaState : LState String) (name : String) : Option (Lambda.LExpr String) :=
  -- Search through the scope stack (most recent first)
  lambdaState.state.findSome? fun scope =>
    match scope.find? name with
    | some (_, expr) => some expr
    | none => none

-- Helper to extract heap object as JSON
-- Helper to convert string value to appropriate JSON type
def stringToJsonValue (s : String) : Lean.Json :=
  -- Try to parse as integer first
  match s.toInt? with
  | some n => Lean.Json.num (Lean.JsonNumber.fromInt n)
  | none =>
    -- Try to parse as boolean
    if s == "true" then Lean.Json.bool true
    else if s == "false" then Lean.Json.bool false
    else Lean.Json.str s  -- Default to string

-- Enhanced helper to extract concrete values from HExpr, handling heap objects
mutual
  partial def extractConcreteValueWithState (state : HState) (expr : HExpr) : Option Lean.Json :=
    match expr with
    | .lambda (Lambda.LExpr.const value _) =>
      some (stringToJsonValue value)  -- Simple constants
    | .address addr =>
      extractObjectAsJson state addr  -- Heap objects
    | .null =>
      some Lean.Json.null  -- Null values
    | _ => none  -- Other expressions not supported yet

  partial def extractObjectAsJson (state : HState) (addr : Address) : Option Lean.Json :=
    match state.getObject addr with
    | some obj =>
      -- Convert heap object (field index -> HExpr) to JSON object
      let fields := obj.toList
      let jsonFields := fields.filterMap fun (fieldIndex, fieldExpr) =>
        match extractConcreteValueWithState state fieldExpr with
        | some fieldJson =>
          -- Use field index as string key for now
          some (toString fieldIndex, fieldJson)
        | none => none

      -- Sort fields by key for consistency
      let sortedFields := jsonFields.toArray.qsort (fun a b => a.1 < b.1) |>.toList
      some (Lean.Json.mkObj sortedFields)
    | none => none

  -- Legacy function for backward compatibility
  partial def extractConcreteValue (expr : HExpr) : Option String :=
    match expr with
    | .lambda (Lambda.LExpr.const value _) => some value
    | _ => none
end

-- Evaluate translated program with functions
def evalTranslatedProgram (stmts : List HeapStrataStatement) : HeapEvalContext :=
  let evalCtx := HeapEvalContext.empty
  evalProgramWithContext stmts evalCtx

-- Helper to run and display results with context
def runAndShowWithContext (ctx : HeapEvalContext) : IO Unit := do
  let finalState := ctx.hstate
  IO.println "=== Evaluation Results ==="
  IO.println s!"Final state: {repr finalState}"

  -- Show heap variables
  IO.println s!"Heap variables: {finalState.getHeapVarNames}"
  for varName in finalState.getHeapVarNames do
    match finalState.getHeapVar varName with
    | some (ty, value) =>
      --IO.println s!"  {varName}: {repr ty} = {repr value}"
      IO.println s!"  {varName}: = {repr value}"
    | none =>
      IO.println s!"  {varName}: <not found>"

  -- Show Lambda variables
  let lambdaVars := getLambdaVarNames finalState.lambdaState
  IO.println s!"Lambda variables: {lambdaVars}"
  for varName in lambdaVars do
    match lookupInLambdaState finalState.lambdaState varName with
    | some expr =>
      IO.println s!"  {varName}: {repr expr}"
    | none =>
      IO.println s!"  {varName}: <not found>"

-- Helper to run and display results (legacy - for programs without functions)
def runAndShow (stmts : List HeapStrataStatement) : IO Unit := do
  let finalContext := evalProgramWithContext stmts HeapEvalContext.empty
  runAndShowWithContext finalContext

-- JSON output function with TranslationContext
def runAndShowJSONWithTranslation (stmts : List HeapStrataStatement) : IO Unit := do
  let finalContext := evalTranslatedProgram  stmts
  let finalState := finalContext.hstate

  let mut jsonFields : List (String × Lean.Json) := []

  -- Extract heap variables
  for varName in finalState.getHeapVarNames do
    match finalState.getHeapVar varName with
    | some (_, value) =>
      match extractConcreteValueWithState finalState value with
      | some jsonValue =>
        jsonFields := (varName, jsonValue) :: jsonFields
      | none => continue
    | none => continue

  -- Extract Lambda variables
  let lambdaVars := getLambdaVarNames finalState.lambdaState
  for varName in lambdaVars do
    match lookupInLambdaState finalState.lambdaState varName with
    | some expr =>
      match extractConcreteValueWithState finalState (.lambda expr) with
      | some jsonValue =>
        jsonFields := (varName, jsonValue) :: jsonFields
      | none => continue
    | none => continue

  -- Create JSON object and output (sorted for consistency)
  let sortedFields := jsonFields.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let jsonObj := Lean.Json.mkObj sortedFields
  IO.println jsonObj.compress  -- Use compress for compact output like {"x": 5, "y": 15}

-- New JSON output function for conformance testing (legacy - for programs without functions)
def runAndShowJSON (stmts : List HeapStrataStatement) : IO Unit := do
  let finalContext := evalProgramWithContext stmts HeapEvalContext.empty
  let finalState := finalContext.hstate

  let mut jsonFields : List (String × Lean.Json) := []

  -- Extract heap variables
  for varName in finalState.getHeapVarNames do
    match finalState.getHeapVar varName with
    | some (_, value) =>
      match extractConcreteValueWithState finalState value with
      | some jsonValue =>
        jsonFields := (varName, jsonValue) :: jsonFields
      | none => continue
    | none => continue

  -- Extract Lambda variables
  let lambdaVars := getLambdaVarNames finalState.lambdaState
  for varName in lambdaVars do
    match lookupInLambdaState finalState.lambdaState varName with
    | some expr =>
      match extractConcreteValueWithState finalState (.lambda expr) with
      | some jsonValue =>
        jsonFields := (varName, jsonValue) :: jsonFields
      | none => continue
    | none => continue

  -- Create JSON object and output (sorted for consistency)
  let sortedFields := jsonFields.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  let jsonObj := Lean.Json.mkObj sortedFields
  IO.println jsonObj.compress  -- Use compress for compact output like {"x": 5, "y": 15}


end Heap
