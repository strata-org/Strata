import Strata.DL.Heap.HExpr
import Strata.DL.Heap.HState
import Strata.DL.Heap.Heap
import Strata.DL.CallHeap.CallHeapStrataStatement
import Strata.DL.Generic.TranslationContext
import Strata.DL.Call.CallCmd
import Strata.DL.Imperative.Stmt

namespace UninitializedFieldAccess

open Heap CallHeap

/-! ## Uninitialized Field Access Analysis

This module implements an analysis to detect when code tries to access fields
of objects before they have been initialized. It uses three-value logic to
handle uncertainty in control flow and aliasing.
-/

-- JSON output structures (same as ValueValidation)
structure Violation where
  object : String
  message : String
  deriving Lean.ToJson, Repr

structure AnalysisResult where
  violations : List Violation
  deriving Lean.ToJson, Repr

-- Three-value logic for field initialization state
inductive InitState
  | Initialized      -- Definitely initialized
  | Uninitialized    -- Definitely uninitialized
  | MaybeInitialized -- Possibly initialized (uncertain)
  deriving Repr, DecidableEq

-- Simple abstract value for unknown field indices
inductive AbstractFieldValue where
  | unknown : AbstractFieldValue

-- State for tracking initialized fields
structure AnalysisState where
  -- Map from addresses to maps of fields and their initialization states
  fieldStates : Std.HashMap Address (Std.HashMap Nat InitState)
  -- Map from variables to possible addresses they point to
  varAddrs : Std.HashMap String (List Address)
  -- Map from variables to integer values (for tracking integer variables)
  intVars : Std.HashMap String (Option Nat)
  -- Map from variables to abstract values (for tracking unknown values from external calls)
  symbolicVars : Std.HashMap String AbstractFieldValue
  -- Heap state for variable resolution and evaluation
  evalState : HState := HState.empty
  -- Function definitions available for analysis
  functions : Std.HashMap String CallHeapStrataFunction := {}
  -- Violations generated during analysis (structured)
  violations : List Violation
  -- Next fresh address to use
  nextAddr : Nat := 1

def AnalysisState.empty : AnalysisState :=
  { fieldStates := {}, varAddrs := {}, intVars := {}, symbolicVars := {}, evalState := HState.empty, functions := {}, violations := [], nextAddr := 1 }

-- Initialize analysis state with functions from TranslationContext
def AnalysisState.withFunctions (ctx : CallHeapTranslationContext) : AnalysisState :=
  let functionMap := ctx.functions.foldl (fun map func => map.insert func.name func) {}
  { AnalysisState.empty with functions := functionMap }

-- Generate a fresh address
def AnalysisState.freshAddr (state : AnalysisState) : (AnalysisState × Address) :=
  let addr := state.nextAddr
  let state' := { state with nextAddr := addr + 1 }
  (state', addr)

-- Join operation for merging initialization states (conservative)
def joinInitStates (s1 s2 : InitState) : InitState :=
  match s1, s2 with
  | InitState.Initialized, InitState.Initialized => InitState.Initialized
  | InitState.Uninitialized, InitState.Uninitialized => InitState.Uninitialized
  | _, _ => InitState.MaybeInitialized

-- Join operation for merging field state maps
def joinFieldStates (map1 map2 : Std.HashMap Nat InitState) : Std.HashMap Nat InitState :=
  -- Start with all fields from map1
  let result := map1

  -- For each field in map2, join with corresponding field in map1 if it exists
  map2.fold (fun acc field state =>
    match acc.get? field with
    | some existingState =>
        acc.insert field (joinInitStates existingState state)
    | none =>
        -- Field only in map2, add it directly
        acc.insert field state
  ) result

-- Helper function to merge lists without duplicates
def mergeLists {α} [BEq α] (l1 l2 : List α) : List α :=
  l1.foldl (fun acc x => if acc.contains x then acc else x :: acc) l2

-- Join operation for merging integer variable values
def joinIntVars (v1 v2 : Option Nat) : Option Nat :=
  match v1, v2 with
  | some n1, some n2 => if n1 == n2 then some n1 else none  -- Same value -> keep it, different values -> unknown
  | _, _ => none  -- If either is unknown, result is unknown

-- Merge states from different control flow paths
def mergeStates (s1 s2 : AnalysisState) : AnalysisState :=
  -- Create a new state
  let newState : AnalysisState := {
    fieldStates := {},
    varAddrs := {},
    intVars := {},
    symbolicVars := {},
    evalState := s1.evalState,  -- Keep the eval state from s1 (arbitrary choice)
    functions := s1.functions,  -- Keep functions from s1
    violations := s1.violations ++ s2.violations,
    nextAddr := max s1.nextAddr s2.nextAddr  -- Use the larger next address
  }

  -- Merge address sets for each variable
  let varAddrs := s1.varAddrs.fold (fun acc var addrs =>
    match s2.varAddrs.get? var with
    | some addrs2 =>
        -- Variable in both states, merge address lists
        acc.insert var (mergeLists addrs addrs2)
    | none =>
        -- Variable only in s1
        acc.insert var addrs
  ) s2.varAddrs

  -- Merge field states for each address
  let fieldStates := s1.fieldStates.fold (fun acc addr fields =>
    match s2.fieldStates.get? addr with
    | some fields2 =>
        -- Address in both states, merge field states
        acc.insert addr (joinFieldStates fields fields2)
    | none =>
        -- Address only in s1
        acc.insert addr fields
  ) s2.fieldStates

  -- Merge integer variable values
  let intVars := s1.intVars.fold (fun acc var value =>
    match s2.intVars.get? var with
    | some value2 =>
        -- Variable in both states, merge values
        acc.insert var (joinIntVars value value2)
    | none =>
        -- Variable only in s1
        acc.insert var value
  ) s2.intVars

  { newState with fieldStates := fieldStates, varAddrs := varAddrs, intVars := intVars }

-- Try to extract an integer value from a constant expression
def extractIntValue (expr : HExpr) : Option Nat :=
  match expr with
  | .lambda (Lambda.LExpr.const s _) =>
    -- Try to parse the string as a natural number
    match s.toNat? with
    | some n => some n
    | none => none
  | _ => none

-- Try to evaluate an expression to get its integer value
def evaluateToInt (expr : HExpr) (state : AnalysisState) : Option Nat :=
  -- First try to evaluate the expression using the HEval evaluator
  let (evalState, result) := Heap.evalHExpr state.evalState expr

  -- Extract integer value from the result
  match result with
  | .lambda (Lambda.LExpr.const s _) =>
    -- Try to parse the string as a natural number
    match s.toNat? with
    | some n => some n
    | none => none
  | _ => none

-- Try to resolve a field index from an expression
def resolveFieldIndex (expr : HExpr) (state : AnalysisState) : Option Nat :=
  match expr with
  | .lambda (.fvar varName _) =>
    -- First check if it's a symbolic variable (from unknown function call)
    match state.symbolicVars.get? varName with
    | some .unknown => none  -- Symbolic variable - can't resolve to concrete index
    | none =>
      -- Not symbolic, try to resolve as concrete value
      -- If it's a variable reference, first check if it's an integer variable in our static analysis
      match state.intVars.get? varName |>.join with
      | some n => some n
      | none =>
        -- If not found in static analysis, try to evaluate it using the HEval evaluator
        let (evalState, result) := Heap.evalHExpr state.evalState expr

        -- Extract integer value from the result
        match result with
        | .lambda (Lambda.LExpr.const s _) =>
          -- Try to parse the string as a natural number
          s.toNat?
        | _ => none
  | _ =>
    -- Try to extract an integer value or evaluate the expression
    match extractIntValue expr with
    | some n => some n
    | none =>
      -- Try to evaluate the expression using the HEval evaluator
      let (evalState, result) := Heap.evalHExpr state.evalState expr

      -- Extract integer value from the result
      match result with
      | .lambda (Lambda.LExpr.const s _) =>
        -- Try to parse the string as a natural number
        s.toNat?
      | _ => none

-- Extract object name from an address expression
def extractObjectName (addrExpr : HExpr) : String :=
  match addrExpr with
  | .lambda (.fvar varName _) => varName
  | .address addr => s!"object_at_{addr}"
  | _ => "unknown_object"

-- Check if a field is initialized with a constant field index
def checkFieldInitializedConst (addrExpr : HExpr) (field : Nat) (state : AnalysisState) : AnalysisState :=
  let objectName := extractObjectName addrExpr
  match addrExpr with
  | .address addr =>
    -- Direct address - check if field is initialized
    match state.fieldStates.get? addr with
    | some fields =>
      match fields.get? field with
      | some InitState.Initialized =>
          -- Field is definitely initialized, no violation
          state
      | some InitState.Uninitialized =>
          -- Field is definitely uninitialized, definite violation
          let violation := Violation.mk objectName s!"Field {field} accessed before initialization at address {addr}"
          { state with violations := violation :: state.violations }
      | some InitState.MaybeInitialized =>
          -- Field might be initialized, potential violation
          let violation := Violation.mk objectName s!"Field {field} might be accessed before initialization at address {addr}"
          { state with violations := violation :: state.violations }
      | none =>
          -- Field not tracked, assume uninitialized
          let violation := Violation.mk objectName s!"Field {field} accessed before initialization at address {addr}"
          { state with violations := violation :: state.violations }
    | none =>
      -- Unknown object
      let violation := Violation.mk objectName s!"Access to field {field} of unknown object at address {addr}"
      { state with violations := violation :: state.violations }

  | .lambda (.fvar varName _) =>
    -- Variable - check all possible addresses it could point to
    match state.varAddrs.get? varName with
    | some addrs =>
      if addrs.isEmpty then
        -- Variable exists but doesn't point to any objects
        let violation := Violation.mk varName s!"Variable {varName} doesn't point to any objects but field {field} is accessed"
        { state with violations := violation :: state.violations }
      else
        -- Check initialization state across all possible addresses
        let allStates := addrs.map (fun addr =>
          match state.fieldStates.get? addr with
          | some fields => fields.get? field |>.getD InitState.Uninitialized
          | none => InitState.Uninitialized
        )

        -- If any address has the field uninitialized, warn
        if allStates.any (· == InitState.Uninitialized) then
          let violation := Violation.mk varName s!"Field {field} may be accessed before initialization in variable {varName}"
          { state with violations := violation :: state.violations }
        -- If all addresses have the field maybe initialized, warn with lower severity
        else if allStates.all (· == InitState.MaybeInitialized) then
          let violation := Violation.mk varName s!"Field {field} might be accessed before initialization in variable {varName}"
          { state with violations := violation :: state.violations }
        else state
    | none =>
      -- Unknown variable
      let violation := Violation.mk varName s!"Access to field {field} of unknown variable {varName}"
      { state with violations := violation :: state.violations }

  | _ =>
    -- Other expressions - conservative violation
    let violation := Violation.mk objectName s!"Access to field {field} of complex expression with unknown initialization state"
    { state with violations := violation :: state.violations }

-- Check if a field is initialized with a variable field index
def checkFieldInitializedVar (addrExpr : HExpr) (fieldExpr : HExpr) (state : AnalysisState) : AnalysisState :=
  -- Try to resolve the field index
  match resolveFieldIndex fieldExpr state with
  | some field =>
    -- Field index resolved, now check if it's initialized
    checkFieldInitializedConst addrExpr field state
  | none =>
    -- Couldn't resolve field index - check if it's because of symbolic variable
    let objectName := extractObjectName addrExpr
    let violationMessage := match fieldExpr with
      | .lambda (.fvar varName _) =>
        match state.symbolicVars.get? varName with
        | some .unknown => s!"Field {varName} is unknown when accessing in {objectName}"
        | none => s!"Access to unknown field index in object {objectName}"
      | _ => s!"Access to unknown field index in object {objectName}"

    let violation := Violation.mk objectName violationMessage
    { state with violations := violation :: state.violations }

-- Mark a field as initialized with a constant field index
def markFieldInitializedConst (addrExpr : HExpr) (field : Nat) (state : AnalysisState) : AnalysisState :=
  match addrExpr with
  | .address addr =>
    -- Direct address - mark field as initialized
    let fields := state.fieldStates.get? addr |>.getD {}
    let fields' := fields.insert field InitState.Initialized
    { state with fieldStates := state.fieldStates.insert addr fields' }

  | .lambda (.fvar varName _) =>
    -- Variable - mark field as initialized for all possible addresses
    match state.varAddrs.get? varName with
    | some addrs =>
      let state' := addrs.foldl (fun s addr =>
        let fields := s.fieldStates.get? addr |>.getD {}
        let fields' := fields.insert field InitState.Initialized
        { s with fieldStates := s.fieldStates.insert addr fields' }
      ) state
      state'
    | none => state

  | _ => state

-- Mark a field as initialized with a variable field index
def markFieldInitializedVar (addrExpr : HExpr) (fieldExpr : HExpr) (state : AnalysisState) : AnalysisState :=
  -- Try to resolve the field index
  match resolveFieldIndex fieldExpr state with
  | some field =>
    -- Field index resolved, now mark it as initialized
    markFieldInitializedConst addrExpr field state
  | none =>
    -- Couldn't resolve field index, can't mark as initialized
    -- This is a conservative approach - we could mark all fields as maybe initialized
    state

-- Handle object allocation
def analyzeAlloc (fields : List (Nat × HExpr)) (state : AnalysisState) : (AnalysisState × Address) :=
  -- Generate a fresh address
  let (state', addr) := state.freshAddr

  -- Create field state map for the new object
  let fieldMap := Std.HashMap.empty

  -- Mark provided fields as initialized
  let fieldMap' := fields.foldl (fun map (idx, _) =>
    map.insert idx InitState.Initialized
  ) fieldMap

  -- Update state with the new object
  let state'' := { state' with fieldStates := state'.fieldStates.insert addr fieldMap' }

  -- Also update the evaluation state
  let (evalState, _) := state''.evalState.alloc fields
  let state''' := { state'' with evalState := evalState }

  (state''', addr)

-- Update variable to address mapping
def updateVarAddr (name : String) (addr : Address) (state : AnalysisState) : AnalysisState :=
  let addrs := state.varAddrs.get? name |>.getD []
  let addrs' := if addrs.contains addr then addrs else addr :: addrs
  { state with varAddrs := state.varAddrs.insert name addrs' }

-- Copy address mappings from source variable to target variable
def copyVarAddrs (target : String) (source : String) (state : AnalysisState) : AnalysisState :=
  match state.varAddrs.get? source with
  | some sourceAddrs =>
    -- Get current target addresses (if any)
    let targetAddrs := state.varAddrs.get? target |>.getD []
    -- Merge source addresses into target addresses (avoiding duplicates)
    let newAddrs := mergeLists targetAddrs sourceAddrs
    -- Update target variable with merged addresses
    { state with varAddrs := state.varAddrs.insert target newAddrs }
  | none => state  -- Source variable has no addresses, nothing to copy

-- Set an integer variable value
def setIntVar (name : String) (value : Option Nat) (state : AnalysisState) : AnalysisState :=
  { state with intVars := state.intVars.insert name value }

-- Update the evaluation state with a variable assignment
def updateEvalState (name : String) (expr : HExpr) (state : AnalysisState) : AnalysisState :=
  -- Evaluate the expression
  let (evalState, result) := Heap.evalHExpr state.evalState expr

  -- Update the evaluation state with the variable assignment
  let newEvalState := HState.setHeapVar evalState name HMonoTy.int result

  -- Return the updated state
  { state with evalState := newEvalState }

-- Forward declaration for mutual recursion
mutual

-- Main analysis function for expressions
partial def analyzeExpr (expr : HExpr) (state : AnalysisState) : AnalysisState :=
  match expr with
  | .deref addrExpr field =>
    -- First analyze the address expression
    let state' := analyzeExpr addrExpr state
    -- Then check if the field is initialized
    checkFieldInitializedConst addrExpr field state'

  | .assign addrExpr field valueExpr =>
    -- First analyze the address expression
    let state' := analyzeExpr addrExpr state
    -- Then analyze the value expression
    let state'' := analyzeExpr valueExpr state'
    -- Finally mark the field as initialized
    markFieldInitializedConst addrExpr field state''

  | .alloc _ fields =>
    -- First analyze all field value expressions
    let state' := fields.foldl (fun s (_, e) => analyzeExpr e s) state
    -- Then allocate the object
    let (state'', _) := analyzeAlloc fields state'
    -- Return the updated state
    state''

  | .app e1 e2 =>
    -- Check for special operations
    match e1 with
    --| .deferredOp "DynamicFieldAccess" _ =>
    --  -- This is a dynamic field access: DynamicFieldAccess(obj, field)
    --  -- First analyze the object expression
    --  let state' := analyzeExpr e2 state
    --  -- For now, we'll just use a placeholder and assume it's uninitialized
    --  let objectName := extractObjectName e2
    --  let violation := Violation.mk objectName "Dynamic field access with unknown field index"
    --  { state' with violations := violation :: state'.violations }

    | .app (.deferredOp "DynamicFieldAccess" _) objExpr =>
      -- This is a dynamic field access: DynamicFieldAccess(obj, field)
      -- First analyze the object expression
      let state' := analyzeExpr objExpr state
      -- Then analyze the field expression
      let state'' := analyzeExpr e2 state'
      -- Check if the field is initialized
      checkFieldInitializedVar objExpr e2 state''

    --| .deferredOp "DynamicFieldAssign" _ =>
    --  -- This is a dynamic field assignment: DynamicFieldAssign(obj, field, value)
    --  -- First analyze the object expression
    --  let state' := analyzeExpr e2 state
    --  -- For now, we'll just use a placeholder and assume it's initialized
    --  state'

    | .app (.deferredOp "DynamicFieldAssign" _) objExpr =>
      -- This is a dynamic field assignment: DynamicFieldAssign(obj, field, value)
      -- First analyze the object expression
      let state' := analyzeExpr objExpr state
      -- Then analyze the field expression
      let state'' := analyzeExpr e2 state'
      -- For now, we'll just use a placeholder and assume it's initialized
      state''

    | .app (.app (.deferredOp "DynamicFieldAssign" _) objExpr) fieldExpr =>
      -- This is a dynamic field assignment: DynamicFieldAssign(obj, field, value)
      -- First analyze the object expression
      let state' := analyzeExpr objExpr state
      -- Then analyze the field expression
      let state'' := analyzeExpr fieldExpr state'
      -- Then analyze the value expression
      let state''' := analyzeExpr e2 state''
      -- Mark the field as initialized
      markFieldInitializedVar objExpr fieldExpr state'''

    | _ =>
      -- Regular function application
      -- Analyze both expressions
      let state' := analyzeExpr e1 state
      analyzeExpr e2 state'

  | .deferredIte guard consequent alternate =>
    -- Analyze the guard
    let state' := analyzeExpr guard state
    -- Analyze both branches
    let thenState := analyzeExpr consequent state'
    let elseState := analyzeExpr alternate state'
    -- Merge the results
    mergeStates thenState elseState

  | _ => state  -- Other expressions don't affect field initialization

-- Analyze a CallHeap command
partial def analyzeCallHeapCmd (cmd : CallHeapStrataCommand) (state : AnalysisState) : AnalysisState :=
  match cmd with
  | .imperativeCmd (Imperative.Cmd.init name _ expr ..) =>
    -- Analyze the expression
    let state' := analyzeExpr expr state
    -- Update the evaluation state
    let state'' := updateEvalState name expr state'
    -- Handle different types of expressions
    match expr with
    | .alloc _ fields =>
      -- Object allocation - update variable mapping
      let (state''', addr) := analyzeAlloc fields state''
      updateVarAddr name addr state'''
    | .lambda (.fvar sourceName _) =>
      -- Variable assignment (e.g., x_alias = x) - copy address mappings
      let state''' := copyVarAddrs name sourceName state''
      -- Also copy integer value if it exists
      match state''.intVars.get? sourceName with
      | some value => setIntVar name value state'''
      | none => state'''
    | .app (.app (.deferredOp "DynamicFieldAccess" _) objExpr) fieldExpr =>
      -- This is a dynamic field access: DynamicFieldAccess(obj, field)
      -- Try to resolve the field index
      match resolveFieldIndex expr state'' with
      | some fieldValue =>
        -- Field index resolved, store it in the integer variables
        setIntVar name (some fieldValue) state''
      | none =>
        -- Try to evaluate the expression using the HEval evaluator
        let (evalState, result) := Heap.evalHExpr state''.evalState expr
        -- Extract integer value from the result
        match result with
        | .lambda (Lambda.LExpr.const s _) =>
          -- Try to parse the string as a natural number
          match s.toNat? with
          | some n => setIntVar name (some n) { state'' with evalState := evalState }
          | none => { state'' with evalState := evalState }
        | _ => state''
    | _ =>
      -- For other expressions, try to extract an integer constant
      match extractIntValue expr with
      | some n => setIntVar name (some n) state''
      | none => state''

  | .imperativeCmd (Imperative.Cmd.set name expr ..) =>
    -- Analyze the expression
    let state' := analyzeExpr expr state
    -- Update the evaluation state
    let state'' := updateEvalState name expr state'
    -- Handle different types of expressions
    match expr with
    | .alloc _ fields =>
      -- Object allocation - update variable mapping
      let (state''', addr) := analyzeAlloc fields state''
      updateVarAddr name addr state'''
    | .lambda (.fvar sourceName _) =>
      -- Variable assignment (e.g., x_alias = x) - copy address mappings
      let state''' := copyVarAddrs name sourceName state''
      -- Also copy integer value if it exists
      match state''.intVars.get? sourceName with
      | some value => setIntVar name value state'''
      | none => state'''
    | .app (.app (.deferredOp "DynamicFieldAccess" _) objExpr) fieldExpr =>
      -- This is a dynamic field access: DynamicFieldAccess(obj, field)
      -- Try to resolve the field index
      match resolveFieldIndex expr state'' with
      | some fieldValue =>
        -- Field index resolved, store it in the integer variables
        setIntVar name (some fieldValue) state''
      | none =>
        -- Try to evaluate the expression using the HEval evaluator
        let (evalState, result) := Heap.evalHExpr state''.evalState expr
        -- Extract integer value from the result
        match result with
        | .lambda (Lambda.LExpr.const s _) =>
          -- Try to parse the string as a natural number
          match s.toNat? with
          | some n => setIntVar name (some n) { state'' with evalState := evalState }
          | none => { state'' with evalState := evalState }
        | _ => state''
    | _ =>
      -- For other expressions, try to extract an integer constant
      match extractIntValue expr with
      | some n => setIntVar name (some n) state''
      | none => state''

  | _ => state  -- Other commands don't affect field initialization

-- Analyze a HeapMidi statement
partial def analyzeHeapStrataStmt (stmt : CallHeapStrataStatement) (state : AnalysisState) : AnalysisState :=
  match stmt with
  | .cmd cmd =>
    match cmd with
    | .imperativeCmd imperativeCmd =>
      analyzeCallHeapCmd cmd state
    | .directCall lhs funcName args =>
      -- Function call analysis
      -- First analyze all argument expressions
      let state' := args.foldl (fun s arg => analyzeExpr arg s) state

      -- Look up the function definition
    match state'.functions.get? funcName with
    | some funcDef =>
      -- Analyze the function body (interprocedural analysis)
      -- For now, we'll do a simplified analysis that assumes:
      -- 1. Function parameters don't alias with caller variables
      -- 2. Function calls may modify any field state to MaybeInitialized
      -- 3. Return values are conservatively assumed to be MaybeInitialized

      -- Analyze function body with a fresh state
      let funcState := analyzeCallHeapBlock { ss := funcDef.body } state'

      -- Merge function analysis results back (conservatively)
      -- For now, we'll just add any violations from the function analysis
      { state' with violations := state'.violations ++ funcState.violations }

    | none =>
      -- Unknown function - mark all LHS variables as unknown
      dbg_trace s!"[DEBUG] Unknown function '{funcName}' - marking {lhs} as symbolic"
      let newSymbolicVars := lhs.foldl (fun vars varName =>
        vars.insert varName .unknown
      ) state'.symbolicVars

      { state' with symbolicVars := newSymbolicVars }

  | .ite cond thenBlock elseBlock _ =>
    -- Analyze the condition
    let state' := analyzeExpr cond state
    -- Analyze both branches
    let thenState := analyzeCallHeapBlock thenBlock state'
    let elseState := analyzeCallHeapBlock elseBlock state'
    -- Merge the results
    mergeStates thenState elseState

  | .block _ block _ =>
    -- Analyze the block
    analyzeCallHeapBlock block state

  | _ => state  -- Other statements don't affect field initialization

-- Analyze a CallHeap block of statements
partial def analyzeCallHeapBlock (block : Imperative.Block CallHeapStrataExpression CallHeapStrataCommand) (state : AnalysisState) : AnalysisState :=
  block.ss.foldl (fun s stmt => analyzeHeapStrataStmt stmt s) state

-- Entry point for analyzing CallHeap programs
partial def analyzeCallHeapProgram (ctx : CallHeapTranslationContext) (stmts : List CallHeapStrataStatement) : AnalysisResult :=
  let initialState := AnalysisState.withFunctions ctx
  let finalState := stmts.foldl (fun state stmt => analyzeHeapStrataStmt stmt state) initialState
  AnalysisResult.mk finalState.violations

end
