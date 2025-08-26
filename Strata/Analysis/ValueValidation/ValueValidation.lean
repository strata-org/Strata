import Strata.DL.Heap.HExpr
import Strata.DL.Heap.HState
import Strata.DL.Heap.Heap
import Strata.DL.CallHeap.CallHeapStrataStatement
import Strata.DL.CallHeap.CallHeapEvaluator
import Strata.DL.Generic.TranslationContext
import Strata.DL.Call.CallCmd
import Strata.DL.Imperative.Stmt

/-! ## Value Validation Analysis for CallHeap

Validates that all values stored in object fields satisfy a user-defined validation predicate.
Requires a user-provided `is_valid(value)` function.
-/

namespace ValueValidation

open Heap CallHeap

-- JSON output structures
structure Violation where
  object : String
  message : String
  deriving Lean.ToJson, Repr

structure AnalysisResult where
  violations : List Violation
  deriving Lean.ToJson, Repr

-- State for tracking validation violations
structure ValidationState where
  -- Evaluation context with functions for calling is_valid
  evalContext : CallHeapEvalContext
  -- Validation violations found during analysis
  violations : List Violation

def ValidationState.empty : ValidationState :=
  { evalContext := CallHeapEvalContext.empty, violations := [] }

-- Initialize validation state with functions from TranslationContext
def ValidationState.withFunctions (ctx : CallHeapTranslationContext) : ValidationState :=
  let evalCtx := ctx.functions.foldl (fun evalCtx func => evalCtx.addFunction func) CallHeapEvalContext.empty
  { ValidationState.empty with evalContext := evalCtx }

-- Try to extract a natural number value from an expression
def extractNatValue (expr : HExpr) (state : ValidationState) : Option Nat :=
  match expr with
  | .lambda (Lambda.LExpr.const s _) => s.toNat?
  | _ =>
    -- Try to evaluate the expression using the heap evaluator
    let (evalState, result) := Heap.evalHExpr state.evalContext.hstate expr
    match result with
    | .lambda (Lambda.LExpr.const s _) => s.toNat?
    | _ => none

-- Call the user-defined is_valid function to validate a value
def callIsValid (value : Nat) (state : ValidationState) : Bool :=
  -- Create argument expression for the value
  let valueExpr := HExpr.lambda (Lambda.LExpr.const (toString value) (some (Lambda.LMonoTy.tcons "int" [])))
  let args := [valueExpr]

  -- Call the is_valid function
  let resultContext := evalFunctionCall "is_valid" args ["validation_result"] state.evalContext

  -- Extract the result
  let (tempState, returnValue) := Heap.evalHExpr resultContext.hstate (HExpr.lambda (Lambda.LExpr.fvar "validation_result" none))

  -- Check if the result is true
  match returnValue with
  | HExpr.lambda (Lambda.LExpr.const "true" _) => true
  | HExpr.lambda (Lambda.LExpr.const "1" _) => true
  | _ => false

-- Extract object name from an address expression
def extractObjectName (addrExpr : HExpr) : String :=
  match addrExpr with
  | .lambda (.fvar varName _) => varName
  | _ => "unknown_object"

-- Validate a single value using the user-defined is_valid function
def validateValue (value : Nat) (objectName : String) (context : String) (state : ValidationState) : ValidationState :=
  if callIsValid value state then
    state
  else
    let message := s!"{context}: value {value} fails is_valid() check"
    let violation := Violation.mk objectName message
    { state with violations := violation :: state.violations }

-- Validate field assignment
def validateFieldAssignment (addrExpr : HExpr) (field : Nat) (valueExpr : HExpr) (state : ValidationState) : ValidationState :=
  match extractNatValue valueExpr state with
  | some value =>
    let objectName := extractObjectName addrExpr
    let context := s!"Field {field} assignment"
    validateValue value objectName context state
  | none => state

-- Validate object allocation
def validateObjectAlloc (fields : List (Nat × HExpr)) (objectName : String) (state : ValidationState) : ValidationState :=
  fields.foldl (fun s (fieldIndex, valueExpr) =>
    match extractNatValue valueExpr s with
    | some value =>
      let context := s!"Object allocation field {fieldIndex}"
      validateValue value objectName context s
    | none => s
  ) state

-- Analyze a Heap expression
partial def analyzeExpr (expr : HExpr) (state : ValidationState) : ValidationState :=
  match expr with
  | .assign addrExpr field valueExpr =>
    validateFieldAssignment addrExpr field valueExpr state
  | .alloc _ fields =>
    state  -- Handled in analyzeCommand when we know the object name
  | _ => state

-- Analyze a CallHeap command
partial def analyzeCommand (cmd : CallHeapStrataCommand) (state : ValidationState) : ValidationState :=
  match cmd with
  | .imperativeCmd (Imperative.Cmd.init name _ expr ..) =>
    let state' := analyzeExpr expr state
    match expr with
    | .alloc _ fields =>
      validateObjectAlloc fields name state'
    | _ => state'
  | .imperativeCmd (Imperative.Cmd.set name expr ..) =>
    analyzeExpr expr state
  | _ => state

-- Analyze a CallHeap statement
partial def analyzeStatement (stmt : CallHeapStrataStatement) (state : ValidationState) : ValidationState :=
  match stmt with
  | .cmd cmd => analyzeCommand cmd state
  | _ => state

-- Entry point for analyzing CallHeap statements
def analyzeCallHeapProgram (ctx : CallHeapTranslationContext) (stmts : List CallHeapStrataStatement) : AnalysisResult :=
  -- Check if is_valid function exists
  let hasIsValid := ctx.functions.any (fun f => f.name == "is_valid")
  if not hasIsValid then
    let errorViolation := Violation.mk "program" "Error: No is_valid function found. Please define an is_valid(value) function."
    AnalysisResult.mk [errorViolation]
  else
    let initialState := ValidationState.withFunctions ctx
    let finalState := stmts.foldl (fun state stmt => analyzeStatement stmt state) initialState
    AnalysisResult.mk finalState.violations

end ValueValidation
