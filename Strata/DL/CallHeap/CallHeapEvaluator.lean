/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
CallHeap Evaluator: Generic evaluator for CallHeap statements in Strata
Adapted from the MIDI HeapMidiEval but with Call dialect separated
-/

import Strata.DL.CallHeap.CallHeapStrataStatement
import Strata.DL.Heap.HState
import Strata.DL.Heap.HEval
import Strata.DL.Heap.HeapStrataEval
import Strata.DL.Lambda.LState
import Strata.DL.Heap.Heap

---------------------------------------------------------------------

namespace CallHeap

open Heap
open Lambda (LState)

/-! ## CallHeap Statement Evaluator

Generic evaluator for CallHeap statements that combines Call and Heap dialects.
This is adapted from the MIDI HeapMidiEval but works with the separated Call dialect.
-/

-- Generic function definition for CallHeap (now using generic framework)
abbrev CallHeapFunction := CallHeapStrataFunction

-- Evaluation context with function storage
structure CallHeapEvalContext where
  hstate : HState
  functions : Std.HashMap String CallHeapFunction

def CallHeapEvalContext.empty : CallHeapEvalContext :=
  { hstate := HState.empty, functions := {} }

def CallHeapEvalContext.addFunction (ctx : CallHeapEvalContext) (func : CallHeapFunction) : CallHeapEvalContext :=
  { ctx with functions := ctx.functions.insert func.name func }

def CallHeapEvalContext.getFunction? (ctx : CallHeapEvalContext) (name : String) : Option CallHeapFunction :=
  ctx.functions.get? name

mutual
-- Function call evaluation (adapted from MIDI)
partial def evalFunctionCall (funcName : String) (args : List HExpr) (lhs : List String) (ctx : CallHeapEvalContext) : CallHeapEvalContext :=
  dbg_trace s!"[DEBUG] Function call: {funcName}({args.length} args) -> {lhs}"
  dbg_trace s!"[DEBUG] Available functions: {ctx.functions.toList.map (·.1)}"

  match ctx.getFunction? funcName with
  | none =>
    dbg_trace s!"[DEBUG] Function '{funcName}' not found!"
    ctx
  | some funcDef =>
    dbg_trace s!"[DEBUG] Found function '{funcName}' with {funcDef.params.length} parameters"
    dbg_trace s!"[DEBUG] Function body has {funcDef.body.length} statements"

    -- Evaluate arguments in current context
    let (newHState, argValues) := args.foldl (fun (state, values) arg =>
      let (newState, value) := Heap.evalHExpr state arg
      dbg_trace s!"[DEBUG] Evaluated arg: {repr value}"
      (newState, values ++ [value])
    ) (ctx.hstate, [])

    dbg_trace s!"[DEBUG] Evaluated {argValues.length} arguments"

    -- Create new scope for function parameters
    let paramBindings := funcDef.params.zip argValues
    dbg_trace s!"[DEBUG] Parameter bindings: {paramBindings.map (fun (p, v) => s!"{p} = {repr v}")}"

    let newScope := paramBindings.foldl (fun scope (param, value) =>
      -- Convert HExpr to LExpr for Lambda scope
      let lambdaValue := match value with
        | .lambda lexpr => lexpr
        | .address addr => Lambda.LExpr.const s!"addr_{addr}" none
        | .null => Lambda.LExpr.const "null" none
        | _ => Lambda.LExpr.const "unknown" none
      dbg_trace s!"[DEBUG] Binding {param} to {repr lambdaValue}"
      scope.insert param (none, lambdaValue)
    ) (Map.empty : Lambda.Scope String)

    -- Push new scope onto Lambda state
    let oldLambdaState := newHState.lambdaState
    let newLambdaState := { oldLambdaState with state := oldLambdaState.state.push newScope }
    let contextWithScope := { ctx with hstate := { newHState with lambdaState := newLambdaState } }

    dbg_trace s!"[DEBUG] Pushed new scope, executing function body..."

    -- Execute function body
    let resultContext := evalProgramWithContext funcDef.body contextWithScope

    dbg_trace s!"[DEBUG] Function body executed"

    -- Capture return value BEFORE popping the scope
    let (tempState, returnValue) := Heap.evalHExpr resultContext.hstate (HExpr.lambda (Lambda.LExpr.fvar "return_value" none))
    dbg_trace s!"[DEBUG] Captured return value using evalHExpr: {repr returnValue}"

    -- Pop the scope AFTER capturing the return value
    let finalLambdaState := tempState.lambdaState.state.pop
    let finalHState := { tempState with lambdaState := { tempState.lambdaState with state := finalLambdaState } }

    -- Handle return value assignment to lhs variables
    let finalContext := { resultContext with hstate := finalHState }
    match lhs with
    | [] =>
      dbg_trace s!"[DEBUG] No return value assignment needed"
      finalContext
    | [lhsVar] =>
      dbg_trace s!"[DEBUG] Assigning captured return value {repr returnValue} to {lhsVar}"
      let finalHState2 := HState.setHeapVar finalContext.hstate lhsVar HMonoTy.int returnValue
      { finalContext with hstate := finalHState2 }
    | _ =>
      dbg_trace s!"[DEBUG] Multiple return values not supported"
      finalContext

-- Evaluate a single CallHeap statement (adapted from MIDI)
partial def evalStatementWithContext (stmt : CallHeapStrataStatement) (ctx : CallHeapEvalContext) : CallHeapEvalContext :=
  match stmt with
  | .cmd (.imperativeCmd (.init name ty expr _)) =>
    dbg_trace s!"[DEBUG] Executing init: {name} : {repr ty} = {repr expr}"
    let (newState, value) := Heap.evalHExpr ctx.hstate expr
    dbg_trace s!"[DEBUG] Evaluated init expr to: {repr value}"
    let finalState := HState.setHeapVar newState name ty value
    { ctx with hstate := finalState }

  | .cmd (.imperativeCmd (.set name expr _)) =>
    dbg_trace s!"[DEBUG] Executing set: {name} = {repr expr}"
    let (newState, value) := Heap.evalHExpr ctx.hstate expr
    dbg_trace s!"[DEBUG] Evaluated set expr to: {repr value}"
    let ty := match HState.getHeapVarType newState name with
      | some existingTy => existingTy
      | none => HMonoTy.int
    let finalState := HState.setHeapVar newState name ty value
    dbg_trace s!"[DEBUG] Set {name} to {repr value}"
    { ctx with hstate := finalState }

  | .cmd (.directCall lhs funcName args) =>
    -- This is the key change from MIDI: .directCall instead of .call
    evalFunctionCall funcName args lhs ctx

  | .ite cond thenBlock elseBlock _ =>
    let (newState, condValue) := Heap.evalHExpr ctx.hstate cond
    let conditionIsTrue := match condValue with
      | .lambda (.const "true" _) => true
      | .lambda (.const "false" _) => false
      | _ => false

    let newCtx := { ctx with hstate := newState }
    if conditionIsTrue then
      evalProgramWithContext thenBlock.ss newCtx
    else
      evalProgramWithContext elseBlock.ss newCtx

  | _ =>
    -- Handle other statement types
    match stmt with
    | .cmd (.imperativeCmd (.havoc name _)) =>
      ctx
    | .cmd (.imperativeCmd (.assert _ _ _)) =>
      ctx
    | .cmd (.imperativeCmd (.assume _ _ _)) =>
      ctx
    | .block _ _ _ =>
      ctx
    | .goto _ _ =>
      ctx
    | .loop _ _ _ _ _ =>
      ctx
    | _ =>
      ctx

-- Evaluate a list of CallHeap statements
partial def evalProgramWithContext (stmts : List CallHeapStrataStatement) (ctx : CallHeapEvalContext) : CallHeapEvalContext :=
  stmts.foldl (fun context stmt => evalStatementWithContext stmt context) ctx

end

-- Convenience functions
def evalCallHeapProgram (stmts : List CallHeapStrataStatement) : CallHeapEvalContext :=
  evalProgramWithContext stmts CallHeapEvalContext.empty

-- Convert CallHeapTranslationContext to CallHeapEvalContext (bridge function)
def callHeapTranslationContextToEvalContext (transCtx : CallHeapTranslationContext) : CallHeapEvalContext :=
  transCtx.functions.foldl (fun ctx func => ctx.addFunction func) CallHeapEvalContext.empty

-- Evaluate translated program with functions (using translation context)
def evalCallHeapTranslatedProgram (transCtx : CallHeapTranslationContext) (stmts : List CallHeapStrataStatement) : CallHeapEvalContext :=
  let evalCtx := callHeapTranslationContextToEvalContext transCtx
  evalProgramWithContext stmts evalCtx

-- JSON output function with TranslationContext (matching MIDI pattern)
def runCallHeapAndShowJSONWithTranslation (transCtx : CallHeapTranslationContext) (stmts : List CallHeapStrataStatement) : IO Unit := do
  let finalContext := evalCallHeapTranslatedProgram transCtx stmts
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

-- Legacy JSON output function for programs without functions
def runCallHeapAndShowJSON (stmts : List CallHeapStrataStatement) : IO Unit := do
  let finalContext := evalCallHeapProgram stmts
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
  IO.println jsonObj.compress

-- Helper to describe a CallHeap statement (adapted from Python version)
def describeCallHeapStatement (stmt: CallHeapStrataStatement) : String :=
  match stmt with
  | .cmd (.imperativeCmd (.init name ty expr _)) =>
    s!"init {name} : {repr ty} = {repr expr}"
  | .cmd (.imperativeCmd (.set name expr _)) =>
    s!"set {name} = {repr expr}"
  | .cmd (.imperativeCmd (.havoc name _)) =>
    s!"havoc {name}"
  | .cmd (.imperativeCmd (.assume name expr _)) =>
    s!"assume {name} : {repr expr}"
  | .cmd (.imperativeCmd (.assert name expr _)) =>
    s!"assert {name} : {repr expr}"
  | .cmd (.directCall lhs funcName args) =>
    let lhsStr := if lhs.isEmpty then "" else s!"{String.intercalate ", " lhs} = "
    let argsStr := String.intercalate ", " (args.map (fun arg => s!"{repr arg}"))
    s!"{lhsStr}{funcName}({argsStr})"
  | .block label block _ =>
    s!"block {label} ( {block.ss.length} statements )"
  | .ite cond thenBlock elseBlock _ =>
    s!"if {repr cond} then ( {thenBlock.ss.length} statements ) else ( {elseBlock.ss.length} statements )"
  | .loop guard measure invariant body _ =>
    let measureStr := match measure with | some m => s!" measure {repr m}" | none => ""
    let invariantStr := match invariant with | some i => s!" invariant {repr i}" | none => ""
    s!"loop {repr guard}{measureStr}{invariantStr} ( {body.ss.length} statements )"
  | .goto label _ =>
    s!"goto {label}"

end CallHeap
