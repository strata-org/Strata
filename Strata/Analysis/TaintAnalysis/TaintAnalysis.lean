import Strata.DL.DataFlow
import Strata.DL.Generic.TranslationContext

/-! ## Generic Taint Analysis for Strata

Tracks data flow from external/untrusted sources through the program.
Works with any type that implements DataFlowCapable interface.

Based on MIDI's generic taint analysis approach.
-/

namespace TaintAnalysis

open DataFlow

-- Taint value with source tracking
inductive TaintValue where
  | tainted : String → TaintValue    -- Tainted from specific external function
  | clean : TaintValue               -- Clean/untainted
  deriving Repr, BEq

-- Violation structure
structure Violation where
  object : String
  message : String
  deriving Repr

-- Analysis result
structure AnalysisResult where
  violations : List Violation
  deriving Repr

-- Analysis state tracking taint for each data location
structure TaintState where
  -- Map from data location strings to taint values
  locationTaints : Std.HashMap String TaintValue
  -- Violations found during analysis
  violations : List Violation
  deriving Repr

def TaintState.empty : TaintState :=
  { locationTaints := Std.HashMap.emptyWithCapacity 16, violations := [] }

-- Convert DataLocation to string key for HashMap
def dataLocationToKey : DataLocation → String
  | .variable name => s!"var:{name}"
  | .heapField objName fieldIndex => s!"heap:{objName}[{fieldIndex}]"
  | .dynamicField objName keyName => s!"heap:{objName}[{keyName}]"
  | .functionParam funcName paramIndex => s!"param:{funcName}[{paramIndex}]"
  | .functionResult funcName => s!"result:{funcName}"
  | .external funcName => s!"external:{funcName}"
  | .literal value => s!"literal:{value}"

-- Get taint value for a data location
def getTaintValue (state : TaintState) (loc : DataLocation) : TaintValue :=
  let key := dataLocationToKey loc
  state.locationTaints.getD key TaintValue.clean

-- Set taint value for a data location, combining with existing taint
def setTaintValue (state : TaintState) (loc : DataLocation) (taint : TaintValue) : TaintState :=
  let key := dataLocationToKey loc
  let existingTaint := getTaintValue state loc
  let combinedTaint := match existingTaint, taint with
    | TaintValue.tainted source, _ => TaintValue.tainted source  -- Keep existing taint
    | _, TaintValue.tainted source => TaintValue.tainted source  -- Use new taint
    | TaintValue.clean, TaintValue.clean => TaintValue.clean    -- Both clean
  { state with locationTaints := state.locationTaints.insert key combinedTaint }

-- Combine taint values (tainted wins)
def combineTaint (t1 t2 : TaintValue) : TaintValue :=
  match t1, t2 with
  | .tainted source, _ => .tainted source
  | _, .tainted source => .tainted source
  | .clean, .clean => .clean

-- Convert DataLocation to object name (like MIDI)
def dataLocationToObjectName (loc : DataLocation) : String :=
  match loc with
  | .variable name => name
  | .heapField objName _ => objName
  | .dynamicField objName _ => objName
  | .functionParam funcName _ => funcName
  | .functionResult funcName => funcName
  | .external funcName => funcName
  | .literal value => value

-- Generate violation message like MIDI
def generateViolationMessage (loc : DataLocation) (source : String) : String :=
  match loc with
  | .variable _ => s!"Variable is tainted from external source: {source}"
  | .heapField _ fieldIndex => s!"Field {fieldIndex} is tainted from external source: {source}"
  | .dynamicField _ keyName => s!"Dynamic field {keyName} is tainted from external source: {source}"
  | .functionParam _ paramIndex => s!"Parameter {paramIndex} is tainted from external source: {source}"
  | .functionResult _ => s!"Function result is tainted from external source: {source}"
  | _ => s!"Location is tainted from external source: {source}"

-- Add violation for tainted data reaching sensitive location
def addViolation (state : TaintState) (loc : DataLocation) (source : String) (operation : String) : TaintState :=
  let objectName := dataLocationToObjectName loc
  let message := generateViolationMessage loc source
  let violation := Violation.mk objectName message
  { state with violations := violation :: state.violations }

-- Process a single data flow
def processDataFlow (state : TaintState) (flow : DataFlow) : TaintState :=
  -- Get taint from source
  let sourceTaint := getTaintValue state flow.source

  -- Handle external sources specially - they are always tainted
  let actualSourceTaint := match flow.source with
    | .external funcName => TaintValue.tainted funcName
    | _ => sourceTaint

  match actualSourceTaint with
  | TaintValue.clean =>
    dbg_trace s!"[DEBUG] No taint propagation: {dataLocationToKey flow.source} is clean"
    state
  | TaintValue.tainted source =>
    dbg_trace s!"[DEBUG] Propagating taint: {dataLocationToKey flow.source} -> {dataLocationToKey flow.target} (source: {source})"
    -- Propagate taint to target
    let stateWithTaint := setTaintValue state flow.target actualSourceTaint
    -- Add violation for tainted target (like MIDI does)
    addViolation stateWithTaint flow.target source flow.operation

-- Process external function calls to introduce taint and violations
def processExternalCalls (state : TaintState) (externalCalls : List (String × List DataLocation × List DataLocation)) : TaintState :=
  externalCalls.foldl (fun s (funcName, _args, results) =>
    dbg_trace s!"[DEBUG] External function detected: {funcName}"
    -- Mark all result locations as tainted from this external function
    results.foldl (fun s' resultLoc =>
      dbg_trace s!"[DEBUG]   Marking {dataLocationToKey resultLoc} as tainted from {funcName}"
      let stateWithTaint := setTaintValue s' resultLoc (TaintValue.tainted funcName)
      -- Add violation for each tainted result from external call
      addViolation stateWithTaint resultLoc funcName "external_call"
    ) s
  ) state

-- Extract data flows from function bodies (like MIDI)
def extractFunctionBodyDataFlows [DataFlowCapable S] (func : Generic.StrataFunction S T) : List DataFlow :=
  let bodyFlows := func.body.flatMap DataFlowCapable.getDataFlows

  dbg_trace s!"[DEBUG] Analyzing function body for: {func.name} with {func.body.length} statements"
  dbg_trace s!"[DEBUG] Function body flows: {bodyFlows.length}"



  bodyFlows.filterMap (fun flow =>
    match flow.target with
    | DataLocation.variable "return_value" =>
      dbg_trace s!"[DEBUG] Function body flow: {dataLocationToKey flow.source} -> result:{func.name} (return)"
      -- Direct return statement - map source to function result
      some (DataFlow.mk flow.source (DataLocation.functionResult func.name) "function_return")
    | _ =>
      -- For other flows within the function body
      match flow.source with
      | DataLocation.variable varName =>
        dbg_trace s!"[DEBUG] Function body flow: {dataLocationToKey flow.source} -> result:{func.name} (body reference)"
        -- Variable referenced in function body flows to function result
        some (DataFlow.mk flow.source (DataLocation.functionResult func.name) "function_body_reference")
      | _ =>
        dbg_trace s!"[DEBUG] Skipping function body flow: {dataLocationToKey flow.source} -> {dataLocationToKey flow.target}"
        none
  )

-- Process all functions in context to extract their data flows
def extractAllFunctionDataFlows [DataFlowCapable S] (ctx : Generic.TranslationContext S T) : List DataFlow :=
  ctx.functions.flatMap extractFunctionBodyDataFlows


-- Main analysis function following MIDI's analyzeGenericProgram pattern
def analyzeGenericProgram [DataFlowCapable S] (ctx : Generic.TranslationContext S T) (stmts : List S) : AnalysisResult :=
  let initialState := TaintState.empty

  -- Process all statements to collect data flows and external calls
  let allFlows := stmts.flatMap DataFlowCapable.getDataFlows
  let allExternalCalls := stmts.flatMap DataFlowCapable.getExternalCalls

  dbg_trace s!"[DEBUG] Found {allFlows.length} data flows and {allExternalCalls.length} external calls"
  dbg_trace s!"[DEBUG] Functions in context: {ctx.functions.map (·.name)}"

  -- First, process external calls to introduce taint and violations
  let stateAfterExternalCalls := processExternalCalls initialState allExternalCalls

  -- First pass: process regular data flows to establish initial taint
  dbg_trace s!"[DEBUG] === FIRST PASS: Processing regular flows ==="
  let stateAfterFirstPass := allFlows.foldl processDataFlow stateAfterExternalCalls

  -- Process function body data flows (now that variables may be tainted)
  dbg_trace s!"[DEBUG] === Processing function body flows ==="
  let functionFlows := extractAllFunctionDataFlows ctx
  dbg_trace s!"[DEBUG] Extracted {functionFlows.length} function body flows"
  let stateAfterFunctionFlows := functionFlows.foldl processDataFlow stateAfterFirstPass

  -- Second pass: process regular data flows again to catch flows from newly tainted function results
  dbg_trace s!"[DEBUG] === SECOND PASS: Processing regular flows again ==="
  let finalState := allFlows.foldl processDataFlow stateAfterFunctionFlows

  AnalysisResult.mk finalState.violations

-- Analyze any type that implements DataFlowCapable
def analyzeDataFlows [DataFlowCapable D] (items : List D) : AnalysisResult :=
  let initialState := TaintState.empty

  -- Process all items to collect data flows and external calls
  let allFlows := items.flatMap DataFlowCapable.getDataFlows
  let allExternalCalls := items.flatMap DataFlowCapable.getExternalCalls

  -- First, process external calls to introduce taint and violations
  let stateAfterExternalCalls := processExternalCalls initialState allExternalCalls

  -- Then, process data flows to propagate taint
  let finalState := allFlows.foldl processDataFlow stateAfterExternalCalls

  AnalysisResult.mk finalState.violations

-- Pretty print results
def printResults (result : AnalysisResult) : IO Unit := do
  IO.println "=== Taint Analysis Results ==="

  if result.violations.isEmpty then
    IO.println "✅ No taint violations detected"
  else
    IO.println s!"⚠️  Found {result.violations.length} taint violations:"
    for violation in result.violations do
      IO.println s!"  • {violation.object}: {violation.message}"

-- JSON serialization instances
instance : Lean.ToJson Violation where
  toJson v := Lean.Json.mkObj [
    ("object", Lean.toJson v.object),
    ("message", Lean.toJson v.message)
  ]

instance : Lean.ToJson AnalysisResult where
  toJson ar := Lean.Json.mkObj [
    ("violations", Lean.toJson ar.violations)
  ]

end TaintAnalysis
