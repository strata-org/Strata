import Strata.DL.DataFlow

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
  | TaintValue.clean => state
  | TaintValue.tainted source =>
    -- Propagate taint to target
    let stateWithTaint := setTaintValue state flow.target actualSourceTaint
    -- Add violation for tainted target (like MIDI does)
    addViolation stateWithTaint flow.target source flow.operation

-- Process external function calls to introduce taint and violations
def processExternalCalls (state : TaintState) (externalCalls : List (String × List DataLocation × List DataLocation)) : TaintState :=
  externalCalls.foldl (fun s (funcName, _args, results) =>
    -- Mark all result locations as tainted from this external function
    results.foldl (fun s' resultLoc =>
      let stateWithTaint := setTaintValue s' resultLoc (TaintValue.tainted funcName)
      -- Add violation for each tainted result from external call
      addViolation stateWithTaint resultLoc funcName "external_call"
    ) s
  ) state

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
