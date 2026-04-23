/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.SimpleAPI
meta import Strata.Languages.Python.PySpecPipeline
meta import Strata.Languages.Laurel.Resolution
meta import Strata.Transform.ProcedureInlining
meta import Strata.Languages.Python.PyFactory
meta import StrataTest.Util.Python

/-! ## End-to-end tests for `pyAnalyzeLaurel` with dispatch

These tests exercise the full pipeline: compile mock PySpec Python sources
to Ion, compile a user Python script to Ion, then run `pyAnalyzeLaurel`
with `--dispatch` through the SimpleAPI. The mock services (Storage,
Messaging) are generic and not tied to any cloud provider.
-/

namespace Strata.Python.AnalyzeLaurelTest

open Strata (pythonAndSpecToLaurel pySpecsDir)

private meta def testDir : System.FilePath :=
  "StrataTest/Languages/Python/Specs/dispatch_test"

/-- Compile a Python source file to a `.python.st.ion` Ion file.
    Returns the path to the generated Ion file. -/
private meta def compilePython
    (pythonCmd : System.FilePath)
    (dialectFile : System.FilePath) (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  let some stem := pyFile.fileStem
    | throw <| .userError s!"No stem for {pyFile}"
  let ionPath := outDir / s!"{stem}.python.st.ion"
  let spawnArgs : IO.Process.SpawnArgs := {
    cmd := toString pythonCmd
    args := #["-m", "strata.gen", "py_to_strata",
              "--dialect", dialectFile.toString,
              pyFile.toString, ionPath.toString]
    cwd := none
    inheritEnv := true
    stdin := .null
    stdout := .piped
    stderr := .piped
  }
  let child ← IO.Process.spawn spawnArgs
  let _stdout ← child.stdout.readToEnd
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  if exitCode ≠ 0 then
    throw <| .userError s!"py_to_strata failed for {pyFile} (exit {exitCode}): {stderr}"
  return ionPath

/-- Set up the test fixture: compile all servicelib modules and return the
    spec directory.  The dispatch and pyspec modules are resolved by name. -/
private meta def setupFixture (pythonCmd : System.FilePath)
    (outDir : System.FilePath) : IO Unit := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.Python.toIon
    -- Compile all servicelib modules (dispatch + individual services)
    match ← pySpecsDir testDir outDir dialectFile
        (modules := #["servicelib", "servicelib.Storage", "servicelib.Messaging", "servicelib.Database"])
        (warningOutput := .none)
        (pythonCmd := toString pythonCmd) |>.toBaseIO with
    | .ok () => pure ()
    | .error msg => throw <| IO.userError s!"pySpecsDir failed: {msg}"

/-- Compile a test Python file to Ion format. -/
private meta def compileTestScript (pythonCmd : System.FilePath)
    (pyFile : System.FilePath)
    (outDir : System.FilePath) : IO System.FilePath := do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile Python.Python.toIon
    compilePython pythonCmd dialectFile pyFile outDir

/-- Run pyAnalyzeLaurel on a test script within the shared fixture. -/
private meta def runAnalyze
    (pythonCmd : System.FilePath)
    (tmpDir : System.FilePath) (scriptName : String)
    : IO (Except String Core.Program) := do
  let testIon ← compileTestScript pythonCmd (testDir / scriptName) tmpDir
  let laurel ←
    match ← Strata.pythonAndSpecToLaurel testIon.toString
        (dispatchModules := #["servicelib"])
        (specDir := tmpDir) |>.toBaseIO with
    | .ok r => pure r
    | .error err => return .error (toString err)
  match ← Strata.translateCombinedLaurel laurel with
  | (some core, []) =>
    -- Also run Core type checking to catch semantic errors (e.g. Heap vs Any)
    match Core.typeCheck Core.VerifyOptions.quiet core (moreFns := Strata.Python.ReFactory) with
    | .error diag => return .error s!"Core type checking failed: {diag}"
    | .ok _ => return .ok core
  | (_, errors) => return .error s!"Laurel to Core translation failed: {errors}"

/-- Run pyAnalyzeLaurel with inlining and verification.
    When `useRoots` is true, entry points are determined via the call graph
    (the CLI `--entry-point roots` default); otherwise only `__main__` is used. -/
private meta def runAnalyzeAndVerify
    (pythonCmd : System.FilePath)
    (tmpDir : System.FilePath) (scriptName : String)
    (useRoots : Bool := false)
    : IO (Except String (Array Core.VCResult)) := do
  let testIon ← compileTestScript pythonCmd (testDir / scriptName) tmpDir
  let laurel ←
    match ← Strata.pythonAndSpecToLaurel testIon.toString
        (dispatchModules := #["servicelib"])
        (specDir := tmpDir) |>.toBaseIO with
    | .ok r => pure r
    | .error err => return .error (toString err)
  let (coreProgramOption, _) ← Strata.translateCombinedLaurel laurel
  let coreProgram ← match coreProgramOption with
    | none => return .error "Laurel to Core translation failed"
    | some core => pure core
  -- Determine entry points
  let entryPoints ←
    if useRoots then
      let (_preludeNames, userProcNames) := Strata.splitProcNames coreProgram
      let cg := coreProgram.toProcedureCG
      let userSet := Std.HashSet.ofList userProcNames
      pure ((cg.computeRoots (preferredRoots := userProcNames)).filter userSet.contains)
    else
      pure ["__main__"]
  let entrySet := Std.HashSet.ofList entryPoints
  let inlinePhases : List Core.PipelinePhase :=
    [_root_.Core.procedureInliningPipelinePhase
      { doInline := fun caller callee a =>
          (match caller with | some c => entrySet.contains c | none => false)
          && _root_.Core.doInlineNonRecursive callee a }]
  let options : Core.VerifyOptions :=
    { Core.VerifyOptions.default with
      stopOnFirstError := false, verbose := .quiet, solver := "z3",
      checkMode := .bugFinding, checkLevel := .full }
  match ← Core.verifyProgram coreProgram options
      (moreFns := Strata.Python.ReFactory)
      (proceduresToVerify := some entryPoints)
      (externalPhases := [Strata.frontEndPhase])
      (prefixPhases := inlinePhases) |>.toBaseIO with
  | .ok results => return .ok results
  | .error msg => return .error (toString msg)

/-- Expected outcome for a test case. -/
private inductive Expected where
  | success
  | fail (msg : String)
  | failPrefix (pfx : String)

/-- All dispatch test cases: (filename, expected outcome). -/
private meta def testCases : List (String × Expected) := [
  -- Positive tests
  .mk "test_single_service.py" .success,
  .mk "test_multi_service.py" .success,
  .mk "test_annotation_fallback.py" .success,
  .mk "test_required_with_optional.py" .success,
  .mk "test_heap_return.py" .success,
  .mk "test_list_str.py" .success,
  .mk "test_nested_try.py" .success,
  .mk "test_try_scope.py" .success,
  .mk "test_dict_expand.py" .success,
  .mk "test_dict_expand_optional.py" .success,
  .mk "test_instance_call_result.py" .success,
  -- Void/non-void call handling tests (Phase 1 TDD)
  .mk "test_void_assign.py" .success,
  .mk "test_void_init.py" .success,
  .mk "test_discard_nonvoid.py" .success,
  -- User-defined class field assignment and method return
  .mk "test_class_field_assign.py" .success,
  .mk "test_class_method_return.py" .success,
  .mk "test_user_class_construct.py" .success,
  -- Negative tests
  .mk "test_invalid_service.py" $
    .failPrefix "User code error: 'connect' called with unknown string \"invalid\"; known services:",
  .mk "test_invalid_method.py" $
    .fail "User code error: Unknown method 'nonexistent_method'",
  .mk "test_invalid_args.py" $
    .fail "User code error: 'put_item' called with unknown keyword arguments: [Wrong]",
  .mk "test_missing_required.py" $
    .fail "User code error: 'put_item' called with missing required arguments: [Key, Data]",
  .mk "test_extra_kwarg.py" $
    .fail "User code error: 'get_item' called with unknown keyword arguments: [Bogus]",
  .mk "test_no_args.py" $
    .fail "User code error: 'put_item' called with missing required arguments: [Bucket, Key, Data]",
  .mk "test_optional_missing_required.py" $
    .fail "User code error: 'list_items' called with missing required arguments: [Bucket]",
  .mk "test_positional_missing.py" $
    .fail "User code error: 'delete_item' called with missing required arguments: [Key]",
  -- Type alias resolution tests (TDD for resolveTypeName refactoring)
  .mk "test_method_dispatch.py" .success,
  .mk "test_keyword_dispatch.py" .success,
  .mk "test_keyword_dispatch_variable.py" .success,
  .mk "test_wrong_keyword_dispatch.py" $
    .failPrefix "Python to Laurel translation failed: Type error: Dispatched function 'connect' called with wrong keyword argument, expected 'service_name' but got 'wrong_param'",
  .mk "test_annotation_dispatch.py" .success,
  .mk "test_constructor_dispatch.py" .success,
  .mk "test_reassign_dispatch.py" .success,
  -- Known failing tests:
  -- With @ separator, Storage_put_item is no longer a known symbol, so it
  -- falls through to the default Any type. These should produce an
  -- error or warning since procedure names are not valid type annotations.
  .mk "test_procedure_as_annotation.py" .success,
  .mk "test_procedure_as_param_type.py" .success
]

/-- Run a single test case and return an error message on failure, or `none` on success. -/
private meta def runTestCase (pythonCmd : System.FilePath) (tmpDir : System.FilePath)
    (scriptName : String) (expected : Expected) : IO (Option String) := do
  let result ← runAnalyze pythonCmd tmpDir scriptName
  match expected, result with
  | .success, .ok _ => return none
  | .success, .error msg =>
    return some s!"pyAnalyzeLaurel failed on {scriptName}: {msg}"
  | .fail _, .ok _ =>
    return some s!"pyAnalyzeLaurel succeeded on {scriptName} but was expected to fail"
  | .fail exp, .error msg =>
    if msg == exp then return none
    else return some s!"{scriptName}: Expected error:\n  {exp}\nGot:\n  {msg}"
  | .failPrefix _pfx, .ok _ =>
    return some s!"pyAnalyzeLaurel succeeded on {scriptName} but was expected to fail"
  | .failPrefix pfx, .error msg =>
    if msg.startsWith pfx then return none
    else return some s!"{scriptName}: Expected error starting with:\n  {pfx}\nGot:\n  {msg}"

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    -- Launch all tests concurrently, checking for duplicate filenames
    let mut seen : Std.HashSet String := {}
    let mut tasks : Array (String × Task (Except IO.Error (Option String))) := #[]
    for (scriptName, expected) in testCases do
      if scriptName ∈ seen then
        throw <| IO.userError s!"Duplicate test filename: {scriptName}"
      seen := seen.insert scriptName
      let task ← IO.asTask (runTestCase pythonCmd tmpDir scriptName expected)
      tasks := tasks.push (scriptName, task)
    -- Composite/Any kind mismatch tests
    -- composite_as_any auto-resolves Storage via connect(); any_as_composite needs explicit pyspec
    let task ← IO.asTask (runTestCase pythonCmd tmpDir
      "test_class_composite_as_any.py"
      (.failPrefix "Known limitation: Unsupported construct: Coercion from user-defined class"))
    tasks := tasks.push ("test_class_composite_as_any.py", task)
    -- test_class_any_as_composite: assigning a str to a Composite-typed field
    -- causes a type unification error in Core.typeCheck, which is expected.
    let task ← IO.asTask do
      let testIon ← compileTestScript pythonCmd (testDir / "test_class_any_as_composite.py") tmpDir
      let laurel ←
        match ← Strata.pythonAndSpecToLaurel testIon.toString
            (dispatchModules := #["servicelib"])
            (pyspecModules := #["servicelib.Storage"])
            (specDir := tmpDir) |>.toBaseIO with
        | .ok r => pure r
        | .error err => return some s!"test_class_any_as_composite.py: {err}"
      match ← Strata.translateCombinedLaurel laurel with
      | (some core, []) =>
        match Core.typeCheck Core.VerifyOptions.quiet core (moreFns := Strata.Python.ReFactory) with
        | .error diag =>
          -- Expected: assigning str (Any) to a Composite-typed field is a type error
          if (diag.message.splitOn "Impossible to unify").length > 1 then return none
          else return some s!"test_class_any_as_composite.py: {diag}"
        | .ok _ => return none
      | (_, errors) => return some s!"test_class_any_as_composite.py: Laurel to Core failed: {errors}"
    tasks := tasks.push ("test_class_any_as_composite.py", task)
    -- Collect results
    let mut errors : Array String := #[]
    for (_, task) in tasks do
      match ← IO.wait task with
      | .ok (some err) => errors := errors.push err
      | .ok none => pure ()
      | .error e => errors := errors.push s!"Task error: {e}"
    if errors.size > 0 then
      throw <| IO.userError ("\n".intercalate errors.toList)

/-! ## Precondition violation test

Verifies that calling `put_item(Bucket="INVALID!", ...)` produces a `✖️ always false`
result for the regex assertion through the full verification pipeline.
Uses `--entry-point roots` to discover the user-defined function as the entry point,
since the test script defines a function but does not call it from the top level.

Expected output (when Python + z3 available):
  servicelib_Storage_Storage_put_item_assert(0)_9: ✔️ always true if reached (Required parameter 'Bucket' is missing)
  servicelib_Storage_Storage_put_item_assert(0)_9: ✔️ always true if reached (Required parameter 'Key' is missing)
  servicelib_Storage_Storage_put_item_assert(0)_9: ✔️ always true if reached (Required parameter 'Data' is missing)
  servicelib_Storage_Storage_put_item_assert(0)_9: ✔️ always true if reached (Bucket must not be empty)
  servicelib_Storage_Storage_put_item_assert(0)_9: ✖️ always false if reached (Bucket must match ^[a-z0-9-]+$)
  servicelib_Storage_Storage_put_item_assert(0)_9: ✔️ always true if reached (Key must not be empty)
-/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    -- These test scripts define functions but do not call them from the
    -- top level, so __main__ has no assertions.  Use `useRoots` to
    -- discover the user-defined function as the entry point.
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      "test_precondition_violation.py" (useRoots := true)
    match result with
    | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
    | .ok vcResults =>
      let mut foundAlwaysFalse := false
      for r in vcResults do
        if r.obligation.label.startsWith "servicelib_Storage_" then
          let line := r.formatOutcome
          if (line.splitOn "✖️").length != 1 then
            foundAlwaysFalse := true
      if !foundAlwaysFalse then
        throw <| IO.userError
          "Expected ✖️ always false for regex violation"

/-! ## Precondition with alias test

Verifies that calling `put_item(Bucket="", ...)` through the alias resolution
path produces a `✖️ always false` result for the "Bucket must not be empty"
assertion. This exercises the full pipeline with type alias resolution.
-/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      "test_precondition_with_alias.py" (useRoots := true)
    match result with
    | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
    | .ok vcResults =>
      let mut foundAlwaysFalse := false
      for r in vcResults do
        if r.obligation.label.startsWith "servicelib_Storage_" then
          let line := r.formatOutcome
          if (line.splitOn "✖️").length != 1 then
            foundAlwaysFalse := true
      if !foundAlwaysFalse then
        throw <| IO.userError
          "Expected ✖️ always false for empty bucket violation"

/-! ## evalIfCanonical regression test (Issue #812)

Symbolic bucket must pass the regex precondition via `evalIfCanonical`.
Without the attribute, the regex VC would be ❓ unknown. -/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let result ← runAnalyzeAndVerify pythonCmd tmpDir
      "test_regex_eval_if_canonical.py" (useRoots := true)
    match result with
    | .error msg => throw <| IO.userError s!"Pipeline failed: {msg}"
    | .ok vcResults =>
      for r in vcResults do
        if r.obligation.label.startsWith "servicelib_Storage_" then
          if !r.isSuccess then
            throw <| IO.userError
              s!"Expected all Storage preconditions to pass but got: {r.formatOutcome}"

/-! ## Resolution error test after FilterPrelude

Verifies that the combined Laurel program (after prelude filtering) resolves
without errors.  This catches cases where FilterPrelude includes a declaration
that references a type or name not present in the filtered prelude — for
example, a composite field typed as a nested class that was never translated
(the `_Exceptions` pattern in real boto3 pyspecs).

The `Database` mock pyspec has a nested `_Exceptions` class.  The pyspec
compiler emits it as a `subclass` in the Ion file.  `classDefToLaurel`
recursively translates subclasses, so the type
`servicelib_Database__Exceptions` is defined and resolves correctly. -/

#eval withPython fun pythonCmd => do
  IO.FS.withTempDir fun tmpDir => do
    setupFixture pythonCmd tmpDir
    let testIon ← compileTestScript pythonCmd
      (testDir / "test_resolution_after_filter.py") tmpDir
    let combined ←
      match ← Strata.pythonAndSpecToLaurel testIon.toString
          (dispatchModules := #["servicelib"])
          (specDir := tmpDir) |>.toBaseIO with
      | .ok r => pure r
      | .error err => throw <| IO.userError s!"pyAnalyzeLaurel failed: {err}"
    let result := Laurel.resolve combined
    unless result.errors.isEmpty do
      let msgs := result.errors.toList.map (·.message)
      throw <| IO.userError s!"Resolution errors after FilterPrelude:\n{"\n".intercalate msgs}"

end Strata.Python.AnalyzeLaurelTest
