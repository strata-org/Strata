/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Laurel.FilterPrelude
import Strata.Languages.Laurel.LaurelCompilationPipeline
public import Strata.Util.Statistics
public import Strata.Languages.Python.PythonToLaurel
import Strata.Languages.Python.ReadPython
import Strata.Languages.Python.PythonLaurelCorePrelude
import Strata.Languages.Python.PythonRuntimeLaurelPart
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM
public import Strata.Pipeline.Messages
import Strata.Languages.Python.Specs.IdentifyOverloads
import Strata.Languages.Python.Specs.ToLaurel
import Strata.Util.DecideProp
import all Strata.DDM.Util.String

/-! ## PySpec Pipeline

Implementation of the Python-to-Core pipeline via PySpec and Laurel.
Reads PySpec Ion files, resolves overloads, builds Laurel declarations,
and translates through to Core for verification.
-/

namespace Strata

open Python (OverloadTable)

/-! ### Types -/

/-- Result of reading PySpec files: combined Laurel declarations and overload table. -/
public structure PySpecLaurelResult where
  laurelProgram : Laurel.Program
  overloads : OverloadTable
  functionSignatures : List Python.PythonFunctionDecl := []
  /-- Maps unprefixed class names to prefixed names for type resolution. -/
  typeAliases : Std.HashMap String String := {}
  /-- Classes whose spec is considered exhaustive (lists all methods). -/
  exhaustiveClasses : Std.HashSet String := {}
  deriving Inhabited

/-- Emit a pipeline message. Tags with the current phase from state.
    Throws `()` if the kind's impact is fatal, aborting the pipeline.
    In verbose mode, prints the message immediately to stderr. -/
public def emitMessage (kind : Pipeline.MessageKind) (message : String)
    (file : System.FilePath := default) (loc : SourceRange := default) : Pipeline.PipelineM Unit := do
  let ctx ← read
  let phase ← ctx.currentPhaseRef.get
  ctx.messagesRef.modify (·.push { file, loc, phase, kind, message })
  let mut fields : List (String × Lean.Json) := [
    ("type", .str "diagnostic"), ("phase", .str phase.display),
    ("file", .str file.toString), ("category", .str kind.category),
    ("impact", .str (toString kind.impact)), ("message", .str message)]
  unless loc == default do
    fields := fields ++ [("start", .num loc.start.byteIdx), ("stop", .num loc.stop.byteIdx)]
  ctx.emitMetric (Lean.Json.mkObj fields)
  if ctx.outputMode == .verbose then
    let tag := if kind.impact.isFatal then "error" else "warning"
    let indent := String.replicate ((phase.depth - 1) * 2) ' '
    let _ ← (do IO.eprintln s!"{indent}[{tag}] {file}: {message}"; (← IO.getStderr).flush : IO Unit).toBaseIO
  if kind.impact.isFatal then
    throw ()

/-- Append a batch of messages to the pipeline state.
    Throws `()` if any message has fatal impact.
    In verbose mode, prints each message immediately to stderr. -/
public def addMessages (msgs : Array Pipeline.PipelineMessage) : Pipeline.PipelineM Unit := do
  let ctx ← read
  ctx.messagesRef.modify (· ++ msgs)
  for msg in msgs do
    let mut fields : List (String × Lean.Json) := [
      ("type", .str "diagnostic"), ("phase", .str msg.phase.display),
      ("file", .str msg.file.toString), ("category", .str msg.kind.category),
      ("impact", .str (toString msg.kind.impact)), ("message", .str msg.message)]
    unless msg.loc == default do
      fields := fields ++ [("start", .num msg.loc.start.byteIdx), ("stop", .num msg.loc.stop.byteIdx)]
    ctx.emitMetric (Lean.Json.mkObj fields)
  if ctx.outputMode == .verbose then
    for msg in msgs do
      let tag := if msg.kind.impact.isFatal then "error" else "warning"
      let indent := String.replicate ((msg.phase.depth - 1) * 2) ' '
      let _ ← (do IO.eprintln s!"{indent}[{tag}] {msg.file}: {msg.message}"; (← IO.getStderr).flush : IO Unit).toBaseIO
  if msgs.any (·.kind.impact.isFatal) then
    throw ()

/-! ### Private Helpers -/

/-- Convert a SpecDefault to a Python None expression. -/
private def specDefaultToExpr : Python.Specs.SpecDefault → Python.expr SourceRange
  | .none => .Constant default (.ConNone default) default

/-- Compute `laurelType` for a pyspec parameter.
    Mirrors `specTypeToLaurelType` in ToLaurel.lean: builtins → `Any`,
    other single-ident types → `UserDefined(prefixedName)`.
    Uses the type's own module (not the function's module) to derive the
    Laurel prefix, so cross-module type references resolve correctly. -/
private def specArgLaurelType (arg : Python.Specs.Arg) : Laurel.HighTypeMd :=
  match arg.type.asIdent with
  | some id =>
    if id ∈ Python.Specs.ToLaurel.builtinIdents then
      Python.AnyTy
    else
      Python.mkHighTypeMd (.UserDefined { text := id.toLaurelName })
  | none => Python.AnyTy

/-- Convert a pyspec Arg to a PythonFunctionDecl arg info.
    `typeTesters` is empty because `buildSpecBody` already generates type
    assertions in the procedure body — call-site preconditions would be
    redundant. -/
private def specArgToFuncDeclArg (arg : Python.Specs.Arg) : Python.PyArgInfo :=
  { name := arg.name,
    source := none,
    laurelType := specArgLaurelType arg,
    typeTesters := #[],
    default := arg.default.map specDefaultToExpr
  }

/-- Build a PythonFunctionDecl from a PySpec FunctionDecl or class method,
    expanding `**kwargs` TypedDict fields into individual parameters. -/
private def funcDeclToFunctionDecl (name : String) (args : Python.Specs.ArgDecls)
    : Except String Python.PythonFunctionDecl := do
  let kwargsArgs ← Python.Specs.ToLaurel.expandKwargsArgs args.kwargs
  let allArgs := args.args ++ args.kwonly ++ kwargsArgs
  pure {
    name,
    args := allArgs.toList.map specArgToFuncDeclArg,
    kwargsName := none,
    ret := none
  }

/-- Extract PythonFunctionDecl entries from pyspec signatures.
    Handles both top-level functions and class methods.
    Strips `self` from class methods and expands `**kwargs` TypedDict fields. -/
private def extractFunctionSignatures (sigs : Array Python.Specs.Signature)
    (modulePrefix : String) : Except String (Array Python.PythonFunctionDecl) := do
  let funcPrefix := if modulePrefix.isEmpty then "" else modulePrefix ++ "_"
  let mut result : Array Python.PythonFunctionDecl := #[]
  for sig in sigs do
    match sig with
    | .functionDecl func =>
      if !func.isOverload then
        result := result.push (← funcDeclToFunctionDecl (funcPrefix ++ func.name) func.args)
    | .classDef cls =>
      let clsName := funcPrefix ++ cls.name
      for method in cls.methods do
        if method.args.args.size == 0 then
          throw s!"Method '{cls.name}.{method.name}' has no arguments (expected 'self' as first parameter)"
        let posArgs := method.args.args.extract 1 method.args.args.size  -- strip self
        let decl ← funcDeclToFunctionDecl (clsName ++ "@" ++ method.name) { method.args with args := posArgs }
        result := result.push decl
    | _ => pure ()
  return result

/-! ### Building PySpec Laurel Declarations -/

private def mergeOverloads (old new : OverloadTable) : OverloadTable :=
  new.fold (init := old) fun o name n =>
    o.alter name fun
      | some existing =>
        some { paramName := existing.paramName
               entries := existing.entries.union n.entries }
      | none => some n

/-- Read PySpec Ion files and collect their Laurel declarations and overload
    tables into a single combined result. Each Ion file is parsed and translated
    to Laurel via `signaturesToLaurel`. The resulting procedures and types are
    accumulated into one `Laurel.Program`, and overload dispatch entries are
    merged into a single table.

    Each entry is a `(modulePrefix, ionPath)` pair. The `modulePrefix` is used
    to namespace all generated Laurel names (e.g., `"servicelib_Storage"` for
    module `servicelib.Storage`). -/
private def buildPySpecLaurelM (pyspecEntries : Array (String × String))
    (overloads : OverloadTable) : Pipeline.PipelineM PySpecLaurelResult := do
  let mut combinedProcedures : Array (Laurel.Procedure × String) := #[]
  let mut combinedTypes : Array (Laurel.TypeDefinition × String) := #[]
  let mut allOverloads := overloads
  let mut funcSigs : Array Python.PythonFunctionDecl := #[]
  let mut allTypeAliases : Std.HashMap String String := {}
  let mut allExhaustiveClasses : Std.HashSet String := {}
  for (modulePrefix, ionPath) in pyspecEntries do
    let ionFile : System.FilePath := ionPath
    let sigs ←
      match ← Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg =>
        emitMessage .pySpecReadError msg (file := ionFile)
        continue
    let { program, errors, overloads, typeAliases, exhaustiveClasses } :=
      Python.Specs.ToLaurel.signaturesToLaurel ionPath sigs modulePrefix
    addMessages errors
    allOverloads := mergeOverloads allOverloads overloads
    allTypeAliases := typeAliases.fold (init := allTypeAliases) fun m k v => m.insert k v
    allExhaustiveClasses := exhaustiveClasses.fold (init := allExhaustiveClasses) fun s name => s.insert name
    match extractFunctionSignatures sigs modulePrefix with
    | .ok fs => funcSigs := funcSigs ++ fs
    | .error msg =>
      emitMessage .functionSignatureError msg (file := ionFile)
    for td in program.types do
      combinedTypes := combinedTypes.push (td, ionPath)
    for proc in program.staticProcedures do
      combinedProcedures := combinedProcedures.push (proc, ionPath)
  -- Reject name collisions across PySpec files (first-wins)
  let mut seenTypes : Std.HashMap String String := {}
  let mut dedupedTypes : Array (Laurel.TypeDefinition × String) := #[]
  for (td, srcFile) in combinedTypes do
    let ident := match td with
      | .Composite ct => ct.name
      | .Constrained ct => ct.name
      | .Datatype dt => dt.name
      | .Alias ta => ta.name
    match seenTypes.get? ident.text with
    | some prevFile =>
      emitMessage .typeNameCollision s!"'{ident.text}' already defined in {prevFile}"
        (file := srcFile) (loc := ident.source.map (·.range) |>.getD default)
    | none =>
      seenTypes := seenTypes.insert ident.text srcFile
      dedupedTypes := dedupedTypes.push (td, srcFile)
  let mut seenProcs : Std.HashMap String String := {}
  let mut dedupedProcs : Array (Laurel.Procedure × String) := #[]
  for (proc, srcFile) in combinedProcedures do
    match seenProcs[proc.name.text]? with
    | some prevFile =>
      emitMessage .procedureNameCollision s!"'{proc.name.text}' already defined in {prevFile}"
        (file := srcFile) (loc := proc.name.source.map (·.range) |>.getD default)
    | none =>
      seenProcs := seenProcs.insert proc.name.text srcFile
      dedupedProcs := dedupedProcs.push (proc, srcFile)

  let combinedLaurel : Laurel.Program := {
    staticProcedures := Strata.Python.pythonRuntimeLaurelPart.staticProcedures ++ dedupedProcs.toList.map Prod.fst
    staticFields := []
    types := Strata.Python.pythonRuntimeLaurelPart.types ++ dedupedTypes.toList.map Prod.fst
    constants := []
  }
  return { laurelProgram := combinedLaurel, overloads := allOverloads
           functionSignatures := funcSigs.toList,
           typeAliases := allTypeAliases
           exhaustiveClasses := allExhaustiveClasses }

/-- Read PySpec Ion files and collect their Laurel declarations and overload
    tables into a single combined result. -/
public def buildPySpecLaurel
    (ctx : Pipeline.PipelineContext)
    (pyspecEntries : Array (String × String))
    (overloads : OverloadTable) : EIO Unit PySpecLaurelResult :=
  buildPySpecLaurelM pyspecEntries overloads |>.run ctx

/-- Read dispatch Ion files and merge their overload tables. -/
private def readDispatchOverloadsM
    (dispatchPaths : Array String) : Pipeline.PipelineM OverloadTable := do
  let mut tbl : OverloadTable := {}
  for dispatchPath in dispatchPaths do
    let ionFile : System.FilePath := dispatchPath
    let sigs ←
      match ← Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg =>
        emitMessage .pySpecReadError msg (file := ionFile)
        continue
    let (overloads, errors) := Python.Specs.ToLaurel.extractOverloads dispatchPath sigs
    addMessages errors
    tbl := mergeOverloads tbl overloads
  return tbl

/-- Read dispatch Ion files and merge their overload tables. -/
public def readDispatchOverloads
    (ctx : Pipeline.PipelineContext)
    (dispatchPaths : Array String) : EIO Unit OverloadTable :=
  readDispatchOverloadsM dispatchPaths |>.run ctx

/-- Resolve a parsed module name to its spec prefix and .ion path.
    Returns `none` if the file is not found on disk. -/
private def resolveModuleEntry (mod : Python.Specs.ModuleName) (specDir : System.FilePath)
    : Pipeline.PipelineM (Option (String × String)) := do
  match ← mod.specIonPath specDir with
  | some specPath =>
    let pfx := "_".intercalate mod.components.toList
    return some (pfx, specPath.toString)
  | none => return none

/-- Resolve module names that must exist. Fatal on invalid name or missing file. -/
private def resolveModules (modules : Array String) (specDir : System.FilePath)
    : Pipeline.PipelineM (Array (String × String)) := do
  let mut entries : Array (String × String) := #[]
  for modName in modules do
    match Python.Specs.ModuleName.ofString modName with
    | .error _ =>
      emitMessage .invalidModuleName s!"invalid module name '{modName}'" (file := specDir)
    | .ok mod =>
      let some entry ← resolveModuleEntry mod specDir
        | emitMessage .missingPySpecModule
            s!"PySpec module '{modName}' not found in {specDir}" (file := specDir)
          continue
      entries := entries.push entry
  return entries


/-- Build dispatch overload table, auto-resolve pyspec files
    from the program AST, and return combined Laurel declarations
    and overload table.

    `dispatchModules` and `pyspecModules` are dotted module names
    (e.g., `"servicelib"`, `"servicelib.Storage"`) resolved against
    `specDir`.  Auto-resolved pyspec files that are missing on disk
    are skipped with a warning. -/
public def resolveAndBuildLaurelPrelude
    (dispatchModules : Array String)
    (pyspecModules : Array String)
    (stmts : Array (Python.stmt SourceRange))
    (specDir : System.FilePath := ".")
    : Pipeline.PipelineM PySpecLaurelResult := do
  -- Dispatch modules (fatal on invalid name or missing file)
  let dispatchEntries ← resolveModules dispatchModules specDir
  let dispatchPaths := dispatchEntries.map (·.2)
  let dispatchOverloads ← readDispatchOverloadsM dispatchPaths
  let resolveState :=
    Python.Specs.IdentifyOverloads.resolveOverloads dispatchOverloads stmts
  for w in resolveState.warnings do
    emitMessage .overloadResolveWarning w (file := specDir)
  -- Auto-resolved from dispatch overload table
  let autoSpecEntries ←
    if dispatchModules.size > 0 then
      let resolvedMods := resolveState.modules.toArray.qsort (· < ·)
      resolveModules resolvedMods specDir
    else pure #[]
  -- Explicit pyspec modules (fatal on invalid name or missing file)
  let explicitEntries ← resolveModules pyspecModules specDir
  buildPySpecLaurelM (autoSpecEntries ++ explicitEntries) dispatchOverloads

/-! ### Pipeline Steps -/

/-- Build PreludeInfo by merging the base Core prelude with PySpec
    Laurel-level declarations and extracted function signatures. -/
public def buildPreludeInfo (result : PySpecLaurelResult) : Python.PreludeInfo :=
  let baseInfo := Python.PreludeInfo.ofCoreProgram { decls := Python.coreOnlyFromRuntimeCorePart }
  let merged := baseInfo.merge
    (Python.PreludeInfo.ofLaurelProgram result.laurelProgram)
  -- Build importedSymbols from merged info + type aliases
  -- Register composite types under their Laurel names
  let symbols : Std.HashMap String Python.ImportedSymbol :=
    merged.compositeTypes.fold (init := {}) fun m name =>
      m.insert name (.compositeType name)
  -- Register procedures under their Laurel names
  let symbols := merged.procedures.fold (init := symbols) fun m name sig =>
    let inlinable := merged.callableProcedures.contains name
    m.insert name (.procedure name sig inlinable)
  -- Register functions under their Laurel names
  let symbols := merged.functions.foldl (init := symbols) fun m name =>
    m.insert name (.function name)
  -- Add unprefixed aliases from typeAliases
  let symbols := result.typeAliases.fold (init := symbols)
    fun syms unprefixed prefixed =>
      -- Composite type alias: Storage → dispatch_test_Storage_Storage
      let syms := if merged.compositeTypes.contains prefixed then
        syms.insert unprefixed (.compositeType prefixed) else syms
      -- Procedure aliases: Storage@put_item → ...
      let syms := merged.procedures.fold (init := syms) fun s name sig =>
        if name.startsWith (prefixed ++ "@") then
          let unprefixedName := unprefixed ++ name.drop prefixed.length
          let inlinable := merged.callableProcedures.contains name
          s.insert unprefixedName (.procedure name sig inlinable)
        else s
      -- Function aliases
      merged.functions.foldl (init := syms) fun s name =>
        if name.startsWith (prefixed ++ "@") then
          s.insert (unprefixed ++ name.drop prefixed.length) (.function name)
        else s
  -- Add unprefixed aliases to exhaustiveClasses
  let exhaustive := result.typeAliases.fold (init := result.exhaustiveClasses)
    fun s unprefixed prefixed =>
      if result.exhaustiveClasses.contains prefixed then s.insert unprefixed else s
  { merged with
    functionSignatures :=
      result.functionSignatures ++ merged.functionSignatures
    importedSymbols := symbols
    exhaustiveClasses := exhaustive }

/-- Combine PySpec and user Laurel programs into a single program,
    prepending External stubs so the Laurel `resolve` pass can see
    prelude names (e.g. `print`, `from_string`). -/
public def combinePySpecLaurel
    (pySpec user : Laurel.Program) : Laurel.Program :=
  { staticProcedures := pySpec.staticProcedures ++ user.staticProcedures
    staticFields := pySpec.staticFields ++ user.staticFields
    types := pySpec.types ++ user.types
    constants := pySpec.constants ++ user.constants
  }

/-- Append the Core part of the Python runtime (datatype definitions,
    procedure bodies, etc.) to the Core program produced by Laurel
    translation. -/
private def appendCorePartOfRuntime (coreFromLaurel : Core.Program) : Core.Program :=
  { decls := coreFromLaurel.decls ++ Python.coreOnlyFromRuntimeCorePart  }

/-- Split procedure names in a Core program into prelude names and user names.
    A declaration is considered a user declaration only if its file range
    matches one of the `userSourcePaths`.  When `userSourcePaths` is empty the
    legacy heuristic is used (no file range or empty file ⇒ prelude). -/
public def splitProcNames (prog : Core.Program)
    (userSourcePaths : List String := [])
    : Std.HashSet String × List String :=
  let isUser := fun d =>
    match Imperative.getFileRange (P := Core.Expression) d.metadata with
    | none => false
    | some fr =>
      if userSourcePaths.isEmpty then
        -- Legacy heuristic: anything with a non-empty file is "user".
        fr.file != .file ""
      else
        -- Positive match: only files the caller says are user sources.
        userSourcePaths.any (fr.file == .file ·)
  let (userDecls, preludeDecls) := prog.decls.partition isUser
  let preludeNames := preludeDecls.foldl (init := ({} : Std.HashSet String)) fun s d =>
    match d.getProc? with
    | some p => s.insert (Core.CoreIdent.toPretty p.header.name)
    | none => s
  let userProcNames := userDecls.filterMap fun d =>
    d.getProc?.map (Core.CoreIdent.toPretty ·.header.name)
  (preludeNames, userProcNames)

/-- Like `translateCombinedLaurel` but also returns the lowered Laurel program
    (after all Laurel-to-Laurel passes, before translation to Core).

    When `keepAllFilesPrefix` is provided, the program state after each named
    Laurel pass is written to `{prefix}.{n}.{passName}.laurel.st`. -/
public def translateCombinedLaurelWithLowered (combined : Laurel.Program)
    (keepAllFilesPrefix : Option String := none)
    (profile : Bool := false)
    (pipelineCtx : Option Pipeline.PipelineContext := none)
    : IO (Option Core.Program × List DiagnosticModel × Laurel.Program × Statistics) := do
  let (coreOption, errors, lowered, stats) ←
    Laurel.translateWithLaurel { inlineFunctionsWhenPossible := true, keepAllFilesPrefix, profile }
      combined (pipelineCtx := pipelineCtx)
  return (coreOption.map appendCorePartOfRuntime, errors, lowered, stats)

/-- Translate a combined Laurel program to Core and prepend the full
    runtime prelude. -/
public def translateCombinedLaurel (combined : Laurel.Program)
    (profile : Bool := false)
    : IO (Option Core.Program × List DiagnosticModel) := do
  let (coreOption, errors, _, _) ← translateCombinedLaurelWithLowered combined (profile := profile)
  return (coreOption, errors)

/-- Errors from the pyAnalyzeLaurel pipeline. -/
public inductive PipelineError where
  /-- The Python source contains invalid code (bad method name, wrong arguments, etc.). -/
  | userCode (range : SourceRange := .none) (msg : String)
  /-- The pipeline encountered a Python construct it intentionally does not yet support. -/
  | knownLimitation (msg : String)
  /-- An unexpected failure — likely a bug in the tool itself. -/
  | internal (msg : String)

public instance : ToString PipelineError where
  toString
    | .userCode _ msg => s!"User code error: {msg}"
    | .knownLimitation msg => s!"Known limitation: {msg}"
    | .internal msg => msg

/-- Result of the full Python + PySpec to Laurel pipeline. -/
public inductive PythonToLaurelResult where
  /-- Translation succeeded, possibly with non-fatal warnings. -/
  | success (program : Laurel.Program) (warnings : Array Pipeline.PipelineMessage)
  /-- A fatal error prevented Laurel generation. Warnings collected before
      the failure are still available. -/
  | failure (error : PipelineError) (warnings : Array Pipeline.PipelineMessage)

/-- Get warnings from a pipeline result regardless of success or failure. -/
public def PythonToLaurelResult.warnings : PythonToLaurelResult → Array Pipeline.PipelineMessage
  | .success _ ws => ws
  | .failure _ ws => ws

/-- Run the pyAnalyzeLaurel pipeline: read a Python Ion program,
    resolve overloads from dispatch files, load PySpec declarations,
    translate Python to Laurel, and combine with PySpec Laurel.

    `dispatchModules` and `pyspecModules` are dotted module names
    resolved against `specDir`.

    The optional `sourcePath` overrides the file path embedded in
    Laurel metadata (useful when the Ion file was generated from a
    `.py` source and you want line numbers to refer to the original).

    Returns a `PythonToLaurelResult` containing either the Laurel program
    or a fatal error, along with any accumulated warnings. -/
public def pythonAndSpecToLaurel
    (pythonIonPath : String)
    (dispatchModules : Array String := #[])
    (pyspecModules : Array String := #[])
    (sourcePath : Option String := none)
    (specDir : System.FilePath := ".")
    (pipelineCtx : Pipeline.PipelineContext)
    : BaseIO PythonToLaurelResult := do
  let stmts ←
    match ← pipelineCtx.withPhase "readPythonIon"
        (Python.readPythonStrata pythonIonPath |>.toBaseIO) with
    | .ok r => pure r
    | .error msg => return .failure (.internal msg) #[]

  let resultOrAbort ←
    pipelineCtx.withPhase "resolveAndBuildPrelude"
      (resolveAndBuildLaurelPrelude dispatchModules pyspecModules stmts specDir |>.run pipelineCtx).toBaseIO
  let pyspecWarnings ← pipelineCtx.messagesRef.get

  let result ← match resultOrAbort with
    | .error () => return .failure (.internal "Pipeline aborted due to fatal errors") pyspecWarnings
    | .ok r => pure r

  let preludeInfo := buildPreludeInfo result
  let metadataPath := sourcePath.getD pythonIonPath

  let (laurelProgram, _ctx) ←
    match Python.pythonToLaurel preludeInfo stmts metadataPath result.overloads with
    | .error (.userPythonError range msg) =>
      return .failure (.userCode range msg) pyspecWarnings
    | .error (.unsupportedConstruct msg ast) =>
      return .failure (.knownLimitation s!"Unsupported construct: {msg}\nAST: {ast}") pyspecWarnings
    | .error e =>
      return .failure (.internal s!"Python to Laurel translation failed: {e}") pyspecWarnings
    | .ok result => pure result

  let filteredPrelude ←
    match Laurel.filterPrelude result.laurelProgram laurelProgram with
    | .ok prog => pure prog
    | .error msg => return .failure (.internal msg) pyspecWarnings

  let combined := combinePySpecLaurel filteredPrelude laurelProgram
  return .success combined pyspecWarnings

end Strata
