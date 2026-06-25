/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all StrataDDM.Util.String
import Strata.Languages.Laurel.FilterPrelude
import Strata.Languages.Laurel.LaurelCompilationPipeline
public import StrataPython.PythonToLaurel
import StrataPython.ReadPython
import StrataPython.PythonLaurelCorePrelude
import StrataPython.PythonRuntimeLaurelPart
import StrataPython.Specs
import StrataPython.Specs.DDM
import StrataPython.Specs.IdentifyOverloads
import StrataPython.Specs.MessageKind
import StrataPython.Specs.ToLaurel
public import Strata.Pipeline.Context
public import Strata.Util.Statistics
import StrataPython.Resolution
import StrataPython.Translation
import Strata.Languages.FineGrainLaurel.Elaborate

/-! ## PySpec Pipeline

Implementation of the Python-to-Core pipeline via PySpec and Laurel.
Reads PySpec Ion files, resolves overloads, builds Laurel declarations,
and translates through to Core for verification.
-/

namespace StrataPython
open Strata
open StrataPython.ToLaurel

open Pipeline (emitMessage emitMessageAndAbort)

/-! ### Types -/

/-- Result of reading PySpec files: combined Laurel declarations and overload table. -/
public structure PySpecLaurelResult where
  laurelProgram : Laurel.Program
  overloads : OverloadTable
  functionSignatures : List PythonFunctionDecl := []
  /-- Maps unprefixed class names to prefixed names for type resolution. -/
  typeAliases : Std.HashMap String String := {}
  /-- Classes whose spec is considered exhaustive (lists all methods). -/
  exhaustiveClasses : Std.HashSet String := {}
  deriving Inhabited

/-! ### Private Helpers -/

/-- Convert a SpecDefault to a Python None expression. -/
private def specDefaultToExpr : Specs.SpecDefault → expr SourceRange
  | .none => .Constant default (.ConNone default) default

/-- Compute `laurelType` for a pyspec parameter.
    Mirrors `specTypeToLaurelType` in ToLaurel.lean: builtins → `Any`,
    other single-ident types → `UserDefined(prefixedName)`.
    Uses the type's own module (not the function's module) to derive the
    Laurel prefix, so cross-module type references resolve correctly. -/
private def specArgLaurelType (arg : Specs.Arg) : Laurel.HighTypeMd :=
  match arg.type.asIdent with
  | some id =>
    if id ∈ Specs.ToLaurel.builtinIdents then
      AnyTy
    else
      mkHighTypeMd (.UserDefined { text := id.toLaurelName })
  | none => AnyTy

/-- Convert a pyspec Arg to a PythonFunctionDecl arg info.
    `typeTesters` is empty because `buildSpecBody` already generates type
    assertions in the procedure body — call-site preconditions would be
    redundant. -/
private def specArgToFuncDeclArg (arg : Specs.Arg) : PyArgInfo :=
  { name := arg.name,
    source := none,
    laurelType := specArgLaurelType arg,
    typeTesters := #[],
    default := arg.default.map specDefaultToExpr
  }

/-- Build a PythonFunctionDecl from a PySpec FunctionDecl or class method,
    expanding `**kwargs` TypedDict fields into individual parameters. -/
private def funcDeclToFunctionDecl (name : String) (args : Specs.ArgDecls)
    : Except String PythonFunctionDecl := do
  let kwargsArgs ← Specs.ToLaurel.expandKwargsArgs args.kwargs
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
private def extractFunctionSignatures (sigs : Array Specs.Signature)
    (moduleName : ModuleName) : Except String (Array PythonFunctionDecl) := do
  let funcPrefix := moduleName.toString (sep := "_") ++ "_"
  let mut result : Array PythonFunctionDecl := #[]
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

    Each entry is a `(moduleName, ionPath)` pair. The module name is used
    to namespace all generated Laurel names (e.g., `"servicelib_Storage"` for
    module `servicelib.Storage`). -/
private def buildPySpecLaurelM (pyspecEntries : Array (ModuleName × String))
    (overloads : OverloadTable) : Pipeline.PipelineM PySpecLaurelResult := do
  let mut combinedProcedures : Array (Laurel.Procedure × String) := #[]
  let mut combinedTypes : Array (Laurel.TypeDefinition × String) := #[]
  let mut allOverloads := overloads
  let mut funcSigs : Array PythonFunctionDecl := #[]
  let mut allTypeAliases : Std.HashMap String String := {}
  let mut allExhaustiveClasses : Std.HashSet String := {}
  for (moduleName, ionPath) in pyspecEntries do
    let ionFile : System.FilePath := ionPath
    let sigs ←
      match ← Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg =>
        emitMessageAndAbort .pySpecReadError msg (file := ionFile)
    let { program, errors, overloads, typeAliases, exhaustiveClasses } :=
      Specs.ToLaurel.signaturesToLaurel ionPath sigs moduleName
    for msg in errors do
      Pipeline.addMessage msg
      if msg.kind.impact.isFatal then throw ()
    allOverloads := mergeOverloads allOverloads overloads
    allTypeAliases := typeAliases.fold (init := allTypeAliases) fun m k v => m.insert k v
    allExhaustiveClasses := exhaustiveClasses.fold (init := allExhaustiveClasses) fun s name => s.insert name
    match extractFunctionSignatures sigs moduleName with
    | .ok fs => funcSigs := funcSigs ++ fs
    | .error msg =>
      emitMessageAndAbort .functionSignatureError msg (file := ionFile)
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
      emitMessageAndAbort .typeNameCollision s!"'{ident.text}' already defined in {prevFile}"
        (file := srcFile) (loc := ident.source.map (·.range) |>.getD default)
    | none =>
      seenTypes := seenTypes.insert ident.text srcFile
      dedupedTypes := dedupedTypes.push (td, srcFile)
  let mut seenProcs : Std.HashMap String String := {}
  let mut dedupedProcs : Array (Laurel.Procedure × String) := #[]
  for (proc, srcFile) in combinedProcedures do
    match seenProcs[proc.name.text]? with
    | some prevFile =>
      emitMessageAndAbort .procedureNameCollision s!"'{proc.name.text}' already defined in {prevFile}"
        (file := srcFile) (loc := proc.name.source.map (·.range) |>.getD default)
    | none =>
      seenProcs := seenProcs.insert proc.name.text srcFile
      dedupedProcs := dedupedProcs.push (proc, srcFile)

  let combinedLaurel : Laurel.Program := {
    staticProcedures := pythonRuntimeLaurelPart.staticProcedures ++ dedupedProcs.toList.map Prod.fst
    staticFields := []
    types := pythonRuntimeLaurelPart.types ++ dedupedTypes.toList.map Prod.fst
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
    (pyspecEntries : Array (ModuleName × String))
    (overloads : OverloadTable) : EIO Unit PySpecLaurelResult :=
  buildPySpecLaurelM pyspecEntries overloads |>.run ctx

/-- Read dispatch Ion files and merge their overload tables. -/
private def readDispatchOverloadsM
    (dispatchPaths : Array String) : Pipeline.PipelineM OverloadTable := do
  let mut tbl : OverloadTable := {}
  for dispatchPath in dispatchPaths do
    let ionFile : System.FilePath := dispatchPath
    let sigs ←
      match ← Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg =>
        emitMessageAndAbort .pySpecReadError msg (file := ionFile)
    let (overloads, errors) := Specs.ToLaurel.extractOverloads dispatchPath sigs
    for msg in errors do
      Pipeline.addMessage msg
      if msg.kind.impact.isFatal then throw ()
    tbl := mergeOverloads tbl overloads
  return tbl

/-- Read dispatch Ion files and merge their overload tables. -/
public def readDispatchOverloads
    (ctx : Pipeline.PipelineContext)
    (dispatchPaths : Array String) : EIO Unit OverloadTable :=
  readDispatchOverloadsM dispatchPaths |>.run ctx

/-- Resolve a parsed module name to its .ion path.
    Returns `none` if the file is not found on disk. -/
private def resolveModuleEntry (mod : ModuleName) (specDir : System.FilePath)
    : Pipeline.PipelineM (Option (ModuleName × String)) := do
  match ← mod.specIonPath specDir with
  | some specPath =>
    return some (mod, specPath.toString)
  | none => return none

/-- Resolve already-parsed module names that must exist. Fatal on missing file. -/
private def resolveModuleNames (modules : Array ModuleName) (specDir : System.FilePath)
    : Pipeline.PipelineM (Array (ModuleName × String)) := do
  let mut entries : Array (ModuleName × String) := #[]
  for mod in modules do
    let some entry ← resolveModuleEntry mod specDir
      | emitMessageAndAbort .missingPySpecModule
          s!"PySpec module '{mod}' not found in {specDir}" (file := specDir)
    entries := entries.push entry
  return entries

/-- Resolve module name strings that must exist. Fatal on invalid name or missing file. -/
private def resolveModules (modules : Array String) (specDir : System.FilePath)
    : Pipeline.PipelineM (Array (ModuleName × String)) := do
  let mut parsed : Array ModuleName := #[]
  for modName in modules do
    let some mod := ModuleName.ofString? modName
      | emitMessageAndAbort .invalidModuleName s!"invalid module name '{modName}'" (file := specDir)
    parsed := parsed.push mod
  resolveModuleNames parsed specDir


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
    (stmts : Array (stmt SourceRange))
    (specDir : System.FilePath := ".")
    : Pipeline.PipelineM PySpecLaurelResult := do
  -- Dispatch modules (fatal on invalid name or missing file)
  let dispatchEntries ← resolveModules dispatchModules specDir
  let dispatchPaths := dispatchEntries.map (·.2)
  let dispatchOverloads ← readDispatchOverloadsM dispatchPaths
  let resolveState :=
    Specs.IdentifyOverloads.resolveOverloads dispatchOverloads stmts
  for w in resolveState.warnings do
    emitMessage .overloadResolveWarning w (file := specDir)
  -- Auto-resolved from dispatch overload table
  let autoSpecEntries ←
    if dispatchModules.size > 0 then
      let resolvedMods := resolveState.modules.toArray.qsort (· < ·)
      resolveModuleNames resolvedMods specDir
    else pure #[]
  -- Explicit pyspec modules (fatal on invalid name or missing file)
  let explicitEntries ← resolveModules pyspecModules specDir
  buildPySpecLaurelM (autoSpecEntries ++ explicitEntries) dispatchOverloads

/-! ### Pipeline Steps -/

/-- Build PreludeInfo by merging the base Core prelude with PySpec
    Laurel-level declarations and extracted function signatures. -/
public def buildPreludeInfo (result : PySpecLaurelResult) : PreludeInfo :=
  let baseInfo := PreludeInfo.ofCoreProgram { decls := coreOnlyFromRuntimeCorePart }
  let merged := baseInfo.merge
    (PreludeInfo.ofLaurelProgram result.laurelProgram)
  -- Build importedSymbols from merged info + type aliases
  -- Register composite types under their Laurel names
  let symbols : Std.HashMap String ImportedSymbol :=
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
  { decls := coreFromLaurel.decls ++ coreOnlyFromRuntimeCorePart  }

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
    (pipelineCtx : Option Pipeline.PipelineContext := none)
    : IO (Option Core.Program × List DiagnosticModel × Laurel.Program × Statistics) := do
  let (coreOption, errors, lowered, stats) ←
    Laurel.translateWithLaurel { inlineFunctionsWhenPossible := true, keepAllFilesPrefix }
      combined (pipelineCtx := pipelineCtx)
  return (coreOption.map appendCorePartOfRuntime, errors, lowered, stats)

/-- Translate a combined Laurel program to Core and prepend the full
    runtime prelude. -/
public def translateCombinedLaurel (combined : Laurel.Program) (keepAllFilesPrefix : Option String := none)
    : IO (Option Core.Program × List DiagnosticModel) := do
  let (coreOption, errors, _, _) ← translateCombinedLaurelWithLowered combined keepAllFilesPrefix
  return (coreOption, errors)


/-- Run the pyAnalyzeLaurel pipeline: read a Python Ion program,
    resolve overloads from dispatch files, load PySpec declarations,
    translate Python to Laurel, and combine with PySpec Laurel.

    `dispatchModules` and `pyspecModules` are dotted module names
    resolved against `specDir`.

    The optional `sourcePath` overrides the file path embedded in
    Laurel metadata (useful when the Ion file was generated from a
    `.py` source and you want line numbers to refer to the original).

    Runs in `PipelineM`. Fatal errors abort via `emitMessageAndAbort`. -/
public def pythonAndSpecToLaurel
    (pythonIonPath : String)
    (dispatchModules : Array String := #[])
    (pyspecModules : Array String := #[])
    (sourcePath : Option String := none)
    (specDir : System.FilePath := ".")
    : Pipeline.PipelineM Laurel.Program := do
  let stmts ← Pipeline.withPhase "readPythonIon" do
    match ← readPythonStrata pythonIonPath |>.toBaseIO with
    | .ok r => pure r
    | .error msg =>
      emitMessageAndAbort (file := pythonIonPath) .pySpecParsingError msg

  let result ← Pipeline.withPhase "resolveAndBuildPrelude" do
    resolveAndBuildLaurelPrelude dispatchModules pyspecModules stmts specDir

  let preludeInfo := buildPreludeInfo result
  let metadataPath := sourcePath.getD pythonIonPath

  let (laurelProgram, _ctx) ←
    match pythonToLaurel preludeInfo stmts metadataPath result.overloads with
    | .error (.userPythonError range msg) =>
      emitMessageAndAbort (file := sourcePath.getD pythonIonPath) (loc := range)
        .laurelLoweringUserError msg
    | .error (.unsupportedConstruct msg ast) =>
      emitMessageAndAbort (file := sourcePath.getD pythonIonPath)
        .laurelLoweringNotImpl s!"Unsupported construct: {msg}\nAST: {ast}"
    | .error e =>
      emitMessageAndAbort (file := sourcePath.getD pythonIonPath)
        .laurelLoweringError s!"Python to Laurel translation failed: {e}"
    | .ok result => pure result

  let filteredPrelude ←
    match Laurel.filterPrelude result.laurelProgram laurelProgram with
    | .ok prog => pure prog
    | .error msg =>
      emitMessageAndAbort (file := sourcePath.getD pythonIonPath) .laurelLoweringError msg

  let combined := combinePySpecLaurel filteredPrelude laurelProgram
  return combined

/-- Names that are unmodeled in the Python runtime (external stdlib, boto3 clients, etc.).
    These are pre-registered in the Laurel resolver's scope as `.unresolved` entries so
    that references to them produce no "not defined" diagnostics.
    Lives here in the Python pipeline, not in the generic Laurel resolver. -/
public def pythonUnmodeledNames : Std.HashSet String :=
  ([ "datetime", "timedelta", "Client", "bytes", "MyInt",
     "Any..as_Composite!", "Any..isfrom_Composite", "from_Composite",
     "date", "timezone", "UTC", "BotocoreError", "ClientError",
     "Dict", "list_to_bool", "dict_to_bool", "float_to_bool",
     "Any_set_to_Any", "Any_list_to_Any", "Any_enumerate_to_Any",
     "Any_dict_to_Any", "Any_range_to_Any",
     "PDiv", "Any_sum_to_Any", "to_int_any", "to_float_any",
     "Any_isinstance_to_bool", "RDS",
     "PBitAnd", "PBitOr", "PBitXor", "PLShift", "PRShift",
     "Any_max_to_Any", "Any_min_to_Any", "Any_hasattr_to_bool",
     "Any_any_to_bool", "Any_all_to_bool", "Any_zip_to_Any",
     "Any_map_to_Any", "Any_filter_to_Any", "Any_sorted_to_Any",
     "Any_reversed_to_Any", "Any_tuple_to_Any", "Any_frozenset_to_Any",
     "Callable", "OperationModel", "StructureShape", "IAMClient",
     "STSClient", "SFNClient", "GetCallerIdentityResponseTypeDef",
     "CreateStateMachineOutputTypeDef", "CreateRoleResponseTypeDef",
     "EC2Client", "S3Client", "DynamoDBClient", "LambdaClient",
     "KMSClient", "SNSClient", "SQSClient", "BedrockClient",
     "BedrockRuntimeClient", "ECSClient", "EKSClient", "ECRClient",
     "CloudWatchClient", "CloudFormationClient", "SecretsManagerClient",
     "SSMClient", "GlacierClient", "PinpointClient", "NeptuneClient",
     "IoTSiteWiseClient", "HealthLakeClient", "DeepLensClient",
     "client", "session", "AsyncIterator", "ServiceResource",
     "SchedulerWrapper", "Iterator", "Generator"
  ] : List String).foldl (fun s n => s.insert n) {}

/-- Python gradual types: names consistent with everything (the dynamic top type).
    `Any` is Python's dynamic type. `re_Match` types the `from_Composite`/
    `Any..as_Composite!` bridge stubs (the prelude cannot name the synthesized
    `Composite`, so it borrows a named composite that flattens to it); making it
    gradual lets a class instance of ANY class flow into the bridge at the
    pre-flatten resolves; post-flatten both sides are `Composite`. -/
public def pythonGradualTypes : Std.HashSet String :=
  (["Any", "re_Match"] : List String).foldl (fun s n => s.insert n) {}

/-- Wrap `e` in a unary `StaticCall` to the named prelude function. -/
private def pyCoerceCall (name : String) (e : Laurel.StmtExprMd) : Laurel.StmtExprMd :=
  { val := .StaticCall { text := name, uniqueId := none } [e], source := e.source }

/-- Classify a Python/Laurel `HighType` to the prelude box/unbox vocabulary key.
    Mirrors the elaborator's `eraseType` (Elaborate.lean): user-defined classes are
    `Composite`; `Any`/containers keep their core name; Python `float` is `real`. -/
private def pyTypeKey : Laurel.HighType → String
  | .TInt => "int" | .TBool => "bool" | .TString => "str"
  | .TFloat64 => "float" | .TReal => "float" | .TVoid => "void"
  | .TCore "real" => "float"
  | .TCore n => n
  | .UserDefined id => match id.text with
    | "Any" => "Any" | "ListAny" => "ListAny" | "DictStrAny" => "DictStrAny"
    | "Error" | "OptionInt" | "Box" | "Field" | "TypeTag" => id.text
    | _ => "Composite"   -- every user class boxes/unboxes as Composite
  | _ => "Any"

/-- Python REALIZER for the abstract `Coercion` verdict. Transcribes the gradual
    (inject/project) rows of the elaborator's `subtype` table (Elaborate.lean:483-521)
    into concrete prelude calls. `inject` boxes a concrete value into `Any` by the
    SOURCE type; `project` unboxes/casts out of `Any` by the TARGET type. `upcast`
    (nominal) and `refl` are identity. Truthiness/numeric-widening are NOT here —
    they are not subtyping (handled by `pythonToBool` / inside prelude ops). -/
public def pythonRealizeCoercion : Laurel.Coercion → Laurel.StmtExprMd → Laurel.StmtExprMd
  | .refl, e => e
  | .upcast, e => e
  | .inject source, e =>
    match pyTypeKey source with
    | "int" => pyCoerceCall "from_int" e
    | "bool" => pyCoerceCall "from_bool" e
    | "str" => pyCoerceCall "from_str" e
    | "float" => pyCoerceCall "from_float" e
    | "ListAny" => pyCoerceCall "from_ListAny" e
    | "DictStrAny" => pyCoerceCall "from_DictStrAny" e
    | "Composite" => pyCoerceCall "from_Composite" e
    | "void" => { val := .StaticCall { text := "from_None", uniqueId := none } [], source := e.source }
    | _ => e   -- already Any or a type with no boxing witness: pass through
  | .project target, e =>
    match pyTypeKey target with
    | "int" => pyCoerceCall "Any..as_int!" e
    | "bool" => pyCoerceCall "Any_to_bool" e
    | "str" => pyCoerceCall "Any..as_string!" e
    | "float" => pyCoerceCall "Any..as_float!" e
    | "ListAny" => pyCoerceCall "Any..as_ListAny!" e
    | "DictStrAny" => pyCoerceCall "Any..as_Dict!" e
    | "Composite" => pyCoerceCall "Any..as_Composite!" e
    | _ => e

/-- Python truthiness coercion for boolean context. Any value used where a `bool`
    is expected is run through `Any_to_bool` (Python user values are `Any`). For an
    already-concrete `bool` it is identity. -/
public def pythonToBool : Laurel.StmtExprMd → Laurel.HighType → Laurel.StmtExprMd
  | e, .TBool => e
  | e, _ => pyCoerceCall "Any_to_bool" e

/-- V2 variant of `translateCombinedLaurel` that pre-registers Python's unmodeled
    external names so the Laurel resolver emits no "not defined" diagnostics for them.
    `extraExternalNames` adds program-specific unmodeled names (e.g. names imported from
    unmodeled modules like `botocore.config.Config`, `pyspark.SparkContext`). -/
private def translateCombinedLaurelV2 (combined : Laurel.Program)
    (extraExternalNames : Std.HashSet String := {})
    : IO (Option Core.Program × List DiagnosticModel) := do
  let allExternal := extraExternalNames.fold (fun s n => s.insert n) pythonUnmodeledNames
  let (coreOption, errors, _, _) ←
    Laurel.translateWithLaurel
      { inlineFunctionsWhenPossible := true
        externalNames := allExternal
        gradualTypes := pythonGradualTypes
        realizeCoercion := some pythonRealizeCoercion
        toBool := some pythonToBool }
      combined
  return (coreOption.map appendCorePartOfRuntime, errors)

/-- Collect names bound by `import`/`from … import …` at the top level of a Python program.
    These are external (their defining modules are unmodeled), so the Laurel resolver must
    treat them as `.unresolved` rather than emitting "'Config' is not defined". This makes
    unmodeled-library usage (boto3 `Config`/`Session`, pyspark `SparkContext`, etc.) sound-
    but-uninterpreted instead of a hard pipeline failure. -/
private def collectImportedNames (stmts : Array (StrataPython.stmt SourceRange)) : Std.HashSet String := Id.run do
  let mut names : Std.HashSet String := {}
  for s in stmts do
    match s with
    | .Import _ aliases =>
      for a in aliases.val do
        match a with
        | .mk_alias _ modName asName =>
          match asName.val with
          | some aliasName => names := names.insert aliasName.val
          | none => names := names.insert modName.val
    | .ImportFrom _ _ imports _ =>
      for a in imports.val do
        match a with
        | .mk_alias _ impName asName =>
          match asName.val with
          | some aliasName => names := names.insert aliasName.val
          | none => names := names.insert impName.val
    | _ => pure ()
  return names

/-- Assemble the Laurel program to elaborate: merge user code and demanded imported stubs. -/
private def assembleElaborationInput
    (userLaurel importedLaurel : Laurel.Program) : Laurel.Program :=
  { staticProcedures := userLaurel.staticProcedures ++ importedLaurel.staticProcedures
    staticFields := userLaurel.staticFields
    types := userLaurel.types ++ importedLaurel.types
    constants := userLaurel.constants }

/-- V2 pipeline: Resolution → Translation → Elaboration → resolve → Core.
    Specs/imports enter via `Resolution.resolve` (loads `.python.st.ion` stubs)
    → `Translation.runTranslation`; exceptions are threaded by `fullElaborate`;
    the resolve + coerce + laurel passes happen in `translateCombinedLaurel`. -/
public def pyAnalyzeV2ToCore (pythonIonPath : String) (sourcePath : Option String := none)
    : IO (Except String (Option Core.Program × List DiagnosticModel)) := do
  let baseDir     := System.FilePath.mk pythonIonPath |>.parent.getD "."
  let metadataPath := sourcePath.getD pythonIonPath
  -- Step 1: Read + resolve
  let stmts ← match ← (readPythonStrata pythonIonPath).toBaseIO with
    | .error msg => return .error s!"read: {msg}"
    | .ok s => pure s
  let resolveResult ← match ← (Resolution.resolve stmts baseDir).toBaseIO with
    | .error msg => return .error s!"resolution: {msg}"
    | .ok r => pure r
  -- Step 2: Translate (user code + demanded imports)
  let importedLaurel : Laurel.Program :=
    match Translation.runTranslation { stmts := resolveResult.demandedStmts, moduleLocals := [] } metadataPath with
    | .ok (prog, _) => prog
    | .error _ => default
  let userLaurel ← match Translation.runTranslation resolveResult.program metadataPath with
    | .error e => return .error s!"translation: {repr e}"
    | .ok (prog, _) => pure prog
  -- Step 3: Elaborate (exception threading)
  let toElaborate  := assembleElaborationInput userLaurel importedLaurel
  let fullRuntime  := pythonRuntimeLaurelPart
  -- Build runtime grade map: maps each proc name to its inferred grade.
  let runtimeGrades := fullRuntime.staticProcedures.foldl
    (fun acc proc => acc.insert proc.name.text (FineGrainLaurel.gradeFromSignature proc))
    ({} : Std.HashMap String FineGrainLaurel.Grade)
  let elaboratedProgram ← match FineGrainLaurel.fullElaborate toElaborate fullRuntime runtimeGrades with
    | .error e => return .error s!"elaboration: {e}"
    | .ok (prog, failures) =>
      if !failures.isEmpty then return .error s!"elaboration failures: {String.intercalate ", " failures}"
      pure prog
  -- Step 4: Lower to Core (resolve + coerce + laurel passes).
  -- Use the full runtime (not filtered) to preserve all datatype definitions
  -- (e.g. ListAny, DictStrAny) needed by the Core verifier's termination checker.
  let combined := combinePySpecLaurel fullRuntime elaboratedProgram
  -- Names imported from unmodeled modules (e.g. `from botocore.config import Config`) are
  -- external: register them so the Laurel resolver treats their uses as sound-but-
  -- uninterpreted instead of "'Config' is not defined".
  let importedNames := collectImportedNames stmts
  let (coreOpt, errs) ← translateCombinedLaurelV2 combined importedNames
  return .ok (coreOpt, errs)

end StrataPython
