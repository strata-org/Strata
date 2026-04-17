/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Laurel.FilterPrelude
import Strata.Languages.Laurel.LaurelCompilationPipeline
public import Strata.Languages.Python.PythonToLaurel
import Strata.Languages.Python.ReadPython
import Strata.Languages.Python.PythonLaurelCorePrelude
import Strata.Languages.Python.PythonRuntimeLaurelPart
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM
import Strata.Languages.Python.Specs.IdentifyOverloads
import Strata.Languages.Python.Specs.ToLaurel
import Strata.Util.DecideProp
import Strata.Util.Profile

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
  /-- Module prefixes used when building pyspec Laurel names. -/
  modulePrefixes : List String := []

/-! ### Private Helpers -/

/-- Convert a SpecDefault to a Python None expression. -/
private def specDefaultToExpr : Python.Specs.SpecDefault → Python.expr SourceRange
  | .none => .Constant default (.ConNone default) default

/-- Convert a pyspec Arg to a PythonFunctionDecl arg tuple. -/
private def specArgToFuncDeclArg (arg : Python.Specs.Arg): Python.PyArgInfo :=
  -- Map each SpecType atom to its PyLauType tag.
  -- Multi-atom types (e.g., Optional[str] = [NoneType, str]) produce
  -- multiple entries so getUnionTypeConstraint generates a disjunction.
  let tys := arg.type.atoms.toList.filterMap fun a => match a with
    | .ident nm _ => Python.PythonIdent.toPyLauType? nm
    | _ => none
  -- Fall back to ["Any"] if no atoms were recognized (unknown types
  -- should not generate constraints).
  let tys := if tys.isEmpty then ["Any"] else tys
  {name := arg.name, md := default, tys := tys, default := arg.default.map specDefaultToExpr}

/-- Build a PythonFunctionDecl from a PySpec FunctionDecl or class method,
    expanding `**kwargs` TypedDict fields into individual parameters. -/
private def funcDeclToFunctionDecl (name : String) (args : Python.Specs.ArgDecls)
    : Except String Python.PythonFunctionDecl := do
  let kwargsArgs ← Python.Specs.ToLaurel.expandKwargsArgs args.kwargs
  let allArgs := args.args ++ args.kwonly ++ kwargsArgs
  pure { name, args := allArgs.toList.map specArgToFuncDeclArg,
         kwargsName := none, ret := none }

/-- Extract PythonFunctionDecl entries from pyspec signatures.
    Handles both top-level functions and class methods.
    Strips `self` from class methods and expands `**kwargs` TypedDict fields. -/
private def extractFunctionSignatures (sigs : Array Python.Specs.Signature)
    (modulePrefix : String) : Except String (List Python.PythonFunctionDecl) := do
  let prefixName (n : String) := if modulePrefix.isEmpty then n else modulePrefix ++ "_" ++ n
  let mut result : List Python.PythonFunctionDecl := []
  for sig in sigs do
    match sig with
    | .functionDecl func =>
      if !func.isOverload then
        result := result ++ [← funcDeclToFunctionDecl (prefixName func.name) func.args]
    | .classDef cls =>
      let clsName := prefixName cls.name
      for method in cls.methods do
        if method.args.args.size == 0 then
          throw s!"Method '{cls.name}.{method.name}' has no arguments (expected 'self' as first parameter)"
        let posArgs := method.args.args.extract 1 method.args.args.size  -- strip self
        let decl ← funcDeclToFunctionDecl (clsName ++ "@" ++ method.name) { method.args with args := posArgs }
        result := result ++ [decl]
    | _ => pure ()
  return result

/-! ### Building PySpec Laurel Declarations -/

private def mergeOverloads (old new : OverloadTable) : OverloadTable :=
  new.fold (init := old) fun o name n =>
    o.alter name fun s => some <| s.getD {} |>.union n



/-- Read PySpec Ion files and collect their Laurel declarations and overload
    tables into a single combined result. Each Ion file is parsed and translated
    to Laurel via `signaturesToLaurel`. The resulting procedures and types are
    accumulated into one `Laurel.Program`, and overload dispatch entries are
    merged into a single table.

    Each entry is a `(modulePrefix, ionPath)` pair. The `modulePrefix` is used
    to namespace all generated Laurel names (e.g., `"servicelib_Storage"` for
    module `servicelib.Storage`). -/
public def buildPySpecLaurel (pyspecEntries : Array (String × String))
    (overloads : OverloadTable) (quiet : Bool := false) : EIO String PySpecLaurelResult := do
  let mut combinedProcedures : Array (Laurel.Procedure × String) := #[]
  let mut combinedTypes : Array (Laurel.TypeDefinition × String) := #[]
  let mut allOverloads := overloads
  let mut funcSigs : List Python.PythonFunctionDecl := []
  let mut allTypeAliases : Std.HashMap String String := {}
  let mut allExhaustiveClasses : Std.HashSet String := {}
  for (modulePrefix, ionPath) in pyspecEntries do
    let ionFile : System.FilePath := ionPath
    let sigs ←
      match ← Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg => throw s!"Could not read {ionFile}: {msg}"
    let { program, errors, overloads, typeAliases, exhaustiveClasses } :=
      Python.Specs.ToLaurel.signaturesToLaurel ionPath sigs modulePrefix
    if errors.size > 0 && !quiet then
      let _ ← IO.eprintln
        s!"{errors.size} PySpec translation warning(s) for {ionPath}:" |>.toBaseIO
      for err in errors do
        let _ ← IO.eprintln s!"  {err.file}: {err.message}" |>.toBaseIO
    allOverloads := mergeOverloads allOverloads overloads
    allTypeAliases := typeAliases.fold (init := allTypeAliases) fun m k v => m.insert k v
    allExhaustiveClasses := exhaustiveClasses.fold (init := allExhaustiveClasses) fun s name => s.insert name
    match extractFunctionSignatures sigs modulePrefix with
    | .ok fs => funcSigs := funcSigs ++ fs
    | .error msg => throw msg
    for td in program.types do
      combinedTypes := combinedTypes.push (td, ionPath)
    for proc in program.staticProcedures do
      combinedProcedures := combinedProcedures.push (proc, ionPath)
  -- Reject name collisions across PySpec files
  let mut seenTypes : Std.HashMap String String := {}
  for (td, srcFile) in combinedTypes do
    let name := match td with
      | .Composite ct => ct.name.text
      | .Constrained ct => ct.name.text
      | .Datatype dt => dt.name.text
    match seenTypes.get? name with
    | some prevFile =>
      throw s!"PySpec type name collision: '{name}' defined in both {prevFile} and {srcFile}"
    | none => pure ()
    seenTypes := seenTypes.insert name srcFile
  let mut seenProcs : Std.HashMap String String := {}
  for (proc, srcFile) in combinedProcedures do
    match seenProcs.get? proc.name.text with
    | some prevFile =>
      throw s!"PySpec procedure name collision: '{proc.name.text}' defined in both {prevFile} and {srcFile}"
    | none => pure ()
    seenProcs := seenProcs.insert proc.name.text srcFile

  let combinedLaurel : Laurel.Program := {
    staticProcedures := Strata.Python.pythonRuntimeLaurelPart.staticProcedures ++ combinedProcedures.toList.map Prod.fst
    staticFields := []
    types := Strata.Python.pythonRuntimeLaurelPart.types ++ combinedTypes.toList.map Prod.fst
    constants := []
  }
  return { laurelProgram := combinedLaurel, overloads := allOverloads
           functionSignatures := funcSigs, typeAliases := allTypeAliases
           exhaustiveClasses := allExhaustiveClasses
           modulePrefixes := (pyspecEntries.map (·.1)).toList }

/-- Read dispatch Ion files and merge their overload tables. -/
public def readDispatchOverloads
    (dispatchPaths : Array String)
    (quiet : Bool := false)
    : EIO String OverloadTable := do
  let mut tbl : OverloadTable := {}
  for dispatchPath in dispatchPaths do
    let ionFile : System.FilePath := dispatchPath
    let sigs ←
      match ← Python.Specs.readDDM ionFile |>.toBaseIO with
      | .ok t => pure t
      | .error msg => throw s!"Could not read dispatch file {ionFile}: {msg}"
    let (overloads, errors) :=
      Python.Specs.ToLaurel.extractOverloads dispatchPath sigs
    if errors.size > 0 && !quiet then
      let _ ← IO.eprintln
        s!"{errors.size} dispatch warning(s) for {ionFile}:" |>.toBaseIO
      for err in errors do
        let _ ← IO.eprintln s!"  {err.file}: {err.message}" |>.toBaseIO
    for (funcName, fnOverloads) in overloads do
      let existing := tbl.getD funcName {}
      tbl := tbl.insert funcName
        (fnOverloads.fold (init := existing)
          fun acc k v => acc.insert k v)
  return tbl

/-- Resolve a module name to a `(modulePrefix, ionPath)` pair for
    `buildPySpecLaurel`.  Returns `none` if the pyspec file is not found. -/
private def resolveModuleEntry (modName : String) (specDir : System.FilePath)
    (quiet : Bool := false)
    : EIO String (Option (String × String)) := do
  match Python.Specs.ModuleName.ofString modName with
  | .error _ =>
    if !quiet then
      let _ ← IO.eprintln
        s!"warning: invalid module name '{modName}', skipping" |>.toBaseIO
    return none
  | .ok mod =>
    match ← mod.specIonPath specDir with
    | some specPath =>
      let pfx := "_".intercalate mod.components.toList
      return some (pfx, specPath.toString)
    | none => return none

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
    (quiet : Bool := false)
    : EIO String PySpecLaurelResult := do
  -- Resolve dispatch module names to Ion paths
  let mut dispatchPaths : Array String := #[]
  for modName in dispatchModules do
    match ← resolveModuleEntry modName specDir (quiet := quiet) with
    | some (_, path) => dispatchPaths := dispatchPaths.push path
    | none => throw s!"Dispatch module '{modName}' not found in {specDir}"
  let dispatchOverloads ← readDispatchOverloads dispatchPaths (quiet := quiet)
  let resolveState :=
    Python.Specs.IdentifyOverloads.resolveOverloads dispatchOverloads stmts
  if !quiet then
    for w in resolveState.warnings do
      let _ ← IO.eprintln s!"warning: {w}" |>.toBaseIO
  -- Auto-resolve pyspec modules from overload table
  let mut autoSpecEntries : Array (String × String) := #[]
  if dispatchModules.size > 0 then
    let resolvedMods := resolveState.modules.toArray.qsort (· < ·)
    for modName in resolvedMods do
      match ← resolveModuleEntry modName specDir (quiet := quiet) with
      | some entry => autoSpecEntries := autoSpecEntries.push entry
      | none =>
        if !quiet then
          let _ ← IO.eprintln
            s!"warning: auto-resolved pyspec not found for module '{modName}'" |>.toBaseIO
  -- Resolve explicit pyspec module names
  let mut explicitEntries : Array (String × String) := #[]
  for modName in pyspecModules do
    match ← resolveModuleEntry modName specDir (quiet := quiet) with
    | some entry => explicitEntries := explicitEntries.push entry
    | none => throw s!"PySpec module '{modName}' not found in {specDir}"
  let allSpecEntries := autoSpecEntries ++ explicitEntries
  buildPySpecLaurel allSpecEntries dispatchOverloads (quiet := quiet)

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
    let inlinable := merged.inlinableProcedures.contains name
    m.insert name (.procedure name sig inlinable)
  -- Register functions under their Laurel names
  let symbols := merged.functions.foldl (init := symbols) fun m name =>
    m.insert name (.function name)
  -- Register unprefixed procedure aliases for pyspec top-level functions.
  -- When a pyspec module "heapq" defines "heappop", the Laurel procedure
  -- is "heapq_heappop". User code that does `from heapq import heappop`
  -- calls it as plain "heappop", so we register that alias here.
  let symbols := result.modulePrefixes.foldl (init := symbols) fun syms pfx =>
    if pfx.isEmpty then syms
    else
      let pfxUnderscore := pfx ++ "_"
      merged.procedures.fold (init := syms) fun m name sig =>
        if name.startsWith pfxUnderscore then
          let shortName := name.drop pfxUnderscore.length |>.toString
          -- Skip class methods (contain @) and don't overwrite existing
          if !shortName.contains '@' && !m.contains shortName then
            let inlinable := merged.inlinableProcedures.contains name
            m.insert shortName (.procedure name sig inlinable)
          else m
        else m
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
          let inlinable := merged.inlinableProcedures.contains name
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

/-- Recursively rename identifiers in a StmtExpr tree. -/
private partial def renameIdent (oldName newName : String) : Laurel.StmtExprMd → Laurel.StmtExprMd
  | ⟨.Identifier id, md⟩ =>
    if id.text == oldName then ⟨.Identifier { id with text := newName }, md⟩
    else ⟨.Identifier id, md⟩
  | ⟨.PrimitiveOp op args, md⟩ =>
    ⟨.PrimitiveOp op (args.map (renameIdent oldName newName)), md⟩
  | ⟨.StaticCall callee args, md⟩ =>
    ⟨.StaticCall callee (args.map (renameIdent oldName newName)), md⟩
  | ⟨.IfThenElse c t e, md⟩ =>
    ⟨.IfThenElse (renameIdent oldName newName c) (renameIdent oldName newName t)
      (e.map (renameIdent oldName newName)), md⟩
  | ⟨.Block stmts lbl, md⟩ =>
    ⟨.Block (stmts.map (renameIdent oldName newName)) lbl, md⟩
  | ⟨.Assign tgts val, md⟩ =>
    ⟨.Assign (tgts.map (renameIdent oldName newName)) (renameIdent oldName newName val), md⟩
  | ⟨.FieldSelect tgt fld, md⟩ =>
    ⟨.FieldSelect (renameIdent oldName newName tgt) fld, md⟩
  | other => other

/-- Combine PySpec and user Laurel programs into a single program,
    prepending External stubs so the Laurel `resolve` pass can see
    prelude names (e.g. `print`, `from_string`).
    Also copies preconditions and postconditions from pyspec procedures
    to matching user-code procedures. -/
public def combinePySpecLaurel
    (pySpec user : Laurel.Program)
    (modulePrefixes : List String := []) : Laurel.Program :=
  -- Build a map from unprefixed name → pyspec preconditions
  let pyspecPreconds : Std.HashMap String (List Laurel.StmtExprMd) :=
    modulePrefixes.foldl (init := {}) fun m pfx =>
      if pfx.isEmpty then m
      else
        let pfxUnderscore := pfx ++ "_"
        pySpec.staticProcedures.foldl (init := m) fun m proc =>
          if proc.name.text.startsWith pfxUnderscore && !proc.preconditions.isEmpty then
            let shortName := proc.name.text.drop pfxUnderscore.length |>.toString
            if !shortName.contains '@' then m.insert shortName proc.preconditions
            else m
          else m
  -- Extract postconditions from pyspec procedure bodies (Body.Opaque postconds ...)
  let pyspecPostconds : Std.HashMap String (List Laurel.StmtExprMd) :=
    modulePrefixes.foldl (init := {}) fun m pfx =>
      if pfx.isEmpty then m
      else
        let pfxUnderscore := pfx ++ "_"
        pySpec.staticProcedures.foldl (init := m) fun m proc =>
          if proc.name.text.startsWith pfxUnderscore then
            match proc.body with
            | .Opaque postconds _ _ =>
              if !postconds.isEmpty then
                let shortName := proc.name.text.drop pfxUnderscore.length |>.toString
                if !shortName.contains '@' then m.insert shortName postconds
                else m
              else m
            | _ => m
          else m
  -- Copy preconditions and postconditions to matching user-code procedures.
  -- When postconditions are present, wrap the user body in Body.Opaque so
  -- the Laurel pipeline can verify the body against the postconditions.
  -- Postconditions reference "result" but user code uses "LaurelResult",
  -- so we rename the identifier in the postcondition expressions.
  let userProcs := user.staticProcedures.map fun proc =>
    let proc := match pyspecPreconds[proc.name.text]? with
      | some preconds => { proc with preconditions := preconds }
      | none => proc
    match pyspecPostconds[proc.name.text]? with
    | some postconds =>
      match proc.body with
      | .Transparent bodyExpr =>
        -- Rename "result" → "LaurelResult" in postconditions to match user code output
        let renamedPostconds := postconds.map (renameIdent "result" "LaurelResult")
        -- Prepend assume(isfrom_int(param)) for each input parameter.
        let mkMd (e : Laurel.StmtExpr) : Laurel.StmtExprMd := ⟨e, bodyExpr.md⟩
        let assumes := proc.inputs.map fun param =>
          mkMd (.Assume (mkMd (.StaticCall (Laurel.mkId "Any..isfrom_int") [mkMd (.Identifier param.name)])))
        let wrappedBody := mkMd (.Block (assumes ++ [bodyExpr]) none)
        { proc with body := .Opaque renamedPostconds (some wrappedBody) [] }
      | _ => proc
    | none => proc
  { staticProcedures := pySpec.staticProcedures ++ userProcs
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
    : IO (Option Core.Program × List DiagnosticModel × Laurel.Program) := do
  let (coreOption, errors, lowered) ←
    Laurel.translateWithLaurel { inlineFunctionsWhenPossible := true } combined
      (keepAllFilesPrefix := keepAllFilesPrefix)
  return (coreOption.map appendCorePartOfRuntime, errors, lowered)

/-- Translate a combined Laurel program to Core and prepend the full
    runtime prelude. -/
public def translateCombinedLaurel (combined : Laurel.Program)
    : IO (Option Core.Program × List DiagnosticModel) := do
  let (coreOption, errors, _) ← translateCombinedLaurelWithLowered combined
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

/-- Run the pyAnalyzeLaurel pipeline: read a Python Ion program,
    resolve overloads from dispatch files, load PySpec declarations,
    translate Python to Laurel, and combine with PySpec Laurel.
    Returns the combined Laurel program ready for
    `translateCombinedLaurel`.

    `dispatchModules` and `pyspecModules` are dotted module names
    resolved against `specDir`.

    The optional `sourcePath` overrides the file path embedded in
    Laurel metadata (useful when the Ion file was generated from a
    `.py` source and you want line numbers to refer to the original). -/
public def pythonAndSpecToLaurel
    (pythonIonPath : String)
    (dispatchModules : Array String := #[])
    (pyspecModules : Array String := #[])
    (sourcePath : Option String := none)
    (specDir : System.FilePath := ".")
    (profile : Bool := false)
    (quiet : Bool := false)
    : EIO PipelineError Laurel.Program := do
  let stmts ← profileStep profile "Read Python Ion" do
    match ← Python.readPythonStrata pythonIonPath |>.toBaseIO with
    | .ok r => pure r
    | .error msg => throw (.internal msg)

  let result ← profileStep profile "Resolve and build Laurel prelude" do
    match ← resolveAndBuildLaurelPrelude dispatchModules pyspecModules stmts specDir (quiet := quiet) |>.toBaseIO with
    | .ok r => pure r
    | .error msg => throw (.internal msg)
  let preludeInfo := buildPreludeInfo result

  let metadataPath := sourcePath.getD pythonIonPath
  let (laurelProgram, _ctx) ← profileStep profile "Translate Python to Laurel" do
    match Python.pythonToLaurel' preludeInfo stmts metadataPath result.overloads with
    | .error (.userPythonError range msg) => throw (.userCode range msg)
    | .error (.unsupportedConstruct msg ast) =>
        throw (.knownLimitation s!"Unsupported construct: {msg}\nAST: {ast}")
    | .error e => throw (.internal s!"Python to Laurel translation failed: {e}")
    | .ok result => pure result

  let filteredPrelude ← profileStep profile "Filter prelude" do
    match Laurel.filterPrelude result.laurelProgram laurelProgram with
    | .ok prog => pure prog
    | .error msg => throw (.internal msg)

  profileStep profile "Combine PySpec and user Laurel" do
    return combinePySpecLaurel filteredPrelude laurelProgram result.modulePrefixes

end Strata
