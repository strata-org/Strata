/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import        Strata.DDM.Format
import all    Strata.DDM.Util.Fin
import        Strata.Languages.Python.ReadPython
import Strata.Languages.Python.Specs.DDM
public import Strata.Languages.Python.Specs.Decls
import        Strata.Languages.Python.Specs.Error
import        Strata.Util.DecideProp

namespace Strata.Python.Specs

/-- Type class for monads that support PySpec error and warning reporting. -/
public class PySpecMClass (m : Type → Type) where
  /-- Report an error at a specific source location. -/
  specError (loc : SourceRange) (message : String) : m Unit
  /-- Report a warning at a specific source location. -/
  specWarning (loc : SourceRange) (message : String) : m Unit
  /-- Run an action and check if any new errors were reported. -/
  runChecked {α} (act : m α) : m (Bool × α)

open PySpecMClass (specError specWarning runChecked)

/-- String identifier for event types. -/
public abbrev EventType := String

/-- Event type for module imports. -/
def importEvent : EventType := "import"

/--
Log message for event type if enabled in the given event set.
Output format: `[event]: message`
-/
public def baseLogEvent (events : Std.HashSet EventType)
    (event : EventType) (message : String) : BaseIO Unit := do
  if event ∈ events then
    let _ ← IO.eprintln s!"[{event}]: {message}" |>.toBaseIO
  pure ()

/--
Creates `PythonToStrataOptions` from an event set.

Enables `logPerf` when `"perf"` is present.
-/
def PythonToStrataOptions.ofEventSet (events : Std.HashSet EventType) : PythonToStrataOptions where
  logPerf := events.contains "perf"

/--
A Python module name split into its dot-separated components.
For example, `typing.List` has components `["typing", "List"]`.
The size constraint ensures at least one component exists.
-/
public structure ModuleName where
  components : Array String
  componentsSizePos : components.size > 0

namespace ModuleName

def ofStringAux (mod : String) (a : Array String) (start cur : mod.Pos) : Except String ModuleName :=
  if h : cur.IsAtEnd then
    let r := mod.extract start cur
    pure {
      components := a.push r
      componentsSizePos := by simp
    }
  else
    let c := cur.get h
    if _ : c = '.' then
      let r := mod.extract start cur
      let next := cur.next h
      ofStringAux mod (a.push r) next next
    else
      let next := cur.next h
      ofStringAux mod a start next
  termination_by cur

/-- Parses a dot-separated module name string (e.g., "typing.List"). -/
public def ofString (mod : String) : Except String ModuleName :=
  ofStringAux mod #[] mod.startPos mod.startPos

public instance : ToString ModuleName where
  toString m :=
    let p : m.components.size > 0 := m.componentsSizePos
    m.components.foldl (init := m.components[0]) (start := 1) (s!"{.}.{.}")

public def foldlDirs {α} (mod : ModuleName) (init : α) (f : α → String → α) : α :=
  mod.components.foldl (init := init) (stop := mod.components.size - 1) f

def foldlMDirs {α m} [Monad m] (mod : ModuleName) (init : α) (f : α → String → m α) : m α := do
  mod.components.foldlM (init := init) (stop := mod.components.size - 1) f

def fileRoot (mod : ModuleName) : String :=
  let p := mod.componentsSizePos
  mod.components.back

/--
Locate the Python source file for a module within `searchPath`.
Navigates subdirectories for intermediate components, then looks for
`{leaf}.py`. Falls back to `{leaf}/__init__.py` for packages.
Returns `(filePath, modulePrefix)` where `modulePrefix` is the array
of package components for resolving relative imports. For `__init__.py`
packages this is all components; for regular files it is all but the last.
-/
public def findInPath (mod : ModuleName) (searchPath : System.FilePath)
    : EIO String (System.FilePath × Array String) := do
  let findComponent path comp := do
        let newPath := path / comp
        if !(← newPath.isDir) then
          throw s!"Directory {newPath} not found"
        return newPath
  let dir ← mod.foldlMDirs (init := searchPath) findComponent
  let file := dir / s!"{mod.fileRoot}.py"
  if let .ok md ← file.metadata |>.toBaseIO then
    if md.type != .file then
      throw s!"{file} is not a regular file."
    let modulePrefix := mod.components.toSubarray (stop := mod.components.size - 1) |>.toArray
    return (file, modulePrefix)
  -- Fall back to __init__.py for packages (directories)
  let pkgDir := dir / mod.fileRoot
  let initFile := pkgDir / "__init__.py"
  if let .ok md ← initFile.metadata |>.toBaseIO then
    if md.type != .file then
      throw s!"{initFile} is not a regular file."
    return (initFile, mod.components)
  -- Fail both
  throw s!"{file} not found (also no {initFile})."

/-- Generates the output filename for a module's spec file. -/
public def strataFileName (mod : ModuleName) : String := s!"{mod.fileRoot}.pyspec.st.ion"

/-- Resolve a module name to a PySpec Ion file path under `specDir`.
    Tries the canonical path first (`specDir/servicelib/Storage.pyspec.st.ion`),
    then falls back to `__init__` layout (`specDir/servicelib/__init__.pyspec.st.ion`)
    for package modules. Returns `none` if neither exists. -/
public def specIonPath (mod : ModuleName) (specDir : System.FilePath)
    : BaseIO (Option System.FilePath) := do
  let canonical := mod.foldlDirs (init := specDir) (· / ·) / mod.strataFileName
  if ← canonical.pathExists then return some canonical
  -- Fall back to __init__ layout for package modules
  let initPath := mod.foldlDirs (init := specDir) (· / ·) / mod.fileRoot / "__init__.pyspec.st.ion"
  if ← initPath.pathExists then return some initPath
  return none

/-- Derive a ModuleName and its search root from a Python source file path.
    For regular files, the root is the parent directory.
    For package init files (`__init__.py`), the module name is the parent
    directory name and the root is the grandparent.
    In both cases, `findInPath mod root` resolves back to the original file. -/
public def ofFile (pythonFile : System.FilePath)
    : Except String (ModuleName × System.FilePath) := do
  let (stem, root) :=
    if pythonFile.fileName == some "__init__.py" then
      (pythonFile.parent >>= (·.fileName), pythonFile.parent >>= (·.parent))
    else
      (pythonFile.fileStem, pythonFile.parent)
  let some s := stem | .error s!"Cannot derive module name from {pythonFile}"
  let some r := root | .error s!"Cannot derive search root from {pythonFile}"
  if s.contains '.' then
    .error s!"File stem '{s}' contains '.'; expected a simple module name (from {pythonFile})"
  pure (← ofString s, r)

-- Unit tests for ofFile
private def testOfFile (path expectedMod expectedRoot : String) : Bool :=
  match ofFile path with
  | .ok (mod, root) => toString mod == expectedMod && root.toString == expectedRoot
  | .error _ => false

#guard testOfFile "path/to/module.py" "module" "path/to"
#guard testOfFile "path/to/service/__init__.py" "service" "path/to"
#guard testOfFile "./module.py" "module" "."
-- Bare filenames without a directory context are rejected
#guard match ofFile "module.py" with | .error _ => true | .ok _ => false
#guard match ofFile "__init__.py" with | .error _ => true | .ok _ => false
-- Dotted file stems are rejected (would be silently split by ofString)
#guard match ofFile "path/to/foo.bar.py" with | .error _ => true | .ok _ => false

end ModuleName

inductive SpecValue
| boolConst (b : Bool)
| dictValue (a : Array (String × SpecValue))
| intConst (loc : SourceRange) (s : Int)
| metaType (name : MetadataType)
| noneConst
| stringConst (loc : SourceRange) (s : String)
| tuple (elts : Array SpecValue)
| typingOverload
| typingTypedDict
| typingRequired
| typingNotRequired
| typingUnpack
| reCompile
| requiredType (type : SpecType)
| notRequiredType (type : SpecType)
| typeValue (type : SpecType)
deriving Inhabited, Repr

structure TypeDecl where
  ident : PythonIdent
  value : SpecValue

/--
Map from Python identifiers to their type specifications.
-/
structure TypeSignature where
  rank : Std.HashMap String (Option (Std.HashMap String SpecValue))

namespace TypeSignature

def ofList (l : List TypeDecl) : TypeSignature where
  rank := l.foldl (init := {}) fun m d =>
    m.alter d.ident.pythonModule fun r =>
      match r with
      | .none => some <| some <| .ofList [(d.ident.name, d.value)]
      | .some none => .some none
      | .some (some m) => m |>.insert d.ident.name d.value

def insert (sig : TypeSignature) (name : String) (m : Option (Std.HashMap String SpecValue)) :=
  { sig with rank := sig.rank.insert name m }

end TypeSignature

/-- Create a type value for prelude types that have no source location. -/
def typeIdent (tp : PythonIdent) : SpecValue := .typeValue  (.ident default tp)

def preludeSig :=
  TypeSignature.ofList [
    .mk .builtinsBool (typeIdent .builtinsBool),
    .mk .builtinsBytearray (typeIdent .builtinsBytearray),
    .mk .builtinsBytes (typeIdent .builtinsBytes),
    .mk .builtinsComplex (typeIdent .builtinsComplex),
    .mk .builtinsDict (typeIdent .builtinsDict),
    .mk .builtinsFloat (typeIdent .builtinsFloat),
    .mk .builtinsInt (typeIdent .builtinsInt),
    .mk .builtinsStr (typeIdent .builtinsStr),
    .mk .noneType (typeIdent .noneType),

    .mk .typingAny (typeIdent .typingAny),
    .mk .typingBinaryIO (typeIdent .typingBinaryIO),
    .mk .typingDict (.metaType .typingDict),
    .mk .typingGenerator (.metaType .typingGenerator),
    .mk .typingList (.metaType .typingList),
    .mk .typingLiteral (.metaType .typingLiteral),
    .mk .typingMapping (.metaType .typingMapping),
    .mk .typingOverload .typingOverload,
    .mk .typingSequence (.metaType .typingSequence),
    .mk .typingTypedDict .typingTypedDict,
    .mk .typingUnion (.metaType .typingUnion),
    .mk .typingRequired .typingRequired,
    .mk .typingNotRequired .typingNotRequired,
    .mk .typingUnpack .typingUnpack,
    .mk .reCompile .reCompile,
  ]

inductive ClassRef where
| unresolved (range : SourceRange)
| resolved

/-- Maps file paths to their FileMap for error location reporting. -/
public abbrev FileMaps := Std.HashMap System.FilePath Lean.FileMap

structure PySpecContext where
  /-- Events to log -/
  eventSet : Std.HashSet String
  /-- Top-level definitions to skip. -/
  skipNames : Std.HashSet PythonIdent := {}
  /-- Command to run for Python -/
  pythonCmd : String
  /-- Path to Python dialect. -/
  dialectFile : System.FilePath
  /-- Path of current Python file being read. -/
  pythonFile : System.FilePath
  /-- Path to write Strata files to. -/
  strataDir : System.FilePath
  /-- Root directory for module resolution. Stays constant across nested imports. -/
  baseSearchPath : System.FilePath
  /-- Package prefix components for resolving relative imports to absolute names.
      For `__init__.py` modules, this is all components (e.g., `#["boto3"]`).
      For regular modules, this is all but the last (e.g., `#["boto3"]` for `boto3.client`).
      Empty for top-level modules with no package. -/
  currentModulePrefix : Array String
  /-- Ref to file map registry for source-location error reporting. -/
  fileMapsRef : IO.Ref FileMaps
  /-- Python module name for the current file (e.g., "boto3.dynamodb").
      Used as `pythonModule` for locally-defined classes. -/
  currentModule : ModuleName

/-- Resolve a module name to a file path, registering the file's FileMap
    for source-location error reporting.  Returns `(filePath, modulePrefix)`
    where `modulePrefix` is the package prefix for resolving relative imports. -/
def PySpecContext.readModule (ctx : PySpecContext) (mod : ModuleName)
    : EIO String (System.FilePath × Array String) := do
  let (pythonPath, modulePrefix) ← mod.findInPath ctx.baseSearchPath
  baseLogEvent ctx.eventSet "findFile"
    s!"Found {mod} as {pythonPath}"
  match ← IO.FS.readFile pythonPath |>.toBaseIO with
  | .ok contents =>
    let fm := Lean.FileMap.ofString contents
    ctx.fileMapsRef.modify fun m => m.insert pythonPath fm
    pure (pythonPath, modulePrefix)
  | .error msg =>
    throw s!"Could not read file {pythonPath}: {msg}"

def preludeAtoms : List (String × PythonIdent) := [
  ("bool", .builtinsBool),
  ("bytearray", .builtinsBytearray),
  ("bytes", .builtinsBytes),
  ("complex", .builtinsComplex),
  ("dict", .builtinsDict),
  ("float", .builtinsFloat),
  ("int", .builtinsInt),
  ("str", .builtinsStr),
]

structure PySpecState where
  typeSigs : TypeSignature := preludeSig
  errors : Array SpecError
  warnings : Array SpecError
  /--
  This maps global identifiers to their value.
  -/
  nameMap : Std.HashMap String SpecValue :=
    preludeAtoms.foldl (init := {}) fun m (nm, pyIdent) =>
      m.insert nm (.typeValue (.ident default pyIdent))
  typeReferences : Std.HashMap String ClassRef := {}
  /--
  Signatures being generated (declarations, functions, classes, etc).
  -/
  elements : Array Signature := #[]

abbrev PySpecM := ReaderT PySpecContext (StateT PySpecState BaseIO)

def logEvent (event : EventType) (message : String) : PySpecM Unit := do
  baseLogEvent (←read).eventSet event message

/-- Check whether a decorator list contains `@overload`. -/
private def hasOverloadDecorator
    (decorators : Array (Strata.Python.expr Strata.SourceRange)) : Bool :=
  decorators.any fun d =>
    match d with
    | .Name _ ⟨_, "overload"⟩ _ => true
    | _ => false

/-- Should we skip the given top-level name? -/
def shouldSkip (name : String) : PySpecM Bool := do
  let ctx ← read
  let nameIdent := { pythonModule := toString ctx.currentModule, name }
  return nameIdent ∈ ctx.skipNames

def specErrorAt (file : System.FilePath) (loc : SourceRange) (message : String) : PySpecM Unit := do
  let e : SpecError := { file, loc, kind := .pySpecParsingError, message }
  modify fun s => { s with errors := s.errors.push e }

instance : PySpecMClass PySpecM where
  specError loc message := do
    specErrorAt (←read).pythonFile loc message
  specWarning loc message := do
    let file := (←read).pythonFile
    let w : SpecError := { file, loc, kind := .pySpecParsingWarning, message }
    modify fun s => { s with warnings := s.warnings.push w }
  runChecked act := do
    let cnt := (←get).errors.size
    let r ← act
    let new_cnt := (←get).errors.size
    return (cnt = new_cnt, r)

def getNameValue? (id : String) : PySpecM (Option SpecValue) :=
  return (←get).nameMap[id]?

def setNameValue (id : String) (v : SpecValue) : PySpecM Unit :=
  modify $ fun s => { s with nameMap := s.nameMap.insert id v }

def recordTypeDef (loc : SourceRange) (cl : String) : PySpecM Unit := do
  match (←get).typeReferences[cl]? with
  | some .resolved =>
    specError loc s!"Class {cl} already defined."
  | _ =>
    modify fun s => { s with
      typeReferences := s.typeReferences.insert cl .resolved
    }

def recordTypeRef (loc : SourceRange) (cl : String) : PySpecM Unit := do
  modify fun s => { s with
    typeReferences := s.typeReferences.insertIfNew cl (.unresolved loc)
  }

def pushSignature (sig : Signature) : PySpecM Unit :=
  modify fun s => { s with elements := s.elements.push sig }

def pushSignatures (sigs : Array Signature) : PySpecM Unit :=
  modify fun s => { s with elements := s.elements ++ sigs }

/--
Type for converting AST expressions to PySpec types
-/
structure TypeTranslator where
  callback : SourceRange -> SpecValue -> PySpecM SpecType

def checkEq {α : Type} (loc : SourceRange) (name : String) (as : Array α) (n : Nat) :
    PySpecM (Option (PULift.{1, 0} (as.size = n))) :=
  match decideProp (as.size = n) with
  | .isTrue p =>
    pure (some ⟨p⟩)
  | .isFalse _ => do
    specError loc s!"{name} expects {n} arguments."
    pure none

def valueAsType (loc : SourceRange) (v : SpecValue) : PySpecM SpecType := do
  match v with
  | .typeValue itp =>
    pure itp
  | .noneConst =>
    return .noneType loc
  | .requiredType tp => return tp
  | .notRequiredType tp => return tp
  | .stringConst loc val =>
    -- Check if this is a known built-in type first
    match ← getNameValue? val with
    | some (.typeValue tp) =>
      return tp
    | _ =>
      recordTypeRef loc val
      let mod := toString (← read).currentModule
      let pyIdent : PythonIdent := { pythonModule := mod, name := val }
      return .ident loc pyIdent
  | _ =>
    specError loc s!"Expected type instead of {repr v}."
    return default

def fixedTranslator (t : PythonIdent) (arity : Nat) : TypeTranslator where
  callback := fun loc arg => do
    if arity = 1 then
      let tp ← valueAsType loc arg
      return .ident loc t #[tp]
    else
      let .tuple args := arg
        | specError loc s!"Expected multiple args instead of {repr arg}."; return default
      let some ⟨_⟩ ← checkEq loc (toString t) args arity
          | return default
      let args ← args.mapM (valueAsType loc)
      return .ident loc t args

def unionTranslator : TypeTranslator where
  callback := fun loc arg => do
    let .tuple args := arg
      | specError loc s!"Union expects tuple"; return default
    let .isTrue argsP := decideProp (args.size > 0)
      | specError loc s!"Union expects at least one argument."; return default
    let tp ← valueAsType loc args[0]
    args.foldlM (start := 1) (init := tp) fun tp v => do
      return SpecType.union loc tp (← valueAsType loc v)

def literalTranslator : TypeTranslator where
  callback := fun loc arg => do
    let args :=
      match arg with
      | .tuple args => args
      |  arg => #[arg]
    let .isTrue _ := decideProp (args.size > 0)
      | specError loc s!"Union expects at least one argument."; return default
    let trans (v : SpecValue) : PySpecM SpecType := do
          match v with
          | .intConst _ n =>
            pure <| .intLiteral loc n
          | .stringConst _ s =>
            pure <| .stringLiteral loc s
          | _ =>
            specError loc s!"Unsupported literal value {repr v}."
            pure default
    return .unionArray loc (← args.mapM trans)

def metadataProcessor : MetadataType → TypeTranslator
| .typingDict => fixedTranslator .typingDict 2
| .typingGenerator => fixedTranslator .typingGenerator 3
| .typingList => fixedTranslator .typingList 1
| .typingLiteral => literalTranslator
| .typingMapping => fixedTranslator .typingMapping 2
| .typingSequence => fixedTranslator .typingSequence 1
| .typingUnion => unionTranslator

def translateCall (loc : SourceRange) (func : SpecValue)
    (args : Array SpecValue) (kwargs : Array (Option String × SpecValue))
    : PySpecM SpecValue := do
  match func with
  | .typingTypedDict =>
    let .isTrue argsSizep := decideProp (args.size = 2)
      | specError loc "TypedDict expects two arguments"; return default
    let .stringConst _ name := args[0]
      | specError loc "TypedDict expects string constant"; return default
    let .dictValue fieldsPairs := args[1]
      | specError loc "TypedDict expects dictionary fields"; return default
    let fields := fieldsPairs |>.map (·.fst)
    -- Determine per-field required status
    if kwargs.size = 0 then
      -- New style: Required[T] / NotRequired[T] per field
      let mut fieldTypes : Array SpecType := #[]
      let mut fieldRequired : Array Bool := #[]
      for (_, v) in fieldsPairs do
        match v with
        | .requiredType tp =>
          fieldTypes := fieldTypes.push tp
          fieldRequired := fieldRequired.push true
        | .notRequiredType tp =>
          fieldTypes := fieldTypes.push tp
          fieldRequired := fieldRequired.push false
        | _ =>
          -- Bare type (no Required/NotRequired wrapper) — treat as required
          fieldTypes := fieldTypes.push (← valueAsType loc v)
          fieldRequired := fieldRequired.push true
      return .typeValue <| .typedDict loc fields fieldTypes fieldRequired
    else
      let .isTrue kwargsSizep := decideProp (kwargs.size = 1)
        | specError loc "TypedDict expects 0 or 1 keywords"; return default
      -- Old style: total= keyword
      let (some "total", totalValue) := kwargs[0]
        | specError loc "TypedDict expects total"; return default
      let .boolConst total := totalValue
        | specError loc "TypedDict expects total bool"; return default
      let values ← fieldsPairs |>.mapM fun (_name, v) => valueAsType loc v
      let fieldRequired := values.map fun _ => total
      return .typeValue <| .typedDict loc fields values fieldRequired
  | _ =>
    specError loc s!"Unknown call {repr func}."
    return default

def translateConstant (loc : SourceRange) (value : constant SourceRange) : PySpecM SpecValue := do
  match value with
  | .ConFalse .. =>
    return .boolConst false
  | .ConTrue .. =>
    return .boolConst true
  | .ConNone _ =>
    return .noneConst
  | .ConPos _ ⟨_, n⟩ =>
    return .intConst loc (Int.ofNat n)
  | .ConNeg _ ⟨_, n⟩ =>
    return .intConst loc (Int.negOfNat n)
  | .ConString _ ⟨_, name⟩ =>
    return .stringConst loc name
  | _ =>
    specError loc s!"Could not interpret constant {value}"
    return default

def translateSubscript (paramLoc : SourceRange) (paramType : String)
      (sargs  : SpecValue) : PySpecM SpecValue := do
  match ← getNameValue? paramType with
  | none =>
    specError paramLoc s!"Unknown parameterized type {paramType}."
    return default
  | some (.typeValue tpp) =>
    let .isTrue tpp_sizep := decideProp (tpp.atoms.size = 1)
      | specError paramLoc s!"Expected type name"
        return default
    let tpa := tpp.atoms[0]
    let .ident tpId tpParams := tpa
      | specError paramLoc "Expected an identifier"
        return default
    if tpId == .builtinsDict ∧ tpParams.size = 0 then
        .typeValue <$> (fixedTranslator .typingDict 2 |>.callback paramLoc sargs)
    else
      specError paramLoc s!"Unsupported type {repr tpId}"
      return default
  | some (.metaType tpId) =>
    let t := metadataProcessor tpId
    .typeValue <$> t.callback paramLoc sargs
  | some .typingRequired =>
    .requiredType <$> valueAsType paramLoc sargs
  | some .typingNotRequired =>
    .notRequiredType <$> valueAsType paramLoc sargs
  | some .typingUnpack =>
    .typeValue <$> valueAsType paramLoc sargs
  | some _ =>
    specError paramLoc s!"Expected {paramType} to be a type."
    return default

def translateDictKey (loc : SourceRange) (mk : opt_expr SourceRange) : PySpecM String := do
  let .some_expr _ k := mk
    | specError loc s!"Dict key missing"; return default
  match k with
  | .Constant _ (.ConString _ ⟨_, key⟩) _ =>
    pure key
  | _ =>
    specError loc s!"Dict key value mismatch"
    return default

mutual

def pyKeywordValue (k : keyword SourceRange) : PySpecM (Option String × SpecValue) := do
  let arg : Option String :=
        match k.arg with
        | ⟨_, none⟩ => none
        | ⟨_, some ⟨_, e⟩⟩ => some e
  pure (arg, ← pySpecValue k.value)
termination_by 2 * sizeOf k
decreasing_by
  cases k
  simp +arith [keyword.value]

def pySpecValue (expr : expr SourceRange) : PySpecM SpecValue := do
  match h : expr with
  | .BinOp loc x op y => do
    match op with
    | .BitOr _ =>
      return .typeValue <| .union loc (← pySpecType x) (← pySpecType y)
    | _ =>
      specError loc s!"Unsupported binary operator {repr op}"
      return default
  | .Call loc pyFunc ⟨_, pyArgs⟩ ⟨_, pyKeywords⟩ =>
    let (success, (func, args, kwargs)) ← runChecked <| do
      let func ← pySpecValue pyFunc
      let args ← pyArgs.attach.mapM fun ⟨e, em⟩ => pySpecValue e
      let kwargs ← pyKeywords.attach.mapM fun ⟨k, km⟩ => pyKeywordValue k
      return (func, args, kwargs)
    if success then
      translateCall loc func args kwargs
    else
      return default
  | .Constant constLoc value ⟨_, kind⟩ =>
    assert! kind.isNone
    translateConstant constLoc value
  | .Dict loc ⟨_, keys⟩ ⟨_, values⟩ =>
    let .isTrue size_eq := decideProp (keys.size = values.size)
      | specError loc s!"Dict key value mismatch"; return default
    let  m : Array (String × SpecValue) ← Array.ofFnM fun (⟨i, _⟩ : Fin keys.size) => do
      let key ← translateDictKey loc keys[i]
      let v ← pySpecValue values[i]
      pure ⟨key, v⟩
    return .dictValue m
  | .Name _ ⟨_, ident⟩ (.Load _) =>
    let some v := ←getNameValue? ident
      | specError expr.ann s!"Unknown identifier {ident}."; return default
    pure v
  | .Attribute _ (.Name _ ⟨_, modName⟩ (.Load _)) ⟨_, attrName⟩ (.Load _) =>
    let qualName := s!"{modName}.{attrName}"
    let some v := ←getNameValue? qualName
      | specError expr.ann s!"Unknown identifier {qualName}."; return default
    pure v
  | .Subscript _ (.Name paramLoc ⟨_, paramType⟩ (.Load _)) subscriptArgs _ =>
    let (success, sargs) ← runChecked <| pySpecValue subscriptArgs
    if success then
      translateSubscript paramLoc paramType sargs
    else
      pure default
  | .Tuple ann ⟨_, pyElts⟩ _ctx =>
    let elts ← pyElts.attach.mapM fun ⟨e, em⟩ => pySpecValue e
    return .tuple elts
  | _ =>
    specError expr.ann s!"Could not interpret {expr}"
    return default
termination_by 2 * sizeOf expr
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

def pySpecType (e : expr SourceRange) : PySpecM SpecType := do
  let (success, v) ← runChecked <| pySpecValue e
  if success then
    valueAsType e.ann v
  else
    return default
termination_by 2 * sizeOf e + 1

end

-- Check expression is compatible with value
def pyDefaultValue (val : expr SourceRange) (_tp : SpecType) : PySpecM Unit := do
  match val with
  | .Constant _ c _ =>
    match c with
    | .ConNone _ =>
      pure ()
    | _ =>
      specError val.ann s!"Unexpected value {toString val}"
  | _ =>
    specError val.ann s!"Unexpected value {toString val}"

def pySpecArg (usedNames : Std.HashSet String)
              (selfType : Option String)
              (arg : Strata.Python.arg Strata.SourceRange)
              (de : Option (expr SourceRange)) : PySpecM Arg := do
  let .mk_arg loc ⟨_, name⟩ ⟨_typeLoc, type⟩ ⟨_, comment⟩ := arg
  if name ∈ usedNames then
    specError loc s!"Argument {name} already declared."
  assert! !loc.isNone
  assert! _typeLoc.isNone
  let tp ←
    match selfType with
    | none =>
      match type with
      | none =>
        specError loc s!"Missing argument to {name}"
        pure default
      | some tp => pySpecType tp
    | some cl =>
      if type.isSome then
        specError loc s!"Unexpected argument to {name}"
      let mod := toString (← read).currentModule
      pure <| .ident loc { pythonModule := mod, name := cl } #[]
  assert! comment.isNone
  let argDefault ←
    match de with
    | none => pure none
    | some d =>
      pyDefaultValue d tp
      pure (some .none)
  return {
    name := name
    type := tp
    default := argDefault
  }

structure SpecAssertionContext where
  filePath : System.FilePath
  kwargsParamName : Option String := none
  kwargsType : Option SpecType := none
  /-- Local variable type bindings (e.g., from for-loop iteration variables). -/
  localTypes : Std.HashMap String SpecType := {}

/-- State for `SpecAssertionM`. -/
structure SpecAssertionState where
  assertions : Array Assertion := #[]
  postconditions : Array SpecExpr := #[]
  errors : Array SpecError := #[]
  warnings : Array SpecError := #[]

/-- Monad for extracting pre and post conditions from methods. -/
abbrev SpecAssertionM := ReaderT SpecAssertionContext (StateM SpecAssertionState)

instance : PySpecMClass SpecAssertionM where
  specError loc message := do
    let file := (←read) |>.filePath
    let e : SpecError := { file, loc, kind := .pySpecParsingError, message }
    modify fun s => { s with errors := s.errors.push e }
  specWarning loc message := do
    let file := (←read) |>.filePath
    let w : SpecError := { file, loc, kind := .pySpecParsingWarning, message }
    modify fun s => { s with warnings := s.warnings.push w }
  runChecked act := do
    let cnt := (←get).errors.size
    let r ← act
    let new_cnt := (←get).errors.size
    return (cnt = new_cnt, r)

/-- Match a subscript expression `param["field"]` against the kwargs parameter
    name from context, returning `(paramName, fieldName)` on success. -/
def extractKwargsField (e : expr SourceRange)
    : SpecAssertionM (Option (String × String)) := do
  match e with
  | .Subscript _ (.Name _ ⟨_, paramName⟩ (.Load _))
      (.Constant _ (.ConString _ ⟨_, fieldName⟩) _) (.Load _) =>
    match (←read).kwargsParamName with
    | some kn =>
      if paramName == kn then return some (kn, fieldName)
      else return none
    | none => return none
  | _ => return none

/-- Extract a `SpecExpr` subject from a Python expression.
    Recognizes kwargs subscripts (`kw["field"]` → `.getIndex (.var kn) fn`),
    nested subscripts (`kw["a"]["b"]` → `.getIndex (.getIndex (.var kn) "a") "b"`),
    and plain variable names (`.Name` → `.var name`).
    Returns `none` for unsupported expression forms. -/
partial def extractSubject (e : expr SourceRange)
    : SpecAssertionM (Option SpecExpr) := do
  match ← extractKwargsField e with
  | some (kn, fn) =>
    return some (.getIndex (.var kn (loc := e.ann)) fn (loc := e.ann))
  | none =>
    pure ()
  match e with
  | .Name _ ⟨_, name⟩ (.Load _) => return some (.var name (loc := e.ann))
  | .Subscript _ inner (.Constant _ (.ConString _ ⟨_, fieldName⟩) _) (.Load _) =>
    match ← extractSubject inner with
    | some subj => return some (.getIndex subj fieldName (loc := e.ann))
    | none => return none
  | _ => return none

/-- Translate a Python `if` condition into a `SpecExpr`.
    Currently recognizes `"key" in container` patterns. -/
def transCondition (e : expr SourceRange) : SpecAssertionM (Option SpecExpr) := do
  match e with
  | .Compare _ (.Constant _ (.ConString _ ⟨_, key⟩) _) ⟨_, ops⟩ ⟨_, comparators⟩ =>
    if h₁ : ops.size = 1 then
      if h₂ : comparators.size = 1 then
        match ops[0] with
        | .In _ =>
          match ← extractSubject comparators[0] with
          | some subj => return some (.containsKey subj key (loc := e.ann))
          | none => pure ()
        | _ => pure ()
    pure ()
  | _ => pure ()
  return none

/-- Run an action that may produce assertions, then wrap each new assertion's
    formula with `implies cond ...` (or `implies (not cond) ...` for else branches).
    If `cond` is `none`, assertions pass through unchanged. -/
def assumeCondition (cond : Option SpecExpr) (loc : SourceRange) (act : SpecAssertionM Unit)
    : SpecAssertionM Unit := do
  let prevAssertions := (←get).assertions
  modify fun s => { s with assertions := #[] }
  act
  let newAssertions := (←get).assertions
  match cond with
  | some c =>
    let wrapped := newAssertions.map fun a =>
      { a with formula := .implies c a.formula loc }
    modify fun s => { s with assertions := prevAssertions ++ wrapped }
  | none =>
    modify fun s => { s with assertions := prevAssertions ++ newAssertions }

/-- Translate a Python expression from an f-string message into a `SpecExpr`.
    Handles kwargs subscripts, variable names, and `len(...)` calls.
    Falls back to `.placeholder` for unsupported patterns. -/
def transMessageExpr (e : expr SourceRange)
    : SpecAssertionM SpecExpr := do
  match ← extractSubject e with
  | some subj => return subj
  | none => pure ()
  match e with
  | .Call _ (.Name _ ⟨_, funcName⟩ (.Load _)) ⟨_, args⟩ _ =>
    if funcName == "len" && args.size == 1 then
      match ← extractSubject args[0]! with
      | some subj => return .len subj (loc := e.ann)
      | none => return .placeholder (loc := e.ann)
    else return .placeholder (loc := e.ann)
  | _ => return .placeholder (loc := e.ann)

/-- Look up a field in a TypedDict SpecType, returning its type if found. -/
def lookupTypedDictField (tp : SpecType) (field : String) : Option SpecType := do
  for atom in tp.atoms do
    match atom with
    | .typedDict fields fieldTypes _ =>
      for i in [:fields.size] do
        if fields[i]! == field then return fieldTypes[i]!
    | _ => pure ()
  none

/-- Infer the type of a Python expression from available type context.
    Handles kwargs subscripts, nested subscripts, and local variable bindings. -/
partial def inferExprType (e : expr SourceRange) : SpecAssertionM (Option SpecType) := do
  match e with
  | .Name _ ⟨_, name⟩ (.Load _) =>
    return (←read).localTypes[name]?
  | .Subscript _ (.Name _ ⟨_, paramName⟩ (.Load _))
      (.Constant _ (.ConString _ ⟨_, fieldName⟩) _) (.Load _) =>
    match (←read).kwargsParamName with
    | some kn =>
      if paramName == kn then
        match (←read).kwargsType with
        | some kwTp => return lookupTypedDictField kwTp fieldName
        | none => return none
      else return none
    | none => return none
  | .Subscript _ inner (.Constant _ (.ConString _ ⟨_, fieldName⟩) _) (.Load _) =>
    match ← inferExprType inner with
    | some innerTp => return lookupTypedDictField innerTp fieldName
    | none => return none
  | _ => return none

/-- Extract the element type from an iterable SpecType (e.g., typing.List(T) → T). -/
def extractElementType (tp : SpecType) : Option SpecType := do
  for atom in tp.atoms do
    match atom with
    | .ident pyId args =>
      if (pyId == .typingList || pyId == .typingSequence) && args.size == 1 then
        return args[0]!
    | _ => pure ()
  none

/-- Extract key and value types from a dict SpecType
    (e.g., typing.Dict(K, V) → (K, V)). -/
def extractDictKeyValueTypes (tp : SpecType) : Option (SpecType × SpecType) := do
  for atom in tp.atoms do
    match atom with
    | .ident pyId args =>
      if (pyId == .typingDict || pyId == .typingMapping) && args.size == 2 then
        return (args[0]!, args[1]!)
    | _ => pure ()
  none

/-- Collect all `== "value"` arms from a chain of `or`-ed comparisons,
    returning the subject and string values, or `none` if the expression
    doesn't fit the pattern
    `subj == "A" or subj == "B" or ...`. -/
partial def collectEnumValues (e : expr SourceRange)
    : SpecAssertionM (Option (SpecExpr × Array String)) := do
  match e with
  | .BoolOp _ (.Or _) ⟨_, values⟩ =>
    let mut result : Option (SpecExpr × Array String) := none
    for val in values do
      match ← collectEnumValues val with
      | some (subj, vals) =>
        match result with
        | none => result := some (subj, vals)
        | some (_prevSubj, acc) =>
          -- TODO: check subject equality once SpecExpr has BEq
          result := some (subj, acc ++ vals)
      | none => return none
    return result
  | .Compare _ lhs ⟨_, ops⟩ ⟨_, comparators⟩ =>
    let .isTrue _ := decideProp (ops.size = 1)
      | return none
    match ops[0] with
    | .Eq _ =>
      let .isTrue _ := decideProp (comparators.size = 1)
        | return none
      match ← extractSubject lhs with
      | some subj =>
        match comparators[0] with
        | .Constant _ (.ConString _ ⟨_, strVal⟩) _ =>
          return some (subj, #[strVal])
        | _ => return none
      | none => return none
    | _ => return none
  | _ => return none

/-- Extract an integer literal from a Python expression.
    Handles `Constant(ConPos n)`, `Constant(ConNeg n)`,
    and `UnaryOp(USub, Constant(ConPos n))` (i.e., `-n`). -/
def extractIntBound (e : expr SourceRange) : Option Int :=
  match e with
  | .Constant _ (.ConPos _ ⟨_, n⟩) _ => some (Int.ofNat n)
  | .Constant _ (.ConNeg _ ⟨_, n⟩) _ => some (Int.negOfNat n)
  | .UnaryOp _ (.USub _) (.Constant _ (.ConPos _ ⟨_, n⟩) _) =>
    some (Int.negOfNat n)
  | _ => none

/-- Extract a float literal string from a Python expression.
    Handles `Constant(ConFloat s)` and `UnaryOp(USub, Constant(ConFloat s))`. -/
def extractFloatBound (e : expr SourceRange) : Option String :=
  match e with
  | .Constant _ (.ConFloat _ ⟨_, s⟩) _ => some s
  | .UnaryOp _ (.USub _) (.Constant _ (.ConFloat _ ⟨_, s⟩) _) => some s!"-{s}"
  | _ => none

/-- Check if a SpecType is the `builtins.int` type. -/
def isIntType (tp : SpecType) : Bool := tp.isAtom (.ident .builtinsInt #[])

/-- Check if a SpecType is the `builtins.float` type. -/
def isFloatType (tp : SpecType) : Bool := tp.isAtom (.ident .builtinsFloat #[])

/-- Build a comparison expression dispatching to float or int variants based on type. -/
private def makeComparison
    (floatCtor intCtor : SpecExpr → SpecExpr → SpecExpr)
    (isFloat isInt : Bool)
    (subj : SpecExpr) (bound : expr SourceRange)
    : SpecAssertionM (Option SpecExpr) := do
  let loc := bound.ann
  if isFloat then
    match extractFloatBound bound with
    | some s => return some (floatCtor subj (.floatLit s (loc := loc)))
    | none =>
      match extractIntBound bound with
      | some n => return some (floatCtor subj (.floatLit (toString n) (loc := loc)))
      | none => return none
  else if isInt then
    match extractIntBound bound with
    | some n => return some (intCtor subj (.intLit n (loc := loc)))
    | none => return none
  else
    match extractIntBound bound with
    | some n => return some (intCtor subj (.intLit n (loc := loc)))
    | none => return none

def transAssertExpr (e : expr SourceRange)
    : SpecAssertionM SpecExpr := do
  let loc := e.ann
  -- isinstance(subject, T)
  match e with
  | .Call _ (.Name _ ⟨_, funcName⟩ (.Load _)) ⟨_, args⟩ _ =>
    if funcName == "isinstance" then
      if h : args.size = 2 then
        match ← extractSubject args[0] with
        | some subj =>
          match args[1] with
          | .Name _ ⟨_, typeName⟩ (.Load _) =>
            return .isInstanceOf subj typeName (loc := loc)
          | _ =>
            specWarning e.ann s!"isinstance: unsupported type argument"
            return .placeholder (loc := loc)
        | none => pure () -- fall through
    if funcName == "len" && args.size == 1 then
      -- This is just len(x), not a comparison; fall through
      pure ()
  | _ => pure ()
  -- len(subject) >= N / len(subject) <= N
  match e with
  | .Compare _ (.Call _ (.Name _ ⟨_, funcName⟩ (.Load _)) ⟨_, callArgs⟩ _)
      ⟨_, ops⟩ ⟨_, comparators⟩ =>
    if funcName == "len" then
      if h₁ : callArgs.size = 1 then
        if h₂ : ops.size = 1 then
          if h₃ : comparators.size = 1 then
            match ← extractSubject callArgs[0] with
            | some subj =>
              match ops[0], extractIntBound comparators[0] with
              | .GtE _, some n => return .intGe (.len subj (loc := loc)) (.intLit n (loc := comparators[0].ann)) (loc := loc)
              | .LtE _, some n => return .intLe (.len subj (loc := loc)) (.intLit n (loc := comparators[0].ann)) (loc := loc)
              | _, _ => pure ()
            | none => pure ()
  | _ => pure ()
  -- subject >= N / subject <= N (type-checked: int or float)
  match e with
  | .Compare _ lhs ⟨_, ops⟩ ⟨_, comparators⟩ =>
    if h₁ : ops.size = 1 then
      if h₂ : comparators.size = 1 then
        match ← extractSubject lhs with
        | some subj =>
          let subjType ← inferExprType lhs
          let isFloat := subjType.any isFloatType
          let isInt := subjType.any isIntType
          let cmp ← match ops[0] with
          | .GtE _ => makeComparison (.floatGe · · (loc := loc)) (.intGe · · (loc := loc)) isFloat isInt subj comparators[0]
          | .LtE _ => makeComparison (.floatLe · · (loc := loc)) (.intLe · · (loc := loc)) isFloat isInt subj comparators[0]
          | _ => pure none
          match cmp with
          | some expr => return expr
          | none => pure ()
        | none => pure ()
  | _ => pure ()
  -- subject == "A" or subject == "B" or ...
  match ← collectEnumValues e with
  | some (subj, vals) =>
    return .enumMember subj vals (loc := loc)
  | none => pure ()
  -- compile("pattern").search(subject) is not None
  match e with
  | .Compare _
      (.Call _ (.Attribute _ (.Call _ (.Name _ ⟨_, compileName⟩ (.Load _)) ⟨_, compileArgs⟩ _)
        ⟨_, searchAttr⟩ (.Load _)) ⟨_, searchArgs⟩ _)
      ⟨_, ops⟩ ⟨_, comparators⟩ =>
    if compileName == "compile" && searchAttr == "search" then
      if h₁ : compileArgs.size = 1 then
        if h₂ : searchArgs.size = 1 then
          if h₃ : ops.size = 1 then
            if h₄ : comparators.size = 1 then
              match compileArgs[0] with
              | .Constant _ (.ConString _ ⟨_, pattern⟩) _ =>
                match ← extractSubject searchArgs[0] with
                | some subj =>
                  match ops[0], comparators[0] with
                  | .IsNot _, .Constant _ (.ConNone _) _ =>
                    return .regexMatch subj pattern (loc := loc)
                  | _, _ => pure ()
                | none => pure ()
              | _ => pure ()
  | _ => pure ()
  -- Fallback: unrecognized pattern
  specWarning e.ann s!"unrecognized assert pattern: {eformat e.toAst}"
  return .placeholder (loc := loc)

mutual

def blockStmt (s : stmt SourceRange) : SpecAssertionM Unit := do
  match s with
  | .Assign _ _targets _value _typeAnn =>
    specWarning s.ann "skipped Assign in function body"
  | .AnnAssign .. =>
    specWarning s.ann "skipped AnnAssign in function body"
  | .Expr _ (.Constant _ (.ConEllipsis _) _) =>
    pure () -- `...` stub body, equivalent to pass
  | .Expr .. =>
    specWarning s.ann "skipped Expr in function body"
  | .Assert _ test msg =>
    let formula ← transAssertExpr test
    let message ← match msg with
      | ⟨_, some (.Constant _ (.ConString _ ⟨_, str⟩) _)⟩ => pure #[MessagePart.str str]
      | ⟨_, some (.JoinedStr _ ⟨_, values⟩)⟩ =>
        values.attach.mapM fun ⟨v, _⟩ =>
          match v with
          | .Constant _ (.ConString _ ⟨_, str⟩) _ => pure (MessagePart.str str)
          | .FormattedValue _ value _ _ =>
            MessagePart.expr <$> transMessageExpr value
          | other => do
            specWarning other.ann "unsupported f-string part"
            pure (MessagePart.str "")
      | ⟨_, none⟩ => pure #[]
      | ⟨_, some e⟩ =>
        specWarning e.ann "assert message is not a string literal"
        pure #[]
    modify fun s => { s with
      assertions := s.assertions.push { message, formula }
    }
  | .Return .. =>
    specWarning s.ann "skipped Return in function body"
  | .Raise .. =>
    specWarning s.ann "skipped Raise in function body"
  | .ClassDef .. =>
    specError s.ann s!"Inner classes are not supported."
  | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ ⟨_, type_comment⟩ =>
    if type_comment.isSome then
      specWarning s.ann "For: type_comment not supported"
    if orelse.size > 0 then
      specWarning s.ann "For: else clause not supported"
    match target, iter with
    -- for varName in iterable:
    | .Name _ ⟨_, varName⟩ (.Store _), _ =>
      match ← extractSubject iter with
      | some listExpr =>
        let elemTp ← do
          match ← inferExprType iter with
          | some iterTp => pure (extractElementType iterTp)
          | none => pure none
        let prevAssertions := (←get).assertions
        modify fun s => { s with assertions := #[] }
        withReader (fun ctx => match elemTp with
          | some tp => { ctx with localTypes := ctx.localTypes.insert varName tp }
          | none => ctx) <|
          blockStmts body
        let bodyAssertions := (←get).assertions
        let wrapped := bodyAssertions.map fun a =>
          { a with formula := .forallList listExpr varName a.formula s.ann }
        modify fun s => { s with assertions := prevAssertions ++ wrapped }
      | none =>
        specWarning s.ann s!"For: cannot extract iterable expression"
    -- for keyVar, valVar in dictExpr.items():
    | .Tuple _ ⟨_, elts⟩ (.Store _),
      .Call _ (.Attribute _ dictExpr ⟨_, "items"⟩ (.Load _)) ⟨_, args⟩ _ =>
      if elts.size != 2 then
        specWarning s.ann "For: dict unpacking requires exactly 2 variables"
      else if args.size != 0 then
        specWarning s.ann "For: .items() call should have no arguments"
      else
        match elts[0]!, elts[1]! with
        | .Name _ ⟨_, keyVar⟩ (.Store _), .Name _ ⟨_, valVar⟩ (.Store _) =>
          match ← extractSubject dictExpr with
          | some dictSubj =>
            -- Type-check: verify the subject is actually a dict type
            let kvTypes ← do
              match ← inferExprType dictExpr with
              | some dictTp =>
                match extractDictKeyValueTypes dictTp with
                | some kv => pure (some kv)
                | none =>
                  specWarning s.ann
                    s!"For: .items() subject is not a Dict/Mapping type"
                  pure none
              | none =>
                specWarning s.ann
                  s!"For: cannot infer type of .items() subject"
                pure none
            let prevAssertions := (←get).assertions
            modify fun st => { st with assertions := #[] }
            withReader (fun ctx => match kvTypes with
              | some (kTp, vTp) =>
                { ctx with localTypes := ctx.localTypes
                    |>.insert keyVar kTp
                    |>.insert valVar vTp }
              | none => ctx) <|
              blockStmts body
            let bodyAssertions := (←get).assertions
            let wrapped := bodyAssertions.map fun a =>
              { a with formula := .forallDict dictSubj keyVar valVar a.formula s.ann }
            modify fun st => { st with assertions := prevAssertions ++ wrapped }
          | none =>
            specWarning s.ann s!"For: cannot extract dict expression"
        | _, _ =>
          specWarning s.ann "For: dict unpacking requires Name targets"
    | _, _ =>
      specWarning s.ann "For: unsupported target pattern"
  | .If _ pred ⟨_, t⟩ ⟨_, f⟩ =>
    let cond ← transCondition pred
    if cond.isNone then
      specWarning pred.ann s!"if: unrecognized condition pattern: {eformat pred.toAst}"
    assumeCondition cond pred.ann <| blockStmts t
    if f.size > 0 then
      assumeCondition (cond.map (.not · pred.ann)) pred.ann <| blockStmts f
  | .Pass _ =>
    pure ()
  | _ => specError s.ann s!"Unsupported statement: {eformat s.toAst}"
termination_by sizeOf s
decreasing_by
  · cases body; decreasing_tactic
  · cases body; decreasing_tactic
  · cases t; decreasing_tactic
  · cases f; decreasing_tactic

def blockStmts (as : Array (stmt SourceRange)) : SpecAssertionM Unit := do
  as.attach.forM fun ⟨b, _⟩ => blockStmt b
termination_by sizeOf as
decreasing_by
· decreasing_tactic

end

def collectAssertions (decls : ArgDecls) (_returnType : SpecType)
    (action : SpecAssertionM Unit)
    : PySpecM SpecAssertionState := do
  let errors := (←get).errors
  let warnings := (←get).warnings
  modify fun s => { s with errors := #[], warnings := #[] }
  let filePath := (←read).pythonFile
  let ctx : SpecAssertionContext :=
    { filePath
      kwargsParamName := decls.kwargs.map Prod.fst
      kwargsType := decls.kwargs.map Prod.snd }
  let ((), as) := action ctx { errors, warnings }
  modify fun s => { s with errors := as.errors, warnings := as.warnings }
  pure as

def pySpecFunctionArgs (fnLoc : SourceRange)
                       (className : Option String)
                       (funName : String)
                       (arguments : arguments SourceRange)
                       (body : Array (Python.stmt SourceRange))
                       (decorators : Array (expr SourceRange))
                       (returns : Option (expr SourceRange)) : PySpecM FunctionDecl := do
  let mut overload : Bool := false
  for pyd in decorators do
    let (success, d) ← runChecked <| pySpecValue pyd
    if success then
      match d with
      | .typingOverload =>
        overload := true
      | _ =>
        specError pyd.ann s!"Decorator {repr d} not supported."

  let .mk_arguments _ ⟨_, posonly⟩ ⟨_, posArgs⟩ ⟨_, vararg⟩ ⟨_, kwonly⟩ ⟨_, kw_defaults⟩ ⟨_, kwarg⟩ ⟨_, defaults⟩ := arguments
  assert! posonly.size = 0
  let argc := posArgs.size

  let .up defaults_bnd ←
    if h : defaults.size ≤ posArgs.size then
      pure <| PULift.up.{1, 0} h
    else
      specError fnLoc s!"internal: bad index"; return default

  let .isTrue kw_bnd := decideProp (kwonly.size = kw_defaults.size)
    | specError fnLoc s!"Keyword only arguments must have defaults."; return default
  assert! vararg.isNone
  let min_default := argc - defaults.size
  let isMethod := className.isSome
  if isMethod ∧ argc = 0 then
    specError fnLoc "Method expecting self argument"
  let mut usedNames : Std.HashSet String := {}
  let mut specArgs : Array Arg := .emptyWithCapacity argc
  for ⟨i, ib⟩ in Fin.range argc do
    let a := posArgs[i]
    -- Arguments with defaults occur at end
    let d : Option _ :=
      if p : i ≥ min_default then
        some defaults[i - min_default]
      else
        none
    let self_type :=
            match className with
            | some cl => if i = 0 then some cl else none
            | none => none
    let ba ← pySpecArg usedNames self_type a d
    usedNames := usedNames.insert ba.name
    specArgs := specArgs.push ba
  let mut kwSpecArgs : Array Arg := .emptyWithCapacity kwonly.size
  for ⟨i, ib⟩ in Fin.range kwonly.size do
    let a := kwonly[i]
    -- Arguments with defaults occur at end
    let d : Option _ :=
        match kw_defaults[i] with
        | .some_expr _ v => some v
        | .missing_expr _ => none
    let ba ← pySpecArg usedNames none a d
    usedNames := usedNames.insert ba.name
    kwSpecArgs := kwSpecArgs.push ba
  -- Handle **kwargs: store parameter name and type
  let mut kwargsOpt : Option (String × SpecType) := none
  match kwarg with
  | none => pure ()
  | some kwargArg =>
    let .mk_arg kwargLoc ⟨_, kwargParamName⟩ ⟨_, kwargType⟩ _ := kwargArg
    match kwargType with
    | some typeExpr =>
      let tp ← pySpecType typeExpr
      kwargsOpt := some (kwargParamName, tp)
    | none => specError kwargLoc s!"**kwargs requires type annotation"
  let argDecls : ArgDecls := { args := specArgs, kwonly := kwSpecArgs, kwargs := kwargsOpt }
  let returnType : SpecType ←
        match returns with
        | none => pure <| .ident fnLoc .typingAny
        | some tp => pySpecType tp
  let as ← collectAssertions argDecls returnType <|
    if overload then
      -- Overload stubs should have `...` as their only body statement.
      unless body.size = 1 &&
             body[0]! matches .Expr _ (.Constant _ (.ConEllipsis _) _) do
        specWarning fnLoc "overload body is not `...`"
    else
      body.forM blockStmt

  return {
    loc := fnLoc
    nameLoc := fnLoc
    name := funName
    args := argDecls
    returnType
    isOverload := overload
    preconditions := as.assertions
    postconditions := as.postconditions
  }

/-- Resolve an array of base class expressions into PythonIdents. -/
private def resolveBaseClasses (bases : Array (expr SourceRange))
    : PySpecM (Array PythonIdent) := do
  let mut result : Array PythonIdent := #[]
  for base in bases do
    match base with
    | .Name _ ⟨_, name⟩ _ =>
      if name == "Exception" then
        result := result.push .builtinsException
      else
        match ← getNameValue? name with
        | some (.typeValue tp) =>
          match tp.asSingleton with
          | some (.ident pyIdent _) =>
            result := result.push pyIdent
          | _ =>
            specError base.ann s!"Unknown base class '{name}'"
        | _ =>
          specError base.ann s!"Unknown base class '{name}'"
    | _ => specError base.ann s!"Unsupported base class expression"
  return result

partial def pySpecClassBody (loc : SourceRange) (className : String)
    (bases : Array PythonIdent)
    (body : Array (Strata.Python.stmt Strata.SourceRange)) : PySpecM ClassDef := do
  let mut usedNames : Std.HashSet String := {}
  let mut fields : Array ClassField := #[]
  let mut classVars : Array ClassVariable := #[]
  let mut subclasses : Array ClassDef := #[]
  let mut methods : Array FunctionDecl := #[]
  for stmt in body do
    match stmt with
    | .Expr _ _ =>
      specWarning stmt.ann s!"skipped Expr in class body ({className})"
    | .AnnAssign _ target annotation _ _ =>
      match target with
      | .Name _ ⟨_, fieldName⟩ _ =>
        let fieldType ← pySpecType annotation
        fields := fields.push { name := fieldName, type := fieldType }
      | _ => specError stmt.ann s!"Unsupported field target"
    | .ClassDef innerLoc ⟨_, innerClassName⟩ ⟨_, innerBases⟩ _keywords ⟨_, innerStmts⟩
                _decorators _typeParams =>
      let innerBaseIdents ← resolveBaseClasses innerBases
      let innerDef ← pySpecClassBody innerLoc innerClassName
        innerBaseIdents innerStmts
      subclasses := subclasses.push innerDef
    | .Assign _ ⟨_, targets⟩ value _typeAnn =>
      if h : targets.size = 1 then
        match targets[0], value with
        | .Name _ ⟨_, varName⟩ _, .Name _ ⟨_, varValue⟩ _ =>
          classVars := classVars.push { name := varName, value := varValue }
        | _, _ => specError stmt.ann s!"Unsupported class variable assignment"
      else
        specError stmt.ann s!"Only single target expected in class variable"
    | .Pass .. => pure ()       -- Skip pass statements
    | .FunctionDef loc ⟨_, name⟩  args ⟨_, body⟩ ⟨_, decorators⟩ ⟨_, returns⟩
                   ⟨_, type_comment⟩ ⟨_, type_params⟩ =>
      if type_comment.isSome then
        specWarning loc "FunctionDef: type_comment not supported"
      if type_params.size > 0 then
        specWarning loc "FunctionDef: type_params not supported"
      if name == "__init__" then
        -- Extract self.field = expr assignments as class fields
        for initStmt in body do
          match initStmt with
          | .Assign _ ⟨_, targets⟩ value _ =>
            if h : targets.size = 1 then
              match targets[0] with
              | .Attribute _ (.Name _ ⟨_, "self"⟩ (.Load _)) ⟨_, fieldName⟩ (.Store _) =>
                -- Try to resolve type from self._ClassName() pattern
                match value with
                | .Call _ (.Attribute _ (.Name _ ⟨_, "self"⟩ (.Load _))
                    ⟨_, innerClsName⟩ (.Load _)) _ _ =>
                  let mod := toString (← read).currentModule
                  let pyIdent : PythonIdent := { pythonModule := mod, name := innerClsName }
                  let f : ClassField := {
                    name := fieldName,
                    type := .ident loc pyIdent #[],
                    constValue := some s!"{innerClsName}()" }
                  fields := fields.push f
                | _ =>
                  specWarning initStmt.ann
                    s!"unsupported __init__ assignment value for self.{fieldName}"
              | _ => specWarning initStmt.ann "unsupported __init__ assignment target"
            else
              specWarning initStmt.ann "unsupported __init__ multi-target assignment"
          | .Expr _ (.Constant _ (.ConEllipsis _) _) => pure ()
          | .Pass .. => pure ()
          | _ => specWarning initStmt.ann s!"unsupported statement in __init__"
      else
        if name ∈ usedNames then
          specError loc s!"{name} already defined."
        let d ← pySpecFunctionArgs (className := some className) loc name args
                                   body decorators returns
        methods := methods.push d
    | _ =>
      specError stmt.ann s!"Unknown class statement {stmt}"
  return {
    loc := loc
    name := className
    bases := bases
    fields := fields
    classVars := classVars
    subclasses := subclasses
    methods := methods
  }

def translateImportFrom (mod : String) (types : Std.HashMap String SpecValue)
      (names : Array (alias SourceRange)) : PySpecM Unit := do
  -- Check if module is a builtin (in prelude) - if so, don't generate extern declarations
  let isBuiltinModule := preludeSig.rank.contains mod
  for a in names do
    let name := a.name
    match types[name]? with
    | none =>
      specError a.ann s!"{name} is not defined in module {mod}."
    | some tpv =>
      let asname := a.asname.getD name
      setNameValue asname tpv
      -- Generate extern declaration for imported types (but not for builtin modules)
      if !isBuiltinModule then
        if let .typeValue _ := tpv then
          let source : PythonIdent := {
            pythonModule := mod
            name := name
          }
          pushSignature (.externTypeDecl asname source)

def getModifiedTime (f : System.FilePath) : IO IO.FS.SystemTime := do
  let md ← f.metadata
  pure <| md.modified

/--
Create a value map for module from signatures.
-/
def signatureValueMap (mod : ModuleName) (sigs : Array Signature) : Std.HashMap String SpecValue :=
  let modName := toString mod
  let addType (m : Std.HashMap String SpecValue) (sig : Signature) :=
        match sig with
        | .classDef d =>
          let pyIdent : PythonIdent := {
            pythonModule := modName
            name := d.name
          }
          m.insert d.name (.typeValue (.ident d.loc pyIdent))
        | .typeDef d =>
          let pyIdent : PythonIdent := {
            pythonModule := modName
            name := d.name
          }
          m.insert d.name (.typeValue (.ident d.loc pyIdent))
        | .externTypeDecl name source =>
          m.insert name (.typeValue (.ident default source))
        | .functionDecl .. => m
  sigs.foldl (init := {}) addType

def checkOverloadBody (stmt : stmt SourceRange) : PySpecM Unit := do
  match stmt with
  | .Expr _ (.Constant _ (.ConEllipsis _) _) => pure ()
  | _ => specError stmt.ann s!"Expected ellipsis"


public def isNewer (path : System.FilePath) (existing : IO.FS.Metadata) : BaseIO Bool := do
  match ← path.metadata |>.toBaseIO with
    | .ok strataMetadata =>
      pure <| strataMetadata.modified > existing.modified
    | .error _ =>
      pure false

/-- Resolve a possibly-relative module name to an absolute one.
    For level-N relative imports, drops (N-1) components from the current
    module prefix and prepends the remainder.  E.g. `from ..X import Y`
    (level 2) in package `a.b.c` resolves to `a.b.X`. -/
def resolveRelativeModuleName (loc : SourceRange) (relName : String) (level : Int)
    : PySpecM String := do
  if level == 0 then return relName
  let pfx := (←read).currentModulePrefix
  if pfx.isEmpty then
    specError loc
      "Cannot use a relative import from a top-level module with no package"
    return relName
  let drop := level.toNat - 1
  if drop >= pfx.size then
    specError loc <|
      s!"Relative import (level {level}) goes beyond the top-level package; " ++
      s!"the current module is only {pfx.size} package level(s) deep"
    return relName
  let base := pfx.toSubarray (stop := pfx.size - drop) |>.toArray
  return ".".intercalate (base.push relName).toList

mutual

/--
Resolves a Python module by name, returning a map of exported identifiers to
their spec values. Loads either from cached PySpec files or by parsing the
Python source if not in cache.
-/
partial def resolveModule (loc : SourceRange) (mod : ModuleName) :
    PySpecM (Std.HashMap String SpecValue) := do
  let (pythonFile, childPrefix) ←
        match ← (←read).readModule mod |>.toBaseIO with
        | .ok r =>
          pure r
        | .error msg =>
          specError loc msg
          return default
  -- Build the output directory for cached .pyspec.st.ion files by mirroring
  -- the module's directory components under the root strata output directory.
  -- E.g., module "service.module" with root "out/" → "out/service/".
  let strataDir := mod.foldlDirs (init := (←read).strataDir) (· / ·)
  let strataFile := strataDir / mod.strataFileName

  let .ok pythonMetadata ← pythonFile.metadata |>.toBaseIO
    | specError loc s!"Could not get file mod time."; return default

  let useStrata : Bool ← isNewer strataFile pythonMetadata
    -- If Strata is newer use it.
  if useStrata then
    match ← readDDM strataFile |>.toBaseIO with
    | .ok sigs =>
      logEvent importEvent s!"Imported {mod} from PySpec file"
      return signatureValueMap mod sigs
    | .error msg =>
      specError loc s!"Could not load Strata file: {msg}"
      return default

  let pythonCmd := (←read).pythonCmd
  let dialectFile := (←read).dialectFile
  let options := PythonToStrataOptions.ofEventSet (←read).eventSet
  let commands ←
    match ← pythonToStrata (pythonCmd := pythonCmd) (options := options)
      dialectFile pythonFile |>.toBaseIO with
    | .ok r => pure r
    | .error msg =>
      specError loc msg
      return default
  let errorCount := (←get).errors.size
  let warningCount := (←get).warnings.size
  let ctx := { (←read) with
    pythonFile := pythonFile
    currentModule := mod
    currentModulePrefix := childPrefix }
  -- This does state shuffling to ensure warnings and errors maintain
  -- a reference count of 1 (for destructive updates).
  let s := ←get
  set { s with errors := #[], warnings := #[] }
  let initState : PySpecState := { errors := s.errors, warnings := s.warnings }
  let (sigs, t) ← translateModuleAux commands |>.run ctx |>.run initState
  let newWarnings := t.warnings.size - warningCount
  modify fun s => { s with errors := t.errors, warnings := t.warnings }
  if t.errors.size > errorCount then
    return default
  let warnMsg := if newWarnings > 0 then s!" ({newWarnings} warning(s))" else ""
  logEvent importEvent s!"Imported {mod}{warnMsg}"

  if let .error msg ← IO.FS.createDirAll strataDir |>.toBaseIO then
    specError loc s!"Could not create directory {strataDir}:  {msg}"
    return default

  if let .error msg ← writeDDM strataFile sigs |>.toBaseIO then
    specError loc s!"Could not write file {strataFile}:  {msg}"
    return default

  return signatureValueMap mod sigs

partial def resolveModuleCached (loc : SourceRange) (mod : ModuleName)
    : PySpecM (Option (Std.HashMap String SpecValue)) := do
  let key := toString mod
  match (←get).typeSigs.rank[key]? with
  | some types =>
    return types
  | none =>
    let (success, r) ← runChecked <| resolveModule loc mod
    let r := if success then some r else none
    modify fun s => { s with typeSigs := s.typeSigs.insert key r }
    return r

/-- Parse a module name string and resolve it, returning `none` on
    parse or resolution failure. -/
partial def parseAndResolveModule (loc : SourceRange) (modName : String)
    : PySpecM (Option (Std.HashMap String SpecValue)) := do
  match ModuleName.ofString modName with
  | .ok mod => resolveModuleCached loc mod
  | .error msg =>
    specError loc msg
    return none

/-- Resolve a module and register its exports under `"{asname}.{name}"`.
    If resolution fails, register `asname` as an opaque extern type. -/
partial def resolveAndRegisterModule (loc : SourceRange)
    (mod asname : String) : PySpecM Unit := do
  if let some types ← parseAndResolveModule loc mod then
    for (name, tpv) in types do
      setNameValue s!"{asname}.{name}" tpv
  else
    let source : PythonIdent := { pythonModule := mod, name := asname }
    let tpv : SpecValue := .typeValue (.ident loc source)
    setNameValue asname tpv
    pushSignature (.externTypeDecl asname source)

/-- Handle a bare `import module` statement by resolving the module and
    registering its exported names under the qualified `module.name` pattern. -/
partial def translateImport (loc : SourceRange)
    (names : Array (alias SourceRange)) : PySpecM Unit := do
  for a in names do
    let mod := a.name
    let asname := a.asname.getD mod
    resolveAndRegisterModule loc mod asname

/-- Handle a `from [..] module import name` statement. Supports absolute
    imports (level 0) and multi-level relative imports (level ≥ 1).
    `pyModule` is the module string (already unwrapped from the annotation).
    `level` is the raw import level from the AST. -/
partial def translateImportFromStmt (loc : SourceRange)
    (pyModule : Option (Ann String SourceRange))
    (names : Array (alias SourceRange))
    (level : Option (int SourceRange)) : PySpecM Unit := do

  let lvl := match level with
    | some lvlE => lvlE.value
    | none => 0

  match pyModule with
  | some ⟨_, relMod⟩ =>
    -- from X import Y  (level 0) or  from .X import Y  (level 1)
    let mod ← resolveRelativeModuleName loc relMod lvl
    if let some types ← parseAndResolveModule loc mod then
      translateImportFrom mod types names
    else
      -- Module resolution failed; register imported names as opaque extern
      -- types so that downstream references don't produce unknown-identifier
      -- errors.
      for a in names do
        let name := a.name
        let asname := a.asname.getD name
        let source : PythonIdent := { pythonModule := mod, name := name }
        let tpv : SpecValue := .typeValue (.ident loc source)
        setNameValue asname tpv
        pushSignature (.externTypeDecl asname source)
  | none =>
    -- from . import X — resolve each name as a sibling module and register
    -- its exports under the qualified "name.export" pattern.
    for a in names do
      let relMod := a.name
      let asname := a.asname.getD relMod
      let mod ← resolveRelativeModuleName loc relMod lvl
      resolveAndRegisterModule loc mod asname

partial def translate (body : Array (stmt Strata.SourceRange)) : PySpecM Unit := do
  for stmt in body do
    match stmt with
    | .Assign loc ⟨_, targets⟩ value _typeAnn =>
      let (success, v) ← runChecked <| pySpecValue value
      if not success then
        continue
      let .isTrue eq := decideProp (targets.size = 1)
        | specError loc s!"Only single target expected."; continue
      let .Name nameLoc ⟨_, name⟩ _ := targets[0]
        | specError loc s!"Unsupported target {targets[0]}"; continue
      assert! !nameLoc.isNone
      setNameValue name v
      match v with
      | .typeValue tp =>
        recordTypeDef loc name
        let d : TypeDef := {
          loc := loc
          nameLoc := nameLoc
          name := name
          definition := tp
        }
        pushSignature <| .typeDef d
      | _ =>
        specWarning loc s!"skipped non-type Assign ({name})"
    | .Expr .. =>
      specWarning stmt.ann "skipped Expr at module level"
    | .FunctionDef loc
                   ⟨_funNameLoc, funName⟩
                   args
                   ⟨_bodyLoc, body⟩
                   ⟨_decoratorsLoc, decorators⟩
                   ⟨_returnsLoc, returns⟩
                   ⟨_typeCommentLoc, typeComment⟩
                   ⟨_typeParamsLoc, typeParams⟩ =>
      if hasOverloadDecorator decorators = false ∧ (←shouldSkip funName) then
        logEvent "skip" s!"Skipping function {funName}"
        continue
      assert! _bodyLoc.isNone
      -- Flag indicating this is an overload
      assert! _decoratorsLoc.isNone
      assert! _returnsLoc.isNone
      assert! _typeCommentLoc.isNone
      assert! typeComment.isNone
      assert! _typeParamsLoc.isNone
      assert! typeParams.size = 0
      let d ← pySpecFunctionArgs (className := none) loc funName args body decorators returns
      pushSignature (.functionDecl d)
    | .Import loc ⟨_, names⟩ =>
      translateImport loc names
    | .ImportFrom loc ⟨_, pyModule⟩ ⟨_, names⟩ ⟨_, level⟩ =>
      translateImportFromStmt loc pyModule names level
    | .ClassDef loc ⟨_classNameLoc, className⟩ ⟨_, bases⟩ ⟨_, keywords⟩ ⟨_, stmts⟩ ⟨_, decorators⟩ ⟨_, typeParams⟩ =>
      if ←shouldSkip className then
        logEvent "skip" s!"Skipping class {className}"
        continue
      assert! _classNameLoc.isNone
      assert! keywords.size = 0
      let isExhaustive := decorators.any fun d =>
        match d with
        | .Name _ ⟨_, "exhaustive"⟩ _ => true
        | _ => false
      assert! decorators.size = 0 || (decorators.size = 1 && isExhaustive)
      assert! typeParams.size = 0
      let baseIdents ← resolveBaseClasses bases
      let (success, _) ← runChecked <| recordTypeDef loc className
      -- Add the class to nameMap so it can be used in forward references
      let mod := toString (← read).currentModule
      setNameValue className (.typeValue (.ident loc { pythonModule := mod, name := className } #[]))
      let d ← pySpecClassBody loc className baseIdents stmts
      let d := { d with exhaustive := isExhaustive }
      if success then
        pushSignature (.classDef d)
    | _ => specError stmt.ann s!"Unknown statement {stmt}"

partial def translateModuleAux (body : Array (Strata.Python.stmt Strata.SourceRange))
  : PySpecM (Array Signature) := do
  let ctx ← read
  let start ← IO.monoNanosNow
  translate body
  let s ← get
  for ⟨cl, t⟩ in s.typeReferences do
    if let .unresolved loc := t then
      specError loc s!"Class {cl} not defined."
  let stop ← IO.monoNanosNow
  let elapsedMs := (stop - start) / 1000000
  baseLogEvent ctx.eventSet "perf" s!"translating {ctx.pythonFile}: {elapsedMs}ms"
  return s.elements

end



/-- Translates Python AST statements to PySpec signatures with dependency resolution. -/
def translateModule
    (dialectFile searchPath strataDir pythonFile : System.FilePath)
    (fileMap : Lean.FileMap)
    (body : Array (Strata.Python.stmt Strata.SourceRange))
    (currentModule : ModuleName)
    (pythonCmd : String := "python")
    (events : Std.HashSet EventType := {})
    (skipNames : Std.HashSet PythonIdent := {})
    (currentModulePrefix : Array String := #[]) :
    BaseIO (FileMaps × Array Signature × Array SpecError × Array SpecError) := do
  let fmm : FileMaps := {}
  let fmm := fmm.insert pythonFile fileMap
  let fileMapsRef : IO.Ref FileMaps ← IO.mkRef fmm
  let ctx : PySpecContext := {
    eventSet := events
    skipNames := skipNames
    pythonCmd := pythonCmd
    dialectFile := dialectFile.toString
    baseSearchPath := searchPath
    currentModulePrefix := currentModulePrefix
    fileMapsRef := fileMapsRef
    strataDir := strataDir
    pythonFile := pythonFile
    currentModule := currentModule
  }
  let (res, s) ← translateModuleAux body |>.run ctx |>.run { warnings := #[], errors := #[] }
  let fmm ← fileMapsRef.get
  pure (fmm, res, s.errors, s.warnings)

/-- Translates a Python source file to PySpec signatures. Main entry point for translation. -/
public def translateFile
    (dialectFile strataDir pythonFile searchPath : System.FilePath)
    (pythonCmd : String := "python")
    (events : Std.HashSet EventType := {})
    (skipNames : Std.HashSet PythonIdent := {})
    (moduleName : Option ModuleName := none)
    : EIO String (Array Signature × Array String) := do
  let currentModule ← match moduleName with
    | some m => pure m
    | none =>
      let (mod, _) ← match ModuleName.ofFile pythonFile with
        | .ok r => pure r
        | .error e => throw e
      pure mod
  let mod := currentModule
  -- Compute the package prefix for relative import resolution.
  let modulePrefix :=
    if pythonFile.fileName == some "__init__.py" then mod.components
    else mod.components.toSubarray (stop := mod.components.size - 1) |>.toArray
  let contents ←
        match ← IO.FS.readFile pythonFile |>.toBaseIO with
        | .ok b => pure b
        | .error msg =>
          match msg with
          | .inappropriateType .. =>
            throw s!"{pythonFile} must be a file."
          | _ =>
            throw s!"{pythonFile} could not be read: {msg}"
  let options := PythonToStrataOptions.ofEventSet events
  let body ←
    match ← pythonToStrata (pythonCmd := pythonCmd) (options := options)
      dialectFile pythonFile |>.toBaseIO with
    | .ok r => pure r
    | .error msg => throw msg
  let (fmm, sigs, errors, warnings) ←
      translateModule
        (pythonCmd := pythonCmd)
        (events := events)
        (skipNames := skipNames)
        (dialectFile := dialectFile)
        (searchPath := searchPath)
        (currentModulePrefix := modulePrefix)
        (strataDir := strataDir)
        (pythonFile := pythonFile)
        (.ofString contents)
        body
        currentModule
  let ppErr (e : SpecError) : EIO String String :=
        match fmm[e.file]? with
        | none =>
          throw s!"No location information for {e.file}"
        | some fm =>
          pure s!"{e.loc.format e.file fm}: {e.message}"
  if errors.size > 0 then
    let msg := "Translation errors:\n"
    let msg ←
      errors.foldlM (init := msg) fun msg e =>
        return s!"{msg}{← ppErr e}\n"
    throw msg
  pure (sigs, ← warnings.mapM ppErr)

end Strata.Python.Specs
