/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.Data.Position
public import Std.Data.HashSet.Basic
import        Strata.DDM.Format
import all    Strata.DDM.Util.Fin
public import Strata.DDM.Util.SourceRange
import        Strata.Languages.Python.ReadPython
import        Strata.Languages.Python.Specs.DDM
public import Strata.Languages.Python.Specs.Decls
import        Strata.Util.DecideProp

namespace Strata.Python.Specs

/-- String identifier for event types. -/
public abbrev EventType := String

/-- Event type for module imports. -/
def importEvent : EventType := "import"

/--
Set of event types to log to stderr. Test code can modify this to
enable/disable logging.
-/
initialize stdoutEventsRef : IO.Ref (Std.HashSet EventType) ← IO.mkRef {}

/--
Log message for event type if enabled in `stdoutEventsRef`.
Output format: `[event]: message`
-/
def logEvent (event : EventType) (message : String) : BaseIO Unit := do
  let events ← stdoutEventsRef.get
  if event ∈ events then
    let _ ← IO.eprintln s!"[{event}]: {message}" |>.toBaseIO
  pure ()

/--
A specification predicate. Currently only supports constant boolean values;
placeholder for future extension with more complex predicates.
-/
inductive Pred where
| const (b : Bool)

namespace Pred

def not (p : Pred) : Pred :=
  match p with
  | .const b => .const (¬ b)

end Pred

/--
Represents an iterable type in Python specifications.
Currently only supports lists; other iterables (sets, generators, etc.) to be
added.
-/
inductive Iterable where
| list

public structure SpecError where
  file : System.FilePath
  loc : Strata.SourceRange
  message : String

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

instance : ToString ModuleName where
  toString m :=
    let p : m.components.size > 0 := m.componentsSizePos
    m.components.foldl (init := m.components[0]) (start := 1) fun s c => s!"{s}.{c}"

def foldlDirs {α} (mod : ModuleName) (init : α) (f : α → String → α) : α :=
  mod.components.foldl (init := init) (stop := mod.components.size - 1) f

def foldlMDirs {α m} [Monad m] (mod : ModuleName) (init : α) (f : α → String → m α) : m α := do
  mod.components.foldlM (init := init) (stop := mod.components.size - 1) f

def fileRoot (mod : ModuleName) : String :=
  let p := mod.componentsSizePos
  mod.components.back

def findInPath (mod : ModuleName) (searchPath : System.FilePath) : EIO String System.FilePath := do
  let findComponent path comp := do
        let newPath := path / comp
        if !(← newPath.isDir) then
          throw s!"Directory {newPath} not found"
        return newPath
  let searchPath ← mod.foldlMDirs (init := searchPath) findComponent
  let file := searchPath / s!"{mod.fileRoot}.py"
  match ← file.metadata |>.toBaseIO with
  | .error err =>
    throw s!"{file} not found: {err}"
  | .ok md =>
    if md.type != .file then
      throw s!"{file} is not a regular file."
    pure file

def strataDir (mod : ModuleName) (root : System.FilePath) : System.FilePath :=
  mod.foldlDirs (init := root) fun d c => d / c

/-- Generates the output filename for a module's spec file. -/
public def strataFileName (mod : ModuleName) : String := s!"{mod.fileRoot}.pyspec.st.ion"

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

def typeIdent (tp : PythonIdent) : SpecValue := .typeValue  (.ident tp)

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
    .mk .typingDict (.metaType .typingDict),
    .mk .typingGenerator (.metaType .typingGenerator),
    .mk .typingList (.metaType .typingList),
    .mk .typingLiteral (.metaType .typingLiteral),
    .mk .typingMapping (.metaType .typingMapping),
    .mk .typingOverload .typingOverload,
    .mk .typingSequence (.metaType .typingSequence),
    .mk .typingTypedDict .typingTypedDict,
    .mk .typingUnion (.metaType .typingUnion),
  ]

inductive ClassRef where
| unresolved (range : SourceRange)
| resolved

/-- Callback that takes a module name and provides filepath to module  -/
abbrev ModuleReader := ModuleName → EIO String System.FilePath

structure PySpecContext where
  /-- Command to run for Python -/
  pythonCmd : String
  /-- Path to Python dialect. -/
  dialectFile : System.FilePath
  /-- Path of current Python file being read. -/
  pythonFile : System.FilePath
  /-- Path to write Strata files to. -/
  strataDir : System.FilePath
  /-- Callback that takes a module name and provides filepath to module  -/
  moduleReader : ModuleReader

def preludeAtoms : List (String × SpecType) := [
  ("bool", .ident .builtinsBool),
  ("bytearray", .ident .builtinsBytearray),
  ("bytes", .ident .builtinsBytes),
  ("complex", .ident .builtinsComplex),
  ("dict", .ident .builtinsDict),
  ("float", .ident .builtinsFloat),
  ("int", .ident .builtinsInt),
  ("str", .ident .builtinsStr),
]

structure PySpecState where
  typeSigs : TypeSignature := preludeSig
  errors : Array SpecError := #[]
  /--
  This maps global identifiers to their value.
  -/
  nameMap : Std.HashMap String SpecValue :=
    preludeAtoms.foldl (init := {}) fun m (nm, tp) =>
      m.insert nm (.typeValue tp)
  typeReferences : Std.HashMap String ClassRef := {}
  /--
  Signatures being generated (declarations, functions, classes, etc).
  -/
  elements : Array Signature := #[]

class PySpecMClass (m : Type → Type) where
  specError (loc : SourceRange) (message : String) : m Unit
  runChecked {α} (act : m α) : m (Bool × α)

abbrev specError := @PySpecMClass.specError
abbrev runChecked := @PySpecMClass.runChecked

abbrev PySpecM := ReaderT PySpecContext (StateT PySpecState BaseIO)

def specErrorAt (file : System.FilePath) (loc : SourceRange) (message : String) : PySpecM Unit := do
  let e : SpecError := { file, loc, message }
  modify fun s => { s with errors := s.errors.push e }

instance : PySpecMClass PySpecM where
  specError loc message := do
    specErrorAt (←read).pythonFile loc message
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
  match inferInstanceAs (Decidable (as.size = n)) with
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
    return .ofAtom .noneType
  | .stringConst loc val =>
    -- Check if this is a known built-in type first
    match ← getNameValue? val with
    | some (.typeValue tp) =>
      return tp
    | _ =>
      recordTypeRef loc val
      return .ofAtom (.pyClass val #[])
  | _ =>
    specError loc s!"Expected type instead of {repr v}."
    return default

def fixedTranslator (t : PythonIdent) (arity : Nat) : TypeTranslator where
  callback := fun loc arg => do
    if arity = 1 then
      let tp ← valueAsType loc arg
      return .ident t #[tp]
    else
      let .tuple args := arg
        | specError loc s!"Expected multiple args instead of {repr arg}."; return default
      let some ⟨_⟩ ← checkEq loc (toString t) args arity
          | return default
      let args ← args.mapM (valueAsType loc)
      return .ident t args

def unionTranslator : TypeTranslator where
  callback := fun loc arg => do
    let .tuple args := arg
      | specError loc s!"Union expects tuple"; return default
    let .isTrue argsP := decideProp (args.size > 0)
      | specError loc s!"Union expects at least one argument."; return default
    let tp ← valueAsType loc args[0]
    args.foldlM (start := 1) (init := tp) fun tp v => do
      return tp ||| (← valueAsType loc v)

def literalTranslator : TypeTranslator where
  callback := fun loc arg => do
    let args :=
      match arg with
      | .tuple args => args
      |  arg => #[arg]
    let .isTrue _ := decideProp (args.size > 0)
      | specError loc s!"Union expects at least one argument."; return default
    let trans (v : SpecValue) : PySpecM SpecAtomType := do
          match v with
          | .intConst _ n =>
            pure <| .intLiteral n
          | .stringConst _ s =>
            pure <| .stringLiteral s
          | _ =>
            specError loc s!"Unsupported literal value {repr v}."
            pure default
    return .ofArray (← args.mapM trans)

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
    let .isTrue kwargsSizep := decideProp (kwargs.size = 1)
      | specError loc "TypedDict expects one keyword"; return default
    let (some "total", totalValue) := kwargs[0]
      | specError loc "TypedDict expects total"; return default
    let .boolConst total := totalValue
      | specError loc "TypedDict expects total bool"; return default
    let .stringConst _ name := args[0]
      | specError loc "TypedDict expects string contant"; return default
    let .dictValue fieldsPairs := args[1]
      | specError loc "TypedDict expects dictionary fields"; return default
    let fields := fieldsPairs |>.map (·.fst)
    let values ← fieldsPairs |>.mapM fun (_name, v) => do
      valueAsType loc v
    return .typeValue <| .ofAtom <| .typedDict fields values total
  | _ =>
    specError loc s!"Unknown call {repr func}."
    return default

def translateConstant (value : constant SourceRange) : PySpecM SpecValue := do
  match value with
  | .ConFalse .. =>
    return .boolConst false
  | .ConTrue .. =>
    return .boolConst true
  | .ConNone _ =>
    return .noneConst
  | .ConPos _ n =>
    return .intConst n.ann (Int.ofNat n.val)
  | .ConNeg _ n =>
    return .intConst n.ann (Int.negOfNat n.val)
  | .ConString _ name =>
    return .stringConst name.ann name.val
  | _ =>
    specError value.ann s!"Could not interpret constant {value}"
    return default

def translateSubscript (paramLoc : SourceRange) (paramType : String) (sargs  : SpecValue) : PySpecM SpecValue := do
  match ← getNameValue? paramType with
  | none =>
    specError paramLoc s!"Unknown parameterized type {paramType}."
    return default
  | some (.typeValue tpp) =>
    let .isTrue tpp_sizep := inferInstanceAs (Decidable (tpp.atoms.size = 1))
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
  | some _ =>
    specError paramLoc s!"Expected {paramType} to be a type."
    return default

def translateDictKey (loc : SourceRange) (mk : opt_expr SourceRange) : PySpecM String := do
  let .some_expr _ k := mk
    | specError loc s!"Dict key missing"; return default
  match k with
  | .Constant _ (.ConString _ key) _ =>
    pure key.val
  | _ =>
    specError loc s!"Dict key value mismatch"
    return default

mutual

def pyKeywordValue (k : keyword SourceRange) : PySpecM (Option String × SpecValue) := do
  let arg : Option String :=
        match k.arg.val with
        | none => none
        | some e => e.val
  pure (arg, ← pySpecValue k.value)
termination_by 2 * sizeOf k
decreasing_by
  cases k
  simp [keyword.value]
  decreasing_tactic

def pySpecValue (expr : expr SourceRange) : PySpecM SpecValue := do
  match h : expr with
  | .BinOp loc x op y => do
    match op with
    | .BitOr _ =>
      return .typeValue <| (← pySpecType x) ||| (← pySpecType y)
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
  | .Constant _ value kind =>
    assert! kind.val.isNone
    translateConstant value
  | .Dict loc ⟨_, keys⟩ ⟨_, values⟩ =>
    let .isTrue size_eq := inferInstanceAs (Decidable (keys.size = values.size))
      | specError loc s!"Dict key value mismatch"; return default
    let  m : Array (String × SpecValue) ← Array.ofFnM fun (⟨i, _⟩ : Fin keys.size) => do
      let key ← translateDictKey loc keys[i]
      let v ← pySpecValue values[i]
      pure ⟨key, v⟩
    return .dictValue m
  | .Name _ ident (.Load _) =>
    let some v := ←getNameValue? ident.val
      | specError expr.ann s!"Unknown identifier {ident.val}."; return default
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
  let .mk_arg loc name ⟨_typeLoc, type⟩ comment := arg
  if name.val ∈ usedNames then
    specError name.ann s!"Argument {name.val} already declared."
  assert! !loc.isNone
  assert! _typeLoc.isNone
  let tp ←
    match selfType with
    | none =>
      match type with
      | none =>
        specError loc s!"Missing argument to {name.val}"
        pure default
      | some tp => pySpecType tp
    | some cl =>
      if type.isSome then
        specError loc s!"Unexpected argument to {name.val}"
      pure <| .pyClass cl #[]
  assert! comment.val.isNone
  let hasDefault ←
    match de with
    | none =>
      pure false
    | some d =>
      pyDefaultValue d tp
      pure true
  return {
    name := name.val
    type := tp
    hasDefault := hasDefault
  }

structure SpecAssertionContext where
  filePath : System.FilePath

/--
State for `SpecAssertionM`

`argc` denotes the number of named arguments.
-/
structure SpecAssertionState (argc : Nat) where
  assertions : Array (Assertion argc) := #[]
  postconditions : Array (SpecPred (argc + 1)) := #[]
  errors : Array SpecError := #[]

/--
Monad for extracting pre and post conditions from methods.
-/
abbrev SpecAssertionM (argc : Nat) := ReaderT SpecAssertionContext (StateM (SpecAssertionState argc))

instance {argc} : PySpecMClass (SpecAssertionM argc) where
  specError loc message := do
    let file := (←read) |>.filePath
    let e : SpecError := { file, loc, message }
    modify fun s => { s with errors := s.errors.push e }
  runChecked act := do
    let cnt := (←get).errors.size
    let r ← act
    let new_cnt := (←get).errors.size
    return (cnt = new_cnt, r)

def transPred {argc} (_e : expr SourceRange) : SpecAssertionM argc Pred := do
  -- FIXME
  pure (.const true)

def transIter {argc} (_e : expr SourceRange) : SpecAssertionM argc Iterable := do
  -- FIXME
  return .list

def assumePred {argc} (_p : Pred) (act : SpecAssertionM argc Unit) : SpecAssertionM argc Unit := do
  act

mutual

def blockStmt {argc : Nat} (s : stmt SourceRange) : SpecAssertionM argc Unit := do
  match s with
  | .Assign _ _targets _value _typeAnn =>
    pure () -- FIXME
  | .AnnAssign .. =>
    pure () -- FIXME
  | .Expr .. =>
    pure () -- FIXME
  | .Assert .. => -- FIXME
    pure ()
  | .Return .. =>-- FIXME
    pure ()
  | .Raise .. =>-- FIXME
    pure ()
  | .ClassDef .. => -- FIXME
    specError s.ann s!"Inner classes are not supported."
  | .For _ _target _iter _body orelse type_comment =>
    assert! type_comment.val.isNone
    assert! orelse.val.size == 0
    pure ()
  | .If _ pred t f =>
    let p ← transPred pred
    assumePred p <| blockStmts t.val
    assumePred (.not p) <| blockStmts f.val
  | .Pass _ =>
    pure ()
  | _ => specError s.ann s!"Unsupported statement: {eformat s.toAst}"
termination_by sizeOf s
decreasing_by
  · cases t;
    decreasing_tactic
  · cases f;
    decreasing_tactic

def blockStmts {argc : Nat} (as : Array (stmt SourceRange)) : SpecAssertionM argc Unit := do
  as.attach.forM fun ⟨b, _⟩ => blockStmt b
termination_by sizeOf as
decreasing_by
· decreasing_tactic

end

def collectAssertions (decls : ArgDecls) (_returnType : SpecType) (action : SpecAssertionM decls.count Unit) : PySpecM (SpecAssertionState decls.count) := do
  let errors := (←get).errors
  modify fun s => { s with errors := #[] }
  let filePath := (←read).pythonFile
  let ((), as) := action { filePath } { errors }
  modify fun s => { s with errors := as.errors }
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

  let .mk_arguments _ posonly ⟨_, posArgs⟩ vararg kwonly kw_defaults kwarg defaults := arguments
  assert! posonly.val.size = 0
  let argc := posArgs.size

  let .up defaults_bnd ←
    if h : defaults.val.size ≤ posArgs.size then
      pure <| PULift.up.{1, 0} h
    else
      specError fnLoc s!"internal: bad index"; return default

  let .isTrue kw_bnd := inferInstanceAs (Decidable (kwonly.val.size = kw_defaults.val.size))
    | specError fnLoc s!"Keyword only arguments must have defaults."; return default
  assert! vararg.val.isNone
  assert! kwarg.val.isNone
  let min_default := argc - defaults.val.size
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
        some defaults.val[i - min_default]
      else
        none
    let self_type :=
            match className with
            | some cl => if i = 0 then some cl else none
            | none => none
    let ba ← pySpecArg usedNames self_type a d
    usedNames := usedNames.insert ba.name
    specArgs := specArgs.push ba
  let mut kwSpecArgs : Array Arg := .emptyWithCapacity kwonly.val.size
  for ⟨i, ib⟩ in Fin.range kwonly.val.size do
    let a := kwonly.val[i]
    -- Arguments with defaults occur at end
    let d : Option _ :=
        match kw_defaults.val[i] with
        | .some_expr _ v => some v
        | .missing_expr _ => none
    let ba ← pySpecArg usedNames none a d
    usedNames := usedNames.insert ba.name
    kwSpecArgs := kwSpecArgs.push ba
  let argDecls : ArgDecls := { args := specArgs, kwonly := kwSpecArgs }
  let returnType : SpecType ←
        match returns with
        | none => pure <| .ident .typingAny
        | some tp => pySpecType tp
  let as ← collectAssertions argDecls returnType <| body.forM blockStmt

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

def pySpecClassBody (loc : SourceRange) (className : String) (body : Array (Strata.Python.stmt Strata.SourceRange)) : PySpecM ClassDef := do
  let mut usedNames : Std.HashSet String := {}
  let mut methods : Array FunctionDecl := #[]
  for stmt in body do
    match stmt with
    | .Expr .. => pure () -- Skip expressions
    | .FunctionDef loc ⟨_, name⟩  args ⟨_, body⟩ ⟨_, decorators⟩ ⟨_, returns⟩
                   ⟨_, type_comment⟩ ⟨_, type_params⟩ =>
      assert! type_comment.isNone
      assert! type_params.size = 0
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
    methods := methods
  }

def checkLevel (loc : SourceRange) (level : Option (int SourceRange)) : PySpecM Unit := do
  match level with
  | some lvl =>
    if lvl.value ≠ 0 then
      specError loc s!"Local import {lvl.value} not supported."
  | none =>
    specError loc s!"Missing import level."

def translateImportFrom (mod : String) (types : Std.HashMap String SpecValue) (names : Array (alias SourceRange)) : PySpecM Unit := do
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
def signatureValueMap (mod : String) (sigs : Array Signature) :
  Std.HashMap String SpecValue :=
  let addType (m : Std.HashMap String SpecValue) (sig : Signature) :=
        match sig with
        | .classDef d =>
          let pyIdent : PythonIdent := {
            pythonModule := mod
            name := d.name
          }
          m.insert d.name (.typeValue (.ident pyIdent))
        | .functionDecl .. | .typeDef .. | .externTypeDecl .. => m
  sigs.foldl (init := {}) addType

def checkOverloadBody (stmt : stmt SourceRange) : PySpecM Unit := do
  match stmt with
  | .Expr _ (.Constant _ (.ConEllipsis _) _) => pure ()
  | _ => specError stmt.ann s!"Expected ellipsis"

mutual

/--
Resolves a Python module by name, returning a map of exported identifiers to
their spec values. Loads either from cached PySpec files or by parsing the
Python source if not in cache.
-/
partial def resolveModule (loc : SourceRange) (modName : String) :
    PySpecM (Std.HashMap String SpecValue) := do
  let mod ←
        match ModuleName.ofString modName with
        | .ok r => pure r
        | .error msg =>
          specError loc msg
          return default
  let moduleReader := (←read).moduleReader
  let pythonFile ←
        match ← moduleReader mod |>.toBaseIO with
        | .ok r =>
          pure r
        | .error msg =>
          specError loc msg
          return default
  let strataDir := mod.strataDir (←read).strataDir
  let strataFile := strataDir / mod.strataFileName

  let .ok pythonMetadata ← pythonFile.metadata |>.toBaseIO
    | specError loc s!"Could not get file mod time."; return default

  -- Check if strataFile is newer than pythonSource
  let useStrata : Bool :=
        match ← strataFile.metadata |>.toBaseIO with
        | .ok strataMetadata => strataMetadata.modified > pythonMetadata.modified
        | .error _ => false
    -- If Strata is newer use it.
  if useStrata then
    logEvent importEvent s!"Importing {modName} from PySpec file"
    match ← readDDM strataFile |>.toBaseIO with
    | .ok sigs =>
      return signatureValueMap modName sigs
    | .error msg =>
      specError loc s!"Could not load Strata file: {msg}"
      return default

  logEvent importEvent s!"Importing {modName} from Python"
  let pythonCmd := (←read).pythonCmd
  let dialectFile := (←read).dialectFile
  let commands ←
    match ← pythonToStrata (pythonCmd := pythonCmd) dialectFile pythonFile |>.toBaseIO with
    | .ok r => pure r
    | .error msg =>
      specError loc msg
      return default
  let errors := (←get).errors
  let errorCount := errors.size
  modify fun s => { s with errors := #[] }
  let ctx := { (←read) with pythonFile := pythonFile }
  let (sigs, t) ← translateModuleAux commands |>.run ctx |>.run { errors := errors }
  modify fun s => { s with errors := t.errors }
  if t.errors.size > errorCount then
    return default

  if let .error msg ← IO.FS.createDirAll strataDir |>.toBaseIO then
    specError loc s!"Could not create directory {strataDir}:  {msg}"
    return default

  if let .error msg ← writeDDM strataFile sigs |>.toBaseIO then
    specError loc s!"Could not write file {strataFile}:  {msg}"
    return default

  return signatureValueMap (toString mod) sigs

partial def resolveModuleCached (loc : SourceRange) (modName : String)
    : PySpecM (Option (Std.HashMap String SpecValue)) := do
  match (←get).typeSigs.rank[modName]? with
  | some types =>
    return types
  | none =>
    let (success, r) ← runChecked <| resolveModule loc modName
    let r := if success then some r else none
    modify fun s => { s with typeSigs := s.typeSigs.insert modName r }
    return r

partial def translate (body : Array (Strata.Python.stmt Strata.SourceRange)) : PySpecM Unit := do
  for stmt in body do
    match stmt with
    | .Assign loc ⟨_, targets⟩ value _typeAnn =>
      let (success, v) ← runChecked <| pySpecValue value
      if not success then
        continue
      let .isTrue eq := inferInstanceAs (Decidable (targets.size = 1))
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
        pure ()
    | .Expr .. =>
      -- Skip expressions
      pure ()
    | .FunctionDef loc
                   ⟨_funNameLoc, funName⟩
                   args
                   ⟨_bodyLoc, body⟩
                   ⟨_decoratorsLoc, decorators⟩
                   ⟨_returnsLoc, returns⟩
                   ⟨_typeCommentLoc, typeComment⟩
                   ⟨_typeParamsLoc, typeParams⟩ =>
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
    | .Import loc names =>
      specError loc s!"Import of {repr names} not supported."
    | .ImportFrom loc ⟨_, pyModule⟩ ⟨_, names⟩ ⟨_, level⟩ =>
      let (success, ()) ← runChecked <| checkLevel loc level
      if not success then
        continue
      let some ⟨_, mod⟩ := pyModule
        | specError loc s!"Local imports not supported"; continue
      if let some types ← resolveModuleCached loc mod then
        translateImportFrom mod types names
    | .ClassDef loc ⟨_classNameLoc, className⟩ bases keywords stmts decorators typeParams =>
      assert! _classNameLoc.isNone
      assert! bases.val.size = 0
      assert! keywords.val.size = 0
      assert! decorators.val.size = 0
      assert! typeParams.val.size = 0
      let (success, _) ← runChecked <| recordTypeDef loc className
      -- Add the class to nameMap so it can be used in forward references
      setNameValue className (.typeValue (.pyClass className #[]))
      let d ← pySpecClassBody loc className stmts.val
      if success then
        pushSignature (.classDef d)
    | _ => specError stmt.ann s!"Unknown statement {stmt}"

partial def translateModuleAux (body : Array (Strata.Python.stmt Strata.SourceRange))
  : PySpecM (Array Signature) := do
  translate body
  let s ← get
  for ⟨cl, t⟩ in s.typeReferences do
    if let .unresolved loc := t then
      specError loc s!"Class {cl} not defined."
  return s.elements

end

/-- Maps file paths to their FileMap for error location reporting. -/
public abbrev FileMaps := Std.HashMap System.FilePath Lean.FileMap

def FileMaps.ppSourceRange (fmm : Strata.Python.Specs.FileMaps) (path : System.FilePath) (loc : SourceRange) : String :=
  match fmm[path]? with
  | none =>
    panic! "Invalid path {file}"
  | some fm =>
    let spos := fm.toPosition loc.start
    let epos := fm.toPosition loc.stop
    -- Render error location information in a format VSCode understands.
    if spos.line == spos.line then
      s!"{path}:{spos.line}:{spos.column+1}-{epos.column+1}"
    else
      s!"{path}:{spos.line}:{spos.column+1}"

/-- Translates Python AST statements to PySpec signatures with dependency resolution. -/
def translateModule
    (dialectFile searchPath strataDir pythonFile : System.FilePath)
    (fileMap : Lean.FileMap)
    (body : Array (Strata.Python.stmt Strata.SourceRange))
    (pythonCmd : String := "python") :
    BaseIO (FileMaps × Array Signature × Array SpecError) := do
  let fmm : FileMaps := {}
  let fmm := fmm.insert pythonFile fileMap
  let fileMapsRef : IO.Ref FileMaps ← IO.mkRef fmm
  let ctx : PySpecContext := {
    pythonCmd := pythonCmd
    dialectFile := dialectFile.toString
    moduleReader := fun (mod : ModuleName) => do
      let pythonPath ← mod.findInPath searchPath
      logEvent "findFile" s!"Found {mod} as {pythonPath} in {searchPath}"
      match ← IO.FS.readFile pythonPath |>.toBaseIO with
      | .ok contents =>
        let fm := Lean.FileMap.ofString contents
        fileMapsRef.modify fun m => m.insert pythonPath fm
        pure pythonPath
      | .error msg =>
        throw s!"Could not read file {pythonPath}: {msg}"
    strataDir := strataDir
    pythonFile := pythonFile
  }
  let (res, s) ← translateModuleAux body |>.run ctx |>.run {}
  pure (←fileMapsRef.get, res, s.errors)

/-- Translates a Python source file to PySpec signatures. Main entry point for translation. -/
public def translateFile
    (dialectFile strataDir pythonFile : System.FilePath)
    (pythonCmd : String := "python")
    (searchPath : Option System.FilePath := none) :
    EIO String (Array Signature) := do
  let searchPath ←
      match searchPath with
      | some p => pure p
      | none =>
        match pythonFile.parent with
        | some p => pure p
        | none => throw s!"{pythonFile} directory unknown"
  let contents ←
        match ← IO.FS.readFile pythonFile |>.toBaseIO with
        | .ok b => pure b
        | .error msg =>
          match msg with
          | .inappropriateType .. =>
            throw s!"{pythonFile} must be a file."
          | _ =>
            throw s!"{pythonFile} could not be read: {msg}"
  let body ←
    match ← pythonToStrata (pythonCmd := pythonCmd) dialectFile pythonFile |>.toBaseIO with
    | .ok r => pure r
    | .error msg => throw msg
  let (fmm, sigs, errors) ←
      Strata.Python.Specs.translateModule
        (pythonCmd := pythonCmd)
        (dialectFile := dialectFile)
        (searchPath := searchPath)
        (strataDir := strataDir)
        (pythonFile := pythonFile)
        (.ofString contents)
        body
  if errors.size > 0 then
    let msg := "Translation errors:\n"
    let msg := errors.foldl (init := msg) fun msg e =>
      s!"{msg}{fmm.ppSourceRange pythonFile e.loc}: {e.message}\n"
    throw msg
  pure sigs

end Strata.Python.Specs
