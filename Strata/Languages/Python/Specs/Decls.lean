/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashMap.Basic
public import Strata.DDM.Util.SourceRange
public import Strata.Languages.Python.OverloadTable

public section
namespace Strata.Python

namespace PythonIdent

def builtinsBool := mk "builtins" "bool"
def builtinsBytearray := mk "builtins" "bytearray"
def builtinsBytes := mk "builtins" "bytes"
def builtinsComplex := mk "builtins" "complex"
def builtinsDict := mk "builtins" "dict"
def builtinsException := mk "builtins" "Exception"
def builtinsFloat := mk "builtins" "float"
def builtinsInt := mk "builtins" "int"
def builtinsStr := mk "builtins" "str"
def noneType := mk "_types" "NoneType"

def typingAny := mk "typing" "Any"
def typingBinaryIO := mk "typing" "BinaryIO"
def typingDict := mk "typing" "Dict"
def typingGenerator := mk "typing" "Generator"
def typingList := mk "typing" "List"
def typingLiteral := mk "typing" "Literal"
def typingMapping := mk "typing" "Mapping"
def typingOverload := mk "typing" "overload"
def typingSequence := mk "typing" "Sequence"
def typingTypedDict := mk "typing" "TypedDict"
def typingUnion := mk "typing" "Union"
def typingRequired := mk "typing" "Required"
def typingNotRequired := mk "typing" "NotRequired"
def typingUnpack := mk "typing" "Unpack"
def reCompile := mk "re" "compile"

end PythonIdent

namespace Specs

/--
Represents Python generic types from the `typing` module that require special
handling during type translation (e.g., parameterized types with specific
arity requirements).
-/
inductive MetadataType where
| typingDict
| typingGenerator
| typingList
| typingLiteral
| typingMapping
| typingSequence
| typingUnion
deriving Repr

def MetadataType.ident : MetadataType -> PythonIdent
| .typingDict => .typingDict
| .typingGenerator => .typingGenerator
| .typingList => .typingList
| .typingLiteral => .typingLiteral
| .typingMapping => .typingMapping
| .typingSequence => .typingSequence
| .typingUnion => .typingUnion

instance : ToString MetadataType where
  toString tp := toString tp.ident

mutual

/--
An atomic type in the PySpec language
-/
inductive SpecAtomType where
| ident (nm : PythonIdent) (args : Array SpecType)
/- An integer literal -/
| intLiteral (value : Int)
/-- A string literal -/
| stringLiteral (value : String)
/-
A typed dictionary with an array of fields and their types.  The arrays
must be of the same length.
The `fieldRequired` array is parallel to `fields`/`fieldTypes`.
`true` = Required, `false` = NotRequired.
-/
| typedDict (fields : Array String)
            (fieldTypes : Array SpecType)
            (fieldRequired : Array Bool)
deriving Inhabited, Repr

structure SpecIdent where
  name : PythonIdent
  args : Array SpecType
deriving Inhabited, Repr

structure SpecTypedDict where
  fields        : Array String
  fieldTypes    : Array SpecType
  fieldRequired : Array Bool
deriving Inhabited, Repr

/--
A PySpec type is a union of atom types, stored with separate collections
for each variant for efficient union operations on literal-heavy types.
-/
structure SpecType where
  private mk ::
  /-- Named type identifiers, sorted by PythonIdent ordering. -/
  idents     : Array SpecIdent
  /-- Integer literal values. -/
  intLits    : Std.HashSet Int
  /-- String literal values. -/
  stringLits : Std.HashSet String
  /-- TypedDict types, sorted by field names. -/
  typedDicts : Array SpecTypedDict
  /-- Source location of this type. May be `.none` for builtin types. -/
  loc : SourceRange
deriving Inhabited

end

namespace SpecAtomType

def noneType : SpecAtomType := .ident .noneType #[]

end SpecAtomType

/-- Heterogeneous lexicographic comparison of two arrays. Shorter arrays
    compare as less than longer arrays when all shared elements are equal. -/
@[specialize]
def compareHLex {α β} (cmp : α → β → Ordering) (a₁ : Array α) (a₂ : Array β) : Ordering :=
  go 0
where go i :=
  if h₁ : a₁.size <= i then
    if a₂.size <= i then .eq else .lt
  else
    if h₂ : a₂.size <= i then
      .gt
    else cmp a₁[i] a₂[i] |>.then $ go (i + 1)
termination_by a₁.size - i

mutual

/-- Compare two atom types by structure, ignoring `loc` in nested `SpecType`
    values. Variants are ordered: ident < intLiteral < stringLiteral
    < typedDict. -/
protected def SpecAtomType.compare (x y : SpecAtomType) : Ordering :=
  match x, y with
  | .ident xnm xargs, .ident ynm yargs =>
    compare xnm ynm |>.then $
      compareHLex (fun ⟨xe, _⟩ ye => xe.compare ye) xargs.attach yargs
  | .ident .., _ => .lt
  | _, .ident .. => .gt

  | .intLiteral xval, .intLiteral yval => compare xval yval
  | .intLiteral .., _ => .lt
  | _, .intLiteral .. => .gt

  | .stringLiteral xval, .stringLiteral yval => compare xval yval
  | .stringLiteral .., _ => .lt
  | _, .stringLiteral .. => .gt

  | .typedDict xfields xfieldTypes xisTotal, .typedDict yfields yfieldTypes yisTotal =>
    compare xfields yfields |>.then $
    compareHLex (fun ⟨xe, _⟩ ye => xe.compare ye) xfieldTypes.attach yfieldTypes |>.then $
    compare xisTotal yisTotal

protected def SpecIdent.compare (x y : SpecIdent) : Ordering :=
  compare x.name y.name |>.then $
    compareHLex (fun ⟨xe, _⟩ ye => xe.compare ye) x.args.attach y.args
termination_by sizeOf x
decreasing_by cases x; decreasing_tactic

protected def SpecTypedDict.compare (x y : SpecTypedDict) : Ordering :=
  compare x.fields y.fields |>.then $
    compareHLex (fun ⟨xe, _⟩ ye => xe.compare ye) x.fieldTypes.attach y.fieldTypes |>.then $
    compare x.fieldRequired y.fieldRequired
termination_by sizeOf x
decreasing_by cases x; decreasing_tactic

/-- Compare two types, ignoring `loc`. -/
protected def SpecType.compare (x y : SpecType) : Ordering :=
  compareHLex (fun ⟨xe, _⟩ ye => xe.compare ye) x.idents.attach y.idents |>.then $
  (compare (x.intLits.toArray.qsort (· < ·)) (y.intLits.toArray.qsort (· < ·))) |>.then $
  (compare (x.stringLits.toArray.qsort (· < ·)) (y.stringLits.toArray.qsort (· < ·))) |>.then $
  compareHLex (fun ⟨xe, _⟩ ye => xe.compare ye) x.typedDicts.attach y.typedDicts
termination_by sizeOf x
decreasing_by all_goals (cases x; decreasing_tactic)

end

namespace SpecType


theorem sizeOf_idents_lt_of_mem {a : SpecIdent} {tp : SpecType}
    (h : a ∈ tp.idents) : sizeOf a < sizeOf tp := by
  cases tp
  decreasing_tactic

theorem sizeOf_typedDicts_lt_of_mem {a : SpecTypedDict} {tp : SpecType}
    (h : a ∈ tp.typedDicts) : sizeOf a < sizeOf tp := by
  cases tp
  decreasing_tactic

/-- Total number of atoms across all fields. -/
def size (tp : SpecType) : Nat :=
  tp.idents.size + tp.intLits.size + tp.stringLits.size + tp.typedDicts.size

/-- Reconstruct the flat array of atoms. Output order: idents (sorted),
    int literals (sorted), string literals (sorted), typedDicts (sorted). -/
def atoms (tp : SpecType) : Array SpecAtomType :=
  let r := tp.idents.map fun si => .ident si.name si.args
  let ints := tp.intLits.toArray.qsort (· < ·)
  let r := ints.foldl (init := r) fun acc k => acc.push (.intLiteral k)
  let strs := tp.stringLits.toArray.qsort (· < ·)
  let r := strs.foldl (init := r) fun acc k => acc.push (.stringLiteral k)
  tp.typedDicts.foldl (init := r) fun acc td =>
    acc.push (.typedDict td.fields td.fieldTypes td.fieldRequired)

end SpecType

mutual

def SpecIdent.toString (si : SpecIdent) : String :=
  if si.args.size == 0 then s!"{si.name}"
  else s!"{si.name}[{", ".intercalate (si.args.map (fun a => a.toString) |>.toList)}]"
termination_by sizeOf si
decreasing_by cases si; decreasing_tactic

def SpecTypedDict.toString (td : SpecTypedDict) : String :=
  let fieldNames := td.fields
  let fieldTypes := td.fieldTypes
    if p : fieldNames.size = fieldTypes.size then
      let ppField (i : Fin fieldNames.size) := s!"{fieldNames[i]} : {SpecType.toString fieldTypes[i]}"
      let results := Array.ofFn ppField
      s!"TypedDict({", ".intercalate results.toList})"
    else
      s!"Malformed typed dict"
termination_by sizeOf td
decreasing_by
  cases td
  decreasing_tactic

def SpecType.toString (tp : SpecType) : String :=
  let parts : Array String :=
    let r := tp.idents.map fun si => si.toString
    let ints := tp.intLits.toArray.qsort (· < ·)
    let r := ints.foldl (init := r) fun acc k => acc.push s!"Literal[{k}]"
    let strs := tp.stringLits.toArray.qsort (· < ·)
    let r := strs.foldl (init := r) fun acc k => acc.push s!"Literal[\"{k}\"]"
    tp.typedDicts.foldl (init := r) fun acc td => acc.push td.toString
  if parts.size == 1 then
    parts[0]!
  else
    s!"Union[{", ".intercalate parts.toList}]"
termination_by sizeOf tp
decreasing_by all_goals (cases tp; decreasing_tactic)

end

instance : ToString SpecType where toString := SpecType.toString

protected def SpecAtomType.toString : SpecAtomType → String
  | .ident nm args =>
    if args.size == 0 then s!"{nm}"
    else s!"{nm}[{", ".intercalate (args.map (fun a => a.toString) |>.toList)}]"
  | .intLiteral v => s!"Literal[{v}]"
  | .stringLiteral v => s!"Literal[\"{v}\"]"
  | .typedDict fieldNames fieldTypes _ =>
    if p : fieldNames.size = fieldTypes.size then
      let ppField (i : Fin fieldNames.size) := s!"{fieldNames[i]} : {SpecType.toString fieldTypes[i]}"
      let results := Array.ofFn ppField
      s!"TypedDict({", ".intercalate results.toList})"
    else
      s!"Malformed typed dict"

instance : ToString SpecAtomType where toString := SpecAtomType.toString

instance : BEq SpecAtomType where
  beq x y := SpecAtomType.compare x y == .eq

instance : BEq SpecIdent where
  beq x y := SpecIdent.compare x y == .eq

instance : BEq SpecTypedDict where
  beq x y := SpecTypedDict.compare x y == .eq

instance : BEq SpecType where
  beq x y := SpecType.compare x y == .eq

instance : Ord SpecAtomType where
  compare := SpecAtomType.compare

instance : Ord SpecIdent where
  compare := SpecIdent.compare

instance : Ord SpecTypedDict where
  compare := SpecTypedDict.compare

instance : Ord SpecType where
  compare := SpecType.compare

instance : LT SpecAtomType where
  lt x y := private compare x y = .lt

namespace SpecType

instance : Repr SpecType where
  reprPrec tp prec := private reprPrec tp.atoms.toList prec

private def empty (loc : SourceRange) : SpecType :=
  { idents := #[], intLits := {}, stringLits := {}, typedDicts := #[], loc }

/-- Sorted merge of two sorted arrays without duplicates. -/
private partial def sortedMerge {α} [Ord α] (x y : Array α) : Array α :=
  go x y 0 0 #[]
where go (x y : Array α) (i j : Nat) (r : Array α) :=
  if hi : i < x.size then
    if hj : j < y.size then
      match compare x[i] y[j] with
      | .lt => go x y (i+1) j (r.push x[i])
      | .eq => go x y (i+1) (j+1) (r.push x[i])
      | .gt => go x y i (j+1) (r.push y[j])
    else
      r ++ x.drop i
  else
    r ++ y.drop j

/-- Union two SpecTypes with a specified location for the result. -/
def union (loc : SourceRange) (x y : SpecType) : SpecType :=
  { idents     := sortedMerge x.idents y.idents
    intLits    := x.intLits.union y.intLits
    stringLits := x.stringLits.union y.stringLits
    typedDicts := sortedMerge x.typedDicts y.typedDicts
    loc }

def ident (loc : SourceRange) (i : PythonIdent) (args : Array SpecType := #[]) : SpecType :=
  { empty loc with idents := #[{ name := i, args }] }

def noneType (loc : SourceRange) : SpecType :=
  ident loc .noneType

def intLiteral (loc : SourceRange) (value : Int) : SpecType :=
  { empty loc with intLits := ({} : Std.HashSet Int).insert value }

def stringLiteral (loc : SourceRange) (value : String) : SpecType :=
  { empty loc with stringLits := ({} : Std.HashSet String).insert value }

def typedDict (loc : SourceRange) (fields : Array String)
    (fieldTypes : Array SpecType) (fieldRequired : Array Bool) : SpecType :=
  { empty loc with typedDicts := #[{ fields, fieldTypes, fieldRequired }] }

def unionArray (loc : SourceRange) (elts : Array SpecType) : SpecType :=
  elts.foldl (init := empty loc) (union loc · ·)

private def asSingleton (tp : SpecType) : Option SpecAtomType := do
  guard (tp.size == 1)
  if h : tp.idents.size = 1 then
    let si := tp.idents[0]
    return .ident si.name si.args
  else if tp.intLits.size == 1 then
    let v := tp.intLits.toArray[0]!
    return .intLiteral v
  else if tp.stringLits.size == 1 then
    let v := tp.stringLits.toArray[0]!
    return .stringLiteral v
  else if h : tp.typedDicts.size = 1 then
    let td := tp.typedDicts[0]
    return .typedDict td.fields td.fieldTypes td.fieldRequired
  else
    none

def asIdent (tp : SpecType) : Option PythonIdent := do
  guard (tp.intLits.size == 0 && tp.stringLits.size == 0
       && tp.typedDicts.size == 0)
  if h : tp.idents.size = 1 then
    let si := tp.idents[0]
    guard (si.args.size == 0)
    return si.name
  else
    none

def isIntType (tp : SpecType) : Bool := tp.asIdent == some .builtinsInt

def isFloatType (tp : SpecType) : Bool := tp.asIdent == some .builtinsFloat

def isStringType (tp : SpecType) : Bool := tp.asIdent == some .builtinsStr

def isBoolType (tp : SpecType) : Bool := tp.asIdent == some .builtinsBool

def isTypedDict (tp : SpecType) : Bool :=
  tp.idents.size == 0 && tp.intLits.size == 0 && tp.stringLits.size == 0
    && tp.typedDicts.size == 1

def lookupTypedDictField (tp : SpecType) (field : String) : Option SpecType := do
  guard tp.isTypedDict
  let td := tp.typedDicts[0]!
  for i in [:td.fields.size] do
    if td.fields[i]! == field then return td.fieldTypes[i]!
  none

def extractElementType (tp : SpecType) : Option SpecType := do
  guard (tp.intLits.size == 0 && tp.stringLits.size == 0
       && tp.typedDicts.size == 0)
  if h : tp.idents.size = 1 then
    let si := tp.idents[0]
    if (si.name == .typingList || si.name == .typingSequence) && si.args.size == 1 then
      return si.args[0]!
    none
  else none

def extractDictKeyValueTypes (tp : SpecType) : Option (SpecType × SpecType) := do
  guard (tp.intLits.size == 0 && tp.stringLits.size == 0
       && tp.typedDicts.size == 0)
  if h : tp.idents.size = 1 then
    let si := tp.idents[0]
    if (si.name == .typingDict || si.name == .typingMapping) && si.args.size == 2 then
      return (si.args[0]!, si.args[1]!)
    none
  else none

def asStringLiteral (tp : SpecType) : Option String := do
  guard (tp.idents.size == 0 && tp.intLits.size == 0
       && tp.typedDicts.size == 0 && tp.stringLits.size == 1)
  return tp.stringLits.toArray[0]!

structure DictField where
  name : String
  type : SpecType
  required : Bool
deriving Inhabited

def asTypedDict (tp : SpecType) : Option (Array DictField) := do
  guard tp.isTypedDict
  let td := tp.typedDicts[0]!
  some <| td.fields.mapIdx fun i name =>
    { name, type := td.fieldTypes.getD i default, required := td.fieldRequired.getD i true }

end SpecType

/-- A default value for a pyspec argument.
    TODO: extend with additional constructors (e.g., string, int, bool literals)
    as PySpec gains support for richer default values. -/
inductive SpecDefault where
  /-- Python `None`. -/
  | none
deriving Inhabited, Repr

structure Arg where
  name : String
  type : SpecType
  default : Option SpecDefault := none
deriving Inhabited

structure ArgDecls where
  args : Array Arg
  kwonly : Array Arg
  kwargs : Option (String × SpecType) := none
deriving Inhabited

namespace ArgDecls

def count (ad : ArgDecls) := ad.args.size + ad.kwonly.size

end ArgDecls

/--
A composable expression tree for translating Python `assert` statements into
structured preconditions and postconditions. Leaf nodes are `var`, `intLit`,
and `placeholder`; interior nodes represent operations like `len`, `getIndex`,
`intGe`/`intLe`, `isInstanceOf`, and `enumMember`.
-/
inductive SpecExpr where
/-- Stands in for an assert pattern not yet supported by the translator.
    The original Python expression is preserved in `Assertion.message`. -/
| placeholder (loc : SourceRange)
| var (name : String) (loc : SourceRange)
| getIndex (subject : SpecExpr) (field : String) (loc : SourceRange)
| isInstanceOf (subject : SpecExpr) (typeName : String) (loc : SourceRange)
/-- `stringLen subject` represents `len(subject)` where `subject` is a string.
    Used in preconditions like `assert len(name) >= 1`. -/
| stringLen (subject : SpecExpr) (loc : SourceRange)
| intLit (value : Int) (loc : SourceRange)
| intGe (subject : SpecExpr) (bound : SpecExpr) (loc : SourceRange)
| intLe (subject : SpecExpr) (bound : SpecExpr) (loc : SourceRange)
/-- A floating-point literal, stored as a string to preserve precision. -/
| floatLit (value : String) (loc : SourceRange)
| floatGe (subject : SpecExpr) (bound : SpecExpr) (loc : SourceRange)
| floatLe (subject : SpecExpr) (bound : SpecExpr) (loc : SourceRange)
| enumMember (subject : SpecExpr) (values : Array String) (loc : SourceRange)
/-- `regexMatch subject pattern` asserts that `subject` matches the regular
    expression `pattern`. Corresponds to `compile(pattern).search(subject) is not None`
    in the Python source. -/
| regexMatch (subject : SpecExpr) (pattern : String) (loc : SourceRange)
/-- `containsKey container key` asserts that `key` is present in `container`.
    Corresponds to `"key" in container` in the Python source. -/
| containsKey (container : SpecExpr) (key : String) (loc : SourceRange)
/-- `implies condition body` asserts that if `condition` holds then `body` holds.
    Used to represent conditional assertions like `if "field" in kwargs: assert ...`. -/
| implies (condition : SpecExpr) (body : SpecExpr) (loc : SourceRange)
/-- Logical negation. Used for else-branch conditions. -/
| not (e : SpecExpr) (loc : SourceRange)
/-- `forallList list varName body` asserts that `body` holds for every element
    of `list`, with `varName` bound to each element in turn. Only `body` may
    refer to `varName`. Corresponds to `for varName in list: assert body`. -/
| forallList (list : SpecExpr) (varName : String) (body : SpecExpr) (loc : SourceRange)
/-- `forallDict dict keyVar valVar body` asserts that `body` holds for every
    key-value pair in `dict`. Both `keyVar` and `valVar` are bound in `body`.
    Corresponds to `for keyVar, valVar in dict.items(): assert body`. -/
| forallDict (dict : SpecExpr) (keyVar : String) (valVar : String) (body : SpecExpr) (loc : SourceRange)
deriving Inhabited

/-- Structural equality ignoring source locations. -/
def SpecExpr.softBEq : SpecExpr → SpecExpr → Bool
  | .placeholder _, .placeholder _ => true
  | .var n₁ _, .var n₂ _ => n₁ == n₂
  | .getIndex s₁ f₁ _, .getIndex s₂ f₂ _ => s₁.softBEq s₂ && f₁ == f₂
  | .isInstanceOf s₁ t₁ _, .isInstanceOf s₂ t₂ _ => s₁.softBEq s₂ && t₁ == t₂
  | .stringLen s₁ _, .stringLen s₂ _ => s₁.softBEq s₂
  | .intLit v₁ _, .intLit v₂ _ => v₁ == v₂
  | .intGe s₁ b₁ _, .intGe s₂ b₂ _ => s₁.softBEq s₂ && b₁.softBEq b₂
  | .intLe s₁ b₁ _, .intLe s₂ b₂ _ => s₁.softBEq s₂ && b₁.softBEq b₂
  | .floatLit v₁ _, .floatLit v₂ _ => v₁ == v₂
  | .floatGe s₁ b₁ _, .floatGe s₂ b₂ _ => s₁.softBEq s₂ && b₁.softBEq b₂
  | .floatLe s₁ b₁ _, .floatLe s₂ b₂ _ => s₁.softBEq s₂ && b₁.softBEq b₂
  | .enumMember s₁ v₁ _, .enumMember s₂ v₂ _ => s₁.softBEq s₂ && v₁ == v₂
  | .regexMatch s₁ p₁ _, .regexMatch s₂ p₂ _ => s₁.softBEq s₂ && p₁ == p₂
  | .containsKey c₁ k₁ _, .containsKey c₂ k₂ _ => c₁.softBEq c₂ && k₁ == k₂
  | .implies c₁ b₁ _, .implies c₂ b₂ _ => c₁.softBEq c₂ && b₁.softBEq b₂
  | .not e₁ _, .not e₂ _ => e₁.softBEq e₂
  | .forallList l₁ v₁ b₁ _, .forallList l₂ v₂ b₂ _ =>
    l₁.softBEq l₂ && v₁ == v₂ && b₁.softBEq b₂
  | .forallDict d₁ k₁ v₁ b₁ _, .forallDict d₂ k₂ v₂ b₂ _ =>
    d₁.softBEq d₂ && k₁ == k₂ && v₁ == v₂ && b₁.softBEq b₂
  | _, _ => false

inductive MessagePart where
| str (s : String)
| expr (e : SpecExpr)
deriving Inhabited

structure Assertion where
  message : Array MessagePart
  formula : SpecExpr
deriving Inhabited

structure FunctionDecl where
  loc : SourceRange
  nameLoc : SourceRange
  name : String
  args : ArgDecls
  returnType : SpecType
  isOverload : Bool
  preconditions : Array Assertion
  postconditions : Array SpecExpr
deriving Inhabited

structure ClassField where
  name : String
  type : SpecType
  /-- An optional constant value for the field (e.g., from `self.x = expr` in `__init__`). -/
  constValue : Option String := none
deriving Inhabited

structure ClassVariable where
  name : String
  value : String
deriving Inhabited

structure ClassDef where
  loc : SourceRange
  name : String
  bases : Array PythonIdent := #[]
  fields : Array ClassField := #[]
  classVars : Array ClassVariable := #[]
  subclasses : Array ClassDef := #[]
  methods : Array FunctionDecl
  /-- When true, the spec is assumed to list every method the class exposes.
      Calls to unlisted methods are flagged as "Unknown method".
      Set via `@exhaustive` decorator on the pyspec class body. -/
  exhaustive : Bool := false
deriving Inhabited

structure TypeDef where
  loc : SourceRange
  nameLoc : SourceRange
  name : String
  definition : SpecType

inductive Signature where
  | externTypeDecl (name : String) (source :  PythonIdent)
  | classDef (d : ClassDef)
  | functionDecl (d : FunctionDecl)
  | typeDef (d : TypeDef)
  deriving Inhabited

end Strata.Python.Specs
end -- public section
