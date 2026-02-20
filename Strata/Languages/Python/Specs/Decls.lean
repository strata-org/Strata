/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashMap.Basic
public import Strata.DDM.Util.SourceRange

public section
namespace Strata.Python.Specs

/--
A fully-qualified Python identifier consisting of a module path and a name.
For example, `typing.List` has module "typing" and name "List".
-/
structure PythonIdent where
  pythonModule : String
  name : String
  deriving DecidableEq, Hashable, Inhabited, Ord, Repr

namespace PythonIdent

protected def ofString (s : String) : Option PythonIdent :=
  match s.revFind? '.' with
  | none => none
  | some idx =>
    some {
      pythonModule := s.extract s.startPos idx
      name := s.extract idx.next! s.endPos
    }

instance : ToString PythonIdent where
  toString i := s!"{i.pythonModule}.{i.name}"

def builtinsBool := mk "builtins" "bool"
def builtinsBytearray := mk "builtins" "bytearray"
def builtinsBytes := mk "builtins" "bytes"
def builtinsComplex := mk "builtins" "complex"
def builtinsDict := mk "builtins" "dict"
def builtinsFloat := mk "builtins" "float"
def builtinsInt := mk "builtins" "int"
def builtinsStr := mk "builtins" "str"
def noneType := mk "_types" "NoneType"

def typingAny := mk "typing" "Any"
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

end PythonIdent

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
| pyClass (name : String) (args : Array SpecType)
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

/--
A PySpec type is a union of atom types.
-/
structure SpecType where
  atoms : Array SpecAtomType
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
    values. Variants are ordered: ident < pyClass < intLiteral < stringLiteral
    < typedDict. -/
protected def SpecAtomType.compare (x y : SpecAtomType) : Ordering :=
  match x, y with
  | .ident xnm xargs, .ident ynm yargs =>
    compare xnm ynm |>.then $
      compareHLex (fun ⟨xe, _⟩ ye => xe.compare ye) xargs.attach yargs
  | .ident .., _ => .lt
  | _, .ident .. => .gt

  | .pyClass xname xargs, .pyClass yname yargs =>
    compare xname yname |>.then $
      compareHLex (fun ⟨xe, _⟩ ye => xe.compare ye) xargs.attach yargs
  | .pyClass .., _ => .lt
  | _, .pyClass .. => .gt

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
termination_by sizeOf x

/-- Compare two types by their atoms arrays, ignoring `loc`. -/
protected def SpecType.compare (x y : SpecType) : Ordering :=
  compareHLex (fun ⟨xe, _⟩ y => xe.compare y )
      x.atoms.attach y.atoms
termination_by sizeOf x
decreasing_by
  cases x
  case mk xl xa =>
    decreasing_tactic

end

instance : BEq SpecAtomType where
  beq x y := SpecAtomType.compare x y == .eq

instance : BEq SpecType where
  beq x y := SpecType.compare x y == .eq

instance : Ord SpecAtomType where
  compare := SpecAtomType.compare

instance : Ord SpecType where
  compare := SpecType.compare

instance : LT SpecAtomType where
  lt x y := private compare x y = .lt

namespace SpecType

instance : Repr SpecType where
  reprPrec tp prec := private reprPrec tp.atoms.toList prec

/--
Merges two sorted arrays of atom types into a single sorted array without
duplicates. Implements the core logic for union type operations using a
two-pointer algorithm.
-/
private partial def unionAux (x y : Array SpecAtomType) (i : Fin x.size) (j : Fin y.size) (r : Array SpecAtomType) : Array SpecAtomType :=
  let xe := x[i]
  let ye := y[j]
  match compare xe ye with
  | .lt =>
    let i' := i.val + 1
    if xip : i' < x.size then
      unionAux x y ⟨i', xip⟩ j (r.push xe)
    else
      r.push xe ++ y.drop j
  | .eq =>
    let i' := i.val + 1
    let j' := j.val + 1
    if xip : i' < x.size then
      if yjp : j' < y.size then
        unionAux x y ⟨i', xip⟩ ⟨j', yjp⟩ (r.push xe)
      else
        r.push xe ++ x.drop i'
    else
      r.push xe ++ y.drop j
  | .gt =>
    let j' := j.val + 1
    if yjp : j' < y.size then
      unionAux x y i ⟨j', yjp⟩ (r.push ye)
    else
      r.push ye ++ x.drop i.val

/-- Union two SpecTypes with a specified location for the result -/
def union (loc : SourceRange) (x y : SpecType) : SpecType :=
  if xp : 0 < x.atoms.size then
    if yp : 0 < y.atoms.size then
      { loc := loc, atoms := unionAux x.atoms y.atoms ⟨0, xp⟩ ⟨0, yp⟩ #[] }
    else
      x
  else
    y

def ofAtom (loc : SourceRange) (atom : SpecAtomType) : SpecType := { loc := loc, atoms := #[atom] }

@[specialize]
private def removeAdjDupsAux {α} [BEq α] (a : Array α) (i : Nat) (r : Array α) (rne : r.size > 0) : Array α :=
  if ilt : i < a.size then
    if r.back == a[i] then
      removeAdjDupsAux a (i+1) r rne
    else
      removeAdjDupsAux a (i+1) (r.push a[i]) (by simp +arith)
  else
    r

/--
Removes duplicate adjacent elements
-/
@[inline]
private def removeAdjDups {α} [BEq α] (a : Array α) : Array α :=
  if p : a.size = 0 then
    #[]
  else
    removeAdjDupsAux a 1 #[a[0]] (by simp +arith)

/-- Construct a `SpecType` from an array of atoms by sorting and
    removing duplicates to produce a canonical representation. -/
protected def ofArray (loc : SourceRange) (atoms : Array SpecAtomType) : SpecType :=
  let elts := atoms.qsort (· < ·)
  { loc := loc, atoms := removeAdjDups elts }

def ident (loc : SourceRange) (i : PythonIdent) (args : Array SpecType := #[]) : SpecType :=
  ofAtom loc (.ident i args)

def pyClass (loc : SourceRange) (name : String) (params : Array SpecType) : SpecType :=
  ofAtom loc (.pyClass name params)

def asSingleton (tp : SpecType) : Option SpecAtomType := do
  if tp.atoms.size = 1 then
    for atp in tp.atoms do return atp
  none

def isAtom (tp : SpecType) (atp : SpecAtomType) : Bool := tp.asSingleton.any (· == atp)

instance : Membership SpecAtomType SpecType where
  mem a e := private a.atoms.binSearchContains e (· < ·) = true

@[instance]
def instDecidableMem (e : SpecAtomType) (tp : SpecType) : Decidable (e ∈ tp) :=
  inferInstanceAs (Decidable (_ = _))

end SpecType

structure Arg where
  name : String
  type : SpecType
  hasDefault : Bool
deriving Inhabited

structure ArgDecls where
  args : Array Arg
  kwonly : Array Arg
deriving Inhabited

namespace ArgDecls

def count (ad : ArgDecls) := ad.args.size + ad.kwonly.size

end ArgDecls

/--
A specification predicate with `free` free variables (arguments + return value
for postconditions). Currently a placeholder; will be extended to support
actual constraint expressions.
-/
inductive SpecPred (free : Nat) where
| placeholder
deriving Inhabited

structure Assertion (free : Nat) where
  message : String
  formula : SpecPred free
deriving Inhabited

structure FunctionDecl where
  loc : SourceRange
  nameLoc : SourceRange
  name : String
  args : ArgDecls
  returnType : SpecType
  isOverload : Bool
  preconditions : Array (Assertion args.count)
  postconditions : Array (SpecPred (args.count + 1))
deriving Inhabited

structure ClassDef where
  loc : SourceRange
  name : String
  methods : Array FunctionDecl

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
end
