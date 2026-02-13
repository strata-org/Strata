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
  deriving DecidableEq, Hashable, Ord, Repr

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
| noneType
/-
A typed dictionary with an array of fields and their types.  The arrays
must be of the same length.
If the `isTotal` flag is set, then all fields are required, and if not the
fields are optional.
-/
| typedDict (fields : Array String)
            (fieldTypes : Array SpecType)
            (isTotal : Bool)
deriving BEq, Hashable, Inhabited, Ord, Repr

/--
A PySpec type is a union of atom types.
-/
structure SpecType where
  atoms : Array SpecAtomType
deriving Inhabited, Ord

end

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
      unionAux x y i ⟨j', yjp⟩ (r.push xe)
    else
      r.push xe ++ x.drop i.val

instance : OrOp SpecType where
  or x y := private
    if xp : 0 < x.atoms.size then
      if yp : 0 < y.atoms.size then
        { atoms := unionAux x.atoms y.atoms ⟨0, xp⟩ ⟨0, yp⟩ #[] }
      else
        x
    else
      y

def ofAtom (atom : SpecAtomType) : SpecType := { atoms := #[atom] }

def ofArray (atoms : Array SpecAtomType) : SpecType := { atoms := atoms.qsort (· < ·) }

def ident (i : PythonIdent) (args : Array SpecType := #[]) : SpecType :=
  .ofAtom (.ident i args)

def pyClass (name : String) (params : Array SpecType) : SpecType := ofAtom <| .pyClass name params

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
