/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.GOTO.SourceLocation
import Strata.Util.Tactics

namespace CProverGOTO
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

public section

namespace Ty

namespace Identifier
/-
Ref.:
cbmc/src/util/std_types.h
cbmc/src/util/mathematical_types.h
cbmc/src/util/irep_ids.def
-/

/--
Primitive types. These correspond to `ID_*` identifiers in
`cbmc/src/util/irep_ids.def`.
-/
inductive Primitive where
  | bool
  | empty
  | string
  | regex
  | integer
  | real
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Primitive where
  format p := match p with
    | .bool => "bool"
    | .empty => "empty"
    | .string => "string"
    | .regex => "regex"
    | .integer => "integer"
    | .real => "real"

/-- Bitvector types -/
inductive BitVector where
  | signedbv (width : Nat)
  | unsignedbv (width : Nat)
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat BitVector where
  format bv := match bv with
    | .signedbv w => f!"signedbv[{w}]"
    | .unsignedbv w => f!"unsignedbv[{w}]"

/-- Function and code types -/
inductive Function where
  | code
  deriving Repr, Inhabited, DecidableEq

/-- The size of an array type (CBMC `array_typet::size`). -/
inductive ArraySize where
  /-- A fixed number of elements. -/
  | constant (n : Nat)
  /-- An unbounded array (CBMC `infinity`). -/
  | infinity
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat ArraySize where
  format s := match s with
    | .constant n => f!"{n}"
    | .infinity => "infinity"

end Identifier

inductive Identifier where
  /-- Primitive types -/
  | primitive (p : Identifier.Primitive)
  /-- Bitvector types -/
  | bitVector (bv : Identifier.BitVector)
  /-- A reference to a named struct type (like CBMC's `struct_tag`). -/
  | structTag (name : String)
  /-- Array type with an optional size. `subtypes = [element]`, or
      `[element, index]` when the array has an explicit index type. -/
  | array (size : Option Identifier.ArraySize)
  /-- Code (function) type; `subtypes = returnType :: parameterTypes`. Each
      parameter is written as a CBMC `parameter` irep, as in a function's
      symbol table entry. -/
  | code
  /-- Pointer type (CBMC `pointer_typet`); `subtypes = [pointee]`, width fixed at 64. -/
  | pointer
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Identifier where
  format i := match i with
    | .primitive p => f!"{p}"
    | .bitVector bv => f!"{bv}"
    | .structTag name => f!"struct_tag({name})"
    | .array none => f!"array"
    | .array (some size) => f!"array[{size}]"
    | .code => f!"code"
    | .pointer => f!"pointer"

end Ty

-------------------------------------------------------------------------------

/--
GOTO [Types](https://diffblue.github.io/cbmc/classtypet.html)
-/
structure Ty where
  /--
  The interpretation of `Ty` depends on the `id` field.
  CBMC pre-defines some type IDs in `util/irep_ids.def`.
  -/
  id         : Ty.Identifier
  subtypes   : List Ty := []
  sourceLoc  : SourceLocation := .nil
  deriving Repr, Inhabited

def Ty.beq (x y : Ty) : Bool :=
  x.id == y.id && x.sourceLoc == y.sourceLoc &&
  go x.subtypes y.subtypes
  termination_by (SizeOf.sizeOf x)
  decreasing_by cases x; term_by_mem
  where go xs ys :=
  match xs, ys with
  | [], [] => true
  | _, [] | [], _ => false
  | x :: xrest, y :: yrest =>
    Ty.beq x y && go xrest yrest
  termination_by (SizeOf.sizeOf xs)

instance : BEq Ty where
  beq := Ty.beq

def formatTy (t : Ty) : Format :=
  let subtypes := t.subtypes.map (fun s => formatTy s)
  let subtypes := Format.joinSep subtypes f!" "
  if subtypes.isEmpty then
    f!"{t.id}"
  else
    f!"({t.id} {subtypes})"
  termination_by (SizeOf.sizeOf t)
  decreasing_by cases t; term_by_mem

instance : ToFormat Ty where
  format t := formatTy t

namespace Ty

/-- Empty type -/
@[expose, match_pattern]
def Empty : Ty :=
  { id := .primitive .empty }

/-- Boolean type -/
@[expose, match_pattern]
def Boolean : Ty :=
  { id := .primitive .bool }

/-- Integer type -/
@[expose, match_pattern]
def Integer : Ty :=
  { id := .primitive .integer }

/-- String type -/
@[expose, match_pattern]
def String : Ty :=
  { id := .primitive .string }

/-- Regex type -/
@[expose, match_pattern]
def Regex : Ty :=
  { id := .primitive .regex }

/-- Real type -/
@[expose, match_pattern]
def Real : Ty :=
  { id := .primitive .real }

/-- Signed bitvector type -/
@[expose, match_pattern]
def SignedBV (width : Nat) : Ty :=
  { id := .bitVector (.signedbv width) }

/-- Unsigned bitvector type -/
@[expose, match_pattern]
def UnsignedBV (width : Nat) : Ty :=
  { id := .bitVector (.unsignedbv width) }

/-- A reference to a named struct type (e.g., a user-defined datatype). -/
@[expose, match_pattern]
def StructTag (name : _root_.String) : Ty :=
  { id := .structTag name }

/-- Array type with element type -/
@[expose, match_pattern]
def Array (elemTy : Ty) : Ty :=
  { id := .array none, subtypes := [elemTy] }

/-- Array type with element type `elemTy`, an optional `size` and an optional
    index type (CBMC's `#index_type`; without it CBMC indexes with
    `signedbv 64`). -/
def mkArray (elemTy : Ty) (size : Option Identifier.ArraySize)
    (indexTy : Option Ty := none) : Ty :=
  { id := .array size, subtypes := elemTy :: indexTy.toList }

/-- Pointer type to `pointee` (CBMC `pointer_typet`, width 64). -/
@[expose, match_pattern]
def Pointer (pointee : Ty) : Ty :=
  { id := .pointer, subtypes := [pointee] }

/-- The type of a function with parameter types `paramTypes` and return type
    `returnType`, equal (up to parameter names) to the type in the function's
    symbol table entry written by `createFunctionSymbol`; the type of a
    `FUNCTION_CALL` callee symbol, which `cbmc --validate-goto-model` checks
    against the symbol table. -/
def mkFunctionType (paramTypes : List Ty) (returnType : Ty) : Ty :=
  { id := .code, subtypes := returnType :: paramTypes }

end Ty

/--
A struct type definition (CBMC `struct_typet`): the struct's name and its
components, in order, as `(name, type)` pairs. It is declared in the symbol
table as the type symbol `tag-<name>`; expressions of the struct have the type
`Ty.StructTag name`.
-/
structure StructDef where
  name       : String
  components : List (String × Ty)
  deriving Repr, Inhabited

/-- The type of the values of the struct `s`. -/
def StructDef.ty (s : StructDef) : Ty :=
  .StructTag s.name

-------------------------------------------------------------------------------

end -- public section
