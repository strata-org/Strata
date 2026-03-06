/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.SourceLocation
import Strata.Util.Tactics

namespace CProverGOTO
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

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
  | integer
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Primitive where
  format p := match p with
    | .bool => "bool"
    | .empty => "empty"
    | .string => "string"
    | .integer => "integer"

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

end Identifier

inductive Identifier where
  /-- Primitive types -/
  | primitive (p : Identifier.Primitive)
  /-- Bitvector types -/
  | bitVector (bv : Identifier.BitVector)
  deriving Repr, Inhabited, DecidableEq

instance : ToFormat Identifier where
  format i := match i with
    | .primitive p => f!"{p}"
    | .bitVector bv => f!"{bv}"

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
@[match_pattern]
def Empty : Ty :=
  { id := .primitive .empty }

/-- Boolean type -/
@[match_pattern]
def Boolean : Ty :=
  { id := .primitive .bool }

/-- Integer type -/
@[match_pattern]
def Integer : Ty :=
  { id := .primitive .integer }

/-- String type -/
@[match_pattern]
def String : Ty :=
  { id := .primitive .string }

/-- Signed bitvector type -/
@[match_pattern]
def SignedBV (width : Nat) : Ty :=
  { id := .bitVector (.signedbv width) }

/-- Unsigned bitvector type -/
@[match_pattern]
def UnsignedBV (width : Nat) : Ty :=
  { id := .bitVector (.unsignedbv width) }

end Ty

-------------------------------------------------------------------------------
