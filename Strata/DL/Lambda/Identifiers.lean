/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.FileRange
import Std.Data.HashMap.Lemmas

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)
open Strata

public section

/--
Identifiers with a name and additional metadata
-/
structure Identifier (IDMeta : Type) : Type where
  /-- A unique name. -/
  name : String
  /-- Any additional metadata that it would be useful to attach to an
  identifier. -/
  metadata : IDMeta
deriving Repr, DecidableEq, Inhabited, Hashable

instance : ToFormat (Identifier IDMeta) where
  format i := i.name

instance : ToString (Identifier IDMeta) where
  toString i := i.name

instance {IDMeta} [Inhabited IDMeta] : Coe String (Identifier IDMeta) where
  coe s := ⟨s, Inhabited.default⟩

/--
Identifiers, optionally with their inferred type.
-/
@[expose] abbrev IdentT (ITy IDMeta: Type) := (Identifier IDMeta) × Option ITy
@[expose] abbrev IdentTs (ITy IDMeta: Type) := List (IdentT ITy IDMeta)

instance {IDMeta ITy: Type} [ToFormat ITy]: ToFormat (IdentT ITy IDMeta) where
  format i := match i.snd with
    | none => f!"{i.fst}"
    | some ty => f!"({i.fst} : {ty})"

def IdentT.ident (x : (IdentT ITy IDMeta)) : Identifier IDMeta :=
  x.fst

def IdentT.ty? (x : (IdentT ITy IDMeta)) : Option ITy :=
  x.snd

def IdentTs.idents (xs : (IdentTs ITy IDMeta)) : List (Identifier IDMeta) :=
  xs.map Prod.fst

def IdentTs.tys? (xs : (IdentTs ITy IDMeta)) : List (Option ITy) :=
  xs.map Prod.snd

@[expose] abbrev Identifiers IDMeta := Std.HashMap String IDMeta

def Identifiers.default {IDMeta} : Identifiers IDMeta := Std.HashMap.emptyWithCapacity

/-
For an informative error message, takes in a `DiagnosticModel`
-/
def Identifiers.addWithError {IDMeta} (m: Identifiers IDMeta) (x: Identifier IDMeta) (f: DiagnosticModel) : Except DiagnosticModel (Identifiers IDMeta) :=
  let (b, m') := m.containsThenInsertIfNew x.name x.metadata
  if b then .error f else .ok m'

def Identifiers.addListWithError {IDMeta} (m: Identifiers IDMeta) (x: List (Identifier IDMeta)) (f: Identifier IDMeta → DiagnosticModel) :=
  x.foldlM (fun m x => Identifiers.addWithError m x (f x)) m

def Identifiers.add {IDMeta} (m: Identifiers IDMeta) (x: Identifier IDMeta) : Except DiagnosticModel (Identifiers IDMeta) :=
  m.addWithError x <| DiagnosticModel.fromFormat f!"Error: duplicate identifier {x.name}"

def Identifiers.contains {IDMeta} [DecidableEq IDMeta] (m: Identifiers IDMeta) (x: Identifier IDMeta) : Bool :=
  match m[x.name]?with
  | some i => x.metadata == i
  | none => false

def Identifiers.containsName {IDMeta} [DecidableEq IDMeta] (m: Identifiers IDMeta) (n: String) : Bool :=
  m[n]?.isSome

instance [ToFormat IDMeta] : ToFormat (Identifiers IDMeta) where
  format m := format (m.toList)

---------------------------------------------------------------------

end -- public section
end Lambda
