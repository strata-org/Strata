/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

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

/-- `BEq` for identifiers, derived from `DecidableEq`. Provided explicitly (rather
    than relying on `instBEqOfDecidableEq`) so that the `LawfulBEq` instance below
    is about a named `BEq`, which in turn gives `LawfulHashable` for free. This is
    what makes `Identifier` usable as a `HMap`/`HMaps` key. -/
instance instBEqIdentifier {IDMeta : Type} [DecidableEq IDMeta] : BEq (Identifier IDMeta) :=
  ⟨fun a b => decide (a = b)⟩

instance instLawfulBEqIdentifier {IDMeta : Type} [DecidableEq IDMeta] :
    LawfulBEq (Identifier IDMeta) where
  eq_of_beq {a b} h := by simp only [BEq.beq, decide_eq_true_eq] at h; exact h
  rfl {a} := by simp [BEq.beq]

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
For an informative error message, takes in a `Message`
-/
def Identifiers.addWithError {IDMeta} (m: Identifiers IDMeta) (x: Identifier IDMeta) (f: Message) : Except Message (Identifiers IDMeta) :=
  let (b, m') := m.containsThenInsertIfNew x.name x.metadata
  if b then .error f else .ok m'

def Identifiers.addListWithError {IDMeta} (m: Identifiers IDMeta) (x: List (Identifier IDMeta)) (f: Identifier IDMeta → Message) :=
  x.foldlM (fun m x => Identifiers.addWithError m x (f x)) m

def Identifiers.add {IDMeta} (m: Identifiers IDMeta) (x: Identifier IDMeta) : Except Message (Identifiers IDMeta) :=
  m.addWithError x <| Message.fromFormat f!"Error: duplicate identifier {x.name}"

def Identifiers.contains {IDMeta} [DecidableEq IDMeta] (m: Identifiers IDMeta) (x: Identifier IDMeta) : Bool :=
  match m[x.name]?with
  | some i => x.metadata == i
  | none => false

def Identifiers.containsName {IDMeta} [DecidableEq IDMeta] (m: Identifiers IDMeta) (n: String) : Bool :=
  m[n]?.isSome

/-- If `m` contains `x`, then looking up `x`'s name yields exactly `x`'s metadata. -/
theorem Identifiers.contains_getElem? {IDMeta} [DecidableEq IDMeta]
    (m : Identifiers IDMeta) (x : Identifier IDMeta) (h : m.contains x = true) :
    m[x.name]? = some x.metadata := by
  simp only [Identifiers.contains] at h
  split at h
  · rename_i i h_get; simp only [beq_iff_eq] at h; rw [h_get, h]
  · exact absurd h (by simp)

instance [ToFormat IDMeta] : ToFormat (Identifiers IDMeta) where
  format m := format (m.toList)

---------------------------------------------------------------------

end -- public section
end Lambda
