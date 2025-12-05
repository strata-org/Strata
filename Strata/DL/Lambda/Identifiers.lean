/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.LTy
import Strata.DL.Util.Map

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

section Identifiers

/--
Identifiers with a name and additional metadata
-/
structure Identifier (IDMeta : Type) : Type where
  name : String
  metadata : IDMeta
deriving Repr, DecidableEq, Inhabited

instance : ToFormat (Identifier IDMeta) where
  format i := i.name

instance : ToString (Identifier IDMeta) where
  toString i := i.name

instance {IDMeta} [Inhabited IDMeta] : Coe String (Identifier IDMeta) where
  coe s := ⟨s, Inhabited.default⟩

/--
Identifiers, optionally with their inferred type.
-/
abbrev IdentT (ITy IDMeta: Type) := (Identifier IDMeta) × Option ITy
abbrev IdentTs (ITy IDMeta: Type) := List (IdentT ITy IDMeta)

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

abbrev Identifiers IDMeta := Std.HashMap String IDMeta

def Identifiers.default {IDMeta} : Identifiers IDMeta := Std.HashMap.emptyWithCapacity

/-
For an informative error message, takes in a `Format`
-/
def Identifiers.addWithError {IDMeta} (m: Identifiers IDMeta) (x: Identifier IDMeta) (f: Format) : Except Format (Identifiers IDMeta) :=
  let (b, m') := m.containsThenInsertIfNew x.name x.metadata
  if b then .error f else .ok m'

def Identifiers.add {IDMeta} (m: Identifiers IDMeta) (x: Identifier IDMeta) : Except Format (Identifiers IDMeta) :=
  m.addWithError x f!"Error: duplicate identifier {x.name}"

def Identifiers.contains {IDMeta} [DecidableEq IDMeta] (m: Identifiers IDMeta) (x: Identifier IDMeta) : Bool :=
  match m[x.name]?with
  | some i => x.metadata == i
  | none => false

def Identifiers.containsName {IDMeta} [DecidableEq IDMeta] (m: Identifiers IDMeta) (n: String) : Bool :=
  m[n]?.isSome

theorem Identifiers.addWithErrorNotin {IDMeta} [DecidableEq IDMeta] {m m': Identifiers IDMeta} {x: Identifier IDMeta}: m.addWithError x f = .ok m' → m.contains x = false := by
  unfold addWithError contains
  simp
  grind

theorem Identifiers.addWithErrorContains {IDMeta} [DecidableEq IDMeta] {m m': Identifiers IDMeta} {x: Identifier IDMeta}: m.addWithError x f = .ok m' → ∀ y, m'.contains y ↔ x = y ∨ m.contains y := by
  unfold addWithError contains;
  have m_contains := (Std.HashMap.containsThenInsertIfNew_fst (m:=m) (k:=x.name) (v:=x.metadata));
  have m'_def := (Std.HashMap.containsThenInsertIfNew_snd (m:=m) (k:=x.name) (v:=x.metadata));
  revert m_contains m'_def
  rcases (Std.HashMap.containsThenInsertIfNew m x.name x.metadata) with ⟨b, m''⟩; simp; intros b_eq m''_eq; subst b m'';
  split <;> intros m_contains; contradiction
  injection m_contains; subst m'; intros y; rw[Std.HashMap.getElem?_insertIfNew]
  cases name_eq: (x.name == y.name); grind
  rw[beq_iff_eq] at name_eq
  rename_i m_contains
  have name_notin : ¬ x.name ∈ m := by grind
  simp; rw[if_neg name_notin]
  cases meta_eq: (x.metadata == y.metadata); grind
  rw[beq_iff_eq] at meta_eq
  constructor
  . intros _; apply Or.inl; cases x; cases y; grind
  . rw[meta_eq]; intros _; simp

instance [ToFormat IDMeta] : ToFormat (Identifiers IDMeta) where
  format m := format (m.toList)

---------------------------------------------------------------------

end Identifiers
end Lambda
