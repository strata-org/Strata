/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


-- import Std.Data.HashMap.Lemmas
import Strata.DL.Lambda.LTy
import Strata.DL.Util.Map

---------------------------------------------------------------------

-- -- Not merged in Lean release yet, so prove it ourselves
@[simp]
theorem Std.HashMap.contains_eq_false_iff_not_mem  {α : Type u} {β : Type v} [BEq α] [Hashable α] {m : Std.HashMap α β} {k : α} :
m.contains k = false ↔ ¬k ∈ m := by
  have m_cont := (Std.HashMap.contains_iff_mem (m:=m) (a:=k))
  revert m_cont; cases (m.contains k) <;> simp

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
Identifiers, optionally with their inferred monotype.
-/
abbrev IdentT (IDMeta : Type) := (Identifier IDMeta) × Option LMonoTy
abbrev IdentTs (IDMeta : Type) := List (IdentT IDMeta)

instance {IDMeta : Type} : ToFormat (IdentT IDMeta) where
  format i := match i.snd with
    | none => f!"{i.fst}"
    | some ty => f!"({i.fst} : {ty})"

def IdentT.ident (x : (IdentT IDMeta)) : Identifier IDMeta :=
  x.fst

def IdentT.monoty? (x : (IdentT IDMeta)) : Option LMonoTy :=
  x.snd

def IdentTs.idents (xs : (IdentTs IDMeta)) : List (Identifier IDMeta) :=
  xs.map Prod.fst

def IdentTs.monotys? (xs : (IdentTs IDMeta)) : List (Option LMonoTy) :=
  xs.map Prod.snd

abbrev Identifiers IDMeta := Std.HashMap String IDMeta

def Identifiers.default {IDMeta} : Identifiers IDMeta := Std.HashMap.emptyWithCapacity

/-
For an informative error message
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
  unfold addWithError contains;
  match h: (Std.HashMap.containsThenInsertIfNew m x.name x.metadata) with
  | ⟨b, m'⟩ =>
    simp;
    cases b with
    | true => simp
    | false =>
      simp; intro C; subst m';
      have Hnotin := (Std.HashMap.containsThenInsertIfNew_fst (m:=m) (k:=x.name) (v:=x.metadata));
      rw[h] at Hnotin;
      symm at Hnotin
      rw [Std.HashMap.contains_eq_isSome_getElem?] at Hnotin
      revert Hnotin
      cases m[x.name]? <;> simp



-- Does this exist
theorem not_false {P: Prop} [Decidable P]: ¬ P → (if P then x else y) = y :=
  by grind

theorem Identifiers.addWithErrorContains {IDMeta} [DecidableEq IDMeta] {m m': Identifiers IDMeta} {x: Identifier IDMeta}: m.addWithError x f = .ok m' → ∀ y, m'.contains y ↔ x = y ∨ m.contains y := by
  unfold addWithError contains;
  have m_contains := (Std.HashMap.containsThenInsertIfNew_fst (m:=m) (k:=x.name) (v:=x.metadata));
  have m'_def := (Std.HashMap.containsThenInsertIfNew_snd (m:=m) (k:=x.name) (v:=x.metadata));
  revert m_contains m'_def
  rcases (Std.HashMap.containsThenInsertIfNew m x.name x.metadata) with ⟨b, m''⟩; simp; intros b_eq m''_eq; subst b m'';
  cases m_contains: (Std.HashMap.contains m x.name) <;> simp; intros m'_eq; subst m'_eq; intros y; rw[Std.HashMap.getElem?_insertIfNew];
  cases name_eq: (x.name == y.name)
  case false =>
    simp; intros x_eq_y; subst x; rw[BEq.rfl ] at name_eq; contradiction
  case true =>
    rw[beq_iff_eq] at name_eq
    simp; rw[Std.HashMap.contains_eq_false_iff_not_mem] at m_contains;
    -- is there a better way?
    rw[not_false m_contains]; simp
    cases meta_eq: (x.metadata == y.metadata)
    case false => grind
    case true =>
      rw[beq_iff_eq] at meta_eq
      constructor
      . intros _; apply Or.inl; cases x; cases y; grind
      . rw[meta_eq]; intros _; rfl

def Identifiers.eq {IDMeta} (m1 m2: Identifiers IDMeta) : Prop :=
  Std.HashMap.Equiv m1 m2

instance [ToFormat IDMeta] : ToFormat (Identifiers IDMeta) where
  format m := format (m.toList)


---------------------------------------------------------------------

end Identifiers
end Lambda
