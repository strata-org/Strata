/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
-- [STOPGAP] Should be replaced by Std.HashMap.

-- Copied over from LNSym
-- https://github.com/leanprover/LNSym/blob/main/Arm/Map.lean

open Std (ToFormat Format format)

/-!
A simple Map-like type based on lists
-/

@[expose] def Map (α : Type u) (β : Type v) := List (α × β)

instance [BEq α] [BEq β] : BEq (Map α β) where
  beq m1 m2 := go m1 m2 where
  go m1 m2 :=
    match m1, m2 with
    | [], [] => true
    | x :: xrest, y :: yrest =>
      x == y && go xrest yrest
    | _, _ => false

instance : Inhabited (Map α β) where
  default := []

instance : EmptyCollection (Map α β) where
  emptyCollection := []

instance : HAppend (Map α β) (Map α β) (Map α β) where
  hAppend := List.append

instance [DecidableEq α] [DecidableEq β] [LawfulBEq α] [LawfulBEq β] : DecidableEq (Map α β) :=
  List.hasDecEq

instance [x : Repr (List (α × β))] : Repr (Map α β) where
  reprPrec := x.reprPrec

def Map.ofList (l : List (α × β)) : Map α β := l

def Map.toList (m : Map α β) : List (α × β) := m

def Map.format' [ToFormat α] [ToFormat β] (m : Map α β) : Format :=
  match m with
  | [] => ""
  | [(k, v)] => (format f!"({k}, {v})")
  | (k, v) :: rest =>
    (format f!"({k}, {v}) ") ++ Map.format' rest

instance [ToFormat α] [ToFormat β] : ToFormat (Map α β) where
  format := Map.format'

def Map.union (m1 m2 : Map α β) : Map α β :=
  List.append m1 m2

abbrev Map.empty : Map α β := []

def Map.find? [DecidableEq α] (m : Map α β) (a' : α) : Option β :=
  match m with
  | [] => none
  | (a, b) :: m => if a = a' then some b else find? m a'

def Map.contains [DecidableEq α] (m : Map α β) (a : α) : Bool :=
  m.find? a |>.isSome

def Map.insert [DecidableEq α] (m : Map α β) (a' : α) (b' : β) : Map α β :=
  match m with
  | [] => [(a', b')]
  | (a, b) :: m => if a = a' then (a', b') :: m else (a, b) :: insert m a' b'

/--
Remove the first occurence of element with key `a'` in `m`.
-/
def Map.remove [DecidableEq α] (m : Map α β) (a' : α) : Map α β :=
  match m with
  | [] => []
  | (a, b) :: m => if a = a' then m else (a, b) :: remove m a'

/--
Remove all occurences of elements with key `a'` in `m`.
-/
def Map.erase [DecidableEq α] (m : Map α β) (a' : α) : Map α β :=
  match m with
  | [] => []
  | (a, b) :: m => if a = a' then erase m a' else (a, b) :: erase m a'

def Map.isEmpty (m : Map α β) : Bool :=
  match m with
  | [] => true
  | _ => false

def Map.size (m : Map α β) : Nat :=
  m.length

def Map.keys (m : Map α β) : List α :=
  match m with
  | [] => []
  | (a, _) :: m => a :: keys m

def Map.values (m : Map α β) : List β :=
  match m with
  | [] => []
  | (_, a) :: m => a :: values m

/-- Are the keys of `m1` and `m2` disjoint? -/
def Map.disjointp [DecidableEq α] (m1 m2 : Map α β) : Prop :=
  ∀ k, (m1.find? k) = none ∨ (m2.find? k = none)

def Map.fmap (f: β → γ) (m: Map α β) : Map α γ :=
  List.map (fun (x, y) => (x, f y)) m

---------------------------------------------------------------------

theorem Map.find?_mem_keys [DecidableEq α] (m : Map α β)
  (h : Map.find? m k = some v) :
  k ∈ Map.keys m := by
  induction m with
  | nil => simp_all [Map.find?]
  | cons head tail ih =>
    simp [Map.find?] at h
    split at h
    · -- Case: head.fst = k
      simp [Map.keys]; simp_all
    · -- Case: head.fst ≠ k
      simp [Map.keys]; right; exact ih h

theorem Map.find?_mem_values [DecidableEq α] (m : Map α β)
  (h : Map.find? m k = some v) :
  v ∈ Map.values m := by
  induction m with
  | nil => simp [Map.find?] at h
  | cons head tail ih =>
    simp [Map.find?] at h
    split at h
    · -- Case: head.fst = k
      simp [Map.values]; simp_all
    · -- Case: head.fst ≠ k
      simp [Map.values]; right; exact ih h

theorem Map.find?_of_not_mem_values [DecidableEq α] (S : Map α β)
  (h1 : Map.find? S i = none) : i ∉ Map.keys S := by
  induction S; all_goals simp_all [Map.keys]
  rename_i _ head tail ih
  simp [Map.find?] at h1
  split at h1 <;> simp_all
  rename_i h; exact fun a => h (id (Eq.symm a))
  done

@[simp]
theorem Map.keys.length :
  (Map.keys ls).length = ls.length := by
  induction ls <;> simp [keys]
  case cons h t ih => assumption

theorem Map.mem_keys_of_mem_keys_remove [DecidableEq α] (m : Map α β) (k1 k2 : α)
  (h : k2 ∈ (Map.remove m k1).keys) : k2 ∈ m.keys := by
  induction m
  case nil => simp_all [Map.keys, Map.remove]
  case cons head tail tail_ih =>
    by_cases h_id_head : head.fst = k1
    case pos =>
      simp_all [Map.remove, Map.keys]
    case neg =>
      simp_all [Map.remove, Map.keys]
      cases h <;> try simp_all

theorem Map.mem_keys_remove_of_ne [DecidableEq α] (m : Map α β) (k a : α)
    (h_mem : a ∈ Map.keys m) (h_ne : a ≠ k) :
    a ∈ Map.keys (Map.remove m k) := by
  induction m with
  | nil => simp [Map.keys] at h_mem
  | cons hd tl ih =>
    obtain ⟨fst, snd⟩ := hd
    simp [Map.remove]
    split
    · rename_i h_eq
      simp [Map.keys] at h_mem
      cases h_mem with
      | inl h => exact absurd (h ▸ h_eq) h_ne
      | inr h => exact h
    · simp [Map.keys] at h_mem ⊢
      cases h_mem with
      | inl h => left; exact h
      | inr h => right; exact ih h

theorem Map.mem_values_of_mem_keys_remove [DecidableEq α] (m : Map α β) (k : α) (v : β)
  (h : v ∈ (Map.remove m k).values) : v ∈ m.values := by
  induction m
  case nil => simp_all [Map.values, Map.remove]
  case cons head tail tail_ih =>
    by_cases h_id_head : head.fst = k
    case pos =>
      simp_all [Map.remove, Map.values]
    case neg =>
      simp_all [Map.remove, Map.values]
      cases h <;> try simp_all

theorem Map.insert_keys [DecidableEq α] (m : Map α β) :
  (Map.insert m key val).keys ⊆ key :: Map.keys m := by
  induction m
  case nil => simp_all [Map.insert, Map.keys]
  case cons hd tl ih =>
    simp_all [Map.insert]
    split
    · simp_all [Map.keys]
    · simp_all [Map.keys]
      grind
  done

theorem Map.insert_values [DecidableEq α] (m : Map α β) :
  (Map.insert m key val).values ⊆ val :: Map.values m := by
  induction m
  case nil => simp_all [Map.insert, Map.values]
  case cons hd tl ih =>
    simp_all [Map.insert]
    split
    · simp_all [Map.values]
    · simp_all [Map.values]
      grind
  done

theorem Map.findNone_eq_notmem_mapfst {m: Map α β} [DecidableEq α]: ¬ a ∈ List.map Prod.fst m ↔ Map.find? m a = none := by
  induction m <;> simp [Map.find?]
  constructor <;> intro H
  split <;> simp_all
  split at H <;> simp_all
  rw [Eq.comm]; assumption
/-- `Map.erase` on a key not in the map is identity. -/
theorem Map.erase_of_find?_none [DecidableEq α]
    (m : Map α β) (x : α) (h : Map.find? m x = none) :
    Map.erase m x = m := by
  induction m with
  | nil => simp [Map.erase]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [Map.find?] at h; split at h
    · simp at h
    · rename_i h_ne
      simp only [Map.erase, h_ne, ↓reduceIte]
      exact congrArg ((a, b) :: ·) (ih h)

/-- `Map.erase` on a singleton appended at the end removes exactly that entry. -/
theorem Map.erase_append_singleton [DecidableEq α]
    (m : Map α β) (x : α) (v : β) (h : Map.find? m x = none) :
    Map.erase (List.append m [(x, v)]) x = m := by
  induction m with
  | nil => simp [Map.erase]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [Map.find?] at h; split at h
    · simp at h
    · rename_i h_ne
      show Map.erase ((a, b) :: (List.append ps [(x, v)])) x = (a, b) :: ps
      unfold Map.erase; split
      · exact absurd ‹_› h_ne
      · exact congrArg ((a, b) :: ·) (ih h)

/-- `Map.find?` on a map appended with a singleton map: either the new entry
    is found, or the result is the same as looking up in the original map. -/
theorem Map.find?_append_singleton [DecidableEq α]
    (m m' : Map α β) (x : α) (v : β) (y : α)
    (hm' : m' = [(x, v)]) :
    Map.find? (m ++ m') y = some v ∧ y = x ∨
    Map.find? (m ++ m') y = Map.find? m y := by
  subst hm'
  induction m with
  | nil =>
    unfold Map; simp only [List.nil_append, Map.find?]
    by_cases h : x = y
    · left; exact ⟨by simp [h], h.symm⟩
    · right; simp [h]
  | cons p m' ih =>
    obtain ⟨a, b⟩ := p
    unfold Map at *; simp only [List.cons_append, Map.find?]
    by_cases h : a = y
    · right; simp [h]
    · simp only [h, ↓reduceIte]; exact ih

/-- When `x` is not in the map, `Map.insert` appends `(x, v)` at the end. -/
theorem Map.insert_fresh_eq_append [DecidableEq α]
    (m : Map α β) (x : α) (v : β) (h : Map.find? m x = none) :
    Map.insert m x v = List.append m [(x, v)] := by
  induction m with
  | nil => unfold Map.insert; rfl
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [Map.find?] at h
    split at h
    · exact absurd h (by simp)
    · rename_i h_ne
      show (if a = x then (x, v) :: tl else (a, b) :: Map.insert tl x v) =
           (a, b) :: List.append tl [(x, v)]
      rw [if_neg h_ne]
      congr 1
      exact ih h

/-- After erasing key `x`, looking up `x` returns `none`. -/
theorem Map.find?_erase_self [DecidableEq α]
    (m : Map α β) (x : α) :
    Map.find? (Map.erase m x) x = none := by
  induction m with
  | nil => simp [Map.erase, Map.find?]
  | cons p ps ih =>
    simp only [Map.erase]; split
    · exact ih
    · simp only [Map.find?]; split
      · rename_i h_ne h_eq; exact absurd h_eq h_ne
      · exact ih

/-- Erasing key `x` does not affect lookups for a different key `y ≠ x`. -/
theorem Map.find?_erase_ne [DecidableEq α]
    (m : Map α β) (x y : α) (h_ne : y ≠ x) :
    Map.find? (Map.erase m x) y = Map.find? m y := by
  induction m with
  | nil => simp [Map.erase, Map.find?]
  | cons p ps ih =>
    simp only [Map.erase]; split
    · rename_i h_eq; simp only [Map.find?]; split
      · rename_i h_py; exact absurd (h_eq ▸ h_py.symm) h_ne
      · exact ih
    · simp only [Map.find?]; split
      · rfl
      · exact ih

/-- Values of a `zipWith Prod.mk` are the second list, truncated to the first list's length. -/
theorem Map.values_zipWith_eq_take (as : List α) (bs : List β) :
    Map.values (List.zipWith Prod.mk as bs) = bs.take as.length := by
  induction as generalizing bs with
  | nil => simp [Map.values]
  | cons a as' ih =>
    match bs with
    | [] => simp [Map.values, List.zipWith]
    | b :: bs' => simp [List.zipWith, Map.values]; exact ih bs'

/-- Removing key `k` does not affect lookups for a different key `a ≠ k`. -/
theorem Map.find?_remove_ne [DecidableEq α]
    (m : Map α β) (k a : α) (h_ne : a ≠ k) :
    Map.find? (Map.remove m k) a = Map.find? m a := by
  induction m with
  | nil => rfl
  | cons xv rest ih =>
    obtain ⟨x, v⟩ := xv
    simp only [Map.remove]
    by_cases h_xk : x = k
    · simp only [h_xk, ↓reduceIte]
      simp only [Map.find?, show k ≠ a from Ne.symm h_ne, ↓reduceIte]
    · simp only [h_xk, ↓reduceIte, Map.find?]
      grind

/-- Keys of `List.zip l1 l2` (viewed as a `Map`) are a subset of `l1`. -/
theorem Map.keys_zip_subset {α β : Type} [DecidableEq α]
    (l1 : List α) (l2 : List β) {x : α} (h : x ∈ Map.keys (l1.zip l2)) : x ∈ l1 := by
  induction l1 generalizing l2 with
  | nil => simp [List.zip, Map.keys] at h
  | cons a rest ih =>
    cases l2 with
    | nil => simp [List.zip, Map.keys] at h
    | cons b rest2 =>
      simp [List.zip, Map.keys] at h
      cases h with
      | inl h => subst h; exact List.mem_cons_self
      | inr h => exact List.mem_cons_of_mem a (ih rest2 h)

/-- `Map.find?` on a zip agrees with `List.find?` using BEq on the first component. -/
theorem Map.find_eq_list_find' [DecidableEq α] (vars : List α) (vals : List β) (x : α) :
    Map.find? (List.zip vars vals) x =
    (match (List.zip vars vals).find? (fun p => p.1 == x) with
     | some (_, v) => some v
     | none => none) := by
  induction vars generalizing vals with
  | nil => simp [List.zip, Map.find?]
  | cons v vs ih =>
    cases vals with
    | nil => simp [List.zip, Map.find?]
    | cons vl vls =>
      simp only [List.zip, List.zipWith, List.find?, Map.find?, BEq.beq]
      by_cases h_eq : v = x
      · simp [h_eq]
      · simp [h_eq]; exact ih vls

theorem Map.keys_erase_subset [DecidableEq α] (m : Map α β) (x : α) :
    ∀ k, k ∈ Map.keys (Map.erase m x) → k ∈ Map.keys m := by
  intro k hk; induction m with
  | nil => simp [Map.erase, Map.keys] at hk
  | cons pair rest ih =>
    obtain ⟨a, b⟩ := pair; simp only [Map.erase] at hk; split at hk
    · simp [Map.keys]; right; exact ih hk
    · simp [Map.keys] at hk ⊢
      grind

/-- Helper: `Map.find?` on `l.map (fun v => (v, f v))` returns `some (f v)` for `v ∈ l`. -/
theorem Map.find?_of_map_self {α : Type} [DecidableEq α] {β : Type}
    (l : List α) (f : α → β) (v : α) (hv : v ∈ l) :
    Map.find? (l.map (fun x => (x, f x))) v = some (f v) := by
  induction l with
  | nil => simp at hv
  | cons w ws ih =>
    simp only [List.map, Map.find?]
    grind

theorem Map.values_erase_subset [DecidableEq α] (m : Map α β) (x : α) :
    ∀ v, v ∈ Map.values (Map.erase m x) → v ∈ Map.values m := by
  induction m with
  | nil => simp [Map.erase, Map.values]
  | cons pair rest ih =>
    obtain ⟨k, val⟩ := pair; simp only [Map.erase]; split
    · intro v hv; simp [Map.values]; right; exact ih v hv
    · intro v hv; simp [Map.values] at hv ⊢
      grind

theorem Map.keys_erase_mem_of_ne [DecidableEq α] (m : Map α β) {a x : α}
    (h_key : a ∈ Map.keys m) (h_ne : a ≠ x) :
    a ∈ Map.keys (Map.erase m x) := by
  induction m with
  | nil => simp [Map.keys] at h_key
  | cons pair rest ih =>
    obtain ⟨k, v⟩ := pair; simp only [Map.erase]; simp [Map.keys] at h_key
    rcases h_key with rfl | h
    · split
      · exact absurd (by assumption) h_ne
      · simp [Map.keys]
    · split
      · exact ih h
      · simp [Map.keys]; right; exact ih h

-- Helper: Map.keys distributes over append
theorem Map.keys_append {α β : Type} (m1 m2 : Map α β) :
    Map.keys (m1 ++ m2) = Map.keys m1 ++ Map.keys m2 := by
  show Map.keys (List.append m1 m2) = Map.keys m1 ++ Map.keys m2
  induction m1 with
  | nil => rfl
  | cons hd tl ih => obtain ⟨a, _⟩ := hd; exact congrArg (a :: ·) ih

/-- Erasing key `a` removes `a` from a single Map's keys. -/
theorem Map.keys_erase_self_not_mem [DecidableEq α]
    (m : Map α β) (a : α)
    (h : a ∈ Map.keys (Map.erase m a)) : False := by
  induction m with
  | nil => simp [Map.erase, Map.keys] at h
  | cons pair rest ih =>
    obtain ⟨k, v⟩ := pair
    simp only [Map.erase] at h
    by_cases h_eq : k = a
    · simp [h_eq] at h; exact ih h
    · simp [h_eq, Map.keys] at h
      grind

/-- `Map.find?` returns `none` when the key is not in `Map.keys`. -/
theorem Map.find?_none_of_not_mem_keys' [DecidableEq α] (m : Map α β) (i : α)
    (h : i ∉ Map.keys m) : Map.find? m i = none := by
  induction m with
  | nil => simp [Map.find?]
  | cons p rest ih =>
    simp [Map.keys] at h; simp [Map.find?]
    split; exact absurd ‹_› (Ne.symm h.1); exact ih h.2

/-- `Map.find?` returns `some v` after `Map.insert m x v`. -/
theorem Map.find?_insert_self [DecidableEq α]
    (m : Map α β) (x : α) (v : β) : Map.find? (Map.insert m x v) x = some v := by
  induction m with
  | nil => simp [Map.insert, Map.find?]
  | cons hd rest ih => simp only [Map.insert]; split <;> simp_all [Map.find?]

/-- `Map.find?` is unchanged for a different key after `Map.insert`. -/
theorem Map.find?_insert_ne [DecidableEq α]
    (m : Map α β) (x y : α) (v : β) (h : x ≠ y) :
    Map.find? (Map.insert m y v) x = Map.find? m x := by
  induction m with
  | nil => simp [Map.insert, Map.find?, Ne.symm h]
  | cons hd rest ih =>
    simp only [Map.insert]
    split
    · rename_i h_eq  -- hd.fst = y
      -- Map.insert replaced hd with (y, v); hd.fst = y, so the if in find? checks y = x
      simp only [Map.find?]
      -- In the new list: first element is (y, v), check y = x
      have h_ne : ¬(y = x) := Ne.symm h
      simp [h_ne]
      -- In the old list: first element is hd, check hd.fst = x
      have h_ne2 : ¬(hd.fst = x) := by rw [h_eq]; exact h_ne
      simp [h_ne2]
    · simp only [Map.find?]; split <;> simp_all

-------------------------------------------------------------------------------
end
