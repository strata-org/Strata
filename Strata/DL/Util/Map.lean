/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- [STOPGAP] Should be replaced by Std.HashMap.

-- Copied over from LNSym
-- https://github.com/leanprover/LNSym/blob/main/Arm/Map.lean

open Std (ToFormat Format format)

/-!
A simple Map-like type based on lists
-/

def Map (α : Type u) (β : Type v) := List (α × β)

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
-------------------------------------------------------------------------------
