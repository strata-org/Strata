/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Copied over from LNSym
-- https://github.com/leanprover/LNSym/blob/main/Arm/Map.lean

open Std (ToFormat Format format)

/-!
A simple Map-like type based on lists
-/

def ListMap (α : Type u) (β : Type v) := List (α × β)

instance [BEq α] [BEq β] : BEq (ListMap α β) where
  beq m1 m2 := go m1 m2 where
  go m1 m2 :=
    match m1, m2 with
    | [], [] => true
    | x :: xrest, y :: yrest =>
      x == y && go xrest yrest
    | _, _ => false

instance : Inhabited (ListMap α β) where
  default := []

instance : EmptyCollection (ListMap α β) where
  emptyCollection := []

instance : HAppend (ListMap α β) (ListMap α β) (ListMap α β) where
  hAppend := List.append

instance [DecidableEq α] [DecidableEq β] [LawfulBEq α] [LawfulBEq β] : DecidableEq (ListMap α β) :=
  List.hasDecEq

instance [x : Repr (List (α × β))] : Repr (ListMap α β) where
  reprPrec := x.reprPrec

def ListMap.ofList (l : List (α × β)) : ListMap α β := l

def ListMap.toList (m : ListMap α β) : List (α × β) := m

def ListMap.format' [ToFormat α] [ToFormat β] (m : ListMap α β) : Format :=
  match m with
  | [] => ""
  | [(k, v)] => (format f!"({k}, {v})")
  | (k, v) :: rest =>
    (format f!"({k}, {v}) ") ++ ListMap.format' rest

instance [ToFormat α] [ToFormat β] : ToFormat (ListMap α β) where
  format := ListMap.format'

def ListMap.union (m1 m2 : ListMap α β) : ListMap α β :=
  List.append m1 m2

abbrev ListMap.empty : ListMap α β := []

def ListMap.find? [DecidableEq α] (m : ListMap α β) (a' : α) : Option β :=
  match m with
  | [] => none
  | (a, b) :: m => if a = a' then some b else find? m a'

def ListMap.contains [DecidableEq α] (m : ListMap α β) (a : α) : Bool :=
  m.find? a |>.isSome

def ListMap.insert [DecidableEq α] (m : ListMap α β) (a' : α) (b' : β) : ListMap α β :=
  match m with
  | [] => [(a', b')]
  | (a, b) :: m => if a = a' then (a', b') :: m else (a, b) :: insert m a' b'

/--
Remove the first occurence of element with key `a'` in `m`.
-/
def ListMap.remove [DecidableEq α] (m : ListMap α β) (a' : α) : ListMap α β :=
  match m with
  | [] => []
  | (a, b) :: m => if a = a' then m else (a, b) :: remove m a'

/--
Remove all occurences of elements with key `a'` in `m`.
-/
def ListMap.erase [DecidableEq α] (m : ListMap α β) (a' : α) : ListMap α β :=
  match m with
  | [] => []
  | (a, b) :: m => if a = a' then erase m a' else (a, b) :: erase m a'

def ListMap.isEmpty (m : ListMap α β) : Bool :=
  match m with
  | [] => true
  | _ => false

def ListMap.size (m : ListMap α β) : Nat :=
  m.length

def ListMap.keys (m : ListMap α β) : List α :=
  match m with
  | [] => []
  | (a, _) :: m => a :: keys m

def ListMap.values (m : ListMap α β) : List β :=
  match m with
  | [] => []
  | (_, a) :: m => a :: values m

/-- Are the keys of `m1` and `m2` disjoint? -/
def ListMap.disjointp [DecidableEq α] (m1 m2 : ListMap α β) : Prop :=
  ∀ k, (m1.find? k) = none ∨ (m2.find? k = none)

---------------------------------------------------------------------

theorem ListMap.find?_mem_keys [DecidableEq α] (m : ListMap α β)
  (h : ListMap.find? m k = some v) :
  k ∈ ListMap.keys m := by
  induction m with
  | nil => simp_all [ListMap.find?]
  | cons head tail ih =>
    simp [ListMap.find?] at h
    split at h
    · -- Case: head.fst = k
      simp [ListMap.keys]; simp_all
    · -- Case: head.fst ≠ k
      simp [ListMap.keys]; right; exact ih h

theorem ListMap.find?_mem_values [DecidableEq α] (m : ListMap α β)
  (h : ListMap.find? m k = some v) :
  v ∈ ListMap.values m := by
  induction m with
  | nil => simp [ListMap.find?] at h
  | cons head tail ih =>
    simp [ListMap.find?] at h
    split at h
    · -- Case: head.fst = k
      simp [ListMap.values]; simp_all
    · -- Case: head.fst ≠ k
      simp [ListMap.values]; right; exact ih h

theorem ListMap.find?_of_not_mem_values [DecidableEq α] (S : ListMap α β)
  (h1 : ListMap.find? S i = none) : i ∉ ListMap.keys S := by
  induction S; all_goals simp_all [ListMap.keys]
  rename_i _ head tail ih
  simp [ListMap.find?] at h1
  split at h1 <;> simp_all
  rename_i h; exact fun a => h (id (Eq.symm a))
  done

@[simp]
theorem ListMap.keys.length :
  (ListMap.keys ls).length = ls.length := by
  induction ls <;> simp [keys]
  case cons h t ih => assumption

-------------------------------------------------------------------------------
