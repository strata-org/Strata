/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/



-- [STOPGAP] Should be replaced by Std.HashMap.

-- Copied over from LNSym
-- https://github.com/leanprover/LNSym/blob/main/Arm/Map.lean

open Std (ToFormat Format format)

/-!
A simple Map-like type based on lists
-/

abbrev Map (α : Type u) (β : Type v) := List (α × β)

instance [BEq α] [BEq β] : BEq (Map α β) where
  beq m1 m2 := go m1 m2 where
  go m1 m2 :=
    match m1, m2 with
    | [], [] => true
    | x :: xrest, y :: yrest =>
      x == y && go xrest yrest
    | _, _ => false

instance [x : Repr (List (α × β))] : Repr (Map α β) where
  reprPrec := x.reprPrec

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

---------------------------------------------------------------------

@[simp] theorem Map.find?_empty [DecidableEq α] (a : α) :
  (Map.empty (β := β)).find? a = none := rfl

@[simp] theorem Map.find?_insert [DecidableEq α] (m : Map α β) (a : α) (b : β) :
  (m.insert a b).find? a = some b := by
  induction m <;> simp [find?, insert] <;> split <;> simp [find?, *]

@[simp] theorem Map.find?_insert_of_ne [DecidableEq α] (m : Map α β) {a a' : α} (b : β) :
  a ≠ a' → (m.insert a b).find? a' = m.find? a' := by
  intro h; induction m <;> simp [find?, insert, *] <;> split <;> simp [find?, *]

theorem Map_find?_of_tail [DecidableEq α] (tail : Map α β)
  (h : Map.find? (head :: tail) x = none) :
  (Map.find? tail x) = none := by
  simp_all [Map.find?]; split at h
  all_goals simp_all

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

@[simp] theorem Map.contains_empty [DecidableEq α] (a : α) :
  (Map.empty (β := β)).contains a = false := rfl

@[simp] theorem Map.contains_insert [DecidableEq α] (m : Map α β) (a : α) (b : β) :
   (m.insert a b).contains a = true := by
  simp [contains]

@[simp] theorem Map.contains_insert_of_ne [DecidableEq α] (m : Map α β) {a a' : α} (b : β) :
    a ≠ a' → (m.insert a b).contains a' = m.contains a' := by
  intro; simp [contains, *]

@[simp] theorem Map.isEmpty_empty :
  (Map.empty (α := α) (β := β)).isEmpty = true := rfl

@[simp] theorem Map.isEmpty_insert_eq_false [DecidableEq α] (m : Map α β) (a : α) (b : β) :
  (m.insert a b).isEmpty = false := by
  induction m <;> simp [insert]
  next => rfl
  next => split <;> simp [isEmpty]

@[simp] theorem Map.size_empty_eq : (Map.empty (α := α) (β := β)).size = 0 := rfl

@[simp] theorem Map.size_insert_eq_of_contains [DecidableEq α] (m : Map α β) (a : α) (b : β) :
   m.contains a = true → (m.insert a b).size = m.size := by
  induction m <;> simp [insert, size]
  intro h; split
  next => simp
  next heq =>
    simp [contains, find?, heq] at h
    simp_all [contains, size]

@[simp] theorem Map.size_insert_eq_of_not_contains [DecidableEq α]
  (m : Map α β) (a : α) (b : β) :
  m.contains a = false → (m.insert a b).size = m.size + 1 := by
  induction m <;> simp [insert, size]
  case cons head tail ih =>
    intro h; split
    next heq => simp [contains, find?, heq] at h
    next heq =>
      simp [contains, find?, heq] at h
      simp [contains, h, size] at ih
      simp [*]

@[simp] theorem Map.erase_empty [DecidableEq α] (a : α) :
  (Map.empty (β := β)).erase a = Map.empty := rfl

@[simp] theorem Map.find?_erase [DecidableEq α] (m : Map α β) (a : α) :
  (m.erase a).find? a = none := by
  induction m <;> simp [erase]
  split <;> simp [*, find?]

@[simp] theorem Map.find?_erase_of_ne [DecidableEq α] (m : Map α β) {a a' : α} :
  a ≠ a' → (m.erase a).find? a' = m.find? a' := by
  intro h
  induction m <;> simp [erase, find?]
  split <;> simp [*, find?]

@[simp] theorem Map.contains_erase [DecidableEq α] (m : Map α β) (a : α) :
  (m.erase a).contains a = false := by
  simp [contains]

@[simp] theorem Map.contains_erase_of_ne [DecidableEq α] (m : Map α β) {a a' : α} :
  a ≠ a' → (m.erase a).contains a' = m.contains a' := by
  intro; simp [contains, *]

@[simp] theorem Map.erase_insert [DecidableEq α] (m : Map α β) (a : α) (b : β) :
  m.contains a = false → (m.insert a b).erase a = m := by
  induction m <;> simp [insert, erase]
  next head tail ih =>
    intro h
    split
    next he => simp [contains, find?, he] at h
    next he =>
     simp [contains, find?, he] at h
     simp [contains, h] at ih
     simp [erase, ih, he]

@[simp] theorem Map.size_erase_le [DecidableEq α] (m : Map α β) (a : α) :
  (m.erase a).size ≤ m.size := by
  induction m <;> simp [erase, size] at *
  split
  next => omega
  next => simp; omega

@[simp] theorem Map.size_erase_eq [DecidableEq α] (m : Map α β) (a : α) :
  m.contains a = false → (m.erase a).size = m.size := by
  induction m <;> simp [erase, size] at *
  split <;> simp [contains, find?, *] at *; assumption

@[simp] theorem Map.size_erase_lt [DecidableEq α] (m : Map α β) (a : α) :
  m.contains a = true → (m.erase a).size < m.size := by
  intro h
  induction m <;> simp [erase, size, contains, find?] at *
  next head tail ih =>
  split
  next => have := Map.size_erase_le tail a;
          exact Nat.lt_succ_of_le this
  next he => simp_all only [ite_false, List.length_cons, true_implies]
             exact Nat.add_lt_add_right ih 1

theorem Map.find?_first [DecidableEq α] (x : α) (y : β) :
  Map.find? ((x, y) :: m) x = some y := by
  simp [Map.find?]

theorem Map.find?_rest [DecidableEq α] (k1 : α) (hneq : k1 ≠ k2) :
  Map.find? ((k1, y) :: m) k2 = Map.find? m k2 := by
  simp_all [Map.find?]

@[simp]
theorem Map.empty_union_left (m : Map α β) :
  Map.union [] m = m := by simp_all [Map.union]

@[simp]
theorem Map.empty_union_right (m : Map α β) :
  Map.union m [] = m := by
  induction m <;> simp_all [Map.union]

@[simp]
theorem Map.empty_disjointp_left [DecidableEq α] (m : Map α β) :
  Map.disjointp [] m := by simp_all [Map.disjointp]

@[simp]
theorem Map.empty_disjointp_right [DecidableEq α] (m : Map α β) :
  Map.disjointp m [] := by simp_all [Map.disjointp]

@[simp]
theorem Map.find?_union {m1 m2 : Map α β} [DecidableEq α] :
   (Map.union m1 m2).find? p = (m1.find? p).or (m2.find? p) := by
   simp_all [Map.union]
   induction m1 <;> simp_all
   rename_i head tail ih
   by_cases h : head.1 = p <;> simp_all [Map.find?]

theorem Map.disjointp_union_find? {m1 m2 : Map α β} [DecidableEq α]
  (h_disjointp : Map.disjointp m2 m1)
  (h_x_in_m1 : Map.find? m1 k = some v) :
  Map.find? (Map.union m2 m1) k = some v := by
  simp_all [Map.disjointp]
  have h_disjointp_k := @h_disjointp k
  simp_all

theorem Map.disjointp_tail [DecidableEq α] (m1 m2 : Map α β)
  (h : Map.disjointp (p :: m2) m1) :
  Map.disjointp m2 m1 := by
  simp_all [Map.disjointp]
  intro k
  have h' := @h k
  clear h
  have hp : p = (p.1, p.2) := by simp_all
  by_cases hk : k = p.1
  case pos => -- k = p.1
    subst k
    rw [hp] at h'
    simp [Map.find?_first] at h'
    simp_all
  case neg => -- k ≠ p.1
    rw [hp] at h'
    rwa [Map.find?_rest] at h'
    exact Ne.symm hk
  done

-------------------------------------------------------------------------------
