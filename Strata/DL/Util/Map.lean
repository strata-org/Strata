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

@[expose] def Map.find? [DecidableEq α] (m : Map α β) (a' : α) : Option β :=
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

@[expose] def Map.isEmpty (m : Map α β) : Bool :=
  match m with
  | [] => true
  | _ => false

def Map.size (m : Map α β) : Nat :=
  m.length

def Map.keys (m : Map α β) : List α :=
  match m with
  | [] => []
  | (a, _) :: m => a :: keys m

theorem Map.keys_eq_map_fst (m : Map α β) : m.keys = m.map Prod.fst := by
  induction m with
  | nil => rfl
  | cons p m ih => cases p; simp [Map.keys, ih]

/-- Deduplicated entries of a map, keeping the first occurrence of each key.
  Note that if the Map is produced via insertions, the keylist always has
  no duplicates, but without enforcing that at the type level, this
  construction is necessary for proofs. -/
def Map.keySet [DecidableEq α] (m : Map α β) : List (α × β) :=
  go m.reverse
where
  go : List (α × β) → List (α × β)
    | [] => []
    | (k, v) :: rest =>
      if Map.find? rest k = none then (k, v) :: go rest
      else go rest

private theorem Map.keySet.go_not_mem_of_find_none [DecidableEq α] (m : List (α × β)) (k : α)
    (h : Map.find? m k = none) : k ∉ (Map.keySet.go m).map Prod.fst := by
  induction m with
  | nil => simp [Map.keySet.go]
  | cons p rest ih =>
    simp only [Map.find?] at h
    split at h
    · simp at h
    · rename_i h_ne
      simp only [Map.keySet.go]
      split
      · simp only [List.map_cons, List.mem_cons]
        intro h_mem
        cases h_mem with
        | inl h_eq => exact absurd h_eq.symm h_ne
        | inr h_rest => exact absurd h_rest (ih h)
      · exact ih h

private theorem Map.keySet.go_nodup [DecidableEq α] (m : List (α × β)) :
    List.Nodup (Map.keySet.go m |>.map Prod.fst) := by
  induction m with
  | nil => exact List.nodup_nil
  | cons p rest ih =>
    simp only [Map.keySet.go]
    split
    · rename_i h_none
      simp only [List.map_cons]
      exact List.nodup_cons.mpr ⟨go_not_mem_of_find_none rest p.fst h_none, ih⟩
    · exact ih

theorem Map.keySet_nodup [DecidableEq α] (m : Map α β) :
    List.Nodup (m.keySet.map Prod.fst) :=
  Map.keySet.go_nodup m.reverse

theorem Map.find?_append [DecidableEq α] (l₁ l₂ : List (α × β)) (x : α) :
    Map.find? (l₁ ++ l₂) x = match Map.find? l₁ x with
      | some v => some v
      | none => Map.find? l₂ x := by
  induction l₁ with
  | nil => simp [Map.find?]
  | cons p rest ih =>
    simp only [List.cons_append, Map.find?]
    split
    · rfl
    · exact ih

private theorem Map.find?_none_of_reverse_none [DecidableEq α] (m : List (α × β)) (x : α)
    (h : Map.find? m x = none) : Map.find? m.reverse x = none := by
  induction m with
  | nil => simp [Map.find?]
  | cons p rest ih =>
    simp only [List.reverse_cons, Map.find?_append]
    simp only [Map.find?] at h
    split at h
    · exact absurd h (by simp)
    · rename_i h_ne
      rw [ih h]
      simp only [Map.find?]
      split
      · rename_i h_eq; exact absurd h_eq h_ne
      · rfl

theorem Map.find?_none_iff_reverse_none [DecidableEq α] (m : List (α × β)) (x : α) :
    Map.find? m x = none ↔ Map.find? m.reverse x = none := by
  constructor
  · exact Map.find?_none_of_reverse_none m x
  · intro h
    have h_rr : m = m.reverse.reverse := (List.reverse_reverse m).symm
    rw [h_rr]
    exact Map.find?_none_of_reverse_none m.reverse x h

private theorem Map.keySet.go_find_rev_iff [DecidableEq α] (m : List (α × β)) (x : α) (v : β) :
    Map.find? m.reverse x = some v ↔ (x, v) ∈ Map.keySet.go m := by
  induction m with
  | nil => simp [Map.keySet.go, Map.find?]
  | cons p rest ih =>
    simp only [List.reverse_cons, Map.keySet.go]
    split
    · rename_i h_none
      rw [Map.find?_append]
      cases h_find_rev : Map.find? rest.reverse x with
      | some w =>
        simp only
        constructor
        · intro h_eq
          injection h_eq with h_wv
          exact List.mem_cons.mpr (Or.inr (ih.mp (h_wv ▸ h_find_rev)))
        · intro h_mem
          cases List.mem_cons.mp h_mem with
          | inl h_eq =>
            have h_xeq : x = p.fst := congrArg Prod.fst h_eq
            rw [h_xeq] at h_find_rev
            have h_none_rev := Map.find?_none_of_reverse_none rest p.fst h_none
            rw [h_none_rev] at h_find_rev
            exact absurd h_find_rev (by simp)
          | inr h_rest =>
            have h_rv := ih.mpr h_rest
            rw [h_rv] at h_find_rev
            injection h_find_rev with h_wv
            subst h_wv; rfl
      | none =>
        simp only [Map.find?]
        split
        · rename_i h_eq
          constructor
          · intro h_val; injection h_val with h_vs
            exact List.mem_cons.mpr (Or.inl (by rw [h_eq, h_vs]))
          · intro h_mem
            cases List.mem_cons.mp h_mem with
            | inl h_peq => exact congrArg some (congrArg Prod.snd h_peq).symm
            | inr h_rest =>
              have h_rv := ih.mpr h_rest
              rw [h_rv] at h_find_rev
              exact absurd h_find_rev (by simp)
        · rename_i h_ne
          constructor
          · intro h_abs; exact absurd h_abs (by simp)
          · intro h_mem
            cases List.mem_cons.mp h_mem with
            | inl h_peq => exact absurd (congrArg Prod.fst h_peq).symm h_ne
            | inr h_rest =>
              have h_rv := ih.mpr h_rest
              rw [h_rv] at h_find_rev
              exact absurd h_find_rev (by simp)
    · rename_i h_some
      rw [Map.find?_append]
      cases h_find_rev : Map.find? rest.reverse x with
      | some w =>
        simp only []
        constructor
        · intro h_eq; injection h_eq with h_wv; exact ih.mp (h_wv ▸ h_find_rev)
        · intro h_mem
          have h_rv := ih.mpr h_mem
          rw [h_rv] at h_find_rev
          injection h_find_rev with h_wv
          subst h_wv; rfl
      | none =>
        simp only [Map.find?]
        constructor
        · intro h_find_p
          split at h_find_p
          · rename_i h_eq
            have h_rest_none := (Map.find?_none_iff_reverse_none rest x).mpr h_find_rev
            rw [← h_eq] at h_rest_none
            exact absurd h_rest_none h_some
          · exact absurd h_find_p (by simp)
        · intro h_mem
          exact absurd (ih.mpr h_mem) (by rw [h_find_rev]; simp)

theorem Map.find?_iff_mem_keySet [DecidableEq α] (m : Map α β) (x : α) (v : β) :
    Map.find? m x = some v ↔ (x, v) ∈ m.keySet := by
  unfold Map.keySet
  have h_rr : m.reverse.reverse = m := List.reverse_reverse m
  conv => lhs; rw [show m = m.reverse.reverse from h_rr.symm]
  exact Map.keySet.go_find_rev_iff m.reverse x v

/-- `Map.find?` returning `some v` implies `(x, v)` is a member of the map (as a list). -/
theorem Map.find?_mem [DecidableEq α] (m : Map α β) (x : α) (v : β)
    (h : Map.find? m x = some v) : List.Mem (x, v) m := by
  induction m with
  | nil => simp [Map.find?] at h
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    simp only [Map.find?] at h
    split at h
    · injection h with h; subst h; rename_i heq; subst heq; exact List.Mem.head _
    · exact List.Mem.tail _ (ih h)

theorem Map.findNone_eq_notmem_mapfst {m: Map α β} [DecidableEq α]: ¬ a ∈ List.map Prod.fst m ↔ Map.find? m a = none := by
  induction m <;> simp [Map.find?]
  constructor <;> intro H
  split <;> simp_all
  split at H <;> simp_all
  rw [Eq.comm]; assumption

theorem Map.find?_keySet [DecidableEq α] (m : Map α β) (k : α) :
    Map.find? m.keySet k = Map.find? m k := by
  cases h : Map.find? m k with
  | none =>
    cases h_ks : Map.find? m.keySet k with
    | none => rfl
    | some w =>
      have h_mem := Map.find?_mem m.keySet k w h_ks
      have h_find := (Map.find?_iff_mem_keySet m k w).mpr h_mem
      rw [h_find] at h
      exact absurd h (by simp)
  | some v =>
    have h_mem := (Map.find?_iff_mem_keySet m k v).mp h
    cases h_ks : Map.find? m.keySet k with
    | none =>
      have h_not_mem := Map.findNone_eq_notmem_mapfst.mpr h_ks
      exact absurd (List.mem_map_of_mem (f := Prod.fst) h_mem) h_not_mem
    | some w =>
      have h_mem_w := Map.find?_mem m.keySet k w h_ks
      have h_find_w := (Map.find?_iff_mem_keySet m k w).mpr h_mem_w
      rw [h] at h_find_w; injection h_find_w with h_vw; subst h_vw; rfl

def Map.values (m : Map α β) : List β :=
  match m with
  | [] => []
  | (_, a) :: m => a :: values m

/-- Are the keys of `m1` and `m2` disjoint? -/
def Map.disjointp [DecidableEq α] (m1 m2 : Map α β) : Prop :=
  ∀ k, (m1.find? k) = none ∨ (m2.find? k = none)

@[expose] def Map.fmap (f: β → γ) (m: Map α β) : Map α γ :=
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

theorem Map.find?_fmap [DecidableEq α] (m : Map α β) (f : β → γ) (k : α) :
    Map.find? (m.fmap f) k = (Map.find? m k).map f := by
  induction m with
  | nil => simp [Map.find?, Map.fmap]
  | cons head tail ih =>
    simp only [Map.fmap, List.map, Map.find?]
    split
    · simp_all
    · exact ih

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

/-- If `Map.find?` returns `some e`, there is an index `i` where the key
lives and no earlier entry has the same key. -/
theorem Map.find?_index [DecidableEq α] {m : Map α β} {a : α} {b : β}
    (h : Map.find? m a = some b)
    : ∃ (i : Nat), (m.map Prod.fst)[i]? = some a
        ∧ (m.map Prod.snd)[i]? = some b
        ∧ ∀ j < i, (m.map Prod.fst)[j]? ≠ some a := by
  induction m with
  | nil => simp [Map.find?] at h
  | cons p rest ih =>
    simp only [Map.find?] at h
    split at h
    · rename_i heq
      cases h
      exact ⟨0, by simp [heq], by simp, fun j hj => by omega⟩
    · rename_i hne
      obtain ⟨i, hk, hv, hfirst⟩ := ih h
      refine ⟨i + 1, by simpa using hk, by simpa using hv, fun j hj => ?_⟩
      cases j with
      | zero => simp; exact hne
      | succ n => simpa using hfirst n (by omega)

/-- If `find?` succeeds on `m` at key `a`, and `cs` has the same length as `m`,
then `find?` on `m.map fst |>.zip cs` also succeeds, and the values come from
the same index. -/
theorem Map.find?_zip [DecidableEq α] {m : Map α β} {a : α} {b : β}
    {cs : List γ}
    (h : Map.find? m a = some b) (hlen : cs.length = m.length)
    : ∃ (c : γ) (i : Nat), Map.find? ((m.map Prod.fst).zip cs) a = some c
           ∧ (m.map Prod.snd)[i]? = some b
           ∧ cs[i]? = some c := by
  induction m generalizing cs with
  | nil => simp [Map.find?] at h
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    cases cs with
    | nil => simp at hlen
    | cons c cs' =>
      simp only [Map.find?] at h
      have hlen' : cs'.length = rest.length := by simpa using hlen
      split at h <;> rename_i heq
      · cases h
        refine ⟨c, 0, ?_, by simp, by simp⟩
        simp [Map.find?, heq]
      · obtain ⟨c', i, hfind, hsnd, hcs⟩ := ih h hlen'
        refine ⟨c', i + 1, ?_, by simpa using hsnd, by simpa using hcs⟩
        simp [Map.find?, heq, hfind]

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
  unfold Map;
  unfold instHAppendMap
  subst hm'
  induction m with
  | nil =>
    simp only [Map.find?, List.append]
    by_cases h : x = y
    · grind
    · right; simp [h]
  | cons p m' ih =>
    obtain ⟨a, b⟩ := p
    simp only [Map.find?, List.append]
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
