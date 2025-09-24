/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.DL.Util.Map

open Std (ToFormat Format format)

abbrev Maps (α : Type u) (β : Type v) := List (Map α β)

instance : Inhabited (Maps α β) where
  default := []

def Maps.format' [ToFormat (Map α β)] (ms : Maps α β) : Format :=
  match ms with
  | [] => ""
  | [m] => (format f!"[{m}]")
  | m :: rest =>
    (format f!"[{m}]{Format.line}") ++ Maps.format' rest

instance[ToFormat (Map α β)] : ToFormat (Maps α β) where
  format := Maps.format'

def Maps.keys (ms : Maps α β) : List α :=
  match ms with
  | [] => []
  | m :: mrest => m.keys ++ Maps.keys mrest

def Maps.values (ms : Maps α β) : List β :=
  match ms with
  | [] => []
  | m :: mrest => m.values ++ Maps.values mrest

def Maps.isEmpty (m : Maps α β) : Bool :=
  match m with
  | [] => true
  | _ => false

/--
Add Map `m` to the beginning of Maps `ms`.
-/
def Maps.push (ms : Maps α β) (m : Map α β) : Maps α β :=
  m :: ms

/--
Remove the newest Map in `ms`. Do nothing if `ms` is empty.
-/
def Maps.pop (ms : Maps α β) : Maps α β :=
  match ms with
  | [] => []
  | _ :: rest => rest

/--
Get the oldest map (i.e., from the end) in `ms`.
-/
def Maps.oldest (ms : Maps α β) : Map α β :=
  ms.getLastD []

/--
Drop the oldest map in `ms`.
-/
def Maps.dropOldest (ms : Maps α β) : Maps α β :=
  ms.dropLast

/--
Get the newest map (i.e., from the beginning) in `ms`.
-/
def Maps.newest (ms : Maps α β) : Map α β :=
  match ms with | [] => [] | m :: _ => m

/--
Append `m` to the end of the newest map in `ms`.
-/
def Maps.addInNewest (ms : Maps α β) (m : Map α β) : Maps α β :=
  let new := ms.newest ++ m
  let ms := ms.pop
  ms.push new

/--
Flatten the Maps `ms` to get a single map.

Searching for `(x : α)` after flattening will proceed from the newest to
the oldest Map.
-/
def Maps.toSingleMap (ms : Maps α β) : Map α β :=
  ms.flatten

/--
Look up `(x : α)` in all the maps in `ms`.
-/
def Maps.find? [DecidableEq α] (ms : Maps α β) (x : α) : Option β :=
  match ms with
  | [] => none
  | m :: rest =>
    match m.find? x with
    | none => Maps.find? rest x
    | some v => some v

/--
Look up `(x : α)` in all the maps in `ms`, returning the default element `d` if
`x` is not found.
-/
def Maps.findD [DecidableEq α] (ms : Maps α β) (x : α) (d : β) : β :=
  match ms with
  | [] => d
  | m :: rest =>
    match m.find? x with
    | none => Maps.findD rest x d
    | some v => v

/--
Remove the first occurence of element with key `a'` in `m`, starting from the
newest map.
-/
def Maps.remove [DecidableEq α] [BEq (Map α β)] (m : Maps α β) (a' : α) : Maps α β :=
  match m with
  | [] => []
  | m :: mrest =>
    let m' := Map.remove m a'
    if m' == m then
      m :: (remove mrest a')
    else
      m' :: (remove mrest a')

/--
Erase `x` and its associated value from `ms`.
-/
def Maps.erase [DecidableEq α] (ms : Maps α β) (x : α) : Maps α β :=
  match ms with
  | [] => []
  | m :: rest => Map.erase m x :: Maps.erase rest x

/--
Update `x` with `v` in `ms`. Do nothing if `x` is not in `ms`.
-/
def Maps.update [DecidableEq α] (ms : Maps α β) (x : α) (v : β) : Maps α β :=
  match ms with
  | [] => []
  | m :: rest =>
    match m.find? x with
    | none => m :: (Maps.update rest x v)
    | some _ => (m.insert x v) :: rest

/--
Insert `(x, v)` in `ms`. If `x` is already in `ms`, update that entry.
Else add it to the most recent map.
-/
def Maps.insert [DecidableEq α] (ms : Maps α β) (x : α) (v : β) : Maps α β :=
  let x_exists := ms.find? x
  match x_exists with
  | none =>
    let m := ms.newest
    let m' := m.insert x v
    (ms.pop).push m'
  | some _ => Maps.update ms x v

/--
Insert `(x, v)` in the oldest map in `ms`. Do nothing if `x` is already in `ms`.
-/
def Maps.insertInOldest [DecidableEq α] (ms : Maps α β) (x : α) (v : β) : Maps α β :=
  let rec go (acc : Maps α β) : Maps α β → Maps α β
    | [] =>
      let m_elem := Map.ofList [(x, v)]
      if acc.isEmpty then [m_elem]
      else acc.reverse ++ [m_elem]
    | [m] =>
      match m.find? x with
      | some _ => acc.reverse ++ [m]
      | none =>
        let m_elem := Map.ofList [(x, v)]
        acc.reverse ++ [m ++ m_elem]
    | m :: rest =>
      match m.find? x with
      | some _ => acc.reverse ++ (m :: rest)
      | none => go (m :: acc) rest
  go [] ms

/--
Insert `(xi, vi)` -- where `xi` and `vi` are corresponding elements of `xs` and
`vs` -- in the oldest map in `ms`, only if `xi` is not in `ms`.
-/
def Maps.addInOldest [DecidableEq α] (ms : Maps α β) (xs : List α) (vs : List β) : Maps α β :=
  match xs, vs with
  | [], _ | _, [] => ms
  | x :: xrest, v :: vrest =>
    let ms := Maps.insertInOldest ms x v
    Maps.addInOldest ms xrest vrest

---------------------------------------------------------------------

theorem Maps.find?_mem_keys [DecidableEq α] (m : Maps α β)
  (h : Maps.find? m k = some v) :
  k ∈ Maps.keys m := by
  induction m with
  | nil => simp_all [Maps.find?]
  | cons head tail ih =>
    simp [Maps.find?] at h
    split at h
    · simp [Maps.keys]; simp_all
    · rename_i _ v1 heq
      simp at h; subst v1
      simp [Maps.keys]
      have := @Map.find?_mem_keys α β k v _ head heq
      simp_all
  done

theorem Maps.find?_mem_values [DecidableEq α] (m : Maps α β)
  (h : Maps.find? m k = some v) :
  v ∈ Maps.values m := by
  induction m with
  | nil => simp [Maps.find?] at h
  | cons head tail ih =>
    simp [Maps.find?] at h
    split at h
    · simp [Maps.values]; simp_all
    · rename_i _ v1 heq
      simp at h; subst v1
      simp [Maps.values]
      have := @Map.find?_mem_values α β k v _ head heq
      simp_all

theorem Maps.find?_of_not_mem_values [DecidableEq α] (S : Maps α β)
  (h1 : Maps.find? S i = none) : i ∉ Maps.keys S := by
  induction S; all_goals simp_all [Maps.keys]
  rename_i _ head tail ih
  simp [Maps.find?] at h1
  split at h1 <;> simp_all
  rename_i h
  exact Map.find?_of_not_mem_values head h
  done

private theorem Maps.insert_fresh_key_subset [DecidableEq α] (ms : Maps α β)
  (h : Maps.find? ms key = none) :
  (Maps.insert ms key val).keys ⊆ key :: Maps.keys ms := by
  simp_all [Maps.insert, Maps.pop, Maps.push, Maps.newest, Maps.keys]
  split <;> simp_all [Map.insert, Maps.keys, Map.keys]
  rename_i ms m ms_rest
  have := @Map.insert_keys _ _ key val _ m
  grind
  done

private theorem Maps.insert_fresh_key_subset_value [DecidableEq α] (ms : Maps α β)
  (h : Maps.find? ms key = none) :
  (Maps.insert ms key val).values ⊆ val :: Maps.values ms := by
  simp_all [Maps.insert, Maps.pop, Maps.push, Maps.newest, Maps.values]
  split <;> simp_all [Map.insert, Maps.values, Map.values]
  rename_i ms m ms_rest
  have := @Map.insert_values _ _ key val _ m
  grind
  done

private theorem Maps.insert_key_update_subset [DecidableEq α] (ms : Maps α β)
  (h : ¬ Maps.find? ms key = none) :
  (Maps.insert ms key val).keys ⊆ Maps.keys ms := by
  simp_all [Maps.insert, Maps.pop, Maps.push, Maps.newest]
  split <;> simp_all
  rename_i v heq
  induction ms
  case nil => simp_all [Maps.find?]
  case cons hd tl ih =>
    simp_all [Maps.update, Maps.find?]
    split <;> simp_all [Maps.keys]
    rename_i heq_hd_key
    have := @Map.find?_mem_keys _ _ key v _ hd heq_hd_key
    have := @Map.insert_keys _ _ key val _ hd
    grind
  done

private theorem Maps.insert_key_update_subset_value [DecidableEq α] (ms : Maps α β)
  (h : ¬ Maps.find? ms key = none) :
  (Maps.insert ms key val).values ⊆ val :: Maps.values ms := by
  simp_all [Maps.insert, Maps.pop, Maps.push, Maps.newest]
  split <;> simp_all
  rename_i v heq
  induction ms
  case nil => simp_all [Maps.find?]
  case cons hd tl ih =>
    simp_all [Maps.update, Maps.find?]
    split <;> simp_all [Maps.values]
    rename_i heq_hd_key
    · have := @Map.find?_mem_values _ _ key val _ hd;
      have := @Map.insert_values _ _ key val _ hd;
      grind
    · have := @Map.find?_mem_values _ _ key val _ hd
      have := @Map.insert_values _ _ key val _ hd
      grind
  done

theorem Maps.insert_keys_subset [DecidableEq α] (ms : Maps α β) :
  (Maps.insert ms key val).keys ⊆ key :: Maps.keys ms := by
  have h1 := @Maps.insert_fresh_key_subset _ _ key val _ ms
  have h2 := @Maps.insert_key_update_subset _ _ key val _ ms
  grind
  done

theorem Maps.insert_values_subset [DecidableEq α] (ms : Maps α β) :
  (Maps.insert ms key val).values ⊆ val :: Maps.values ms := by
  have h1 := @Maps.insert_fresh_key_subset_value _ _ key val _ ms
  have h2 := @Maps.insert_key_update_subset_value _ _ key val _ ms
  grind

@[simp]
theorem Maps.keys_of_push_empty :
  (Maps.push ms []).keys = ms.keys := by
  simp_all [Maps.push, Maps.keys, Map.keys]

@[simp]
theorem Maps.values_of_push_empty :
  (Maps.push ms []).values = ms.values := by
  simp_all [Maps.push, Maps.values, Map.values]

theorem Maps.mem_keys_of_mem_keys_remove [DecidableEq α] [BEq (Map α β)]
  (ms : Maps α β) (k1 k2 : α) (h : k2 ∈ (Maps.remove ms k1).keys) :
  k2 ∈ ms.keys := by
  induction ms
  case nil => simp_all [Maps.keys, Maps.remove]
  case cons m ms ih =>
    simp_all [Maps.remove, Maps.keys]
    split at h <;> simp_all [Maps.keys]
    · grind
    · cases h
      · simp [@Map.mem_keys_of_mem_keys_remove _ _ _ m k1 k2 (by assumption)]
      · simp_all

theorem Maps.mem_values_of_mem_keys_remove [DecidableEq α] [BEq (Map α β)]
  (ms : Maps α β) (k : α) (v : β) (h : v ∈ (Maps.remove ms k).values) :
  v ∈ ms.values := by
  induction ms
  case nil => simp_all [Maps.values, Maps.remove]
  case cons m ms ih =>
    simp_all [Maps.remove, Maps.values]
    split at h <;> simp_all [Maps.values]
    · grind
    · cases h
      · simp [@Map.mem_values_of_mem_keys_remove _ _ _ m k v (by assumption)]
      · simp_all

---------------------------------------------------------------------
