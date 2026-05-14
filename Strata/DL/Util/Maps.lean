/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Util.Map
import all Strata.DL.Util.Map

open Std (ToFormat Format format)

public section

@[expose] abbrev Maps (α : Type u) (β : Type v) := List (Map α β)

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
@[expose] def Maps.toSingleMap (ms : Maps α β) : Map α β :=
  ms.flatten

/--
Look up `(x : α)` in all the maps in `ms`.
-/
@[expose] def Maps.find? [DecidableEq α] (ms : Maps α β) (x : α) : Option β :=
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
@[expose] def Maps.findD [DecidableEq α] (ms : Maps α β) (x : α) (d : β) : β :=
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

theorem Maps.mem_keys_remove_of_ne [DecidableEq α] [BEq (Map α β)]
    (ms : Maps α β) (k a : α)
    (h_mem : a ∈ Maps.keys ms) (h_ne : a ≠ k) :
    a ∈ Maps.keys (Maps.remove ms k) := by
  induction ms with
  | nil => simp [Maps.keys] at h_mem
  | cons m mrest ih =>
    simp [Maps.keys] at h_mem
    simp [Maps.remove]
    split <;> simp [Maps.keys]
    · cases h_mem with
      | inl h => left; exact h
      | inr h => right; exact ih h
    · cases h_mem with
      | inl h =>
        left; exact Map.mem_keys_remove_of_ne m k a h h_ne
      | inr h => right; exact ih h

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

/-- `Maps.find?` returns `none` when the key is not in `Maps.keys`. -/
theorem Maps.not_mem_keys_find?_none' [DecidableEq α] (S : Maps α β) (i : α)
    (h : i ∉ Maps.keys S) : Maps.find? S i = none := by
  induction S with
  | nil => simp [Maps.find?]
  | cons m rest ih =>
    simp [Maps.keys] at h; simp [Maps.find?]
    simp [Map.find?_none_of_not_mem_keys' m i h.1]; exact ih h.2

/-- If a key is in `Maps.keys`, then `Maps.find?` returns `some`. -/
theorem Maps.find?_of_mem_keys' [DecidableEq α] (S : Maps α β) (i : α)
    (h : i ∈ Maps.keys S) : ∃ v, Maps.find? S i = some v := by
  induction S with
  | nil => simp [Maps.keys] at h
  | cons m rest ih =>
    simp [Maps.keys] at h
    simp [Maps.find?]
    cases h_eq : Map.find? m i with
    | some v => exact ⟨v, rfl⟩
    | none =>
      have h_not_in_m : i ∉ Map.keys m := Map.find?_of_not_mem_values m h_eq
      exact ih (by cases h with | inl h => exact absurd h h_not_in_m | inr h => exact h)

/-- `Maps.update ms x v` maps `x` to `v`. -/
theorem Maps.find?_update_self [DecidableEq α]
    (ms : Maps α β) (x : α) (v : β) (h : ms.find? x ≠ none) :
    (Maps.update ms x v).find? x = some v := by
  induction ms with
  | nil => simp [Maps.find?] at h
  | cons m rest ih =>
    simp only [Maps.update]; split
    · rename_i h_none; simp only [Maps.find?, h_none]; apply ih
      simp [Maps.find?, h_none] at h; exact h
    · simp [Maps.find?, Map.find?_insert_self]

/-- `Maps.insert ms x v` maps `x` to `v`. -/
theorem Maps.find?_insert_self [DecidableEq α]
    (ms : Maps α β) (x : α) (v : β) :
    Maps.find? (Maps.insert ms x v) x = some v := by
  simp only [Maps.insert]; split
  · match ms with
    | [] => simp [Maps.pop, Maps.push, Maps.newest, Maps.find?, Map.find?_insert_self]
    | _ :: _ => simp [Maps.pop, Maps.push, Maps.newest, Maps.find?, Map.find?_insert_self]
  · exact Maps.find?_update_self ms x v (by simp_all)

/-- `Maps.find?` is unchanged for a different key after `Maps.insert`. -/
theorem Maps.find?_insert_ne [DecidableEq α]
    (ms : Maps α β) (x y : α) (v : β) (h_ne : x ≠ y) :
    Maps.find? (Maps.insert ms y v) x = Maps.find? ms x := by
  simp only [Maps.insert]
  cases h_fb : Maps.find? ms y with
  | none =>
    match ms with
    | [] => simp [Maps.pop, Maps.push, Maps.newest, Maps.find?, Map.find?, Map.insert, Ne.symm h_ne]
    | _ :: _ =>
      simp only [Maps.pop, Maps.push, Maps.newest, Maps.find?]
      rw [Map.find?_insert_ne _ _ _ _ h_ne]
  | some val =>
    induction ms with
    | nil => simp [Maps.find?] at h_fb
    | cons m rest ih =>
      simp only [Maps.update]
      split
      · rename_i h_none
        simp only [Maps.find?]
        cases Map.find? m x with
        | none =>
          have h_rest : Maps.find? rest y = some val := by
            simp only [Maps.find?, h_none] at h_fb; exact h_fb
          exact ih h_rest
        | some _ => rfl
      · simp only [Maps.find?]
        rw [Map.find?_insert_ne _ _ _ _ h_ne]

/-- `Maps.erase` on a key not in any scope is identity. -/
theorem Maps.erase_of_fresh [DecidableEq α]
    (ms : Maps α β) (x : α) (h : ∀ m, m ∈ ms → Map.find? m x = none) :
    Maps.erase ms x = ms := by
  induction ms with
  | nil => simp [Maps.erase]
  | cons m rest ih =>
    simp only [Maps.erase]; congr 1
    · exact Map.erase_of_find?_none m x (h m List.mem_cons_self)
    · exact ih (fun r hr => h r (List.mem_cons_of_mem m hr))

/-- Erasing a key that was just added to the newest scope restores the original value,
    provided the key didn't exist in the original and the maps are non-empty. -/
theorem Maps.erase_addInNewest_fresh [DecidableEq α]
    {m : Map α β} {rest : Maps α β} (x : α) (v : β)
    (h_fresh : ∀ s, s ∈ (m :: rest) → Map.find? s x = none) :
    Maps.erase (Maps.addInNewest (m :: rest) [(x, v)]) x = m :: rest := by
  -- addInNewest (m :: rest) [(x, v)] = (m ++ [(x, v)]) :: rest
  show Map.erase (List.append m [(x, v)]) x :: Maps.erase rest x = m :: rest
  congr 1
  · exact Map.erase_append_singleton m x v (h_fresh m List.mem_cons_self)
  · exact Maps.erase_of_fresh rest x (fun r hr => h_fresh r (List.mem_cons_of_mem m hr))

/-- Looking up in `addInNewest ms [(x, v)]` either returns the new binding or
    falls through to the original map. -/
theorem Maps.find?_addInNewest_single [DecidableEq α]
    (ms : Maps α β) (x : α) (v : β) (y : α) :
    Maps.find? (Maps.addInNewest ms [(x, v)]) y = some v ∧ y = x ∨
    Maps.find? (Maps.addInNewest ms [(x, v)]) y = Maps.find? ms y := by
  -- After unfolding, addInNewest ms [(x,v)] prepends (newest ms ++ [(x,v)]) to (pop ms).
  -- We case split on ms and use Map.find?_append_singleton on the newest map.
  cases ms with
  | nil =>
    show Maps.find? (Maps.addInNewest [] [(x, v)]) y = some v ∧ y = x ∨
         Maps.find? (Maps.addInNewest [] [(x, v)]) y = Maps.find? [] y
    simp only [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]
    rcases Map.find?_append_singleton [] [(x, v)] x v y rfl with ⟨h1, h2⟩ | h1
    · left
      constructor
      · simp only [Maps.find?]; rw [h1]
      · exact h2
    · right
      simp only [Maps.find?]; rw [h1]; rfl
  | cons m rest =>
    show Maps.find? (Maps.addInNewest (m :: rest) [(x, v)]) y = some v ∧ y = x ∨
         Maps.find? (Maps.addInNewest (m :: rest) [(x, v)]) y = Maps.find? (m :: rest) y
    simp only [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push, Maps.find?]
    rcases Map.find?_append_singleton m [(x, v)] x v y rfl with ⟨h1, h2⟩ | h1
    · left; rw [h1]; exact ⟨rfl, h2⟩
    · right; rw [h1]

/-- When `Maps.find? ms x = none`, the newest scope also has `find? = none`. -/
theorem Maps.find?_none_newest [DecidableEq α]
    (ms : Maps α β) (x : α) (h : Maps.find? ms x = none) :
    Map.find? (Maps.newest ms) x = none := by
  match ms with
  | [] => simp [Maps.newest, Map.find?]
  | m :: rest =>
    simp only [Maps.newest]
    simp only [Maps.find?] at h
    split at h
    · assumption
    · exact absurd h (by simp)

/-- When the key is fresh (not found in any scope), `Maps.insert` equals `Maps.addInNewest`. -/
theorem Maps.insert_eq_addInNewest_fresh [DecidableEq α]
    (ms : Maps α β) (x : α) (v : β) (h : Maps.find? ms x = none) :
    Maps.insert ms x v = Maps.addInNewest ms [(x, v)] := by
  unfold Maps.insert
  simp [h]
  rw [Map.insert_fresh_eq_append _ _ _ (Maps.find?_none_newest ms x h)]
  unfold Maps.addInNewest
  rfl

/-- After erasing key `x` from all scopes, looking up `x` returns `none`. -/
theorem Maps.find?_erase_self [DecidableEq α]
    (ms : Maps α β) (x : α) :
    Maps.find? (Maps.erase ms x) x = none := by
  induction ms with
  | nil => simp [Maps.erase, Maps.find?]
  | cons m rest ih =>
    simp only [Maps.erase, Maps.find?, Map.find?_erase_self, ih]

/-- Erasing key `x` from all scopes does not affect lookups for `y ≠ x`. -/
theorem Maps.find?_erase_ne [DecidableEq α]
    (ms : Maps α β) (x y : α) (h_ne : y ≠ x) :
    Maps.find? (Maps.erase ms x) y = Maps.find? ms y := by
  induction ms with
  | nil => simp [Maps.erase, Maps.find?]
  | cons m rest ih =>
    simp only [Maps.erase, Maps.find?, Map.find?_erase_ne m x y h_ne, ih]

/-- Removing a key `k` from maps doesn't affect lookups of other keys `a ≠ k`. -/
theorem Maps.find?_remove_ne [DecidableEq α] [BEq (Map α β)]
    (ms : Maps α β) (k a : α) (h_ne : a ≠ k) :
    Maps.find? (Maps.remove ms k) a = Maps.find? ms a := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    simp only [Maps.remove]
    show Maps.find? (if Map.remove m k == m then m :: Maps.remove rest k
         else Map.remove m k :: Maps.remove rest k) a = _
    split
    · simp only [Maps.find?]; rw [ih]
    · simp only [Maps.find?]; rw [Map.find?_remove_ne m k a h_ne, ih]

theorem Maps.keys_erase_subset [DecidableEq α] (S : Maps α β) (x : α) :
    ∀ k, k ∈ Maps.keys (Maps.erase S x) → k ∈ Maps.keys S := by
  intro k hk; induction S with
  | nil => simp [Maps.erase, Maps.keys] at hk
  | cons scope rest ih =>
    simp only [Maps.erase, Maps.keys] at hk ⊢
    rcases List.mem_append.mp hk with h | h
    · exact List.mem_append_left _ (Map.keys_erase_subset scope x k h)
    · exact List.mem_append_right _ (ih h)

/-- Erasing key `a` from Maps `S` removes `a` from the keys. -/
theorem Maps.keys_erase_self_not_mem [DecidableEq α]
    (S : Maps α β) (a : α)
    (h : a ∈ Maps.keys (Maps.erase S a)) : False := by
  induction S with
  | nil => simp [Maps.erase, Maps.keys] at h
  | cons scope rest ih =>
    simp only [Maps.erase, Maps.keys] at h
    rcases List.mem_append.mp h with h_scope | h_rest
    · exact Map.keys_erase_self_not_mem scope a h_scope
    · exact ih h_rest

theorem Maps.values_erase_subset [DecidableEq α] (ms : Maps α β) (x : α) :
    ∀ v, v ∈ Maps.values (Maps.erase ms x) → v ∈ Maps.values ms := by
  induction ms with
  | nil => simp [Maps.erase, Maps.values]
  | cons scope rest ih =>
    intro v hv; simp only [Maps.erase, Maps.values] at hv ⊢
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_append_left _ (Map.values_erase_subset scope x v h)
    · exact List.mem_append_right _ (ih v h)

theorem Maps.keys_erase_mem_of_ne [DecidableEq α] {S : Maps α β} {a x : α}
    (h_key : a ∈ Maps.keys S) (h_ne : a ≠ x) :
    a ∈ Maps.keys (Maps.erase S x) := by
  induction S with
  | nil => simp [Maps.keys] at h_key
  | cons scope rest ih =>
    simp only [Maps.erase, Maps.keys] at h_key ⊢
    rcases List.mem_append.mp h_key with h | h
    · exact List.mem_append_left _ (Map.keys_erase_mem_of_ne scope h h_ne)
    · exact List.mem_append_right _ (ih h)

-- addInNewest on cons simplifies to appending to the first scope
theorem Maps.addInNewest_cons (scope : Map α β) (rest : Maps α β) (m : Map α β) :
    Maps.addInNewest (scope :: rest) m = (scope ++ m) :: rest := by
  simp [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]

/-- `Maps.findD` returns the default when `Maps.find?` is `none`. -/
theorem Maps.findD_find?_none [DecidableEq α]
    (ms : Maps α β) (x : α) (d : β)
    (h : Maps.find? ms x = none) :
    Maps.findD ms x d = d := by
  induction ms with
  | nil => simp [Maps.findD]
  | cons m rest ih =>
    simp only [Maps.find?, Maps.findD] at h ⊢
    split <;> simp_all

/-- `Maps.findD` returns the found value when `Maps.find?` is `some v`. -/
theorem Maps.findD_find?_some [DecidableEq α]
    (ms : Maps α β) (x : α) (d : β) (v : β)
    (h : Maps.find? ms x = some v) :
    Maps.findD ms x d = v := by
  induction ms with
  | nil => simp [Maps.find?] at h
  | cons m rest ih =>
    simp only [Maps.find?, Maps.findD] at h ⊢
    split <;> simp_all

/-- `Maps.find?` returning `some v` implies `(x, v)` is in `toSingleMap`. -/
theorem Maps.find?_mem_toSingleMap [DecidableEq α] (ms : Maps α β) (x : α) (v : β)
    (h : Maps.find? ms x = some v) : List.Mem (x, v) ms.toSingleMap := by
  induction ms with
  | nil => simp [Maps.find?] at h
  | cons m rest ih =>
    simp only [Maps.find?] at h
    simp only [Maps.toSingleMap, List.flatten]
    cases hf : Map.find? m x with
    | none => rw [hf] at h; exact List.mem_append_right _ (ih h)
    | some w =>
      rw [hf] at h; injection h with h; subst h
      exact List.mem_append_left _ (Map.find?_mem m x w hf)

/-- If `Maps.find?` returns `none`, then `Map.find?` on the flattened map also returns `none`. -/
theorem Maps.find?_none_toSingleMap [DecidableEq α]
    (ms : Maps α β) (x : α) (h : Maps.find? ms x = none) :
    Map.find? ms.toSingleMap x = none := by
  induction ms with
  | nil =>
    show Map.find? ([] : Maps α β).flatten x = none
    rfl
  | cons m rest ih =>
    simp only [Maps.find?] at h
    cases hm : Map.find? m x with
    | some v => rw [hm] at h; simp at h
    | none =>
      rw [hm] at h
      have ih_rest := ih h
      have hm_not_mem := Map.findNone_eq_notmem_mapfst.mpr hm
      have hr_not_mem := Map.findNone_eq_notmem_mapfst.mpr ih_rest
      apply Map.findNone_eq_notmem_mapfst.mp
      show ¬ x ∈ List.map Prod.fst ((m :: rest : Maps α β).flatten)
      grind

theorem Maps.find?_toSingleMap [DecidableEq α] (ms : Maps α β) (x : α) :
    Map.find? ms.toSingleMap x = Maps.find? ms x := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    unfold Map at m
    show Map.find? ((m ++ rest.flatten)) x = _
    rw [Map.find?_append]
    simp only [Maps.find?]
    cases Map.find? m x with
    | none => exact ih
    | some v => rfl

---------------------------------------------------------------------
end
