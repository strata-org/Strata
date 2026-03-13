import Lean.Elab.Term
import Lean.Data.Position
import Std.Data.HashMap.Lemmas

public section

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

---------------------------------------------------------------------
end



/-! ## Formalization of Mono- and Poly- Types in Lambda

We implement a Hindley-Milner type system for expressions in Lambda, which means
that we can infer the types of unannotated `LExpr`s. Note that at this time, we
do not have `let`s in `LExpr`, so we do not tackle let-polymorphism yet.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)


public section

/-- Type identifiers. For now, these are just strings. -/
@[expose] abbrev TyIdentifier := String

instance : Coe String TyIdentifier where
  coe := id

/-- Monomorphic types in Lambda. Note that all free type variables (`.ftvar`)
are implicitly universally quantified.  -/
inductive LMonoTy : Type where
  /-- A type variable. -/
  | ftvar (name : TyIdentifier)
  /-- A type constructor. -/
  | tcons (name : String) (args : List LMonoTy)
  /-- A bit vector type. This is a special case so that it can be parameterized
  by a size. -/
  | bitvec (size : Nat)
  deriving Inhabited, Repr

@[expose] abbrev LMonoTys := List LMonoTy

@[expose, match_pattern]
def LMonoTy.bool : LMonoTy :=
  .tcons "bool" []

@[expose, match_pattern]
def LMonoTy.int : LMonoTy :=
  .tcons "int" []

@[expose, match_pattern]
def LMonoTy.real : LMonoTy :=
  .tcons "real" []

@[expose, match_pattern]
def LMonoTy.bv1 : LMonoTy :=
  .bitvec 1

@[expose, match_pattern]
def LMonoTy.bv8 : LMonoTy :=
  .bitvec 8

@[expose, match_pattern]
def LMonoTy.bv16 : LMonoTy :=
  .bitvec 16

@[expose, match_pattern]
def LMonoTy.bv32 : LMonoTy :=
  .bitvec 32

@[expose, match_pattern]
def LMonoTy.bv64 : LMonoTy :=
  .bitvec 64

@[expose, match_pattern]
def LMonoTy.string : LMonoTy :=
  .tcons "string" []

def LMonoTy.arrow (t1 t2 : LMonoTy) : LMonoTy :=
  .tcons "arrow" [t1, t2]

def LMonoTy.mkArrow (mty : LMonoTy) (mtys : LMonoTys) : LMonoTy :=
  match mtys with
  | [] => mty
  | m :: mrest =>
    let mrest' := LMonoTy.mkArrow m mrest
    .arrow mty mrest'

/--
Create an iterated arrow type where `mty` is the return type
-/
def LMonoTy.mkArrow' (mty : LMonoTy) (mtys : LMonoTys) : LMonoTy :=
  match mtys with
  | [] => mty
  | m :: mrest => .arrow m (LMonoTy.mkArrow' mty mrest)

mutual
def LMonoTy.destructArrow (mty : LMonoTy) : LMonoTys :=
  match mty with
  | .tcons "arrow" (t1 :: trest) =>
    t1 :: LMonoTys.destructArrow trest
  | _ => [mty]

def LMonoTys.destructArrow (mtys : LMonoTys) : LMonoTys :=
  match mtys with
  | [] => []
  | mty :: mrest =>
    let mtys := LMonoTy.destructArrow mty
    let mrest_tys := LMonoTys.destructArrow mrest
    mtys ++ mrest_tys
end

theorem LMonoTy.destructArrow_non_empty (mty : LMonoTy) :
  (mty.destructArrow) ≠ [] := by
  unfold destructArrow; split <;> simp_all

def LMonoTy.getArrowArgs (t: LMonoTy) : List LMonoTy :=
  match t with
  | .arrow t1 t2 => t1 :: t2.getArrowArgs
  | _ => []

/--
Polymorphic type schemes in Lambda.
-/
inductive LTy : Type where
  /-- A type containing universally quantified type variables. -/
  | forAll (vars : List TyIdentifier) (ty : LMonoTy)
  deriving Inhabited, Repr

@[expose] abbrev LTys := List LTy

---------------------------------------------------------------------

/--
Induction rule for `LMonoTy`.

Lean's default `induction` tactic does not support nested or mutual inductive
types. So we define our own induction principle below.
-/
@[induction_eliminator]
theorem LMonoTy.induct {P : LMonoTy → Prop}
  (ftvar : ∀f, P (.ftvar f))
  (bitvec : ∀n, P (.bitvec n))
  (tcons : ∀name args, (∀ ty ∈ args, P ty) → P (.tcons name args)) :
  ∀ ty, P ty := by
  intro n
  apply LMonoTy.rec <;> try assumption
  case nil => simp
  case cons =>
    intro head tail h_head h_tail
    simp_all
  done

mutual
/--
Compute the size of `ty` as a tree.
-/
@[simp]
def LMonoTy.size (ty : LMonoTy) : Nat :=
  match ty with
  | .ftvar _ => 1
  | .tcons _ args => 1 + LMonoTys.size args
  | .bitvec _ => 1

@[simp]
def LMonoTys.size (args : LMonoTys) : Nat :=
    match args with
    | [] => 0
    | t :: rest => LMonoTy.size t + LMonoTys.size rest
end

theorem LMonoTy.size_gt_zero :
  0 < LMonoTy.size ty := by
  induction ty <;>  simp_all [LMonoTy.size]
  unfold LMonoTys.size; split
  simp_all; omega

theorem LMonoTy.size_lt_of_mem {ty: LMonoTy} {tys: LMonoTys} (h: ty ∈ tys):
  ty.size <= tys.size := by
  induction tys <;> simp only[LMonoTys.size]<;> grind

/--
Boolean equality for `LMonoTy`.
-/
def LMonoTy.BEq (x y : LMonoTy) : Bool :=
  match x, y with
  | .ftvar i, .ftvar j => i == j
  | .bitvec i, .bitvec j => i == j
  | .tcons i1 j1, .tcons i2 j2 =>
    i1 == i2 && j1.length == j2.length && go j1 j2
  | _, _ => false
  where go j1 j2 :=
  match j1, j2 with
  | [], _ => true
  | _, [] => true
  | x :: xrest, y :: yrest =>
    LMonoTy.BEq x y && go xrest yrest

@[simp]
theorem LMonoTy.BEq_refl : LMonoTy.BEq ty ty := by
  induction ty <;> simp_all [LMonoTy.BEq]
  rename_i name args ih
  induction args
  case tcons.nil => simp [LMonoTy.BEq.go]
  case tcons.cons =>
    rename_i head tail ih'
    simp_all [LMonoTy.BEq.go]
  done

instance : DecidableEq LMonoTy :=
  fun x y =>
    if h: LMonoTy.BEq x y then
      isTrue (by
                induction x generalizing y
                case ftvar =>
                  unfold LMonoTy.BEq at h <;> split at h <;> try simp_all
                case bitvec =>
                  unfold LMonoTy.BEq at h <;> split at h <;> try simp_all
                case tcons =>
                  rename_i name args ih
                  cases y <;> try simp_all [LMonoTy.BEq]
                  rename_i name' args'
                  obtain ⟨⟨h1, h2⟩, h3⟩ := h
                  induction args generalizing args'
                  case nil => unfold List.length at h2; split at h2 <;> simp_all
                  case cons head' tail' ih' =>
                    unfold LMonoTy.BEq.go at h3 <;> split at h3 <;> try simp_all
                    rename_i j1 j2 x xrest y yrest heq
                    obtain ⟨h3_1, h3_2⟩ := h3
                    obtain ⟨ih1, ih2⟩ := ih
                    exact ⟨ih1 y h3_1, ih' ih2 yrest h3_2 rfl⟩)
    else
      isFalse (by induction x generalizing y
                  case ftvar =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                  case bitvec n =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                  case tcons name args ih =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                    rename_i name' args'
                    intro hname; simp [hname] at h
                    induction args generalizing args'
                    case tcons.nil =>
                      simp [LMonoTy.BEq.go] at h
                      unfold List.length at h; split at h <;> simp_all
                    case tcons.cons head tail ih' =>
                      cases args' <;> try simp_all
                      rename_i head' tail'; intro _
                      have ih'' := @ih' tail'
                      unfold LMonoTy.BEq.go at h
                      simp_all)

instance : Inhabited LMonoTy where
  default := .tcons "bool" []

instance : ToString LTy where
  toString x := toString (repr x)

mutual
/--
Get the free type variables in monotype `mty`, which are simply the `.ftvar`s in
it.
-/
def LMonoTy.freeVars (mty : LMonoTy) : List TyIdentifier :=
  match mty with
  | .ftvar x => [x]
  | .bitvec _ => []
  | .tcons _ ltys => LMonoTys.freeVars ltys

/--
Get the free type variables in monotypes `mtys`, which are simply the `.ftvar`s
in them.
-/
def LMonoTys.freeVars (mtys : LMonoTys) : List TyIdentifier :=
    match mtys with
    | [] => [] | ty :: rest => LMonoTy.freeVars ty ++ LMonoTys.freeVars rest
end

@[simp]
theorem LMonoTys.freeVars_of_cons :
  LMonoTys.freeVars (x :: xs) = LMonoTy.freeVars x ++ LMonoTys.freeVars xs := by
  simp_all [LMonoTys.freeVars]

/--
Get all type constructors in monotype `mty`.
-/
def LMonoTy.getTyConstructors (mty : LMonoTy) : List LMonoTy :=
  match mty with
  | .ftvar _ => []
  | .bitvec _ => []
  | .tcons name mtys =>
    let typeargs :=  List.replicate mtys.length "_dummy"
    let args := typeargs.mapIdx (fun i elem => LMonoTy.ftvar (elem ++ toString i))
    let mty := .tcons name args
    let ans := mty :: go mtys
    ans.eraseDups
  where go mtys :=
  match mtys with
  | [] => [] | m :: mrest => LMonoTy.getTyConstructors m ++ go mrest

---------------------------------------------------------------------

/--
Boolean equality for `LTy`.
-/
def LTy.BEq (x y : LTy) : Bool :=
  match x, y with
  | .forAll xs xlty, .forAll ys ylty =>
    xs == ys && xlty == ylty

instance : DecidableEq LTy :=
  fun x y =>
    if h: LTy.BEq x y then
      isTrue (by
                unfold LTy.BEq at h
                split at h <;> simp_all)
    else
      isFalse (by
                unfold LTy.BEq at h
                split at h <;> simp_all)

/--
Get the free type variables in type scheme `ty`, which are all the unbound
`.ftvar`s in it.
-/
def LTy.freeVars (ty : LTy) : List TyIdentifier :=
  match ty with
  | .forAll xs lty => let lfv := LMonoTy.freeVars lty
                      lfv.removeAll xs

/--
Get the bound type variables in a type scheme.
-/
def LTy.boundVars (sch : LTy) : List TyIdentifier :=
  match sch with
  | .forAll xs _ => xs

/--
A type scheme `ty` is a mono-type if there are no bound variables.
-/
def LTy.isMonoType (ty : LTy) : Bool :=
  ty.boundVars.isEmpty

/--
Obtain a mono-type from a type scheme `ty`.
-/
def LTy.toMonoType (ty : LTy) (h : LTy.isMonoType ty) : LMonoTy :=
  match ty with
  | .forAll _ lty => lty

/--
Optionally obtain a mono-type from a type scheme `ty`.
-/
def LTy.toMonoType? (ty : LTy) : Option LMonoTy :=
  match ty with
  | .forAll [] lty => .some lty
  | _ => .none

/--
Unsafe coerce from a type scheme to a mono-type.
-/
def LTy.toMonoTypeUnsafe (ty : LTy) : LMonoTy :=
  match ty with
  | .forAll _ lty => lty

---------------------------------------------------------------------

/- Formatting and Parsing -/

instance : ToString LMonoTy where
  toString x := toString (repr x)

private def formatLMonoTy (lmonoty : LMonoTy) : Format :=
  match lmonoty with
  | .ftvar x => toString x
  | .bitvec n => f!"bv{n}"
  | .tcons name tys =>
    if tys.isEmpty then
      f!"{name}"
    else
      let args := (Std.Format.joinSep (tys.map formatLMonoTy) (" "))
      Std.Format.paren (name ++ " " ++ args)

instance : ToFormat LMonoTy where
  format := private formatLMonoTy

instance : ToFormat LTy where
  format ty := match ty with
  | .forAll names lmonoty =>
    if names.isEmpty then f!"{lmonoty}"
    else f!"∀{names}. {lmonoty}"


namespace LTy

/- Syntax for conveniently building `LMonoTy` and `LTy` terms, scoped under the
namespace `LMonoTy.Syntax`. -/
namespace Syntax

/-
NOTE: %<ident> is elaborated to type variables. <ident> is elaborated to a
`tcons` constructor's name.
-/

declare_syntax_cat lmonoty

declare_syntax_cat ftvar
scoped syntax "%" noWs ident : ftvar
scoped syntax ftvar : lmonoty

declare_syntax_cat tcons
declare_syntax_cat tident
scoped syntax ident : tident
scoped syntax tident (lmonoty)* : tcons
scoped syntax tcons : lmonoty
-- Special handling for function types.
scoped syntax:65 lmonoty:66 "→" lmonoty:65 : lmonoty
-- Special handling for bool and int types.
declare_syntax_cat tprim
scoped syntax "int" : tprim
scoped syntax "bool" : tprim
scoped syntax tprim : tcons

scoped syntax "(" lmonoty ")" : lmonoty

open Lean Elab Meta in
meta partial def elabLMonoTy : Lean.Syntax → MetaM Expr
  | `(lmonoty| %$f:ident) => do
     mkAppM ``LMonoTy.ftvar #[mkStrLit (toString f.getId)]
  | `(lmonoty| $ty1:lmonoty → $ty2:lmonoty) => do
     let ty1' ← elabLMonoTy ty1
     let ty2' ← elabLMonoTy ty2
     let tys ← mkListLit (mkConst ``LMonoTy) [ty1', ty2']
     mkAppM ``LMonoTy.tcons #[(mkStrLit "arrow"), tys]
  | `(lmonoty| int) => do
    let argslist ← mkListLit (mkConst ``LMonoTy) []
    mkAppM ``LMonoTy.tcons #[(mkStrLit "int"), argslist]
  | `(lmonoty| bool) => do
    let argslist ← mkListLit (mkConst ``LMonoTy) []
    mkAppM ``LMonoTy.tcons #[(mkStrLit "bool"), argslist]
  | `(lmonoty| bv1) =>  mkAppM ``LMonoTy.bv1 #[]
  | `(lmonoty| bv8) =>  mkAppM ``LMonoTy.bv8 #[]
  | `(lmonoty| bv16) => mkAppM ``LMonoTy.bv16 #[]
  | `(lmonoty| bv32) => mkAppM ``LMonoTy.bv32 #[]
  | `(lmonoty| bv64) => mkAppM ``LMonoTy.bv64 #[]
  | `(lmonoty| $i:ident $args:lmonoty*) => do
    let args' ← go args
    let argslist ← mkListLit (mkConst ``LMonoTy) args'.toList
    mkAppM ``LMonoTy.tcons #[(mkStrLit (toString i.getId)), argslist]
  | `(lmonoty| ($ty:lmonoty)) => elabLMonoTy ty
  | _ => throwUnsupportedSyntax
  where go (args : TSyntaxArray `lmonoty) : MetaM (Array Expr) := do
    let mut arr := #[]
    for a in args do
      let a' ← elabLMonoTy a
      arr := arr.push a'
    return arr

elab "mty[" ty:lmonoty "]" : term => elabLMonoTy ty

declare_syntax_cat lty
scoped syntax (lmonoty)* : lty
scoped syntax "∀" (ident)* "." (lmonoty)* : lty
scoped syntax "(" lty ")" : lty

open Lean Elab Meta in
meta partial def elabLTy : Lean.Syntax → MetaM Expr
  | `(lty| ∀ $vars:ident* . $ty:lmonoty) => do
      let vars' := List.map (fun f => mkStrLit (toString f.getId)) vars.toList
      let varslist ← mkListLit (mkConst ``String) vars'
      let ty' ← elabLMonoTy ty
      mkAppM ``LTy.forAll #[varslist, ty']
  | `(lty| $ty:lmonoty) => do
      let emptylist ← mkListLit (mkConst ``String) []
      let ty' ← elabLMonoTy ty
      mkAppM ``LTy.forAll #[emptylist, ty']
  | `(lty| ($ty:lty)) => elabLTy ty
  | _ => throwUnsupportedSyntax

elab "t[" lsch:lty "]" : term => elabLTy lsch

end Syntax
end LTy

---------------------------------------------------------------------

open LTy.Syntax

def LMonoTy.inputArity (ty : LMonoTy) : Nat :=
  match ty with
  | .tcons "arrow" (_a :: rest) => 1 + go rest
  | _ => 0
  where go args :=
  match args with
  | [] => 0
  | a :: arest => inputArity a + go arest

def LTy.inputArity (ty : LTy) : Nat :=
  match ty with
  | .forAll _ mty => mty.inputArity

def LMonoTy.inputTypes (ty : LMonoTy) : List LMonoTy :=
  match ty with
  | .tcons "arrow" (a :: rest) => a :: go rest
  | _ => []
  where go args :=
  match args with
  | [] => []
  | a :: arest => inputTypes a ++ go arest

---------------------------------------------------------------------

/--
Close `ty` by `x`, i.e., add `x` as a bound type variable.
-/
def LTy.close (x : TyIdentifier) (ty : LTy) : LTy :=
  match ty with
  | .forAll vars lty => .forAll (x :: vars) lty

end -- public section
end Lambda

public section
namespace Strata

/--
Source location information in the DDM is defined
by a range of bytes in a UTF-8 string with the input
Line/column information can be constructed from a
`Lean.FileMap`

As an example, in the string `"123abc\ndef"`, the string
`"abc"` has the position `{start := 3, stop := 6 }` while
`"def"` has the position `{start := 7, stop := 10 }`.
-/
structure SourceRange where
  /-- The starting offset of the source range. -/
  start : String.Pos.Raw
  /-- One past the end of the range. -/
  stop : String.Pos.Raw
deriving DecidableEq, Inhabited, Repr

namespace SourceRange

def none : SourceRange := { start := 0, stop := 0 }

def isNone (loc : SourceRange) : Bool := loc.start = 0 ∧ loc.stop = 0

instance : Std.ToFormat SourceRange where
 format fr := f!"{fr.start}-{fr.stop}"

/-- Format a SourceRange as a string using a FileMap for line:column conversion.
    Renders location information in a format VSCode understands.
    Returns "path:line:col-col" if on same line, otherwise "path:line:col". -/
def format (loc : SourceRange) (path : System.FilePath) (fm : Lean.FileMap) : String :=
  let spos := fm.toPosition loc.start
  let epos := fm.toPosition loc.stop
  if spos.line == epos.line then
    s!"{path}:{spos.line}:{spos.column+1}-{epos.column+1}"
  else
    s!"{path}:{spos.line}:{spos.column+1}"

end Strata.SourceRange
end

open Std (Format)

public section
namespace Strata

inductive Uri where
  | file (path: String)
  deriving DecidableEq, Repr, Inhabited

instance : Std.ToFormat Uri where
 format fr := private match fr with | .file path => path

structure FileRange where
  file: Uri
  range: SourceRange
  deriving DecidableEq, Repr, Inhabited

instance : Std.ToFormat FileRange where
 format fr := private f!"{fr.file}:{fr.range}"

structure File2dRange where
  file: Uri
  start: Lean.Position
  ending: Lean.Position
  deriving DecidableEq, Repr

instance : Std.ToFormat File2dRange where
 format fr := private
    let baseName := match fr.file with
                    | .file path => (path.splitToList (· == '/')).getLast!
    f!"{baseName}({fr.start.line}, {fr.start.column})-({fr.ending.line}, {fr.ending.column})"

instance : Std.ToFormat FileRange where
 format fr := f!"{fr.file}:{fr.range}"

/-- A default file range for errors without source location.
This should only be used for generated nodes that are guaranteed to be correct. -/
def FileRange.unknown : FileRange :=
  { file := .file "<unknown>", range := SourceRange.none }

/-- Format a file range using a FileMap to convert byte offsets to line/column positions. -/
def FileRange.format (fr : FileRange) (fileMap : Option Lean.FileMap) (includeEnd? : Bool := true) : Std.Format :=
  let baseName := match fr.file with
                  | .file path => (path.splitToList (· == '/')).getLast!
  match fileMap with
  | some fm =>
    -- Lean's InputContext may have a fileMap which has an empty source and
    -- position. This can happen when InputContext is assigned Inhabited.default.
    if fm.source.isEmpty ∧ fm.positions.isEmpty then f!"" else
    let startPos := fm.toPosition fr.range.start
    let endPos := fm.toPosition fr.range.stop
    if includeEnd? then
      if startPos.line == endPos.line then
        f!"{baseName}({startPos.line},({startPos.column}-{endPos.column}))"
      else
        f!"{baseName}(({startPos.line},{startPos.column})-({endPos.line},{endPos.column}))"
    else
      f!"{baseName}({startPos.line}, {startPos.column})"
  | none =>
    if fr.range.isNone then
      f!""
    else
      f!"{baseName}({fr.range.start}-{fr.range.stop})"

/-- A diagnostic model that holds a file range and a message.
    This can be converted to a formatted string using a FileMap. -/
structure DiagnosticModel where
  fileRange : FileRange
  message : String
  deriving Repr, BEq, Inhabited

instance : Inhabited DiagnosticModel where
  default := { fileRange := FileRange.unknown, message := "" }

/-- Create a DiagnosticModel from just a message (using default location).
This should not be called, it only exists temporarily to enable incrementally
migrating code without error locations -/
def DiagnosticModel.fromMessage (msg : String) : DiagnosticModel :=
  { fileRange := FileRange.unknown, message := msg }

/-- Create a DiagnosticModel from a Format (using default location).
This should not be called, it only exists temporarily to enable incrementally
migrating code without error locations -/
def DiagnosticModel.fromFormat (fmt : Std.Format) : DiagnosticModel :=
  { fileRange := FileRange.unknown, message := toString fmt }

/-- Create a DiagnosticModel with source location. -/
def DiagnosticModel.withRange (fr : FileRange) (msg : Format) : DiagnosticModel :=
  { fileRange := fr, message := toString msg }

/-- Format a DiagnosticModel using a FileMap to convert byte offsets to line/column positions. -/
def DiagnosticModel.format (dm : DiagnosticModel) (fileMap : Option Lean.FileMap) (includeEnd? : Bool := true) : Std.Format :=
  let rangeStr := dm.fileRange.format fileMap includeEnd?
  if dm.fileRange.range.isNone then
    f!"{dm.message}"
  else
    f!"{rangeStr} {dm.message}"

/-- Format just the file range portion of a DiagnosticModel. -/
def DiagnosticModel.formatRange (dm : DiagnosticModel) (fileMap : Option Lean.FileMap) (includeEnd? : Bool := true) : Std.Format :=
  dm.fileRange.format fileMap includeEnd?

/-- Update the file range of a DiagnosticModel if it's currently unknown.
This should not be called, it only exists temporarily to enable incrementally
migrating code without error locations -/
def DiagnosticModel.withRangeIfUnknown (dm : DiagnosticModel) (fr : FileRange) : DiagnosticModel :=
  if dm.fileRange.range.isNone then
    { dm with fileRange := fr }
  else
    dm

instance : ToString DiagnosticModel where
  toString dm := dm.format none |> toString

end Strata
end


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
For an informative error message, takes in a `DiagnosticModel`
-/
def Identifiers.addWithError {IDMeta} (m: Identifiers IDMeta) (x: Identifier IDMeta) (f: DiagnosticModel) : Except DiagnosticModel (Identifiers IDMeta) :=
  let (b, m') := m.containsThenInsertIfNew x.name x.metadata
  if b then .error f else .ok m'

def Identifiers.addListWithError {IDMeta} (m: Identifiers IDMeta) (x: List (Identifier IDMeta)) (f: Identifier IDMeta → DiagnosticModel) :=
  x.foldlM (fun m x => Identifiers.addWithError m x (f x)) m

def Identifiers.add {IDMeta} (m: Identifiers IDMeta) (x: Identifier IDMeta) : Except DiagnosticModel (Identifiers IDMeta) :=
  m.addWithError x <| DiagnosticModel.fromFormat f!"Error: duplicate identifier {x.name}"

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

theorem Identifiers.addListWithErrorNotin {IDMeta} [DecidableEq IDMeta]
  {m m': Identifiers IDMeta} {l: List (Identifier IDMeta)} {f: Identifier IDMeta → DiagnosticModel}:
  m.addListWithError l f = .ok m' → forall x, x ∈ l → m.contains x = false := by
  unfold addListWithError
  induction l generalizing m m' with
  | nil => simp
  | cons h t IH =>
    simp only[List.foldlM, bind, Except.bind]
    split <;> intros Hid; try contradiction
    intros x
    rw[List.mem_cons]
    rename_i Heq
    have Hin := Identifiers.addWithErrorNotin Heq
    have := addWithErrorContains Heq x; grind

theorem Identifiers.addListWithErrorContains {IDMeta} [DecidableEq IDMeta]
  {m m': Identifiers IDMeta} {l: List (Identifier IDMeta)} {f: Identifier IDMeta → DiagnosticModel}: m.addListWithError l f = .ok m' → ∀ y, m'.contains y ↔ y ∈ l ∨ m.contains y := by
  unfold addListWithError
  induction l generalizing m m' with
  | nil => simp; intros Heq; cases Heq; grind
  | cons h t IH =>
    simp only[List.foldlM, bind, Except.bind]
    split <;> intros Hid; try contradiction
    intros x
    rw[List.mem_cons]
    rename_i Heq
    have Hcont := Identifiers.addWithErrorContains Heq x
    have Hin := Identifiers.addWithErrorNotin Heq
    grind

theorem Identifiers.addListWithErrorNoDup {IDMeta} [DecidableEq IDMeta]
  {m m': Identifiers IDMeta} {l: List (Identifier IDMeta)} {f: Identifier IDMeta → DiagnosticModel}: m.addListWithError l f = .ok m' → l.Nodup := by
  unfold addListWithError
  induction l generalizing m m' with
  | nil => simp
  | cons h t IH =>
    simp only[List.foldlM, bind, Except.bind]
    split <;> intros Hid; try contradiction
    apply List.nodup_cons.mpr
    constructor <;> try grind
    intros h_in_t
    rename_i Hadd
    have := Identifiers.addWithErrorContains Hadd h
    have := Identifiers.addListWithErrorNotin Hid h
    grind

instance [ToFormat IDMeta] : ToFormat (Identifiers IDMeta) where
  format m := format (m.toList)

---------------------------------------------------------------------

end -- public section
end Lambda

public section
namespace Lambda
/--
Metadata annotations.

[Stopgap] We will eventually design a structured metadata language that we will
modify along with our code transformation functions.
-/
structure Info where
  value : String
  deriving DecidableEq, Repr

end Lambda
end

public section

def beq_eq_DecidableEq
  {T : Type}
  (beq : T → T → Bool)
  (beq_eq : (x1 x2 : T) → beq x1 x2 = true ↔ x1 = x2) :
  DecidableEq T :=
  fun x1 x2 =>
    let eq := beq_eq x1 x2
    if h: beq x1 x2 then
      isTrue (eq.mp h)
    else
      isFalse (fun heq => h (eq.mpr heq))

/--
Solves goals of the form `beq e1 e2 = true ↔ e1 = e2` if `beq` is
marked with `@[grind]`.
-/
syntax "solve_beq" ident ident  : tactic
macro_rules
  | `(tactic|solve_beq $e1:ident $e2:ident) =>
  `(tactic|
    constructor <;> intro h <;>
    try (induction $e1:ident generalizing $e2 <;> cases $e2:ident <;> grind) <;>
    (subst_vars; induction $e2:ident <;> grind)
  )
end


/-! ## Lambda Expressions with Quantifiers

Lambda expressions are formalized by the inductive type `LExpr`. Type
formalization is described in `Strata.DL.Lambda.LTy`.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

public section

inductive QuantifierKind
  | all
  | exist
  deriving Repr, DecidableEq

/-
Traceable class for combining multiple metadata with labeled provenance.

Takes a list of (reason, metadata) pairs and combines them into a single metadata.
Each pair describes why that metadata is being included in the combination.

Usage:
  Traceable.combine [("function", fnMeta), ("argument", argMeta), ("context", ctxMeta)]
-/
class Traceable (Reason: Type) (Metadata : Type) where
  combine : List (Reason × Metadata) → Metadata

/--
Expected interface for pure expressions that can be used to specialize the
Imperative dialect.
-/
structure LExprParams : Type 1 where
  /-- The type of metadata allowed on expressions. -/
  Metadata: Type
  /-- The type of metadata allowed on identifiers. -/
  IDMeta : Type
  deriving Inhabited

/--
Extended LExprParams that includes TypeType parameter.
-/
structure LExprParamsT : Type 1 where
  /-- The base parameters, with the types for expression and identifier metadata. -/
  base : LExprParams
  /-- The type of types used to annotate expressions. -/
  TypeType : Type
  deriving Inhabited

/--
Dot notation syntax: T.mono transforms LExprParams into LExprParamsT with LMonoTy.
-/
@[expose] abbrev LExprParams.mono (T : LExprParams) : LExprParamsT :=
  ⟨T, LMonoTy⟩

@[expose] abbrev LExprParams.Identifier (T : LExprParams) := Lambda.Identifier T.IDMeta

structure Typed (T: Type) where
  underlying: T
  type: LMonoTy

-- Metadata annotated with a type
@[expose] abbrev LExprParams.typed (T: LExprParams): LExprParams :=
  ⟨ Typed T.Metadata, T.IDMeta ⟩

@[expose] abbrev LExprParamsT.typed (T: LExprParamsT): LExprParamsT :=
  ⟨T.base.typed, LMonoTy⟩

/--
Lambda constants.

Constants are integers, strings, reals, bitvectors of a fixed length, or
booleans.
-/
inductive LConst : Type where
  /-- An unbounded integer constant. -/
  | intConst (i: Int)

  /-- A string constant, using Lean's `String` type for a sequence of Unicode
  code points encoded with UTF-8. -/
  | strConst (s: String)

  /-- A real constant, represented as a rational number. -/
  | realConst (r: Rat)

  /-- A bit vector constant, represented using Lean's `BitVec` type. -/
  | bitvecConst (n: Nat) (b: BitVec n)

  /-- A Boolean constant. -/
  | boolConst (b: Bool)
deriving Repr, DecidableEq

/--
Lambda expressions with quantifiers.

Like Lean's own expressions, we use the locally nameless
representation for this abstract syntax.
See this [paper](https://chargueraud.org/research/2009/ln/main.pdf)
for details.

We leave placeholders for type annotations only for constants
(`.const`), operations (`.op`), binders (`.abs`, `.quant`), and free
variables (`.fvar`).

LExpr is parameterized by `LExprParamsT`, which includes arbitrary metadata,
user-allowed type annotations (optional), and special metadata to attach to
`Identifier`s. Type inference adds any missing type annotations.
-/
inductive LExpr (T : LExprParamsT) : Type where
  /-- A constant (in the sense of literals). -/
  | const   (m: T.base.Metadata) (c: LConst)
  /-- A built-in operation, referred to by name. -/
  | op      (m: T.base.Metadata) (o : Identifier T.base.IDMeta) (ty : Option T.TypeType)
  /-- A bound variable, in de Bruijn form. -/
  | bvar    (m: T.base.Metadata) (deBruijnIndex : Nat)
  /-- A free variable, with an optional type annotation. -/
  | fvar    (m: T.base.Metadata) (name : Identifier T.base.IDMeta) (ty : Option T.TypeType)
  /-- An abstraction, where `prettyName` is a display name (empty string if none provided) and `ty` is the (optional) type of bound variable. -/
  | abs     (m: T.base.Metadata) (prettyName : String) (ty : Option T.TypeType) (e : LExpr T)
  /-- A quantified expression, where `k` indicates whether it is universally or
  existentially quantified, `prettyName` is a display name (empty string if none provided) and `ty` is the type of bound variable; `trigger` is
  a trigger pattern (primarily for use with SMT). -/
  | quant   (m: T.base.Metadata) (k : QuantifierKind) (prettyName : String) (ty : Option T.TypeType) (trigger: LExpr T) (e : LExpr T)
  /-- A function application. -/
  | app     (m: T.base.Metadata) (fn e : LExpr T)
  /-- A conditional expression. This is a constructor rather than a built-in
  operation because it occurs so frequently. -/
  | ite     (m: T.base.Metadata) (c t e : LExpr T)
  /-- An equality expression. This is a constructor rather than a built-in
  operation because it occurs so frequently. -/
  | eq      (m: T.base.Metadata) (e1 e2 : LExpr T)

instance [Repr T.base.Metadata] [Repr T.TypeType] [Repr T.base.IDMeta] : Repr (LExpr T) where
  reprPrec e prec :=
    let rec go : LExpr T → Std.Format
      | .const m c =>
        f!"LExpr.const {repr m} {repr c}"
      | .op m o ty =>
        match ty with
        | none => f!"LExpr.op {repr m} {repr o} none"
        | some ty => f!"LExpr.op {repr m} {repr o} (some {repr ty})"
      | .bvar m i => f!"LExpr.bvar {repr m} {repr i}"
      | .fvar m name ty =>
        match ty with
        | none => f!"LExpr.fvar {repr m} {repr name} none"
        | some ty => f!"LExpr.fvar {repr m} {repr name} (some {repr ty})"
      | .abs m name ty e =>
        match ty with
        | none => f!"LExpr.abs {repr m} {repr name} none ({go e})"
        | some ty => f!"LExpr.abs {repr m} {repr name} (some {repr ty}) ({go e})"
      | .quant m k name ty tr e =>
        let kindStr := match k with | .all => "QuantifierKind.all" | .exist => "QuantifierKind.exist"
        match ty with
        | none => f!"LExpr.quant {repr m} {kindStr} {repr name} none ({go tr}) ({go e})"
        | some ty => f!"LExpr.quant {repr m} {kindStr} {repr name} (some {repr ty}) ({go tr}) ({go e})"
      | .app m fn e => f!"LExpr.app {repr m} ({go fn}) ({go e})"
      | .ite m c t e => f!"LExpr.ite {repr m} ({go c}) ({go t}) ({go e})"
      | .eq m e1 e2 => f!"LExpr.eq {repr m} ({go e1}) ({go e2})"
    if prec > 0 then Std.Format.paren (go e) else go e

-- Boolean equality function for LExpr
@[grind]
def LExpr.beq [BEq T.base.Metadata] [BEq T.TypeType] [BEq (Identifier T.base.IDMeta)] : LExpr T → LExpr T → Bool
  | .const m1 c1, e2 =>
    match e2 with
    | .const m2 c2 => m1 == m2 && c1 == c2
    | _ => false
  | .op m1 o1 ty1, e2 =>
    match e2 with
    | .op m2 o2 ty2 => m1 == m2 && o1 == o2 && ty1 == ty2
    | _ => false
  | .bvar m1 i1, e2 =>
    match e2 with
    | .bvar m2 i2 => m1 == m2 && i1 == i2
    | _ => false
  | .fvar m1 n1 ty1, e2 =>
    match e2 with
    | .fvar m2 n2 ty2 => m1 == m2 && n1 == n2 && ty1 == ty2
    | _ => false
  | .abs m1 name1 ty1 e1', e2 =>
    match e2 with
    | .abs m2 name2 ty2 e2' => m1 == m2 && name1 == name2 && ty1 == ty2 && LExpr.beq e1' e2'
    | _ => false
  | .quant m1 k1 name1 ty1 tr1 e1', e2 =>
    match e2 with
    | .quant m2 k2 name2 ty2 tr2 e2' =>
      m1 == m2 && k1 == k2 && name1 == name2 && ty1 == ty2 && LExpr.beq tr1 tr2 && LExpr.beq e1' e2'
    | _ => false
  | .app m1 fn1 e1', e2 =>
    match e2 with
    | .app m2 fn2 e2' => m1 == m2 && LExpr.beq fn1 fn2 && LExpr.beq e1' e2'
    | _ => false
  | .ite m1 c1 t1 e1', e2 =>
    match e2 with
    | .ite m2 c2 t2 e2' =>
      m1 == m2 && LExpr.beq c1 c2 && LExpr.beq t1 t2 && LExpr.beq e1' e2'
    | _ => false
  | .eq m1 e1a e1b, e2 =>
    match e2 with
    | .eq m2 e2a e2b => m1 == m2 && LExpr.beq e1a e2a && LExpr.beq e1b e2b
    | _ => false

instance [BEq T.base.Metadata] [BEq T.TypeType] [BEq (Identifier T.base.IDMeta)] : BEq (LExpr T) where
  beq := LExpr.beq

-- First, prove that beq is sound and complete
theorem LExpr.beq_eq {T : LExprParamsT} [DecidableEq T.base.Metadata] [DecidableEq T.TypeType] [DecidableEq T.base.IDMeta]
  (e1 e2 : LExpr T) : LExpr.beq e1 e2 = true ↔ e1 = e2 := by
  solve_beq e1 e2

-- Now use this theorem in DecidableEq
instance {T: LExprParamsT} [DecidableEq T.base.Metadata] [DecidableEq T.TypeType] [DecidableEq T.base.IDMeta] : DecidableEq (LExpr T) :=
  fun e1 e2 =>
    if h : LExpr.beq e1 e2 then
      isTrue (LExpr.beq_eq e1 e2 |>.mp h)
    else
      isFalse (fun heq => h (LExpr.beq_eq e1 e2 |>.mpr heq))

def LExpr.noTrigger {T : LExprParamsT} (m : T.base.Metadata) : LExpr T := .bvar m 0
def LExpr.allTr {T : LExprParamsT} (m : T.base.Metadata) (name : String) (ty : Option T.TypeType) := @LExpr.quant T m .all name ty
def LExpr.all {T : LExprParamsT} (m : T.base.Metadata) (name : String) (ty : Option T.TypeType) := @LExpr.quant T m .all name ty (LExpr.noTrigger m)
def LExpr.existTr {T : LExprParamsT} (m : T.base.Metadata) (name : String) (ty : Option T.TypeType) := @LExpr.quant T m .exist name ty
def LExpr.exist {T : LExprParamsT} (m : T.base.Metadata) (name : String) (ty : Option T.TypeType) := @LExpr.quant T m .exist name ty (LExpr.noTrigger m)

@[expose, match_pattern]
def LExpr.intConst (m : T.base.Metadata) (n: Int) : LExpr T := .const m <| LConst.intConst n
@[expose, match_pattern]
def LExpr.strConst (m : T.base.Metadata) (s: String) : LExpr T := .const m <| LConst.strConst s
@[expose, match_pattern]
def LExpr.realConst (m : T.base.Metadata) (r: Rat) : LExpr T := .const m <| LConst.realConst r
@[expose, match_pattern]
def LExpr.bitvecConst (m : T.base.Metadata) (n: Nat) (b: BitVec n) : LExpr T := .const m <| LConst.bitvecConst n b
@[expose, match_pattern]
def LExpr.boolConst (m : T.base.Metadata) (b: Bool) : LExpr T := .const m <| LConst.boolConst b

abbrev LExpr.absUntyped {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.abs T m ""  .none
abbrev LExpr.allUntypedTr {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .all "" .none
abbrev LExpr.allUntyped {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .all "" .none (LExpr.noTrigger m)
abbrev LExpr.existUntypedTr {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .exist "" .none
abbrev LExpr.existUntyped {T : LExprParamsT} (m : T.base.Metadata) := @LExpr.quant T m .exist "" .none (LExpr.noTrigger m)

@[simp]
def LExpr.sizeOf: LExpr T → Nat
  | LExpr.abs _ _ _ e => 2 + sizeOf e
  | LExpr.quant _ _ _ _ tr e => 3 + sizeOf e + sizeOf tr
  | LExpr.app _ fn e => 3 + sizeOf fn + sizeOf e
  | LExpr.ite _ c t e => 4 + sizeOf c + sizeOf t + sizeOf e
  | LExpr.eq _ e1 e2 => 3 + sizeOf e1 + sizeOf e2
  | _ => 1

/--
Get type of a constant `c`
-/
def LConst.ty (c: LConst) : LMonoTy :=
  match c with
  | .intConst _ => .int
  | .strConst _ => .string
  | .bitvecConst n _ => .bitvec n
  | .realConst _ => .real
  | .boolConst _ => .bool

/--
Get type name of a constant `c` (e.g. "int")
-/
def LConst.tyName (c: LConst) : String :=
  match c with
  | .intConst _ => "int"
  | .strConst _ => "string"
  | .bitvecConst _ _ => "bitvec"
  | .realConst _ => "real"
  | .boolConst _ => "bool"

/--
Get type name of a constant `c` as a Format (e.g. "Integers")
-/
def LConst.tyNameFormat (c: LConst) : Format :=
  match c with
  | .intConst _ => f!"Integers"
  | .strConst _ => f!"Strings"
  | .bitvecConst n _ => f!"Bit vectors of size {n}"
  | .realConst _ => f!"Reals"
  | .boolConst _ => f!"Booleans"

---------------------------------------------------------------------

namespace LExpr

instance (T : LExprParamsT) [Inhabited T.base.Metadata] : Inhabited (LExpr T) where
  default := .boolConst default false

def LExpr.getVars (e : LExpr T) : List (Identifier T.base.IDMeta) := match e with
  | .const _ _ => [] | .bvar _ _ => [] | .op _ _ _ => []
  | .fvar _ y _ => [y]
  | .abs _ _ _ e' => LExpr.getVars e'
  | .quant _ _ _ _ tr' e' => LExpr.getVars tr' ++ LExpr.getVars e'
  | .app _ e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2
  | .ite _ c t e => LExpr.getVars c ++ LExpr.getVars t ++ LExpr.getVars e
  | .eq _ e1 e2 => LExpr.getVars e1 ++ LExpr.getVars e2

def getOps (e : LExpr T) := match e with
  | .op _ name _ => [name]
  | .const _ _ => [] | .bvar _ _ => [] | .fvar _ _ _ => []
  | .abs _ _ _ e' => getOps e'
  | .quant _ _ _ _ tr e' =>
    -- NOTE: We also get all ops in the triggers here.
    getOps tr ++ getOps e'
  | .app _ e1 e2 => getOps e1 ++ getOps e2
  | .ite _ c t e => getOps c ++ getOps t ++ getOps e
  | .eq _ e1 e2 => getOps e1 ++ getOps e2

def getFVarName? {T : LExprParamsT} (e : LExpr T) : Option (Identifier T.base.IDMeta) :=
  match e with
  | .fvar _ name _ => some name
  | _ => none

/-- Collect all free variable identifiers in an expression. -/
def collectFvarNames {T : LExprParamsT} : LExpr T → List (Identifier T.base.IDMeta)
  | .fvar _ name _ => [name]
  | .abs _ _ _ e => collectFvarNames e
  | .quant _ _ _ _ tr e => collectFvarNames tr ++ collectFvarNames e
  | .app _ e1 e2 => collectFvarNames e1 ++ collectFvarNames e2
  | .ite _ c t e => collectFvarNames c ++ collectFvarNames t ++ collectFvarNames e
  | .eq _ e1 e2 => collectFvarNames e1 ++ collectFvarNames e2
  | _ => []

def isConst {T : LExprParamsT} (e : LExpr T) : Bool :=
  match e with
  | .const _ _ => true
  | _ => false

def isOp (e : LExpr T) : Bool :=
  match e with
  | .op _ _ _ => true
  | _ => false

@[expose, match_pattern]
protected def true {T : LExprParams} (m : T.Metadata) : LExpr T.mono := .boolConst m true

@[expose, match_pattern]
protected def false {T : LExprParams} (m : T.Metadata) : LExpr T.mono := .boolConst m false

def isTrue (T : LExprParamsT) (e : LExpr T) : Bool :=
  match e with
  | .boolConst _ true => true
  | _ => false

def isFalse (T : LExprParamsT) (e : LExpr T) : Bool :=
  match e with
  | .boolConst _ false => true
  | _ => false

/-- An iterated/multi-argument lambda with arguments of types `tys` and body `body`-/
def absMulti (m: Metadata) (tys: List TypeType) (body: LExpr ⟨⟨Metadata, IDMeta⟩, TypeType⟩)
    : LExpr ⟨⟨Metadata, IDMeta⟩, TypeType⟩ :=
  List.foldr (fun ty e => .abs m "" (.some ty) e) body tys

/-- An iterated/multi-argument lambda with n inferred arguments and body `body`-/
def absMultiInfer (m: Metadata) (n: Nat) (body: LExpr ⟨⟨Metadata, IDMeta⟩, TypeType⟩)
    : LExpr ⟨⟨Metadata, IDMeta⟩, TypeType⟩ :=
  List.foldr (fun _ e => .abs m "" .none e) body (List.range n)

/--
If `e` is an `LExpr` boolean, then denote that into a Lean `Bool`.
-/
def denoteBool {T : LExprParams} (e : LExpr ⟨T, TypeType⟩) : Option Bool :=
  match e with
  | .boolConst _ b => some b
  | _ => none

/--
If `e` is an `LExpr` integer, then denote that into a Lean `Int`.
-/
def denoteInt {T : LExprParams} (e : LExpr ⟨T, TypeType⟩) : Option Int :=
  match e with
  | .intConst _ x => x
  | _ => none

/--
If `e` is an `LExpr` real, then denote that into a Lean `Rat`.
-/
def denoteReal {T : LExprParams} (e : LExpr ⟨T, TypeType⟩) : Option Rat :=
  match e with
  | .realConst _ r => some r
  | _ => none

/--
If `e` is an `LExpr` bv<n>, then denote that into a Lean `BitVec n`.
-/
def denoteBitVec {T : LExprParams} (n : Nat) (e : LExpr ⟨T, TypeType⟩) : Option (BitVec n) :=
  match e with
  | .bitvecConst _ n' b => if n == n' then some (BitVec.ofNat n b.toNat) else none
  | _ => none

/--
If `e` is an `LExpr` string, then denote that into a Lean `String`.
-/
def denoteString {T : LExprParams} (e : LExpr T.mono) : Option String :=
  match e with
  | .strConst _ s => some s
  | _ => none

def mkApp {T : LExprParamsT} (m : T.base.Metadata) (fn : LExpr T) (args : List (LExpr T)) : LExpr T :=
  match args with
  | [] => fn
  | a :: rest =>
    mkApp m (.app m fn a) rest

/--
Returns the metadata of `e`.
-/
def metadata {T : LExprParamsT} (e : LExpr T) : T.base.Metadata :=
  match e with
  | .const m _ => m
  | .op m _ _ => m
  | .bvar m _ => m
  | .fvar m _ _ => m
  | .abs m _ _ _ => m
  | .quant m _ _ _ _ _ => m
  | .app m _ _ => m
  | .ite m _ _ _ => m
  | .eq m _ _ => m

def replaceMetadata1 {T : LExprParamsT} (r: T.base.Metadata) (e : LExpr T) : LExpr T :=
  match e with
  | .const _ c => .const r c
  | .op _ o ty => .op r o ty
  | .bvar _ i => .bvar r i
  | .fvar _ name ty => .fvar r name ty
  | .abs _ name ty e' => .abs r name ty e'
  | .quant _ qk name ty tr e' => .quant r qk name ty tr e'
  | .app _ e1 e2 => .app r e1 e2
  | .ite _ c t e' => .ite r c t e'
  | .eq _ e1 e2 => .eq r e1 e2


/--
Transform metadata in an expression using a callback function.
-/
def replaceMetadata {T : LExprParamsT} (e : LExpr T) (f : T.base.Metadata → NewMetadata) : LExpr ⟨⟨NewMetadata, T.base.IDMeta⟩, T.TypeType⟩ :=
  match e with
  | .const m c =>
    .const (f m) c
  | .op m o uty =>
    .op (f m) o uty
  | .bvar m b =>
    .bvar (f m) b
  | .fvar m x uty =>
    .fvar (f m) x uty
  | .app m e1 e2 =>
    let e1 := replaceMetadata e1 f
    let e2 := replaceMetadata e2 f
    .app (f m) e1 e2
  | .abs m name uty e =>
    let e := replaceMetadata e f
    .abs (f m) name uty e
  | .quant m qk name argTy tr e =>
    let e := replaceMetadata e f
    let tr := replaceMetadata tr f
    .quant (f m) qk name argTy tr e
  | .ite m c t f_expr =>
    let c := replaceMetadata c f
    let t := replaceMetadata t f
    let f_expr := replaceMetadata f_expr f
    .ite (f m) c t f_expr
  | .eq m e1 e2 =>
    let e1 := replaceMetadata e1 f
    let e2 := replaceMetadata e2 f
    .eq (f m) e1 e2

-- Replace all metadata by a unit, suitable for comparison
def eraseMetadata {T : LExprParamsT} (e : LExpr T) : LExpr ⟨⟨Unit, T.base.IDMeta⟩, T.TypeType⟩ := LExpr.replaceMetadata e (λ_ =>())

/--
Compute the size of `e` as a tree.

Not optimized for execution efficiency, but can be used for termination
arguments.
-/
def size (T : LExprParamsT) (e : LExpr T) : Nat :=
  match e with
  | .const .. | .op .. | .bvar .. | .fvar .. => 1
  | .abs _ _ _ e' => 1 + size T e'
  | .quant _ _ _ _ _ e' => 1 + size T e'
  | .app _ e1 e2 => 1 + size T e1 + size T e2
  | .ite _ c t f => 1 + size T c + size T t + size T f
  | .eq _ e1 e2 => 1 + size T e1 + size T e2

/--
Erase all type annotations from `e` except the bound variables of abstractions
and quantified expressions.
-/
def eraseTypes {T : LExprParamsT} (e : LExpr T) : LExpr T :=
  match e with
  | .const m c => .const m c
  | .op m o _ => .op m o none
  | .fvar m x _ => .fvar m x none
  | .bvar _ _ => e
  | .abs m name ty e => .abs m name ty (eraseTypes e)
  | .quant m qk name _ tr e => .quant m qk name .none (eraseTypes tr) (eraseTypes e)
  | .app m e1 e2 => .app m (eraseTypes e1) (eraseTypes e2)
  | .ite m c t f => .ite m (eraseTypes c) (eraseTypes t) (eraseTypes f)
  | .eq m e1 e2 => .eq m (eraseTypes e1) (eraseTypes e2)

---------------------------------------------------------------------

/- Formatting and Parsing of Lambda Expressions -/
instance : ToString LConst where
  toString c :=
    match c with
    | .intConst i => toString i
    | .strConst s => s
    | .realConst r => toString r
    | .bitvecConst _ b => toString (b.toNat)
    | .boolConst b => toString b

instance (T : LExprParamsT) [Repr T.base.IDMeta] [Repr T.TypeType] [Repr T.base.Metadata] : ToString (LExpr T) where
   toString a := toString (repr a)

private def collectAppSpine {T : LExprParamsT} : LExpr T → List (LExpr T)
  | .app _ fn arg => collectAppSpine fn ++ [arg]
  | other => [other]

/-
Theorem: For any application expression e, every element of collectAppSpine e
is strictly smaller than e.

Proof: By obtaining m, fn, arg from hApp, then by induction on fn.

  Base case (fn is not .app):
    1. collectAppSpine e = [fn, arg]
       by definition (subst e = app m fn arg, fn not .app)
    2. ec = fn or ec = arg
    3. sizeOf e = 3 + sizeOf fn + sizeOf arg > sizeOf ec
       by arithmetic

  Inductive case (fn = app m' fn' arg'):
    Assume: ∀ ec ∈ collectAppSpine (app m' fn' arg'),
            ec.sizeOf < (app m' fn' arg').sizeOf  [IH]
    1. collectAppSpine e = collectAppSpine (app m' fn' arg') ++ [arg]
       by definition
    2. Case ec ∈ collectAppSpine (app m' fn' arg'):
       ec.sizeOf < sizeOf fn < sizeOf e by IH and arithmetic
    3. Case ec = arg:
       ec.sizeOf < sizeOf e by arithmetic
-/
private theorem collectAppSpine_lt {T : LExprParamsT} (e : LExpr T) (ec : LExpr T)
    (hec : ec ∈ collectAppSpine e) (hApp : ∃ m fn arg, e = .app m fn arg) :
    ec.sizeOf < e.sizeOf := by
  obtain ⟨m, fn, arg, rfl⟩ := hApp
  induction fn generalizing arg m ec with
  | app m' fn' arg' ih =>
    simp [collectAppSpine] at hec
    cases hec with
    | inl h =>
      have := ih ec m' arg' (by simp [collectAppSpine]; exact Or.inl h)
      simp [LExpr.sizeOf] at this ⊢; omega
    | inr h =>
      rcases h with rfl | rfl <;> simp [LExpr.sizeOf] <;> omega
  | _ =>
    simp [collectAppSpine] at hec
    rcases hec with rfl | rfl <;> simp [LExpr.sizeOf] <;> omega

private def formatLExpr (T : LExprParamsT) [ToFormat T.base.IDMeta] [ToFormat T.TypeType] (e : LExpr T) :
    Format :=
  match _: e with
  | .const _ c => f!"#{c}"
  | .op _ c ty =>
    match ty with
    | none => f!"~{c}"
    | some ty => f!"(~{c} : {ty})"
  | .bvar _ i => f!"%{i}"
  | .fvar _ x ty =>
    match ty with
    | none => f!"{x}"
    | some ty => f!"({x} : {ty})"
  | .abs _ _ _ e1 => Format.paren (f!"λ {formatLExpr T e1}")
  | .quant _ .all _ _ _ e1 => Format.paren (f!"∀ {formatLExpr T e1}")
  | .quant _ .exist _ _ _ e1 => Format.paren (f!"∃ {formatLExpr T e1}")
  | .app m fn arg =>
    let fmts := (collectAppSpine e).attach.map (fun ⟨ec, hec⟩ =>
      have : sizeOf ec < sizeOf e := collectAppSpine_lt e ec hec ⟨m, fn, arg, by subst_vars; rfl⟩
      formatLExpr T ec)
    Format.paren (Format.group (Format.joinSep fmts Format.line))
  | .ite _ c t el => Format.paren
                      ("if " ++ formatLExpr T c ++
                       " then " ++ formatLExpr T t ++ " else "
                       ++ formatLExpr T el)
  | .eq _ e1 e2 => Format.paren (formatLExpr T e1 ++ " == " ++ formatLExpr T e2)
  termination_by sizeOf e

instance (T : LExprParamsT) [ToFormat T.base.IDMeta] [ToFormat T.TypeType] : ToFormat (LExpr T) where
  format := private formatLExpr T

/-
Syntax for conveniently building `LExpr` terms with `LMonoTy`, scoped under the namespace
`LExpr.SyntaxMono`.
-/
namespace SyntaxMono
open Lean Elab Meta

-- Although T is not used in the class, it makes it possible to create instances
-- so that toExpr is meant to be typed
meta class MkLExprParams (T: LExprParams) where
  elabIdent : Lean.Syntax → MetaM Expr
  toExpr : Expr

declare_syntax_cat lidentmono

declare_syntax_cat lexprmono

-- We expect that `LExpr` will support at least Boolean constants because
-- it includes an if-then-else construct. Here we define a syntactic category
-- for booleans, and also -- for practical reasons -- integers as well.
declare_syntax_cat lconstmono
declare_syntax_cat lnummono
scoped syntax "#" noWs num : lnummono
scoped syntax "#" noWs "-" noWs num : lnummono
scoped syntax lnummono : lconstmono
declare_syntax_cat lboolmono
scoped syntax "#true" : lboolmono
scoped syntax "#false" : lboolmono
scoped syntax lboolmono : lconstmono
scoped syntax "#" noWs ident : lconstmono
scoped syntax "(" lconstmono ":" lmonoty ")" : lconstmono
scoped syntax lconstmono : lexprmono

meta def mkIntLit (n: NumLit) : Expr := Expr.app (.const ``Int.ofNat []) (mkNatLit n.getNat)
meta def mkNegLit (n: NumLit) := Expr.app (.const ``Int.neg []) (mkIntLit n)

meta def elabLConstMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lconstmono| #$n:num)  => do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let intVal := mkIntLit n
    let lconstVal ← mkAppM ``LConst.intConst #[intVal]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | `(lconstmono| #-$n:num)  => do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let intVal := mkNegLit n
    let lconstVal ← mkAppM ``LConst.intConst #[intVal]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | `(lconstmono| #true)    => do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let lconstVal ← mkAppM ``LConst.boolConst #[toExpr true]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | `(lconstmono| #false)   =>  do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let lconstVal ← mkAppM ``LConst.boolConst #[toExpr false]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | `(lconstmono| #$s:ident) => do
    let s := toString s.getId
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    let lconstVal ← mkAppM ``LConst.strConst #[mkStrLit s]
    return mkAppN (.const ``LExpr.const []) #[tMono, metadata, lconstVal]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lopmono
scoped syntax "~" noWs lidentmono : lopmono
scoped syntax "(" lopmono ":" lmonoty ")" : lopmono
scoped syntax lopmono : lexprmono

meta def elabLOpMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lopmono| ~$s:lidentmono)  => do
    let none ← mkNone (mkConst ``LMonoTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.op []) #[tMono, metadata, ← MkLExprParams.elabIdent T s, none]
  | `(lopmono| (~$s:lidentmono : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.op []) #[tMono, metadata, ← MkLExprParams.elabIdent T s, lmonoty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lbvarmono
scoped syntax "%" noWs num : lbvarmono
meta def elabLBVarMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lbvarmono| %$n:num) => do
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.bvar []) #[tMono, metadata, mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax
scoped syntax lbvarmono : lexprmono

declare_syntax_cat lfvarmono
scoped syntax lidentmono : lfvarmono
scoped syntax "(" lidentmono ":" lmonoty ")" : lfvarmono

meta def elabLFVarMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lfvarmono| $i:lidentmono) => do
    let none ← mkNone (mkConst ``LMonoTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.fvar []) #[tMono, metadata, ← MkLExprParams.elabIdent T i, none]
  | `(lfvarmono| ($i:lidentmono : $ty:lmonoty)) => do
    let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy ty
    let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
    let metadata ← mkAppM ``Unit.unit #[]
    let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
    return mkAppN (.const ``LExpr.fvar []) #[tMono, metadata, ← MkLExprParams.elabIdent T i, lmonoty]
  | _ => throwUnsupportedSyntax
scoped syntax lfvarmono : lexprmono

declare_syntax_cat mabsmono
declare_syntax_cat mallmono
declare_syntax_cat mexistmono
scoped syntax "λ" lexprmono : mabsmono
scoped syntax "λ" "(" lmonoty ")" ":" lexprmono : mabsmono
scoped syntax "∀" lexprmono : mallmono
scoped syntax "∀" "{" lexprmono "}" lexprmono : mallmono
scoped syntax "∀" "(" lmonoty ")" ":" lexprmono : mallmono
scoped syntax "∀" "(" lmonoty ")" ":" "{" lexprmono "}" lexprmono : mallmono
scoped syntax "∃" lexprmono : mexistmono
scoped syntax "∃" "{" lexprmono "}" lexprmono : mexistmono
scoped syntax "∃" "(" lmonoty ")" ":" lexprmono : mexistmono
scoped syntax "∃" "(" lmonoty ")" ":" "{" lexprmono "}" lexprmono : mexistmono
scoped syntax mabsmono : lexprmono
scoped syntax mallmono : lexprmono
scoped syntax mexistmono : lexprmono
declare_syntax_cat mappmono
scoped syntax "(" lexprmono lexprmono ")" : mappmono
scoped syntax mappmono : lexprmono
declare_syntax_cat meqmono
scoped syntax "==" : meqmono
scoped syntax lexprmono meqmono lexprmono : lexprmono
declare_syntax_cat mifmono
scoped syntax "if" : mifmono
scoped syntax "then" : mifmono
scoped syntax "else" : mifmono
scoped syntax mifmono lexprmono mifmono lexprmono mifmono lexprmono : lexprmono

scoped syntax "(" lexprmono ")" : lexprmono

open LTy.Syntax in
/-- Elaborator for Lambda expressions.

All type annotations in `LExpr` are for monotypes, not polytypes. It's the
user's responsibility to ensure correct usage of type variables (i.e., they're
unique).
-/
meta partial def elabLExprMono [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lexprmono| $c:lconstmono) => elabLConstMono (T:=T) c
  | `(lexprmono| $o:lopmono) => elabLOpMono (T:=T) o
  | `(lexprmono| $b:lbvarmono) => elabLBVarMono (T:=T) b
  | `(lexprmono| $f:lfvarmono) => elabLFVarMono (T:=T) f
  | `(lexprmono| λ $e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.absUntyped []) #[tMono, metadata, e']
  | `(lexprmono| λ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.abs []) #[tMono, metadata, mkStrLit "", lmonoty, e']
  | `(lexprmono| ∀ $e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.allUntyped []) #[tMono, metadata, e']
  | `(lexprmono| ∀ {$tr}$e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let tr' ← elabLExprMono (T:=T) tr
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     return mkAppN (.const ``LExpr.allUntypedTr []) #[tMono, metadata, tr', e']
  | `(lexprmono| ∀ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     let emptyName := mkStrLit ""
     return mkAppN (.const ``LExpr.all []) #[tMono, metadata, emptyName, lmonoty, e']
  | `(lexprmono| ∀ ($mty:lmonoty):{$tr} $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tr' ← elabLExprMono (T:=T) tr
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     let emptyName := mkStrLit ""
     return mkAppN (.const ``LExpr.allTr []) #[tMono, metadata, emptyName, lmonoty, tr', e']
  | `(lexprmono| ∃ ($mty:lmonoty): $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     let emptyName := mkStrLit ""
     return mkAppN (.const ``LExpr.exist []) #[tMono, metadata, emptyName, lmonoty, e']
  | `(lexprmono| ∃ ($mty:lmonoty):{$tr} $e:lexprmono) => do
     let lmonoty ← Lambda.LTy.Syntax.elabLMonoTy mty
     let lmonoty ← mkSome (mkConst ``LMonoTy) lmonoty
     let e' ← elabLExprMono (T:=T) e
     let tr' ← elabLExprMono (T:=T) tr
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     let metadata ← mkAppM ``Unit.unit #[]
     let emptyName := mkStrLit ""
     return mkAppN (.const ``LExpr.existTr []) #[tMono, metadata, emptyName, lmonoty, tr', e']
  | `(lexprmono| ∃ $e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.existUntyped []) #[tMono, metadata, e']
  | `(lexprmono| ∃{$tr} $e:lexprmono) => do
     let e' ← elabLExprMono (T:=T) e
     let tr' ← elabLExprMono (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.existUntypedTr []) #[tMono, metadata, tr', e']
  | `(lexprmono| ($e1:lexprmono $e2:lexprmono)) => do
     let e1' ← elabLExprMono (T:=T) e1
     let e2' ← elabLExprMono (T:=T) e2
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.app []) #[tMono, metadata, e1', e2']
  | `(lexprmono| $e1:lexprmono == $e2:lexprmono) => do
     let e1' ← elabLExprMono (T:=T) e1
     let e2' ← elabLExprMono (T:=T) e2
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.eq []) #[tMono, metadata, e1', e2']
  | `(lexprmono| if $e1:lexprmono then $e2:lexprmono else $e3:lexprmono) => do
     let e1' ← elabLExprMono (T:=T) e1
     let e2' ← elabLExprMono (T:=T) e2
     let e3' ← elabLExprMono (T:=T) e3
     let metadata ← mkAppM ``Unit.unit #[]
     let tMono ← mkAppM ``LExprParams.mono #[MkLExprParams.toExpr T]
     return mkAppN (.const ``LExpr.ite []) #[tMono, metadata, e1', e2', e3']
  | `(lexprmono| ($e:lexprmono)) => elabLExprMono (T:=T) e
  | _ => throwUnsupportedSyntax

scoped syntax ident : lidentmono
/-- Elaborator for String identifiers, construct a String instance -/
meta def elabStrIdent : Lean.Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := s.getId
    return mkAppN (.const `Lambda.Identifier.mk []) #[.const ``Unit [], mkStrLit s.toString, .const ``Unit.unit []]
  | _ => throwUnsupportedSyntax

-- Unit metadata, Unit IDMeta
meta instance : MkLExprParams ⟨Unit, Unit⟩ where
  elabIdent := elabStrIdent
  toExpr := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (mkConst ``Unit)

elab "esM[" e:lexprmono "]" : term => elabLExprMono (T:=⟨Unit, Unit⟩) e

-- Syntax tests moved to StrataTest/DL/Lambda/LExprSyntaxTests.lean

end SyntaxMono



/-
Syntax for conveniently building `LExpr` terms with `LTy`, scoped under the namespace
`LExpr.Syntax`.
-/
namespace Syntax
open Lean Elab Meta

-- Although T is not used in the class, it makes it possible to create instances
-- so that toExpr is meant to be typed
meta class MkLExprParams (T: LExprParams) where
  elabIdent : Lean.Syntax → MetaM Expr
  toExpr : Expr

declare_syntax_cat lident

declare_syntax_cat lexpr

-- We expect that `LExpr` will support at least Boolean constants because
-- it includes an if-then-else construct. Here we define a syntactic category
-- for booleans, and also -- for practical reasons -- integers as well.
declare_syntax_cat lconst
declare_syntax_cat lnum
scoped syntax "#" noWs num : lnum
scoped syntax "#" noWs "-" noWs num : lnum
scoped syntax lnum : lconst
declare_syntax_cat lbool
scoped syntax "#true" : lbool
scoped syntax "#false" : lbool
scoped syntax lbool : lconst
scoped syntax "#" noWs ident : lconst
scoped syntax "(" lconst ":" lty ")" : lconst
scoped syntax lconst : lexpr

meta def mkIntLit (n: NumLit) : Expr := Expr.app (.const ``Int.ofNat []) (mkNatLit n.getNat)
meta def mkNegLit (n: NumLit) := Expr.app (.const ``Int.neg []) (mkIntLit n)

meta def elabLConst [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lconst| #$n:num)  => do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    let lconstVal ← mkAppM ``LConst.intConst #[mkIntLit n]
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, lconstVal]
  | `(lconst| #-$n:num) => do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    let lconstVal ← mkAppM ``LConst.intConst #[mkNegLit n]
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, lconstVal]
  | `(lconst| #true)    => do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.boolConst []) #[tParams, metadata, toExpr true]
  | `(lconst| #false)   =>  do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.boolConst []) #[tParams, metadata, toExpr false]
  | `(lconst| #$s:ident) => do
    let s := toString s.getId
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.const []) #[tParams, metadata, mkStrLit s]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lop
scoped syntax "~" noWs lident : lop
scoped syntax "(" lop ":" lty ")" : lop
scoped syntax lop : lexpr

meta def elabLOp [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lop| ~$s:lident)  => do
    let none ← mkNone (mkConst ``LTy)
    let ident ← MkLExprParams.elabIdent T s
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.op []) #[tParams, metadata, ident, none]
  | `(lop| (~$s:lident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.op []) #[tParams, metadata, ← MkLExprParams.elabIdent T s, lty]
  | _ => throwUnsupportedSyntax

declare_syntax_cat lbvar
scoped syntax "%" noWs num : lbvar

meta def elabLBVar [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lbvar| %$n:num) => do
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.bvar []) #[tParams, metadata, mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax
scoped syntax lbvar : lexpr

declare_syntax_cat lfvar
scoped syntax lident : lfvar
scoped syntax "(" lident ":" lty ")" : lfvar

meta def elabLFVar [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lfvar| $i:lident) => do
    let none ← mkNone (mkConst ``LTy)
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.fvar []) #[tParams, metadata, ← MkLExprParams.elabIdent T i, none]
  | `(lfvar| ($i:lident : $ty:lty)) => do
    let lty ← Lambda.LTy.Syntax.elabLTy ty
    let lty ← mkSome (mkConst ``LTy) lty
    let metadata ← mkAppM ``Unit.unit #[]
    let baseParams := MkLExprParams.toExpr T
    let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
    return mkAppN (.const ``LExpr.fvar []) #[tParams, metadata, ← MkLExprParams.elabIdent T i, lty]
  | _ => throwUnsupportedSyntax
scoped syntax lfvar : lexpr

declare_syntax_cat mabs
declare_syntax_cat mall
declare_syntax_cat mexist
scoped syntax "λ" lexpr : mabs
scoped syntax "λ" "(" lty ")" ":" lexpr : mabs
scoped syntax "∀" lexpr : mall
scoped syntax "∀" "{" lexpr "}" lexpr : mall
scoped syntax "∀" "(" lty ")" ":" lexpr : mall
scoped syntax "∀" "(" lty ")" ":" "{" lexpr "}" lexpr : mall
scoped syntax "∃" lexpr : mexist
scoped syntax "∃" "{" lexpr "}" lexpr : mexist
scoped syntax "∃" "(" lty ")" ":" lexpr : mexist
scoped syntax "∃" "(" lty ")" ":" "{" lexpr "}" lexpr : mexist
scoped syntax mabs : lexpr
scoped syntax mall : lexpr
scoped syntax mexist : lexpr
declare_syntax_cat mapp
scoped syntax "(" lexpr lexpr ")" : mapp
scoped syntax mapp : lexpr
declare_syntax_cat meq
scoped syntax "==" : meq
scoped syntax lexpr meq lexpr : lexpr
declare_syntax_cat mif
scoped syntax "if" : mif
scoped syntax "then" : mif
scoped syntax "else" : mif
scoped syntax mif lexpr mif lexpr mif lexpr : lexpr

scoped syntax "(" lexpr ")" : lexpr

open LTy.Syntax in
/-- Elaborator for Lambda expressions.

It's the user's responsibility to ensure correct usage of type variables (i.e., they're
unique).
-/
meta partial def elabLExpr [MkLExprParams T] : Lean.Syntax → MetaM Expr
  | `(lexpr| $c:lconst) => elabLConst (T:=T) c
  | `(lexpr| $o:lop) => elabLOp (T:=T) o
  | `(lexpr| $b:lbvar) => elabLBVar (T:=T) b
  | `(lexpr| $f:lfvar) => elabLFVar (T:=T) f
  | `(lexpr| λ $e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.absUntyped []) #[tParams, metadata, e']
  | `(lexpr| λ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.abs []) #[tParams, metadata, mkStrLit "", lty, e']
  | `(lexpr| ∀ $e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.allUntyped []) #[tParams, metadata, e']
  | `(lexpr| ∀{$tr}$e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let tr' ← elabLExpr (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.allUntypedTr []) #[tParams, metadata, tr', e']
  | `(lexpr| ∀ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     let emptyName := mkStrLit ""
     return mkAppN (.const ``LExpr.all []) #[tParams, metadata, emptyName, lty, e']
  | `(lexpr| ∀ ($mty:lty): {$tr}$e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let tr' ← elabLExpr (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     let emptyName := mkStrLit ""
     return mkAppN (.const ``LExpr.allTr []) #[tParams, metadata, emptyName, lty, tr', e']
  | `(lexpr| ∃ ($mty:lty): $e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     let emptyName := mkStrLit ""
     return mkAppN (.const ``LExpr.exist []) #[tParams, metadata, emptyName, lty, e']
  | `(lexpr| ∃ ($mty:lty): {$tr}$e:lexpr) => do
     let lty ← Lambda.LTy.Syntax.elabLTy mty
     let lty ← mkSome (mkConst ``LTy) lty
     let e' ← elabLExpr (T:=T) e
     let tr' ← elabLExpr (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     let emptyName := mkStrLit ""
     return mkAppN (.const ``LExpr.existTr []) #[tParams, metadata, emptyName, lty, tr', e']
  | `(lexpr| ∃ $e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.existUntyped []) #[tParams, metadata, e']
  | `(lexpr| ∃ {$tr} $e:lexpr) => do
     let e' ← elabLExpr (T:=T) e
     let tr' ← elabLExpr (T:=T) tr
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.existUntypedTr []) #[tParams, metadata, tr', e']
  | `(lexpr| ($e1:lexpr $e2:lexpr)) => do
     let e1' ← elabLExpr (T:=T) e1
     let e2' ← elabLExpr (T:=T) e2
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.app []) #[tParams, metadata, e1', e2']
  | `(lexpr| $e1:lexpr == $e2:lexpr) => do
     let e1' ← elabLExpr (T:=T) e1
     let e2' ← elabLExpr (T:=T) e2
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.eq []) #[tParams, metadata, e1', e2']
  | `(lexpr| if $e1:lexpr then $e2:lexpr else $e3:lexpr) => do
     let e1' ← elabLExpr (T:=T) e1
     let e2' ← elabLExpr (T:=T) e2
     let e3' ← elabLExpr (T:=T) e3
     let metadata ← mkAppM ``Unit.unit #[]
     let baseParams := MkLExprParams.toExpr T
     let tParams := mkApp2 (mkConst ``LExprParamsT.mk) baseParams (mkConst ``LTy)
     return mkAppN (.const ``LExpr.ite []) #[tParams, metadata, e1', e2', e3']
  | `(lexpr| ($e:lexpr)) => elabLExpr (T:=T) e
  | _ => throwUnsupportedSyntax

scoped syntax ident : lident
/-- Elaborator for String identifiers, construct a String instance -/
meta def elabStrIdent : Lean.Syntax → MetaM Expr
  | `(lident| $s:ident) => do
    let s := s.getId
    return mkAppN (.const `Lambda.Identifier.mk []) #[.const ``Unit [], mkStrLit s.toString, .const ``Unit.unit []]
  | _ => throwUnsupportedSyntax

meta instance : MkLExprParams ⟨Unit, Unit⟩ where
  elabIdent := elabStrIdent
  toExpr := mkApp2 (mkConst ``LExprParams.mk) (mkConst ``Unit) (mkConst ``Unit)

elab "es[" e:lexpr "]" : term => elabLExpr (T:=⟨Unit, Unit⟩) e

-- Syntax tests moved to StrataTest/DL/Lambda/LExprSyntaxTests.lean

end Syntax

---------------------------------------------------------------------

end LExpr
end -- public section
end Lambda


/-! ## Well-formedness of Lambda Expressions

See the definition `Lambda.LExpr.WF`. Also see theorem `HasType.regularity` in
`Strata.DL.Lambda.LExprTypeSpec`.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

public section

namespace LExpr

variable {T : LExprParams} [DecidableEq T.IDMeta]

/--
Compute the free variables in an `LExpr`, which are simply all the `LExpr.fvar`s
in it.
-/
def freeVars (e : LExpr ⟨T, GenericTy⟩) : IdentTs GenericTy T.IDMeta :=
  match e with
  | .const _ _ => []
  | .op _ _ _ => []
  | .bvar _ _ => []
  | .fvar _ x ty => [(x, ty)]
  | .abs _ _ _ e1 => freeVars e1
  | .quant _ _ _ _ tr e1 => freeVars tr ++ freeVars e1
  | .app _ e1 e2 => freeVars e1 ++ freeVars e2
  | .ite _ c t e => freeVars c ++ freeVars t ++ freeVars e
  | .eq _ e1 e2 => freeVars e1 ++ freeVars e2

/--
Is `x` a fresh variable w.r.t. `e`?
-/
def fresh (x : IdentT GenericTy T.IDMeta) (e : LExpr ⟨T, GenericTy⟩) : Prop :=
  x ∉ (freeVars e)

/-- An expression `e` is closed if has no free variables. -/
def closed (e : LExpr ⟨T, GenericTy⟩) : Bool :=
  freeVars e |>.isEmpty

omit [DecidableEq T.IDMeta] in
@[simp]
theorem fresh_abs {x : IdentT GenericTy T.IDMeta} {m : T.Metadata} {name : String} {ty : Option GenericTy} {e : LExpr ⟨T, GenericTy⟩} :
  fresh x (.abs m name ty e) = fresh x e := by
  simp [fresh, freeVars]

omit [DecidableEq T.IDMeta] in
@[simp]
theorem freeVars_abs {m : T.Metadata} {name : String} {ty : Option GenericTy} {e : LExpr ⟨T, GenericTy⟩} :
  freeVars (.abs m name ty e) = freeVars e := by
  simp [freeVars]

omit [DecidableEq T.IDMeta] in
@[simp]
theorem closed_abs {m : T.Metadata} {name : String} {ty : Option GenericTy} {e : LExpr ⟨T, GenericTy⟩} :
  closed (.abs m name ty e) = closed e := by
  simp [closed]

---------------------------------------------------------------------

/-! ### Substitutions in `LExpr`s -/

/--
This function replaces some bound variables in `e` by an arbitrary expression
`s` (and `s` may contain some free variables).

`substK k s e` keeps track of the number `k` of abstractions that have passed
by; it replaces all leaves of the form `(.bvar k)` with `s`.
-/
def substK {T:LExprParamsT} (k : Nat) (s : T.base.Metadata → LExpr T)
    (e : LExpr T) : LExpr T :=
  match e with
  | .const m c => .const m c
  | .op m o ty => .op m o ty
  | .bvar m i => if i == k then s m else .bvar m i
  | .fvar m y ty => .fvar m y ty
  | .abs m name ty e' => .abs m name ty (substK (k + 1) s e')
  | .quant m qk name ty tr' e' => .quant m qk name ty (substK (k + 1) s tr') (substK (k + 1) s e')
  | .app m e1 e2 => .app m (substK k s e1) (substK k s e2)
  | .ite m c t e => .ite m (substK k s c) (substK k s t) (substK k s e)
  | .eq m e1 e2 => .eq m (substK k s e1) (substK k s e2)

/--
Substitute the outermost bound variable in `e` by an arbitrary expression `s`.

This function is useful for β-reduction -- the reduction of
`app (abs e) s` can be implemented by `subst s e`. Having a locally nameless
representation allows us to avoid the pitfalls of variable shadowing and
capture. E.g., consider the following, written in the "raw" style of lambda
calculus.

`(λxλy x y) (λa b) --β--> λy (λa b) y`

If we'd used vanilla de Bruijn representation, we'd have the following instead,
where we'd need to shift the index of the free variable `b` to avoid capture:

`(λλ 1 0) (λ 5) --β--> λ (λ 6) 0`

We distinguish between free and bound variables in our notation, which allows us
to avoid such issues:

`(λλ 1 0) (λ b) --β--> (λ (λ b) 0)`
-/
def subst {T:LExprParamsT} (s : T.base.Metadata → LExpr T) (e : LExpr T) : LExpr T :=
  substK 0 s e

/--
This function turns some bound variables to free variables to investigate the
body of an abstraction. `varOpen k x e` keeps track of the number `k` of
abstractions that have passed by; it replaces all leaves of the form `(.bvar k)`
with `(.fvar x)`.

Note that `x` is expected to be a fresh variable w.r.t. `e`.
-/
def varOpen (k : Nat) (x : IdentT GenericTy T.IDMeta) (e : LExpr ⟨T, GenericTy⟩) : LExpr ⟨T, GenericTy⟩ :=
  substK k (fun m => .fvar m x.fst x.snd) e

theorem varOpen_sizeOf {T}:
  ∀ (x:IdentT GenericTy T.IDMeta) e k,
    (varOpen (T := T) k x e).sizeOf = e.sizeOf := by
  intros x e
  induction e
  case const _ _ | op _ _ _ | fvar _ _ _ =>
    unfold varOpen substK; solve | simp
  case bvar _ n =>
    intro k
    unfold varOpen substK
    split <;> solve | simp
  case abs _ ty e IH =>
    unfold varOpen substK
    intro k
    simp only [sizeOf]
    unfold varOpen at IH
    grind
  case quant _ ty e trigger x_IH trigger_IH =>
    unfold varOpen substK
    intro k
    simp only [sizeOf]
    unfold varOpen at x_IH trigger_IH
    grind
  case app _ _ lhs_IH rhs_IH  | eq _ _ lhs_IH rhs_IH =>
    unfold varOpen substK
    unfold varOpen at lhs_IH rhs_IH
    simp only [sizeOf]
    grind
  case ite _ _ c_IH then_IH else_IH =>
    unfold varOpen substK
    unfold varOpen at c_IH then_IH else_IH
    simp only [sizeOf]
    grind

/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `varClose k x e` keeps track of the number `k`
of abstractions that have passed by; it replaces all `(.fvar x)` with
`(.bvar k)`.
-/
def varClose {T} {GenericTy} [BEq (Identifier T.IDMeta)] [BEq GenericTy] (k : Nat) (x : IdentT GenericTy T.IDMeta) (e : LExpr ⟨T, GenericTy⟩) : LExpr ⟨T, GenericTy⟩ :=
  match e with
  | .const m c => .const m c
  | .op m o ty => .op m o ty
  | .bvar m i => .bvar m i
  | .fvar m y (yty: Option GenericTy) => if x.fst == y && (yty == x.snd) then
                      (.bvar m k) else (.fvar m y yty)
  | .abs m name ty e' => .abs m name ty (varClose (k + 1) x e')
  | .quant m qk name ty tr' e' => .quant m qk name ty (varClose (k + 1) x tr') (varClose (k + 1) x e')
  | .app m e1 e2 => .app m (varClose k x e1) (varClose k x e2)
  | .ite m c t e => .ite m (varClose k x c) (varClose k x t) (varClose k x e)
  | .eq m e1 e2 => .eq m (varClose k x e1) (varClose k x e2)


theorem varClose_of_varOpen [LawfulBEq T.IDMeta] [BEq T.Metadata] [ReflBEq T.Metadata] [BEq GenericTy] [ReflBEq GenericTy] [LawfulBEq GenericTy]  (h : fresh x e) :
  varClose (T := T) (GenericTy := GenericTy) i x (varOpen i x e) = e := by
  induction e generalizing i x
  all_goals try simp_all [fresh, varOpen, LExpr.substK, varClose, freeVars]
  case bvar _ j =>
    by_cases hi : j = i <;>
    simp_all [varClose]
  case fvar _ name ty =>
    intro h1
    have ⟨x1, x2⟩ := x
    simp at h h1
    exact fun a => h h1 (id (Eq.symm a))
  done

---------------------------------------------------------------------

/-! ### Well-formedness of `LExpr`s -/

/--
Characterizing terms that are locally closed, i.e., have no dangling bound
variables.

Example of a term that is not locally closed: `(.abs "x" (.bvar 1))`.
-/
def lcAt (k : Nat) (e : LExpr ⟨T, GenericTy⟩) : Bool :=
  match e with
  | .const _ _ => true
  | .op _ _ _ => true
  | .bvar _ i => i < k
  | .fvar _ _ _ => true
  | .abs _ _ _ e1 => lcAt (k + 1) e1
  | .quant _ _ _ _ tr e1 => lcAt (k + 1) tr && lcAt (k + 1) e1
  | .app _ e1 e2 => lcAt k e1 && lcAt k e2
  | .ite _ c t e' => lcAt k c && lcAt k t && lcAt k e'
  | .eq _ e1 e2 => lcAt k e1 && lcAt k e2

theorem varOpen_varClose_when_lcAt [DecidableEq GenericTy] [BEq T.Metadata] [LawfulBEq T.Metadata]
  (h1 : lcAt k e) (h2 : k <= i) :
  (varOpen i x (varClose (T := T) (GenericTy := GenericTy) i x e)) = e := by
  induction e generalizing k i x
  case const c ty =>
    simp! [lcAt, varOpen, substK]
  case op o ty =>
    simp! [lcAt, varOpen, substK]
  case bvar j =>
    simp_all! [lcAt, varOpen, substK]; omega
  case fvar name ty =>
    simp_all [lcAt, varOpen, varClose]
    by_cases hx: x.fst = name <;> simp_all[substK]
    by_cases ht: ty = x.snd <;> simp_all [substK]
  case abs e e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih (k + 1) (i + 1) x.fst]
  case quant qk e tr_ih e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih (k + 1) (i + 1) x.fst, @tr_ih (k + 1) (i + 1) x.fst]
  case app fn e fn_ih e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih k i x.fst, @fn_ih k i x.fst]
  case ite c t e c_ih t_ih e_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e_ih k i x.fst, @c_ih k i x.fst, @t_ih k i x.fst]
  case eq e1 e2 e1_ih e2_ih =>
    simp_all [lcAt, varOpen, substK, varClose]
    simp_all [@e1_ih k i x.fst, @e2_ih k i x.fst]
  done

theorem lcAt_substK_inv (he: lcAt k (substK i s e)) (hik: k ≤ i) : lcAt (i + 1) e := by
  induction e generalizing i k s <;> simp_all[lcAt, substK] <;> try grind
  case bvar id j =>
    by_cases j = i
    case pos hji => omega
    case neg hji => rw[if_neg hji] at he; simp[lcAt] at he; omega

theorem lcAt_varOpen_inv (hs: lcAt k (varOpen i x e)) (hik: k ≤ i) : lcAt (i + 1) e := by
  unfold varOpen at hs; exact (lcAt_substK_inv hs hik)

theorem lcAt_varOpen_abs
  (h1 : lcAt k (varOpen i x y)) (h2 : k <= i) :
  lcAt i (abs m name ty y) := by
  simp[lcAt]; apply (@lcAt_varOpen_inv k i)<;> assumption

theorem lcAt_varOpen_quant
  (hy : lcAt k (varOpen i x y)) (hki : k <= i)
  (htr: lcAt k (varOpen i x tr)) :
  lcAt i (quant m qk name ty tr y) := by
  simp[lcAt]; constructor<;> apply (@lcAt_varOpen_inv k i) <;> assumption

/--
An `LExpr e` is well-formed if it has no dangling bound variables.

We expect the type system to guarantee the well-formedness of an `LExpr`, i.e.,
we will prove a _regularity_ lemma; see lemma `HasType.regularity`.
-/
def WF {T} {GenericTy} (e : LExpr ⟨T, GenericTy⟩) : Bool :=
  lcAt 0 e

theorem varOpen_of_varClose {T} {GenericTy} [BEq T.Metadata] [LawfulBEq T.Metadata] [DecidableEq T.IDMeta] [DecidableEq GenericTy] {i : Nat} {x : IdentT GenericTy T.IDMeta} {e : LExpr ⟨T, GenericTy⟩} (h : LExpr.WF e) :
  varOpen i x (varClose i x e) = e := by
  simp_all [LExpr.WF]
  rename_i r1 r2 r3
  have c := varOpen_varClose_when_lcAt (GenericTy:=GenericTy) (k:=0) (e:=e) (i:=i) (x:=x) h
  simp at c
  exact c

---------------------------------------------------------------------

/-! ### Substitution on `LExpr`s -/

/--
Increment bound variable indices in `e` by `n`. Only bvars at or above `cutoff`
are shifted; bvars below `cutoff` (bound within `e`) are left alone. The cutoff
increases when going under binders.
-/
def liftBVars (n : Nat) (e : LExpr ⟨T, GenericTy⟩) (cutoff : Nat := 0) : LExpr ⟨T, GenericTy⟩ :=
  match e with
  | .const _ _ => e | .op _ _ _ => e | .fvar _ _ _ => e
  | .bvar m i => if i >= cutoff then .bvar m (i + n) else e
  | .abs m name ty e' => .abs m name ty (liftBVars n e' (cutoff + 1))
  | .quant m qk name ty tr' e' => .quant m qk name ty (liftBVars n tr' (cutoff + 1)) (liftBVars n e' (cutoff + 1))
  | .app m fn e' => .app m (liftBVars n fn cutoff) (liftBVars n e' cutoff)
  | .ite m c t e' => .ite m (liftBVars n c cutoff) (liftBVars n t cutoff) (liftBVars n e' cutoff)
  | .eq m e1 e2 => .eq m (liftBVars n e1 cutoff) (liftBVars n e2 cutoff)

/--
Substitute `(.fvar x _)` in `e` with `to`. Does NOT lift de Bruijn indices in `to`
when going under binders - safe when `to` contains no bvars (e.g., substituting
fvar→fvar). Use `substFvarLifting` when `to` contains bvars.
-/
@[expose] def substFvar [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (fr : T.Identifier) (to : LExpr ⟨T, GenericTy⟩)
  : (LExpr ⟨T, GenericTy⟩) :=
  match e with
  | .const _ _ => e | .bvar _ _ => e | .op _ _ _ => e
  | .fvar _ name _ => if name == fr then to else e
  | .abs m name ty e' => .abs m name ty (substFvar e' fr to)
  | .quant m qk name ty tr' e' => .quant m qk name ty (substFvar tr' fr to) (substFvar e' fr to)
  | .app m fn e' => .app m (substFvar fn fr to) (substFvar e' fr to)
  | .ite m c t e' => .ite m (substFvar c fr to) (substFvar t fr to) (substFvar e' fr to)
  | .eq m e1 e2 => .eq m (substFvar e1 fr to) (substFvar e2 fr to)

/--
Like `substFvar`, but properly lifts de Bruijn indices in `to` when going under
binders. Use this when `to` contains bound variables that should be preserved.

**Important:** `to` is interpreted in the *outer* scope (before entering `e`).
Any bvars in `to` must refer to binders *outside* `e`, not to binders within `e`.
When the traversal descends under a binder in `e`, `liftBVars` shifts `to`'s
indices so they continue to point to the same outer binders.
-/
def substFvarLifting [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (fr : T.Identifier) (to : LExpr ⟨T, GenericTy⟩)
  : (LExpr ⟨T, GenericTy⟩) :=
  go e 0
where
  go (e : LExpr ⟨T, GenericTy⟩) (depth : Nat) : LExpr ⟨T, GenericTy⟩ :=
    match e with
    | .const _ _ => e | .bvar _ _ => e | .op _ _ _ => e
    | .fvar _ name _ => if name == fr then liftBVars depth to else e
    | .abs m name ty e' => .abs m name ty (go e' (depth + 1))
    | .quant m qk name ty tr' e' => .quant m qk name ty (go tr' (depth + 1)) (go e' (depth + 1))
    | .app m fn e' => .app m (go fn depth) (go e' depth)
    | .ite m c t f => .ite m (go c depth) (go t depth) (go f depth)
    | .eq m e1 e2 => .eq m (go e1 depth) (go e2 depth)

def substFvarsLifting [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (sm : Map T.Identifier (LExpr ⟨T, GenericTy⟩))
  : LExpr ⟨T, GenericTy⟩ :=
  List.foldl (fun e (var, s) => substFvarLifting e var s) e sm

@[expose] def substFvars [BEq T.IDMeta] (e : LExpr ⟨T, GenericTy⟩) (sm : Map T.Identifier (LExpr ⟨T, GenericTy⟩))
  : LExpr ⟨T, GenericTy⟩ :=
  List.foldl (fun e (var, s) => substFvar e var s) e sm

---------------------------------------------------------------------

end LExpr
end -- public section
end Lambda

public section
-- Copied over from LNSym
-- https://github.com/leanprover/LNSym/blob/main/Arm/Map.lean

open Std (ToFormat Format format)

/-!
A simple Map-like type based on lists
-/

@[expose] def ListMap (α : Type u) (β : Type v) := List (α × β)

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
end

public section
/-!
## Structured Function Attributes

Structured attributes for controlling partial evaluator behavior
(inlining, concrete evaluation).
-/

namespace Strata.DL.Util

/-- Attributes for functions that control partial evaluator behavior. -/
inductive FuncAttr where
  /-- Always inline the function body when called. -/
  | inline
  /-- Inline when argument at `paramIdx` is a constructor application. -/
  | inlineIfConstr (paramIdx : Nat)
  /-- Use concrete evaluation when argument at `paramIdx` is a constructor application. -/
  | evalIfConstr (paramIdx : Nat)
  deriving DecidableEq, Repr, Inhabited, BEq

open Std (ToFormat Format format)

instance : ToFormat FuncAttr where
  format
    | .inline => "inline"
    | .inlineIfConstr i => f!"inlineIfConstr {i}"
    | .evalIfConstr i => f!"evalIfConstr {i}"

instance : ToFormat (Array FuncAttr) where
  format attrs := Format.joinSep (attrs.toList.map format) ", "

/-- Return the `paramIdx` of the first `inlineIfConstr` attribute, if any. -/
def FuncAttr.findInlineIfConstr (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .inlineIfConstr i => some i | _ => none

/-- Return the `paramIdx` of the first `evalIfConstr` attribute, if any. -/
def FuncAttr.findEvalIfConstr (attrs : Array FuncAttr) : Option Nat :=
  attrs.findSome? fun | .evalIfConstr i => some i | _ => none

end Strata.DL.Util
end


/-!
## Generic Function Structure

This module defines a generic function structure that can be instantiated for
different expression languages. It is parameterized by identifier, expression,
type, and metadata types.

For Lambda expressions, see `LFunc` in `Strata.DL.Lambda.Factory`.
For Imperative expressions, see `PureFunc` in `Strata.DL.Imperative.PureExpr`.
-/

namespace Strata.DL.Util

open Std (ToFormat Format format)

public section

/-- Type identifiers for generic type arguments. Alias for String. -/
@[expose] abbrev TyIdentifier := String

/-- A precondition with its associated metadata -/
structure FuncPrecondition (ExprT : Type) (MetadataT : Type) where
  expr : ExprT
  md : MetadataT

/--
A generic function structure, parameterized by identifier, expression, type, and metadata types.

This structure can be instantiated for different expression languages.
For Lambda expressions, use `LFunc`. For other expression systems, instantiate
with appropriate types.

A optional evaluation function can be provided in the `concreteEval` field for
each factory function to allow the partial evaluator to do constant propagation
when all the arguments of a function are concrete. Such a function should take
two inputs: a function call expression and also -- somewhat redundantly, but
perhaps more conveniently -- the list of arguments in this expression.  Here's
an example of a `concreteEval` function for `Int.Add`:

```
(fun e args => match args with
               | [e1, e2] =>
                 let e1i := LExpr.denoteInt e1
                 let e2i := LExpr.denoteInt e2
                 match e1i, e2i with
                 | some x, some y => (.const (toString (x + y)) mty[int])
                 | _, _ => e
               | _ => e)
```

Note that if there is an arity mismatch or if the arguments are not
concrete/constants, this fails and it returns .none.
If LFunc already has body, it must not have concreteEval, and vice versa.

(TODO) Use `.bvar`s in the body to correspond to the formals instead of using
`.fvar`s.
-/
structure Func (IdentT : Type) (ExprT : Type) (TyT : Type) (MetadataT : Type) where
  name     : IdentT
  typeArgs : List TyIdentifier := []
  isConstr : Bool := false --whether function is datatype constructor
  isRecursive : Bool := false
  inputs   : ListMap IdentT TyT
  output   : TyT
  body     : Option ExprT := .none
  -- Structured attributes controlling partial evaluator behavior (inlining, etc.)
  attr     : Array FuncAttr := #[]
  -- The MetadataT argument is the metadata that will be attached to the
  -- resulting expression of concreteEval if evaluation was successful.
  concreteEval : Option (MetadataT → List ExprT → Option ExprT) := .none
  axioms   : List ExprT := []  -- For axiomatic definitions
  preconditions : List (FuncPrecondition ExprT MetadataT) := []

def Func.format {IdentT ExprT TyT MetadataT : Type} [ToFormat IdentT] [ToFormat ExprT] [ToFormat TyT] [Inhabited ExprT] (f : Func IdentT ExprT TyT MetadataT) : Format :=
  let attr := if f.attr.isEmpty then f!"" else f!"@[{f.attr}]{Format.line}"
  let typeArgs : Format := if f.typeArgs.isEmpty
                  then f!""
                  else f!"∀{f.typeArgs}."
  -- Format inputs recursively like Signature.format
  let rec formatInputs (inputs : List (IdentT × TyT)) : Format :=
    match inputs with
    | [] => f!""
    | [(k, v)] => f!"({k} : {v})"
    | (k, v) :: rest => f!"({k} : {v}) " ++ formatInputs rest
  let type := f!"{typeArgs} ({formatInputs f.inputs}) → {f.output}"
  let preconds := f.preconditions.map (f!"  requires {·.expr}")
  let precondsStr := if preconds.isEmpty then f!"" else Format.line ++ Format.joinSep preconds Format.line
  let sep := if f.body.isNone then f!";" else f!" :="
  let body := if f.body.isNone then f!"" else Std.Format.indentD f!"({f.body.get!})"
  let recPrefix := if f.isRecursive then f!"rec " else f!""
  f!"{attr}\
     {recPrefix}func {f.name} : {type}{precondsStr}{sep}\
     {body}"

instance {IdentT ExprT TyT MetadataT : Type} [ToFormat IdentT] [ToFormat ExprT] [ToFormat TyT] [Inhabited ExprT] : ToFormat (Func IdentT ExprT TyT MetadataT) where
  format := Func.format

/--
Well-formedness properties of Func. These are split from Func because
otherwise it becomes impossible to create a 'temporary' Func object whose
wellformedness might not hold yet.

The `getName`, `getVarNames` and `getTyFreeVars` functions are used to extract
names from identifiers, expressions and types, allowing this structure to work
with different types.
-/
structure FuncWF {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String) (getVarNames : ExprT → List String)
    (getTyFreeVars : TyT → List String)
    (f : Func IdentT ExprT TyT MetadataT) where
  -- No args have same name.
  arg_nodup:
    List.Nodup (f.inputs.map (getName ·.1))
  -- Free variables of body must be arguments.
  body_freevars:
    ∀ b, f.body = .some b →
      getVarNames b ⊆ f.inputs.map (getName ·.1)
  -- concreteEval does not succeed if the length of args is incorrect.
  concreteEval_argmatch:
    ∀ fn md args res, f.concreteEval = .some fn
      → fn md args = .some res
      → args.length = f.inputs.length
  -- body and concreteEval cannot exist at once
  body_or_concreteEval:
    ¬ (f.concreteEval.isSome ∧ f.body.isSome)
  -- No typeArgs have same name
  typeArgs_nodup:
    List.Nodup f.typeArgs
  -- All type vars in input and output are in typeArg
  inputs_typevars_in_typeArgs:
    ∀ ty, ty ∈ f.inputs.values →
      getTyFreeVars ty ⊆ f.typeArgs
  output_typevars_in_typeArgs:
    getTyFreeVars f.output ⊆ f.typeArgs
  -- Free variables of preconditions must be arguments.
  precond_freevars:
    ∀ p, p ∈ f.preconditions →
      getVarNames p.expr ⊆ f.inputs.map (getName ·.1)

instance FuncWF.arg_nodup_decidable {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (List.Nodup (f.inputs.map (getName ·.1))) := by
  apply List.nodupDecidable

instance FuncWF.body_freevars_decidable {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String) (getVarNames : ExprT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (∀ b, f.body = .some b →
      getVarNames b ⊆ f.inputs.map (getName ·.1)) :=
  by exact f.body.decidableForallMem

-- FuncWF.concreteEval_argmatch is not decidable.

instance FuncWF.body_or_concreteEval_decidable
    {IdentT ExprT TyT MetadataT : Type}
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (¬ (f.concreteEval.isSome ∧ f.body.isSome)) := by
  exact instDecidableNot

instance FuncWF.typeArgs_decidable
    {IdentT ExprT TyT MetadataT : Type}
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (List.Nodup f.typeArgs) := by
  apply List.nodupDecidable

instance FuncWF.inputs_typevars_in_typeArgs_decidable
    {IdentT ExprT TyT MetadataT : Type}
    (getTyFreeVars : TyT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (∀ ty, ty ∈ f.inputs.values →
      getTyFreeVars ty ⊆ f.typeArgs) := by
  exact List.decidableBAll (fun x => getTyFreeVars x ⊆ f.typeArgs)
    (ListMap.values f.inputs)

instance FuncWF.output_typevars_in_typeArgs_decidable
    {IdentT ExprT TyT MetadataT : Type}
    (getTyFreeVars : TyT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (getTyFreeVars f.output ⊆ f.typeArgs) := by
  apply List.instDecidableRelSubsetOfDecidableEq

instance FuncWF.precond_freevars_decidable
    {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String) (getVarNames : ExprT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (∀ p, p ∈ f.preconditions →
      getVarNames p.expr ⊆ f.inputs.map (getName ·.1)) := by
  exact List.decidableBAll (fun x => getVarNames x.expr ⊆ f.inputs.map (getName ·.1))
    f.preconditions

end -- public section
end Strata.DL.Util

public section
/-! # List Utilities
-/

namespace List

theorem List.subset_append_cons_right {α : Type} [DecidableEq α] {a b c : List α} {x : α}
  (h : a ⊆ (b ++ c)) : a ⊆ b ++ (x :: c) := by
  simp_all [List.instHasSubset, List.Subset]
  intro e he
  have := @h e he
  cases this <;> simp_all
  done

/--
Remove duplicates in a list.
-/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as =>
    let as := as.dedup
    if a ∈ as then as else a :: as

/--
A deduplicated list satisfies `Nodup`.
-/
theorem nodup_dedup {α : Type} [DecidableEq α] (l : List α) :
  l.dedup.Nodup := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    simp [dedup]
    split
    · exact ih
    · rename_i h; constructor
      · exact fun a' a_1 => Ne.symm (ne_of_mem_of_not_mem a_1 h)
      · exact ih

/--
The upper bound of the length of a deduplicated list is the length of the
original list.
-/
theorem length_dedup_le {α : Type} [DecidableEq α] (l : List α) :
  l.dedup.length ≤ l.length := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    simp [dedup]
    split
    · exact Nat.le_succ_of_le ih
    · simp; exact ih

/--
The lower bound of the length of a deduplicated list with an element consed onto
it (i.e., `(a :: l)`) is the length of the deduplicated list `l`.
-/
theorem length_dedup_cons_le {α : Type} [DecidableEq α] (a : α) (l : List α) :
  l.dedup.length ≤ (a :: l).dedup.length := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    simp [dedup]
    split
    · exact ih
    · rename_i a' h
      simp_all
      by_cases a' = a
      · simp_all
      · by_cases a' ∈ as.dedup <;> simp_all

theorem mem_dedup_of_mem {α : Type} [DecidableEq α]
  (l : List α) (a : α) : a ∈ l.dedup → a ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons b bs ih =>
    simp [dedup]
    split
    · intro h
      exact Or.symm (Or.intro_left (a = b) (ih h))
    · intro h
      cases h with
      | head => exact Or.symm (Or.inr rfl)
      | tail _ h' => exact Or.symm (Or.intro_left (a = b) (ih h'))

theorem mem_of_mem_dedup {α : Type} [DecidableEq α]
  (l : List α) (a : α) : a ∈ l → a ∈ l.dedup := by
  induction l with
  | nil => simp [dedup]
  | cons b bs ih =>
    simp [dedup]
    intro h; cases h
    · subst a
      by_cases b ∈ bs.dedup <;> simp_all
    · by_cases b ∈ bs.dedup <;> simp_all

/--
An element `a` is in a list `l` iff it is in the deduplicated version
of `l`.
-/
theorem mem_of_dedup {α : Type} [DecidableEq α]
  (l : List α) (a : α) : a ∈ l ↔ a ∈ l.dedup := by
  apply Iff.intro
  exact fun h => mem_of_mem_dedup l a h
  exact fun h => mem_dedup_of_mem l a h

theorem length_dedup_cons_of_mem {α : Type} [DecidableEq α] (a : α) (l : List α)
  (h : a ∈ l) : (a :: l).dedup.length = l.dedup.length := by
  simp [dedup]
  have : a ∈ l.dedup := mem_of_mem_dedup l a h
  simp [this]

theorem length_dedup_cons_of_not_mem {α : Type} [DecidableEq α] (a : α) (l : List α)
  (h : a ∉ l) : (a :: l).dedup.length = 1 + l.dedup.length := by
  induction l
  · simp_all [dedup]
  · rename_i head tail ih
    simp_all [dedup]
    obtain ⟨h1, h2⟩ := h
    split
    · have := @mem_dedup_of_mem _ _ tail a
      simp_all
      omega
    · have := @mem_dedup_of_mem _ _ tail a
      simp_all
      omega

theorem mem_append_left_of_mem_dedup {α : Type} [DecidableEq α] (a : α) (l₁ l₂ : List α)
  (h1 : ¬a ∈ l₂.dedup) (h2 : a ∈ (l₁ ++ l₂).dedup) :
  a ∈ l₁ := by
  have := @mem_dedup_of_mem _ _ (l₁ ++ l₂) a (by assumption)
  have := @mem_dedup_of_mem _ _ l₂ a
  simp_all; cases this
  · assumption
  · have := @mem_of_mem_dedup _ _ l₂ a (by assumption)
    contradiction

theorem mem_append_right_of_mem_dedup {α : Type} [DecidableEq α] (a : α) (l₁ l₂ : List α)
  (h1 : ¬a ∈ l₁.dedup) (h2 : a ∈ (l₁ ++ l₂).dedup) :
  a ∈ l₂ := by
  have := @mem_dedup_of_mem _ _ (l₁ ++ l₂) a (by assumption)
  have := @mem_dedup_of_mem _ _ l₁ a
  simp_all; cases this
  · have := @mem_of_mem_dedup _ _ l₁ a (by assumption)
    contradiction
  · assumption

theorem length_dedup_append_le_sum {α : Type} [DecidableEq α] (l₁ l₂ : List α) :
  (l₁ ++ l₂).dedup.length ≤ l₁.dedup.length + l₂.dedup.length := by
  induction l₁ generalizing l₂
  · simp_all
  · rename_i head tail ih
    simp [dedup]
    by_cases h1 : head ∈ tail.dedup
    · have : head ∈ (tail ++ l₂).dedup := by
        have := @mem_dedup_of_mem _ _ tail head h1
        have := @mem_of_mem_dedup _ _ (tail ++ l₂) head
        simp_all
      simp_all
    · simp_all
      by_cases h2 : head ∈ l₂.dedup
      · have : head ∈ (tail ++ l₂).dedup := by
          have := @mem_dedup_of_mem _ _ l₂ head  h2
          have := @mem_of_mem_dedup _ _ (tail ++ l₂) head
          simp_all
        simp_all
        have := ih l₂
        omega
      · have : head ∉ (tail ++ l₂).dedup := by
          have := @mem_dedup_of_mem _ _ (tail ++ l₂) head
          intro h
          simp_all
          have := @mem_of_mem_dedup _ _ tail head
          have := @mem_of_mem_dedup _ _ l₂ head
          simp_all
        simp_all
        have := ih l₂
        omega

theorem removeAll_of_cons {α : Type} [DecidableEq α] (x : α) (xs ys : List α)
  (h : x ∉ ys) :
  ((x :: xs).removeAll ys) = x :: (xs.removeAll ys) := by
  induction xs
  case nil => simp_all [removeAll]
  case cons a as ih =>
    simp_all [removeAll]

theorem length_dedup_of_removeAll {α : Type} [DecidableEq α] (a : α) (l : List α)
  (h : a ∈ l) :
  l.dedup.length = 1 + (l.removeAll [a]).dedup.length := by
  induction l
  case nil => simp_all
  case cons x xs ih =>
    simp [dedup]
    simp at h
    by_cases h : a = x
    case pos =>
      subst a
      split
      · rename_i h_x_xs
        have : x ∈ xs := by exact (mem_of_dedup xs x).mpr h_x_xs
        have ih' := ih this
        simp_all [removeAll]
      · simp [removeAll]
        have : x ∉ xs := by
          have := @mem_of_dedup _ _ xs x
          simp_all
        have : (filter (fun x_1 => !decide (x_1 = x)) xs) = xs := by
          simp_all
          intro a ha
          exact ne_of_mem_of_not_mem ha this
        rw [this]
        omega
    case neg =>
      rename_i h_a_x_xs
      simp_all
      split
      · rename_i hx
        have := @removeAll_of_cons _ _ x xs [a]
        have h' : ¬x = a := by exact fun a_1 => h (id (Eq.symm a_1))
        simp [h'] at this
        rw [this]
        have := @length_dedup_cons_of_mem _ _ x (xs.removeAll [a])
        have : x ∈ xs.removeAll [a] := by
          simp [removeAll, h']
          exact (mem_of_dedup xs x).mpr hx
        simp_all
      · rename_i h_x_not_in_xs
        simp_all
        have := @removeAll_of_cons _ _ x xs [a]
        have h' : ¬x = a := by exact fun a_1 => h (id (Eq.symm a_1))
        simp [h'] at this
        rw [this]
        have := @length_dedup_cons_of_not_mem _ _ x (xs.removeAll [a])
        have : ¬ x ∈ xs.removeAll [a] := by
          simp [removeAll]
          have : x ∉ xs := by
            have := @mem_of_dedup _ _ xs x
            simp_all
          simp_all
        simp_all
        omega

theorem length_dedup_append_le_left {α : Type} [DecidableEq α] (l₁ l₂ : List α) :
  l₁.dedup.length ≤ (l₁ ++ l₂).dedup.length := by
  induction l₁ generalizing l₂
  case nil => simp [dedup]
  case cons a as ih =>
    simp [dedup]
    split
    · rename_i h
      have : a ∈ as := by exact (mem_of_dedup as a).mpr h
      have : a ∈ (as ++ l₂).dedup := by
        have : a ∈ as ++ l₂ := by simp_all
        exact (mem_of_dedup (as ++ l₂) a).mp this
      simp_all
    · by_cases ha : a ∈ (as ++ l₂).dedup
      case pos =>
        rename_i h_a_as
        simp_all
        have h_l2 : ∃ l, l = l₂.removeAll [a] := by simp_all
        obtain ⟨l, hl⟩ := h_l2
        simp_all
        have h_a_as_l2 : a ∈ as ++ l₂ := by exact (mem_of_dedup (as ++ l₂) a).mpr ha
        have h := @length_dedup_of_removeAll _ _ a (as ++ l₂) h_a_as_l2
        rw [h]
        have : ((as ++ l₂).removeAll [a]) = as ++ l := by
          simp [removeAll]
          have h_not_in_a_as : a ∉ as := by
            have := @mem_of_dedup _ _ as a
            simp_all
          have h_a_as : filter (fun x => !decide (x = a)) as = as := by
            simp_all
            intro a1 ha1
            exact ne_of_mem_of_not_mem ha1 h_not_in_a_as
          have h_a_l2 : filter (fun x => !decide (x = a)) l₂ = l := by
            rw [hl]
            simp [removeAll]
          simp_all
        rw [this]
        exact Nat.sub_le_iff_le_add'.mp (ih l)
      case neg =>
        simp_all

theorem length_dedup_append_all_in_right {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₁.all (fun e => e ∈ l₂)) :
  (l₁ ++ l₂).dedup.length = l₂.dedup.length := by
  induction l₁
  · simp_all
  · rename_i head tail ih
    simp_all
    obtain ⟨h1, h2⟩ := h
    have h1' : head ∈ tail ++ l₂ := by simp_all
    simp [@length_dedup_cons_of_mem _ _ head (tail ++ l₂) h1']
    induction tail <;> try simp
    rename_i x xrest ih
    simp_all [dedup]
    have : x ∈ (xrest ++ l₂) := by simp_all
    have : x ∈ (xrest ++ l₂).dedup := by
      exact @mem_of_mem_dedup _ _ (xrest ++ l₂) x (by assumption)
    simp_all
    done

theorem length_dedup_append_subset_right {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₁ ⊆ l₂) :
  (l₁ ++ l₂).dedup.length = l₂.dedup.length := by
  simp_all [List.instHasSubset, List.Subset]
  exact @length_dedup_append_all_in_right _ _ l₁ l₂ (by simp_all)

theorem length_dedup_append_all_in_left {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₂.all (fun e => e ∈ l₁)) :
  (l₁ ++ l₂).dedup.length = l₁.dedup.length := by
  induction l₂ generalizing l₁
  case nil => simp_all
  case cons x xs ih =>
    have h1 : (l₁ ++ x :: xs) = (l₁ ++ [x]) ++ xs := by exact append_cons l₁ x xs
    rw [h1]
    have ih' := ih (l₁ ++ [x])
    simp_all
    obtain ⟨hx, h_x_l1⟩ := h
    have h_1 := @length_dedup_of_removeAll _ _ x (l₁ ++ [x]) (by simp_all)
    have h_2 := @length_dedup_of_removeAll _ _ x (l₁) (by simp_all)
    have h_3 : ((l₁ ++ [x]).removeAll [x]) = l₁.removeAll [x] := by
      simp [removeAll]
    simp_all

theorem length_dedup_all_in_eq {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h1 : l₁.all (fun e => e ∈ l₂))
  (h2 : l₂.all (fun e => e ∈ l₁)) :
  l₁.dedup.length = l₂.dedup.length := by
  have h_1 := @length_dedup_append_all_in_right _ _ l₁ l₂ h1
  have h_2 := @length_dedup_append_all_in_left _ _ l₁ l₂ h2
  simp_all

theorem length_dedup_subset_eq {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h1 : l₁ ⊆ l₂) (h2 : l₂ ⊆ l₁) :
  l₁.dedup.length = l₂.dedup.length := by
  have := @length_dedup_all_in_eq _ _ l₁ l₂
  simp_all [List.instHasSubset, List.Subset]

theorem length_dedup_append_le_right {α : Type} [DecidableEq α] (l₁ l₂ : List α) :
  l₂.dedup.length ≤ (l₁ ++ l₂).dedup.length := by
  have h_left := @length_dedup_append_le_left _ _ l₂ l₁
  have := @length_dedup_all_in_eq _ _ (l₁ ++ l₂) (l₂ ++ l₁)
  simp_all

theorem length_dedup_of_all_in_not_mem_lt {α : Type} [DecidableEq α] (l₁ l₂ : List α) (a : α)
  (h1 : l₁.all (fun e => e ∈ l₂)) (h2 : a ∉ l₁) (h3 : a ∈ l₂) :
  l₁.dedup.length < l₂.dedup.length := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp_all [dedup]
    have : a ∈ l₂.dedup := by
      have := @mem_of_dedup _ _ l₂ a
      simp_all
    exact length_pos_of_mem this
  | cons head tail ih =>
    simp at h1 ih
    simp [dedup]
    obtain ⟨h1_head_l2, h1⟩ := h1
    split
    · rename_i h_head_tail
      exact @ih l₂ h1 (by simp_all) h3
    · rename_i h_head_not_in_tail
      have h_head_tail := @length_dedup_cons_of_not_mem _ _ head tail
      by_cases h_head_in_tail : head ∈ tail
      case pos =>
        simp_all [@mem_of_dedup _ _ tail head]
      case neg =>
        have h_removeAll := @length_dedup_of_removeAll _ _ head l₂ h1_head_l2
        simp_all
        obtain ⟨h_a_head, h_a_tail⟩ := h2
        have h1' : ∀ (x : α), x ∈ tail → x ∈ l₂.removeAll [head] := by
          intro x hx
          have h_x_not_head : ¬ x = head := by exact ne_of_mem_of_not_mem hx h_head_in_tail
          have h_x_in_l2 := @h1 x hx
          simp_all [removeAll]
        have h_a_l2 : a ∈ l₂.removeAll [head] := by
          simp_all [removeAll]
        have ih' := @ih (l₂.removeAll [head]) h1' h_a_l2
        omega
  done

theorem length_dedup_of_subset_not_mem_lt {α : Type} [DecidableEq α] (l₁ l₂ : List α) (a : α)
  (h1 : l₁ ⊆ l₂) (h2 : a ∉ l₁) (h3 : a ∈ l₂) :
  l₁.dedup.length < l₂.dedup.length := by
  have := @length_dedup_of_all_in_not_mem_lt _ _ l₁ l₂ a
  simp_all [List.instHasSubset, List.Subset]

theorem length_dedup_of_subset_le {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₁ ⊆ l₂) : l₁.dedup.length ≤ l₂.dedup.length := by
  induction l₁ with
  | nil => simp_all [dedup]
  | cons head tail ih =>
    have h_tail_l2 : tail ⊆ l₂ := by simp_all
    have ih' := @ih h_tail_l2
    by_cases h_head : head ∈ tail
    case pos =>
      have := @length_dedup_cons_of_mem _ _ head tail h_head
      exact le_of_eq_of_le this (ih h_tail_l2)
    case neg =>
      simp_all
      have := @length_dedup_of_subset_not_mem_lt _ _ tail l₂ head h_tail_l2 h_head h
      have h_head_dedup : head ∉ tail.dedup := by
        have := @mem_of_dedup _ _ tail head
        simp_all
      simp_all [dedup]
      omega

theorem subset_nodup_length {α} {s1 s2: List α} (hn: s1.Nodup) (hsub: s1 ⊆ s2) : s1.length ≤ s2.length := by
  induction s1 generalizing s2 with
  | nil => simp
  | cons x t IH =>
    simp only[List.length]
    have xin: x ∈ s2 := by apply hsub; grind
    rw[List.mem_iff_append] at xin
    rcases xin with ⟨l1, ⟨l2, hs2⟩⟩; subst_vars
    have hsub1: t ⊆ (l1 ++ l2) := by grind
    grind


/-- Deduplicates l and counts the number of occurrences for each element. -/
def occurrences {α : Type} [DecidableEq α] (l : List α) : List (α × Nat) :=
  l.dedup.map (λ x => (x, l.count x))

theorem occurrences_len_eq_dedup {α} [DecidableEq α]:
  ∀ (l : List α), l.dedup.length = l.occurrences.length := by
  intros l
  unfold occurrences
  grind

theorem occurrences_find {α} [DecidableEq α] (l : List α) (x : α)
  (hx : x ∈ l)
  : l.occurrences.find? (fun ⟨k, _⟩ => k == x) = .some (x, l.count x) := by
  simp only [occurrences, find?_map, Option.map_eq_some_iff, Prod.mk.injEq]
  have : x ∈ l.dedup := by induction l <;> grind [dedup]
  generalize l.dedup = ld at *
  induction ld <;> simp [List.find?, Function.comp_apply] <;>
    (first | grind | split <;> grind)

/--
`foldlIdx f init l` folds `f` over `l` with an index.
-/
def foldlIdx (f : β → Nat → α → β) (init : β) (l : List α) : β :=
  ((List.range l.length).zip l).foldl (fun acc (i, a) => f acc i a) init

/-- If `P x → Q x` for all `x ∈ L`, then `(L.filter P).length ≤ (L.filter Q).length`. -/
theorem filter_length_le_of_imp {L : List α} {P Q : α → Bool}
    (h_imp : ∀ x ∈ L, P x = true → Q x = true) :
    (L.filter P).length ≤ (L.filter Q).length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun y hy => h_imp y (.tail x hy))
    simp only [List.filter]
    cases hPx : P x <;> cases hQx : Q x
    · exact ih'
    · simp; omega
    · have := h_imp x (.head xs) hPx; simp_all
    · simp; omega

/-- If `P x → Q x` for all `x ∈ L`, and there is a witness `a ∈ L` with `Q a` but `¬P a`,
    then `(L.filter P).length < (L.filter Q).length`. -/
theorem filter_length_lt_of_imp_witness {L : List α} {P Q : α → Bool}
    {a : α}
    (h_imp : ∀ x ∈ L, P x = true → Q x = true)
    (h_in : a ∈ L) (hQa : Q a = true) (hPa : ¬(P a = true)) :
    (L.filter P).length < (L.filter Q).length := by
  induction L with
  | nil => nomatch h_in
  | cons y ys ih =>
    have h_imp_ys : ∀ z ∈ ys, P z = true → Q z = true :=
      fun z hz => h_imp z (.tail y hz)
    simp only [List.filter]
    cases h_in with
    | head =>
      have hPa_false : P a = false := by
        cases h : P a
        · rfl
        · exact absurd h hPa
      simp only [hPa_false, hQa, List.length_cons]
      have := filter_length_le_of_imp h_imp_ys
      omega
    | tail _ h_in_ys =>
      cases hPy : P y <;> cases hQy : Q y
      · exact ih h_imp_ys h_in_ys
      · simp; have := ih h_imp_ys h_in_ys; omega
      · have := h_imp y (.head ys) hPy; simp_all
      · simp; have := ih h_imp_ys h_in_ys; omega

/-- If every element of `xs` is in `ys`, then `xs.removeAll ys = []`. -/
theorem removeAll_eq_nil_of_forall_mem [BEq α] [LawfulBEq α]
    {xs ys : List α} (h : ∀ x, x ∈ xs → x ∈ ys) :
    xs.removeAll ys = [] := by
  simp only [List.removeAll]
  rw [List.filter_eq_nil_iff]
  grind

theorem removeAll_not_mem [BEq α] [LawfulBEq α] {x : α} {xs : List α}
    (h : x ∉ xs) : xs.removeAll [x] = xs := by
  simp only [List.removeAll]
  rw [List.filter_eq_self]
  intro a ha
  simp only [List.elem_cons, List.elem_nil]
  split <;> simp_all

end List
end


/-!
## Lambda's Factory

This module formalizes Lambda's _factory_, which is a mechanism to extend the
type checker (see `Strata.DL.Lambda.LExprT`) and partial evaluator (see
`Strata.DL.Lambda.LExprEval`) by providing a map from operations to their types
and optionally, denotations. The factory allows adding type checking and
evaluation support for new operations without modifying the implementation of
either or any core ASTs.

Also see `Strata.DL.Lambda.IntBoolFactory` for a concrete example of a factory.
-/


namespace Lambda
open Strata
open Std (ToFormat Format format)

public section

variable {T : LExprParams} [Inhabited T.Metadata] [ToFormat T.IDMeta]

---------------------------------------------------------------------

open LTy.Syntax

section Factory

variable {IDMeta : Type} [DecidableEq IDMeta] [Inhabited IDMeta]

/--
A signature is a map from variable identifiers to types.
-/
@[expose] abbrev Signature (IDMeta : Type) (Ty : Type) := ListMap (Identifier IDMeta) Ty

def Signature.format (ty : Signature IDMeta Ty) [Std.ToFormat Ty] : Std.Format :=
  match ty with
  | [] => ""
  | [(k, v)] => f!"({k} : {v})"
  | (k, v) :: rest =>
    f!"({k} : {v}) " ++ Signature.format rest

@[expose] abbrev LMonoTySignature := Signature IDMeta LMonoTy

@[expose] abbrev LTySignature := Signature IDMeta LTy

-- Re-export Func from Util for backward compatibility
open Strata.DL.Util (Func FuncPrecondition TyIdentifier)

/--
A Lambda factory function - instantiation of `Func` for Lambda expressions.

Universally quantified type identifiers, if any, appear before this signature and can
quantify over the type identifiers in it.
-/
@[expose] abbrev LFunc (T : LExprParams) := Func (T.Identifier) (LExpr T.mono) LMonoTy T.Metadata

/--
Helper constructor for LFunc to maintain backward compatibility.
-/
def LFunc.mk {T : LExprParams} (name : T.Identifier) (typeArgs : List TyIdentifier := [])
    (isConstr : Bool := false) (isRecursive : Bool := false)
    (inputs : ListMap T.Identifier LMonoTy) (output : LMonoTy)
    (body : Option (LExpr T.mono) := .none) (attr : Array Strata.DL.Util.FuncAttr := #[])
    (concreteEval : Option (T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) := .none)
    (axioms : List (LExpr T.mono) := [])
    (preconditions : List (FuncPrecondition (LExpr T.mono) T.Metadata) := []) : LFunc T :=
  Func.mk name typeArgs isConstr isRecursive inputs output body attr concreteEval axioms preconditions

instance [Inhabited T.Metadata] [Inhabited T.IDMeta] : Inhabited (LFunc T) where
  default := { name := Inhabited.default, inputs := [], output := LMonoTy.bool }

-- Provide explicit instance for LFunc to ensure proper resolution
instance [ToFormat T.IDMeta] [Inhabited T.Metadata] : ToFormat (LFunc T) where
  format := Func.format

def LFunc.type [DecidableEq T.IDMeta] (f : (LFunc T)) : Except Format LTy := do
  if !(decide f.inputs.keys.Nodup) then
    .error f!"[{f.name}] Duplicates found in the formals!\
              {Format.line}\
              {f.inputs}"
  else if !(decide f.typeArgs.Nodup) then
    .error f!"[{f.name}] Duplicates found in the universally \
              quantified type identifiers!\
              {Format.line}\
              {f.typeArgs}"
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  match input_tys with
  | [] => .ok (.forAll f.typeArgs f.output)
  | ity :: irest =>
    .ok (.forAll f.typeArgs (Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)))

omit [Inhabited T.Metadata] [ToFormat T.IDMeta] in
theorem LFunc.type_inputs_nodup [DecidableEq T.IDMeta] (f : LFunc T) (ty : LTy) :
    f.type = .ok ty → f.inputs.keys.Nodup := by
  intro h
  simp only [LFunc.type, bind, Except.bind] at h
  -- At this point grind is possible if this proof needs maintenance
  split at h <;> try contradiction
  simp_all

def LFunc.opExpr [Inhabited T.Metadata] (f: LFunc T) : LExpr T.mono :=
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  let ty := match input_tys with
            | [] => f.output
            | ity :: irest => Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)
  .op (default : T.Metadata) f.name (some ty)

def LFunc.inputPolyTypes (f : (LFunc T)) : @LTySignature T.IDMeta :=
  f.inputs.map (fun (id, mty) => (id, .forAll f.typeArgs mty))

def LFunc.outputPolyType (f : (LFunc T)) : LTy :=
  .forAll f.typeArgs f.output

def LFunc.eraseTypes (f : LFunc T) : LFunc T :=
  { f with
    body := f.body.map LExpr.eraseTypes,
    axioms := f.axioms.map LExpr.eraseTypes,
    preconditions := f.preconditions.map fun p => { p with expr := p.expr.eraseTypes }
  }

/--
The type checker and partial evaluator for Lambda is parameterizable by
a user-provided `Factory`.

We don't have any "built-in" functions like `+`, `-`, etc. in `(LExpr
IDMeta)` -- lambdas are our only tool. `Factory` gives us a way to add
support for concrete/symbolic evaluation and type checking for `FunFactory`
functions without actually modifying any core logic or the ASTs.
-/
@[expose] def Factory (T : LExprParams) := Array (LFunc T)

def Factory.default : @Factory T := #[]

instance : Inhabited (@Factory T) where
  default := @Factory.default T

instance : Membership (LFunc T) (@Factory T) where
  mem x f := Array.Mem x f


def Factory.getFunctionNames (F : @Factory T) : Array T.Identifier :=
  F.map (fun f => f.name)

def Factory.getFactoryLFunc (F : @Factory T) (name : String) : Option (LFunc T) :=
  F.find? (fun fn => fn.name.name == name)

/--
Add a function `func` to the factory `F`. Redefinitions are not allowed.
-/
def Factory.addFactoryFunc (F : @Factory T) (func : LFunc T) : Except DiagnosticModel (@Factory T) :=
  match F.getFactoryLFunc func.name.name with
  | none => .ok (F.push func)
  | some func' =>
    .error <| DiagnosticModel.fromFormat f!"A function of name {func.name} already exists! \
              Redefinitions are not allowed.\n\
              Existing Function: {func'}\n\
              New Function:{func}"


/--
Append a factory `newF` to an existing factory `F`, checking for redefinitions
along the way.
-/
def Factory.addFactory (F newF : @Factory T) : Except DiagnosticModel (@Factory T) :=
  Array.foldlM (fun factory func => factory.addFactoryFunc func) F newF


@[expose] def getLFuncCall {GenericTy} (e : LExpr ⟨T, GenericTy⟩) : LExpr ⟨T, GenericTy⟩ × List (LExpr ⟨T, GenericTy⟩) :=
  go e []
  where go e (acc : List (LExpr ⟨T, GenericTy⟩)) :=
  match e with
  | .app _ (.app _ e' arg1) arg2 =>  go e' ([arg1, arg2] ++ acc)
  | .app _ (.op m fn  fnty) arg1 =>  ((.op m fn fnty), ([arg1] ++ acc))
  | _ => (e, acc)

def getConcreteLFuncCall (e : LExpr ⟨T, GenericTy⟩) : LExpr ⟨T, GenericTy⟩ × List (LExpr ⟨T, GenericTy⟩) :=
  let (op, args) := getLFuncCall e
  if args.all (@LExpr.isConst ⟨T, GenericTy⟩) then (op, args) else (e, [])

/--
If `e` is a call of a factory function, get the operator (`.op`), a list
of all the actuals, and the `(LFunc IDMeta)`.
-/
def Factory.callOfLFunc {GenericTy} (F : @Factory T) (e : LExpr ⟨T, GenericTy⟩)
    (allowPartialApp := false)
    : Option (LExpr ⟨T, GenericTy⟩ × List (LExpr ⟨T, GenericTy⟩) × LFunc T) :=
  let (op, args) := getLFuncCall e
  match op with
  | .op _ name _ =>
    let maybe_func := getFactoryLFunc F name.name
    match maybe_func with
    | none => none
    | some func =>
      -- Note that we don't do any type or well-formedness checking here; this
      -- is just a simple arity check.
      let matchesArg:Bool :=
        if allowPartialApp then Nat.ble args.length func.inputs.length
        else args.length == func.inputs.length
      match matchesArg with
      | true => (op, args, func) | false => none
  | _ => none

end Factory

theorem getLFuncCall.go_size {T: LExprParamsT} {e: LExpr T} {op args acc} : getLFuncCall.go e acc = (op, args) →
op.sizeOf + List.sum (args.map LExpr.sizeOf) <= e.sizeOf + List.sum (acc.map LExpr.sizeOf) := by
  fun_induction go generalizing op args
  case case1 acc e' arg1 arg2 IH =>
    intros Hgo; specialize (IH Hgo); simp_all; omega
  case case2 acc fn fnty arg1 =>
    simp_all; intros op_eq args_eq; subst op args; simp; omega
  case case3 op' args' _ _ => intros Hop; cases Hop; omega

theorem LExpr.sizeOf_pos {T} (e: LExpr T): 0 < sizeOf e := by
  cases e<;> simp <;> omega

theorem List.sum_size_le (f: α → Nat) {l: List α} {x: α} (x_in: x ∈ l): f x ≤ List.sum (l.map f) := by
  induction l; simp_all; grind

theorem getLFuncCall_smaller {T} {e: LExpr T} {op args} : getLFuncCall e = (op, args) → (forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  unfold getLFuncCall; intros Hgo; have Hsize := (getLFuncCall.go_size Hgo);
  simp_all; have Hop:= LExpr.sizeOf_pos op; intros a a_in;
  have Ha := List.sum_size_le LExpr.sizeOf a_in; omega

theorem Factory.callOfLFunc_smaller {T} {F : @Factory T.base} {e : LExpr T} {op args F'}
    {allowPartialMatch}
    : Factory.callOfLFunc F e (allowPartialApp := allowPartialMatch) = some (op, args, F') →
  (forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  simp[Factory.callOfLFunc]; cases Hfunc: (getLFuncCall e) with | mk op args;
  simp; cases op <;> simp
  rename_i o ty; cases (F.getFactoryLFunc o.name) <;> simp
  rename_i F'
  cases allowPartialMatch
  · cases (args.length == List.length F'.inputs) <;> simp; intros op_eq args_eq F_eq
    subst op args F'; exact (getLFuncCall_smaller Hfunc)
  · cases (Nat.ble args.length (List.length F'.inputs)) <;> simp
    intros op_eq args_eq F_eq
    subst op args F'; exact (getLFuncCall_smaller Hfunc)

end -- public section
end Lambda

namespace Lambda

open Std (ToFormat Format format)

public section

---------------------------------------------------------------------

/-! ### Variable scopes

We keep a stack of `Scopes`, where we map in-scope free variables to the
`LExpr` values.

While the evaluation of Lambda expressions does not strictly need the notion of
scopes, other dialects that include Lambda may need to do so. For the evaluation
of Lambda expressions in isolation, the stack can contain a single scope.
-/

variable {T : LExprParams} [Inhabited T.Metadata] [BEq T.Metadata] [DecidableEq T.IDMeta] [BEq T.IDMeta] [ToFormat T.IDMeta] [BEq (LExpr T.mono)] [ToFormat (LExpr T.mono)]

@[expose] def Scope (T : LExprParams) : Type := Map T.Identifier (Option LMonoTy × (LExpr T.mono))

@[expose] def Scope.ofMap (m : Map T.Identifier (Option LMonoTy × (LExpr T.mono))) : Scope T := m
@[expose] def Scope.toMap (s : Scope T) : Map T.Identifier (Option LMonoTy × (LExpr T.mono)) := s

instance : BEq (Scope T) where
  beq m1 m2 := m1.toMap == m2.toMap

instance : Inhabited (Scope T) where
  default := Scope.ofMap []

private def Scope.format (m : Scope T) : Std.Format :=
  match m with
  | [] => ""
  | [(k, (ty, v))] => go k ty v
  | (k, (ty, v)) :: rest =>
    go k ty v ++ Format.line ++ Scope.format rest
  where go k ty v :=
    match ty with
    | some ty => f!"({k} : {ty}) → {v}"
    | none => f!"{k} → {v}"

instance (priority := high) : ToFormat (Scope T) where
  format := private Scope.format

/--
Merge two maps `m1` and `m2`, where `m1` is assumed to be the map if `cond`
is `true` and `m2` when it is false.
-/
def Scope.merge (cond : LExpr T.mono) (m1 m2 : Scope T) : Scope T :=
  match m1 with
  | [] => m2.map (fun (i, (ty, e)) => (i, (ty, mkIte cond (.fvar (default : T.Metadata) i ty) e)))
  | (k, (ty1, e1)) :: rest =>
    match m2.find? k with
    | none =>
      (k, (ty1, mkIte cond e1 (.fvar (default : T.Metadata) k ty1))) ::
      Scope.merge cond rest m2
    | some (ty2, e2) =>
      if ty1 ≠ ty2 then
        panic! s!"[Scope.merge] Variable {Std.format k} is of two different types \
                  in the two varMaps\n\
                  {Std.format m1}\n{Std.format m2}"
      else
        (k, (ty1, mkIte cond e1 e2)) ::
      Scope.merge cond rest (m2.erase k)
  where mkIte (cond tru fals : LExpr T.mono) : LExpr T.mono :=
    if tru == fals then tru
    else (LExpr.ite (default : T.Metadata) cond tru fals)



/--
A stack of scopes, where each scope maps the free variables
to their `LExpr` values.
-/
@[expose] abbrev Scopes (T : LExprParams) := Maps T.Identifier (Option LMonoTy × LExpr T.mono)

/--
Merge two scopes, where `s1` is assumed to be the scope if `cond` is true, and
`s2` otherwise.
-/
def Scopes.merge (cond : LExpr T.mono) (s1 s2 : Scopes T) : Scopes T :=
  match s1, s2 with
  | [], _ => s2
  | _, [] => s1
  | x :: xrest, y :: yrest =>
    Scope.merge cond x y :: Scopes.merge cond xrest yrest

--------------------------------------------------------------------

end -- public section
end Lambda


/-! ## State for (Partial) Evaluation of Lambda Expressions

See `Strata.DL.Lambda.LExprEval` for the partial evaluator.
-/

namespace Lambda
open Strata
open Std (ToFormat Format format)

public section

variable {T : LExprParams} [Inhabited T.Metadata] [BEq T.Metadata] [DecidableEq T.IDMeta] [BEq T.IDMeta] [ToFormat T.IDMeta] [ToFormat (LFunc T)] [ToFormat (Scopes T)] [Inhabited (LExpr T.mono)]
---------------------------------------------------------------------

/-
Configuration for symbolic execution, where we have `gen` for keeping track of
fresh `fvar`'s numbering. We also have a `fuel` argument for the evaluation
function, and support for factory functions.

We rely on the parser disallowing Lambda variables to begin with `$__`, which is
reserved for internal use. Also see `TEnv.genExprVar` used during type inference
and `LState.genVar` used during evaluation.
-/
structure EvalConfig (T : LExprParams) where
  factory : @Factory T
  fuel : Nat := 200
  varPrefix : String := "$__"
  gen : Nat := 0

instance : ToFormat (EvalConfig T) where
  format c :=
    f!"Eval Depth: {(repr c.fuel)}" ++ Format.line ++
    f!"Variable Prefix: {c.varPrefix}" ++ Format.line ++
    f!"Variable gen count: {c.gen}" ++ Format.line ++
    f!"Factory Functions:" ++ Format.line ++
    Std.Format.joinSep c.factory.toList f!"{Format.line}"

def EvalConfig.init : EvalConfig T :=
  { factory := @Factory.default T,
    fuel := 200,
    gen := 0 }

def EvalConfig.incGen (c : EvalConfig T) : EvalConfig T :=
    { c with gen := c.gen + 1 }

def EvalConfig.genSym (x : String) (c : EvalConfig T) : String × EvalConfig T :=
  let new_idx := c.gen
  let c := c.incGen
  let new_var := c.varPrefix ++ x ++ toString new_idx
  (new_var, c)

---------------------------------------------------------------------

/-- The Lambda evaluation state. -/
structure LState (T : LExprParams) where
  config : EvalConfig T
  state : Scopes T

-- scoped notation (name := lstate) "Σ" => LState

def LState.init : LState T :=
  { state := [],
    config := EvalConfig.init }

/-- An empty `LState` -/
instance : EmptyCollection (LState T) where
  emptyCollection := LState.init

instance : Inhabited (LState T) where
  default := LState.init

instance : ToFormat (LState T) where
  format s :=
    let { state, config }  := s
    format f!"State:{Format.line}{state}{Format.line}{Format.line}\
              Evaluation Config:{Format.line}{config}{Format.line}\
              {Format.line}"

/--
Add function `func` to the existing factory of functions in `σ`. Redefinitions
are not allowed.
-/
def LState.addFactoryFunc (σ : LState T) (func : (LFunc T)) : Except DiagnosticModel (LState T) := do
  let F ← σ.config.factory.addFactoryFunc func
  .ok { σ with config := { σ.config with factory := F }}

/--
Append `Factory f` to the existing factory of functions in `σ`, checking for
redefinitions.
-/
def LState.addFactory (σ : (LState T)) (F : @Factory T) : Except DiagnosticModel (LState T) := do
  let oldF := σ.config.factory
  let newF ← oldF.addFactory F
  .ok { σ with config := { σ.config with factory := newF } }

/--
Replace the `factory` field of σ with F.
-/
def LState.setFactory (σ : (LState IDMeta)) (F : @Factory IDMeta)
    : (LState IDMeta) :=
  { σ with config := { σ.config with factory := F } }

/--
Get all the known variables from the scopes in state `σ`.
-/
def LState.knownVars (σ : LState T) : List T.Identifier :=
  go σ.state []
  where go (s : Scopes T) (acc : List T.Identifier) :=
  match s with
  | [] => acc
  | m :: rest => go rest (acc ++ m.keys)

/--
Generate a fresh (internal) identifier with the base name
`x`; i.e., `σ.config.varPrefix ++ x`.
-/
def LState.genVar {IDMeta} [Inhabited IDMeta] [DecidableEq IDMeta] (x : String) (σ : LState ⟨Unit, IDMeta⟩) : String × LState ⟨Unit, IDMeta⟩ :=
  let (new_var, config) := σ.config.genSym x
  let σ := { σ with config := config }
  let known_vars := LState.knownVars σ
  let new_var := ⟨ new_var, Inhabited.default  ⟩
  if new_var ∈ known_vars then
    panic s!"[LState.genVar] Generated variable {new_var} is not fresh!\n\
             Known variables: {known_vars}"
  else
    (new_var.name, σ)

/--
Generate fresh identifiers, each with the base name in `xs`.
-/
def LState.genVars (xs : List String) (σ : (LState ⟨Unit, Unit⟩)) : (List String × (LState ⟨Unit, Unit⟩)) :=
  let (vars, σ') := go xs σ []
  (vars.reverse, σ')
  where go (xs : List String) (σ : LState ⟨Unit, Unit⟩) (acc : List String) :=
    match xs with
    | [] => (acc, σ)
    | x :: rest =>
      let (x', σ) := LState.genVar x σ
      go rest σ (x' :: acc)

instance : ToFormat (T.Identifier × LState T) where
  format im :=
    f!"New Variable: {im.fst}{Format.line}\
       Gen in EvalConfig: {im.snd.config.gen}{Format.line}\
       {im.snd}"

---------------------------------------------------------------------

/--
Substitute `.fvar`s in `e` by looking up their values in `σ`.
-/
@[expose] def LExpr.substFvarsFromState (σ : (LState T)) (e : (LExpr T.mono)) : (LExpr T.mono) :=
  let sm := σ.state.toSingleMap.map (fun (x, (_, v)) => (x, v))
  Lambda.LExpr.substFvars e sm

---------------------------------------------------------------------

end -- public section
end Lambda

/-! ## Partial evaluator for Lambda expressions

See function `Lambda.LExpr.eval` for the implementation.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)
open Strata.DL.Util (FuncAttr)

public section

namespace LExpr

variable {T : LExprParamsT} {TBase : LExprParams} [BEq T.TypeType] [DecidableEq T.base.Metadata] [DecidableEq TBase.IDMeta] [ToFormat T.base.Metadata]
         [Inhabited T.base.IDMeta] [DecidableEq T.base.IDMeta] [ToFormat T.base.IDMeta] [Traceable EvalProvenance TBase.Metadata]

inductive EvalProvenance
  | Original -- The metadata of the original expression
  | ReplacementVar -- The original bound variable that was replaced
  | Abstraction -- The lambda that triggered the replacement

/--
Check for boolean equality of two expressions `e1` and `e2` after erasing any
type annotations.
-/
def eqModuloTypes (e1 e2 : LExpr T) : Bool :=
  e1.eraseMetadata.eraseTypes == e2.eraseMetadata.eraseTypes

/--
Canonical values of `LExpr`s.

Equality is simply `==` (or more accurately, `eqModuloTypes`) for these
`LExpr`s. Also see `eql` for a version that can tolerate nested metadata.

If `e:LExpr` is `.app`, say `e1 e2 .. en`, `e` is a canonical value if
(1) `e1` is a constructor and `e2 .. en` are all canonical values, or
(2) `e1` is a named function `f` (not abstraction) and `n` is less than the
    number of arguments required to run the function `f`.

The intuition of case (2) is as follows. Let's assume that we would like to
calculate `Int.Add 1 (2+3)`. According to the small step semantics, we would
like to calculate `2+3` to `5`, hence it becomes `Int.Add 1 5` and eventually 6.
Without (2), this is impossible because the `reduce_2` rule of small step
semantics only fires when `Int.Add 1` is a 'canonical value'. Therefore, without
(2), the semantics stuck and `2+3` can never be evaluated to `5`.
-/
def isCanonicalValue (F : @Factory T.base) (e : LExpr T) : Bool :=
  match he: e with
  | .const _ _ => true
  | .abs _ _ _ _ | .quant _ _ _ _ _ _ =>
    -- We're using the locally nameless representation, which guarantees that
    -- `closed (.abs e) = closed e` (see theorem `closed_abs`).
    -- So we could simplify the following to `closed e`, but leave it as is for
    -- clarity.
    LExpr.closed e
  | e' =>
    match h: Factory.callOfLFunc F e true with
    | some (_, args, f) =>
      (f.isConstr || Nat.blt args.length f.inputs.length) &&
      List.all (args.attach.map (fun ⟨ x, _⟩ =>
        have : x.sizeOf < e'.sizeOf := by
          have Hsmall := Factory.callOfLFunc_smaller h; grind
        (isCanonicalValue F x))) id
    | none => false
  termination_by e.sizeOf

/--
Check if `e` is a constructor application.
-/
def isConstrApp (F : @Factory T.base) (e : LExpr T) : Bool :=
  match Factory.callOfLFunc F e true with
  | some (_, _, f) => f.isConstr
  | none => false

/--
Equality of canonical values `e1` and `e2`.

We can tolerate nested metadata here.
-/
def eql (F : @Factory T.base) (e1 e2 : LExpr T)
  (_h1 : isCanonicalValue F e1) (_h2 : isCanonicalValue F e2) : Bool :=
  if eqModuloTypes e1 e2 then
    true
  else
    eqModuloTypes e1 e2

instance [ToFormat T.TypeType]: ToFormat (Except Format (LExpr T)) where
  format x := match x with
              | .ok e => format e
              | .error err => err

instance [ToFormat T.TypeType]: ToFormat (Except Strata.DiagnosticModel (LExpr T)) where
  format x := match x with
              | .ok e => format e
              | .error err => f!"{err.message}"

/--
Embed `core` in an abstraction whose depth is `arity`. Used to implement
eta-expansion.

E.g., `mkAbsOfArity 2 core` will give `λxλy ((core y) x)`.
-/
def mkAbsOfArity (arity : Nat) (core : LExpr T) : (LExpr T) :=
  go 0 arity core
  where go (bvarcount arity : Nat) (core : LExpr T) : (LExpr T) :=
  match arity with
  | 0 => core
  | n + 1 =>
    go (bvarcount + 1) n (.abs core.metadata "" .none (.app core.metadata core (.bvar core.metadata bvarcount)))

/--
A metadata merger. It will be invoked 'subst s e' is invoked, to create a new
metadata.
-/
def mergeMetadataForSubst (metaAbs metaE2 metaReplacementVar: TBase.Metadata) :=
  Traceable.combine
  [(EvalProvenance.Original,       metaE2),
    (EvalProvenance.ReplacementVar, metaReplacementVar),
    (EvalProvenance.Abstraction,    metaAbs)]


mutual
/--
(Partial) evaluator for Lambda expressions w.r.t. a module, written using a fuel
argument.

Note that this function ascribes Curry-style semantics to `LExpr`s, i.e., we
can evaluate ill-typed terms w.r.t. a given type system here.

We prefer Curry-style semantics because they separate the type system from
evaluation, allowing us to potentially apply different type systems with our
expressions, along with supporting dynamically-typed languages.

Currently evaluator only supports LExpr with LMonoTy because LFuncs registered
at Factory must have LMonoTy.
-/
def eval (n : Nat) (σ : LState TBase) (e : (LExpr TBase.mono))
    : LExpr TBase.mono :=
  match n with
  | 0 => e
  | n' + 1 =>
    if isCanonicalValue σ.config.factory e then
      e
    else
      -- Special handling for Factory functions.
      match σ.config.factory.callOfLFunc e with
      | some (op_expr, args, lfunc) =>
        let args := args.map (fun a => eval n' σ a)
        let constrArgAt (idx : Option Nat) :=
          match idx with
          | some i => (args[i]? |>.map (isConstrApp σ.config.factory)).getD false
          | none => false
        if h: lfunc.body.isSome && (lfunc.attr.contains .inline ||
          constrArgAt (FuncAttr.findInlineIfConstr lfunc.attr)) then
          -- Inline a function only if it has a body.
          let body := lfunc.body.get (by simp_all)
          let input_map := lfunc.inputs.keys.zip args
          let new_e := substFvars body input_map
          eval n' σ new_e
        else
          let new_e := @mkApp TBase.mono e.metadata op_expr args
            -- All arguments in the function call are concrete.
            -- We can, provided a denotation function, evaluate this function
            -- call.
          if args.all (isCanonicalValue σ.config.factory) ||
            -- Other functions (e.g. Eliminators) only require the designated
            -- arg to be a constructor
            constrArgAt (FuncAttr.findEvalIfConstr lfunc.attr) then
            match lfunc.concreteEval with
            | none => new_e
            | some ceval =>
              match ceval new_e.metadata args with
              | .some e' => eval n' σ e'
              | .none => new_e
          else
            -- At least one argument in the function call is symbolic.
            new_e
      | none =>
        -- Not a call of a factory function - go through evalCore
        evalCore n' σ e

def evalCore  (n' : Nat) (σ : LState TBase) (e : LExpr TBase.mono) : LExpr TBase.mono :=
  match e with
  | .const _ _  => e
  | .op _ _ _     => e
  | .bvar _ _     => e
  | .fvar _ x ty  => (σ.state.findD x (ty, e)).snd
   -- Note: closed .abs terms are canonical values; we'll be here if .abs
   -- contains free variables.
  | .abs _ _ _ _   => LExpr.substFvarsFromState σ e
  | .quant _ _ _ _ _ _ => LExpr.substFvarsFromState σ e
  | .app _ e1 e2 => evalApp n' σ e e1 e2
  | .eq m e1 e2 => evalEq n' σ m e1 e2
  | .ite m c t f => evalIte n' σ m c t f

-- Note: this evaluation is eager -- both branches are fully evaluated even when
-- the condition is not resolved to true/false. This was originally lazy (only
-- substituting free variables via `substFvarsFromState`), but we switched to
-- eager evaluation to support recursive functions, where the branches may
-- contain recursive calls that need to be unfolded. If we ever need a lazy mode
-- again, we should add a flag.
def evalIte (n' : Nat) (σ : LState TBase) (m: TBase.Metadata) (c t f : LExpr TBase.mono) : LExpr TBase.mono :=
  let c' := eval n' σ c
  match c' with
  | .true _ => eval n' σ t
  | .false _ => eval n' σ f
  | _ =>
    let t' := eval n' σ t
    let f' := eval n' σ f
    .ite m c' t' f'

def evalEq (n' : Nat) (σ : LState TBase) (m: TBase.Metadata) (e1 e2 : LExpr TBase.mono) : LExpr TBase.mono :=
  open LTy.Syntax in
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  if eqModuloTypes e1'.eraseMetadata e2'.eraseMetadata then
    -- Short-circuit: e1' and e2' are syntactically the same after type erasure.
    LExpr.true m
  else if h: isCanonicalValue σ.config.factory e1' ∧
             isCanonicalValue σ.config.factory e2' then
    if eql σ.config.factory e1' e2' h.left h.right then
      LExpr.true m
    else LExpr.false m
  else
    .eq m e1' e2'

def evalApp (n' : Nat) (σ : LState TBase) (e e1 e2 : LExpr TBase.mono) : LExpr TBase.mono :=
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  match e1' with
  | .abs mAbs _ _ e1' =>
    let e' := subst (fun metaReplacementVar =>
      let newMeta := mergeMetadataForSubst mAbs e2'.metadata metaReplacementVar
      replaceMetadata1 newMeta e2') e1'
    if eqModuloTypes e e' then e else eval n' σ e'
  | .op m fn _ =>
    match σ.config.factory.getFactoryLFunc fn.name with
    | none => LExpr.app m e1' e2'
    | some lfunc =>
      let e' := LExpr.app m e1' e2'
      -- In `e'`, we have already supplied one input to `fn`.
      -- Note that we can't have 0-arity Factory functions at this point.
      let e'' := @mkAbsOfArity TBase.mono (lfunc.inputs.length - 1) (e' : LExpr TBase.mono)
      eval n' σ e''
  | _ => .app e.metadata e1' e2'
end

instance : Traceable EvalProvenance Unit where
  combine _ := ()

end LExpr
end -- public section
end Lambda

/-!
## Well-formedness of LFunc and Factory

WF of Func is separately defined in Strata/DL/Util/Func.lean
-/

namespace Lambda

open Std (ToFormat Format format)
open Strata.DL.Util (Func FuncWF TyIdentifier)

public section

variable {T : LExprParams} [Inhabited T.Metadata] [ToFormat T.IDMeta]

/-- Well-formedness properties for LFunc — extends generic `FuncWF` with
    Lambda-specific extractors and the generated-prefix guard on `typeArgs`. -/
structure LFuncWF {T : LExprParams} (f : LFunc T) extends
    FuncWF
      (fun id => id.name) -- getName
      (fun e => (LExpr.freeVars e).map (·.1.name)) -- getVarNames
      (fun e => e.freeVars) -- getTyFreeVars
      f where
  /-- Type arguments must not start with the reserved generated-variable
      prefix `$__ty` used by the type-checker. -/
  typeArgs_no_gen_prefix :
    ∀ ta, ta ∈ f.typeArgs → ¬ ("$__ty".toList.isPrefixOf ta.toList = true) := by decide

/-- An LFunc bundled with its well-formedness proof. -/
structure WFLFunc (T : LExprParams) where
  func : LFunc T
  wf : LFuncWF func

/-- The name of the underlying LFunc. -/
def WFLFunc.name (f : WFLFunc T) : T.Identifier := f.func.name

/-- The operator expression for the underlying LFunc. -/
def WFLFunc.opExpr [Inhabited T.Metadata] (f : WFLFunc T) : LExpr T.mono :=
  f.func.opExpr

/-- An array of well-formed LFuncs with a proof that function
    names are unique. -/
structure WFLFactory (T : LExprParams) where
  funcs : Array (WFLFunc T)
  name_nodup : List.Nodup (funcs.toList.map (·.func.name.name))

/-- Construct a `WFLFactory` from an array of `WFLFunc`s.
    The `name_nodup` proof defaults to `by decide`. -/
def WFLFactory.ofArray (funcs : Array (WFLFunc T))
    (name_nodup : List.Nodup (funcs.toList.map (·.func.name.name)) := by decide)
    : WFLFactory T :=
  ⟨funcs, name_nodup⟩

/-- Extract the underlying `Factory` from a `WFLFactory`. -/
def WFLFactory.toFactory (wf : WFLFactory T) : @Factory T :=
  wf.funcs.map (·.func)

instance LFuncWF.arg_nodup_decidable {T : LExprParams} (f : LFunc T):
    Decidable (List.Nodup (f.inputs.map (·.1.name))) := by
  apply List.nodupDecidable

instance LFuncWF.body_freevars_decidable {T : LExprParams} (f : LFunc T):
    Decidable (∀ b, f.body = .some b →
      (LExpr.freeVars b).map (·.1.name) ⊆ f.inputs.map (·.1.name)) :=
  by exact f.body.decidableForallMem

-- LFuncWF.concreteEval_argmatch is not decidable.

instance LFuncWF.body_or_concreteEval_decidable {T : LExprParams} (f : LFunc T):
    Decidable (¬ (f.concreteEval.isSome ∧ f.body.isSome)) := by
  exact instDecidableNot

instance LFuncWF.typeArgs_decidable {T : LExprParams} (f : LFunc T):
    Decidable (List.Nodup f.typeArgs) := by
  apply List.nodupDecidable

instance LFuncWF.inputs_typevars_in_typeArgs_decidable {T : LExprParams} (f : LFunc T):
    Decidable (∀ ty, ty ∈ f.inputs.values →
      ty.freeVars ⊆ f.typeArgs) := by
  exact List.decidableBAll (fun x => x.freeVars ⊆ f.typeArgs)
    (ListMap.values f.inputs)

instance LFuncWF.output_typevars_in_typeArgs_decidable {T : LExprParams} (f : LFunc T):
    Decidable (f.output.freeVars ⊆ f.typeArgs) := by
  apply List.instDecidableRelSubsetOfDecidableEq


/--
Well-formedness properties of Factory.
-/
structure FactoryWF (fac:Factory T) where
  name_nodup:
    List.Nodup (fac.toList.map (·.name.name))
  lfuncs_wf:
    ∀ (lf:LFunc T), lf ∈ fac → LFuncWF lf


instance FactoryWF.name_nodup_decidable (fac : Factory T):
    Decidable (List.Nodup (fac.toList.map (·.name.name))) := by
  apply List.nodupDecidable

/--
If Factory.addFactoryFunc succeeds, and the input factory & LFunc were already
well-formed, the returned factory is also well-formed.
-/
theorem Factory.addFactoryFunc_wf
  (F : @Factory T) (F_wf: FactoryWF F) (func : LFunc T) (func_wf: LFuncWF func):
  ∀ F', F.addFactoryFunc func = .ok F' → FactoryWF F' :=
by
  unfold Factory.addFactoryFunc
  unfold Factory.getFactoryLFunc
  intros F' Hmatch
  split at Hmatch <;> try grind -- Case-analysis on the match condition
  rename_i heq
  cases Hmatch -- F' is Array.push F
  apply FactoryWF.mk
  case name_nodup =>
    have Hnn := F_wf.name_nodup
    grind [Array.toList_push,List]
  case lfuncs_wf =>
    intros lf Hmem
    rw [Array.mem_push] at Hmem
    cases Hmem
    · have Hwf := F_wf.lfuncs_wf
      apply Hwf; assumption
    · grind


/--
If Factory.addFactory succeeds, and the input two factories were already
well-formed, the returned factory is also well-formed.
-/
theorem Factory.addFactory_wf
  (F : @Factory T) (F_wf: FactoryWF F) (newF : @Factory T)
  (newF_wf: FactoryWF newF):
  ∀ F', F.addFactory newF = .ok F' → FactoryWF F' :=
by
  unfold Factory.addFactory
  rw [← Array.foldlM_toList]
  generalize Hl: newF.toList = l
  induction l generalizing newF F
  · rw [Array.toList_eq_nil_iff] at Hl
    rw [List.foldlM_nil]
    unfold Pure.pure Except.instMonad Except.pure
    grind
  · rename_i lf lf_tail tail_ih
    have Hl: newF = (List.toArray [lf]) ++ (List.toArray lf_tail) := by grind
    have Htail_wf: FactoryWF (lf_tail.toArray) := by
      rw [Hl] at newF_wf
      apply FactoryWF.mk
      · have newF_wf_name_nodup := newF_wf.name_nodup
        grind
      · intro lf
        have newF_wf_lfuncs_wf := newF_wf.lfuncs_wf lf
        intro Hmem
        apply newF_wf_lfuncs_wf
        apply Array.mem_append_right
        assumption
    have Hhead_wf: LFuncWF lf := by
      rw [Hl] at newF_wf
      have Hwf := newF_wf.lfuncs_wf
      apply Hwf
      apply Array.mem_append_left
      grind
    intro F'
    simp only [List.foldlM]
    unfold bind
    unfold Except.instMonad
    simp only []
    unfold Except.bind
    intro H
    split at H
    · contradiction
    · rename_i F_interm HaddFacFun
      have HF_interm_wf: FactoryWF F_interm := by
        apply (Factory.addFactoryFunc_wf F F_wf lf) <;> assumption
      simp only [] at H
      apply tail_ih F_interm HF_interm_wf (lf_tail.toArray) <;> grind

end -- public section
end Lambda

public section
section Relation

@[expose] def Relation (A: Type) := A → A → Prop
def Reflexive (r: Relation A) : Prop := ∀ x, r x x
def Transitive (r: Relation A) : Prop := ∀ x y z, r x y → r y z → r x z

inductive ReflTrans {A: Type} (r: Relation A) : Relation A where
  | refl : ∀ x, ReflTrans r x x
  | step: ∀ x y z, r x y → ReflTrans r y z → ReflTrans r x z

theorem ReflTrans_Reflexive {A: Type} (r: Relation A):
  Reflexive (ReflTrans r) := by apply ReflTrans.refl

theorem ReflTrans_Transitive {A: Type} (r: Relation A):
  Transitive (ReflTrans r) := by
  unfold Transitive; intros x y z rxy
  induction rxy generalizing z
  case refl => simp
  case step x1 y1 z1 rxy1 ryz1 IH =>
    intros rzz1;
    apply (ReflTrans.step _ y1 _ rxy1 (IH _ rzz1))

end Relation
end

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)

public section

variable {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta]

open Lambda

/--
A free variable -> expression mapping.
-/
abbrev Env (Tbase:LExprParams) := Tbase.Identifier → Option (LExpr Tbase.mono)

def Scopes.toEnv (s:Scopes Tbase) : Env Tbase :=
  fun t => (s.find? t).map (·.snd)

/--
A small-step semantics for `LExpr`.

Currently only defined for expressions paremeterized by `LMonoTy`, but it will
be expanded to an arbitrary type in the future.

The order of constructors matter because the `constructor` tactic will rely on
it.

This small-step definitions faithfully follows the behavior of `LExpr.eval`,
except that:
1. This inductive definition may get stuck early when there is no
   assignment to a free variable available.

2. This semantics does not describe how metadata must change, because
   metadata must not affect evaluation semantics. Different concrete evaluators
   like `LExpr.eval` can have different strategy for updating metadata.
-/
inductive Step (F:@Factory Tbase) (rf:Env Tbase)
  : LExpr Tbase.mono → LExpr Tbase.mono → Prop where
/-- A free variable. Stuck if `fvar` does not exist in `FreeVarMap`. -/
| expand_fvar:
  ∀ (x:Tbase.Identifier) (e:LExpr Tbase.mono),
    rf x = .some e →
    Step F rf (.fvar m x ty) e

/-- Call-by-value semantics: beta reduction. -/
| beta:
  ∀ (e1 v2 eres:LExpr Tbase.mono),
    LExpr.isCanonicalValue F v2 →
    eres = LExpr.subst (fun _ => v2) e1 →
    Step F rf (.app m1 (.abs m2 name ty e1) v2) eres

/-- Call-by-value semantics: argument evaluation. -/
| reduce_2:
  ∀ (v1 e2 e2':LExpr Tbase.mono),
    LExpr.isCanonicalValue F v1 →
    Step F rf e2 e2' →
    Step F rf (.app m v1 e2) (.app m' v1 e2')

/-- Call-by-value semantics: function evaluation. -/
| reduce_1:
  ∀ (e1 e1' e2:LExpr Tbase.mono),
    Step F rf e1 e1' →
    Step F rf (.app m e1 e2) (.app m' e1' e2)

/-- Evaluation of `ite`: condition is true, select "then" branch. -/
| ite_reduce_then:
  ∀ (ethen eelse:LExpr Tbase.mono),
    Step F rf (.ite m (.const mc (.boolConst true)) ethen eelse) ethen

/-- Evaluation of `ite`: condition is false, select "else" branch. -/
| ite_reduce_else:
  ∀ (ethen eelse:LExpr Tbase.mono),
    Step F rf (.ite m (.const mc (.boolConst false)) ethen eelse) eelse

/-- Evaluation of `ite` condition. -/
| ite_reduce_cond:
  ∀ (econd econd' ethen eelse:LExpr Tbase.mono),
    Step F rf econd econd' →
    Step F rf (.ite m econd ethen eelse) (.ite m' econd' ethen eelse)

/-- Evaluation of `ite` "then" branch (when condition is not yet resolved). -/
| ite_reduce_then_branch:
  ∀ (econd ethen ethen' eelse:LExpr Tbase.mono),
    Step F rf ethen ethen' →
    Step F rf (.ite m econd ethen eelse) (.ite m' econd ethen' eelse)

/-- Evaluation of `ite` "else" branch (when condition is not yet resolved). -/
| ite_reduce_else_branch:
  ∀ (econd ethen eelse eelse':LExpr Tbase.mono),
    Step F rf eelse eelse' →
    Step F rf (.ite m econd ethen eelse) (.ite m' econd ethen eelse')

/-- Evaluation of equality. Reduce after both operands evaluate to values. -/
| eq_reduce:
  ∀ (e1 e2 eres:LExpr Tbase.mono)
    (H1:LExpr.isCanonicalValue F e1)
    (H2:LExpr.isCanonicalValue F e2),
    eres = .const mc (.boolConst (LExpr.eql F e1 e2 H1 H2)) →
    Step F rf (.eq m e1 e2) eres

/-- Evaluation of the left-hand side of an equality. -/
| eq_reduce_lhs:
  ∀ (e1 e1' e2:LExpr Tbase.mono),
    Step F rf e1 e1' →
    Step F rf (.eq m e1 e2) (.eq m' e1' e2)

/-- Evaluation of the right-hand side of an equality. -/
| eq_reduce_rhs:
  ∀ (v1 e2 e2':LExpr Tbase.mono),
    LExpr.isCanonicalValue F v1 →
    Step F rf e2 e2' →
    Step F rf (.eq m v1 e2) (.eq m' v1 e2')

/-- Evaluate a built-in function when a body expression is available in the
`Factory` argument `F`. This is consistent with what `LExpr.eval` does (modulo
the `inline` flag). Note that it might also be possible to evaluate with
`eval_fn`. A key correctness property is that doing so will yield the same
result. Note that this rule does not enforce an evaluation order. -/
| expand_fn:
  ∀ (e callee fnbody new_body:LExpr Tbase.mono) args fn,
    F.callOfLFunc e = .some (callee,args,fn) →
    fn.body = .some fnbody →
    new_body = LExpr.substFvars fnbody (fn.inputs.keys.zip args) →
    Step F rf e new_body

/-- Evaluate a built-in function when a concrete evaluation function is
available in the `Factory` argument `F`.  Note that it might also be possible to
evaluate with `expand_fn`. A key correctness property is that doing so will
yield the same result. Note that this rule does not enforce an evaluation
order. -/
| eval_fn:
  ∀ (e callee e':LExpr Tbase.mono) args fn denotefn,
    F.callOfLFunc e = .some (callee,args,fn) →
    fn.concreteEval = .some denotefn →
    .some e' = denotefn m args →
    Step F rf e e'

@[expose] def StepStar (F:@Factory Tbase) (rf:Env Tbase)
  : LExpr Tbase.mono → LExpr Tbase.mono → Prop :=
  ReflTrans (Step F rf)

theorem eval_StepStar
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (σ : LState Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF σ.config.factory)
    (hEnv : ∀ x v, Scopes.toEnv σ.state x = some v →
              LExpr.isCanonicalValue σ.config.factory v) :
    ∃ (e' : LExpr Tbase.mono) (sm : Map Tbase.Identifier (LExpr Tbase.mono)),
      StepStar σ.config.factory (Scopes.toEnv σ.state) e e' ∧
      sm.Sublist (σ.state.toSingleMap.map (fun (x, (_, v)) => (x, v))) ∧
      (LExpr.substFvars e' sm).eraseMetadata = (LExpr.eval n σ e).eraseMetadata := by
  sorry

end -- public section
end Lambda
