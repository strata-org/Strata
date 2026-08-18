/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
-- Copied over from LNSym
-- https://github.com/leanprover/LNSym/blob/main/Arm/Map.lean

open Std (ToFormat Format format)

/-!
# List-based maps: `ListMap` and `Map`

Two near-identical simple map types, both backed by `List (α × β)` and exposing
the same core operations.  `ListMap` is defined in this section; `Map` in the
next.
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


@[expose]
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


def ListMap.findWithIdx? [DecidableEq α] (m : ListMap α β) (a' : α) : Option (Nat × β) :=
  go m a' 0
where
  go : ListMap α β → α → Nat → Option (Nat × β)
  | [], _, _ => none
  | (a, b) :: m, a', i => if a = a' then some (i, b) else go m a' (i + 1)


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


@[expose]
def ListMap.values (m : ListMap α β) : List β :=
  match m with
  | [] => []
  | (_, a) :: m => a :: values m


/-- Are the keys of `m1` and `m2` disjoint? -/
def ListMap.disjointp [DecidableEq α] (m1 m2 : ListMap α β) : Prop :=
  ∀ k, (m1.find? k) = none ∨ (m2.find? k = none)



-------------------------------------------------------------------------------
end

public section
-- [STOPGAP] Should be replaced by Std.HashMap.

-- Copied over from LNSym
-- https://github.com/leanprover/LNSym/blob/main/Arm/Map.lean

open Std (ToFormat Format format)

/-! ## `Map`

A second list-based map, near-identical to `ListMap` above (it adds `keySet` and
`fmap`, where `ListMap` adds `findWithIdx?`).
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


def Map.values (m : Map α β) : List β :=
  match m with
  | [] => []
  | (_, a) :: m => a :: values m


/-- Are the keys of `m1` and `m2` disjoint? -/
def Map.disjointp [DecidableEq α] (m1 m2 : Map α β) : Prop :=
  ∀ k, (m1.find? k) = none ∨ (m2.find? k = none)


@[expose] def Map.fmap (f: β → γ) (m: Map α β) : Map α γ :=
  List.map (fun (x, y) => (x, f y)) m


-------------------------------------------------------------------------------
end
