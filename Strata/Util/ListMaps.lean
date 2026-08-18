/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.ListMap
import all Strata.Util.ListMap

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
Remove `x` and its associated value from `ms`.
-/
def Maps.remove [DecidableEq α] (ms : Maps α β) (x : α) : Maps α β :=
  match ms with
  | [] => []
  | m :: rest => Map.erase m x :: Maps.remove rest x


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
end
