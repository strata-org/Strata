/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.LExprDenoteConsts

/-!
## Semantic equality of literals

`LConst.semEq? fuel c d` decides whether two well-typed literals of one sort have the same value
(`constVal`). Folding an equality of two literals must compare what they denote, not how they
are written: a map literal denotes the function `SortDenote.mapOf` builds from its default and
entries, so the order of the entries and every entry after the first with a given key are
unobservable, and so is the default when the listed keys exhaust the key sort.

Two equal literals are equal at every sort, as mainline's `LConst.eql` answers first; so
`semEq?` answers wherever `eql` does, with the same answer, and also decides the map literals
whose entries are reordered, repeat a key or hide the default, where `eql` does not answer.
At a sort without `Map` the value of a literal determines the literal (`constVal_injective`), so
there semantic equality is structural equality. This covers the Boolean, integer, string and
bit-vector literals, rational literals (a rational literal denotes `Real.ofRat` of a reduced
fraction, and `ofRat` is injective, `Strata.Util.Real.ofRat_inj`), and sequences of those.
Only sorts containing `Map` need more.

The answer is an `Option Bool`: `some b` is the answer, and `none` means that it is not
decided, so a fold must not fold. `none` arises where the answer depends on the
interpretation of the sorts and not on the literals alone, and where the procedure does not
decide (see `LConst.keysCover?`). `semEq?_sound` states that a `some` answer is correct in every
interpretation whose type constructors are inhabited, as every model's are (`Interp`).

- `LConst.keysCover?` — do the values of the listed keys exhaust the key sort
- `LConst.semEq?` — the decision, with `LConst.listEqWith`, `LConst.lookupWith`,
  `LConst.allWith` and `LConst.mapEqWith`

Its soundness, `LConst.semEq?_sound`, is in `Strata.DL.Lambda.Denote.LConstSemEqProps`.
-/

namespace Lambda

public section

/-- Do the values of the keys `us`, literals of sort `k`, exhaust the values of `k`?

- At `bool`: exactly when both Boolean literals are among them.
- At `bitvec n`: exactly when each of the `2 ^ n` bit vectors is among them. Fewer than `2 ^ n`
  keys cannot exhaust them, which is checked first, so the enumeration runs only over at most as
  many values as there are keys.
- At `int`, `real`, `string` and `Sequence a`: never. The sort has infinitely many values (a
  sequence sort because its element sort is inhabited), and finitely many keys are listed.
- At any other sort: not decided (`none`). This is a key sort that is itself a map sort, or
  that is named by the interpretation. Whether finitely many keys exhaust it can depend on the
  interpretation of the sorts: the maps from an interpreted sort `u` to `bool` that a literal
  can denote with no entry are the two constant maps, and those two exhaust the sort exactly
  when `u` has one value. -/
@[expose] def LConst.keysCover? (k : LSort) (us : List LConst) : Option Bool :=
  match k with
  | .tcons "bool" [] =>
    some (us.any (fun u => u matches .boolConst true) &&
      us.any (fun u => u matches .boolConst false))
  | .bitvec n =>
    if 2 ^ n ≤ us.length then
      some ((List.range (2 ^ n)).all fun i =>
        us.any fun u => match u with
          | .bitvecConst m b => m == n && b.toNat == i
          | _ => false)
    else some false
  | .tcons "int" [] | .tcons "real" [] | .tcons "string" [] | .tcons "Sequence" [_] => some false
  | _ => none

/-- Compare two lists of literals elementwise with `f`: they are equal when they have the same
    length and `f` finds each pair equal. -/
@[expose] def LConst.listEqWith (f : LConst → LConst → Option Bool) :
    List LConst → List LConst → Option Bool
  | [], [] => some true
  | x :: xs, y :: ys =>
    match f x y with
    | some true => listEqWith f xs ys
    | some false => some false
    | none => none
  | _, _ => some false

/-- The literal a map literal's entries `es` send the key `u` to, comparing keys with `f`:
    `some (some w)` when the first entry whose key `f` finds equal to `u` has value `w`,
    `some none` when `f` finds no key equal to `u`, and `none` when `f` does not decide a key
    before the first equal one. -/
@[expose] def LConst.lookupWith (f : LConst → LConst → Option Bool) (u : LConst) :
    List (LConst × LConst) → Option (Option LConst)
  | [] => some none
  | (k, w) :: r =>
    match f k u with
    | some true => some (some w)
    | some false => lookupWith f u r
    | none => none

/-- Does `g` hold of every element of a list: `some false` when `g` refutes an element before
    any undecided one, `some true` when `g` holds of all. -/
@[expose] def LConst.allWith (g : LConst → Option Bool) : List LConst → Option Bool
  | [] => some true
  | u :: r =>
    match g u with
    | some true => allWith g r
    | some false => some false
    | none => none

/-- Compare two map literals of key sort `k`, with defaults `dc`, `dd` and entries `xs`, `ys`, as
    the functions they denote, comparing literals of the key and value sorts with `f`.

    The two functions agree at a key that neither lists exactly when both send it to their
    default. So they are equal exactly when they agree at every listed key `u` (the values
    `lookupWith` finds, or the defaults), and either the defaults are equal or the listed keys
    exhaust the key sort (`keysCover?`), in which case no unlisted key exists and the defaults
    are unobservable. -/
@[expose] def LConst.mapEqWith (f : LConst → LConst → Option Bool) (k : LSort) (dc : LConst)
    (xs : List (LConst × LConst)) (dd : LConst) (ys : List (LConst × LConst)) : Option Bool :=
  let us := xs.map Prod.fst ++ ys.map Prod.fst
  match allWith (fun u =>
      match lookupWith f u xs, lookupWith f u ys with
      | some a, some b => f (a.getD dc) (b.getD dd)
      | _, _ => none) us with
  | some true =>
    match f dc dd with
    | some true => some true
    | some false => keysCover? k us
    | none => none
  | some false => some false
  | none => none

mutual
/-- How deeply collection literals nest in a literal: `1` for a primitive literal, and one more
    than the deepest part for a map or sequence literal. `semEq?` descends one level per unit of
    fuel, so this much fuel lets it reach every part of a literal. -/
@[expose] def LConst.depth : LConst → Nat
  | .mapConst _ _ d ⟨es⟩ => max d.depth (LConst.depthEntries es) + 1
  | .sequenceConst _ ⟨es⟩ => LConst.depthElems es + 1
  | _ => 1
/-- The depth of the deepest key or value of a map literal's entries. -/
@[expose] def LConst.depthEntries : List (LConst × LConst) → Nat
  | [] => 0
  | (a, b) :: r => max (max a.depth b.depth) (LConst.depthEntries r)
/-- The depth of the deepest element of a sequence literal. -/
@[expose] def LConst.depthElems : List LConst → Nat
  | [] => 0
  | a :: r => max a.depth (LConst.depthElems r)
end

/-- **Semantic equality of two literals of one sort**, with `fuel` bounding the nesting of
    collection literals it descends through (`none` when exhausted). Two equal literals are
    equal (`true`, the first case of `LConst.eql`, at any fuel). At a sort without `Map` it is
    structural equality (`constVal_injective`); sequences are compared elementwise and maps as
    the functions they denote (`mapEqWith`). So it answers wherever `LConst.eql` answers, with
    the same answer. -/
@[expose] def LConst.semEq? : Nat → LConst → LConst → Option Bool
  | 0, c, d => if c = d then some true else none
  | fuel + 1, c, d =>
    if c = d then some true
    else if c.sort.hasMap = false then some false
    else
      match c, d with
      | .sequenceConst _ ⟨xs⟩, .sequenceConst _ ⟨ys⟩ => listEqWith (semEq? fuel) xs ys
      | .mapConst k _ dc ⟨xs⟩, .mapConst _ _ dd ⟨ys⟩ => mapEqWith (semEq? fuel) k dc xs dd ys
      | _, _ => some false

end

end Lambda
