/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LTy

/-! ## Sorts

Ground monomorphic types. They name the sort of a value in the denotational
semantics (`Strata.DL.Lambda.Denote.LExprDenote`) and the element types of
collection literals (`LConst.mapConst`, `LConst.sequenceConst`). Their properties, and
their decidable equality, are in `Strata.DL.Lambda.LSortProps`.
-/

namespace Lambda

/-- A sort is a ground monomorphic type — an `LMonoTy` with no free type
variables. We use a separate type rather than `LMonoTy` to avoid carrying
around proofs that a type has no type variables. -/
public inductive LSort where
  /-- A named type constructor applied to sort arguments. -/
  | tcons (name : String) (args : List LSort)
  /-- A bit vector sort of the given size. -/
  | bitvec (size : Nat)
deriving Repr, Hashable

public section

/-- The Boolean sort. -/
protected abbrev LSort.bool : LSort := .tcons "bool" []
/-- The integer sort. -/
protected abbrev LSort.int : LSort := .tcons "int" []
/-- The real sort. -/
protected abbrev LSort.real : LSort := .tcons "real" []
/-- The string sort. -/
protected abbrev LSort.string : LSort := .tcons "string" []
/-- The sort `Map k v` of the total maps from `k` to `v`. -/
protected abbrev LSort.map (k v : LSort) : LSort := .tcons "Map" [k, v]
/-- The sort `Sequence a` of the finite sequences of `a`. -/
protected abbrev LSort.seq (a : LSort) : LSort := .tcons "Sequence" [a]

end

/-- Boolean equality of sorts, structurally. -/
public def LSort_eqb (s1 s2: LSort) : Bool :=
  match s1, s2 with
  | .tcons n1 a1, .tcons n2 a2 =>
    n1 == n2 && LSort_eqb_list a1 a2
  | .bitvec s1, .bitvec s2 => s1 == s2
  | _ , _ => false
where LSort_eqb_list : List LSort → List LSort → Bool
  | [], [] => true
  | x :: xs, y :: ys => LSort_eqb x y && LSort_eqb_list xs ys
  | _, _ => false

/-- Recursion on sorts with the hypothesis on the arguments of a constructor stated by list
    membership. -/
public def LSort.rec' (P : LSort → Sort u)
    (htcons : ∀ name args, (∀ x, x ∈ args → P x) → P (.tcons name args))
    (hbitvec : ∀ n, P (.bitvec n)) : ∀ s, P s
  | .tcons name args => htcons name args (fun x _ => rec' P htcons hbitvec x)
  | .bitvec n => hbitvec n

/-- The monomorphic type (without type variables) naming a sort. -/
@[expose] public def LSort.toMonoTy : LSort → LMonoTy
  | .tcons name args => .tcons name (map args)
  | .bitvec n => .bitvec n
where
  map : List LSort → List LMonoTy
  | [] => []
  | s :: ss => toMonoTy s :: map ss

/-- Whether a sort mentions the `Map` type constructor anywhere. Two well-typed
constants of a sort without `Map` are equal exactly when they denote the same value;
map literals are not canonical (two different literals can denote the same map,
e.g. when the key sort is finite), so for them only syntactic equality is known to
imply semantic equality. -/
@[expose] public def LSort.hasMap : LSort → Bool
  | .tcons name args => name == "Map" || hasMapList args
  | .bitvec _ => false
where
  hasMapList : List LSort → Bool
  | [] => false
  | s :: ss => hasMap s || hasMapList ss

end Lambda

namespace Lambda

/-- The sort a monomorphic type names, if it has no type variables. -/
@[expose] public def LMonoTy.toSort? : LMonoTy → Option LSort
  | .ftvar _ => none
  | .bitvec n => some (.bitvec n)
  | .tcons name args => (toSortList? args).map (.tcons name)
where
  toSortList? : List LMonoTy → Option (List LSort)
  | [] => some []
  | t :: ts => match toSort? t, toSortList? ts with
    | some s, some ss => some (s :: ss)
    | _, _ => none

end Lambda
