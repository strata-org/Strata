/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.Denote.LExprDenoteConsts

meta section

/-! # Tests for map and sequence literals

Unit tests for the `mapConst` and `sequenceConst` constants of `LConst`: the map-entry
operations `LConst.mapUpdate` and `LConst.mapSelect`, the equality test `LConst.eql`, and
the well-typedness check `LConst.wt`. -/

namespace Lambda.LConstCollectionTests

private def intS : LSort := .tcons "int" []
private def boolS : LSort := .tcons "bool" []

/-- Integer key-value pairs as literal entries. -/
private def ents (es : Array (Int × Int)) : Array (LConst × LConst) :=
  es.map fun (k, v) => (.intConst k, .intConst v)

/-- The `Map int int` literal with default `0` and the given entries. -/
private def intMap (es : Array (Int × Int)) : LConst := .mapConst intS intS (.intConst 0) (ents es)

/-- The `Sequence int` literal with the given elements. -/
private def intSeq (xs : Array Int) : LConst := .sequenceConst intS (xs.map .intConst)

/-! ## Map entries -/

-- An update appends the new entry; updating a key again replaces its entry.
#guard LConst.mapUpdate (.intConst 0) #[] (.intConst 1) (.intConst 10) = ents #[(1, 10)]
#guard LConst.mapUpdate (.intConst 0) (ents #[(1, 10), (2, 20)]) (.intConst 1) (.intConst 30) =
  ents #[(2, 20), (1, 30)]
-- Setting a key to the default drops its entry.
#guard LConst.mapUpdate (.intConst 0) (ents #[(1, 10)]) (.intConst 1) (.intConst 0) = #[]

-- A select returns the key's value, or the default for a key without an entry.
#guard LConst.mapSelect (.intConst 0) (ents #[(1, 10), (2, 20)]) (.intConst 2) = .intConst 20
#guard LConst.mapSelect (.intConst 0) (ents #[(1, 10)]) (.intConst 3) = .intConst 0

/-! ## Repeated keys

When the entries of a map literal repeat a key, the first entry with that key counts: in the
evaluator (`LConst.mapSelect`), in the semantics (`SortDenote.mapOf`), and in the SMT encoding,
which puts the first entry outermost (`SMTEncoderTests`). -/

-- `{1 ↦ 2, 1 ↦ 3, _ ↦ 0}` reads `2` at key `1`.
#guard LConst.mapSelect (.intConst 0) (ents #[(1, 2), (1, 3)]) (.intConst 1) = .intConst 2

/-- The value of `{1 ↦ 2, 1 ↦ 3, _ ↦ 0}` at key `1` is `2`. -/
example (tcInterp : TyConstrInterp) :
    ∃ m, constVal tcInterp (.tcons "Map" [.int, .int])
        (.mapConst .int .int (.intConst 0)
          ⟨[(.intConst 1, .intConst 2), (.intConst 1, .intConst 3)]⟩)
        = some m ∧
      m (show SortDenote tcInterp .int from (1 : Int)) =
        (show SortDenote tcInterp .int from (2 : Int)) := by
  let i : Int → SortDenote tcInterp .int := id
  have hhead : ∀ {k v : LSort} (dv : SortDenote tcInterp v) (key : SortDenote tcInterp k)
      (x : SortDenote tcInterp v) rest, SortDenote.mapOf dv ((key, x) :: rest) key = x := by
    intro k v dv key x rest
    simp [SortDenote.mapOf]
  refine ⟨SortDenote.mapOf (i 0) [(i 1, i 2), (i 1, i 3)], ?_, hhead _ _ _ _⟩
  simp only [constVal_mapConst, constVal_intConst, constValEntries]
  rfl

/-! ## Equality of literals -/

-- Equal literals are equal.
#guard LConst.eql (intMap #[(1, 10)]) (intMap #[(1, 10)]) = some true
-- Different sequence literals of a sort without `Map` are different.
#guard LConst.eql (intSeq #[1, 2]) (intSeq #[2, 1]) = some false
-- Different map literals may denote the same map (here, the same entries in another order),
-- so their equality is left undecided.
#guard LConst.eql (intMap #[(1, 10), (2, 20)]) (intMap #[(2, 20), (1, 10)]) = none
-- A sequence whose elements are maps also has no decided disequality.
private def seqOfMaps : LConst := .sequenceConst (.tcons "Map" [intS, intS]) #[intMap #[]]
#guard LConst.eql seqOfMaps (.sequenceConst (.tcons "Map" [intS, intS]) #[]) = none

/-! ## Well-typedness -/

-- A collection literal is well typed only when its elements have the declared sorts.
#guard (intMap #[(1, 10)]).wt
#guard !(LConst.mapConst intS intS (.intConst 0) #[(.boolConst true, .intConst 1)]).wt
#guard !(LConst.mapConst intS intS (.boolConst false) #[]).wt
#guard (intSeq #[1, 2]).wt
#guard !(LConst.sequenceConst boolS #[.intConst 1]).wt
-- An ill-typed literal has type `bool`.
#guard (LConst.sequenceConst boolS #[.intConst 1]).ty = .bool
#guard (intSeq #[]).ty = .tcons "Sequence" [.int]

end Lambda.LConstCollectionTests
