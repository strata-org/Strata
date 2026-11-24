/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Transform.Passive.CoreLang

/-!
# The literal fold compares what literals denote

`Core.WP.constFold` folds an equality of two literals of one type. These tests pin the cases
where comparing how the literals are written gives the wrong answer, so that the semantic
comparison (`Lambda.LConst.semEq?`) and the well-typedness guard are not "simplified" back to
structural equality.
-/

namespace Strata.ConstFoldSemEqTests

open Lambda Core Core.WP

private def lit (c : LConst) : Expression.Expr := .const valueLoc c
private def eqE (a b : LConst) : Expression.Expr := .eq valueLoc (lit a) (lit b)

/-! ## A literal that is not well typed is not folded

`sequenceConst bool [intConst 0]` declares element sort `bool` and holds an integer. It is not
well typed, so its type is `bool` (`LConst.ty_of_not_wt`) and its value is `false`
(`denoteCollection`'s not-well-typed branch), the type and the value of `boolConst false`.
Structurally the two differ. A fold that compared them structurally would answer `false` for an
equality whose sides have one value. The literal is not folded at all: as an expression it has no
typing, hence no value. -/

private def illTyped : LConst := .sequenceConst .bool #[.intConst 0]

#guard illTyped.wt = false
#guard illTyped.ty = (LConst.boolConst false).ty
#guard constFold (lit illTyped) = none
#guard constFold (eqE illTyped (.boolConst false)) = none

/-! ## Map literals are compared as the functions they denote -/

/-- `{true ↦ 1, false ↦ 2}`, default `0`. -/
private def mTF : LConst :=
  .mapConst .bool .int (.intConst 0) #[(.boolConst true, .intConst 1), (.boolConst false, .intConst 2)]
/-- The same entries in the other order. -/
private def mFT : LConst :=
  .mapConst .bool .int (.intConst 0) #[(.boolConst false, .intConst 2), (.boolConst true, .intConst 1)]
/-- The same entries with default `7`. Both values of `bool` are listed, so no key reaches the
    default: the default is unobservable. -/
private def mTF7 : LConst :=
  .mapConst .bool .int (.intConst 7) #[(.boolConst true, .intConst 1), (.boolConst false, .intConst 2)]
/-- Only `true` listed: the default is observable at `false`. -/
private def mT0 : LConst := .mapConst .bool .int (.intConst 0) #[(.boolConst true, .intConst 1)]
private def mT7 : LConst := .mapConst .bool .int (.intConst 7) #[(.boolConst true, .intConst 1)]
/-- A repeated key: only the first entry with a key is observable. -/
private def mDup : LConst :=
  .mapConst .bool .int (.intConst 0)
    #[(.boolConst true, .intConst 1), (.boolConst true, .intConst 9), (.boolConst false, .intConst 2)]

-- entries in a different order denote one function
#guard constFold (eqE mTF mFT) = some (.boolConst true)
-- a default the listed keys make unobservable does not distinguish two maps
#guard constFold (eqE mTF mTF7) = some (.boolConst true)
-- an observable default does
#guard constFold (eqE mT0 mT7) = some (.boolConst false)
-- an entry shadowed by an earlier one with the same key is unobservable
#guard constFold (eqE mTF mDup) = some (.boolConst true)

/-! ## Key sorts with many or infinitely many values -/

/-- Integer keys: finitely many listed keys never exhaust `int`, so differing defaults are
    observable. -/
private def mI0 : LConst := .mapConst .int .int (.intConst 0) #[(.intConst 1, .intConst 1)]
private def mI5 : LConst := .mapConst .int .int (.intConst 5) #[(.intConst 1, .intConst 1)]
#guard constFold (eqE mI0 mI5) = some (.boolConst false)

/-- `bitvec 1` keys: listing both bit vectors makes the default unobservable. -/
private def mB0 : LConst :=
  .mapConst (.bitvec 1) .int (.intConst 0)
    #[(.bitvecConst 1 0, .intConst 1), (.bitvecConst 1 1, .intConst 2)]
private def mB9 : LConst :=
  .mapConst (.bitvec 1) .int (.intConst 9)
    #[(.bitvecConst 1 1, .intConst 2), (.bitvecConst 1 0, .intConst 1)]
#guard constFold (eqE mB0 mB9) = some (.boolConst true)

/-- `bitvec 32` keys: one listed key cannot exhaust `2 ^ 32` values. This is answered from the
    count of listed keys, without enumerating the bit vectors. -/
private def mW0 : LConst := .mapConst (.bitvec 32) .int (.intConst 0) #[(.bitvecConst 32 5, .intConst 1)]
private def mW3 : LConst := .mapConst (.bitvec 32) .int (.intConst 3) #[(.bitvecConst 32 5, .intConst 1)]
#guard constFold (eqE mW0 mW3) = some (.boolConst false)

/-! ## Primitive literals still fold by value -/

#guard constFold (eqE (.intConst 3) (.intConst 3)) = some (.boolConst true)
#guard constFold (eqE (.intConst 3) (.intConst 4)) = some (.boolConst false)
-- literals of different types are not compared
#guard constFold (eqE (.intConst 3) (.boolConst true)) = none

/-! ## Agreement with `LConst.eql`

`LConst.semEq?` answers wherever mainline's `LConst.eql` (the literal equality of symbolic
evaluation) answers, with the same answer, and decides the map cases `eql` leaves open. -/

/-- `semEq?` with the fuel `constFold` gives it. -/
private def se (a b : LConst) : Option Bool := LConst.semEq? (max a.depth b.depth) a b

private def iL (n : Int) : LConst := .intConst n
private def mI (d : LConst) (es : List (LConst × LConst)) : LConst := .mapConst .int .int d es.toArray
/-- A key of sort `Map T bool`, `T` a sort the model interprets: the constant map to `b`. -/
private def kT (b : Bool) : LConst := .mapConst (.tcons "T" []) .bool (.boolConst b) #[]
/-- A map keyed by maps over the interpreted sort `T`. -/
private def mK (es : List (LConst × LConst)) : LConst :=
  .mapConst (.tcons "Map" [.tcons "T" [], .bool]) .int (iL 0) es.toArray

-- identical map literals keyed by maps over an interpreted sort are equal
#guard se (mK [(kT true, iL 1), (kT false, iL 2)]) (mK [(kT true, iL 1), (kT false, iL 2)]) =
  some true

/-- Representative pairs of literals: primitive, sequence and map literals, equal and not,
    well typed and not. -/
private def pairs : List (LConst × LConst) :=
  [(iL 1, iL 1), (iL 1, iL 2), (.rationalConst (1/2), .rationalConst (2/4)),
   (.bitvecConst 8 3, .bitvecConst 8 3), (.bitvecConst 8 3, .bitvecConst 8 4),
   (.boolConst true, .boolConst false), (.strConst "a", .strConst "a"),
   (.sequenceConst .int #[iL 1], .sequenceConst .int #[iL 1]),
   (.sequenceConst .int #[iL 1], .sequenceConst .int #[iL 2]),
   (.sequenceConst .int #[.boolConst true], .sequenceConst .int #[.boolConst true]),
   (mI (iL 0) [(iL 1, iL 2)], mI (iL 0) [(iL 1, iL 2)]),
   (mI (iL 0) [(iL 1, iL 2), (iL 3, iL 4)], mI (iL 0) [(iL 3, iL 4), (iL 1, iL 2)]),
   (mI (iL 0) [(iL 1, iL 2)], mI (iL 0) [(iL 1, iL 3)]),
   (mTF, mFT), (mTF, mTF7), (mT0, mT7),
   (mK [(kT true, iL 1)], mK [(kT true, iL 1)]), (mK [(kT true, iL 1)], mK [(kT false, iL 1)])]

-- wherever `eql` answers, `semEq?` gives the same answer
#guard pairs.all fun (a, b) => match LConst.eql a b with
  | some r => se a b == some r
  | none => true
-- the pairs on which `eql` answers and those on which only `semEq?` does
#guard pairs.map (fun (a, b) => (LConst.eql a b, se a b)) ==
  [(some true, some true), (some false, some false), (some true, some true),
   (some true, some true), (some false, some false), (some false, some false),
   (some true, some true), (some true, some true), (some false, some false),
   (some true, some true), (some true, some true), (none, some true), (none, some false),
   (none, some true), (none, some true), (none, some false), (some true, some true),
   (none, none)]

end Strata.ConstFoldSemEqTests
