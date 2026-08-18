/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Unit tests for `matchTypeArg` (MonomorphizeComposites), the type-argument inference
that binds a declared type's type variables against a concrete actual type (e.g.
`Box<T>` vs `Box<int>` ⇒ `T = int`) to drive procedure monomorphization. Covers
recursion, consistent/inconsistent repeated vars, arity + base-name mismatches.
-/
-- `import all` exposes `matchTypeArg`'s definition body so the monotonicity theorem
-- can `unfold`/induct on it (a plain `import` keeps the body opaque).
meta import all Strata.Languages.Laurel.MonomorphizeComposites
-- The monotonicity theorem itself lives in the `<A>Props.lean` companion; referenced below.
import Strata.Languages.Laurel.MonomorphizeCompositesProps
meta section
open Strata.Laurel
namespace Strata.Laurel.MatchTypeArgTest
-- HighType builders
private def hi (h : HighType) : HighTypeMd := ⟨h, .unknown⟩
private def tv (s : String) : HighType := .TVar (mkId s)
private def ud (s : String) : HighType := .UserDefined (mkId s)
private def app (base : HighType) (args : List HighType) : HighType := .Applied (hi base) (args.map hi)
-- lookup helper
private def look (m : Option (Std.HashMap String HighType)) (k : String) : Option HighType :=
  m.bind (·.get? k)

-- Empty starting accumulator, reused by every case.
private def e : Std.HashMap String HighType := {}

-- The 13 cases below are elaboration-time `#guard`s: each pins a concrete expected output,
-- so a mismatch fails the BUILD (with a diff) rather than a runtime panic. They align with
-- the `#guard` base case and `matchTypeArg_monotone` theorem further down.

-- (1) Box<T> vs Box<int> → T = int
#guard look (matchTypeArg (app (ud "Box") [tv "T"]) (app (ud "Box") [.TInt]) e) "T" == some .TInt
-- (2) nested Box<Box<T>> vs Box<Box<bool>> → T = bool
#guard look (matchTypeArg (app (ud "Box") [app (ud "Box") [tv "T"]]) (app (ud "Box") [app (ud "Box") [.TBool]]) e) "T" == some .TBool
-- (3) two params, T consistent (Pair<T,T> vs Pair<int,int>) → T = int
#guard look (matchTypeArg (app (ud "Pair") [tv "T", tv "T"]) (app (ud "Pair") [.TInt, .TInt]) e) "T" == some .TInt
-- (4) two params, T INCONSISTENT (Pair<T,T> vs Pair<int,bool>) → none
#guard (matchTypeArg (app (ud "Pair") [tv "T", tv "T"]) (app (ud "Pair") [.TInt, .TBool]) e).isNone
-- (5) arity mismatch (Box<T> vs Box<int,bool>) → none
#guard (matchTypeArg (app (ud "Box") [tv "T"]) (app (ud "Box") [.TInt, .TBool]) e).isNone
-- (6) bare T vs concrete composite → T = that composite
#guard look (matchTypeArg (tv "T") (ud "Widget") e) "T" == some (.UserDefined (mkId "Widget"))
-- (7) DIFFERENT base names, same arity (Box<T> vs Pair<int>) → none: monomorphization
--     self-guards on the base name, so mismatched heads don't bind T=int on arity alone.
#guard (matchTypeArg (app (ud "Box") [tv "T"]) (app (ud "Pair") [.TInt]) e).isNone
-- (8) Map<T,U> vs Map<int,bool> → T = int, U = bool  (live arm — Map has surface syntax)
#guard look (matchTypeArg (.TMap (hi (tv "T")) (hi (tv "U"))) (.TMap (hi .TInt) (hi .TBool)) e) "T" == some .TInt
#guard look (matchTypeArg (.TMap (hi (tv "T")) (hi (tv "U"))) (.TMap (hi .TInt) (hi .TBool)) e) "U" == some .TBool
-- (9) Map<T,T> vs Map<int,bool> → none: T bound int on key, then bool≠int on value
#guard (matchTypeArg (.TMap (hi (tv "T")) (hi (tv "T"))) (.TMap (hi .TInt) (hi .TBool)) e).isNone
-- (10) Set<T> vs Set<int> → T = int  (arm exists though no Set surface syntax yet)
#guard look (matchTypeArg (.TSet (hi (tv "T"))) (.TSet (hi .TInt)) e) "T" == some .TInt
-- (11) BOUNDARY: empty-arg `.Applied` on both sides (Box<> vs Box<>) → some, no bindings.
--      Exercises the length-eq-TRUE (0==0) + empty-fold identity path. Not a shape the
--      front-end emits (surface `Box` with no args collapses to `.UserDefined`), but the
--      matcher must handle it as the degenerate base of the args-fold.
#guard (matchTypeArg (app (ud "Box") []) (app (ud "Box") []) e).any (·.isEmpty)
-- (12) empty-vs-nonempty arity (Box<> vs Box<int>) → none: the 0-vs-1 analogue of case 5.
#guard (matchTypeArg (app (ud "Box") []) (app (ud "Box") [.TInt]) e).isNone
-- (13) empty-arg, different base (Box<> vs Pair<>) → none: base-name guard fires even at arity 0.
#guard (matchTypeArg (app (ud "Box") []) (app (ud "Pair") []) e).isNone
-- (14) a declared `.Intersection` has no dedicated arm, so it hits the catch-all `_ => some acc`:
--      it binds nothing and passes through (does not spuriously match or fail). Pins that a
--      declared type outside {`.TVar`,`.Applied`,`.TSet`,`.TMap`} is a no-op, not a mis-match.
#guard (matchTypeArg (.Intersection [hi .TInt, hi .TBool]) .TInt e).any (·.isEmpty)

-- (15-17) OUTER constructor mismatch: a declared `.Applied`/`.TSet`/`.TMap` faces an
-- actual of a DIFFERENT head. Each falls to that arm's own `| _ => none` (definition
-- lines ~123/124/127) — branches distinct from the within-constructor arity/base/value
-- mismatches above, and NOT subsumed by `matchTypeArg_monotone` (which pins accumulator
-- preservation on SUCCESS, never a rejection). One `.isNone` per constructor pins them.
#guard (matchTypeArg (app (ud "Box") [tv "T"]) .TInt e).isNone            -- .Applied vs non-.Applied
#guard (matchTypeArg (.TSet (hi (tv "T"))) .TBool e).isNone               -- .TSet vs non-.TSet
#guard (matchTypeArg (.TMap (hi (tv "T")) (hi (tv "U"))) .TInt e).isNone  -- .TMap vs non-.TMap

-- Beyond the executable cases: the base case pinned as an elaboration-time `#guard`
-- (a fresh `.TVar` against an empty accumulator binds exactly that var).
#guard (matchTypeArg (tv "T") .TInt {}).bind (·.get? "T") == some HighType.TInt

-- The semantic invariant the args-fold in the `.Applied` case relies on — matching only ever
-- EXTENDS the accumulator, never drops a prior binding — is proved as `matchTypeArg_monotone`
-- in `MonomorphizeCompositesProps.lean` (the `<A>Props.lean` home for facts about `A`). It is
-- the whole-function monotonicity the fold needs: a `.TVar` bound while matching an earlier
-- `.Applied` argument must survive so the consistency check against it fires for a later one
-- (cases 3/4). Referenced here so this test file's coverage note stays anchored to the theorem.
#check @Strata.Laurel.matchTypeArg_monotone

end Strata.Laurel.MatchTypeArgTest
