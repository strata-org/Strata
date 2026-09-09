/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
`anyHighType` and the predicates built on it.

The property worth pinning is ANY DEPTH: each predicate must see an occurrence nested inside a
compound type, not only one at the head. That is the whole reason they share one walker, and a
test using only bare types would pass on a walker that never descended. So each predicate is
checked bare and then under every compound constructor `anyHighType` recurses into.
-/

import StrataLaurel.Implementation.LaurelAST

namespace Strata.Laurel

private def ty (t : HighType) : HighTypeMd := ⟨t, default⟩
/-- `Sequence<τ>` — one level of nesting under a generic application. -/
private def seqOf (t : HighType) : HighType := .Applied (ty (.UserDefined (mkId "Sequence"))) [ty t]
private def tvarT : HighType := .TVar (mkId "T")

/-! ## `mentionsUnknown`, bare and under each compound constructor -/

#guard mentionsUnknown .Unknown
#guard mentionsUnknown (seqOf .Unknown)                      -- `.Applied` type argument
#guard mentionsUnknown (.Applied (ty .Unknown) [ty .TInt])   -- `.Applied` base
#guard mentionsUnknown (.TMap (ty .TInt) (ty .Unknown))
#guard mentionsUnknown (.TSet (ty .Unknown))
#guard mentionsUnknown (.Intersection [ty .TInt, ty .Unknown])
#guard mentionsUnknown (.MultiValuedExpr [ty .TInt, ty .Unknown])
#guard !mentionsUnknown (seqOf .TInt)
#guard !mentionsUnknown tvarT

/-! ## `mentionsTVar`, bare and under each compound constructor -/

#guard mentionsTVar tvarT
#guard mentionsTVar (seqOf tvarT)
#guard mentionsTVar (.Applied (ty tvarT) [ty .TInt])
#guard mentionsTVar (.TMap (ty .TInt) (ty tvarT))
#guard mentionsTVar (.TSet (ty tvarT))
#guard mentionsTVar (.Intersection [ty .TInt, ty tvarT])
#guard mentionsTVar (.MultiValuedExpr [ty .TInt, ty tvarT])
#guard !mentionsTVar (seqOf .TInt)
#guard !mentionsTVar .Unknown

/-! ## Any predicate gets the same descent

An arbitrary predicate — not one of the two above — sees a nested occurrence too: the descent
belongs to `anyHighType`, not to the predicates defined on it. -/

#guard anyHighType (· matches .UserDefined _) (.TSet (ty (seqOf .TInt)))
#guard !anyHighType (· matches .UserDefined _) (.TSet (ty .TInt))

/-! ## Descent is not depth-limited

The cases above nest one level. These nest three, through a different constructor at each level, so
the recursion is exercised as a recursion rather than as a single step per arm. -/

#guard mentionsUnknown (seqOf (.TMap (ty .TInt) (ty (.TSet (ty .Unknown)))))
#guard mentionsTVar (seqOf (.TMap (ty .TInt) (ty (.TSet (ty tvarT)))))
#guard !mentionsUnknown (seqOf (.TMap (ty .TInt) (ty (.TSet (ty .TInt)))))

end Strata.Laurel
