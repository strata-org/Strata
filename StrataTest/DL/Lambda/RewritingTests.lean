/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.Rewriting

meta section

namespace Lambda.RewritingTests

open Lambda

/-! Tests for the first-order matcher and rewrite-rule engine in
`Strata.DL.Lambda.Rewriting`. We instantiate everything at the simple parameter
`⟨⟨Unit, Unit⟩, Unit⟩`, where identifiers are plain strings (with `Unit`
metadata) and there are no type annotations. -/

abbrev P : LExprParamsT := ⟨⟨Unit, Unit⟩, Unit⟩
abbrev E := LExpr P

def fv (s : String) : E := .fvar () ⟨s, ()⟩ none
def op (s : String) : E := .op () ⟨s, ()⟩ none
def app (f a : E) : E := .app () f a
def app2 (f a b : E) : E := app (app f a) b
def cI (n : Int) : E := .intConst () n
def cB (b : Bool) : E := .boolConst () b

/-! ### Basic structural matching -/

-- A pattern variable binds to whatever it is matched against.
#guard (LExpr.matchPattern (fv "X") (cI 5)).isSome

-- Constants match only equal constants.
#guard (LExpr.matchPattern (cI 5) (cI 5)).isSome
#guard !(LExpr.matchPattern (cI 5) (cI 6)).isSome

-- Operators match by name.
#guard (LExpr.matchPattern (op "f") (op "f")).isSome
#guard !(LExpr.matchPattern (op "f") (op "g")).isSome

-- Structural match through an application: `(f X)` against `(f 5)`.
#guard (LExpr.matchPattern (app (op "f") (fv "X")) (app (op "f") (cI 5))).isSome
-- Mismatched head operator fails.
#guard !(LExpr.matchPattern (app (op "f") (fv "X")) (app (op "g") (cI 5))).isSome

/-! ### No higher-order matching -/

-- Pattern `(P x)` where `P` is itself a free variable must fail immediately,
-- even against a structurally-shaped term.
#guard !(LExpr.matchPattern (app (fv "P") (fv "x")) (app (op "foo") (cI 5))).isSome

/-! ### Nonlinear patterns -/

-- `(X == X)` matches `(z == z)` ...
#guard (LExpr.matchPattern (.eq () (fv "X") (fv "X")) (.eq () (fv "z") (fv "z"))).isSome
-- ... but not `(z == true)`.
#guard !(LExpr.matchPattern (.eq () (fv "X") (fv "X")) (.eq () (fv "z") (cB true))).isSome

/-! ### Instantiation and rule application -/

-- Applying `(f X) -> (g X)` to `(f 5)` yields `(g 5)`.
#guard
  (RewriteRule.apply ⟨app (op "f") (fv "X"), app (op "g") (fv "X")⟩ (app (op "f") (cI 5)))
    == some (app (op "g") (cI 5))

-- A rule whose lhs does not match returns none.
#guard
  (RewriteRule.apply ⟨app (op "f") (fv "X"), fv "X"⟩ (app (op "h") (cI 5))) == none

-- `RewriteRules.apply` returns the result of the first matching rule.
#guard
  (RewriteRules.apply
    [ ⟨app (op "f") (fv "X"), cI 1⟩,
      ⟨app (op "g") (fv "X"), cI 2⟩ ]
    (app (op "g") (cI 99)))
    == some (cI 2)

-- An idempotent boolean-style rule: `And true X -> X`.
#guard
  (RewriteRule.apply ⟨app2 (op "Bool.And") (cB true) (fv "X"), fv "X"⟩
    (app2 (op "Bool.And") (cB true) (fv "p")))
    == some (fv "p")

-- The same rule does not fire when the first operand is not `true`.
#guard
  (RewriteRule.apply ⟨app2 (op "Bool.And") (cB true) (fv "X"), fv "X"⟩
    (app2 (op "Bool.And") (cB false) (fv "p")))
    == none

/-! ### Matching ignores metadata and type annotations -/

-- A pattern variable with a type annotation still binds; matching ignores the
-- annotation difference on the matched term.
#guard
  (LExpr.matchPattern (LExpr.fvar () ⟨"X", ()⟩ (some ())) (cI 7)).isSome

/-! ### Well-formedness -/

-- Every free var in rhs occurs in lhs: well-formed.
#guard (RewriteRule.isWellFormed ⟨app (op "f") (fv "X"), app (op "g") (fv "X")⟩)
-- rhs has no free vars: well-formed.
#guard (RewriteRule.isWellFormed ⟨app (op "f") (fv "X"), cI 0⟩)
-- rhs introduces a free var `Y` not bound by lhs: not well-formed.
#guard !(RewriteRule.isWellFormed ⟨app (op "f") (fv "X"), app (fv "X") (fv "Y")⟩)

end Lambda.RewritingTests
