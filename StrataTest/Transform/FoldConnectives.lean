/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Transform.FoldConnectives

meta section

/-! # Folding boolean connectives with a literal argument

Each rule of `connectiveValue?`, with the literal on either side, and the
bottom-up fold of a nested term. -/

namespace Core.FoldConnectives.Tests

private def p : Expression.Expr := .fvar () ⟨"p", ()⟩ none
private def lit (b : Bool) : Expression.Expr := .const () (.boolConst b)
private def bin (op a b : Expression.Expr) : Expression.Expr :=
  .app () (.app () op a) b

#guard connectiveValue? (bin boolAndOp p (lit false)) == some (lit false)
#guard connectiveValue? (bin boolAndOp (lit false) p) == some (lit false)
#guard connectiveValue? (bin boolAndOp p (lit true)) == some p
#guard connectiveValue? (bin boolAndOp (lit true) p) == some p
#guard connectiveValue? (bin boolOrOp p (lit true)) == some (lit true)
#guard connectiveValue? (bin boolOrOp (lit true) p) == some (lit true)
#guard connectiveValue? (bin boolOrOp p (lit false)) == some p
#guard connectiveValue? (bin boolOrOp (lit false) p) == some p
#guard connectiveValue? (bin boolImpliesOp p (lit true)) == some (lit true)
#guard connectiveValue? (bin boolImpliesOp (lit false) p) == some (lit true)
#guard connectiveValue? (bin boolImpliesOp (lit true) p) == some p
#guard connectiveValue? (bin boolImpliesOp p (lit false)) == none
#guard connectiveValue? (bin boolOrOp p p) == none

-- `(p || true) && (p ==> false)` folds to `p ==> false`.
#guard foldConnectives (bin boolAndOp (bin boolOrOp p (lit true))
    (bin boolImpliesOp p (lit false)))
  == bin boolImpliesOp p (lit false)
#guard foldConnectives (bin boolOrOp p p) == bin boolOrOp p p

end Core.FoldConnectives.Tests

end
