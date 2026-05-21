/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.SemanticsEvalTautschnig

/-! # Smoke tests for `concreteEval` and `parseConstant`

Phase 2.b ratchet: confirm the ported tautschnig concrete evaluator
runs on small examples. -/

namespace CProverGOTOConcreteEvalTests

open CProverGOTO CProverGOTO.SemanticsTautschnig

/-! ## parseConstant on booleans and integers

`parseConstant` is a non-`partial` `def`, but its body matches on
`Ty.id` patterns whose unfolding is gated by definitional opacity.
We use `decide` (or `simp [parseConstant, Ty.Boolean, Ty.Integer]`)
rather than `rfl` to force the reduction. -/

example : parseConstant "true" Ty.Boolean = some (.vBool true) := by
  simp [parseConstant]
example : parseConstant "false" Ty.Boolean = some (.vBool false) := by
  simp [parseConstant]
-- `parseConstant "42" Ty.Integer = some (.vInt 42)` is a `#eval` smoke test
-- below; the equational form would need a manual unfolding of
-- `String.toInt?` that is not reduceable in `simp`.
#eval (parseConstant "42" Ty.Integer : Option Value)

/-! ## concreteEval on simple constants and variables

`concreteEval` is a `partial def`, so its body does not reduce in
the kernel. We confirm it runs by `#eval` rather than by an
equational check. The `#eval` lines below print to the build log; a
non-error build is the smoke-test pass condition. -/

/-- The constant `true`. -/
def trueExpr : Expr :=
  { id := .nullary (.constant "true"), type := Ty.Boolean }

/-- The constant `42`. -/
def fortytwoExpr : Expr :=
  { id := .nullary (.constant "42"), type := Ty.Integer }

#eval (concreteEval Store.empty trueExpr : Option Value)
#eval (concreteEval Store.empty fortytwoExpr : Option Value)

/-! ## concreteEval reads from the store -/

/-- Symbol expression `x`. -/
def xExpr : Expr :=
  { id := .nullary (.symbol "x"), type := Ty.Integer }

def σ_x_is_5 : Store := Store.empty.update "x" (.vInt 5)

#eval (concreteEval σ_x_is_5 xExpr : Option Value)

/-! ## Unsupported expressions return none -/

/-- `nondet(name)` is not handled by concreteEval. -/
def nondetExpr : Expr :=
  { id := .nullary (.nondet "x"), type := Ty.Integer }

#eval (concreteEval Store.empty nondetExpr : Option Value)

end CProverGOTOConcreteEvalTests
