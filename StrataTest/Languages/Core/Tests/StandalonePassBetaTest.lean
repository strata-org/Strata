/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Transform.GuardProp
import Strata.Transform.DefInline
import Strata.Languages.Core
import StrataTest.Languages.Core.Tests.ObligationProgramTestUtils

/-! # The standalone passes keep `noBetaRedexes`

`guardFwdPipelinePhase`, `defInlinePipelinePhase` and `guardPropPipelinePhase` claim to preserve
`noBetaRedexes`. On a body that defines a function value as a conditional of two abstractions
and applies it, none of `guardFwd`, `defInline (.after addFold)` and `guardProp` leaves a redex:
guard forwarding and guard propagation substitute only variables and non-function literals, and
the standalone inlining substitutes the conditional without collapsing it. -/

namespace StandalonePassBetaTest

open Core Lambda Imperative ObligationProgramTestUtils

def intToInt : LMonoTy := .arrow .int .int
def g : Expression.Expr := .fvar Core.valueLoc (id' "g") (some .bool)
def f : Expression.Expr := .fvar Core.valueLoc (id' "f") (some intToInt)
def idFn : Expression.Expr := .abs Core.valueLoc "x" (some .int) (.bvar Core.valueLoc 0)

/-- `havoc g; f := ite(g, λ x. x, λ x. x); assume g; assert f(1) == 1`. -/
def body : Statements :=
  [.cmd (.cmd (.init (id' "g") (.forAll [] .bool) .nondet md)),
   .cmd (.cmd (.init (id' "f") (.forAll [] intToInt) (.det (.ite Core.valueLoc g idFn idFn)) md)),
   .cmd (.cmd (.assume "h" g md)),
   assert' "a" (.eq Core.valueLoc (.app Core.valueLoc f (int 1)) (int 1))]

/-- Every expression of `ss` is free of beta redexes, the check of `noBetaRedexes`. -/
def noRedex (ss : Statements) : Bool := (Statements.allExprs ss).all LExpr.noBetaRedex

#guard noRedex body
#guard noRedex (GuardFwd.guardFwd body)
#guard noRedex (DefInline.defInline (.after DefInline.addFold) body)
#guard noRedex (GuardProp.guardProp body)
#guard noRedex (GuardProp.guardProp (DefInline.defInline (.after DefInline.addFold)
  (GuardFwd.guardFwd body)))

end StandalonePassBetaTest
