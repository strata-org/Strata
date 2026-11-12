/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core
public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.StmtCFGCallSemanticsProps
public import Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteSubst

/-! # Core Hoare test support

Key results:
- `boolFactory` builds a runtime factory from a model;
- `someValuation` supplies a world over any Core factory;
- `withTwoIntArgs_left` and `withTwoIntArgs_right` read the two arguments of
  `withTwoIntArgs`.
-/

public section

namespace CoreHoareTestSupport

open Imperative

/-- The runtime factory of the model `model`, reading every residual type variable at
`bool`. -/
abbrev boolFactory {F : Lambda.Factory Core.CoreLParams} (model : Lambda.Interp F) :
    Core.Expression.Factory :=
  { factory := F, model := model, tyVarVal := fun _ => .bool }

/-- A world over any Core expression factory: off-factory conditions never hold. -/
def someValuation (factory : Lambda.Factory Core.CoreLParams) :
    Core.Logic.DenoteValuation factory where
  offFactoryHolds := fun _ => False

/-- Override `fv` with two integer arguments. -/
def withTwoIntArgs
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta]
    {tcInterp : Lambda.TyConstrInterp}
    (fv : Lambda.FreeVarVal T tcInterp) (x y : T.Identifier) (a b : Int) :
    Lambda.FreeVarVal T tcInterp :=
  Lambda.IdentInterp.withArgs fv [(x, .int), (y, .int)] (.cons a (.cons b .nil))

/-- The first identifier in `withTwoIntArgs` maps to its supplied value. -/
theorem withTwoIntArgs_left
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta]
    {tcInterp : Lambda.TyConstrInterp}
    (fv : Lambda.FreeVarVal T tcInterp) (x y : T.Identifier) (a b : Int) :
    withTwoIntArgs fv x y a b x .int = a := by
  exact Lambda.IdentInterp.withArgs_get tcInterp fv
    [(x, Lambda.LSort.int), (y, Lambda.LSort.int)]
    (.cons a (.cons b .nil)) x Lambda.LSort.int 0 (by rfl) (by rfl) (by intro j hj; omega)

/-- If the identifiers differ, the second identifier in `withTwoIntArgs` maps
    to its supplied value. -/
theorem withTwoIntArgs_right
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta]
    {tcInterp : Lambda.TyConstrInterp}
    (fv : Lambda.FreeVarVal T tcInterp) (x y : T.Identifier) (a b : Int)
    (hne : y ≠ x) : withTwoIntArgs fv x y a b y .int = b := by
  exact Lambda.IdentInterp.withArgs_get tcInterp fv
    [(x, Lambda.LSort.int), (y, Lambda.LSort.int)]
    (.cons a (.cons b .nil)) y Lambda.LSort.int 1 (by rfl) (by rfl) (by
      intro j hj
      have : j = 0 := by omega
      subst j
      simpa using (fun hxy : x = y => hne hxy.symm))

end CoreHoareTestSupport

end -- public section
