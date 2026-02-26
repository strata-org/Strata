/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF

namespace Lambda.LExpr.WFTests

open Lambda

-- Fix the type parameters so BEq resolves
abbrev Params : LExprParams := ⟨Unit, Unit⟩
abbrev MonoExpr := LExpr Params.mono

-- Shorthand constructors with fixed type
def c (n : Int) : MonoExpr := .const () (.intConst n)
def bv (i : Nat) : MonoExpr := .bvar () i
def fv (name : String) (ty : Option LMonoTy := .none) : MonoExpr := .fvar () name ty
def lam (e : MonoExpr) : MonoExpr := .abs () .none e
def ap (f a : MonoExpr) : MonoExpr := .app () f a
def eq' (a b : MonoExpr) : MonoExpr := .eq () a b
def ite' (c t f : MonoExpr) : MonoExpr := .ite () c t f
def qa (e : MonoExpr) : MonoExpr := .quant () .all .none (bv 0) e

/-! ### liftBVars tests -/

-- Constant is identity
#guard liftBVars 1 (c 5) == c 5

-- fvar is identity
#guard liftBVars 1 (fv "x" (.some .int)) == fv "x" (.some .int)

-- bvar 0 with default cutoff 0, lift by 1 → bvar 1
#guard liftBVars 1 (bv 0) == bv 1

-- bvar 1, lift by 2 → bvar 3
#guard liftBVars 2 (bv 1) == bv 3

-- bvar below cutoff is not shifted
#guard liftBVars 1 (bv 0) (cutoff := 1) == bv 0

-- bvar at cutoff is shifted
#guard liftBVars 1 (bv 1) (cutoff := 1) == bv 2

-- abs increments cutoff: abs(bvar 0) stays (bound by abs)
#guard liftBVars 1 (lam (bv 0)) == lam (bv 0)

-- abs(bvar 1): free relative to abs, becomes 2
#guard liftBVars 1 (lam (bv 1)) == lam (bv 2)

-- Nested abs: abs(abs(bvar 2)) → abs(abs(bvar 3))
#guard liftBVars 1 (lam (lam (bv 2))) == lam (lam (bv 3))

-- Recurses into app
#guard liftBVars 1 (ap (bv 0) (bv 1)) == ap (bv 1) (bv 2)

-- Recurses into eq
#guard liftBVars 1 (eq' (bv 0) (bv 1)) == eq' (bv 1) (bv 2)

-- Recurses into ite
#guard liftBVars 1 (ite' (bv 0) (bv 1) (bv 2)) == ite' (bv 1) (bv 2) (bv 3)

/-! ### substFvarLifting tests -/

-- Basic: replace fvar "x" with a constant
#guard substFvarLifting (fv "x" (.some .int)) "x" (c 42) == c 42

-- Non-matching fvar untouched
#guard substFvarLifting (fv "y" (.some .int)) "x" (c 42) == fv "y" (.some .int)

-- KEY TEST: substituting fvar with bvar under a binder lifts the bvar.
-- substFvarLifting (abs(fvar "x")) "x" (bvar 0)
-- Under abs, depth=1, so bvar 0 → bvar 1
#guard substFvarLifting (lam (fv "x")) "x" (bv 0) == lam (bv 1)

-- Compare with substFvar (no lifting) — bvar 0 stays 0 (captured by abs)
#guard substFvar (lam (fv "x")) "x" (bv 0) == lam (bv 0)

-- Double nesting: abs(abs(fvar "x")) with bvar 0
-- depth=2, so bvar 0 → bvar 2
#guard substFvarLifting (lam (lam (fv "x"))) "x" (bv 0) == lam (lam (bv 2))

-- Top level (depth=0) does not lift
#guard substFvarLifting (fv "x") "x" (bv 0) == bv 0

-- Under quant also lifts
#guard substFvarLifting (qa (fv "x")) "x" (bv 0) == qa (bv 1)

-- In app (no binder) does not lift
#guard substFvarLifting (ap (fv "x") (fv "x")) "x" (bv 0) == ap (bv 0) (bv 0)

/-! ### substFvarsLifting tests -/

-- Multiple substitutions under abs: both lifted by 1
#guard substFvarsLifting
    (lam (ap (fv "x") (fv "y")))
    [("x", bv 0), ("y", bv 1)]
    == lam (ap (bv 1) (bv 2))

-- Empty substitution is identity
#guard substFvarsLifting (fv "x") [] == fv "x"

end Lambda.LExpr.WFTests
