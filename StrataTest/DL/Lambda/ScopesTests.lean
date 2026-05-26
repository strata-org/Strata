/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Scopes

/-! ## Tests for Scopes -/

namespace Lambda
open Std (ToFormat Format format)
open LTy.Syntax LExpr.SyntaxMono

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TestParams.Identifier where
  coe s := Identifier.mk s ()

/--
info: (x : int) → #8
(z : int) → (if #true then #100 else (z : int))
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
              [("x", (mty[int], .intConst () 8)),
               ("z", (mty[int], .intConst () 100))]
              [("x", (mty[int], .intConst () 8))]

/--
info: (x : int) → (if #true then #8 else (x : int))
(z : int) → (if #true then #100 else (z : int))
(y : int) → (if #true then (y : int) else #8)
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
              [("x", (mty[int], .intConst () 8)),
               ("z", (mty[int], .intConst () 100))]
              [("y", (mty[int], .intConst () 8))]

/--
info: (y : int) → (if #true then #8 else (y : int))
(x : int) → (if #true then (x : int) else #8)
(z : int) → (if #true then (z : int) else #100)
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
              [("y", (mty[int], .intConst () 8 ))]
              [("x", (mty[int], .intConst () 8)),
               ("z", (mty[int], .intConst () 100))]

/--
info: (a : int) → (if #true then #8 else (a : int))
(x : int) → (if #true then #800 else #8)
(b : int) → (if #true then #900 else (b : int))
(z : int) → (if #true then (z : int) else #100)
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
                [("a", (mty[int], (.intConst () 8))),
                 ("x", (mty[int], (.intConst () 800))),
                 ("b", (mty[int], (.intConst () 900)))]
                [("x", (mty[int], (.intConst () 8))),
                 ("z", (mty[int], (.intConst () 100)))]

end Lambda
