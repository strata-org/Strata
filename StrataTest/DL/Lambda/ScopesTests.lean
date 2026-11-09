/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.Scopes

/-! ## Tests for Scopes -/

meta section
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

-- `m2` lists `x` twice, first: the merged entry comes first and shadows the later one.
/--
info: (x : int) → (if #true then #1 else #2)
(x : int) → (if #true then (x : int) else #3)
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
                [("x", (mty[int], (.intConst () 1)))]
                [("x", (mty[int], (.intConst () 2))),
                 ("x", (mty[int], (.intConst () 3)))]

-- The same, with `x` not first in `m2`: the later entry for `x` is dropped.
/--
info: (x : int) → (if #true then #1 else #2)
(y : int) → (if #true then (y : int) else #0)
-/
#guard_msgs in
#eval format $ Scope.merge (T:=TestParams) (.boolConst () true)
                [("x", (mty[int], (.intConst () 1)))]
                [("y", (mty[int], (.intConst () 0))),
                 ("x", (mty[int], (.intConst () 2))),
                 ("x", (mty[int], (.intConst () 3)))]

end Lambda
end
