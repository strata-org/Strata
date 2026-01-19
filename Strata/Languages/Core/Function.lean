/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Statement

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Lambda

/-! # Strata Core Functions -/

abbrev Function := Lambda.LFunc CoreLParams

-- Type class instances to enable type class resolution for CoreLParams.Identifier
instance : DecidableEq CoreLParams.IDMeta :=
  show DecidableEq Visibility from inferInstance

instance : ToFormat CoreLParams.IDMeta :=
  show ToFormat Visibility from inferInstance

open LTy.Syntax LExpr.SyntaxMono in
/-- info: ok: ∀[a, b]. (arrow int (arrow a (arrow b (arrow a a)))) -/
#guard_msgs in
#eval do let type ← LFunc.type (T:=CoreLParams)
                     ({ name := CoreIdent.unres "Foo",
                        typeArgs := ["a", "b"],
                        inputs := [(CoreIdent.locl "w", mty[int]), (CoreIdent.locl "x", mty[%a]), (CoreIdent.locl "y", mty[%b]), (CoreIdent.locl "z", mty[%a])],
                        output := mty[%a],
                        body := some (LExpr.fvar () (CoreIdent.locl "x") none) } : Function)
         return format type

---------------------------------------------------------------------

end Core
