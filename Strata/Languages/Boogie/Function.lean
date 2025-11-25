/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Statement

---------------------------------------------------------------------

namespace Boogie

open Std (ToFormat Format format)
open Lambda

/-! # Boogie Functions -/

abbrev Function := Lambda.LFunc BoogieLParams

-- Type class instances to enable type class resolution for BoogieLParams.Identifier
instance : DecidableEq BoogieLParams.IDMeta :=
  show DecidableEq Visibility from inferInstance

instance : ToFormat BoogieLParams.IDMeta :=
  show ToFormat Visibility from inferInstance

open LTy.Syntax LExpr.SyntaxMono in
/-- info: ok: ∀[a, b]. (arrow int (arrow a (arrow b (arrow a a)))) -/
#guard_msgs in
#eval do let type ← LFunc.type (T:=BoogieLParams)
                     ({ name := BoogieIdent.unres "Foo",
                        typeArgs := ["a", "b"],
                        inputs := [(BoogieIdent.locl "w", mty[int]), (BoogieIdent.locl "x", mty[%a]), (BoogieIdent.locl "y", mty[%b]), (BoogieIdent.locl "z", mty[%a])],
                        output := mty[%a],
                        body := some (LExpr.fvar () (BoogieIdent.locl "x") none) } : Function)
         return format type

---------------------------------------------------------------------

end Boogie
