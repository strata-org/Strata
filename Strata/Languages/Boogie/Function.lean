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

abbrev Function := Lambda.LFunc Visibility

open LTy.Syntax LExpr.SyntaxMono in
/-- info: ok: ∀[a, b]. (arrow int (arrow a (arrow b (arrow a a)))) -/
#guard_msgs in
#eval do let type ← LFunc.type (IDMeta:=Visibility)
                     ({ name := (BoogieIdent.unres "Foo"),
                        typeArgs := ["a", "b"],
                        inputs := [((BoogieIdent.locl "w"), mty[int]), ((BoogieIdent.locl "x"), mty[%a]), ((BoogieIdent.locl "y"), mty[%b]), ((BoogieIdent.locl "z"), mty[%a])],
                        output := mty[%a],
                        body := some (.fvar (BoogieIdent.locl "x") none) } : Function)
         return format type

---------------------------------------------------------------------

end Boogie
