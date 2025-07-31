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

abbrev Function := Lambda.LFunc BoogieIdent

open LTy.Syntax LExpr.Syntax in
/-- info: ok: ∀[a, b]. (arrow int (arrow a (arrow b (arrow a a)))) -/
#guard_msgs in
#eval do let type ← LFunc.type (Identifier:=BoogieIdent)
                     ({ name := (.unres, "Foo"),
                        typeArgs := ["a", "b"],
                        inputs := [((.locl, "w"), mty[int]), ((.locl, "x"), mty[%a]), ((.locl, "y"), mty[%b]), ((.locl, "z"), mty[%a])],
                        output := mty[%a],
                        body := some (.fvar (.locl, "x") none) } : Function)
         return format type

---------------------------------------------------------------------

end Boogie
