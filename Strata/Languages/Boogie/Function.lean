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

<<<<<<< HEAD
abbrev Function := Lambda.LFunc BoogieLParams

-- Type class instances to enable type class resolution for BoogieLParams.Identifier
instance : DecidableEq BoogieLParams.Identifier :=
  show DecidableEq BoogieIdent from inferInstance

instance : ToFormat BoogieLParams.Identifier :=
  show ToFormat BoogieIdent from inferInstance
=======
abbrev Function := Lambda.LFunc BoogieLParams
>>>>>>> origin/main

open LTy.Syntax LExpr.SyntaxMono in
/-- info: ok: ∀[a, b]. (arrow int (arrow a (arrow b (arrow a a)))) -/
#guard_msgs in
<<<<<<< HEAD
#eval do let type ← LFunc.type (T:=BoogieLParams)
                     ({ name := BoogieIdent.unres "Foo",
                        typeArgs := ["a", "b"],
                        inputs := [(BoogieIdent.locl "w", mty[int]), (BoogieIdent.locl "x", mty[%a]), (BoogieIdent.locl "y", mty[%b]), (BoogieIdent.locl "z", mty[%a])],
                        output := mty[%a],
                        body := some (LExpr.fvar () (BoogieIdent.locl "x") none) } : Function)
=======
#eval do let type ← LFunc.type (IDMeta:=Visibility)
                     ({ name := (BoogieIdent.unres "Foo"),
                        typeArgs := ["a", "b"],
                        inputs := [((BoogieIdent.locl "w"), mty[int]), ((BoogieIdent.locl "x"), mty[%a]), ((BoogieIdent.locl "y"), mty[%b]), ((BoogieIdent.locl "z"), mty[%a])],
                        output := mty[%a],
                        body := some (.fvar (BoogieIdent.locl "x") none) } : Function)
>>>>>>> origin/main
         return format type

---------------------------------------------------------------------

end Boogie
