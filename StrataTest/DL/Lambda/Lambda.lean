/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.Lambda
import Strata.DL.Lambda.IntBoolFactory

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)
open LExpr LTy


section Test
open LState LExpr LExpr.SyntaxMono

/--
info: error: A function of name Int.Add already exists! Redefinitions are not allowed.
Existing Function: func Int.Add :  ((x : int) (y : int)) → int;
New Function:func Int.Add :  () → int;
-/
#guard_msgs in
#eval do let F ← IntBoolFactory.addFactoryFunc { name := "Int.Add",
                                                 inputs := [],
                                                 output := .tcons "int" [] }
         let ans ← typeCheckAndPartialEval TypeFactory.default F esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) #1))) #100)]
         return format ans

/--
info: Annotated expression:
(((~Int.Le : (arrow int (arrow int bool))) (((~Int.Div : (arrow int (arrow int int))) #300) (((~Int.Add : (arrow int (arrow int int))) #2) #1))) #100)

---
info: #true
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval TypeFactory.default  IntBoolFactory
                esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) #1))) #100)]

/--
info: Annotated expression:
((~Int.Div : (arrow int (arrow int int))) (((~Int.Add : (arrow int (arrow int int))) #2) #1))

---
info: (λ (((~Int.Div : (arrow int (arrow int int))) #3) %0))
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval TypeFactory.default  IntBoolFactory
               esM[((~Int.Div ((~Int.Add #2) #1)))]
/--
info: Annotated expression:
((λ (%0 #2)) ((~Int.Div : (arrow int (arrow int int))) #300))

---
info: #150
-/
#guard_msgs in
#eval format $ typeCheckAndPartialEval TypeFactory.default  IntBoolFactory
                esM[((λ (%0 #2)) (~Int.Div #300))]

end Test

---------------------------------------------------------------------
