/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.ProcedureType

namespace Core

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

/--
info: ok: (procedure P (x : int, out y : int)
 spec {
   requires [|0_lt_x|]: 0 < x;
   ensures [ret_y_lt_0]: y < 0;
   } {
   y := 0 - x;
 };
 ,
 context:
 types:   ⏎
 aliases: [] state: tyGen: 6 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: [])
-/
#guard_msgs in
#eval do let ans ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                             Program.init
                             { header := {name := "P",
                                          typeArgs := [],
                                          inputs := [("x", mty[int])],
                                          outputs := [("y", mty[int])] },
                               spec := { preconditions := [("0_lt_x", ⟨eb[((~Int.Lt #0) x)], .Default, #[]⟩)],
                                         postconditions := [("ret_y_lt_0", ⟨eb[((~Int.Lt y) #0)], .Default, #[]⟩)] },
                               body := [
                                 Statement.set "y" eb[((~Int.Sub #0) x)] .empty
                               ]
                             }
                            .empty
         return format ans


---------------------------------------------------------------------
end Tests
end Core
