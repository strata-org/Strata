/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.ProcedureEval

namespace Core

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

/-

info: Error:
none
Subst Map:
(x, ($__x0 : int)) (y, ($__y1 : int))
Expression Env:
State:
-/
#guard_msgs in
#eval do let E := Env.init
         let (_proc, E) := evalOne E
              { header := {name := "P",
                           typeArgs := [],
                           inputs := [("x", mty[int])],
                           outputs := [("y", mty[int])] },
                spec := {
                    modifies := [],
                    preconditions := [("0_lt_x", ⟨eb[((~Int.Lt #0) x)], .Default, #[]⟩)],
                    postconditions := [("ret_y_lt_0", ⟨eb[((~Int.Lt y) #0)], .Default, #[]⟩)] },
                body := [
                  Statement.set "y" eb[(~Int.Neg x)]
                ]
              }
          return format E


end Tests
---------------------------------------------------------------------

end Core
