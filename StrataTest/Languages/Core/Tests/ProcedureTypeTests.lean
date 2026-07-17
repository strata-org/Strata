/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.ProcedureType
import Strata.Languages.Core.Factory

meta section

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
                               body := .structured [
                                 Statement.set "y" eb[((~Int.Sub #0) x)] .empty
                               ]
                             }
                            .empty
         return format ans


---------------------------------------------------------------------
-- Type-parameter well-formedness: `Procedure.typeCheck` rejects a signature type
-- variable not declared in `typeArgs` (mirroring `LFunc.type`'s check for
-- functions). This cannot be expressed in concrete `#strata` syntax — the
-- translator rejects the undeclared type before the checker runs (cf. the
-- AST-level Q2d test in `RigidTypeVarsTests`) — so it is exercised directly at
-- the `Procedure.typeCheck` level.
/--
info: error: [Undecl]: type variables [b] appear in the signature but are not declared in typeArgs [a]
-/
#guard_msgs in
#eval do let ans ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                             Program.init
                             { header := {name := "Undecl",
                                          typeArgs := ["a"],
                                          inputs := [("x", mty[%b])],
                                          outputs := [] },
                               spec := { preconditions := [], postconditions := [] },
                               body := .structured [] }
                            .empty
         return format ans

---------------------------------------------------------------------
end Tests
end Core

end
