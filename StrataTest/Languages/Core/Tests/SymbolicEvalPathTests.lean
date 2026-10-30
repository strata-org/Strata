/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.ProcedureEval

meta section

/-! ## Test: an evaluation error on a path other than the first

The result of a procedure carries the error of any of its paths. Here the then
path exits the block and the else path assigns an undeclared variable, so the
two paths stay separate and only the second one fails. Type checking would
reject this body, so it is built directly.
-/

namespace Core

open Statement Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

/--
info: some [ASSIGN ERROR] Variable u has not been declared yet, so it cannot be assigned to 1.
-/
#guard_msgs in
#eval
  let (E, _) := Core.Procedure.eval Env.init
    { header := { name := "P", typeArgs := [], inputs := [("b", mty[bool])], outputs := [] },
      spec := { preconditions := [], postconditions := [] },
      body := .structured [
        .block "L"
          [.ite (.det eb[b]) [.exit "L" .empty] [Statement.set "u" eb[#1] .empty] .empty]
          .empty,
        Statement.assert "after" eb[#false] .empty] }
  Std.format E.error

end Core

end
