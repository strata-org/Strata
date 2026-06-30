/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.StatementType
meta import Strata.Languages.Core.ProcedureType
import Strata.Languages.Core.Factory

/-! Local `var` annotations in Core must be MONOMORPHIC (`preprocess` Part A) and
    may only reference the enclosing procedure's type parameters (`preprocess`
    Part B). A polymorphic annotation `∀a. a→a` is rejected outright, and a bare
    free type variable with no enclosing `proc<…>` is rejected as out of scope. -/

meta section

namespace Core.MonoLocalBindingTest

open Std (ToFormat Format format)
open Procedure Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

-- Part A: a polymorphic annotation `var x : ∀a. a→a` is rejected. Instantiating it
-- would leak a fresh, non-rigid type variable into the ambient context (the
-- type-soundness bug behind this restriction), so `preprocess` forbids it.
/--
info: error: Variable annotation must be monomorphic, but got polymorphic type ∀[α]. (arrow α α) (type variables [α] are bound)
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                    [ .init "x" t[∀α. %α → %α] (.det (.abs () "y" none (.bvar () 0))) .empty ]
         return format ans.fst

-- Part B (out of scope): `var z : a` with no enclosing `proc<a>` is rejected — the
-- free type variable `a` is not a procedure type parameter (not rigid).
/--
info: error: Variable annotation references type variables [a] that are not procedure type parameters
-/
#guard_msgs in
#eval do let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none
                    [ .init "z" t[%a] .nondet .empty ]
         return format ans.fst

-- Part B (in scope): inside `procedure P<t>(x : t)`, the body annotation `var z : t`
-- is accepted. The procedure renames `t` to a fresh rigid type variable in the body
-- environment, so the normalized annotation references only that rigid var. This
-- mirrors how a function body may refer to its signature type parameters.
/--
info: ok: (procedure P (x : t)
 {
   var z : t := x;
 };
 ,
 context:
 types:   ⏎
 aliases: [] state: tyGen: 1 tyPrefix: $__ty exprGen: 0 exprPrefix: $__var subst: [(t, $__ty0)])
-/
#guard_msgs in
#eval do let ans ← typeCheck { LContext.default with functions := Core.Factory } TEnv.default
                    Program.init
                    { header := { name := "P", typeArgs := ["t"],
                                  inputs := [("x", mty[%t])], outputs := [] },
                      spec := { preconditions := [], postconditions := [] },
                      body := .structured [ Statement.init "z" t[%t] (.det eb[x]) .empty ] }
                    .empty
         return format ans

end Core.MonoLocalBindingTest
end
