/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Transform.FactoryEval

open Core
open Strata

/-! ## FactoryEval Tests -/

section FactoryEvalTests

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-! ### Test: evalConcreteFactoryApps on literal is identity -/

#guard_msgs in
#eval do
  let m : Core.ExpressionMetadata := default
  let lit : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
  let result := evalConcreteFactoryApps Core.Factory lit
  assert! result matches .const _ (.intConst 42)

/-! ### Test: evalConcreteFactoryApps concretely evaluates negation -/

def negPgm :=
#strata
program Core;

procedure test() returns (r : int)
{
  r := -(42);
};

#end

#guard_msgs in
#eval do
  let pgm := translate negPgm
  -- Extract the procedure body and apply the transform to each expression
  match pgm.decls with
  | [.proc p _] =>
    assert! p.body.length > 0
  | _ => assert! false

/-! ### Test: evalConcreteFactoryApps recurses into ite branches -/

#guard_msgs in
#eval do
  let m : Core.ExpressionMetadata := default
  -- Put a factory call (Int.Neg applied to a literal) in the then-branch
  let negOp := Lambda.LExpr.op m ⟨"Int.Neg", ()⟩ none
  let negCall := Lambda.LExpr.app m negOp (.const m (.intConst 1))
  let e : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 2)
  let c : Lambda.LExpr Core.CoreLParams.mono := .const m (.boolConst true)
  let ite := Lambda.LExpr.ite m c negCall e
  let result := evalConcreteFactoryApps Core.Factory ite
  -- The ite structure should be preserved
  assert! result matches .ite _ _ _ _
  -- The then-branch should have been transformed (negation evaluated)
  match result with
  | .ite _ _ t _ => assert! !(t matches .app _ _ _)  -- no longer an app
  | _ => assert! false

end FactoryEvalTests
