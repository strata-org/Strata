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

/-! ### Test: evalConcreteFactoryApps on a program with negation -/

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
  -- Just check it doesn't crash
  assert! pgm.decls.length > 0

/-! ### Test: evalConcreteFactoryApps recurses into ite -/

#guard_msgs in
#eval do
  let m : Core.ExpressionMetadata := default
  let t : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 1)
  let e : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 2)
  let c : Lambda.LExpr Core.CoreLParams.mono := .const m (.boolConst true)
  let ite := Lambda.LExpr.ite m c t e
  let result := evalConcreteFactoryApps Core.Factory ite
  -- ite with constant condition is not simplified by factory eval
  -- (that's the evaluator's job), but subexpressions are recursed into
  assert! result matches .ite _ _ _ _

end FactoryEvalTests
