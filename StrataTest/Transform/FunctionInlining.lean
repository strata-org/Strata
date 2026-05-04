/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Transform.FunctionInlining

open Core
open Strata

/-! ## FunctionInlining Tests -/

section FunctionInliningTests

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-! ### Test: inlineFuncDefs on a literal is identity -/

#guard_msgs in
#eval do
  let m : Core.ExpressionMetadata := default
  let lit : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
  let result := inlineFuncDefs Core.Factory id lit
  assert! result matches .const _ (.intConst 42)

/-! ### Test: inlineRecFuncDefs at depth 0 is identity -/

#guard_msgs in
#eval do
  let m : Core.ExpressionMetadata := default
  let lit : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
  let result := inlineRecFuncDefs Core.Factory 0 lit
  assert! result matches .const _ (.intConst 42)

/-! ### Test: inlineFuncDefs leaves primitives (no body) unchanged -/

#guard_msgs in
#eval do
  let m : Core.ExpressionMetadata := default
  let negOp := Lambda.LExpr.op m ⟨"Int.Neg", ()⟩ none
  let call := Lambda.LExpr.app m negOp (.const m (.intConst 5))
  let result := inlineFuncDefs Core.Factory id call
  -- Int.Neg is a primitive (no body) — should NOT be inlined
  assert! result matches .app _ _ _

end FunctionInliningTests
