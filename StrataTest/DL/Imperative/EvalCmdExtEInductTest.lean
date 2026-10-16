/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.CFGSemanticsProps

/-! # Tests for `EvalCmdExtE.induct` and `StepCFGE.casesRules`

`EvalCmdExtE.induct` proves, by `induction … using`, that `EvalCmdExtE` is
monotone in the procedure table: a derivation under `π` is a derivation under any
`π'` that resolves every name `π` resolves to the same procedure.  The call case
uses the induction hypothesis for every command step of the callee body,
structured or CFG, at any call depth.  `StepCFGE.casesRules` proves, by
`cases … using`, that a CFG step from `.atBlock` emits no events. -/

namespace EvalCmdExtEInductTest

open Imperative

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]

example {π π' : String → Option (Procedure P (CmdExt P) Hdr)}
    (hπ : ∀ n p, π n = some p → π' n = some p)
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : CmdExt P} {evs : Trace P}
    (h : EvalCmdExtE π fac σ c σ' evs) : EvalCmdExtE π' fac σ c σ' evs := by
  induction h using EvalCmdExtE.induct with
  | cmd_sem h => exact .cmd_sem h
  | call_sem hn hentry _ hexit ih =>
    rcases ih with ⟨ss, ρ', hss, rfl, hrun⟩ | ⟨g, σ', f, hg, rfl, hrun⟩
    · exact .call_sem (hπ _ _ hn) hentry
        (hss ▸ .structured (hrun.imp fun _ _ _ _ _ ⟨_, h⟩ => h)) hexit
    · have hrun' := hrun.imp fun _ _ _ hs => hs.imp fun _ _ _ _ _ ⟨_, h⟩ => h
      exact .call_sem (hπ _ _ hn) hentry
        (hg ▸ .cfg (CFGRunExtE_iff_stepCFGStarE.mpr hrun')) hexit

example {l CmdT EventT : Type} [BEq l] [HasVal P]
    {EvalCmd : EvalCmdParamE P CmdT EventT} {fac : P.Factory}
    {cfg : CFG l (DetBlock l CmdT P)} {t : l} {σ : SemanticStore P} {f : Bool}
    {tr : List EventT} {c' : CFGConfig l CmdT P}
    (h : StepCFGE P EvalCmd fac cfg (.atBlock t σ f) tr c') : tr = [] := by
  generalize hc : CFGConfig.atBlock t σ f = c at h
  cases h using StepCFGE.casesRules <;> first | rfl | cases hc

end EvalCmdExtEInductTest
