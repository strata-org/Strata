/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.CFGSemanticsProps

/-! # Tests for `EvalCmdExtE.induct` and `StepCFGE` case analysis

`EvalCmdExtE.induct` proves, by `induction … using`, that `EvalCmdExtE` is
monotone in the procedure table: a derivation under `π` is a derivation under any
`π'` that resolves every name `π` resolves to the same procedure.  The call case
uses the induction hypothesis for every command step of the callee body,
structured or CFG, at any call depth.  Case analysis on a `StepCFGE` step
shows that a CFG step from `.atBlock` emits no events. -/

namespace EvalCmdExtEInductTest

open Imperative

variable {P : PureExpr}
  [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [ProcedureTypeInstantiation P Hdr]
  [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]

example {π π' : String → Option (Procedure P (CmdExt P) Hdr)}
    (hπ : ∀ n tyArgs p, Calls.typeInstantiatedCallee π n tyArgs = some p →
      Calls.typeInstantiatedCallee π' n tyArgs = some p)
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : CmdExt P} {evs : Trace P}
    (h : EvalCmdExtE π fac σ c σ' evs) : EvalCmdExtE π' fac σ c σ' evs := by
  induction h using EvalCmdExtE.induct with
  | cmd_sem h => exact .cmd_sem h
  | call_sem hn hno hentry _ hexit ih =>
    rcases ih with ⟨ss, ρ', _, hss, rfl, hrun⟩ | ⟨g, ρ', _, hg, rfl, hrun⟩
    · exact .call_sem (hπ _ _ _ hn) hno hentry
        (hss ▸ .structured (hrun.imp fun _ _ _ _ _ ⟨_, h⟩ => h)) hexit
    · have hrun' := hrun.imp fun _ _ _ hs => hs.imp fun _ _ _ _ _ ⟨_, h⟩ => h
      exact .call_sem (hπ _ _ _ hn) hno hentry
        (hg ▸ .cfg hrun') hexit
  | call_abstract_sem hn hb hentry hhavoc hexit =>
    exact .call_abstract_sem (hπ _ _ _ hn) hb hentry hhavoc hexit

example {l CmdT : Type} {EventT : Type _} [BEq l] [HasVal P]
    {EvalCmd : EvalCmdParamE P CmdT EventT}
    {cfg : CFG l (DetBlock l CmdT P)} {t : l} {ρ : Env P}
    {tr : List EventT} {c' : CFGConfig l CmdT P}
    (h : StepCFGE P EvalCmd (.atBlock cfg t ρ) tr c') : tr = [] := by
  generalize hc : CFGConfig.atBlock cfg t ρ = c at h
  cases h <;> first | rfl | cases hc

end EvalCmdExtEInductTest
