/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.LangDef

/-! # Event-language termination

Defines two complementary termination notions for `EventLang`:

- `EventLang.TerminatesAt` describes one concrete execution, including its
  emitted trace and final environment.
- `EventLang.Terminates` requires every possible execution to terminate without
  getting stuck, while allowing nondeterministic executions to produce different
  traces and final environments.
-/

public section

namespace Strata.Logic

open Imperative

/-- `s` terminates from `ρ₀` at `ρ'` along `trace` either normally or by
exiting with a label. Hoare triples constrain both outcomes because an enclosing
block may catch an exiting outcome and continue execution. -/
@[expose] abbrev EventLang.TerminatesAt
    {P : PureExpr} {EventT : Type} (EL : EventLang P EventT)
    (s : EL.StmtT) (ρ₀ : Env P) (trace : List EventT) (ρ' : Env P) : Prop :=
  EL.traceStar (EL.stmtCfg s ρ₀) trace (EL.terminalCfg ρ') ∨
    ∃ label, EL.traceStar (EL.stmtCfg s ρ₀) trace (EL.exitingCfg label ρ')

/-- A configuration must terminate when it is final, or when it can take a step
and every possible successor must terminate. The progress premise excludes stuck
non-final configurations; the definition excludes infinite executions,
including divergent nondeterministic branches. -/
inductive EventLang.MustTerminate
    {P : PureExpr} {EventT : Type} (EL : EventLang P EventT) : EL.CfgT → Prop where
  | terminal (ρ : Env P) : EL.MustTerminate (EL.terminalCfg ρ)
  | exiting (label : String) (ρ : Env P) :
      EL.MustTerminate (EL.exitingCfg label ρ)
  | step {cfg : EL.CfgT}
      (progress : ∃ emitted cfg', EL.step cfg emitted cfg')
      (successors : ∀ emitted cfg', EL.step cfg emitted cfg' → EL.MustTerminate cfg') :
      EL.MustTerminate cfg

/-- Every execution of `s` from `ρ₀` eventually reaches a terminal or exiting
configuration. In particular, no execution gets stuck or diverges. The final
environment and emitted trace may differ across nondeterministic executions. -/
@[expose] abbrev EventLang.Terminates
    {P : PureExpr} {EventT : Type} (EL : EventLang P EventT)
    (s : EL.StmtT) (ρ₀ : Env P) : Prop :=
  EL.MustTerminate (EL.stmtCfg s ρ₀)

end Strata.Logic

end -- public section
