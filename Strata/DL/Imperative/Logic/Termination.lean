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

It also names the two ways an execution can fail to finish: `EventLang.CanDiverge`,
saying some infinite sequence of steps starts at a configuration, and
`EventLang.MayGetStuck`, saying some execution reaches a `Stuck` configuration,
one that is not `Final` and has no step. `TerminationProps` proves that a
configuration must terminate exactly when neither holds.

Divergence is stated with functions `ℕ → CfgT` and bounded reachability
`EventLang.ReachesWithin`, with no coinduction: an infinite execution is a
sequence of configurations each of which steps to the next.
-/

public section

namespace Strata.Logic

open Imperative

/-- `s` terminates from `ρ₀` at `ρ'` along `trace` either normally or by
exiting with a label. Hoare triples constrain both outcomes because an enclosing
block may catch an exiting outcome and continue execution. -/
abbrev EventLang.TerminatesAt
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

/-- `cfg` is finished: the statement completed normally, or by an exit that no
    enclosing block caught. An exit still inside a block is not final: the
    configuration is then a block or sequence frame around the exiting one, and
    it steps on once the block catches the exit or passes it outward. -/
@[expose] def EventLang.Final
    {P : PureExpr} {EventT : Type} (EL : EventLang P EventT) (cfg : EL.CfgT) : Prop :=
  (∃ ρ, cfg = EL.terminalCfg ρ) ∨ ∃ label ρ, cfg = EL.exitingCfg label ρ

/-- `cfg` is stuck: it has not finished and can take no step. -/
@[expose] def EventLang.Stuck
    {P : PureExpr} {EventT : Type} (EL : EventLang P EventT) (cfg : EL.CfgT) : Prop :=
  ¬ EL.Final cfg ∧ ∀ emitted cfg', ¬ EL.step cfg emitted cfg'

/-- Some execution from `cfg` reaches a stuck configuration. -/
@[expose] def EventLang.MayGetStuck
    {P : PureExpr} {EventT : Type} (EL : EventLang P EventT) (cfg : EL.CfgT) : Prop :=
  ∃ trace cfg', EL.traceStar cfg trace cfg' ∧ EL.Stuck cfg'

/-- Every execution of `s` from `ρ₀` eventually reaches a terminal or exiting
configuration. In particular, no execution gets stuck or diverges. The final
environment and emitted trace may differ across nondeterministic executions. -/
abbrev EventLang.Terminates
    {P : PureExpr} {EventT : Type} (EL : EventLang P EventT)
    (s : EL.StmtT) (ρ₀ : Env P) : Prop :=
  EL.MustTerminate (EL.stmtCfg s ρ₀)

/-- `cfg` reaches `cfg'` in at most `n` steps, emitting `trace`. -/
abbrev EventLang.ReachesWithin {P : PureExpr} {EventT : Type} (EL : EventLang P EventT) :
    Nat → EL.CfgT → List EventT → EL.CfgT → Prop :=
  ReflTransTraceN EL.step

/-! ## Divergence -/

/-- An infinite sequence of configurations. -/
abbrev EventLang.Transitions {P : PureExpr} {EventT : Type} (EL : EventLang P EventT) :=
  Nat → EL.CfgT

/-- `f` diverges: each of its configurations steps to the next. -/
@[expose] def EventLang.Diverges {P : PureExpr} {EventT : Type} (EL : EventLang P EventT)
    (f : EL.Transitions) : Prop :=
  ∀ i, ∃ emitted, EL.step (f i) emitted (f (i + 1))

/-- Some diverging sequence starts at `cfg`. -/
@[expose] def EventLang.CanDiverge {P : PureExpr} {EventT : Type} (EL : EventLang P EventT)
    (cfg : EL.CfgT) : Prop :=
  ∃ f : EL.Transitions, f 0 = cfg ∧ EL.Diverges f

/-- Every configuration reachable from `cfg` can take a step: no execution from
    `cfg` finishes or gets stuck. -/
@[expose] def EventLang.MustDiverge {P : PureExpr} {EventT : Type} (EL : EventLang P EventT)
    (cfg : EL.CfgT) : Prop :=
  ∀ n trace cfg', EL.ReachesWithin n cfg trace cfg' → ∃ emitted cfg'', EL.step cfg' emitted cfg''

/-- The sequence built by choosing, from each configuration satisfying `Q`, a
    successor that also satisfies `Q`. -/
@[expose] noncomputable def EventLang.chooseSeq {P : PureExpr} {EventT : Type} {EL : EventLang P EventT}
    (Q : EL.CfgT → Prop) (next : ∀ c, Q c → ∃ c' emitted, EL.step c emitted c' ∧ Q c')
    (c₀ : {c // Q c}) : Nat → {c // Q c}
  | 0 => c₀
  | i + 1 =>
    let c := EventLang.chooseSeq Q next c₀ i
    ⟨Classical.choose (next c.1 c.2),
      (Classical.choose_spec (Classical.choose_spec (next c.1 c.2))).2⟩

end Strata.Logic

end -- public section
