/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkSim
public import Strata.DL.Imperative.InterpreterTowerProps
public import Strata.Languages.Core.ConfigWF
public import Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterProps
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.InterpreterReplayProps
import all Strata.Languages.Core.Counterexample.BackLinkSim
import all Strata.Languages.Core.ConfigWF
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.Languages.Core.Counterexample.ValuationToRun
import Strata.DL.Imperative.Counterexample.Tactics
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.Languages.Core.IdentifiersProps
import Strata.Languages.Core.InterpreterDomainProps
public import Strata.Languages.Core.ReplayWF
import all Strata.DL.Imperative.CmdSemantics

/-! # Replay-vs-replay simulation over a configuration relation: definitions

Stuttering steps (`Stutters`, `StuttersRel`), the relational step simulation `RelStepSim`,
and agreement of stores, expressions and events outside a set of names (`StoreAgreeOutside`,
`ExprAvoids`, `EventArgAgree`, `EvAgree`); a command avoiding a set of names (`CmdAvoids`)
and the relational context of two runs agreeing outside it (`AgreeCtx`).  The simulation
theorems and the step lemmas are in `BackLinkRelSimProps`. -/

namespace Core

open Imperative

public section

/-! ## The whole run, from a per-step obligation -/

/-- One downstream step *stutters* against the upstream configuration `c`: from every
    state it either fails without touching the state, or succeeds without touching it,
    at a configuration still related to `c`. -/
@[expose] def Stutters (K : RelCtx)
    (R : IConfig Expression Command → IConfig Expression Command → Prop)
    (X' : ReplayM Expression (IConfig Expression Command))
    (c : IConfig Expression Command) : Prop :=
  ∀ s', (∃ c'1, rrun X' K.cfgD s' = (.ok c'1, s') ∧ R c'1 c) ∨
    (∃ e, rrun X' K.cfgD s' = (.error e, s'))

/-- One downstream step *stutters relationally* against the upstream configuration `c`
    (whose state does not move): from related states, a success keeps the states related
    and the next downstream configuration related to `c`; a failure whose state has fired
    downstream means the upstream state has fired. -/
@[expose] def StuttersRel (K : RelCtx)
    (R : IConfig Expression Command → IConfig Expression Command → Prop)
    (X' : ReplayM Expression (IConfig Expression Command))
    (c : IConfig Expression Command) : Prop :=
  ∀ s' s, StRel K s' s →
    (∀ c'1 s'1, rrun X' K.cfgD s' = (.ok c'1, s'1) → StRel K s'1 s ∧ R c'1 c) ∧
    (∀ e s'1, rrun X' K.cfgD s' = (.error e, s'1) → FiredD K s'1 → FiredU K s)

/-- **The per-step obligation of a relational simulation.**  From interpreter
    configurations related by `R` whose downstream abstraction (`IConfig.abs`) the monadic
    interpreter does not stop at, a downstream step at fuel `k ≥ 1` either stutters or is matched,
    in lockstep, by one upstream step at any fuel `m ≥ k` from a configuration whose abstraction
    the monadic interpreter does not stop at. -/
@[expose] def RelStepSim (K : RelCtx) (sc' sc : StepCmdM Expression Command (ReplayM Expression))
    (R : IConfig Expression Command → IConfig Expression Command → Prop) : Prop :=
  ∀ c' c, R c' c → ¬ IConfig.Done c' → ∀ k m, 1 ≤ k → k ≤ m →
    StuttersRel K R (stepInterp sc' k c') c ∨
      (¬ IConfig.Done c ∧ RelDom K (stepInterp sc' k c') (stepInterp sc m c) R)

/-! ## Evaluation agreement outside a set of names

The event relation of phases whose two runs differ only on the values of names the
source never mentions: the stores agree outside those names, and a condition mentioning
none of them evaluates alike. -/

/-- Two stores agree outside the names `fresh`. -/
@[expose] def StoreAgreeOutside (fresh : Expression.Ident → Prop)
    (σ' σ : RStore Expression) : Prop :=
  ∀ x, ¬ fresh x → σ' x = σ x

/-- An expression mentions no name of `fresh`. -/
@[expose] def ExprAvoids (fresh : Expression.Ident → Prop) (e : Expression.Expr) : Prop :=
  ∀ x ∈ Lambda.LExpr.LExpr.getVars e, ¬ fresh x

/-- Agreement of two event arguments up to the names `fresh` (upstream-side
    well-formedness included). -/
@[expose] def EventArgAgree (fresh : Expression.Ident → Prop)
    (a' a : REventArg Expression (InterpLang.RFactory Expression)) : Prop :=
  a'.factory = a.factory ∧ a'.label = a.label ∧ a'.expr = a.expr ∧ a'.metadata = a.metadata ∧
    StoreAgreeOutside fresh a'.store a.store ∧ ExprAvoids fresh a.expr ∧
    FactoryOK a.factory ∧ StoreClosed a.store

/-- Agreement of two events up to the names `fresh`: the same kind, and agreeing
    arguments. -/
@[expose] def EvAgree (fresh : Expression.Ident → Prop) :
    IEvent Expression → IEvent Expression → Prop
  | .assert a', .assert a => EventArgAgree fresh a' a
  | .assume a', .assume a => EventArgAgree fresh a' a
  | .cover a', .cover a => EventArgAgree fresh a' a
  | _, _ => False

/-! ## The equality instance -/

/-! ## Runs agreeing outside a set of names -/

/-- A base command mentions no name of `fresh` (in the names it writes or the
    expressions it reads). -/
@[expose] def CmdAvoids (fresh : Expression.Ident → Prop) : Cmd Expression → Prop
  | .init x _ (.det e) _ => ¬ fresh x ∧ ExprAvoids fresh e
  | .init x _ .nondet _ => ¬ fresh x
  | .set x (.det e) _ => ¬ fresh x ∧ ExprAvoids fresh e
  | .set x .nondet _ => ¬ fresh x
  | .assert _ e _ => ExprAvoids fresh e
  | .assume _ e _ => ExprAvoids fresh e
  | .cover _ e _ => ExprAvoids fresh e

/-- A relational context whose event relation is agreement up to `fresh`. -/
@[expose] def AgreeCtx (K : RelCtx) (fresh : Expression.Ident → Prop) : Prop :=
  ∀ ev' ev, EvAgree fresh ev' ev → K.ER ev' ev

end -- public section

end Core
