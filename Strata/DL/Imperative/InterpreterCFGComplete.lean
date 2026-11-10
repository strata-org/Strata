/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCFG
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.InterpreterSemanticsSpec
import Strata.DL.Imperative.CFGSemanticsProps
import Strata.DL.Imperative.InterpreterCompleteGeneric
import Strata.DL.Imperative.InterpreterConfigProps
import Strata.DL.Imperative.InterpreterSemanticsSpecProps
import all Strata.DL.Imperative.InterpreterCFG

/-! # Completeness of the monadic CFG interpreter against `StepCFGEngE`

The dual of `InterpreterCFGSound.lean`: every engine-realizable event-trace relational derivation
`StepCFGEngStarE` to a terminal config, from the configuration a runtime configuration denotes
(`ICFGConfig.Denoting`, `ICFGConfig.abs`), is *reproduced* by an executable `runInterpCFG` run
from that runtime configuration at some (every sufficiently large) fuel, reaching a configuration
denoting the derivation's final one and emitting runtime events whose images (`REvent.abs`) are
exactly the derivation's event list (`InterpObs.TraceExt`).

`StepCFGEngE` is the reference relation `StepCFGE` whose guard rules also carry the engine's
evaluation of the guard (`EngEval`: some fuel reaches the guard's value, and every runtime value
the engine can commit is read as `true`, resp. `false`, by `InterpLang.boolLit?`).
`StepCFGStarE.toStepCFGEngStarE` makes a reference derivation engine-realizable under the global
`BoundedEvalComplete` and `EngineGuardsAgree`.

The statement is command-generic.  It is parameterized by a completeness obligation in the
"stable at every sufficiently large fuel" shape the engine's fuel-monotone evaluator forces, and
by that fuel-monotonicity (`hMono`):

* `hCmdC` — every reference command step `EvalCmd F σ c σ' emitted` from the image of a
  denoting runtime store is reproduced by the executable store-stepper `stepCmd` at every fuel
  `≥ f0`, reaching a denoting runtime store whose image is `σ'` and emitting runtime events
  whose images are `emitted`.

At instantiation `EvalCmd` is the engine-realizable command relation (the one
whose nondeterministic choices are recorded), so `hCmdC` is dischargeable.
Relating a plain call-aware `StepCFGExtStarE` derivation to an engine-realizable
one is a separate realizability argument that this module does not make.

Key definitions: `StepCFGEngE`, `StepCFGEngStarE`.  Key theorems: `runInterpCFG_completeE`
(whole-run completeness) and `runInterpCFG_follows_fam` (whole-run completeness along an oracle,
for a family of command steppers); `StepCFGEngStarE.toStepCFGStarE`,
`StepCFGStarE.toStepCFGEngStarE` (the bridges to the reference relation). -/

namespace Imperative

public section

/-! ## The engine-realizable CFG step relation -/

/-- The **engine-realizable** CFG step relation: the rules of `StepCFGE`, with the two guard rules
    additionally carrying the engine's evaluation of the guard: the bounded evaluator reaches the
    guard's reference value at some fuel, and every runtime value it can commit is read as `true`
    (for `goto_true`), respectively `false` (for `goto_false`), by `InterpLang.boolLit?`, which is
    how `stepInterpCFG` reads guard values (`EngEval`). -/
inductive StepCFGEngE
    {l CmdT : Type} {EventT : Type _} [BEq l] (P : PureExpr)
    (EvalCmd : EvalCmdParamE P CmdT EventT) [HasBool P] [InterpLang P] :
    CFGConfig l CmdT P → List EventT → CFGConfig l CmdT P → Prop where
  /-- Fetch: turn `.atBlock t` into `.inBlock t b.cmds b.transfer`. -/
  | fetch :
      List.lookup t cfg.blocks = .some b →
      StepCFGEngE P EvalCmd
        (.atBlock cfg t ρ) []
        (.inBlock cfg t b.cmds b.transfer ρ)
  /-- Run one command from the residual list. -/
  | step_cmd :
      EvalCmd ρ.factory ρ.store c σ' emitted →
      StepCFGEngE P EvalCmd
        (.inBlock cfg t (c :: cs) tr ρ) emitted
        (.inBlock cfg t cs tr { ρ with store := σ' })
  /-- Empty residual + true branch, evaluated by the engine to a value read as `true`: jump to
      the true label. -/
  | goto_true :
      P.eval ρ.factory ρ.store c = .some (HasBool.ttVal ρ.factory) →
      EngEval P ρ.factory ρ.store c (fun _ r => InterpLang.boolLit? r = some true) →
      StepCFGEngE P EvalCmd
        (.inBlock cfg t [] (.condGoto c tlbl elbl md) ρ) []
        (.atBlock cfg tlbl ρ)
  /-- Empty residual + false branch, evaluated by the engine to a value read as `false`: jump to
      the false label. -/
  | goto_false :
      P.eval ρ.factory ρ.store c = .some (HasBool.ffVal ρ.factory) →
      EngEval P ρ.factory ρ.store c (fun _ r => InterpLang.boolLit? r = some false) →
      StepCFGEngE P EvalCmd
        (.inBlock cfg t [] (.condGoto c tlbl elbl md) ρ) []
        (.atBlock cfg elbl ρ)
  /-- Empty residual + `finish`: halt at `.terminal`. -/
  | finish :
      StepCFGEngE P EvalCmd
        (.inBlock cfg t [] (.finish md) ρ) []
        (.terminal ρ)

/-- Reflexive-transitive event-trace execution of `StepCFGEngE`. -/
abbrev StepCFGEngStarE
    {l CmdT : Type} {EventT : Type _} [BEq l]
    (P : PureExpr) (EvalCmd : EvalCmdParamE P CmdT EventT) [HasBool P] [InterpLang P] :
    CFGConfig l CmdT P → List EventT → CFGConfig l CmdT P → Prop :=
  ReflTransTrace (StepCFGEngE P EvalCmd)

section EngBridge

variable {P : PureExpr} {l CmdT : Type} {EventT : Type _} [BEq l]
  [HasBool P] [HasBoolOps P] [HasFvars P] [InterpLang P] {EvalCmd : EvalCmdParamE P CmdT EventT}

/-- An engine-realizable CFG step is a reference `StepCFGE` step with the same events and
    successor. -/
private theorem StepCFGEngE.toStepCFGE {c c' : CFGConfig l CmdT P} {evs : List EventT}
    (h : StepCFGEngE P EvalCmd c evs c') : StepCFGE P EvalCmd c evs c' := by
  cases h <;> constructor <;> assumption

omit [HasBoolOps P] [HasFvars P] in
/-- The engine-realizable CFG step relation is monotone in its command relation. -/
theorem StepCFGEngE.imp {EvalCmd' : EvalCmdParamE P CmdT EventT}
    (h_imp : ∀ fac σ c σ' emitted, EvalCmd fac σ c σ' emitted → EvalCmd' fac σ c σ' emitted)
    {c c' : CFGConfig l CmdT P} {evs : List EventT}
    (h : StepCFGEngE P EvalCmd c evs c') : StepCFGEngE P EvalCmd' c evs c' := by
  cases h with
  | step_cmd h => exact .step_cmd (h_imp _ _ _ _ _ h)
  | _ => constructor <;> assumption

/-- An engine-realizable CFG run is a reference `StepCFGStarE` run with the same events and final
    configuration. -/
theorem StepCFGEngStarE.toStepCFGStarE {c c' : CFGConfig l CmdT P} {evs : List EventT}
    (h : StepCFGEngStarE P EvalCmd c evs c') : StepCFGStarE P EvalCmd c evs c' :=
  h.imp fun _ _ _ => StepCFGEngE.toStepCFGE

/-- A reference CFG step is engine-realizable when the bounded evaluator reaches every reference
    value (`BoundedEvalComplete`) and runtime guard values agree with the reference ones
    (`EngineGuardsAgree`). -/
private theorem StepCFGE.toStepCFGEngE (hEvalComplete : BoundedEvalComplete P)
    (hGuards : EngineGuardsAgree P) {c c' : CFGConfig l CmdT P} {evs : List EventT}
    (h : StepCFGE P EvalCmd c evs c') : StepCFGEngE P EvalCmd c evs c' := by
  cases h with
  | goto_true he => exact .goto_true he ⟨hEvalComplete.reach, (hGuards _ _ _).1 he⟩
  | goto_false he => exact .goto_false he ⟨hEvalComplete.reach, (hGuards _ _ _).2 he⟩
  | _ => constructor <;> assumption

/-- A reference CFG run is engine-realizable when the bounded evaluator reaches every reference
    value (`BoundedEvalComplete`) and runtime guard values agree with the reference ones
    (`EngineGuardsAgree`). -/
theorem StepCFGStarE.toStepCFGEngStarE (hEvalComplete : BoundedEvalComplete P)
    (hGuards : EngineGuardsAgree P) {c c' : CFGConfig l CmdT P} {evs : List EventT}
    (h : StepCFGStarE P EvalCmd c evs c') : StepCFGEngStarE P EvalCmd c evs c' :=
  ReflTransTrace.imp (fun _ _ _ => StepCFGE.toStepCFGEngE hEvalComplete hGuards) h

omit [HasBoolOps P] [HasFvars P] [BEq l] in
/-- An engine evaluation of a guard `c` whose committed runtime values are all read as the
    Boolean `b` (`InterpLang.boolLit?`), on a store whose reference value of `c` exists, yields,
    on every runtime store denoting the store, one runtime value read as `b` at every large enough
    fuel, when the bounded evaluator is fuel-monotone. -/
private theorem EngEval.guard (hMono : BoundedEvalMono P) {F : P.Factory} {σr : RStore P}
    {σ : SemanticStore P} {c : P.Expr} {b : Bool} {v : P.Val} (hσ : StoreDenotes F σr σ)
    (h : EngEval P F σ c (fun _ r => InterpLang.boolLit? r = some b))
    (he : P.eval F σ c = some v) :
    ∃ f0 r, InterpLang.boolLit? r = some b ∧ ∀ fuel, f0 ≤ fuel →
      InterpLang.boundedEval (P := P) fuel (InterpLang.rfactory F) σr c = some r := by
  obtain ⟨n, r, hb, -⟩ := h.1 σr v hσ he
  exact ⟨n, r, h.2 σr n r hσ hb, fun k hk => hMono n k _ _ _ _ hk hb⟩

end EngBridge

variable {P : PureExpr} {l CmdT : Type} [BEq l]
variable [HasBool P] [HasBoolOps P] [HasFvars P]
    [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
variable {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- A CFG configuration at which `runInterpCFG` halts and returns the config. -/
@[expose] def CFGConfig.Done {l CmdT : Type} {P : PureExpr} :
    CFGConfig l CmdT P → Prop
  | .terminal _ => True
  | _ => False

/-- A CFG interpreter configuration at which `runInterpCFG` halts and returns the config. -/
@[expose] def ICFGConfig.Done {l CmdT : Type} {P : PureExpr} [InterpLang P] :
    ICFGConfig l CmdT P → Prop
  | .terminal _ => True
  | _ => False

omit [HasBoolOps P] [HasFvars P] in
/-- `runInterpCFG` on a `Done` config returns it unchanged, at any fuel. -/
private theorem runInterpCFG_done (obs : InterpObs P m)
    (stepCmd : StepCmdStoreM P CmdT m) (fuel : Nat) {c : ICFGConfig l CmdT P} (hc : c.Done)
    (cfgr : obs.Cfg) (st : obs.St) :
    obs.run (runInterpCFG stepCmd fuel c) cfgr st = (.ok c, st) := by
  cases c <;> simp_all! [obs.run_pure, runInterpCFG]

omit [BEq l] [HasBool P] [HasBoolOps P] [HasFvars P] [DecidableEq P.Expr] in
/-- A CFG interpreter configuration halts exactly when the `CFGConfig` it stands for halts. -/
private theorem ICFGConfig.abs_done_iff {F : P.Factory} {c : ICFGConfig l CmdT P} :
    (c.abs F).Done ↔ c.Done := by
  cases c <;> exact Iff.rfl

omit [HasBoolOps P] [HasFvars P] [DecidableEq P.Expr] in
/-- On a configuration that does not halt, `runInterpCFG` at fuel `k + 1` runs one
    `stepInterpCFG` step at fuel `k + 1` and continues at fuel `k`. -/
private theorem runInterpCFG_succ_of_not_done (stepCmd : StepCmdStoreM P CmdT m) (k : Nat)
    {c : ICFGConfig l CmdT P} (hc : ¬ c.Done) :
    runInterpCFG stepCmd (k + 1) c =
      stepInterpCFG stepCmd (k + 1) c >>= runInterpCFG stepCmd k := by
  cases c <;> first | rfl | exact absurd trivial hc

omit [HasBoolOps P] [HasFvars P] in
/-- **Per-step completeness of `stepInterpCFG`.**  Each transition of the engine-realizable
    event-trace CFG relation `StepCFGEngE` out of the `CFGConfig` a denoting configuration `start`
    stands for is reproduced by one executable `stepInterpCFG` step from `start` at every
    sufficiently large fuel, reaching a configuration denoting the transition's target and emitting
    runtime events whose images are exactly the transition's events.  It assumes that the command
    stepper reproduces every reference command step at every sufficiently large fuel and that the
    bounded evaluator is fuel-monotone. -/
private theorem stepInterpCFG_completeE
    (obs : InterpObs P m)
    (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (stepCmd : StepCmdStoreM P CmdT m)
    (F : P.Factory)
    (hCmdC : ∀ (σ : IStore P) c σ' emitted cfgr st, RStore.Denoting F σ.get →
        EvalCmd F (InterpLang.absStore F σ.get) c σ' emitted →
        ∃ f0 st', ∃ σi : IStore P, InterpLang.absStore F σi.get = σ' ∧ RStore.Denoting F σi.get ∧
          (∀ fuel, f0 ≤ fuel →
            obs.run (stepCmd fuel (InterpLang.rfactory F) σ c) cfgr st = (.ok σi, st'))
          ∧ obs.TraceExt F st st' emitted)
    (hMono : BoundedEvalMono P)
    {start : ICFGConfig l CmdT P} {emitted : List (Event P)} {next : CFGConfig l CmdT P}
    (hden : start.Denoting F) (h : StepCFGEngE P EvalCmd (start.abs F) emitted next)
    (cfgr : obs.Cfg) (st : obs.St) :
    ∃ f0 st', ∃ next' : ICFGConfig l CmdT P, next'.Denotes F next ∧ (∀ fuel, f0 ≤ fuel →
        obs.run (stepInterpCFG stepCmd fuel start) cfgr st = (.ok next', st'))
      ∧ obs.TraceExt F st st' emitted := by
  generalize hs : start.abs F = s at h
  cases h <;> cases start <;> simp only [ICFGConfig.abs] at hs <;> cases hs <;>
    obtain ⟨hdS, hdF⟩ := hden <;> simp only [ICFGConfig.env] at hdS hdF
  case fetch =>
    exact ⟨0, st, .inBlock _ _ _ _ _, ⟨⟨hdS, hdF⟩, rfl⟩,
      fun _ _ => by simp [stepInterpCFG, *, obs.run_pure], [], rfl, rfl⟩
  case step_cmd hc =>
    obtain ⟨f0, st', σi, rfl, hdi, hr, ht⟩ := hCmdC _ _ _ _ cfgr st hdS hc
    exact ⟨f0, st', .inBlock _ _ _ _ ⟨σi, InterpLang.rfactory F⟩, ⟨⟨hdi, rfl⟩, rfl⟩,
      fun fuel h => by simp [stepInterpCFG, obs.run_bind, hdF, hr fuel h, obs.run_pure], ht⟩
  case goto_true hc hok =>
    obtain ⟨f0, r, hr, hf⟩ := EngEval.guard hMono (storeDenotes_absStore hdS) hok hc
    exact ⟨f0, st, .atBlock _ _ _, ⟨⟨hdS, hdF⟩, rfl⟩, fun fuel h => by
      simp [stepInterpCFG, hdF, hf fuel h, hr, obs.run_pure], [], rfl, rfl⟩
  case goto_false hc hok =>
    obtain ⟨f0, r, hr, hf⟩ := EngEval.guard hMono (storeDenotes_absStore hdS) hok hc
    exact ⟨f0, st, .atBlock _ _ _, ⟨⟨hdS, hdF⟩, rfl⟩, fun fuel h => by
      simp [stepInterpCFG, hdF, hf fuel h, hr, obs.run_pure], [], rfl, rfl⟩
  case finish =>
    exact ⟨0, st, .terminal _, ⟨⟨hdS, hdF⟩, rfl⟩, fun _ _ => by
      simp [stepInterpCFG, obs.run_pure], [], rfl, rfl⟩

omit [HasBoolOps P] [HasFvars P] in
/-- **Completeness of the monadic CFG interpreter against `StepCFGEngE`.**  Every derivation
    from the `CFGConfig` of `start` (`ICFGConfig.abs`) to `final` of `StepCFGEngStarE`, the
    multi-step engine-realizable event-trace CFG semantics, that ends in a terminal config is
    reproduced by a `runInterpCFG` run from the denoting configuration `start` at every sufficiently
    large fuel, reaching a configuration denoting `final` and emitting runtime events whose images
    are exactly the derivation's events.  It assumes that the command stepper reproduces every
    reference command step at every sufficiently large fuel and that the bounded evaluator is
    fuel-monotone. -/
theorem runInterpCFG_completeE
    (obs : InterpObs P m)
    (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (stepCmd : StepCmdStoreM P CmdT m)
    (F : P.Factory)
    (hCmdC : ∀ (σ : IStore P) c σ' emitted cfgr st, RStore.Denoting F σ.get →
        EvalCmd F (InterpLang.absStore F σ.get) c σ' emitted →
        ∃ f0 st', ∃ σi : IStore P, InterpLang.absStore F σi.get = σ' ∧ RStore.Denoting F σi.get ∧
          (∀ fuel, f0 ≤ fuel →
            obs.run (stepCmd fuel (InterpLang.rfactory F) σ c) cfgr st = (.ok σi, st'))
          ∧ obs.TraceExt F st st' emitted)
    (hMono : BoundedEvalMono P)
    {start : ICFGConfig l CmdT P} {final : CFGConfig l CmdT P} {evs : List (Event P)}
    (hden : start.Denoting F) (hstar : StepCFGEngStarE P EvalCmd (start.abs F) evs final)
    (hdone : final.Done) (cfgr : obs.Cfg) (st : obs.St) :
    ∃ f0 st', ∃ final' : ICFGConfig l CmdT P, final'.Denotes F final ∧ (∀ fuel, f0 ≤ fuel →
        obs.run (runInterpCFG stepCmd fuel start) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  generalize hs : start.abs F = s at hstar
  induction hstar generalizing start st with
  | refl => exact ⟨0, st, start, ⟨hden, hs⟩, fun _ _ =>
      runInterpCFG_done obs _ _ (ICFGConfig.abs_done_iff.1 (hs ▸ hdone)) _ _, [], rfl, rfl⟩
  | step x e y rest z hstep _ ih =>
    obtain ⟨f1, s1, y1, ⟨hd1, hy⟩, h1, t1⟩ :=
      stepInterpCFG_completeE obs EvalCmd stepCmd F hCmdC hMono hden (hs ▸ hstep) cfgr st
    obtain ⟨f2, s2, z1, hz, h2, t2⟩ := ih hd1 hdone s1 hy
    refine ⟨f1 + f2 + 1, s2, z1, hz, fun fuel hf => ?_, t1.append t2⟩
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hnd : ¬ x.Done := by cases hstep <;> exact id
    subst hs
    simp only [runInterpCFG_succ_of_not_done _ _ (mt ICFGConfig.abs_done_iff.2 hnd),
      obs.run_bind, h1 (k + 1) (by omega), h2 k (by omega)]

/-! ## Completeness along an oracle, for a family of command steppers

The command stepper of a CFG run may come from a family `S i j`, indexed by two stepper indices
that stay fixed along the run (a callee body baked at the call's call-depth budget and fuel), and
a command may read nondeterministic choices off an oracle and leave a pending-choice predicate
`Pending` on the observation state.  `runInterpCFG_follows_fam` reproduces such a run at every
large enough stepper indices and fuel. -/

/-- One step of a CFG run whose commands read their choices off an oracle, on a CFG
    configuration paired with an oracle: a command step runs the command through `E`, which turns
    the oracle `o` into `o'`; a command-free control-flow step leaves the oracle alone. -/
inductive OracleCFGStepE (E : P.Factory → SemanticStore P → CmdT → SemanticStore P →
      List (Event P) → List P.Val → List P.Val → Prop) :
    CFGConfig l CmdT P × List P.Val → List (Event P) → CFGConfig l CmdT P × List P.Val →
      Prop where
  /-- Run one command from the residual list of the current block, at the factory and store of
      the configuration's environment. -/
  | step_cmd {g : CFG l (DetBlock l CmdT P)} {t : l} {c : CmdT} {cs : List CmdT}
      {tr : DetTransferCmd l P} {ρ : Env P} {σ' : SemanticStore P} {evs : List (Event P)}
      {o o' : List P.Val} :
      E ρ.factory ρ.store c σ' evs o o' →
      OracleCFGStepE E (.inBlock g t (c :: cs) tr ρ, o) evs
        (.inBlock g t cs tr { ρ with store := σ' }, o')
  /-- Take one command-free control-flow step (a `StepCFGEngE` step under the command relation
      that holds of nothing); it emits no events. -/
  | step_admin {c c' : CFGConfig l CmdT P} {o : List P.Val} :
      StepCFGEngE P (fun _ _ _ _ (_ : List (Event P)) => False) c [] c' →
      OracleCFGStepE E (c, o) [] (c', o)

omit [HasBoolOps P] [HasFvars P] in
/-- **Per-step completeness of `stepInterpCFG` along an oracle, for a family of command
    steppers.**  Each step of an oracle-reading CFG run whose events satisfy `Q` is reproduced,
    from every state `st` with `Pending st` of its oracle, by one `stepInterpCFG (S i j)` step at
    every large enough stepper indices `i`, `j` and fuel from the denoting configuration `x1`,
    reaching a configuration denoting the step's target, emitting runtime events whose images
    are exactly the step's events and leaving `Pending` of the step's remaining oracle.  It
    assumes that every command step of `E` whose events satisfy `Q` is reproduced that way by
    `S i j` (`hcmd`) and that the bounded evaluator is fuel-monotone (`hMono`). -/
private theorem stepInterpCFG_follows_fam (obs : InterpObs P m) (cfgr : obs.Cfg) (F : P.Factory)
    (Pending : obs.St → List P.Val → Prop) {Q : Event P → Prop}
    {E : P.Factory → SemanticStore P → CmdT → SemanticStore P → List (Event P) →
      List P.Val → List P.Val → Prop}
    (S : Nat → Nat → StepCmdStoreM P CmdT m)
    (hcmd : ∀ (σ : IStore P) c σ' evs o o', RStore.Denoting F σ.get →
      E F (InterpLang.absStore F σ.get) c σ' evs o o' →
      (∀ ev ∈ evs, Q ev) → ∀ st, Pending st o → ∃ f0 st', ∃ σi : IStore P,
        InterpLang.absStore F σi.get = σ' ∧ RStore.Denoting F σi.get ∧
        (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
          obs.run (S i j fuel (InterpLang.rfactory F) σ c) cfgr st = (.ok σi, st'))
        ∧ Pending st' o' ∧ obs.TraceExt F st st' evs)
    (hMono : BoundedEvalMono P)
    {x1 : ICFGConfig l CmdT P} {o : List P.Val} {y : CFGConfig l CmdT P × List P.Val}
    {evs : List (Event P)}
    (hden : x1.Denoting F) (h : OracleCFGStepE E ((x1.abs F), o) evs y) (hq : ∀ ev ∈ evs, Q ev)
        (st : obs.St)
    (hst : Pending st o) :
    ∃ f0 st', ∃ y1 : ICFGConfig l CmdT P, y1.Denotes F y.1 ∧
      (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
        obs.run (stepInterpCFG (S i j) fuel x1) cfgr st = (.ok y1, st'))
      ∧ Pending st' y.2 ∧ obs.TraceExt F st st' evs := by
  generalize hx : ((x1.abs F), o) = x at h
  cases h with
  | step_cmd he =>
    cases x1 <;> simp only [ICFGConfig.abs] at hx <;> cases hx
    obtain ⟨hdS, hdF⟩ := hden
    simp only [ICFGConfig.env] at hdS hdF
    obtain ⟨f0, s, σi, rfl, hdi, hr, hp, ht⟩ := hcmd _ _ _ _ _ _ hdS he hq st hst
    exact ⟨f0, s, .inBlock _ _ _ _ ⟨σi, InterpLang.rfactory F⟩, ⟨⟨hdi, rfl⟩, rfl⟩,
      fun i j fuel hi hj hf => by
        simp [stepInterpCFG, obs.run_bind, hdF, hr i j fuel hi hj hf, obs.run_pure], hp, ht⟩
  | step_admin hs =>
    cases hs
    case step_cmd h => exact h.elim
    all_goals cases x1 <;> simp only [ICFGConfig.abs] at hx <;> cases hx <;>
      obtain ⟨hdS, hdF⟩ := hden <;> simp only [ICFGConfig.env] at hdS hdF
    case step_admin.fetch =>
      exact ⟨0, st, .inBlock _ _ _ _ _, ⟨⟨hdS, hdF⟩, rfl⟩, fun _ _ _ _ _ _ => by
        simp [stepInterpCFG, *, obs.run_pure], hst, [], rfl, rfl⟩
    case step_admin.goto_true hc hok =>
      obtain ⟨f0, r, hr, hf⟩ := EngEval.guard hMono (storeDenotes_absStore hdS) hok hc
      exact ⟨f0, st, .atBlock _ _ _, ⟨⟨hdS, hdF⟩, rfl⟩, fun _ _ fuel _ _ h => by
        simp [stepInterpCFG, hdF, hf fuel h, hr, obs.run_pure], hst, [], rfl, rfl⟩
    case step_admin.goto_false hc hok =>
      obtain ⟨f0, r, hr, hf⟩ := EngEval.guard hMono (storeDenotes_absStore hdS) hok hc
      exact ⟨f0, st, .atBlock _ _ _, ⟨⟨hdS, hdF⟩, rfl⟩, fun _ _ fuel _ _ h => by
        simp [stepInterpCFG, hdF, hf fuel h, hr, obs.run_pure], hst, [], rfl, rfl⟩
    case step_admin.finish =>
      exact ⟨0, st, .terminal _, ⟨⟨hdS, hdF⟩, rfl⟩, fun _ _ _ _ _ _ => by
        simp [stepInterpCFG, obs.run_pure], hst, [], rfl, rfl⟩

omit [HasBoolOps P] [HasFvars P] in
/-- **Completeness of the CFG driver along an oracle, for a family of command steppers.** An
    oracle-reading CFG run from the `CFGConfig` of `x1` (`ICFGConfig.abs`) with oracle `o` to a
    halted `y.1` with oracle `y.2` is reproduced, from every state `st` with `Pending st o`, by
    `runInterpCFG (S i j)` from `x1` at every large enough stepper indices `i`, `j` and fuel,
    when `x1` denotes, reaching a configuration denoting `y.1`, emitting runtime events whose
    images are exactly the run's events and leaving `Pending st' y.2`, when the run's events
    satisfy `Q`. It assumes that every command step of `E` whose events satisfy `Q` is
    reproduced that way by `S i j` (`hcmd`) and that the bounded evaluator is fuel-monotone
    (`hMono`). -/
theorem runInterpCFG_follows_fam (obs : InterpObs P m) (cfgr : obs.Cfg) (F : P.Factory)
    (Pending : obs.St → List P.Val → Prop) {Q : Event P → Prop}
    {E : P.Factory → SemanticStore P → CmdT → SemanticStore P → List (Event P) →
      List P.Val → List P.Val → Prop}
    (S : Nat → Nat → StepCmdStoreM P CmdT m)
    (hcmd : ∀ (σ : IStore P) c σ' evs o o', RStore.Denoting F σ.get →
      E F (InterpLang.absStore F σ.get) c σ' evs o o' →
      (∀ ev ∈ evs, Q ev) → ∀ st, Pending st o → ∃ f0 st', ∃ σi : IStore P,
        InterpLang.absStore F σi.get = σ' ∧ RStore.Denoting F σi.get ∧
        (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
          obs.run (S i j fuel (InterpLang.rfactory F) σ c) cfgr st = (.ok σi, st'))
        ∧ Pending st' o' ∧ obs.TraceExt F st st' evs)
    (hMono : BoundedEvalMono P)
    {x1 : ICFGConfig l CmdT P} {o : List P.Val} {y : CFGConfig l CmdT P × List P.Val}
    {evs : List (Event P)}
    (hden : x1.Denoting F) (h : ReflTransTrace (OracleCFGStepE E) ((x1.abs F), o) evs y)
        (hdone : y.1.Done)
    (hq : ∀ ev ∈ evs, Q ev) :
    ∀ st, Pending st o → ∃ f0 st', ∃ y1 : ICFGConfig l CmdT P, y1.Denotes F y.1 ∧
      (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
        obs.run (runInterpCFG (S i j) fuel x1) cfgr st = (.ok y1, st'))
      ∧ Pending st' y.2 ∧ obs.TraceExt F st st' evs := by
  generalize hx : ((x1.abs F), o) = x at h
  induction h generalizing x1 o with
  | refl =>
    subst hx
    exact fun st hst => ⟨0, st, x1, ⟨hden, rfl⟩, fun _ _ _ _ _ _ => runInterpCFG_done obs _ _
      (ICFGConfig.abs_done_iff.1 hdone) _ _, hst, [], rfl, rfl⟩
  | step x e y rest z hs _ ih =>
    intro st hst
    simp only [List.forall_mem_append] at hq
    obtain ⟨f1, s1, y1, ⟨hd1, hy⟩, h1, p1, t1⟩ :=
      stepInterpCFG_follows_fam obs cfgr F Pending S hcmd hMono hden (hx ▸ hs) hq.1 st hst
    obtain ⟨f2, s2, z1, hz, h2, p2, t2⟩ := ih hd1 hdone hq.2 (Prod.ext hy rfl) s1 p1
    refine ⟨f1 + f2 + 1, s2, z1, hz, fun i j fuel hi hj hf => ?_, p2, t1.append t2⟩
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hnd : ¬ x.1.Done := by
      cases hs with
      | step_cmd => exact id
      | step_admin h => cases h <;> exact id
    subst hx
    simp only [runInterpCFG_succ_of_not_done _ _ (mt ICFGConfig.abs_done_iff.2 hnd),
      obs.run_bind, h1 i j (k + 1) (by omega) (by omega) (by omega),
      h2 i j k (by omega) (by omega) (by omega)]

end -- public section

end Imperative
