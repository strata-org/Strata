/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterKleene
public import Strata.DL.Imperative.InterpreterKleeneSound
public import Strata.DL.Imperative.KleeneStmtSemantics
public import Strata.DL.Imperative.KleeneSemanticsProps
public import Strata.DL.Imperative.InterpreterCompleteObs
public import Strata.DL.Imperative.InterpreterCallComplete
import all Strata.DL.Imperative.InterpreterKleene
import all Strata.DL.Imperative.InterpreterKleeneCall
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.InterpreterCallComplete
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterSemanticsSpec

/-! # Completeness of the monadic Kleene interpreter against `StepKleeneE`

For the **base** command language (`CmdT = Cmd P`, no `.call`), every
engine-realizable reference derivation `StepKleeneStarE (EvalCmdEngE R)` ending at
a terminal configuration is **reproduced** by a `ReplayM` run of the Kleene driver
`runInterpKleene stepBaseCmdStore` at some fuel, from every tracked interpreter configuration
denoting the derivation's start configuration (`IKleeneConfig.Denoting`, `IKleeneConfig.abs`),
whose oracle is the derivation's own choice sequence, emitting runtime events whose images
(`REvent.abs`) are exactly the derivation's events and reaching a configuration denoting the
same terminal configuration.  Since every such derivation is a reference
`StepKleeneStarE EvalCmdE` derivation (`StepKleeneE.imp` + `EvalCmdEngE.toEvalCmdE`),
this is completeness of the monadic interpreter against the base-command event semantics.

The per-step and whole-run lemmas start from any tracked interpreter configuration
(`IKleeneConfig.Tracked`) whose abstraction (`IKleeneConfig.abs`) the derivation starts from;
keeping every scope frame exact needs every command evaluation to define only the names
`CmdDefs` lists (`CmdDefsSound`).

The nondeterminism is handled exactly as in the structured engine
(`InterpreterCompleteObs.lean`): the oracle is threaded explicitly, each `.choice`
/ `.loop` step consuming one Boolean value (`HasBool.tt` to take the left arm / one
more iteration, `HasBool.ff` to take the right arm / stop), so no unsatisfiable
`ChooseResolves` obligation is incurred.

This explicit-oracle result covers base commands only.  Commands with `.call` are
covered by the second part of the module, which states completeness against the
engine-realizable closure, with the call-nesting-height-indexed command relation
`EvalCommandEngAtE π R n` reproducing each callee body run.

A third part states completeness along an oracle for a family of command steppers, monad-generic
and for every command type: the oracle-reading Kleene relation `OracleKleeneStepE` pops the
Boolean of each `.choice` / `.loop` off the oracle, and the observation only has to follow the
pending choices (`ChooseFollows`), so a `.choice` or `.loop` may be resolved differently each time
it is reached, from the same store or not.

Key definitions: `StepKleeneEngE` / `StepKleeneEngStarE`, the engine-realizable
Kleene step relation (`StepKleeneE` with the `.choice` / `.loop` nondeterminism
resolved by a value recorded in the choice record `R`); `OracleKleeneStepE`, the oracle-reading
Kleene step relation.  Key theorems:
`runInterpKleene_completeE` (base commands, over the explicit oracle),
`runInterpKleene_engCompleteE` (monad-generic, engine-realizable),
`runInterpKleene_callCompleteE` (call-aware), and `runInterpKleene_follows_fam` (monad-generic,
along an oracle). -/

namespace Imperative

public section

variable {P : PureExpr} [HasBoolOps P] [HasFvar P]
    [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]

/-! ## Unfolding the monadic Kleene interpreter on non-terminal configurations -/

section Unfold

variable {CmdT : Type} [CmdDefs P CmdT] {m : Type → Type} [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m]
    (stepCmd : StepCmdStoreM P CmdT m) (fuel : Nat)

omit [HasFvar P] [DecidableEq P.Expr] in
/-- On a non-terminal inner configuration, a Kleene step of a sequence context steps the inner
    configuration and keeps the right statement. -/
private theorem stepInterpKleene_seq_step {inner : IKleeneConfig P CmdT}
    (s2 : KleeneStmt P CmdT) (h : ∀ ρ, inner ≠ .terminal ρ) :
    stepInterpKleene stepCmd fuel (.seq inner s2)
      = stepInterpKleene stepCmd fuel inner >>= fun i => pure (.seq i s2) := by
  cases inner <;> first | rfl | exact absurd rfl (h _)

omit [HasFvar P] [DecidableEq P.Expr] in
/-- On a non-terminal inner configuration, a Kleene step of a block context steps the inner
    configuration and records the step in the block's frame. -/
private theorem stepInterpKleene_block_step {inner : IKleeneConfig P CmdT}
    (fr : ScopeFrame P) (h : ∀ ρ, inner ≠ .terminal ρ) :
    stepInterpKleene stepCmd fuel (.block fr inner)
      = stepInterpKleene stepCmd fuel inner >>= fun i =>
          pure (.block (fr.record inner.levelCmd?) i) := by
  cases inner <;> first | rfl | exact absurd rfl (h _)
omit [HasFvar P] [DecidableEq P.Expr] in
omit [HasFvar P] in
/-- On a non-terminal configuration, a Kleene run with one more fuel unit takes one step, then
    runs on. -/
private theorem runInterpKleene_succ_step {c : IKleeneConfig P CmdT}
    (h : ∀ ρ, c ≠ .terminal ρ) :
    runInterpKleene stepCmd (fuel + 1) c
      = stepInterpKleene stepCmd (fuel + 1) c >>= runInterpKleene stepCmd fuel := by
  cases c <;> first | rfl | exact absurd rfl (h _)

end Unfold

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] in
/-- The level store of a Kleene configuration whose stores denote denotes. -/
private theorem IKleeneConfig.Denoting.lvl {CmdT : Type} {F : P.Factory} {c : IKleeneConfig P CmdT}
    (h : c.Denoting F) : RStore.Denoting F c.lvl := by
  induction c with
  | seq _ _ ih => exact ih h
  | block _ _ _ => exact h.1
  | _ => exact h.1

section ReplayBase

variable (R : ChoiceRecord P) (cfg : ReplayCfg P)
    (hcfg : cfg.interruptOn = fun _ => none)
    (hMono : BoundedEvalMono P)
    (hvalid : ValidChoices (P := P) R)
    (hbool : ∀ (f : InterpLang.RFactory P),
      ((InterpLang.ops (P := P)).isValue f (HasBool.tt (P := P)) = true
        ∧ (InterpLang.ops (P := P)).hasType f (HasBool.tt (P := P))
            (HasBool.boolTy (P := P)) = true)
      ∧ ((InterpLang.ops (P := P)).isValue f (HasBool.ff (P := P)) = true
        ∧ (InterpLang.ops (P := P)).hasType f (HasBool.ff (P := P))
            (HasBool.boolTy (P := P)) = true))
    (hlit : InterpLang.boolLit? (HasBool.tt (P := P)) = some true ∧
      InterpLang.boolLit? (HasBool.ff (P := P)) = some false)

include hcfg hMono hvalid hbool hlit

omit hcfg hMono hvalid hlit [HasFvar P] [DecidableEq P.Ident] in
/-- A replayed `choose` at `boolTy` consumes a Boolean oracle head. -/
private theorem replayRun_choose_bool {f : InterpLang.RFactory P} {σ : RStore P} {v : P.Expr}
    {rest u : List P.Expr} {t : List (IEvent P)}
    (hv : v = HasBool.tt (P := P) ∨ v = HasBool.ff (P := P)) :
    replayRun (InterpEffects.choose (P := P) f σ (HasBool.boolTy (P := P))) cfg
        { remaining := v :: rest, usedRev := u, traceRev := t }
      = (.ok v, { remaining := rest, usedRev := v :: u, traceRev := t }) := by
  apply replayRun_choose_cons <;> grind [hbool f]

/-- **Per-step completeness of `stepInterpKleene` over base commands.**  One step of the
    event-trace Kleene reference relation `StepKleeneE` out of the abstraction
    (`IKleeneConfig.abs`) of a tracked (`IKleeneConfig.Tracked`) configuration `c`, whose
    commands follow the engine-realizable base-command relation (nondeterministic values read
    off the choice record `R`), is reproduced by one replayed `stepInterpKleene` step from `c`
    at every sufficiently large fuel, reaching a tracked configuration that stands for the
    step's successor, consuming an oracle segment `os`, logging it as used, and recording the
    step's events. -/
private theorem stepKleeneE_complete_replay {F : P.Factory}
    {c : IKleeneConfig P (Cmd P)} {evs : List (Event P)} {c' : KleeneConfig P (Cmd P)}
    (hd : c.Denoting F) (ht : c.Tracked) (h : StepKleeneE P (EvalCmdEngE P R) (c.abs F) evs c') :
    ∃ (f0 : Nat) (os : List P.Expr) (ci : IKleeneConfig P (Cmd P)) (revs : List (IEvent P)),
      (ci.abs F) = c' ∧ ci.Denoting F ∧ ci.Tracked ∧ revs.map (REvent.abs F) = evs ∧
      ∀ (fuel : Nat), f0 ≤ fuel →
      ∀ (rest u : List P.Expr) (t : List (IEvent P)),
        replayRun (stepInterpKleene (stepBaseCmdStore (m := ReplayM P)) fuel c) cfg
            { remaining := os ++ rest, usedRev := u, traceRev := t }
          = (.ok ci, { remaining := rest, usedRev := os.reverse ++ u,
                       traceRev := revs.reverse ++ t }) := by
  generalize hx : c.abs F = x at h
  induction h generalizing c with
  | @step_cmd _ σ' _ ρ hc =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    obtain ⟨hdS, hdF⟩ := hd
    obtain ⟨f0, os, σi, revs, rfl, hdi, hrevs, h1⟩ :=
      evalCmdEngE_complete_replay cfg hcfg hMono hvalid hdS hc
    exact ⟨f0, os, .terminal ⟨σi, InterpLang.rfactory F⟩, revs, rfl, ⟨hdi, rfl⟩, trivial, hrevs,
      fun fuel hf rest u t => by
        simp [stepInterpKleene, replayRun_bind, hdF, h1 fuel hf, replayRun_pure, -bind_pure_comp]⟩
  | @step_seq s1 s2 ρ =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, [], .seq (.stmt s1 ρ) s2, [], rfl, hd, trivial, rfl, fun _ _ _ _ _ => by
      simp [stepInterpKleene, replayRun_pure]⟩
  | @step_choice_left s1 s2 ρ =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, [HasBool.tt], .stmt s1 ρ, [], rfl, hd, trivial, rfl, fun _ _ _ _ _ => by
      simp [stepInterpKleene, resolveGuard, replayRun_bind,
        replayRun_choose_bool cfg hbool (.inl rfl), hlit.1, replayRun_pure, -bind_pure_comp]⟩
  | @step_choice_right s1 s2 ρ =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, [HasBool.ff], .stmt s2 ρ, [], rfl, hd, trivial, rfl, fun _ _ _ _ _ => by
      simp [stepInterpKleene, resolveGuard, replayRun_bind,
        replayRun_choose_bool cfg hbool (.inr rfl), hlit.2, replayRun_pure, -bind_pure_comp]⟩
  | @step_loop_zero s ρ =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, [HasBool.ff], .terminal ρ, [], rfl, hd, trivial, rfl, fun _ _ _ _ _ => by
      simp [stepInterpKleene, resolveGuard, replayRun_bind,
        replayRun_choose_bool cfg hbool (.inr rfl), hlit.2, replayRun_pure, -bind_pure_comp]⟩
  | @step_loop_step s ρ =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, [HasBool.tt], .seq (.block (.opened ρ.store) (.stmt s ρ)) (.loop s), [], rfl,
      ⟨hd.1, hd⟩, by simp [IKleeneConfig.Tracked, IKleeneConfig.lvl], rfl, fun _ _ _ _ _ => by
      simp [stepInterpKleene, resolveGuard, replayRun_bind,
        replayRun_choose_bool cfg hbool (.inl rfl), hlit.1, replayRun_pure, -bind_pure_comp]⟩
  | @step_block s ρ =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, [], .block (.opened ρ.store) (.stmt s ρ), [], rfl, ⟨hd.1, hd⟩,
      by simp [IKleeneConfig.Tracked, IKleeneConfig.lvl], rfl, fun _ _ _ _ _ => by
      simp [stepInterpKleene, replayRun_pure]⟩
  | @step_seq_inner _ _ _ s2 hs ih =>
    obtain ⟨ci, rfl, hci⟩ := (IKleeneConfig.abs_eq_seq ..).1 hx
    obtain ⟨f0, os, c1, revs, ha, hd1, ht1, hrevs, h1⟩ := ih (c := ci) hd ht hci
    have hnt : ∀ ρ, ci ≠ .terminal ρ := by rintro _ rfl; cases hci; cases hs
    exact ⟨f0, os, .seq c1 s2, revs, by simp [IKleeneConfig.abs, ha], hd1, ht1, hrevs,
      fun fuel hf _ _ _ => by
        simp [stepInterpKleene_seq_step _ _ _ hnt, replayRun_bind, h1 fuel hf, replayRun_pure,
          -bind_pure_comp]⟩
  | @step_seq_done ρ s2 =>
    obtain ⟨ci, rfl, hci⟩ := (IKleeneConfig.abs_eq_seq ..).1 hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_terminal ..).1 hci
    exact ⟨0, [], .stmt s2 ρ, [], rfl, hd, trivial, rfl, fun _ _ _ _ _ => by
      simp [stepInterpKleene, replayRun_pure]⟩
  | @step_block_body _ _ _ _ hs ih =>
    obtain ⟨fr, ci, rfl, hfr, hci⟩ := (IKleeneConfig.abs_eq_block ..).1 hx
    obtain ⟨f0, os, c1, revs, ha, hd1, ht1, hrevs, h1⟩ := ih (c := ci) hd.2 ht.2 hci
    have hnt : ∀ ρ, ci ≠ .terminal ρ := by rintro _ rfl; cases hci; cases hs
    have hl := StepKleeneE.lvl_defines
      (fun _ _ _ _ _ h => evalCmdE_cmdDefsSound _ _ _ _ _ h.toEvalCmdE) hs
    refine ⟨f0, os, .block (fr.record ci.levelCmd?) c1, revs,
      by simp [IKleeneConfig.abs, ha, hfr],
      ⟨(ScopeFrame.record_parent fr ci.levelCmd?).symm ▸ hd.1, hd1⟩,
      ⟨ScopeFrame.record_exact ht.1 fun x hx => ?_, ht1⟩, hrevs, fun fuel hf _ _ _ => by
        simp [stepInterpKleene_block_step _ _ _ hnt, replayRun_bind, h1 fuel hf,
          replayRun_pure, -bind_pure_comp]⟩
    have hx' := hl x (by rwa [← ha, IKleeneConfig.lvl_abs, InterpLang.absStore_isSome hd1.lvl])
    rwa [← hci, IKleeneConfig.lvl_abs, IKleeneConfig.levelCmd?_abs,
      InterpLang.absStore_isSome hd.2.lvl] at hx'
  | @step_block_done _ ρ =>
    obtain ⟨fr, ci, rfl, rfl, hci⟩ := (IKleeneConfig.abs_eq_block ..).1 hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_terminal ..).1 hci
    refine ⟨0, [], .terminal { ρ with store := fr.exit ρ.store }, [], ?_,
      ⟨ScopeFrame.exit_eq ht.1 ▸ hd.2.1.project _, hd.2.2⟩, trivial, rfl,
      fun _ _ _ _ _ => by simp [stepInterpKleene, replayRun_pure]⟩
    simp only [IKleeneConfig.abs, IEnv.abs, ScopeFrame.exit_eq ht.1,
      InterpLang.absStore_project _ hd.1]

/-- **Whole-run completeness of `runInterpKleene` over base commands.**  A derivation of the
    multi-step event-trace Kleene reference semantics `StepKleeneStarE` from the abstraction
    (`IKleeneConfig.abs`) of a tracked (`IKleeneConfig.Tracked`) configuration `start`, whose
    commands follow the engine-realizable base-command relation and which reaches a terminal
    config `final`, is reproduced by a replayed `runInterpKleene` run from `start` to a
    configuration denoting `final` at every sufficiently large fuel, consuming an oracle
    `oracle`, logging it as used, and recording runtime events whose images are the
    derivation's events. -/
private theorem runInterpKleene_complete_replay {F : P.Factory}
    {start : IKleeneConfig P (Cmd P)} {final : KleeneConfig P (Cmd P)} {evs : List (Event P)}
    (hd : start.Denoting F) (ht : start.Tracked)
    (hrun : StepKleeneStarE P (EvalCmdEngE P R) (start.abs F) evs final)
    (hdone : ∃ e, final = .terminal e) :
    ∃ (f0 : Nat) (oracle : List P.Expr) (final' : IKleeneConfig P (Cmd P))
      (revs : List (IEvent P)), (final'.abs F) = final ∧ final'.Denoting F ∧
      revs.map (REvent.abs F) = evs ∧
      ∀ (fuel : Nat), f0 ≤ fuel →
      ∀ (rest u : List P.Expr) (t : List (IEvent P)),
        replayRun (runInterpKleene (stepBaseCmdStore (m := ReplayM P)) fuel start) cfg
            { remaining := oracle ++ rest, usedRev := u, traceRev := t }
          = (.ok final', { remaining := rest, usedRev := oracle.reverse ++ u,
                                      traceRev := revs.reverse ++ t }) := by
  generalize hx : start.abs F = x at hrun
  induction hrun generalizing start with
  | refl =>
    obtain ⟨e, rfl⟩ := hdone
    obtain ⟨ie, rfl, rfl⟩ := (IKleeneConfig.abs_eq_terminal ..).1 hx
    exact ⟨0, [], .terminal ie, [], rfl, hd, rfl, fun fuel _ _ _ _ => by
      cases fuel <;> simp [runInterpKleene, replayRun_pure]⟩
  | step _ _ _ _ _ hs _ ih =>
    subst hx
    obtain ⟨fStep, osStep, c1, rStep, ha, hd1, ht1, hrStep, hStep⟩ :=
      stepKleeneE_complete_replay _ _ hcfg hMono hvalid hbool hlit hd ht hs
    obtain ⟨fRest, osRest, final', rRest, hfa, hdf, hrRest, hRest⟩ := ih hd1 ht1 hdone ha
    have hnt : ∀ ρ, start ≠ .terminal ρ := by rintro _ rfl; cases hs
    refine ⟨fStep + fRest + 1, osStep ++ osRest, final', rStep ++ rRest, hfa, hdf,
      by simp [hrStep, hrRest], fun | 0, h => nomatch h | k + 1, _ => ?_⟩
    simp [runInterpKleene_succ_step _ _ hnt, replayRun_bind, hStep (k + 1) (by omega),
      hRest k (by omega)]

/-- **Completeness of the monadic Kleene interpreter against the base-command
    event semantics.**  A derivation of the multi-step event-trace Kleene semantics
    `StepKleeneStarE` whose commands follow the engine-realizable base-command relation
    (nondeterministic values read off the choice record `R`) and which reaches a terminal
    config is a derivation of the reference semantics over the base command relation
    `EvalCmdE`, and it is reproduced by a replay run from every tracked interpreter
    configuration `istart` denoting the start config to a configuration denoting the final
    config (oracle `oracle`, from the empty start state), whose recorded trace is runtime events
    whose images are exactly its events, most recent first. -/
theorem runInterpKleene_completeE (F : P.Factory)
    {start final : KleeneConfig P (Cmd P)} {evs : List (Event P)}
    (istart : IKleeneConfig P (Cmd P))
    (hstart : istart.Denoting F ∧ istart.Tracked ∧ istart.abs F = start)
    (hrun : StepKleeneStarE P (EvalCmdEngE P R) start evs final)
    (hdone : ∃ e, final = .terminal e) :
    (StepKleeneStarE P (@EvalCmdE P _ _) start evs final)
    ∧ ∃ (fuel : Nat) (oracle : List P.Expr) (st' : ReplayState P)
        (final' : IKleeneConfig P (Cmd P)) (revs : List (IEvent P)), (final'.abs F) = final ∧
        final'.Denoting F ∧
        replayRun (runInterpKleene (stepBaseCmdStore (m := ReplayM P)) fuel istart)
            cfg { remaining := oracle } = (.ok final', st')
          ∧ st'.traceRev = revs.reverse ∧ revs.map (REvent.abs F) = evs := by
  obtain ⟨hd, ht, rfl⟩ := hstart
  obtain ⟨fuel, oracle, final', revs, hfa, hdf, hrevs, hreplay⟩ :=
    runInterpKleene_complete_replay _ cfg hcfg hMono hvalid hbool hlit hd ht hrun hdone
  exact ⟨hrun.imp fun _ _ _ => (·.imp fun _ _ _ _ _ => (·.toEvalCmdE)), fuel, oracle, _, final',
    revs, hfa, hdf, by simpa using hreplay fuel .refl [] [] [], by simp, hrevs⟩

end ReplayBase

/-! # Call-aware completeness (engine-realizable, monad-generic)

Mirrors the CFG construction (`InterpreterCFGCallComplete.lean`): completeness is
stated against the **engine-realizable** event closure `StepKleeneEngStarE R
(EvalCommandEngAtE π R n)`, where every nondeterministic choice is *recorded* in
the choice record `R` — the `.choice` Boolean and the `.loop` continue/stop
decision are each a value `R ρ.factory ρ.store boolTy v`, and a `.call`'s internal
choices live in `R` through `EvalCommandEngAtE`.  This is the "with the choices
recorded" sense of completeness.  Relating a plain `StepKleeneExtStarE` derivation to
the engine is a separate realizability argument about the derivation's choices, not about
Kleene control flow, so this module does not make it. -/

open Classical in
/-- The **engine-realizable** Kleene event step: `StepKleeneE` with the `.choice`
    and `.loop` nondeterminism resolved by a recorded choice `R … v` and the branch
    taken by whether `v` is the true value of the factory; `v` is the true or the false value,
    so a `ChooseResolves` observation can reproduce it. -/
inductive StepKleeneEngE {CmdT : Type} (R : ChoiceRecord P)
    (EvalCmd : EvalCmdParamE P CmdT (Event P)) :
    KleeneConfig P CmdT → List (Event P) → KleeneConfig P CmdT → Prop where
  | step_cmd {ρ : Env P} {c : CmdT} {σ' : SemanticStore P} {emitted : List (Event P)} :
    EvalCmd ρ.factory ρ.store c σ' emitted →
    StepKleeneEngE R EvalCmd (.stmt (.cmd c) ρ) emitted (.terminal { ρ with store := σ' })
  | step_seq {s1 s2 : KleeneStmt P CmdT} {ρ : Env P} :
    StepKleeneEngE R EvalCmd (.stmt (.seq s1 s2) ρ) [] (.seq (.stmt s1 ρ) s2)
  | step_choice {s1 s2 : KleeneStmt P CmdT} {ρ : Env P} {v : P.Val} :
    R ρ.factory ρ.store (HasBool.boolTy (P := P)) v →
    (v = HasBool.ttVal ρ.factory ∨ v = HasBool.ffVal ρ.factory) →
    StepKleeneEngE R EvalCmd (.stmt (.choice s1 s2) ρ) []
      (.stmt (if v = HasBool.ttVal ρ.factory then s1 else s2) ρ)
  | step_loop {s : KleeneStmt P CmdT} {ρ : Env P} {v : P.Val} :
    R ρ.factory ρ.store (HasBool.boolTy (P := P)) v →
    (v = HasBool.ttVal ρ.factory ∨ v = HasBool.ffVal ρ.factory) →
    StepKleeneEngE R EvalCmd (.stmt (.loop s) ρ) []
      (if v = HasBool.ttVal ρ.factory
        then .seq (.block ρ.store (.stmt s ρ)) (.loop s) else .terminal ρ)
  | step_block {s : KleeneStmt P CmdT} {ρ : Env P} :
    StepKleeneEngE R EvalCmd (.stmt (.block s) ρ) [] (.block ρ.store (.stmt s ρ))
  | step_seq_inner {inner inner' : KleeneConfig P CmdT} {emitted : List (Event P)}
      {s2 : KleeneStmt P CmdT} :
    StepKleeneEngE R EvalCmd inner emitted inner' →
    StepKleeneEngE R EvalCmd (.seq inner s2) emitted (.seq inner' s2)
  | step_seq_done {ρ' : Env P} {s2 : KleeneStmt P CmdT} :
    StepKleeneEngE R EvalCmd (.seq (.terminal ρ') s2) [] (.stmt s2 ρ')
  | step_block_body {inner inner' : KleeneConfig P CmdT} {emitted : List (Event P)}
      {σ_parent : SemanticStore P} :
    StepKleeneEngE R EvalCmd inner emitted inner' →
    StepKleeneEngE R EvalCmd (.block σ_parent inner) emitted (.block σ_parent inner')
  | step_block_done {ρ' : Env P} {σ_parent : SemanticStore P} :
    StepKleeneEngE R EvalCmd (.block σ_parent (.terminal ρ')) []
      (.terminal { ρ' with store := projectStore σ_parent ρ'.store })

/-- The reflexive-transitive closure of `StepKleeneEngE`, concatenating each step's events
    chronologically. -/
abbrev StepKleeneEngStarE {CmdT : Type} (R : ChoiceRecord P)
    (EvalCmd : EvalCmdParamE P CmdT (Event P)) :
    KleeneConfig P CmdT → List (Event P) → KleeneConfig P CmdT → Prop :=
  ReflTransTrace (StepKleeneEngE R EvalCmd)

section Generic

variable {CmdT : Type} [CmdDefs P CmdT] {m : Type → Type} [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m]

variable (obs : InterpObs P m) (R : ChoiceRecord P)
    (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (stepOf : Nat → StepCmdStoreM P CmdT m)
    (cfgr : obs.Cfg) {F : P.Factory}
    (hChoose : ChooseResolves obs cfgr F R)
    (hCmdC : ∀ (σ : IStore P) (c : CmdT) (σ' : SemanticStore P)
        (emitted : List (Event P)) (st : obs.St), RStore.Denoting F σ.get →
        EvalCmd F (InterpLang.absStore F σ.get) c σ' emitted →
        ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
          RStore.Denoting F σi.get ∧
          (∀ i fuel, f0 ≤ i → f0 ≤ fuel →
            obs.run (stepOf i fuel (InterpLang.rfactory F) σ c) cfgr st = (.ok σi, st'))
          ∧ obs.TraceExt F st st' emitted)

include hChoose hCmdC

omit [HasFvar P] in
/-- **Per-step completeness of `stepInterpKleene`.**  One step of the engine-realizable
    Kleene relation `StepKleeneEngE` out of the abstraction (`IKleeneConfig.abs`) of a tracked
    (`IKleeneConfig.Tracked`) configuration `c` is reproduced by one `stepInterpKleene` step
    from `c` at every sufficiently large fuel, reaching a tracked configuration that stands for
    the step's successor and emitting runtime events whose images are exactly the step's
    events.  It assumes that the observation resolves every choice recorded in `R`, that the
    command stepper
    reproduces every reference command step at every sufficiently large fuel, and that every
    reference command evaluation defines only the names `CmdDefs` lists (`hdefs`). -/
private theorem stepKleeneEngE_completeE
    (hdefs : CmdDefsSound EvalCmd)
    {c : IKleeneConfig P CmdT} {evs : List (Event P)} {c' : KleeneConfig P CmdT}
    (hd : c.Denoting F) (ht : c.Tracked) (h : StepKleeneEngE R EvalCmd (c.abs F) evs c')
    (st : obs.St) :
    ∃ (f0 : Nat) (ci : IKleeneConfig P CmdT) (st' : obs.St),
      (∀ i fuel, f0 ≤ i → f0 ≤ fuel →
        obs.run (stepInterpKleene (stepOf i) fuel c) cfgr st = (.ok ci, st'))
      ∧ (ci.abs F) = c' ∧ ci.Denoting F ∧ ci.Tracked ∧ obs.TraceExt F st st' evs := by
  generalize hx : c.abs F = x at h
  induction h generalizing c st with
  | @step_cmd ρ _ σ' _ hc =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    obtain ⟨hdS, hdF⟩ := hd
    obtain ⟨f0, σi, st', rfl, hdi, h1, h2⟩ := hCmdC ρ.store _ _ _ st hdS hc
    exact ⟨f0, .terminal ⟨σi, InterpLang.rfactory F⟩, st', fun i fuel hi hf => by
      simp [stepInterpKleene, obs.run_bind, hdF, h1 i fuel hi hf, obs.run_pure, -bind_pure_comp],
      rfl, ⟨hdi, rfl⟩, trivial, h2⟩
  | @step_seq s1 s2 ρ =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, .seq (.stmt s1 ρ) s2, st, fun _ _ _ _ => by simp [stepInterpKleene, obs.run_pure],
      rfl, hd, trivial, [], rfl, rfl⟩
  | @step_choice s1 s2 ρ v hR hv =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    obtain ⟨hdS, hdF⟩ := hd
    obtain ⟨r, st', h1, -, hvt, hvf, h2⟩ := hChoose _ _ _ _ st (storeDenotes_absStore hdS) hR
    by_cases hvv : v = HasBool.ttVal F
    · exact ⟨0, .stmt s1 ρ, st', fun _ _ _ _ => by
        simp [stepInterpKleene, resolveGuard, obs.run_bind, hdF, h1, hvt hvv, obs.run_pure,
          -bind_pure_comp], by simp [IKleeneConfig.abs, IEnv.abs, hvv], ⟨hdS, hdF⟩, trivial, [],
        rfl, h2⟩
    · exact ⟨0, .stmt s2 ρ, st', fun _ _ _ _ => by
        simp [stepInterpKleene, resolveGuard, obs.run_bind, hdF, h1, hvf (hv.resolve_left hvv),
          obs.run_pure, -bind_pure_comp], by simp [IKleeneConfig.abs, IEnv.abs, hvv], ⟨hdS, hdF⟩,
        trivial, [], rfl, h2⟩
  | @step_loop s ρ v hR hv =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    obtain ⟨hdS, hdF⟩ := hd
    obtain ⟨r, st', h1, -, hvt, hvf, h2⟩ := hChoose _ _ _ _ st (storeDenotes_absStore hdS) hR
    by_cases hvv : v = HasBool.ttVal F
    · refine ⟨0, .seq (.block (.opened ρ.store) (.stmt s ρ)) (.loop s), st', fun _ _ _ _ => ?_,
        by simp [hvv, IKleeneConfig.abs, ScopeFrame.opened, IEnv.abs], ⟨hdS, hdS, hdF⟩,
        by simp [IKleeneConfig.Tracked, IKleeneConfig.lvl], [], rfl, h2⟩
      simp [stepInterpKleene, resolveGuard, obs.run_bind, hdF, h1, obs.run_pure, hvt hvv]
    · refine ⟨0, .terminal ρ, st', fun _ _ _ _ => ?_, by simp [hvv, IKleeneConfig.abs, IEnv.abs],
        ⟨hdS, hdF⟩, trivial, [], rfl, h2⟩
      simp [stepInterpKleene, resolveGuard, obs.run_bind, hdF, h1, obs.run_pure,
        hvf (hv.resolve_left hvv)]
  | @step_block s ρ =>
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx
    exact ⟨0, .block (.opened ρ.store) (.stmt s ρ), st,
      fun _ _ _ _ => by simp [stepInterpKleene, obs.run_pure], rfl, ⟨hd.1, hd⟩,
      by simp [IKleeneConfig.Tracked, IKleeneConfig.lvl], [], rfl, rfl⟩
  | @step_seq_inner _ _ _ s2 hs ih =>
    obtain ⟨ci, rfl, hci⟩ := (IKleeneConfig.abs_eq_seq ..).1 hx
    obtain ⟨f0, c1, st', h1, ha, hd1, ht1, h2⟩ := ih (c := ci) hd ht st hci
    have hnt : ∀ ρ, ci ≠ .terminal ρ := by rintro _ rfl; cases hci; cases hs
    exact ⟨f0, .seq c1 s2, st', fun i fuel hi hf => by
      simp [stepInterpKleene_seq_step _ _ _ hnt, obs.run_bind, h1 i fuel hi hf, obs.run_pure,
        -bind_pure_comp], by simp [IKleeneConfig.abs, ha], hd1, ht1, h2⟩
  | @step_seq_done ρ s2 =>
    obtain ⟨ci, rfl, hci⟩ := (IKleeneConfig.abs_eq_seq ..).1 hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_terminal ..).1 hci
    exact ⟨0, .stmt s2 ρ, st, fun _ _ _ _ => by simp [stepInterpKleene, obs.run_pure], rfl,
      hd, trivial, [], rfl, rfl⟩
  | @step_block_body _ _ _ _ hs ih =>
    obtain ⟨fr, ci, rfl, hfr, hci⟩ := (IKleeneConfig.abs_eq_block ..).1 hx
    obtain ⟨f0, c1, st', h1, ha, hd1, ht1, h2⟩ := ih (c := ci) hd.2 ht.2 st hci
    have hnt : ∀ ρ, ci ≠ .terminal ρ := by rintro _ rfl; cases hci; cases hs
    have hE : ∀ {a e b}, StepKleeneEngE R EvalCmd a e b → StepKleeneE P EvalCmd a e b := by
      intro _ _ _ h
      induction h with
      | step_cmd hc => exact .step_cmd hc
      | step_choice => split <;> constructor
      | step_loop => split <;> constructor
      | step_seq_inner _ ih => exact .step_seq_inner ih
      | step_block_body _ ih => exact .step_block_body ih
      | _ => constructor
    have hl := StepKleeneE.lvl_defines hdefs (hE hs)
    refine ⟨f0, .block (fr.record ci.levelCmd?) c1, st', fun i fuel hi hf => by
      simp [stepInterpKleene_block_step _ _ _ hnt, obs.run_bind, h1 i fuel hi hf, obs.run_pure,
        -bind_pure_comp], by simp [IKleeneConfig.abs, ha, hfr],
      ⟨(ScopeFrame.record_parent fr ci.levelCmd?).symm ▸ hd.1, hd1⟩,
      ⟨ScopeFrame.record_exact ht.1 fun x hx => ?_, ht1⟩, h2⟩
    have hx' := hl x (by rwa [← ha, IKleeneConfig.lvl_abs, InterpLang.absStore_isSome hd1.lvl])
    rwa [← hci, IKleeneConfig.lvl_abs, IKleeneConfig.levelCmd?_abs,
      InterpLang.absStore_isSome hd.2.lvl] at hx'
  | @step_block_done ρ _ =>
    obtain ⟨fr, ci, rfl, rfl, hci⟩ := (IKleeneConfig.abs_eq_block ..).1 hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_terminal ..).1 hci
    refine ⟨0, .terminal { ρ with store := fr.exit ρ.store }, st,
      fun _ _ _ _ => by simp [stepInterpKleene, obs.run_pure], ?_,
      ⟨ScopeFrame.exit_eq ht.1 ▸ hd.2.1.project _, hd.2.2⟩, trivial, [], rfl, rfl⟩
    simp only [IKleeneConfig.abs, IEnv.abs, ScopeFrame.exit_eq ht.1,
      InterpLang.absStore_project _ hd.1]

omit [HasFvar P] in
/-- **Whole-run completeness of `runInterpKleene`.**  Every derivation of the multi-step
    engine-realizable Kleene semantics `StepKleeneEngStarE` (nondeterministic choices read off
    the choice record `R`) from the abstraction (`IKleeneConfig.abs`) of a tracked
    (`IKleeneConfig.Tracked`) configuration `start` that reaches a terminal config `final` is
    reproduced by a `runInterpKleene` run from `start` to a configuration denoting `final` at
    every sufficiently large fuel, emitting runtime events whose images are exactly the
    derivation's events.  It assumes that the observation resolves every choice recorded in `R`,
    that the command stepper reproduces every reference command step at every sufficiently
    large fuel, and that every reference command evaluation defines only the names `CmdDefs`
    lists (`hdefs`). -/
theorem runInterpKleene_engCompleteE
    (hdefs : CmdDefsSound EvalCmd)
    {start : IKleeneConfig P CmdT} {final : KleeneConfig P CmdT} {evs : List (Event P)}
    (hd : start.Denoting F) (ht : start.Tracked)
    (hstar : StepKleeneEngStarE R EvalCmd (start.abs F) evs final)
    (hdone : ∃ e, final = .terminal e) (st : obs.St) :
    ∃ (f0 : Nat) (final' : IKleeneConfig P CmdT) (st' : obs.St), (final'.abs F) = final ∧
      final'.Denoting F ∧
      (∀ i fuel, f0 ≤ i → f0 ≤ fuel →
        obs.run (runInterpKleene (stepOf i) fuel start) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  generalize hx : start.abs F = x at hstar
  induction hstar generalizing start st with
  | refl =>
    obtain ⟨e, rfl⟩ := hdone
    obtain ⟨ie, rfl, rfl⟩ := (IKleeneConfig.abs_eq_terminal ..).1 hx
    exact ⟨0, .terminal ie, st, rfl, hd, fun _ fuel _ _ => by
      cases fuel <;> simp [runInterpKleene, obs.run_pure], [], rfl, rfl⟩
  | step _ _ _ _ _ hs _ ih =>
    subst hx
    obtain ⟨fStep, c1, stStep, hStep, ha, hd1, ht1, tStep⟩ :=
      stepKleeneEngE_completeE _ _ _ _ _ hChoose hCmdC hdefs hd ht hs st
    obtain ⟨fRest, final', stRest, hfa, hdf, hRest, tRest⟩ := ih hd1 ht1 hdone stStep ha
    have hnt : ∀ ρ, start ≠ .terminal ρ := by rintro _ rfl; cases hs
    refine ⟨fStep + fRest + 1, final', stRest, hfa, hdf,
      fun | _, 0, _, h => nomatch h | i, k + 1, _, _ => ?_, tStep.append tRest⟩
    simp [runInterpKleene_succ_step _ _ hnt, obs.run_bind, hStep i (k + 1) (by omega) (by omega),
      hRest i k (by omega) (by omega)]

end Generic

/-! # Completeness along an oracle, for a family of command steppers

A Kleene run may read each nondeterministic choice off an oracle: the Boolean of a `.choice` or
of a `.loop`, and the choices of each command.  The observation state then carries a
pending-choice predicate `Pending`, and `choose` only has to follow the pending choices
(`ChooseFollows`), so runs that resolve the same `.choice` or `.loop` differently from the same
store are covered.  `runInterpKleene_follows_fam` reproduces such a run at every large enough
stepper index and fuel. -/

/-- One step of a Kleene run that reads its nondeterministic choices off an oracle, on a Kleene
    configuration paired with an oracle.  A command runs through `E`, which turns the oracle `o`
    into `o'`; a `.choice` pops `ttVal` to take its left arm and `ffVal` to take its right arm; a
    `.loop` pops `ttVal` to run one more iteration in its own block and `ffVal` to stop; every
    other step is the `StepKleeneE` step of the same shape and leaves the oracle alone. -/
inductive OracleKleeneStepE {CmdT : Type}
    (E : P.Factory → SemanticStore P → CmdT → SemanticStore P → List (Event P) →
      List P.Val → List P.Val → Prop) :
    KleeneConfig P CmdT × List P.Val → List (Event P) → KleeneConfig P CmdT × List P.Val →
      Prop where
  /-- Run one command through `E`, at the factory and store of the environment. -/
  | step_cmd {ρ : Env P} {c : CmdT} {σ' : SemanticStore P} {evs : List (Event P)}
      {o o' : List P.Val} :
      E ρ.factory ρ.store c σ' evs o o' →
      OracleKleeneStepE E (.stmt (.cmd c) ρ, o) evs (.terminal { ρ with store := σ' }, o')
  /-- A `.seq` statement enters a sequence context. -/
  | step_seq {s1 s2 : KleeneStmt P CmdT} {ρ : Env P} {o : List P.Val} :
      OracleKleeneStepE E (.stmt (.seq s1 s2) ρ, o) [] (.seq (.stmt s1 ρ) s2, o)
  /-- A `.choice` pops `ttVal` to take its left arm. -/
  | step_choice_left {s1 s2 : KleeneStmt P CmdT} {ρ : Env P} {o : List P.Val} :
      OracleKleeneStepE E (.stmt (.choice s1 s2) ρ, HasBool.ttVal ρ.factory :: o) []
        (.stmt s1 ρ, o)
  /-- A `.choice` pops `ffVal` to take its right arm. -/
  | step_choice_right {s1 s2 : KleeneStmt P CmdT} {ρ : Env P} {o : List P.Val} :
      OracleKleeneStepE E (.stmt (.choice s1 s2) ρ, HasBool.ffVal ρ.factory :: o) []
        (.stmt s2 ρ, o)
  /-- A `.loop` pops `ttVal` to run one more iteration of its body in its own block. -/
  | step_loop_step {s : KleeneStmt P CmdT} {ρ : Env P} {o : List P.Val} :
      OracleKleeneStepE E (.stmt (.loop s) ρ, HasBool.ttVal ρ.factory :: o) []
        (.seq (.block ρ.store (.stmt s ρ)) (.loop s), o)
  /-- A `.loop` pops `ffVal` to stop. -/
  | step_loop_zero {s : KleeneStmt P CmdT} {ρ : Env P} {o : List P.Val} :
      OracleKleeneStepE E (.stmt (.loop s) ρ, HasBool.ffVal ρ.factory :: o) [] (.terminal ρ, o)
  /-- A `.block` statement enters a block context, saving the parent store. -/
  | step_block {s : KleeneStmt P CmdT} {ρ : Env P} {o : List P.Val} :
      OracleKleeneStepE E (.stmt (.block s) ρ, o) [] (.block ρ.store (.stmt s ρ), o)
  /-- Lift one inner step of a sequence context. -/
  | step_seq_inner {inner inner' : KleeneConfig P CmdT} {evs : List (Event P)}
      {s2 : KleeneStmt P CmdT} {o o' : List P.Val} :
      OracleKleeneStepE E (inner, o) evs (inner', o') →
      OracleKleeneStepE E (.seq inner s2, o) evs (.seq inner' s2, o')
  /-- A sequence context whose inner configuration is terminal continues with its right
      statement. -/
  | step_seq_done {ρ' : Env P} {s2 : KleeneStmt P CmdT} {o : List P.Val} :
      OracleKleeneStepE E (.seq (.terminal ρ') s2, o) [] (.stmt s2 ρ', o)
  /-- Lift one inner step of a block context. -/
  | step_block_body {inner inner' : KleeneConfig P CmdT} {evs : List (Event P)}
      {σp : SemanticStore P} {o o' : List P.Val} :
      OracleKleeneStepE E (inner, o) evs (inner', o') →
      OracleKleeneStepE E (.block σp inner, o) evs (.block σp inner', o')
  /-- A block context whose inner configuration is terminal projects the store onto the parent
      store's names. -/
  | step_block_done {ρ' : Env P} {σp : SemanticStore P} {o : List P.Val} :
      OracleKleeneStepE E (.block σp (.terminal ρ'), o) []
        (.terminal { ρ' with store := projectStore σp ρ'.store }, o)

section Follows

variable {CmdT : Type} [CmdDefs P CmdT] {m : Type → Type} [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m]

omit [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CmdDefs P CmdT] in
/-- An oracle-reading Kleene step is a `StepKleeneE` step of its configurations, over the command
    relation that forgets the oracles. -/
private theorem OracleKleeneStepE.toStepKleeneE
    {E : P.Factory → SemanticStore P → CmdT → SemanticStore P → List (Event P) →
      List P.Val → List P.Val → Prop}
    {x y : KleeneConfig P CmdT × List P.Val} {evs : List (Event P)}
    (h : OracleKleeneStepE E x evs y) :
    StepKleeneE P (fun f σ c σ' evs => ∃ o o', E f σ c σ' evs o o') x.1 evs y.1 := by
  induction h with
  | step_cmd h => exact .step_cmd ⟨_, _, h⟩
  | step_seq_inner _ ih => exact .step_seq_inner ih
  | step_block_body _ ih => exact .step_block_body ih
  | _ => constructor

variable (obs : InterpObs P m) (cfgr : obs.Cfg) (F : P.Factory) (R : ChoiceRecord P)
    (Pending : obs.St → List P.Val → Prop) {Q : Event P → Prop}
    {E : P.Factory → SemanticStore P → CmdT → SemanticStore P → List (Event P) →
      List P.Val → List P.Val → Prop}
    (stepOf : Nat → StepCmdStoreM P CmdT m)
    (hf : ChooseFollows obs cfgr F R Pending)
    (hbool : ∀ f σ, R f σ HasBool.boolTy (HasBool.ttVal f) ∧
      R f σ HasBool.boolTy (HasBool.ffVal f))
    (hcmd : ∀ (σ : IStore P) c σ' evs o o', RStore.Denoting F σ.get →
      E F (InterpLang.absStore F σ.get) c σ' evs o o' → (∀ ev ∈ evs, Q ev) →
      ∀ st, Pending st o → ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St),
        InterpLang.absStore F σi.get = σ' ∧ RStore.Denoting F σi.get ∧
        (∀ i fuel, f0 ≤ i → f0 ≤ fuel →
          obs.run (stepOf i fuel (InterpLang.rfactory F) σ c) cfgr st = (.ok σi, st'))
        ∧ Pending st' o' ∧ obs.TraceExt F st st' evs)
    (hdefs : ∀ f σ c σ' evs o o', E f σ c σ' evs o o' →
      DefinesWithin σ σ' (CmdDefs.defs (P := P) c))

include hf hbool hcmd hdefs

omit [HasFvar P] in
/-- **Per-step completeness of `stepInterpKleene` along an oracle.**  One oracle-reading Kleene
    step out of the abstraction (`IKleeneConfig.abs`) of a tracked (`IKleeneConfig.Tracked`)
    configuration `c` that denotes at `F`, with oracle `o`, whose events satisfy `Q`, is
    reproduced, from every state `st` with `Pending st o`, by one `stepInterpKleene (stepOf i)`
    step from `c` at every large enough stepper index `i` and fuel, reaching a tracked
    configuration that stands for the step's successor, leaving `Pending` of the step's remaining
    oracle and emitting runtime events whose images are exactly the step's events.  It assumes
    that `choose` follows the pending choices `R` allows (`hf`), that `R` allows `tt` and `ff` as
    Booleans (`hbool`), that every command step of `E` whose events satisfy `Q` is reproduced
    that way by `stepOf i` (`hcmd`), and that every command evaluation of `E` defines only the
    names `CmdDefs` lists (`hdefs`). -/
private theorem stepInterpKleene_follows_fam
    {c : IKleeneConfig P CmdT} {o : List P.Val} {y : KleeneConfig P CmdT × List P.Val}
    {evs : List (Event P)} (hd : c.Denoting F) (ht : c.Tracked)
    (h : OracleKleeneStepE E (c.abs F, o) evs y) (hq : ∀ ev ∈ evs, Q ev)
    (st : obs.St) (hst : Pending st o) :
    ∃ (f0 : Nat) (ci : IKleeneConfig P CmdT) (st' : obs.St),
      (∀ i fuel, f0 ≤ i → f0 ≤ fuel →
        obs.run (stepInterpKleene (stepOf i) fuel c) cfgr st = (.ok ci, st'))
      ∧ ci.abs F = y.1 ∧ ci.Denoting F ∧ ci.Tracked ∧ Pending st' y.2
      ∧ obs.TraceExt F st st' evs := by
  generalize hx : (c.abs F, o) = x at h
  induction h generalizing c o st with
  | @step_cmd ρ _ σ' _ _ _ hc =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx1
    obtain ⟨hdS, hdF⟩ := hd
    obtain ⟨f0, σi, st', rfl, hdi, h1, hp, h2⟩ := hcmd ρ.store _ _ _ _ _ hdS hc hq st hst
    exact ⟨f0, .terminal ⟨σi, InterpLang.rfactory F⟩, st', fun i fuel hi hf => by
      simp [stepInterpKleene, obs.run_bind, hdF, h1 i fuel hi hf, obs.run_pure, -bind_pure_comp],
      rfl, ⟨hdi, rfl⟩, trivial, hp, h2⟩
  | @step_seq s1 s2 ρ =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx1
    exact ⟨0, .seq (.stmt s1 ρ) s2, st, fun _ _ _ _ => by simp [stepInterpKleene, obs.run_pure],
      rfl, hd, trivial, hst, [], rfl, rfl⟩
  | @step_choice_left s1 s2 ρ =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx1
    obtain ⟨hdS, hdF⟩ := hd
    obtain ⟨r, st', h1, -, hvt, -, h2, hp⟩ :=
      hf.choose _ _ _ _ _ st (storeDenotes_absStore hdS) hst (hbool _ _).1
    exact ⟨0, .stmt s1 ρ, st', fun _ _ _ _ => by
      simp [stepInterpKleene, resolveGuard, obs.run_bind, hdF, h1, hvt rfl, obs.run_pure,
        -bind_pure_comp], rfl,
      ⟨hdS, hdF⟩, trivial, hp, [], rfl, h2⟩
  | @step_choice_right s1 s2 ρ =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx1
    obtain ⟨hdS, hdF⟩ := hd
    obtain ⟨r, st', h1, -, -, hvf, h2, hp⟩ :=
      hf.choose _ _ _ _ _ st (storeDenotes_absStore hdS) hst (hbool _ _).2
    exact ⟨0, .stmt s2 ρ, st', fun _ _ _ _ => by
      simp [stepInterpKleene, resolveGuard, obs.run_bind, hdF, h1, hvf rfl, obs.run_pure,
        -bind_pure_comp], rfl, ⟨hdS, hdF⟩, trivial, hp, [], rfl, h2⟩
  | @step_loop_step s ρ =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx1
    obtain ⟨hdS, hdF⟩ := hd
    obtain ⟨r, st', h1, -, hvt, -, h2, hp⟩ :=
      hf.choose _ _ _ _ _ st (storeDenotes_absStore hdS) hst (hbool _ _).1
    exact ⟨0, .seq (.block (.opened ρ.store) (.stmt s ρ)) (.loop s), st', fun _ _ _ _ => by
      simp [stepInterpKleene, resolveGuard, obs.run_bind, hdF, h1, hvt rfl, obs.run_pure],
      by simp [IKleeneConfig.abs, ScopeFrame.opened, IEnv.abs], ⟨hdS, hdS, hdF⟩,
      by simp [IKleeneConfig.Tracked, IKleeneConfig.lvl], hp, [], rfl, h2⟩
  | @step_loop_zero s ρ =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx1
    obtain ⟨hdS, hdF⟩ := hd
    obtain ⟨r, st', h1, -, -, hvf, h2, hp⟩ :=
      hf.choose _ _ _ _ _ st (storeDenotes_absStore hdS) hst (hbool _ _).2
    exact ⟨0, .terminal ρ, st', fun _ _ _ _ => by
      simp [stepInterpKleene, resolveGuard, obs.run_bind, hdF, h1, hvf rfl, obs.run_pure], rfl,
      ⟨hdS, hdF⟩, trivial, hp, [], rfl, h2⟩
  | @step_block s ρ =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_stmt ..).1 hx1
    exact ⟨0, .block (.opened ρ.store) (.stmt s ρ), st,
      fun _ _ _ _ => by simp [stepInterpKleene, obs.run_pure], rfl, ⟨hd.1, hd⟩,
      by simp [IKleeneConfig.Tracked, IKleeneConfig.lvl], hst, [], rfl, rfl⟩
  | @step_seq_inner _ _ _ s2 _ _ hs ih =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨ci, rfl, hci⟩ := (IKleeneConfig.abs_eq_seq ..).1 hx1
    obtain ⟨f0, c1, st', h1, ha, hd1, ht1, hp, h2⟩ :=
      ih (c := ci) hd ht hq st hst (Prod.ext hci rfl)
    have hnt : ∀ ρ, ci ≠ .terminal ρ := by rintro _ rfl; cases hci; cases hs
    exact ⟨f0, .seq c1 s2, st', fun i fuel hi hf => by
      simp [stepInterpKleene_seq_step _ _ _ hnt, obs.run_bind, h1 i fuel hi hf, obs.run_pure,
        -bind_pure_comp], by simp [IKleeneConfig.abs, ha], hd1, ht1, hp, h2⟩
  | @step_seq_done ρ s2 =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨ci, rfl, hci⟩ := (IKleeneConfig.abs_eq_seq ..).1 hx1
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_terminal ..).1 hci
    exact ⟨0, .stmt s2 ρ, st, fun _ _ _ _ => by simp [stepInterpKleene, obs.run_pure], rfl,
      hd, trivial, hst, [], rfl, rfl⟩
  | @step_block_body _ _ _ _ _ _ hs ih =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨fr, ci, rfl, hfr, hci⟩ := (IKleeneConfig.abs_eq_block ..).1 hx1
    obtain ⟨f0, c1, st', h1, ha, hd1, ht1, hp, h2⟩ :=
      ih (c := ci) hd.2 ht.2 hq st hst (Prod.ext hci rfl)
    have hnt : ∀ ρ, ci ≠ .terminal ρ := by rintro _ rfl; cases hci; cases hs
    have hl := StepKleeneE.lvl_defines (fun _ _ _ _ _ ⟨_, _, h⟩ => hdefs _ _ _ _ _ _ _ h)
      hs.toStepKleeneE
    refine ⟨f0, .block (fr.record ci.levelCmd?) c1, st', fun i fuel hi hf => by
      simp [stepInterpKleene_block_step _ _ _ hnt, obs.run_bind, h1 i fuel hi hf, obs.run_pure,
        -bind_pure_comp], by simp [IKleeneConfig.abs, ha, hfr],
      ⟨(ScopeFrame.record_parent fr ci.levelCmd?).symm ▸ hd.1, hd1⟩,
      ⟨ScopeFrame.record_exact ht.1 fun x hx => ?_, ht1⟩, hp, h2⟩
    have hx' := hl x (by rwa [← ha, IKleeneConfig.lvl_abs, InterpLang.absStore_isSome hd1.lvl])
    rwa [← hci, IKleeneConfig.lvl_abs, IKleeneConfig.levelCmd?_abs,
      InterpLang.absStore_isSome hd.2.lvl] at hx'
  | @step_block_done ρ _ =>
    obtain ⟨hx1, rfl⟩ := Prod.mk.inj hx
    obtain ⟨fr, ci, rfl, rfl, hci⟩ := (IKleeneConfig.abs_eq_block ..).1 hx1
    obtain ⟨ρ, rfl, rfl⟩ := (IKleeneConfig.abs_eq_terminal ..).1 hci
    refine ⟨0, .terminal { ρ with store := fr.exit ρ.store }, st,
      fun _ _ _ _ => by simp [stepInterpKleene, obs.run_pure], ?_,
      ⟨ScopeFrame.exit_eq ht.1 ▸ hd.2.1.project _, hd.2.2⟩, trivial, hst, [], rfl, rfl⟩
    simp only [IKleeneConfig.abs, IEnv.abs, ScopeFrame.exit_eq ht.1,
      InterpLang.absStore_project _ hd.1]

omit [HasFvar P] in
/-- **Completeness of the Kleene driver along an oracle, for a family of command steppers.**  An
    oracle-reading Kleene run from the abstraction (`IKleeneConfig.abs`) of a tracked
    (`IKleeneConfig.Tracked`) configuration `start` that denotes at `F`, with oracle `o`, to a
    terminal `y.1` with oracle `y.2`, whose events satisfy `Q`, is reproduced, from every state
    `st` with `Pending st o`, by `runInterpKleene (stepOf i)` from `start` at every large enough
    stepper index `i` and fuel, reaching a configuration that denotes at `F` and stands for
    `y.1`, leaving `Pending st' y.2` and emitting runtime events whose images are exactly the
    run's events.  The choices of the run are arbitrary: a `.choice` or `.loop` may be resolved
    differently each time it is reached.  It assumes that `choose` follows the pending choices
    `R` allows (`hf`), that `R` allows `tt` and `ff` as Booleans (`hbool`), that every command
    step of `E` whose events satisfy `Q` is reproduced by `stepOf i` at every large enough `i`
    and fuel, following its choices (`hcmd`), and that every command evaluation of `E` defines
    only the names `CmdDefs` lists (`hdefs`). -/
theorem runInterpKleene_follows_fam
    {start : IKleeneConfig P CmdT} {o : List P.Val} {y : KleeneConfig P CmdT × List P.Val}
    {evs : List (Event P)} (hd : start.Denoting F) (ht : start.Tracked)
    (h : ReflTransTrace (OracleKleeneStepE E) (start.abs F, o) evs y)
    (hdone : ∃ e, y.1 = .terminal e) (hq : ∀ ev ∈ evs, Q ev) (st : obs.St)
    (hst : Pending st o) :
    ∃ (f0 : Nat) (final' : IKleeneConfig P CmdT) (st' : obs.St), final'.abs F = y.1 ∧
      final'.Denoting F ∧
      (∀ i fuel, f0 ≤ i → f0 ≤ fuel →
        obs.run (runInterpKleene (stepOf i) fuel start) cfgr st = (.ok final', st'))
      ∧ Pending st' y.2 ∧ obs.TraceExt F st st' evs := by
  generalize hx : (start.abs F, o) = x at h
  induction h generalizing start o st with
  | refl =>
    subst hx
    obtain ⟨e, he⟩ := hdone
    obtain ⟨ie, rfl, rfl⟩ := (IKleeneConfig.abs_eq_terminal ..).1 he
    exact ⟨0, .terminal ie, st, rfl, hd, fun _ fuel _ _ => by
      cases fuel <;> simp [runInterpKleene, obs.run_pure], hst, [], rfl, rfl⟩
  | step _ _ _ _ _ hs _ ih =>
    subst hx
    simp only [List.forall_mem_append] at hq
    obtain ⟨fStep, c1, stStep, hStep, ha, hd1, ht1, pStep, tStep⟩ :=
      stepInterpKleene_follows_fam obs cfgr F R Pending stepOf hf hbool hcmd hdefs hd ht hs
        hq.1 st hst
    obtain ⟨fRest, final', stRest, hfa, hdf, hRest, pRest, tRest⟩ :=
      ih hd1 ht1 hdone hq.2 stStep pStep (Prod.ext ha rfl)
    have hnt : ∀ ρ, start ≠ .terminal ρ := by rintro _ rfl; cases hs
    refine ⟨fStep + fRest + 1, final', stRest, hfa, hdf,
      fun | _, 0, _, h => nomatch h | i, k + 1, _, _ => ?_, pRest, tStep.append tRest⟩
    simp [runInterpKleene_succ_step _ _ hnt, obs.run_bind, hStep i (k + 1) (by omega) (by omega),
      hRest i k (by omega) (by omega)]

end Follows

namespace Calls

variable [HasFvars P] [CallLangWF P] [HasOldIdent P]
variable {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m] [MonadExcept StopReason m]
variable {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

omit [CallLangWF P] in
/-- **Call-aware completeness of the monadic Kleene interpreter.**  Every derivation of
    the engine-realizable Kleene semantics `StepKleeneEngStarE R (EvalCommandEngAtE π R n)`
    (each `.choice`, `.loop` and in-call nondeterministic choice read off the choice record
    `R`, calls nested at most `n` deep) from `start` that reaches a terminal config `final` is
    reproduced by a `runCallInterpKleene π` run from every tracked interpreter configuration
    `istart` denoting `start` to a configuration denoting `final` at every sufficiently large
    fuel and call-depth limit, emitting runtime events whose images are exactly the
    derivation's events.  It assumes that the observation emits every event and resolves every
    choice recorded in `R`, and that the bounded evaluator is fuel-monotone. -/
theorem runInterpKleene_callCompleteE
    (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (R : ChoiceRecord P) (n : Nat)
    (cfgr : obs.Cfg) {F : P.Factory}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P)
    (start final : KleeneConfig P (CmdExt P)) (evs : List (Event P))
    (istart : IKleeneConfig P (CmdExt P))
    (hstart : istart.Denoting F ∧ istart.Tracked ∧ istart.abs F = start)
    (hstar : StepKleeneEngStarE R (EvalCommandEngAtE π R n) start evs final)
    (hdone : ∃ e, final = .terminal e) (st : obs.St) :
    ∃ (f0 : Nat) (final' : IKleeneConfig P (CmdExt P)) (st' : obs.St), (final'.abs F) = final ∧
      final'.Denoting F ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCallInterpKleene π fuel istart d) cfgr st
          = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs := by
  obtain ⟨hd, ht, rfl⟩ := hstart
  exact (runInterpKleene_engCompleteE _ _ _ (fun d => stepKleeneCmd π d) _ hchoose
    (fun σ c σ' emitted st hd h =>
      (cfg_stepCmd_store_complete _ _ n hemit hchoose hMono σ c σ' emitted st hd h).imp
        fun _ ⟨σi, st', hσ, hdi, hr, ht⟩ =>
          ⟨σi, st', hσ, hdi, fun d k hd hk => hr k d hk hd, ht⟩)
    (evalCommandEngAtE_cmdDefsSound π R n) hd ht hstar hdone st).imp
    fun _ ⟨c, s, hc, hdc, h, ht⟩ => ⟨c, s, hc, hdc, fun fuel d hf hd => h d fuel hd hf, ht⟩

end Calls

end -- public section

end Imperative
