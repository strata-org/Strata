/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterSoundGeneric
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.Interpreter
import Strata.DL.Imperative.InterpreterReplayTactics

/-! # Properties of `replayRun`, `RunBridge` and `obsReplay`

Lemmas about the definitions of `InterpreterObs.lean`:
* run lemmas for `emit` with the stop hook off (`replayRun_emit`) and for `choose` on a
  non-empty oracle (`replayRun_choose_cons`);
* `RunBridge` for `emit`, `choose` and `>>=` (`runBridge_emit`, `runBridge_choose`,
  `runBridge_bind`);
* `runInterp_sound_replay`: every `ReplayM` run of the base-command engine is a
  `StepStmtStarE` execution with the recorded trace. -/

namespace Imperative
public section
section Observations
variable {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]

/-! ## Run lemmas for `emit` and `choose`, and `RunBridge` -/

/-- `emit` with the stop hook off (`interruptOn = fun _ => none`) records the event and returns. -/
theorem replayRun_emit (ev : IEvent P) (cfg : ReplayCfg P) (st : ReplayState P)
    (h : cfg.interruptOn = fun _ => none) :
    replayRun (InterpEffects.emit (P := P) (m := ReplayM P) ev) cfg st
      = (.ok ⟨⟩, { st with traceRev := ev :: st.traceRev }) := by
  cases cfg
  cases h
  rfl

/-- With a non-empty oracle whose head passes the value checks, `choose` takes the head, logs it
    in `usedRev`, and leaves the trace unchanged. -/
theorem replayRun_choose_cons (factory : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
    (cfg : ReplayCfg P) (st : ReplayState P) (v : P.Expr) (rest : List P.Expr)
    (hrem : st.remaining = v :: rest)
    (hv : (InterpLang.ops (P := P)).isValue factory v = true)
    (ht : (InterpLang.ops (P := P)).hasType factory v ty = true) :
    replayRun (InterpEffects.choose (P := P) factory store ty) cfg st
      = (.ok v, { st with remaining := rest, usedRev := v :: st.usedRev }) := by
  simp only [InterpEffects.choose, Bool.and_eq_true, replayRun_read_bind, replayRun_get_bind,
    hrem, hv, ht, and_self, ↓reduceIte]
  rfl

/-- `emit` satisfies `RunBridge`: under the stop hook it records a suffix of the hook-off trace
    and, when it does not throw, agrees with the hook-off run. -/
theorem runBridge_emit (ev : IEvent P) (cfg : ReplayCfg P) (st : ReplayState P) :
    RunBridge (InterpEffects.emit (P := P) (m := ReplayM P) ev) cfg st := by
  grind [replayRun_emit_state, replayRun_emit, interruptOff]

/-- `choose` gives equal runs under two configs with the same `oracleConfig`. -/
theorem replayRun_choose_cfg_congr (factory : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
    (cfg cfg' : ReplayCfg P) (st : ReplayState P) (h : cfg.oracleConfig = cfg'.oracleConfig) :
    replayRun (InterpEffects.choose (P := P) factory store ty) cfg st
      = replayRun (InterpEffects.choose (P := P) factory store ty) cfg' st := by
  simp only [InterpEffects.choose, Bool.and_eq_true, replayRun_read_bind, h, replayRun_get_bind]
  (repeat' split) <;> rfl

/-- `choose` satisfies `RunBridge` (its run under the stop hook equals its hook-off run), since
    it does not read `interruptOn`. -/
theorem runBridge_choose (factory : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    RunBridge (InterpEffects.choose (P := P) factory store ty) cfg st := by
  grind [replayRun_choose_cfg_congr, interruptOff]

omit [HasBool P] [DecidableEq P.Expr] in
/-- `RunBridge` (the run under `cfg` records a suffix of the hook-off trace and, on success,
    equals the hook-off run) is closed under `>>=`, provided the continuation, run with the stop
    hook off, only extends the trace that `x` left. -/
theorem runBridge_bind {α β : Type} (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : RunBridge x cfg st)
    (hg : ∀ a s, replayRun x cfg st = (.ok a, s) → RunBridge (g a) cfg s)
    (hgmono : ∀ aO sO, replayRun x (interruptOff cfg) st = (.ok aO, sO) →
        sO.traceRev <:+ (replayRun (g aO) (interruptOff cfg) sO).2.traceRev) :
    RunBridge (x >>= g) cfg st := by grind [replayRun_bind]

/-! ## Whole-run replay soundness -/

section
variable [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [InterpLangTyped P]
  [InterpLangBool P]

/-- **Replay soundness.**  Every `ReplayM` run of the base-command engine that starts from an
    interpreter configuration denoting a configuration with typed stores (`Config.storeTyped`)
    under a well-formed factory (`FactoryWF`) at which the bounded evaluator is sound up to
    denotation (`BoundedEvalSoundAt`), and reaches `final` is an execution of the reference
    event-trace semantics (`StepStmtStarE`) to a configuration `final` denotes, whose event trace
    is the denotation of exactly what the run recorded. -/
theorem runInterp_sound_replay :
    RunInterpSound P (ReplayM P) (obsReplay (P := P)) (baseStepCmd (m := ReplayM P))
      (@EvalCmdE P _ _)
      (Config.storeTyped (P := P) (CmdT := Cmd P)) :=
  runInterp_sound_generic _ _ _ _ (stepInterpSoundGeneric_of_laws _)

end
end Observations
end
end Imperative
