/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterObs
import all Strata.Languages.Core.InterpreterObs
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterSoundGeneric
import all Strata.Languages.Core.InterpreterEval
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.InterpreterEvalProps
import Strata.Languages.Core.InterpreterReplayTactics
import Strata.DL.Imperative.InterpreterObsProps
public import Strata.Languages.Core.InterpreterEvalSound

/-! # Properties of Core's `EvalM` observation

Lemmas about the definitions of `Core/InterpreterObs.lean`.

Key theorems:
* `evalRun_modify`: `evalRun` of a state update.
* `evalRun_throwH`, `evalRun_modify_throwH`: `evalRun` of an `EvalHalt` throw.
* `runInterpReplay_sound`: a `ReplayM` run of the base-command engine is a `StepStmtStarE`
  execution with exactly the recorded events.
* `runInterpEval_sound`: the same for an `EvalM` run.
* `runInterp_sound_replay`, `runInterp_sound_eval`: the `RunInterpSound` contracts for Core's
  `ReplayM` and `EvalM` runs. -/

namespace Core
open Imperative
public section

/-! ## `evalRun` of state updates and `EvalHalt` throws -/

/-- `evalRun` of `modify g` succeeds and moves to `g s`. -/
theorem evalRun_modify (g : EvalState → EvalState) (opts : EvalOpts) (s : EvalState) :
    evalRun (modify g : EvalM PUnit) opts s = (.ok ⟨⟩, g s) := (rfl)

/-- `evalRun` of an `EvalHalt` throw fails with its `evalHaltReason`, state unchanged. -/
theorem evalRun_throwH {α : Type} (h : EvalHalt) (opts : EvalOpts) (st : EvalState) :
    evalRun (throwThe EvalHalt h : EvalM α) opts st = (.error (evalHaltReason h), st) := (rfl)

/-- `evalRun` of `modify g` then an `EvalHalt` throw fails with its `evalHaltReason` at `g st`. -/
theorem evalRun_modify_throwH {α : Type} (g : EvalState → EvalState) (h : EvalHalt)
    (opts : EvalOpts) (st : EvalState) :
    evalRun ((modify g : EvalM PUnit) >>= fun _ => (throwThe EvalHalt h : EvalM α)) opts st
      = (.error (evalHaltReason h), g st) := (rfl)

/-! ## Whole-run soundness of `ReplayM` and `EvalM` runs -/

/-- Replay soundness for Core (`RunInterpSound` at the replay observation): a `ReplayM` run of the
    base-command engine from a configuration with a well-formed factory (`FactoryWF`), at which the
    bounded evaluator is sound (`BoundedEvalSoundAt`), and typed stores (`Config.storeTyped`)
    that reaches `final` is a reference `StepStmtStarE` execution over
    `EvalCmdE` to `final.abs` whose events are exactly the recorded ones. -/
theorem runInterp_sound_replay :
    RunInterpSound Expression (ReplayM Expression) (obsReplay (P := Expression))
      (baseStepCmd (m := ReplayM Expression)) (@EvalCmdE Expression _ _)
      (Config.storeTyped (P := Expression) (CmdT := Cmd Expression)) :=
  Imperative.runInterp_sound_replay

/-- **Replay soundness for Core.** A `ReplayM` run of the base-command engine from (the interpreter
    configuration of) a configuration with a well-formed factory (`FactoryWF`), at which the
    bounded evaluator is sound (`BoundedEvalSoundAt`), and typed stores (`Config.storeTyped`)
    that reaches `final` is a reference `StepStmtStarE` execution to
    `final.abs` with exactly the recorded events. -/
theorem runInterpReplay_sound :
    ∀ (fuel : Nat) (F : Expression.Factory) (start : Config Expression (Cmd Expression))
      (istart final : IConfig Expression (Cmd Expression))
      (cfg : ReplayCfg Expression) (st st' : ReplayState Expression),
      istart.Denotes F start →
      replayRun (runInterp (baseStepCmd (P := Expression) (m := ReplayM Expression)) fuel
          istart) cfg st
        = (.ok final, st') →
      FactoryWF (P := Expression) F → BoundedEvalSoundAt Expression F → Config.storeTyped start →
      ∃ (evs : List (Event Expression)) (revs : List (IEvent Expression))
        (final' : Config Expression (Cmd Expression)),
        StepStmtStarE (P := Expression) (@EvalCmdE Expression _ _) start evs final' ∧
          final.Denotes F final' ∧ st'.traceRev = revs.reverse ++ st.traceRev ∧
          revs.map (REvent.abs F) = evs :=
  runInterp_sound_replay

/-- **Replay soundness for Core at factories meeting `EvalFactoryWF`.** A `ReplayM` run of the
    base-command engine from (the interpreter configuration of) a configuration with a well-formed
    factory (`FactoryWF`), whose functions meet the conditions under which the bounded evaluator
    is sound (`EvalFactoryWF`, which `evalFactoryWF_of_userFuncs` gives program factories), and
    typed stores (`Config.storeTyped`) that reaches `final` is a reference `StepStmtStarE`
    execution to `final.abs` with exactly the recorded events. -/
theorem runInterpReplay_sound_of_evalFactoryWF :
    ∀ (fuel : Nat) (F : Expression.Factory) (start : Config Expression (Cmd Expression))
      (istart final : IConfig Expression (Cmd Expression))
      (cfg : ReplayCfg Expression) (st st' : ReplayState Expression),
      istart.Denotes F start →
      replayRun (runInterp (baseStepCmd (P := Expression) (m := ReplayM Expression)) fuel
          istart) cfg st
        = (.ok final, st') →
      FactoryWF (P := Expression) F → EvalFactoryWF F.factory → Config.storeTyped start →
      ∃ (evs : List (Event Expression)) (revs : List (IEvent Expression))
        (final' : Config Expression (Cmd Expression)),
        StepStmtStarE (P := Expression) (@EvalCmdE Expression _ _) start evs final' ∧
          final.Denotes F final' ∧ st'.traceRev = revs.reverse ++ st.traceRev ∧
          revs.map (REvent.abs F) = evs :=
  fun fuel F start istart final cfg st st' hs hr hf hEvalF ht =>
    runInterpReplay_sound fuel F start istart final cfg st st' hs hr hf
      (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) ht

/-- `EvalM` soundness for Core (`RunInterpSound` at the `EvalM` observation): an `EvalM` run of the
    base-command engine from a configuration with a well-formed factory (`FactoryWF`), at which the
    bounded evaluator is sound (`BoundedEvalSoundAt`), and typed stores (`Config.storeTyped`)
    that reaches `final` is a reference
    `StepStmtStarE` execution over `EvalCmdE` to `final.abs` whose events are exactly the recorded
    ones. -/
theorem runInterp_sound_eval :
    RunInterpSound Expression EvalM obsEval
      (baseStepCmd (m := EvalM)) (@EvalCmdE Expression _ _)
      (Config.storeTyped (P := Expression) (CmdT := Cmd Expression)) :=
  runInterp_sound_generic _ _ _ _ (stepInterpSoundGeneric_of_laws _)

/-- **`EvalM` soundness.** An `EvalM` run of the base-command engine from (the interpreter
    configuration of) a configuration with a well-formed factory (`FactoryWF`), at which the
    bounded evaluator is sound (`BoundedEvalSoundAt`), and typed stores (`Config.storeTyped`)
    that reaches `final` is a reference `StepStmtStarE` execution to
    `final.abs` with exactly the recorded events. -/
theorem runInterpEval_sound :
    ∀ (fuel : Nat) (F : Expression.Factory) (start : Config Expression (Cmd Expression))
      (istart final : IConfig Expression (Cmd Expression)) (opts : EvalOpts) (st st' : EvalState),
      istart.Denotes F start →
      evalRun (runInterp (baseStepCmd (P := Expression) (m := EvalM)) fuel istart)
          opts st
        = (.ok final, st') →
      FactoryWF (P := Expression) F → BoundedEvalSoundAt Expression F → Config.storeTyped start →
      ∃ (evs : List (Event Expression)) (revs : List (IEvent Expression))
        (final' : Config Expression (Cmd Expression)),
        StepStmtStarE (P := Expression) (@EvalCmdE Expression _ _) start evs final' ∧
          final.Denotes F final' ∧ st'.traceRev = revs.reverse ++ st.traceRev ∧
          revs.map (REvent.abs F) = evs :=
  runInterp_sound_eval

/-- **`EvalM` soundness at factories meeting `EvalFactoryWF`.** An `EvalM` run of the
    base-command engine from (the interpreter configuration of) a configuration with a well-formed
    factory (`FactoryWF`), whose functions meet the conditions under which the bounded evaluator
    is sound (`EvalFactoryWF`, which `evalFactoryWF_of_userFuncs` gives program factories), and
    typed stores (`Config.storeTyped`) that reaches `final` is a reference `StepStmtStarE`
    execution to `final.abs` with exactly the recorded events. -/
theorem runInterpEval_sound_of_evalFactoryWF :
    ∀ (fuel : Nat) (F : Expression.Factory) (start : Config Expression (Cmd Expression))
      (istart final : IConfig Expression (Cmd Expression)) (opts : EvalOpts) (st st' : EvalState),
      istart.Denotes F start →
      evalRun (runInterp (baseStepCmd (P := Expression) (m := EvalM)) fuel istart)
          opts st
        = (.ok final, st') →
      FactoryWF (P := Expression) F → EvalFactoryWF F.factory → Config.storeTyped start →
      ∃ (evs : List (Event Expression)) (revs : List (IEvent Expression))
        (final' : Config Expression (Cmd Expression)),
        StepStmtStarE (P := Expression) (@EvalCmdE Expression _ _) start evs final' ∧
          final.Denotes F final' ∧ st'.traceRev = revs.reverse ++ st.traceRev ∧
          revs.map (REvent.abs F) = evs :=
  fun fuel F start istart final opts st st' hs hr hf hEvalF ht =>
    runInterpEval_sound fuel F start istart final opts st st' hs hr hf
      (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) ht

end
end Core
