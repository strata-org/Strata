/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCallEmbed
import all Strata.DL.Imperative.InterpreterCallEmbed
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterCall
import Strata.DL.Imperative.InterpreterReplayTactics
public import Strata.DL.Imperative.InterpreterCallProps

/-! # Properties of the embedding of base-command programs into call-aware ones

Lemmas about the definitions of `InterpreterCallEmbed.lean`:
* `runInterp_embedIConfig`: on an embedded interpreter configuration, the call-aware run at any
  callee table is the embedding of the base run;
* `runReplay_embedConfig`: call-aware replay of an embedded program returns the same verdict
  and remaining oracle as base replay.
-/

namespace Imperative
public section
namespace Calls
variable {P : PureExpr}

/-! ## `embedBlock` on list constructors and conditionals -/

/-- `embedBlock` maps the empty block to the empty block. -/
@[simp] theorem embedBlock_nil : embedBlock (P := P) [] = [] := rfl

/-- `embedBlock` embeds a block statement by statement. -/
@[simp] theorem embedBlock_cons (s : Stmt P (Cmd P)) (ss : List (Stmt P (Cmd P))) :
    embedBlock (s :: ss) = embedStmt s :: embedBlock ss := rfl

/-- `embedBlock` commutes with an `if` between two blocks. -/
theorem embedBlock_ite (c : Prop) [Decidable c] (t e : List (Stmt P (Cmd P))) :
    embedBlock (if c then t else e) = if c then embedBlock t else embedBlock e := apply_ite ..

/-! ## The call-aware run on an embedded configuration -/

variable [InterpLang P] in
/-- Embedding commutes with the semantic configuration an interpreter configuration stands for. -/
theorem embedIConfig_abs [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P (Cmd P)) :
    (embedIConfig c).abs F = embedConfig (c.abs F) := by
  induction c with
  | seqs inner k ih =>
    simp only [embedIConfig, IConfig.abs, ih]
    induction k with
    | zero => rfl
    | succ k ihk => simp only [Config.wrapSeqs, embedConfig, embedBlock_nil] at ihk ⊢; rw [ihk]
  | _ => simp_all only [embedIConfig, IConfig.abs, embedConfig]

section Simulation
variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [HasFvar P]
  [HasOldIdent P] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- On an embedded configuration, the call-aware stepper takes the embedding of the base stepper's
    step. -/
private theorem stepInterp_embedIConfig
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (d fuel : Nat) :
    ∀ c : IConfig P (Cmd P),
      stepInterp (stepCmd (m := m) π d) fuel (embedIConfig c)
        = embedIConfig <$> stepInterp (baseStepCmd (m := m)) fuel c := fun c => by
  have hrec : ∀ (fr : ScopeFrame P) (c : IConfig P (Cmd P)),
      fr.record (embedIConfig c).levelCmd? = fr.record c.levelCmd? := fun fr c => by
    have hlvl : ∀ c : IConfig P (Cmd P),
        (embedIConfig c).levelCmd? = c.levelCmd?.map CmdExt.cmd := fun c => by
      induction c with
      | stmt s _ => cases s <;> rfl
      | seq _ _ ih | seqs _ _ ih => simpa [embedIConfig, IConfig.levelCmd?] using ih
      | _ => rfl
    unfold ScopeFrame.record
    rw [hlvl]
    cases fr.defined <;> cases c.levelCmd? <;> rfl
  fun_induction stepInterp <;>
    simp_all +zetaDelta only [embedIConfig, embedStmt, stepCmd_cmd, bind_pure_comp, baseStepCmd,
      Functor.map_map, map_pure, stepInterp, ↓reduceIte, map_bind, embedBlock_cons,
      embedBlock_nil] <;>
    first
    | (cases ‹List _› <;> simp_all only [imp_false, not_true_eq_false, reduceCtorEq, implies_true,
        embedBlock_cons]; done)
    | (cases ‹IConfig _ _› <;>
        simp_all only [reduceCtorEq, implies_true, embedIConfig, bind_map_left,
          IConfig.terminal.injEq, IConfig.exiting.injEq, imp_false, not_and,
          forall_apply_eq_imp_iff, forall_eq'] <;>
        refine bind_congr fun a => ?_ <;> cases a <;> simp [embedIConfig]; done)
    | (congr 1; funext a; cases a <;> simp [embedIConfig, embedStmt]; done)

/-- **Whole run.** On an embedded interpreter configuration, the call-aware interpreter (at any
    callee table `π`) is the embedding of the base interpreter's run, in any monad `m` where mapping
    a function over a throw is the throw itself. -/
theorem runInterp_embedIConfig
    (hmapThrow : ∀ {α β : Type} (f : α → β) (e : StopReason), f <$> (throw e : m α) = throw e)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (d : Nat) :
    ∀ (fuel : Nat) (c : IConfig P (Cmd P)),
      runInterp (stepCmd (m := m) π d) fuel (embedIConfig c)
        = embedIConfig <$> runInterp (baseStepCmd (m := m)) fuel c := fun f c => by
  fun_induction runInterp <;> (try first | rw [runInterp.eq_3] | rw [runInterp.eq_4]) <;>
    simp_all only [embedIConfig, runInterp_terminal, map_pure, runInterp_exiting, imp_false,
      stepInterp_embedIConfig, bind_map_left, map_bind] <;>
    cases ‹IConfig _ _› <;> simp_all only [reduceCtorEq, not_false_eq_true, implies_true,
        embedIConfig, IConfig.terminal.injEq, forall_eq', IConfig.exiting.injEq, not_and,
        forall_apply_eq_imp_iff, imp_false]

end Simulation

/-! ## Replay of an embedded configuration -/

section Replay
variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [HasFvar P]
  [HasOldIdent P] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

omit [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [HasFvar P]
  [HasOldIdent P] in
/-- `f <$> throw e` is `throw e` in `ReplayM`. -/
private theorem replayM_map_throw {α β : Type} (f : α → β) (e : StopReason) :
    f <$> (throw e : ReplayM P α) = throw e := rfl

omit [DecidableEq P.Ident] [HasFvar P] [HasOldIdent P] [HasBool P] [DecidableEq P.Expr]
    in
/-- Running a mapped `ReplayM` computation maps its outcome and keeps its final state. -/
private theorem replayRun_map {α β : Type} (f : α → β) (x : ReplayM P α) (cfg : ReplayCfg P)
    (st : ReplayState P) :
    replayRun (f <$> x) cfg st = ((replayRun x cfg st).1.map f, (replayRun x cfg st).2) := by
  grind [map_eq_pure_bind, replayRun_bind, replayRun_pure, Except.map]

/-- Call-aware replay of an embedded interpreter config is the base replay run, outcome mapped by
    `embedIConfig`. -/
private theorem runReplayRun_embedIConfig (π : String → Option (Procedure P (CmdExt P) Hdr))
    (fuel : Nat) (c : IConfig P (Cmd P)) (cfg : ReplayCfg P) (oracle : List P.Expr) (d : Nat) :
    runReplayRun (runCallInterp (m := ReplayM P) π fuel (embedIConfig c) d) cfg oracle
      = ((runReplayRun (runInterp (baseStepCmd (m := ReplayM P)) fuel c) cfg oracle).1.map
            embedIConfig,
         (runReplayRun (runInterp (baseStepCmd (m := ReplayM P)) fuel c) cfg oracle).2) := by
  simp only [runCallInterp_eq, runInterp_embedIConfig replayM_map_throw]
  apply replayRun_map

/-- **Replay verdict of an embedded program.**  At any callee table `π`, call-aware replay of
    the embedding `embedIConfig c` of an interpreter configuration returns the same verdict and
    remaining oracle as base replay of `c`. -/
theorem runReplay_embedConfig (π : String → Option (Procedure P (CmdExt P) Hdr))
    (fuel : Nat) (c : IConfig P (Cmd P)) (cfg : ReplayCfg P) (haltOn : IEvent P → Bool)
    (oracle : List P.Expr) (d : Nat) :
    runReplay (runCallInterp (m := ReplayM P) π fuel (embedIConfig c) d) cfg haltOn
        oracle
      = runReplay (runInterp (baseStepCmd (m := ReplayM P)) fuel c) cfg haltOn
        oracle := by
  grind [runReplay, runReplayRun_embedIConfig, Except.map]

end Replay
end Calls
end
end Imperative
