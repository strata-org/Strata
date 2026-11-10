/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterProps
public import Strata.DL.Imperative.InterpreterConfigProps
import all Strata.DL.Imperative.InterpreterConfig
import all Strata.DL.Imperative.Interpreter

/-! # Sequence towers

Properties of the monadic interpreter's sequence towers (`IConfig.seqs`) and of their expansion
`IConfig.unseqs` into nested `.seq · []` contexts:

* `StepStmtE.wrapSeqs`: a reference step lifts through `k` empty-tail sequence contexts;
* `IConfig.abs_unseqs`, `IConfig.unseqs_unseqs`, `IConfig.levelCmd?_unseqs`: the expansion stands
  for the same semantic configuration, is idempotent and keeps the level command;
* `stepInterp_wrapSeqs`: an interpreter step from a configuration under `k` contexts `.seq · []` is
  the inner step, wrapped;
* `stepInterp_unseqs`: an interpreter step from a configuration and from its expansion reach
  configurations with the same expansion, with the same effects. -/

namespace Imperative

public section

variable {P : PureExpr} {CmdT : Type}

/-! ## Reference steps under sequence contexts -/

/-- A reference step lifts through `k` sequence contexts with no remaining statements. -/
theorem StepStmtE.wrapSeqs [HasBool P] [HasBoolOps P] {EventT : Type _}
    {EvalCmd : EvalCmdParamE P CmdT EventT} {c c' : Config P CmdT} {evs : List EventT}
    (h : StepStmtE P EvalCmd c evs c') :
    ∀ k, StepStmtE P EvalCmd (c.wrapSeqs k) evs (c'.wrapSeqs k)
  | 0 => h
  | k + 1 => .step_seq_inner (StepStmtE.wrapSeqs h k)

/-- A reference step out of a configuration under `k + 1` sequence contexts with no remaining
    statements is a step of the configuration, lifted; or, from a terminal configuration, the
    step to the statement list `[]`, under `k` contexts; or, from an exiting configuration, the
    step to that exit, under `k` contexts. -/
theorem StepStmtE.wrapSeqs_inv [HasBool P] [HasBoolOps P] {EventT : Type _}
    {EvalCmd : EvalCmdParamE P CmdT EventT} {c d : Config P CmdT} {evs : List EventT} :
    ∀ {k}, StepStmtE P EvalCmd (c.wrapSeqs (k + 1)) evs d →
      (∃ c', StepStmtE P EvalCmd c evs c' ∧ d = c'.wrapSeqs (k + 1)) ∨
      (∃ ρ, c = .terminal ρ ∧ evs = [] ∧ d = (Config.stmts [] ρ).wrapSeqs k) ∨
      (∃ l ρ, c = .exiting l ρ ∧ evs = [] ∧ d = (Config.exiting l ρ).wrapSeqs k)
  | 0, h => by
    cases h with
    | step_seq_inner hc => exact .inl ⟨_, hc, rfl⟩
    | step_seq_done => exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
    | step_seq_exit => exact .inr (.inr ⟨_, _, rfl, rfl, rfl⟩)
  | k + 1, h => by
    have lift : ∀ {e : List EventT} {x : Config P CmdT},
        StepStmtE P EvalCmd (c.wrapSeqs (k + 1)) e x →
        (∃ c', StepStmtE P EvalCmd c e c' ∧ Config.seq x [] = c'.wrapSeqs (k + 1 + 1)) ∨
        (∃ ρ, c = .terminal ρ ∧ e = [] ∧ Config.seq x [] = (Config.stmts [] ρ).wrapSeqs (k + 1)) ∨
        (∃ l ρ, c = .exiting l ρ ∧ e = [] ∧
          Config.seq x [] = (Config.exiting l ρ).wrapSeqs (k + 1)) := by
      intro e x hx
      rcases StepStmtE.wrapSeqs_inv hx with
        ⟨c', hc, rfl⟩ | ⟨ρ, rfl, rfl, rfl⟩ | ⟨l, ρ, rfl, rfl, rfl⟩
      · exact .inl ⟨c', hc, rfl⟩
      · exact .inr (.inl ⟨ρ, rfl, rfl, rfl⟩)
      · exact .inr (.inr ⟨l, ρ, rfl, rfl, rfl⟩)
    cases h with
    | step_seq_inner hc => exact lift hc

/-! ## The expansion of sequence towers -/

section Expansion

variable [InterpLang P]

/-- `k + 1` contexts `.seq · []` are one context around `k` of them. -/
private theorem IConfig.wrapSeqs_succ' (c : IConfig P CmdT) (k : Nat) :
    c.wrapSeqs (k + 1) = (IConfig.seq c []).wrapSeqs k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (IConfig.seq · []) ih

/-- Contexts `.seq · []` compose by adding their numbers. -/
private theorem IConfig.wrapSeqs_add (c : IConfig P CmdT) (j k : Nat) :
    (c.wrapSeqs j).wrapSeqs k = c.wrapSeqs (j + k) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (IConfig.seq · []) ih

/-- The expansion commutes with contexts `.seq · []`. -/
@[simp] theorem IConfig.unseqs_wrapSeqs (c : IConfig P CmdT) (k : Nat) :
    (c.wrapSeqs k).unseqs = c.unseqs.wrapSeqs k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (IConfig.seq · []) ih

/-- The expansion is idempotent. -/
@[simp] theorem IConfig.unseqs_unseqs (c : IConfig P CmdT) : c.unseqs.unseqs = c.unseqs := by
  induction c with
  | seqs i k ih => simp [IConfig.unseqs, ih]
  | seq i ss ih => simp [IConfig.unseqs, ih]
  | block l fr i ih => simp [IConfig.unseqs, ih]
  | _ => rfl

/-- Contexts `.seq · []` stand for semantic contexts `.seq · []`. -/
@[simp] theorem IConfig.abs_wrapSeqs [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT)
    (k : Nat) : (c.wrapSeqs k).abs F = (c.abs F).wrapSeqs k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [IConfig.wrapSeqs, IConfig.abs, Config.wrapSeqs, ih]

/-- The expansion stands for the same semantic configuration. -/
@[simp] theorem IConfig.abs_unseqs [DecidableEq P.Ident] (F : P.Factory) (c : IConfig P CmdT) :
    c.unseqs.abs F = c.abs F := by
  induction c with
  | seqs i k ih => simp [IConfig.unseqs, IConfig.abs, ih]
  | seq i ss ih => simp [IConfig.unseqs, IConfig.abs, ih]
  | block l fr i ih => simp [IConfig.unseqs, IConfig.abs, ih]
  | _ => rfl

/-- Contexts `.seq · []` keep the level command. -/
@[simp] theorem IConfig.levelCmd?_wrapSeqs (c : IConfig P CmdT) (k : Nat) :
    (c.wrapSeqs k).levelCmd? = c.levelCmd? := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- The expansion keeps the level command. -/
@[simp] theorem IConfig.levelCmd?_unseqs (c : IConfig P CmdT) :
    c.unseqs.levelCmd? = c.levelCmd? := by
  induction c with
  | stmt s _ => cases s <;> rfl
  | seqs i k ih => simp [IConfig.unseqs, IConfig.levelCmd?, ih]
  | seq i ss ih => exact ih
  | _ => rfl

/-- The expansion of one more context `.seq · []` is that context around the expansion. -/
@[simp] theorem IConfig.unseqs_seqNil (c : IConfig P CmdT) :
    c.seqNil.unseqs = .seq c.unseqs [] := by
  cases c <;> rfl

/-- One more empty-tail sequence context always gives a sequence tower. -/
theorem IConfig.seqNil_eq_seqs (c : IConfig P CmdT) : ∃ i k, c.seqNil = .seqs i k := by
  cases c <;> exact ⟨_, _, rfl⟩

/-- A configuration and its expansion are terminal together. -/
theorem IConfig.unseqs_eq_terminal (c : IConfig P CmdT) (e : IEnv P) :
    c.unseqs = .terminal e ↔ c = .terminal e := by
  cases c with
  | seqs i k => cases k <;> simp [IConfig.unseqs, IConfig.wrapSeqs]
  | _ => simp [IConfig.unseqs]

/-- A configuration and its expansion are exiting together. -/
theorem IConfig.unseqs_eq_exiting (c : IConfig P CmdT) (l : String) (e : IEnv P) :
    c.unseqs = .exiting l e ↔ c = .exiting l e := by
  cases c with
  | seqs i k => cases k <;> simp [IConfig.unseqs, IConfig.wrapSeqs]
  | _ => simp [IConfig.unseqs]

end Expansion

/-! ## Interpreter steps on towers -/

section Step

variable {m : Type → Type}
variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CmdDefs P CmdT]
    [Monad m] [LawfulMonad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- A step from a configuration under `k` contexts `.seq · []` is the step of the configuration,
    wrapped, when it is neither terminal nor exiting. -/
theorem stepInterp_wrapSeqs (stepCmd : StepCmdM P CmdT m) (fuel : Nat) (c : IConfig P CmdT)
    (hnt : ∀ e, c ≠ .terminal e) (hex : ∀ l e, c ≠ .exiting l e) :
    ∀ k, stepInterp stepCmd fuel (c.wrapSeqs k)
      = stepInterp stepCmd fuel c >>= fun i => pure (i.wrapSeqs k)
  | 0 => by simp [IConfig.wrapSeqs]
  | k + 1 => by
    have hk : ∀ e, c.wrapSeqs k ≠ .terminal e := by cases k <;> simp_all [IConfig.wrapSeqs]
    have hk' : ∀ l e, c.wrapSeqs k ≠ .exiting l e := by cases k <;> simp_all [IConfig.wrapSeqs]
    simp only [IConfig.wrapSeqs]
    rw [stepInterp_seq_unfold_gen _ _ _ _ hk hk', stepInterp_wrapSeqs stepCmd fuel c hnt hex k]
    simp

/-- **A step from a configuration and from its expansion agree up to expansion**: they run the
    same effects and reach configurations with the same expansion. -/
theorem stepInterp_unseqs (stepCmd : StepCmdM P CmdT m) (fuel : Nat) :
    ∀ c : IConfig P CmdT, (·.unseqs) <$> stepInterp stepCmd fuel c
      = (·.unseqs) <$> stepInterp stepCmd fuel c.unseqs := by
  intro c
  induction c with
  | stmt | stmts | terminal | exiting => rfl
  | seq i ss ih =>
    by_cases hd : (∃ e, i = .terminal e) ∨ ∃ l e, i = .exiting l e
    · rcases hd with ⟨e, rfl⟩ | ⟨l, e, rfl⟩ <;> rfl
    have hnt : ∀ e, i ≠ .terminal e := fun e h => hd (.inl ⟨e, h⟩)
    have hex : ∀ l e, i ≠ .exiting l e := fun l e h => hd (.inr ⟨l, e, h⟩)
    have hnt' : ∀ e, i.unseqs ≠ .terminal e := fun e h => hnt e ((i.unseqs_eq_terminal e).1 h)
    have hex' : ∀ l e, i.unseqs ≠ .exiting l e := fun l e h =>
      hex l e ((i.unseqs_eq_exiting l e).1 h)
    simp only [IConfig.unseqs]
    rw [stepInterp_seq_unfold_gen _ _ _ _ hnt hex, stepInterp_seq_unfold_gen _ _ _ _ hnt' hex']
    have h2 := congrArg (Functor.map (IConfig.seq · ss)) ih
    simpa [Functor.map_map, IConfig.unseqs] using h2
  | block l fr i ih =>
    by_cases hd : (∃ e, i = .terminal e) ∨ ∃ l e, i = .exiting l e
    · rcases hd with ⟨e, rfl⟩ | ⟨l', e, rfl⟩ <;> rfl
    have hnt : ∀ e, i ≠ .terminal e := fun e h => hd (.inl ⟨e, h⟩)
    have hex : ∀ l e, i ≠ .exiting l e := fun l e h => hd (.inr ⟨l, e, h⟩)
    have hnt' : ∀ e, i.unseqs ≠ .terminal e := fun e h => hnt e ((i.unseqs_eq_terminal e).1 h)
    have hex' : ∀ l e, i.unseqs ≠ .exiting l e := fun l e h =>
      hex l e ((i.unseqs_eq_exiting l e).1 h)
    simp only [IConfig.unseqs]
    rw [stepInterp_block_unfold_gen _ _ _ _ _ hnt hex,
      stepInterp_block_unfold_gen _ _ _ _ _ hnt' hex', IConfig.levelCmd?_unseqs]
    have h2 := congrArg (Functor.map (IConfig.block l (fr.record i.levelCmd?) ·)) ih
    simpa [Functor.map_map, IConfig.unseqs] using h2
  | seqs i k ih =>
    by_cases hd : (∃ e, i = .terminal e) ∨ ∃ l e, i = .exiting l e
    · rcases hd with ⟨e, rfl⟩ | ⟨l, e, rfl⟩ <;> cases k with
      | zero => rfl
      | succ k =>
        simp only [IConfig.unseqs, IConfig.wrapSeqs_succ' _ (k + 1)]
        rw [stepInterp_wrapSeqs _ _ _ (by simp) (by simp)]
        simp [stepInterp, IConfig.unseqs]
    have hnt : ∀ e, i ≠ .terminal e := fun e h => hd (.inl ⟨e, h⟩)
    have hex : ∀ l e, i ≠ .exiting l e := fun l e h => hd (.inr ⟨l, e, h⟩)
    have hnt' : ∀ e, i.unseqs ≠ .terminal e := fun e h => hnt e ((i.unseqs_eq_terminal e).1 h)
    have hex' : ∀ l e, i.unseqs ≠ .exiting l e := fun l e h =>
      hex l e ((i.unseqs_eq_exiting l e).1 h)
    let mrg : IConfig P CmdT → IConfig P CmdT := fun i' =>
      match i' with
      | .seqs c j => .seqs c (j + k + 1)
      | _ => .seqs i' k
    have hstep : stepInterp stepCmd fuel (.seqs i k) = mrg <$> stepInterp stepCmd fuel i := by
      rw [← bind_pure_comp]
      rw [stepInterp.eq_def]
      cases i
      case terminal =>
        simp_all only [exists_false, or_self, not_false_eq_true, ne_eq, IConfig.terminal.injEq,
          forall_eq']
      case exiting =>
        simp_all only [exists_false, or_self, not_false_eq_true, ne_eq, reduceCtorEq, implies_true,
          IConfig.exiting.injEq, not_and, forall_apply_eq_imp_iff, imp_false, forall_eq']
      all_goals
        simp_all only [exists_false, or_self, not_false_eq_true, ne_eq, reduceCtorEq, implies_true,
          bind_pure_comp]
        rw [← bind_pure_comp]
        exact bind_congr fun i' => by cases i' <;> rfl
    have hmerge : ∀ i', (mrg i').unseqs = i'.unseqs.wrapSeqs (k + 1) := by
      intro i'
      cases i' with
      | seqs c j =>
        simp only [mrg, IConfig.unseqs, IConfig.wrapSeqs_add]
        rw [show j + 1 + (k + 1) = j + k + 1 + 1 by omega]
      | _ => rfl
    simp only [IConfig.unseqs]
    rw [hstep, stepInterp_wrapSeqs _ _ _ hnt' hex' (k + 1), bind_pure_comp, Functor.map_map,
      Functor.map_map]
    calc (fun x => (mrg x).unseqs) <$> stepInterp stepCmd fuel i
        = (·.wrapSeqs (k + 1)) <$> ((·.unseqs) <$> stepInterp stepCmd fuel i) := by
          rw [Functor.map_map]; exact congrArg (· <$> _) (funext hmerge)
      _ = (·.wrapSeqs (k + 1)) <$> ((·.unseqs) <$> stepInterp stepCmd fuel i.unseqs) := by rw [ih]
      _ = _ := by rw [Functor.map_map]; simp
