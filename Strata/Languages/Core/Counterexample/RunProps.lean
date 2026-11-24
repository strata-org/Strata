/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.Run
public import Strata.Languages.Core.Counterexample.BackLink
public import Strata.Languages.Core.Counterexample.ValuationToRun
import all Strata.Languages.Core.Counterexample.Run
import all Strata.Languages.Core.Counterexample.BackLink
import all Strata.Languages.Core.Counterexample.ValuationToRun
public import Strata.DL.Imperative.Counterexample.RunProps
public import Strata.DL.Imperative.Counterexample.BackLinkProps
import Strata.DL.Imperative.InterpreterConfigProps
import Strata.DL.Imperative.InterpreterTowerProps

/-! # Properties of level-(a) counterexamples of Core: outcome validity and the target walk

Key theorems:
- `validOutcome_empty`: the outcome carrying no counterexample data is valid.
- `ValidOutcome.fail_iff_isFail`: on a valid outcome, the runtime verdict `isFail` is
  the `Fail` verdict.
-/

namespace Core

open Imperative

public section

open BackLinkOutcome in
/-- The outcome carrying no counterexample data (`BackLinkOutcome.empty`) is valid
    (`ValidOutcome`) for every procedure table, target and unit. -/
theorem validOutcome_empty (π : String → Option Procedure) (target : AssertId Expression)
    (st : List (Stmt Expression Command)) :
    ValidOutcome π target st (.empty : BackLinkOutcome Expression Command) := by
  simp [ValidOutcomeOf, chain, empty]

/-- On a valid outcome (`ValidOutcome`), the `Fail` verdict (a claim starting at the top
    of `stmts`) holds exactly when the outcome is a lone claim: no unconfirmed slices and
    a claim present. -/
private theorem ValidOutcome.fail_iff {π : String → Option Procedure} {target : AssertId Expression}
    {stmts : List (Stmt Expression Command)} {o : BackLinkOutcome Expression Command}
    (hv : ValidOutcome π target stmts o) :
    o.Fail stmts ↔ o.slices = [] ∧ o.claim.isSome := by
  rcases o with ⟨s, _ | ⟨c, f⟩⟩ <;> grind [ValidOutcomeOf, BackLinkOutcome.chain,
    BackLinkOutcome.Fail]

/-- On a valid outcome (`ValidOutcome`: its head starts at the top of `stmts`, its claim
    is genuine and feasible, its slices are well-formed), the runtime verdict `isFail`
    holds exactly when the `Fail` verdict does (a claim starting at the top of `stmts`). -/
theorem ValidOutcome.fail_iff_isFail {π : String → Option Procedure}
    {target : AssertId Expression} {stmts : List (Stmt Expression Command)}
    {o : BackLinkOutcome Expression Command} (hv : ValidOutcome π target stmts o) :
    o.Fail stmts ↔ o.isFail = true := hv.fail_iff.trans o.isFail_iff.symm

/-! ## Observers of the target walk ignore the interpreter's bookkeeping -/

/-- Below one more tower level, the sub-configurations one level deeper are iteration starts
    exactly when the original ones are. -/
private theorem isIterStart_sub_seqNil (lp : Statement) (x : IConfig Expression Command) (n : Nat) :
    isIterStart lp (IConfig.subAt x.seqNil (n + 1)) = isIterStart lp (IConfig.subAt x n) := by
  cases x with
  | seqs y j =>
    cases n with
    | zero => simp [IConfig.seqNil, IConfig.subAt, isIterStart]
    | succ m =>
      simp only [IConfig.seqNil, IConfig.subAt]
      by_cases h : m < j
      · simp [h, isIterStart, show m + 1 < j + 1 by omega]
      · simp [h, show ¬ m + 1 < j + 1 by omega, show m + 1 - (j + 1) = m - j by omega]
  | _ => simp [IConfig.seqNil, IConfig.subAt]

/-- A configuration under one more tower level is not an iteration start. -/
private theorem isIterStart_sub_seqNil_zero (lp : Statement) (x : IConfig Expression Command) :
    isIterStart lp (IConfig.subAt x.seqNil 0) = false := by
  cases x <;> rfl

/-- Under `m` more tower levels, the sub-configuration at depth `e` is an iteration start exactly
    when `e ≥ m` and the one at depth `e - m` of the original configuration is. -/
private theorem isIterStart_repeat_seqNil (lp : Statement) (X : IConfig Expression Command) :
    ∀ (m e : Nat), isIterStart lp (IConfig.subAt (Nat.repeat IConfig.seqNil m X) e) =
      if e < m then false else isIterStart lp (IConfig.subAt X (e - m))
  | 0, e => by simp [Nat.repeat]
  | m + 1, 0 => by simp [Nat.repeat, isIterStart_sub_seqNil_zero]
  | m + 1, e + 1 => by
    simp only [Nat.repeat, isIterStart_sub_seqNil, isIterStart_repeat_seqNil lp X m e]
    by_cases h : e < m
    · simp [h, show e + 1 < m + 1 by omega]
    · simp [h, show ¬ e + 1 < m + 1 by omega]

/-- At every depth, the sub-configuration of a configuration with the interpreter's bookkeeping
    forgotten is an iteration start exactly when the original configuration's is. -/
private theorem isIterStart_norm (lp : Statement) (c : IConfig Expression Command) :
    ∀ e, isIterStart lp (IConfig.subAt c.norm e) = isIterStart lp (IConfig.subAt c e) := by
  induction c with
  | seq i ss ih =>
    intro e
    cases ss with
    | nil =>
      cases e with
      | zero =>
        simp only [IConfig.norm, isIterStart_sub_seqNil_zero]
        cases i <;> simp [IConfig.subAt, isIterStart]
      | succ n => simp [IConfig.norm, isIterStart_sub_seqNil, IConfig.subAt, ih]
    | cons s ss =>
      cases e with
      | zero =>
        cases i with
        | seqs j k =>
          obtain ⟨y, n, hy⟩ := IConfig.seqNil_eq_seqs (Nat.repeat IConfig.seqNil k j.norm)
          simp [IConfig.norm, Nat.repeat, IConfig.subAt, isIterStart, hy]
        | seq j ss' =>
          cases ss' with
          | nil =>
            obtain ⟨y, n, hy⟩ := IConfig.seqNil_eq_seqs j.norm
            simp [IConfig.norm, IConfig.subAt, isIterStart, hy]
          | cons => simp [IConfig.norm, IConfig.subAt, isIterStart]
        | block l fr j =>
          cases l <;> cases ss <;> simp [IConfig.norm, IConfig.subAt, isIterStart]
        | _ => simp [IConfig.norm, IConfig.subAt, isIterStart]
      | succ n => simp [IConfig.norm, IConfig.subAt, ih]
  | seqs i k ih =>
    intro e
    simp only [IConfig.norm, isIterStart_repeat_seqNil]
    cases e with
    | zero => simp [IConfig.subAt, isIterStart]
    | succ n =>
      simp only [IConfig.subAt]
      by_cases h : n < k
      · simp [h, isIterStart, show n + 1 < k + 1 by omega]
      · simp [h, show ¬ n + 1 < k + 1 by omega, show n + 1 - (k + 1) = n - k by omega, ih]
  | block l fr i ih =>
    intro e
    cases e with
    | zero => simp [IConfig.norm, IConfig.subAt, isIterStart]
    | succ n => exact ih n
  | _ => intro e; cases e <;> rfl

/-- Whether a step started an iteration does not depend on the interpreter's bookkeeping. -/
theorem iterationStarted_norm (c c' : IConfig Expression Command) :
    iterationStarted c.norm c'.norm = iterationStarted c c' := by
  simp only [iterationStarted, IConfig.focus_norm]
  split
  · exact isIterStart_norm _ c' _
  · rfl

/-- The loop-VC watch ignores the interpreter's bookkeeping. -/
theorem loopVCFire_absInvariant (id : LoopVCId) (f : Nat) : (loopVCFire id f).AbsInvariant := by
  refine ⟨fun opens c => ?_, fun c c' => ?_⟩
  · simp only [loopVCFire, loopHeadFires, IConfig.focus_norm]
  · simp only [loopVCFire, iterationStarted_norm, iterationFires, IConfig.focus_norm]

/-- The point-check watch ignores the interpreter's bookkeeping. -/
theorem pointFire_absInvariant (id : PointCheckId) (f : Nat) :
    WalkFire.AbsInvariant { pre := fun _ c => pointFires id f c, post := fun _ _ => false } := by
  refine ⟨fun opens c => ?_, fun _ _ => rfl⟩
  simp only [pointFires, IConfig.focus_norm]

/-- The open-iteration bookkeeping across a step does not depend on the interpreter's own
    bookkeeping. -/
theorem updateOpens_norm (f : Nat) (opens : List OpenIter) (c c' : IConfig Expression Command) :
    updateOpens f opens c.norm c'.norm = updateOpens f opens c c' := by
  simp only [updateOpens, IConfig.activeDepth_norm, IConfig.focus_norm, iterationStarted_norm]

/-- A watch on semantic configurations, applied to the configurations interpreter configurations
    stand for under a factory `F`, ignores the interpreter's bookkeeping. -/
theorem WalkFire.ofAbs_absInvariant (F : Expression.Factory)
    (pre : List OpenIter → Config Expression Command → Bool)
    (post : Config Expression Command → Config Expression Command → Bool) :
    (WalkFire.ofAbs F pre post).AbsInvariant :=
  ⟨fun opens c => by simp [WalkFire.ofAbs], fun c c' => by simp [WalkFire.ofAbs]⟩

end -- public section

end Core
