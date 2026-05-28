/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LoopElim
public import Strata.Transform.CoreSpecification
public import Strata.Transform.CoreSpecificationProps
public import Strata.Transform.Specification
public import Strata.Transform.SpecificationProps
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.SemanticsProps
public import Strata.DL.Util.Relations
import all Strata.Transform.LoopElim
import all Strata.Transform.Specification
import all Strata.Transform.SpecificationProps
import all Strata.Transform.CoreSpecification
import all Strata.Transform.CoreSpecificationProps
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.SemanticsProps
import all Strata.DL.Util.Relations

/-! # Loop-Elimination Transformation Correctness

The top-level theorem is `loopElim_overapproximatesAggressive`: the
loop-eliminated program aggressively overapproximates the original.

For each source execution reaching terminal `ρ'`, the transformed program
either reaches the same terminal `ρ'` (exact simulation), or terminates at
some `ρ''` with `hasFailure = true` (an invariant VC failed).

Unlike earlier formulations, this proof does *not* require a `loopInvsBool`
precondition on the source statement: the small-step loop semantics in this
repo already propagates invariant failures into `hasFailure` on the source
side, so source and target agree on invariant-failure behaviour.
-/

public section

namespace Core.LoopElim

open Imperative Specification Specification.Transform Core Imperative.LoopElim

variable (π : String → Option Procedure)
variable (φ : CoreEval → PureFunc Expression → CoreEval)

abbrev LangCore :=
  Core.Specification.Lang.core π φ
abbrev CoreStar := StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
abbrev CC := Config Expression Command

/-! ## Projecting removeLoopsM results -/

/-- Run the `ExceptT`-wrapped monadic computation, yielding the raw pair. -/
noncomputable def stmtRun (σ : LoopElimState) (s : Statement) :
    Except String (Bool × Statement) × LoopElimState :=
  StateT.run (ExceptT.run (Stmt.removeLoopsM s)) σ

noncomputable def blockRun (σ : LoopElimState) (ss : Statements) :
    Except String (Bool × Statements) × LoopElimState :=
  StateT.run (ExceptT.run (Block.removeLoopsM ss)) σ

/-- The transformation succeeded (did not throw). -/
noncomputable def stmtOk (σ : LoopElimState) (s : Statement) : Prop :=
  (stmtRun σ s).fst.isOk = Bool.true

noncomputable def blockOk (σ : LoopElimState) (ss : Statements) : Prop :=
  (blockRun σ ss).fst.isOk = Bool.true

noncomputable def stmtPostState (σ : LoopElimState) (s : Statement) : LoopElimState :=
  (stmtRun σ s).snd

noncomputable def blockPostState (σ : LoopElimState) (ss : Statements) : LoopElimState :=
  (blockRun σ ss).snd

/-- Extract the transformed statement as a projection of `stmtRun`.
    When the transformation fails, returns `default`. -/
noncomputable def stmtResult (σ : LoopElimState) (s : Statement) : Statement :=
  match (stmtRun σ s).fst with
  | .ok (_, s') => s'
  | .error _ => default

/-- Extract the transformed block as a projection of `blockRun`.
    When the transformation fails, returns `default`. -/
noncomputable def blockResult (σ : LoopElimState) (ss : Statements) : Statements :=
  match (blockRun σ ss).fst with
  | .ok (_, ss') => ss'
  | .error _ => default

/-! ## Identity lemmas -/

private theorem stmtResult_cmd (σ : LoopElimState) (c : Command) :
    stmtResult σ (.cmd c) = .cmd c := by
  simp [stmtResult, stmtRun, Stmt.removeLoopsM, StateT.run, ExceptT.run,
        pure, StateT.pure, ExceptT.pure, ExceptT.mk]

private theorem stmtResult_exit (σ : LoopElimState) (l : String)
    (md : MetaData Expression) :
    stmtResult σ (.exit l md) = .exit l md := by
  simp [stmtResult, stmtRun, Stmt.removeLoopsM, StateT.run, ExceptT.run,
        pure, StateT.pure, ExceptT.pure, ExceptT.mk]

private theorem stmtResult_funcDecl (σ : LoopElimState) (d : PureFunc Expression)
    (md : MetaData Expression) :
    stmtResult σ (.funcDecl d md) = .funcDecl d md := by
  simp [stmtResult, stmtRun, Stmt.removeLoopsM, StateT.run, ExceptT.run,
        pure, StateT.pure, ExceptT.pure, ExceptT.mk]

private theorem stmtResult_typeDecl (σ : LoopElimState) (tc : TypeConstructor)
    (md : MetaData Expression) :
    stmtResult σ (.typeDecl tc md) = .typeDecl tc md := by
  simp [stmtResult, stmtRun, Stmt.removeLoopsM, StateT.run, ExceptT.run,
        pure, StateT.pure, ExceptT.pure, ExceptT.mk]

private theorem stmtResult_block (σ : LoopElimState) (l : String)
    (bss : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.block l bss md)) :
    stmtResult σ (.block l bss md) = .block l (blockResult σ bss) md := by
  simp only [stmtResult, stmtRun, blockResult, blockRun, Stmt.removeLoopsM,
    StateT.run, ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    StateT.bind, pure, StateT.pure, ExceptT.pure]
  have hok' := hok
  simp only [stmtOk, stmtRun, Stmt.removeLoopsM, StateT.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    pure, StateT.pure, ExceptT.pure, Except.isOk, Except.toBool] at hok'
  generalize hq : Block.removeLoopsM bss σ = r at hok' ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v => rfl
  | error e => exact Bool.noConfusion hok'

private theorem stmtResult_ite (σ : LoopElimState) (c : ExprOrNondet Expression)
    (tss ess : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.ite c tss ess md)) :
    stmtResult σ (.ite c tss ess md) =
      .ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md := by
  have hok' := hok
  simp only [stmtOk, stmtRun, stmtResult, blockResult, blockRun, blockPostState,
    Stmt.removeLoopsM, StateT.run, ExceptT.run, bind, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, StateT.bind, pure, StateT.pure, ExceptT.pure,
    Except.isOk, Except.toBool] at hok' ⊢
  generalize hq : Block.removeLoopsM tss σ = r at hok' ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | error e => exact Bool.noConfusion hok'
  | ok v =>
    simp only [StateT.bind, ExceptT.bindCont, pure, StateT.pure, ExceptT.pure,
      ExceptT.mk] at hok' ⊢
    generalize hq2 : Block.removeLoopsM ess snd_st = r2 at hok' ⊢
    obtain ⟨fst_res2, snd_st2⟩ := r2
    cases fst_res2 with
    | error e2 => exact Bool.noConfusion hok'
    | ok v2 => rfl

private theorem blockResult_nil (σ : LoopElimState) :
    blockResult σ [] = [] := by
  simp [blockResult, blockRun, Block.removeLoopsM, StateT.run, ExceptT.run,
        pure, StateT.pure, ExceptT.pure, ExceptT.mk]

private theorem blockResult_cons (σ : LoopElimState) (s : Statement)
    (ss : Statements) (hok : blockOk σ (s :: ss)) :
    blockResult σ (s :: ss) =
      stmtResult σ s :: blockResult (stmtPostState σ s) ss := by
  have hok' := hok
  simp only [blockOk, blockRun, blockResult, stmtResult, stmtRun, stmtPostState,
    Block.removeLoopsM, StateT.run, ExceptT.run, bind, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, StateT.bind, pure, StateT.pure, ExceptT.pure,
    Except.isOk, Except.toBool] at hok' ⊢
  generalize hq : Stmt.removeLoopsM s σ = r at hok' ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | error e => exact Bool.noConfusion hok'
  | ok v =>
    simp only [StateT.bind, ExceptT.bindCont, pure, StateT.pure, ExceptT.pure,
      ExceptT.mk] at hok' ⊢
    generalize hq2 : Block.removeLoopsM ss snd_st = r2 at hok' ⊢
    obtain ⟨fst_res2, snd_st2⟩ := r2
    cases fst_res2 with
    | error e2 => exact Bool.noConfusion hok'
    | ok v2 => rfl

private theorem hasFailure_false_backwards
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hnf : c₂.getEnv.hasFailure = Bool.false) :
    c₁.getEnv.hasFailure = Bool.false := by
  cases h : c₁.getEnv.hasFailure
  · rfl
  · exact absurd (StepStmtStar_hasFailure_monotone hstar h) (by simp [hnf])

/-! ## Lifting lemmas for CanFail

The general versions (over arbitrary `CmdT`/`evalCmd`/`extendEval`) live in
`Imperative.Specification.Transform` (see `Strata.Transform.SpecificationProps`):
`canFail_head_to_block`, `canFail_tail_to_block`,
`canFailBlock_to_canFail_block`, `canFailBlock_append_left`,
`canFailBlock_append_right`. -/

/-! ## Loop-specific helpers -/

/-- When the source loop terminal has `hasFailure = false`, the loop step's
    `hasInvFailure` is `false`. -/
private theorem loop_step_hasInvFailure_false_of_or
    {ρ : Env Expression} {hasInvFailure : Bool}
    (hresult_nf : (ρ.hasFailure || hasInvFailure) = Bool.false) :
    hasInvFailure = Bool.false := by
  cases hasInvFailure with
  | false => rfl
  | true => simp [Bool.or_true] at hresult_nf

/-- Any first step of a `.loop` reduction yields the boolean-valuedness of
    each invariant at the pre-state.  All four loop step constructors
    (`step_loop_*`) carry the same `hinv_bool` premise. -/
private theorem loop_first_step_hinv_bool
    {ρ₀ : Env Expression}
    {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {C : CC}
    (h1 : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)
          (.stmt (.loop guardE measure inv body md) ρ₀) C) :
    ∀ le ∈ inv,
      ρ₀.eval ρ₀.store le.2 = some HasBool.tt ∨
      ρ₀.eval ρ₀.store le.2 = some HasBool.ff := by
  cases h1 with
  | step_loop_exit _ hib _ _ => exact hib
  | step_loop_enter _ hib _ _ _ => exact hib
  | step_loop_nondet_exit hib _ => exact hib
  | step_loop_nondet_enter hib _ => exact hib

/-- The env update `{ρ with hasFailure := ρ.hasFailure || false}` is the identity. -/
private theorem env_or_false_eq (ρ : Env Expression) :
    ({ ρ with hasFailure := ρ.hasFailure || Bool.false } : Env Expression) = ρ := by
  cases ρ; simp [Bool.or_false]

/-- Single assert step: assert passes when expr is tt. -/
private theorem assert_pass_step
    (l : String) (e : Expression.Expr) (md : MetaData Expression)
    (ρ : Env Expression) (htt : ρ.eval ρ.store e = .some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval) :
    CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assert l e md)) ρ) (.terminal ρ) := by
  have h : CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assert l e md)) ρ)
      (.terminal { ρ with store := ρ.store, hasFailure := ρ.hasFailure || Bool.false }) :=
    .step _ _ _ (.step_cmd (EvalCommand.cmd_sem (.eval_assert_pass htt hwfb))) (.refl _)
  rwa [env_or_false_eq] at h

/-- Single assume step: assume passes when expr is tt. -/
private theorem assume_pass_step
    (l : String) (e : Expression.Expr) (md : MetaData Expression)
    (ρ : Env Expression) (htt : ρ.eval ρ.store e = .some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval) :
    CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assume l e md)) ρ) (.terminal ρ) := by
  have h : CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assume l e md)) ρ)
      (.terminal { ρ with store := ρ.store, hasFailure := ρ.hasFailure || Bool.false }) :=
    .step _ _ _ (.step_cmd (EvalCommand.cmd_sem (.eval_assume htt hwfb))) (.refl _)
  rwa [env_or_false_eq] at h

/-- Execute a list of passive assert/assume statements that all pass. -/
private theorem stmts_passive_all_pass
    (ss : Statements) (ρ : Env Expression)
    (hall : ∀ s ∈ ss, CoreStar π φ (.stmt s ρ) (.terminal ρ)) :
    CoreStar π φ (.stmts ss ρ) (.terminal ρ) := by
  induction ss with
  | nil => exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons hd tl ih =>
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ ρ (hall hd (.head ..)))
      (ih (fun s hs => hall s (.tail _ hs)))

/-- The mapIdx assert list terminates when all invariants are `tt`. -/
private theorem stmts_mapIdx_assert_terminal
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (md : MetaData Expression) (mkLabel : Nat → String → String)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hall : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt) :
    CoreStar π φ
      (.stmts (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (mkLabel i le.1) le.2 md)) ρ)
      (.terminal ρ) := by
  apply stmts_passive_all_pass π φ _ ρ
  intro s hs; rw [List.mem_mapIdx] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact assert_pass_step π φ _ _ md ρ (hall _ (List.getElem_mem hi)) hwfb

/-- The mapIdx assume list terminates when all invariants are `tt`. -/
private theorem stmts_mapIdx_assume_terminal
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (md : MetaData Expression) (mkLabel : Nat → String → String)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hall : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt) :
    CoreStar π φ
      (.stmts (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (mkLabel i le.1) le.2 md)) ρ)
      (.terminal ρ) := by
  apply stmts_passive_all_pass π φ _ ρ
  intro s hs; rw [List.mem_mapIdx] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact assume_pass_step π φ _ _ md ρ (hall _ (List.getElem_mem hi)) hwfb

/-- CanFail for a list of assert statements where some expression is ff. -/
private theorem stmts_assert_list_canFail
    (ss : Statements) (ρ : Env Expression)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hall : ∀ s ∈ ss, ∃ (l : String) (e : Expression.Expr) (md' : MetaData Expression),
      s = Stmt.cmd (HasPassiveCmds.assert l e md') ∧
      (ρ.eval ρ.store e = .some HasBool.tt ∨ ρ.eval ρ.store e = .some HasBool.ff))
    (hff : ∃ s ∈ ss, ∃ (l : String) (e : Expression.Expr) (md' : MetaData Expression),
      s = Stmt.cmd (HasPassiveCmds.assert l e md') ∧ ρ.eval ρ.store e = .some HasBool.ff) :
    CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) ss ρ := by
  induction ss with
  | nil => obtain ⟨_, hm, _⟩ := hff; exact absurd hm (by simp)
  | cons hd tl ih =>
    obtain ⟨l, e, md', heq, hbool⟩ := hall hd (.head ..)
    subst heq
    cases hbool with
    | inr hff_hd =>
      exact ⟨.seq (.terminal { ρ with hasFailure := ρ.hasFailure || Bool.true }) _,
        by simp [Config.getEnv, Bool.or_true],
        ReflTrans_Transitive _ _ _ _
          (.step _ _ _ .step_stmts_cons (.refl _))
          (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _
            (.step _ _ _ (.step_cmd (EvalCommand.cmd_sem (.eval_assert_fail hff_hd hwfb))) (.refl _)))⟩
    | inl htt_hd =>
      have htl_ff : ∃ s ∈ tl, ∃ l' e' md'',
          s = Stmt.cmd (HasPassiveCmds.assert l' e' md'') ∧ ρ.eval ρ.store e' = .some HasBool.ff := by
        obtain ⟨s, hs, l', e', md'', heq', hff'⟩ := hff
        cases hs with
        | head => simp at heq'; obtain ⟨_, rfl, _⟩ := heq'; rw [hff'] at htt_hd; cases htt_hd
        | tail _ h => exact ⟨s, h, l', e', md'', heq', hff'⟩
      have ⟨cfg, hfail, hreach⟩ := ih (fun s hs => hall s (.tail _ hs)) htl_ff
      exact ⟨cfg, hfail,
        ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ ρ
            (assert_pass_step π φ _ _ md' ρ htt_hd hwfb))
          hreach⟩

/-- If some invariant evaluates to `ff`, the assert list CanFails. -/
private theorem stmts_mapIdx_assert_canFail
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (md : MetaData Expression) (mkLabel : Nat → String → String)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hinv_bool : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                              ρ.eval ρ.store le.2 = .some HasBool.ff)
    (hsome_ff : ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) :
    CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert (mkLabel i le.1) le.2 md)) ρ := by
  apply stmts_assert_list_canFail π φ _ ρ hwfb
  · intro s hs; rw [List.mem_mapIdx] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    exact ⟨_, _, md, rfl, hinv_bool _ (List.getElem_mem hi)⟩
  · obtain ⟨le, hle, hff⟩ := hsome_ff
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hle
    refine ⟨Stmt.cmd (HasPassiveCmds.assert (mkLabel i le.1) le.2 md),
            List.mem_mapIdx.mpr ⟨i, hi, by subst heq; rfl⟩,
            mkLabel i le.1, le.2, md, rfl, hff⟩

/-- When not all invariants evaluate to tt and each is boolean, some evaluates to ff. -/
private theorem not_all_tt_implies_some_ff
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (hinv_bool : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                              ρ.eval ρ.store le.2 = .some HasBool.ff)
    (hnot_all_tt : ¬∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt) :
    ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff := by
  induction inv with
  | nil => exact absurd (fun _ h => nomatch h) hnot_all_tt
  | cons x xs ih =>
    cases hinv_bool x (.head ..) with
    | inr hff => exact ⟨x, .head .., hff⟩
    | inl htt =>
      have : ¬∀ le ∈ xs, ρ.eval ρ.store le.2 = .some HasBool.tt := by
        intro h; apply hnot_all_tt; intro le hle
        cases hle with | head => exact htt | tail _ hmem => exact h le hmem
      have ⟨le, hle, hff⟩ := ih (fun le hle => hinv_bool le (.tail _ hle)) this
      exact ⟨le, .tail _ hle, hff⟩

/-! ## Havoc trace primitives

Helpers for replaying a havoc block (a list of `havoc x` commands wrapped in a
`.block`) so it lands on a chosen target store.  `havoc` is non-deterministic,
so the trace can pick any value for each variable — the helpers here provide
the witness trace that lands precisely on the desired store. -/

/-- A single `havoc n` command can change the store value at `n` to any target
    value, leaving all other variables unchanged. -/
private theorem havoc_targeting_single
    (x : Expression.Ident) (md : MetaData Expression)
    (ρ₀ : Env Expression) (v_target : Expression.Expr)
    (hdef_src : (ρ₀.store x).isSome)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval) :
    ∃ σ' : SemanticStore Expression,
      σ' x = some v_target ∧
      (∀ y, x ≠ y → σ' y = ρ₀.store y) ∧
      CoreStar π φ
        (.stmt (.cmd (HasHavoc.havoc x md)) ρ₀)
        (.terminal { ρ₀ with store := σ' }) := by
  change ∃ σ' : SemanticStore Expression,
    σ' x = some v_target ∧
    (∀ y, x ≠ y → σ' y = ρ₀.store y) ∧
    CoreStar π φ
      (.stmt (.cmd (CmdExt.cmd (Cmd.set x .nondet md))) ρ₀)
      (.terminal { ρ₀ with store := σ' })
  obtain ⟨v_old, hv_old⟩ := Option.isSome_iff_exists.mp hdef_src
  let σ' : SemanticStore Expression := fun y => if x = y then some v_target else ρ₀.store y
  have hσ'_x : σ' x = some v_target := by simp [σ']
  have hσ'_other : ∀ y, x ≠ y → σ' y = ρ₀.store y := by
    intro y hne; simp [σ', hne]
  have hupdate : UpdateState Expression ρ₀.store x v_target σ' :=
    .update hv_old hσ'_x hσ'_other
  exact ⟨σ', hσ'_x, hσ'_other,
    .step _ _ _
      (.step_cmd (EvalCommand.cmd_sem (.eval_set_nondet hupdate hwfvar)))
      (by simp [Bool.or_false]; exact .refl _)⟩

/-- Execute a list of havoc commands, updating the store to match `σ_target`
    on each variable in `vars`. -/
private theorem havocs_targeting_stmts
    (vars : List Expression.Ident) (md : MetaData Expression)
    (ρ₀ : Env Expression) (σ_target : SemanticStore Expression)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hdef_src : ∀ x ∈ vars, (ρ₀.store x).isSome)
    (hdef_tgt : ∀ x ∈ vars, (σ_target x).isSome) :
    ∃ σ_out : SemanticStore Expression,
      (∀ x ∈ vars, σ_out x = σ_target x) ∧
      (∀ x, x ∉ vars → σ_out x = ρ₀.store x) ∧
      CoreStar π φ
        (.stmts (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ρ₀)
        (.terminal { ρ₀ with store := σ_out }) := by
  induction vars generalizing ρ₀ with
  | nil =>
    refine ⟨ρ₀.store, fun _ h => absurd h (List.not_mem_nil), fun _ _ => rfl, ?_⟩
    show CoreStar π φ (.stmts (List.map _ []) ρ₀) (.terminal { ρ₀ with store := ρ₀.store })
    rw [List.map_nil]
    have h : ({ ρ₀ with store := ρ₀.store } : Env Expression) = ρ₀ := by
      cases ρ₀; rfl
    rw [h]; exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons x rest ih =>
    have hdef_x := hdef_tgt x (.head ..)
    obtain ⟨v_target, hv_target⟩ := Option.isSome_iff_exists.mp hdef_x
    have ⟨σ₁, hσ₁_x, hσ₁_other, hstep_x⟩ :=
      havoc_targeting_single π φ x md ρ₀ v_target (hdef_src x (.head ..)) hwfvar
    let ρ₁ : Env Expression := { ρ₀ with store := σ₁ }
    have hdef_src_rest : ∀ y ∈ rest, (σ₁ y).isSome := by
      intro y hy
      by_cases hxy : x = y
      · subst hxy; rw [hσ₁_x]; simp
      · rw [hσ₁_other y hxy]; exact hdef_src y (.tail _ hy)
    have hdef_tgt_rest : ∀ y ∈ rest, (σ_target y).isSome :=
      fun y hy => hdef_tgt y (.tail _ hy)
    have ⟨σ_out, hmatch, hother, hstar_rest⟩ :=
      ih ρ₁ hwfvar hdef_src_rest hdef_tgt_rest
    refine ⟨σ_out, ?_, ?_, ?_⟩
    · intro y hy
      cases hy with
      | head =>
        by_cases hx_rest : x ∈ rest
        · exact hmatch x hx_rest
        · exact (hother x hx_rest).trans (hσ₁_x.trans hv_target.symm)
      | tail _ hy' => exact hmatch y hy'
    · intro y hy
      have hy_rest : y ∉ rest := fun h => hy (.tail _ h)
      have hxy : x ≠ y := fun h => hy (h ▸ .head ..)
      exact (hother y hy_rest).trans (hσ₁_other y hxy)
    · simp only [List.map]
      exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
          (.cmd (HasHavoc.havoc x md))
          (rest.map fun n => Stmt.cmd (HasHavoc.havoc n md))
          ρ₀ ρ₁ hstep_x)
        hstar_rest

/-- Execute the havoc block, targeting `ρ_target.store` on `vars`.  The
    wrapping block uses `∅` outer metadata while the inner havoc commands use
    `md`.  This matches the form produced by `buildHavocBlock`. -/
private theorem havoc_block_to_target
    (label : String) (vars : List Expression.Ident) (md : MetaData Expression)
    (ρ₀ ρ_target : Env Expression)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hdef_src : ∀ x ∈ vars, (ρ₀.store x).isSome)
    (hdef_tgt : ∀ x ∈ vars, (ρ_target.store x).isSome)
    (hagree : ∀ x, x ∉ vars → ρ_target.store x = ρ₀.store x) :
    CoreStar π φ
      (.stmt (.block label (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ∅) ρ₀)
      (.terminal { ρ₀ with store := ρ_target.store }) := by
  have ⟨σ_out, hmatch, hother, hstar⟩ :=
    havocs_targeting_stmts π φ vars md ρ₀ ρ_target.store hwfvar hdef_src hdef_tgt
  have h : projectStore ρ₀.store σ_out = ρ_target.store := by
    funext x
    simp [projectStore]
    split
    · rename_i hsome
      by_cases hx : x ∈ vars
      · exact hmatch x hx
      · rw [hother x hx, hagree x hx]
    · rename_i hnone
      simp at hnone
      by_cases hx : x ∈ vars
      · have := hdef_src x hx
        simp [hnone] at this
      · rw [← hnone, hagree x hx]
  have := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) label _ ∅ ρ₀ { ρ₀ with store := σ_out } hstar
  show CoreStar π φ (.stmt (.block label (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ∅) ρ₀)
    (.terminal { ρ₀ with store := ρ_target.store })
  have heq : { { ρ₀ with store := σ_out } with store := projectStore ρ₀.store σ_out } =
    { ρ₀ with store := ρ_target.store } := by
    simp [h]
  rw [heq] at this
  exact this

/-- The loop transformation for any guard produces this structure. -/
private theorem stmtResult_loop_struct (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md)) :
    ∃ (loop_label first_iter_label : String)
      (first_iter_body then_branch : Statements),
    stmtResult σ (.loop guard measure inv body md) =
      .block loop_label [.block first_iter_label first_iter_body {}, .ite guard then_branch [] {}] {} ∧
    first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) := by
  change ∃ (loop_label first_iter_label : String) (first_iter_body then_branch : Statements),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s') => s' | .error _ => default) =
    .block loop_label [.block first_iter_label first_iter_body {}, .ite guard then_branch [] {}] {} ∧
    first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md))
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    simp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    repeat (first
      | (cases h; exact ⟨_, _, _, _, rfl, rfl⟩)
      | contradiction
      | (split at h; skip))
    all_goals (first | (cases h; exact ⟨_, _, _, _, rfl, rfl⟩) | contradiction)

/-! ## Store agreement outside modifiedVars -/

/-! ### Helper: Block.modifiedVars/definedVars append decomposition -/

private theorem block_modifiedVars_append (ss₁ ss₂ : Statements) :
    Block.modifiedVars (ss₁ ++ ss₂) = Block.modifiedVars ss₁ ++ Block.modifiedVars ss₂ := by
  induction ss₁ with
  | nil => simp [Block.modifiedVars]
  | cons s rest ih => simp [Block.modifiedVars, ih, List.append_assoc]

private theorem block_definedVars_append (ss₁ ss₂ : Statements) (ex : Bool) :
    Block.definedVars (ss₁ ++ ss₂) ex = Block.definedVars ss₁ ex ++ Block.definedVars ss₂ ex := by
  induction ss₁ with
  | nil => simp [Block.definedVars]
  | cons s rest ih => simp [Block.definedVars, ih, List.append_assoc]

private theorem block_funcDeclNames_append (ss₁ ss₂ : Statements) :
    Block.funcDeclNames (P := Expression) (C := Command) (ss₁ ++ ss₂) =
      Block.funcDeclNames ss₁ ++ Block.funcDeclNames ss₂ := by
  induction ss₁ with
  | nil => simp [Block.funcDeclNames]
  | cons s rest ih => simp [Block.funcDeclNames, ih, List.append_assoc]

/-! ### Helper: UpdateStates frame property -/

private theorem updateState_store_frame
    {σ σ' : CoreStore} {v : Expression.Ident} {e : Expression.Expr}
    (hup : UpdateState Expression σ v e σ')
    {y : Expression.Ident} (hne : v ≠ y) :
    σ' y = σ y := by
  cases hup with | update _ _ hframe => exact hframe y hne

private theorem updateStates_store_frame
    {σ σ' : CoreStore} {xs : List Expression.Ident} {vs : List Expression.Expr}
    (hups : UpdateStates σ xs vs σ')
    {y : Expression.Ident} (hy : y ∉ xs) :
    σ' y = σ y := by
  induction hups with
  | update_none => rfl
  | update_some hup _ ih =>
    have hne : _ ≠ y := fun h => hy (List.mem_cons.mpr (.inl h.symm))
    have htail : y ∉ _ := fun h => hy (List.mem_cons.mpr (.inr h))
    exact (ih htail).trans (updateState_store_frame hup hne)

private theorem initState_store_frame
    {σ σ' : CoreStore} {v : Expression.Ident} {e : Expression.Expr}
    (hinit : InitState Expression σ v e σ')
    {y : Expression.Ident} (hne : v ≠ y) :
    σ' y = σ y := by
  cases hinit with | init _ _ hframe => exact hframe y hne

/-! ### EvalCommand store frame -/

/-- `EvalCommand` preserves the store at variables not in `Stmt.modifiedVars (.cmd c)`
    or `Stmt.definedVars (.cmd c)`.  Stated with `Stmt` wrappers so that the
    hypothesis types are stable under `@[expose]` opacity. -/
private theorem evalCommand_store_frame_stmt
    {ρ : Env Expression} {c : Command} {σ' : CoreStore} {f : Bool}
    (heval : EvalCommand π φ ρ.eval ρ.store c σ' f)
    {x : Expression.Ident}
    (hmod : x ∉ Stmt.modifiedVars (Stmt.cmd c))
    (hdef : x ∉ Stmt.definedVars (Stmt.cmd c) false) :
    σ' x = ρ.store x := by
  cases heval with
  | cmd_sem hcmd =>
    -- hmod : x ∉ Stmt.modifiedVars (.cmd c), hdef : x ∉ Stmt.definedVars (.cmd c)
    -- After case split on hcmd, c is a specific Cmd constructor
    -- EvalCmd case split
    cases hcmd with
    | eval_init _ hinit _ =>
      apply initState_store_frame hinit
      intro heq; apply hdef
      simp [Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars, Cmd.definedVars]
      exact heq.symm
    | eval_init_unconstrained hinit _ =>
      apply initState_store_frame hinit
      intro heq; apply hdef
      simp [Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars, Cmd.definedVars]
      exact heq.symm
    | eval_set _ hup _ =>
      apply updateState_store_frame hup
      intro heq; apply hmod
      show x ∈ [_]; exact List.mem_singleton.mpr heq.symm
    | eval_set_nondet hup _ =>
      apply updateState_store_frame hup
      intro heq; apply hmod
      show x ∈ [_]; exact List.mem_singleton.mpr heq.symm
    | eval_assert_pass _ _ => rfl
    | eval_assert_fail _ _ => rfl
    | eval_assume _ _ => rfl
    | eval_cover _ => rfl
  | call_sem _ _ hlhs _ _ _ _ _ _ _ _ _ _ _ _ _ hups =>
    apply updateStates_store_frame hups
    intro hmem; apply hmod
    show x ∈ Stmt.modifiedVars (Stmt.cmd (CmdExt.call _ _ _))
    simp only [Stmt.modifiedVars, HasVarsImp.modifiedVars, Command.modifiedVars]
    rw [hlhs]; exact hmem

/-! ### Config-level touched vars -/

/-- The set of variables that a config can still modify or define during execution. -/
private def Config.touchedVarsSet : CC → List Expression.Ident
  | .stmt s _ => Stmt.modifiedVars s ++ Stmt.definedVars s false
  | .stmts ss _ => Block.modifiedVars ss ++ Block.definedVars ss false
  | .terminal _ => []
  | .exiting _ _ => []
  | .block _ _ _ inner => Config.touchedVarsSet inner
  | .seq inner ss => Config.touchedVarsSet inner ++ Block.modifiedVars ss ++ Block.definedVars ss false

/-! ### Outer-store invariant for block scoping -/

/-- Command evaluation preserves store-isSome. -/
private theorem evalCommand_preserves_isSome
    {ρ : Env Expression} {c : Command} {σ' : CoreStore} {f : Bool}
    {n : Expression.Ident}
    (heval : EvalCommand π φ ρ.eval ρ.store c σ' f)
    (hdef : (ρ.store n).isSome) :
    (σ' n).isSome := by
  have hdef' : isDefined ρ.store [n] := fun v hv => by
    cases List.mem_singleton.mp hv; exact hdef
  cases heval with
  | cmd_sem hcmd =>
    exact (EvalCmdDefMonotone' hdef' hcmd) n (List.Mem.head _)
  | call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hups =>
    exact (UpdateStatesDefMonotone hdef' hups) n (List.Mem.head _)

/-- Block-scope invariant indexed by an outer store `σ_outer`: inside every nested
    `.block _ σ_parent inner`, `σ_parent` contains all vars defined in `σ_outer`,
    AND `inner.getEnv.store` also contains all vars defined in `σ_outer`.
    Trivially true for non-block configs. -/
private def outerInv (σ_outer : SemanticStore Expression) : CC → Prop
  | .stmt _ ρ => ∀ n, (σ_outer n).isSome → (ρ.store n).isSome
  | .stmts _ ρ => ∀ n, (σ_outer n).isSome → (ρ.store n).isSome
  | .terminal ρ => ∀ n, (σ_outer n).isSome → (ρ.store n).isSome
  | .exiting _ ρ => ∀ n, (σ_outer n).isSome → (ρ.store n).isSome
  | .block _ σ_parent _ inner =>
    (∀ n, (σ_outer n).isSome → (σ_parent n).isSome) ∧ outerInv σ_outer inner
  | .seq inner _ => outerInv σ_outer inner

/-- `outerInv σ_outer c` implies `∀ n, (σ_outer n).isSome → (c.getEnv.store n).isSome`. -/
private theorem outerInv_implies_getEnv_isSome (σ_outer : SemanticStore Expression) (c : CC)
    (hinv : outerInv σ_outer c) :
    ∀ n, (σ_outer n).isSome → (c.getEnv.store n).isSome := by
  match c with
  | .stmt _ _ => exact hinv
  | .stmts _ _ => exact hinv
  | .terminal _ => exact hinv
  | .exiting _ _ => exact hinv
  | .block _ _ _ inner =>
    obtain ⟨_, hinner⟩ := hinv
    simp [Config.getEnv]
    exact outerInv_implies_getEnv_isSome σ_outer inner hinner
  | .seq inner _ =>
    simp [Config.getEnv]
    exact outerInv_implies_getEnv_isSome σ_outer inner hinv

/-- Single-step preserves `outerInv σ_outer`. -/
private theorem step_preserves_outerInv
    {σ_outer : SemanticStore Expression} {a b : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b)
    (hinv : outerInv σ_outer a) :
    outerInv σ_outer b := by
  induction hstep with
  | step_cmd heval =>
    intro n hout
    simp [outerInv] at hinv
    exact evalCommand_preserves_isSome (π := π) (φ := φ) heval (hinv n hout)
  | step_block => exact ⟨hinv, hinv⟩
  | step_ite_true _ _ => exact ⟨hinv, hinv⟩
  | step_ite_false _ _ => exact ⟨hinv, hinv⟩
  | step_ite_nondet_true => exact ⟨hinv, hinv⟩
  | step_ite_nondet_false => exact ⟨hinv, hinv⟩
  | step_loop_enter _ _ _ _ _ => exact ⟨hinv, hinv⟩
  | step_loop_exit _ _ _ _ => exact hinv
  | step_loop_nondet_enter _ _ => exact ⟨hinv, hinv⟩
  | step_loop_nondet_exit _ _ => exact hinv
  | step_exit => exact hinv
  | step_funcDecl => exact hinv
  | step_typeDecl => exact hinv
  | step_stmts_nil => exact hinv
  | step_stmts_cons => exact hinv
  | step_seq_inner _ ih => exact ih hinv
  | step_seq_done => exact hinv
  | step_seq_exit => exact hinv
  | step_block_body _ ih =>
    obtain ⟨hpar, hinner⟩ := hinv
    exact ⟨hpar, ih hinner⟩
  | step_block_done =>
    obtain ⟨hpar, hinner⟩ := hinv
    intro n hout
    exact projectStore_isSome (hpar n hout) (hinner n hout)
  | step_block_exit_match _ =>
    obtain ⟨hpar, hinner⟩ := hinv
    intro n hout
    exact projectStore_isSome (hpar n hout) (hinner n hout)
  | step_block_exit_mismatch _ =>
    obtain ⟨hpar, hinner⟩ := hinv
    intro n hout
    exact projectStore_isSome (hpar n hout) (hinner n hout)

/-- Star-step preserves `outerInv σ_outer`. -/
private theorem star_preserves_outerInv
    {σ_outer : SemanticStore Expression} {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hinv : outerInv σ_outer c₁) :
    outerInv σ_outer c₂ := by
  induction hstar with
  | refl => exact hinv
  | step _ _ _ hstep _ ih => exact ih (step_preserves_outerInv π φ hstep hinv)

/-- Convenient wrapper: if a trace starts from `.stmt s ρ₀`, then variables in
    `ρ₀.store` remain defined throughout the trace. -/
private theorem stmt_star_preserves_isSome
    (s : Stmt Expression Command) (ρ₀ : Env Expression) (c₂ : CC)
    (hstar : CoreStar π φ (.stmt s ρ₀) c₂)
    (x : Expression.Ident) (hx : (ρ₀.store x).isSome) :
    (c₂.getEnv.store x).isSome := by
  have hinv₀ : outerInv ρ₀.store (.stmt s ρ₀) := fun _ h => h
  have hinv₂ := star_preserves_outerInv π φ hstar hinv₀
  exact outerInv_implies_getEnv_isSome ρ₀.store c₂ hinv₂ x hx

/-! ### Equality of projected store for loop-elim body

    In the loop-elim context, the block's `σ_parent = ρ₀.store` and the body execution
    only touches vars that are already `isSome` in `ρ₀.store` (by `hswf`). Under these
    conditions, `projectStore ρ₀.store ρ_inner.store = ρ_inner.store`, i.e., the block
    projection is a no-op.

    The key insight: `init x` requires `(current.store x) = none`. But `x ∈ definedVars body`
    combined with `hswf` gives `(ρ₀.store x).isSome`, and by `outerInv` this propagates
    to `(current.store x).isSome`. So `init` commands for vars in `definedVars body` NEVER
    fire during execution, meaning no new vars are introduced. -/

/-- `projectStore_self_env` applied at an env with a different store. -/
private def sameDomInv (σ_outer : SemanticStore Expression) : CC → Prop
  | .stmt _ ρ => ∀ n, (ρ.store n).isSome ↔ (σ_outer n).isSome
  | .stmts _ ρ => ∀ n, (ρ.store n).isSome ↔ (σ_outer n).isSome
  | .terminal ρ => ∀ n, (ρ.store n).isSome ↔ (σ_outer n).isSome
  | .exiting _ ρ => ∀ n, (ρ.store n).isSome ↔ (σ_outer n).isSome
  | .block _ σ_parent _ inner =>
    (∀ n, (σ_parent n).isSome ↔ (σ_outer n).isSome) ∧ sameDomInv σ_outer inner
  | .seq inner _ => sameDomInv σ_outer inner

/-- `sameDomInv σ_outer c` implies `∀ n, (c.getEnv.store n).isSome ↔ (σ_outer n).isSome`. -/
private theorem sameDomInv_implies_getEnv_iff (σ_outer : SemanticStore Expression) (c : CC)
    (hinv : sameDomInv σ_outer c) :
    ∀ n, (c.getEnv.store n).isSome ↔ (σ_outer n).isSome := by
  match c with
  | .stmt _ _ => exact hinv
  | .stmts _ _ => exact hinv
  | .terminal _ => exact hinv
  | .exiting _ _ => exact hinv
  | .block _ _ _ inner =>
    obtain ⟨_, hinner⟩ := hinv
    exact sameDomInv_implies_getEnv_iff σ_outer inner hinner
  | .seq inner _ =>
    exact sameDomInv_implies_getEnv_iff σ_outer inner hinv

/-! ### Syntactic commands collection

    `Stmt.commands` and `Block.commands` collect all atomic commands appearing
    syntactically in a statement / block tree. Used to state and prove the
    trace-reachability invariant for `stmt_star_preserves_reservedFresh`. -/

mutual
private def Stmt.commandsIn (s : Stmt Expression Command) : List Command :=
  match s with
  | .cmd c => [c]
  | .block _ bss _ => Block.commandsIn bss
  | .ite _ tss ess _ => Block.commandsIn tss ++ Block.commandsIn ess
  | .loop _ _ _ body _ => Block.commandsIn body
  | _ => []

private def Block.commandsIn (ss : Statements) : List Command :=
  match ss with
  | [] => []
  | s :: rest => Stmt.commandsIn s ++ Block.commandsIn rest
end

mutual
/-- **Lemma 2 (syntactic)**, statement-level version: if a command `c` appears
    syntactically in a statement `s`, then `Cmd.definedVars c ⊆ Stmt.definedVars s`. -/
private theorem Stmt.definedVars_of_commandIn (s : Stmt Expression Command) (c : Command) :
    c ∈ Stmt.commandsIn s →
    ∀ x, x ∈ Imperative.HasVarsImp.definedVars c false → x ∈ Stmt.definedVars s false := by
  intro hs x hx
  match s with
  | .cmd c' =>
    simp [Stmt.commandsIn] at hs
    subst hs
    simpa [Stmt.definedVars] using hx
  | .block _ bss _ =>
    simp [Stmt.commandsIn] at hs
    have := Block.definedVars_of_commandIn bss c hs x hx
    simpa [Stmt.definedVars] using this
  | .ite _ tss ess _ =>
    simp [Stmt.commandsIn, List.mem_append] at hs
    rcases hs with htss | hess
    · have := Block.definedVars_of_commandIn tss c htss x hx
      simp [Stmt.definedVars]; exact Or.inl this
    · have := Block.definedVars_of_commandIn ess c hess x hx
      simp [Stmt.definedVars]; exact Or.inr this
  | .loop _ _ _ body _ =>
    simp [Stmt.commandsIn] at hs
    have := Block.definedVars_of_commandIn body c hs x hx
    simpa [Stmt.definedVars] using this
  | .exit _ _ => simp [Stmt.commandsIn] at hs
  | .funcDecl _ _ => simp [Stmt.commandsIn] at hs
  | .typeDecl _ _ => simp [Stmt.commandsIn] at hs

/-- **Lemma 2 (syntactic)**: if a command `c` appears syntactically in block `ss`,
    then `Cmd.definedVars c ⊆ Block.definedVars ss`. -/
private theorem Block.definedVars_of_commandIn (ss : Statements) (c : Command) :
    c ∈ Block.commandsIn ss →
    ∀ x, x ∈ Imperative.HasVarsImp.definedVars c false → x ∈ Block.definedVars ss false := by
  intro hmem x hx
  match ss with
  | [] => simp [Block.commandsIn] at hmem
  | s :: rest =>
    simp only [Block.commandsIn, List.mem_append] at hmem
    rcases hmem with hs | hrest
    · have := Stmt.definedVars_of_commandIn s c hs x hx
      simp [Block.definedVars]; exact Or.inl this
    · have := Block.definedVars_of_commandIn rest c hrest x hx
      simp [Block.definedVars]; exact Or.inr this
end

/-- Collect all commands syntactically present in a config's code structure.
    Does NOT include commands in the env — just the code being executed. -/
private def Config.cmdsIn : CC → List Command
  | .stmt s _ => Stmt.commandsIn s
  | .stmts ss _ => Block.commandsIn ss
  | .terminal _ => []
  | .exiting _ _ => []
  | .block _ _ _ inner => Config.cmdsIn inner
  | .seq inner ss => Config.cmdsIn inner ++ Block.commandsIn ss

/-- Helper: commands in `Block.commandsIn (ss ++ ss')` split as append. -/
private theorem step_cmdsIn_subset
    {a b : CC} (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b) :
    ∀ c, c ∈ Config.cmdsIn b → c ∈ Config.cmdsIn a := by
  induction hstep with
  | step_cmd _ => intro c hc; simp [Config.cmdsIn] at hc
  | step_block => intro c hc; simpa [Config.cmdsIn, Stmt.commandsIn] using hc
  | step_ite_true _ _ =>
    intro c hc
    simp only [Config.cmdsIn, Stmt.commandsIn, List.mem_append]
    exact Or.inl (by simpa [Config.cmdsIn] using hc)
  | step_ite_false _ _ =>
    intro c hc
    simp only [Config.cmdsIn, Stmt.commandsIn, List.mem_append]
    exact Or.inr (by simpa [Config.cmdsIn] using hc)
  | step_ite_nondet_true =>
    intro c hc
    simp only [Config.cmdsIn, Stmt.commandsIn, List.mem_append]
    exact Or.inl (by simpa [Config.cmdsIn] using hc)
  | step_ite_nondet_false =>
    intro c hc
    simp only [Config.cmdsIn, Stmt.commandsIn, List.mem_append]
    exact Or.inr (by simpa [Config.cmdsIn] using hc)
  | step_loop_enter _ _ _ _ _ =>
    intro c hc
    -- b = .seq (.block .none _ (.stmts body _)) [loop]
    -- Config.cmdsIn b = Block.commandsIn body ++ Block.commandsIn [loop]
    --                 = Block.commandsIn body ++ Stmt.commandsIn loop
    --                 = Block.commandsIn body ++ Block.commandsIn body
    -- a = .stmt (.loop ..) ρ, Config.cmdsIn a = Stmt.commandsIn (.loop ..) = Block.commandsIn body
    simp only [Config.cmdsIn, Block.commandsIn, Stmt.commandsIn,
               List.append_nil, List.mem_append] at hc
    simp only [Config.cmdsIn, Stmt.commandsIn]
    rcases hc with h | h
    · exact h
    · exact h
  | step_loop_exit _ _ _ _ => intro c hc; simp [Config.cmdsIn] at hc
  | step_loop_nondet_enter _ _ =>
    intro c hc
    simp only [Config.cmdsIn, Block.commandsIn, Stmt.commandsIn,
               List.append_nil, List.mem_append] at hc
    simp only [Config.cmdsIn, Stmt.commandsIn]
    rcases hc with h | h
    · exact h
    · exact h
  | step_loop_nondet_exit _ _ => intro c hc; simp [Config.cmdsIn] at hc
  | step_exit => intro c hc; simp [Config.cmdsIn] at hc
  | step_funcDecl => intro c hc; simp [Config.cmdsIn] at hc
  | step_typeDecl => intro c hc; simp [Config.cmdsIn] at hc
  | step_stmts_nil => intro c hc; simp [Config.cmdsIn] at hc
  | step_stmts_cons =>
    intro c hc
    simp only [Config.cmdsIn, List.mem_append] at hc
    simp only [Config.cmdsIn, Block.commandsIn, List.mem_append]
    exact hc
  | step_seq_inner _ ih =>
    intro c hc
    simp only [Config.cmdsIn, List.mem_append] at hc
    simp only [Config.cmdsIn, List.mem_append]
    rcases hc with h | h
    · exact Or.inl (ih c h)
    · exact Or.inr h
  | step_seq_done => intro c hc; simpa [Config.cmdsIn] using hc
  | step_seq_exit => intro c hc; simp [Config.cmdsIn] at hc
  | step_block_body _ ih => intro c hc; simp [Config.cmdsIn] at hc ⊢; exact ih c hc
  | step_block_done => intro c hc; simp [Config.cmdsIn] at hc
  | step_block_exit_match _ => intro c hc; simp [Config.cmdsIn] at hc
  | step_block_exit_mismatch _ => intro c hc; simp [Config.cmdsIn] at hc

/-! ### "No new variables" helpers for `stmt_star_preserves_reservedFresh` -/

/-- `UpdateState` preserves the store domain in the reverse direction as well:
    if `σ'` has variable `n` defined, so did `σ`. -/
private theorem updateState_no_new_vars
    {σ σ' : CoreStore} {x : Expression.Ident} {v : Expression.Expr}
    (hup : UpdateState Expression σ x v σ')
    {n : Expression.Ident}
    (hn : (σ' n).isSome) : (σ n).isSome := by
  cases hup with
  | update hold hnew hframe =>
    by_cases heq : x = n
    · subst heq; simp [hold]
    · have : σ' n = σ n := hframe n heq
      simp [this] at hn; exact hn

/-- `UpdateStates` preserves the store domain in the reverse direction. -/
private theorem updateStates_no_new_vars
    {σ σ' : CoreStore} {xs : List Expression.Ident} {vs : List Expression.Expr}
    (hups : UpdateStates σ xs vs σ')
    {n : Expression.Ident}
    (hn : (σ' n).isSome) : (σ n).isSome := by
  induction hups with
  | update_none => exact hn
  | update_some hup _ ih => exact updateState_no_new_vars hup (ih hn)

/-- `EvalCmd` preserves the store domain in the reverse direction, provided the
    command's `definedVars` are already defined in `σ` (which blocks `init` from firing
    for any new variable). -/
private theorem evalCmd_no_new_vars
    {δ : CoreEval} {σ σ' : CoreStore} {c : Cmd Expression} {f : Bool}
    (heval : EvalCmd (P := Expression) δ σ c σ' f)
    (hdef_old : ∀ y ∈ Cmd.definedVars c, (σ y).isSome)
    {n : Expression.Ident}
    (hn : (σ' n).isSome) : (σ n).isSome := by
  cases heval with
  | eval_init _ hinit _ =>
    -- InitState requires σ x = none, but x ∈ Cmd.definedVars (.init x ..) = [x],
    -- so hdef_old gives (σ x).isSome, a contradiction.
    cases hinit with
    | init hnone _ _ =>
      have hx := hdef_old _ (show _ ∈ [_] from List.mem_singleton.mpr rfl)
      rw [hnone] at hx; exact absurd hx (by simp)
  | eval_init_unconstrained hinit _ =>
    cases hinit with
    | init hnone _ _ =>
      have hx := hdef_old _ (show _ ∈ [_] from List.mem_singleton.mpr rfl)
      rw [hnone] at hx; exact absurd hx (by simp)
  | eval_set _ hup _ => exact updateState_no_new_vars hup hn
  | eval_set_nondet hup _ => exact updateState_no_new_vars hup hn
  | eval_assert_pass _ _ => exact hn
  | eval_assert_fail _ _ => exact hn
  | eval_assume _ _ => exact hn
  | eval_cover _ => exact hn

/-- `EvalCommand` preserves the store domain in the reverse direction, provided the
    command's `definedVars` are already defined in `ρ.store`. -/
private theorem evalCommand_no_new_vars
    {ρ : Env Expression} {c : Command} {σ' : CoreStore} {f : Bool}
    (heval : EvalCommand π φ ρ.eval ρ.store c σ' f)
    (hdef_old : ∀ y ∈ Imperative.HasVarsImp.definedVars c false, (ρ.store y).isSome)
    {n : Expression.Ident}
    (hn : (σ' n).isSome) : (ρ.store n).isSome := by
  cases heval with
  | cmd_sem hcmd =>
    apply evalCmd_no_new_vars hcmd ?_ hn
    intro y hy
    apply hdef_old
    show y ∈ Command.definedVars (CmdExt.cmd _)
    simpa [Command.definedVars] using hy
  | call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hups =>
    exact updateStates_no_new_vars hups hn

/-- Single-step "no new vars" lemma under the `outerInv σ_outer` invariant.
    If `σ_outer` already contains all the command-definedVars reachable from the current
    config (as captured by `hdef_safe`), then a step cannot introduce new variables. -/
private theorem step_no_new_vars
    {σ_outer : SemanticStore Expression} {a b : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b)
    (hinv : outerInv σ_outer a)
    (hdef_safe : ∀ c ∈ Config.cmdsIn a, ∀ y ∈ Imperative.HasVarsImp.definedVars c false,
      (σ_outer y).isSome)
    {n : Expression.Ident}
    (hn : (b.getEnv.store n).isSome) : (a.getEnv.store n).isSome := by
  induction hstep with
  | step_cmd heval =>
    -- a = .stmt (.cmd cmd) ρ, b = .terminal { ρ with store := σ'', .. }
    simp only [Config.getEnv] at hn ⊢
    rename_i cmd σ'' f ρ
    have hc_in : cmd ∈ Config.cmdsIn (Config.stmt (Stmt.cmd cmd) ρ) := by
      simp [Config.cmdsIn, Stmt.commandsIn]
    have hdef_local : ∀ y ∈ Imperative.HasVarsImp.definedVars cmd false,
        (ρ.store y).isSome := fun y hy => by
      have hout := hdef_safe cmd hc_in y hy
      simp only [outerInv] at hinv
      exact hinv y hout
    exact evalCommand_no_new_vars (π := π) (φ := φ) heval hdef_local hn
  | step_block => exact hn
  | step_ite_true _ _ => exact hn
  | step_ite_false _ _ => exact hn
  | step_ite_nondet_true => exact hn
  | step_ite_nondet_false => exact hn
  | step_loop_enter _ _ _ _ _ => exact hn
  | step_loop_exit _ _ _ _ => exact hn
  | step_loop_nondet_enter _ _ => exact hn
  | step_loop_nondet_exit _ _ => exact hn
  | step_exit => exact hn
  | step_funcDecl => simpa [Config.getEnv] using hn
  | step_typeDecl => exact hn
  | step_stmts_nil => exact hn
  | step_stmts_cons => exact hn
  | step_seq_inner hstep_inner ih =>
    -- a = .seq inner ss, b = .seq inner' ss
    -- hn : b.getEnv.store n isSome. Need a.getEnv.store n isSome.
    simp only [Config.getEnv] at hn ⊢
    apply ih hinv ?_ hn
    intro c hc y hy
    apply hdef_safe c ?_ y hy
    simp only [Config.cmdsIn, List.mem_append]; exact Or.inl hc
  | step_seq_done => exact hn
  | step_seq_exit => simpa [Config.getEnv] using hn
  | step_block_body _ ih =>
    -- a = .block l σ_parent inner, b = .block l σ_parent inner'
    simp only [Config.getEnv] at hn ⊢
    obtain ⟨_, hinner⟩ := hinv
    apply ih hinner ?_ hn
    intro c hc y hy
    apply hdef_safe c ?_ y hy
    simp only [Config.cmdsIn]; exact hc
  | step_block_done =>
    -- b.store = projectStore σ_parent ρ'.store
    -- a = .block .none σ_parent (.terminal ρ'), a.getEnv.store = σ_parent
    obtain ⟨_, _⟩ := hinv
    simp only [Config.getEnv] at hn ⊢
    simp only [projectStore] at hn
    split at hn
    · assumption
    · simp at hn
  | step_block_exit_match _ =>
    obtain ⟨_, _⟩ := hinv
    simp only [Config.getEnv] at hn ⊢
    simp only [projectStore] at hn
    split at hn
    · assumption
    · simp at hn
  | step_block_exit_mismatch _ =>
    obtain ⟨_, _⟩ := hinv
    simp only [Config.getEnv] at hn ⊢
    simp only [projectStore] at hn
    split at hn
    · assumption
    · simp at hn

/-- Star-step "no new vars" lemma. Follows by iterating `step_no_new_vars`. -/
private theorem star_no_new_vars
    {σ_outer : SemanticStore Expression} {a b : CC}
    (hstar : CoreStar π φ a b)
    (hinv : outerInv σ_outer a)
    (hdef_safe : ∀ c ∈ Config.cmdsIn a, ∀ y ∈ Imperative.HasVarsImp.definedVars c false,
      (σ_outer y).isSome)
    {n : Expression.Ident}
    (hn : (b.getEnv.store n).isSome) : (a.getEnv.store n).isSome := by
  induction hstar with
  | refl => exact hn
  | step _ _ _ hstep _ ih =>
    apply step_no_new_vars (π := π) (φ := φ) hstep hinv hdef_safe
    apply ih (step_preserves_outerInv π φ hstep hinv)
    · intro c hc y hy
      exact hdef_safe c (step_cmdsIn_subset π φ hstep c hc) y hy
    · exact hn

/-- Preservation of an arbitrary "fresh-name" predicate across a single-statement
    trace `.stmt s ρ₀ →* .terminal ρ₁`.  If every var that `s` *defines* (via init
    or funcDecl) is already isSome in `ρ₀`, then no fresh names appear at `ρ₁`, so
    any predicate that holds for all currently-defined names at `ρ₀` continues to
    hold at `ρ₁`.

    Stated generically over a predicate `P` (e.g., "name doesn't have a reserved
    prefix") so this can be used at multiple call sites.  The
    `Stmt.definedVars s ⊆ ρ₀ isSome` precondition is precisely what's needed
    to keep init/funcDecl from firing.  This is a derived form of the
    simulation-level hypothesis (`Stmt.modifiedOrDefinedVars s ⊆ ρ₀ isSome`),
    which is genuinely strong and tied to the architectural-gap pre-`InitEnvWF`
    interface still threaded through `simulation`/`canfail_simulation`. -/
private theorem stmt_star_preserves_reservedFresh
    (s : Stmt Expression Command) (ρ₀ ρ₁ : Env Expression)
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (hswf_def : ∀ n ∈ Stmt.definedVars s false, (ρ₀.store n).isSome)
    {P : Expression.Ident → Prop}
    (hreserved : ∀ n, (ρ₀.store n).isSome → P n) :
    ∀ n, (ρ₁.store n).isSome → P n := by
  intro n hn
  apply hreserved n
  -- Reduce to `(ρ₀.store n).isSome` via star_no_new_vars.
  have hinv₀ : outerInv ρ₀.store (.stmt s ρ₀) := fun _ h => h
  have hdef_safe : ∀ c ∈ Config.cmdsIn (Config.stmt s ρ₀),
      ∀ y ∈ Imperative.HasVarsImp.definedVars c false, (ρ₀.store y).isSome := by
    intro c hc y hy
    apply hswf_def
    simp only [Config.cmdsIn] at hc
    exact Stmt.definedVars_of_commandIn s c hc y hy
  have := star_no_new_vars (π := π) (φ := φ) hstar hinv₀ hdef_safe (n := n)
  simp only [Config.getEnv] at this
  exact this hn

/-! ### Single step preserves store outside touched vars

    The unrestricted version (`c₂.getEnv.store x = c₁.getEnv.store x` assuming only
    `x ∉ Config.touchedVarsSet c₁`) is NOT provable after the `projectStore` semantics
    change: on block-exit steps the projection can silently drop variables that were
    defined inside the block. We instead provide a version strengthened with an
    `outerInv σ_outer c₁` hypothesis plus `(σ_outer x).isSome`, under which all block
    cases hold via `projectStore_isSome`. -/

/-! ### Step monotonicity: touched vars of c₂ ⊆ touched vars of c₁ -/

private theorem step_touchedVars_subset
    (c₁ c₂ : CC)
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂) :
    ∀ x, x ∈ Config.touchedVarsSet c₂ → x ∈ Config.touchedVarsSet c₁ := by
  intro x hx
  induction hstep with
  | step_cmd _ => simp [Config.touchedVarsSet] at hx
  | step_block =>
    -- c₁ = .stmt (.block l ss md) ρ, c₂ = .block (.some l) (.stmts ss ρ)
    -- touchedVarsSet c₁ = Stmt.modifiedVars (.block l ss md) ++ Stmt.definedVars (.block l ss md)
    --                    = Block.modifiedVars ss ++ Block.definedVars ss
    -- touchedVarsSet c₂ = Config.touchedVarsSet (.stmts ss ρ)
    --                    = Block.modifiedVars ss ++ Block.definedVars ss
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte] at hx ⊢
    exact hx
  | step_ite_true _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at hx ⊢
    rcases hx with h | h
    · left; left; exact h
    · right; left; exact h
  | step_ite_false _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at hx ⊢
    rcases hx with h | h
    · left; right; exact h
    · right; right; exact h
  | step_ite_nondet_true =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at hx ⊢
    rcases hx with h | h
    · left; left; exact h
    · right; left; exact h
  | step_ite_nondet_false =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at hx ⊢
    rcases hx with h | h
    · left; right; exact h
    · right; right; exact h
  | step_loop_enter _ _ _ _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
               Bool.false_eq_true, ↓reduceIte, Block.modifiedVars, Block.definedVars,
               List.append_nil, List.mem_append] at hx ⊢
    rcases hx with ((h | h) | h) | h
    · exact .inl h
    · exact .inr h
    · exact .inl h
    · exact .inr h
  | step_loop_exit _ _ _ _ => simp [Config.touchedVarsSet] at hx
  | step_loop_nondet_enter _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
               Bool.false_eq_true, ↓reduceIte, Block.modifiedVars, Block.definedVars,
               List.append_nil, List.mem_append] at hx ⊢
    rcases hx with ((h | h) | h) | h
    · exact .inl h
    · exact .inr h
    · exact .inl h
    · exact .inr h
  | step_loop_nondet_exit _ _ => simp [Config.touchedVarsSet] at hx
  | step_exit => simp [Config.touchedVarsSet] at hx
  | step_funcDecl => simp [Config.touchedVarsSet] at hx
  | step_typeDecl => simp [Config.touchedVarsSet] at hx
  | step_stmts_nil => simp [Config.touchedVarsSet] at hx
  | step_stmts_cons =>
    -- c₁ = .stmts (s :: ss) ρ, c₂ = .seq (.stmt s ρ) ss
    -- touchedVarsSet c₁ = Block.modifiedVars (s :: ss) ++ Block.definedVars (s :: ss)
    --   = (Stmt.modifiedVars s ++ Block.modifiedVars ss) ++ (Stmt.definedVars s ++ Block.definedVars ss)
    -- touchedVarsSet c₂ = touchedVarsSet (.stmt s ρ) ++ Block.modifiedVars ss ++ Block.definedVars ss
    --   = (Stmt.modifiedVars s ++ Stmt.definedVars s) ++ Block.modifiedVars ss ++ Block.definedVars ss
    simp only [Config.touchedVarsSet, Block.modifiedVars, Block.definedVars, List.mem_append] at hx ⊢
    -- Both contain exactly Stmt.modifiedVars s, Stmt.definedVars s, Block.modifiedVars ss, Block.definedVars ss
    rcases hx with ((h | h) | h) | h
    · left; left; exact h
    · right; left; exact h
    · left; right; exact h
    · right; right; exact h
  | step_seq_inner _ ih =>
    -- c₂ = .seq inner' ss, c₁ = .seq inner ss
    -- touchedVarsSet = touchedVarsSet inner_x ++ Block.modifiedVars ss ++ Block.definedVars ss
    -- x is in c₂'s touched vars. Show it's in c₁'s touched vars.
    -- Strategy: if x is in inner' part, use ih. Otherwise pass through.
    simp only [Config.touchedVarsSet] at hx ⊢
    -- hx : x ∈ (Config.touchedVarsSet inner' ++ Block.modifiedVars ss ++ Block.definedVars ss)
    -- goal : x ∈ (Config.touchedVarsSet inner ++ Block.modifiedVars ss ++ Block.definedVars ss)
    have hmem := List.mem_append.mp hx
    cases hmem with
    | inl h =>
      have hmem2 := List.mem_append.mp h
      cases hmem2 with
      | inl h2 =>
        exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (ih h2))))
      | inr h2 =>
        exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h2)))
    | inr h =>
      exact List.mem_append.mpr (.inr h)
  | step_seq_done =>
    simp only [Config.touchedVarsSet, List.mem_append, List.not_mem_nil, false_or] at hx ⊢
    exact hx
  | step_seq_exit =>
    simp [Config.touchedVarsSet] at hx
  | step_block_body _ ih =>
    simp only [Config.touchedVarsSet] at hx ⊢
    exact ih hx
  | step_block_done => simp [Config.touchedVarsSet] at hx
  | step_block_exit_match _ => simp [Config.touchedVarsSet] at hx
  | step_block_exit_mismatch _ => simp [Config.touchedVarsSet] at hx

/-! ### Multi-step store preservation (isNone-preservation, no outerInv needed)

For the `BlockInitEnvWF.toBlock_tail_post` derivation we need to argue that
variables that are `isNone` at `ρ₀` and outside `touchedVarsSet` of the trace
remain `isNone` at `ρ₁`.  This is *one-directional* and doesn't require any
`outerInv` hypothesis (block-exit's `projectStore` produces `none` for both
input branches when the var is `isNone`). -/

/-- Single-step store frame for variables that are `isNone` at `c₁` and outside
    `c₁`'s touched vars: the store at `x` stays the same after a single step. -/
private theorem step_preserves_store_outside_touchedVars_isNone
    {c₁ c₂ : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂)
    (x : Expression.Ident)
    (hnone : (c₁.getEnv.store x).isNone)
    (hx : x ∉ Config.touchedVarsSet c₁) :
    c₂.getEnv.store x = c₁.getEnv.store x := by
  induction hstep with
  | step_cmd heval =>
    have hmod : x ∉ Stmt.modifiedVars (Stmt.cmd ‹Command›) :=
      fun hmem => hx (show x ∈ Config.touchedVarsSet _ by
        simp only [Config.touchedVarsSet]; exact List.mem_append_left _ hmem)
    have hdef : x ∉ Stmt.definedVars (Stmt.cmd ‹Command›) false :=
      fun hmem => hx (show x ∈ Config.touchedVarsSet _ by
        simp only [Config.touchedVarsSet]; exact List.mem_append_right _ hmem)
    exact evalCommand_store_frame_stmt (π := π) (φ := φ) heval hmod hdef
  | step_block => rfl
  | step_ite_true _ _ => rfl
  | step_ite_false _ _ => rfl
  | step_ite_nondet_true => rfl
  | step_ite_nondet_false => rfl
  | step_loop_enter _ _ _ _ _ => rfl
  | step_loop_exit _ _ _ _ => rfl
  | step_loop_nondet_enter _ _ => rfl
  | step_loop_nondet_exit _ _ => rfl
  | step_exit => rfl
  | step_funcDecl => simp [Config.getEnv]
  | step_typeDecl => rfl
  | step_stmts_nil => rfl
  | step_stmts_cons => rfl
  | step_seq_inner _ ih =>
    exact ih hnone (fun hmem => hx (by
      simp only [Config.touchedVarsSet, List.mem_append]
      left; left; exact hmem))
  | step_seq_done => rfl
  | step_seq_exit => rfl
  | step_block_body _ ih =>
    simp only [Config.getEnv, Config.touchedVarsSet] at hnone hx ⊢
    exact ih hnone hx
  | step_block_done =>
    -- c₁ = .block l σ_parent (.terminal ρ'), c₁.store x = ρ'.store x.
    -- c₂.store x = projectStore σ_parent ρ'.store x.  Since (ρ'.store x).isNone
    -- (= hnone), both branches of projectStore give `none`.
    simp only [Config.getEnv] at hnone ⊢
    simp only [projectStore]
    have hρ'_none : ‹Env Expression›.store x = none :=
      Option.isNone_iff_eq_none.mp hnone
    rw [hρ'_none]; split <;> rfl
  | step_block_exit_match _ =>
    simp only [Config.getEnv] at hnone ⊢
    simp only [projectStore]
    have hρ'_none : ‹Env Expression›.store x = none :=
      Option.isNone_iff_eq_none.mp hnone
    rw [hρ'_none]; split <;> rfl
  | step_block_exit_mismatch _ =>
    simp only [Config.getEnv] at hnone ⊢
    simp only [projectStore]
    have hρ'_none : ‹Env Expression›.store x = none :=
      Option.isNone_iff_eq_none.mp hnone
    rw [hρ'_none]; split <;> rfl

/-- Star version of `step_preserves_store_outside_touchedVars_isNone`. -/
private theorem star_preserves_store_outside_touchedVars_isNone
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (x : Expression.Ident)
    (hnone : (c₁.getEnv.store x).isNone)
    (hx : x ∉ Config.touchedVarsSet c₁) :
    c₂.getEnv.store x = c₁.getEnv.store x := by
  induction hstar with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have hx_mid : x ∉ Config.touchedVarsSet mid :=
      fun hmem => hx (step_touchedVars_subset π φ _ _ hstep x hmem)
    have hframe := step_preserves_store_outside_touchedVars_isNone
      (π := π) (φ := φ) hstep x hnone hx
    have hnone_mid : (mid.getEnv.store x).isNone := by
      rw [hframe]; exact hnone
    rw [ih hnone_mid hx_mid, hframe]

/-- Single-step value preservation for isSome variables outside touchedVarsSet.
    When `(σ₀ x).isSome` and `x ∉ Config.touchedVarsSet c₁` and
    the outer-inv holds (so block parents have x isSome), the value is preserved. -/
private theorem step_preserves_store_outside_touchedVars_isSome
    {σ₀ : SemanticStore Expression} {c₁ c₂ : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂)
    (x : Expression.Ident)
    (hsome₀ : (σ₀ x).isSome)
    (hx : x ∉ Config.touchedVarsSet c₁)
    (hinv : outerInv σ₀ c₁) :
    c₂.getEnv.store x = c₁.getEnv.store x := by
  induction hstep with
  | step_cmd heval =>
    have hmod : x ∉ Stmt.modifiedVars (Stmt.cmd ‹Command›) :=
      fun hmem => hx (show x ∈ Config.touchedVarsSet _ by
        simp only [Config.touchedVarsSet]; exact List.mem_append_left _ hmem)
    have hdef : x ∉ Stmt.definedVars (Stmt.cmd ‹Command›) false :=
      fun hmem => hx (show x ∈ Config.touchedVarsSet _ by
        simp only [Config.touchedVarsSet]; exact List.mem_append_right _ hmem)
    exact evalCommand_store_frame_stmt (π := π) (φ := φ) heval hmod hdef
  | step_block => rfl
  | step_ite_true _ _ => rfl
  | step_ite_false _ _ => rfl
  | step_ite_nondet_true => rfl
  | step_ite_nondet_false => rfl
  | step_loop_enter _ _ _ _ _ => rfl
  | step_loop_exit _ _ _ _ => rfl
  | step_loop_nondet_enter _ _ => rfl
  | step_loop_nondet_exit _ _ => rfl
  | step_exit => rfl
  | step_funcDecl => simp [Config.getEnv]
  | step_typeDecl => rfl
  | step_stmts_nil => rfl
  | step_stmts_cons => rfl
  | step_seq_inner _ ih =>
    exact ih (fun hmem => hx (by
      simp only [Config.touchedVarsSet, List.mem_append]
      left; left; exact hmem)) hinv
  | step_seq_done => rfl
  | step_seq_exit => rfl
  | step_block_body _ ih =>
    simp only [Config.getEnv, Config.touchedVarsSet] at hx ⊢
    obtain ⟨_, hinner⟩ := hinv
    exact ih hx hinner
  | step_block_done =>
    simp only [Config.getEnv] at hinv ⊢
    obtain ⟨hpar, _⟩ := hinv
    simp only [projectStore]
    rw [if_pos (hpar x hsome₀)]
  | step_block_exit_match _ =>
    simp only [Config.getEnv] at hinv ⊢
    obtain ⟨hpar, _⟩ := hinv
    simp only [projectStore]
    rw [if_pos (hpar x hsome₀)]
  | step_block_exit_mismatch _ =>
    simp only [Config.getEnv] at hinv ⊢
    obtain ⟨hpar, _⟩ := hinv
    simp only [projectStore]
    rw [if_pos (hpar x hsome₀)]

/-- Star version: value preservation for isSome variables outside touchedVarsSet. -/
private theorem star_preserves_store_outside_touchedVars_isSome
    {σ₀ : SemanticStore Expression} {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (x : Expression.Ident)
    (hsome₀ : (σ₀ x).isSome)
    (hx : x ∉ Config.touchedVarsSet c₁)
    (hinv : outerInv σ₀ c₁) :
    c₂.getEnv.store x = c₁.getEnv.store x := by
  induction hstar with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have hx_mid : x ∉ Config.touchedVarsSet mid :=
      fun hmem => hx (step_touchedVars_subset π φ _ _ hstep x hmem)
    have hframe := step_preserves_store_outside_touchedVars_isSome
      (π := π) (φ := φ) hstep x hsome₀ hx hinv
    have hinv_mid : outerInv σ₀ mid := step_preserves_outerInv π φ hstep hinv
    rw [ih hx_mid hinv_mid, hframe]

/-! ## Composing statement traces -/

/-- Statement list prefix terminates at ρ₁, suffix terminates at ρ₂ →
    concatenation terminates at ρ₂. -/
private theorem stmts_concat_terminal
    (ss₁ ss₂ : Statements) (ρ₀ ρ₁ ρ₂ : Env Expression)
    (h₁ : CoreStar π φ (.stmts ss₁ ρ₀) (.terminal ρ₁))
    (h₂ : CoreStar π φ (.stmts ss₂ ρ₁) (.terminal ρ₂)) :
    CoreStar π φ (.stmts (ss₁ ++ ss₂) ρ₀) (.terminal ρ₂) :=
  ReflTrans_Transitive _ _ _ _
    (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ) ss₁ ss₂ ρ₀ ρ₁ h₁)
    h₂

/-- If a prefix of a statement list reaches `.exiting`, then the prefix
    concatenated with any suffix also reaches `.exiting` (the suffix is
    never touched). -/
private theorem stmts_prefix_exiting_append
    (ss₁ ss₂ : Statements) (ρ₀ ρ' : Env Expression) (lbl : String)
    (h : CoreStar π φ (.stmts ss₁ ρ₀) (.exiting lbl ρ')) :
    CoreStar π φ (.stmts (ss₁ ++ ss₂) ρ₀) (.exiting lbl ρ') := by
  induction ss₁ generalizing ρ₀ with
  | nil =>
    -- .stmts [] ρ₀ steps to .terminal ρ₀; cannot reach .exiting
    cases h with
    | step _ _ _ h1 _ => cases h1 with | step_stmts_nil => rename_i h2; cases h2 with
      | step _ _ _ h3 _ => exact nomatch h3
  | cons s rest ih =>
    -- .stmts (s :: rest) ρ₀ → .seq (.stmt s ρ₀) rest
    -- .stmts (s :: (rest ++ ss₂)) ρ₀ → .seq (.stmt s ρ₀) (rest ++ ss₂)
    cases h with
    | step _ _ _ h1 hrest => cases h1 with
      | step_stmts_cons =>
        match seq_reaches_exiting (P := Expression)
          (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) hrest with
        | .inl hexit_s =>
          -- s exits: .stmts (s :: rest ++ ss₂) ρ₀ exits via stmts_cons_exiting
          exact stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) s (rest ++ ss₂) lbl ρ₀ ρ' hexit_s
        | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
          -- s terminates at ρ₁, rest exits: by IH, rest ++ ss₂ exits
          exact ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
              s (rest ++ ss₂) ρ₀ ρ₁ hterm_s)
            (ih ρ₁ hexit_rest)

/-! ## Block-none decomposition and hcov-free stmts decomposition -/

/-- Decompose `.block .none inner` reaching terminal in `ReflTransT`:
    the inner reached `.terminal ρ_inner`.  (Under the new semantics where
    `.exiting .none` is unreachable, the previous "break" disjunct is empty.) -/
private theorem blockT_none_reaches_terminal
    {inner : CC} {σ_parent : SemanticStore Expression}
    {e_parent : SemanticEval Expression} {ρ' : Env Expression}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.block .none σ_parent e_parent inner) (.terminal ρ')) :
    ∃ ρ_inner,
    (∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.terminal ρ_inner)), h.len < hstar.len) ∧
    ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } := by
  match hstar with
  | .step _ (.block _ _ _ inner₁) _ (.step_block_body h) hrest =>
    have ⟨ρ_inner, ⟨hh, hlen⟩, heq⟩ := blockT_none_reaches_terminal hrest
    exact ⟨ρ_inner, ⟨.step _ _ _ h hh, by simp [ReflTransT.len]; omega⟩, heq⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .refl _ => exact ⟨_, ⟨.refl _, by simp [ReflTransT.len]⟩, rfl⟩
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match heq) _ => cases heq
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h
  termination_by hstar.len

/-- If `.block .none inner` reaches `.exiting l ρ'` in `ReflTransT`,
    the inner reaches `.exiting l ρ_inner` with strictly shorter trace,
    and `ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent }`. -/
private theorem blockT_none_reaches_exiting_some
    {inner : CC} {σ_parent : SemanticStore Expression}
    {e_parent : SemanticEval Expression} {l : String} {ρ' : Env Expression}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.block .none σ_parent e_parent inner) (.exiting l ρ')) :
    ∃ (ρ_inner : Env Expression),
      ∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.exiting l ρ_inner)),
      h.len < hstar.len ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } := by
  match hstar with
  | .step _ (.block _ _ _ inner₁) _ (.step_block_body h) hrest =>
    have ⟨ρ_inner, hh, hlen, heq⟩ := blockT_none_reaches_exiting_some hrest
    exact ⟨ρ_inner, .step _ _ _ h hh, by simp [ReflTransT.len]; omega, heq⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match heq) _ => cases heq
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .refl _ => exact ⟨_, .refl _, by simp [ReflTransT.len], rfl⟩
    | .step _ _ _ h _ => exact nomatch h
  termination_by hstar.len

/-- Invert a `.seq` execution reaching `.exiting` in `ReflTransT`:
    either the inner exited (with length bound), or the inner terminated
    and the tail stmts exited (with combined length bound). -/
private theorem seqT_reaches_exiting
    {inner : CC} {ss : Statements} {lbl : String} {ρ' : Env Expression}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.seq inner ss) (.exiting lbl ρ')) :
    (∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.exiting lbl ρ')), h.len < hstar.len) ∨
    (∃ (ρ₁ : Env Expression),
      ∃ (h1 : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmts ss ρ₁) (.exiting lbl ρ')),
        h1.len + h2.len < hstar.len) := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    match seqT_reaches_exiting hrest with
    | .inl ⟨h_inner, hlen⟩ =>
      exact .inl ⟨.step _ _ _ h h_inner, by simp [ReflTransT.len]; omega⟩
    | .inr ⟨ρ₁, h1, h2, hlen⟩ =>
      exact .inr ⟨ρ₁, .step _ _ _ h h1, h2, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact .inr ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    exact .inl ⟨hrest, by simp [ReflTransT.len]⟩

/-- When a block body has no function declarations and reaches `.exiting`,
    the evaluator is preserved. -/
private theorem block_none_reaches_exiting_some
    {inner : CC} {σ_parent : SemanticStore Expression}
    {e_parent : SemanticEval Expression} {l : String} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block .none σ_parent e_parent inner) (.exiting l ρ')) :
    ∃ (ρ_inner : Env Expression),
      CoreStar π φ inner (.exiting l ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ inner σ_parent e_parent l ρ',
        src = .block (none : Option String) σ_parent e_parent inner → tgt = .exiting l ρ' →
      ∃ (ρ_inner : Env Expression),
        CoreStar π φ inner (.exiting l ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } from
    this _ _ hstar _ _ _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner σ_parent e_parent l ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      have ⟨ρ_inner, hexit, hproj⟩ := ih _ _ _ _ _ rfl htgt
      exact ⟨ρ_inner, .step _ _ _ h hexit, hproj⟩
    | step_block_done =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_match heq => cases heq
    | step_block_exit_mismatch hne =>
      subst htgt
      cases hrest with
      | refl => exact ⟨_, .refl _, rfl⟩
      | step _ _ _ h _ => cases h


private theorem blockOk_cons_left {σ : LoopElimState} {s : Statement} {ss : Statements}
    (h : blockOk σ (s :: ss)) : stmtOk σ s := by
  simp only [blockOk, blockRun, stmtOk, stmtRun, Block.removeLoopsM, StateT.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Stmt.removeLoopsM s σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v => simp
  | error e => exact Bool.noConfusion h

private theorem blockOk_cons_right {σ : LoopElimState} {s : Statement} {ss : Statements}
    (h : blockOk σ (s :: ss)) : blockOk (stmtPostState σ s) ss := by
  simp only [blockOk, blockRun, stmtPostState, stmtRun, Block.removeLoopsM, StateT.run,
    ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Stmt.removeLoopsM s σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v =>
    simp only [StateT.bind, ExceptT.bindCont, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h
    generalize hq2 : Block.removeLoopsM ss snd_st = r2 at h ⊢
    obtain ⟨fst_res2, snd_st2⟩ := r2
    cases fst_res2 with
    | ok v2 => simp
    | error e2 => exact Bool.noConfusion h
  | error e =>
    simp only [pure, StateT.pure, Prod.fst] at h
    exact Bool.noConfusion h

private theorem stmtOk_block_inner {σ : LoopElimState} {l : String}
    {bss : Statements} {md : MetaData Expression}
    (h : stmtOk σ (.block l bss md)) : blockOk σ bss := by
  simp only [stmtOk, stmtRun, blockOk, blockRun, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent, StateT.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Functor.map, liftM, monadLift, MonadLift.monadLift,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Block.removeLoopsM bss σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v => simp
  | error e => exact Bool.noConfusion h

private theorem stmtOk_ite_left {σ : LoopElimState} {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression}
    (h : stmtOk σ (.ite c tss ess md)) : blockOk σ tss := by
  simp only [stmtOk, stmtRun, blockOk, blockRun, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent, StateT.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Functor.map, liftM, monadLift, MonadLift.monadLift,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Block.removeLoopsM tss σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v => simp
  | error e => exact Bool.noConfusion h

private theorem stmtOk_ite_right {σ : LoopElimState} {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression}
    (h : stmtOk σ (.ite c tss ess md)) : blockOk (blockPostState σ tss) ess := by
  simp only [stmtOk, stmtRun, blockOk, blockRun, blockPostState, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent, StateT.run,
    ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Functor.map, liftM, monadLift, MonadLift.monadLift,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Block.removeLoopsM tss σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v =>
    simp only [StateT.bind, ExceptT.bindCont, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h
    generalize hq2 : Block.removeLoopsM ess snd_st = r2 at h ⊢
    obtain ⟨fst_res2, snd_st2⟩ := r2
    cases fst_res2 with
    | ok v2 => simp
    | error e2 => exact Bool.noConfusion h
  | error e => nomatch h

/-! ## InitEnvWF derivations for sub-statements

Helpers to extract `BlockInitEnvWF`/`InitEnvWF` of sub-pieces from a parent
`InitEnvWF`/`BlockInitEnvWF`. These power the recursive calls in
`simulation`/`canfail_simulation`. -/

/-! ### `defUseWellFormed` projection helpers -/

/-- Extensional congruence for blocks. -/
private theorem defUseWellFormed_block_congr {outer₁ outer₂ : Expression.Ident → Bool}
    (heq : ∀ n, outer₁ n = outer₂ n) (bss : Statements) :
    Block.defUseWellFormed outer₁ bss = Block.defUseWellFormed outer₂ bss := by
  have hf : outer₁ = outer₂ := funext heq
  rw [hf]




/-- Project `Stmt.defUseWellFormed outer (.block l bss md) = Block.defUseWellFormed outer bss`. -/
private theorem defUseWellFormed_block (outer : Expression.Ident → Bool) (l : String)
    (bss : Statements) (md : MetaData Expression) :
    Stmt.defUseWellFormed outer (.block l bss md) = Block.defUseWellFormed outer bss := by
  unfold Stmt.defUseWellFormed; rfl

/-- From a true `defUseWellFormed` for an `.ite`, project both branches. -/
private theorem defUseWellFormed_ite_branches {outer : Expression.Ident → Bool}
    {c : ExprOrNondet Expression} {tss ess : Statements} {md : MetaData Expression}
    (h : Stmt.defUseWellFormed outer (.ite c tss ess md) = Bool.true) :
    Block.defUseWellFormed outer tss = Bool.true ∧
    Block.defUseWellFormed outer ess = Bool.true := by
  unfold Stmt.defUseWellFormed at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

/-- From a true `defUseWellFormed` on `s :: ss`, project the head and tail
    (with the tail seen against an extended outer scope). -/
private theorem defUseWellFormed_cons {outer : Expression.Ident → Bool}
    {s : Statement} {ss : Statements}
    (h : Block.defUseWellFormed outer (s :: ss) = Bool.true) :
    Stmt.defUseWellFormed outer s = Bool.true ∧
    Block.defUseWellFormed (fun n => outer n || decide (n ∈ Stmt.definedVars s true)) ss = Bool.true := by
  unfold Block.defUseWellFormed at h
  simp only [Bool.and_eq_true] at h
  exact h

/-- Build a `Block.defUseWellFormed` from a stmt and a tail well-formedness
    against an extended outer scope. -/
private theorem defUseWellFormed_cons_intro {outer : Expression.Ident → Bool}
    {s : Statement} {ss : Statements}
    (h_s : Stmt.defUseWellFormed outer s = Bool.true)
    (h_ss : Block.defUseWellFormed (fun n => outer n || decide (n ∈ Stmt.definedVars s true)) ss = Bool.true) :
    Block.defUseWellFormed outer (s :: ss) = Bool.true := by
  unfold Block.defUseWellFormed
  simp only [Bool.and_eq_true]; exact ⟨h_s, h_ss⟩

/-- Monotonicity-with-freshness for `defUseWellFormed`: extending `outer` by a
    set of fresh names that don't appear in the statement's `touchedVars` ∪
    `definedVars` preserves `defUseWellFormed`.

    Concretely: if the statement is well-formed against `outer`, and a predicate
    `extra` characterizes a set of names disjoint from the statement's vars,
    then the statement is also well-formed against `(fun n => outer n || extra n)`. -/
private theorem defUseWellFormed_outer_extend_aux (sz : Nat) :
    (∀ (outer extra : Expression.Ident → Bool) (s : Statement),
      Stmt.sizeOf s ≤ sz →
      Stmt.defUseWellFormed outer s = Bool.true →
      (∀ n, extra n = Bool.true →
        n ∉ Stmt.modifiedVars s ∧ n ∉ Stmt.getVars s ∧
        n ∉ Stmt.definedVars s false ∧ n ∉ Stmt.funcDeclNames s) →
      Stmt.defUseWellFormed (fun n => outer n || extra n) s = Bool.true) ∧
    (∀ (outer extra : Expression.Ident → Bool) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.defUseWellFormed outer bss = Bool.true →
      (∀ n, extra n = Bool.true →
        n ∉ Block.modifiedVars bss ∧ n ∉ Block.getVars bss ∧
        n ∉ Block.definedVars bss false ∧ n ∉ Block.funcDeclNames bss) →
      Block.defUseWellFormed (fun n => outer n || extra n) bss = Bool.true) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro outer extra s hsz; cases s <;> simp [Stmt.sizeOf] at hsz
    · intro outer extra bss hsz hwf hext
      match bss with
      | [] => simp [Block.defUseWellFormed]
      | s :: rest => simp [Block.sizeOf] at hsz
  | succ k ih =>
    obtain ⟨ih_stmt, ih_block⟩ := ih
    refine ⟨?_, ?_⟩
    · -- Stmt case
      intro outer extra s hsz hwf hext
      match s with
      | .cmd c =>
        unfold Stmt.defUseWellFormed at hwf ⊢
        simp only [Bool.and_eq_true] at hwf ⊢
        obtain ⟨⟨hgv, hmv⟩, hdef⟩ := hwf
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [List.all_eq_true] at hgv ⊢
          intro n hn
          simp only [Bool.or_eq_true]
          exact .inl (hgv n hn)
        · rw [List.all_eq_true] at hmv ⊢
          intro n hn
          simp only [Bool.or_eq_true]
          exact .inl (hmv n hn)
        · rw [List.all_eq_true] at hdef ⊢
          intro n hn
          have hd := hdef n hn
          simp only [decide_eq_true_eq] at hd ⊢
          intro hcontra
          rw [Bool.or_eq_true] at hcontra
          rcases hcontra with h | h
          · exact hd h
          · exact (hext n h).2.2.1 (by
              simp only [Stmt.definedVars, HasVarsImp.definedVars] at hn
              simp only [Stmt.definedVars, HasVarsImp.definedVars]; exact hn)
      | .block l bss md =>
        unfold Stmt.defUseWellFormed at hwf ⊢
        have hsz_bss : Block.sizeOf bss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hext_bss : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars bss ∧ n ∉ Block.getVars bss ∧
            n ∉ Block.definedVars bss false ∧ n ∉ Block.funcDeclNames bss := by
          intro n hn
          have ⟨hm, hg, hd, hfd⟩ := hext n hn
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [Stmt.modifiedVars] using hm
          · simpa [Stmt.getVars] using hg
          · simpa [Stmt.definedVars] using hd
          · simpa [Stmt.funcDeclNames] using hfd
        exact ih_block outer extra bss hsz_bss hwf hext_bss
      | .ite cond tbss ebss md =>
        unfold Stmt.defUseWellFormed at hwf ⊢
        simp only [Bool.and_eq_true] at hwf ⊢
        obtain ⟨⟨hcond_all, htbss⟩, hebss⟩ := hwf
        rw [List.all_eq_true] at hcond_all
        have hsz_t : Block.sizeOf tbss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_e : Block.sizeOf ebss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hext_t : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars tbss ∧ n ∉ Block.getVars tbss ∧
            n ∉ Block.definedVars tbss false ∧ n ∉ Block.funcDeclNames tbss := by
          intro n hn
          have ⟨hm, hg, hd, hfd⟩ := hext n hn
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro hh; exact hm (by
              simp only [Stmt.modifiedVars, List.mem_append]; exact .inl hh)
          · intro hh; exact hg (by
              simp only [Stmt.getVars, List.mem_append]; exact .inl (.inr hh))
          · intro hh; exact hd (by
              simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]
              exact .inl hh)
          · intro hh; exact hfd (by
              simp only [Stmt.funcDeclNames, List.mem_append]; exact .inl hh)
        have hext_e : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars ebss ∧ n ∉ Block.getVars ebss ∧
            n ∉ Block.definedVars ebss false ∧ n ∉ Block.funcDeclNames ebss := by
          intro n hn
          have ⟨hm, hg, hd, hfd⟩ := hext n hn
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro hh; exact hm (by
              simp only [Stmt.modifiedVars, List.mem_append]; exact .inr hh)
          · intro hh; exact hg (by
              simp only [Stmt.getVars, List.mem_append]; exact .inr hh)
          · intro hh; exact hd (by
              simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]
              exact .inr hh)
          · intro hh; exact hfd (by
              simp only [Stmt.funcDeclNames, List.mem_append]; exact .inr hh)
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [List.all_eq_true]
          intro n hn; simp only [Bool.or_eq_true]; exact .inl (hcond_all n hn)
        · exact ih_block outer extra tbss hsz_t htbss hext_t
        · exact ih_block outer extra ebss hsz_e hebss hext_e
      | .loop guard measure inv body md =>
        unfold Stmt.defUseWellFormed at hwf ⊢
        simp only [Bool.and_eq_true] at hwf ⊢
        obtain ⟨⟨⟨hguard_all, hmeas_all⟩, hinv_all⟩, hbody⟩ := hwf
        rw [List.all_eq_true] at hguard_all hmeas_all hinv_all
        have hsz_body : Block.sizeOf body ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hext_body : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars body ∧ n ∉ Block.getVars body ∧
            n ∉ Block.definedVars body false ∧ n ∉ Block.funcDeclNames body := by
          intro n hn
          have ⟨hm, hg, hd, hfd⟩ := hext n hn
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [Stmt.modifiedVars] using hm
          · intro hh; exact hg (by
              simp only [Stmt.getVars, List.mem_append]; exact .inr hh)
          · simpa [Stmt.definedVars] using hd
          · simpa [Stmt.funcDeclNames] using hfd
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · rw [List.all_eq_true]
          intro n hn; simp only [Bool.or_eq_true]; exact .inl (hguard_all n hn)
        · rw [List.all_eq_true]
          intro n hn; simp only [Bool.or_eq_true]; exact .inl (hmeas_all n hn)
        · rw [List.all_eq_true]
          intro n hn; simp only [Bool.or_eq_true]; exact .inl (hinv_all n hn)
        · exact ih_block outer extra body hsz_body hbody hext_body
      | .exit l md => simp [Stmt.defUseWellFormed]
      | .funcDecl decl md =>
        -- The funcDecl case checks (a) the body's free vars are in `definedVars`
        -- (preserved under `outer || extra` by `Or`), and (b) `decl.name` is not
        -- in `definedVars`.  For (b), we know `decl.name` is in `funcDeclNames`,
        -- so `extra decl.name = false` by the strengthened `hext`.
        unfold Stmt.defUseWellFormed at hwf ⊢
        simp only [Bool.and_eq_true] at hwf ⊢
        obtain ⟨hgv, hname⟩ := hwf
        refine ⟨?_, ?_⟩
        · rw [List.all_eq_true] at hgv ⊢
          intro n hn; simp only [Bool.or_eq_true]; exact .inl (hgv n hn)
        · have h_ext_false : extra decl.name = Bool.false := by
            cases hh : extra decl.name with
            | false => rfl
            | true =>
              exfalso
              have hfd : decl.name ∈ Stmt.funcDeclNames (Stmt.funcDecl decl md : Statement) := by
                simp [Stmt.funcDeclNames]
              exact (hext decl.name hh).2.2.2 hfd
          have h_outer_false : outer decl.name = Bool.false := by
            simpa [Bool.not_eq_true'] using hname
          simp [h_ext_false, h_outer_false]
      | .typeDecl tc md => simp [Stmt.defUseWellFormed]
    · -- Block case
      intro outer extra bss hsz hwf hext
      match bss with
      | [] => simp [Block.defUseWellFormed]
      | s :: rest =>
        unfold Block.defUseWellFormed at hwf ⊢
        simp only [Bool.and_eq_true] at hwf ⊢
        obtain ⟨hwf_s, hwf_rest⟩ := hwf
        have hsz_s : Stmt.sizeOf s ≤ k := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ k := by simp [Block.sizeOf] at hsz; omega
        have hext_s : ∀ n, extra n = Bool.true →
            n ∉ Stmt.modifiedVars s ∧ n ∉ Stmt.getVars s ∧
            n ∉ Stmt.definedVars s false ∧ n ∉ Stmt.funcDeclNames s := by
          intro n hn
          have ⟨hm, hg, hd, hfd⟩ := hext n hn
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro hh; exact hm (by
              simp only [Block.modifiedVars, List.mem_append]; exact .inl hh)
          · intro hh; exact hg (by
              simp only [Block.getVars, List.mem_append]; exact .inl hh)
          · intro hh; exact hd (by
              simp only [Block.definedVars, List.mem_append]; exact .inl hh)
          · intro hh; exact hfd (by
              simp only [Block.funcDeclNames, List.mem_append]; exact .inl hh)
        have hext_rest : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars rest ∧ n ∉ Block.getVars rest ∧
            n ∉ Block.definedVars rest false ∧ n ∉ Block.funcDeclNames rest := by
          intro n hn
          have ⟨hm, hg, hd, hfd⟩ := hext n hn
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro hh; exact hm (by
              simp only [Block.modifiedVars, List.mem_append]; exact .inr hh)
          · intro hh; exact hg (by
              simp only [Block.getVars, List.mem_append]; exact .inr hh)
          · intro hh; exact hd (by
              simp only [Block.definedVars, List.mem_append]; exact .inr hh)
          · intro hh; exact hfd (by
              simp only [Block.funcDeclNames, List.mem_append]; exact .inr hh)
        refine ⟨ih_stmt outer extra s hsz_s hwf_s hext_s, ?_⟩
        -- For tail, the inner outer extends by `decide (n ∈ Stmt.definedVars s true)`.
        -- Want: Block.defUseWellFormed
        --   (fun n => (outer n || extra n) || decide (n ∈ Stmt.definedVars s true)) rest
        -- Have: Block.defUseWellFormed
        --   (fun n => outer n || decide (n ∈ Stmt.definedVars s true)) rest
        -- Use ih_block with extra := extra and outer = original tail outer.
        have h_inner : Block.defUseWellFormed
            (fun n => (fun m => outer m || decide (m ∈ Stmt.definedVars s true)) n || extra n)
            rest = Bool.true :=
          ih_block (fun m => outer m || decide (m ∈ Stmt.definedVars s true)) extra rest
            hsz_rest hwf_rest hext_rest
        -- Reorganize the boolean predicate.
        have heq : (fun n =>
              (outer n || decide (n ∈ Stmt.definedVars s true)) || extra n) =
            (fun n => (outer n || extra n) || decide (n ∈ Stmt.definedVars s true)) := by
          funext n; simp only [Bool.or_assoc, Bool.or_comm (decide _) (extra _)]
        rw [heq] at h_inner
        exact h_inner

private theorem defUseWellFormed_outer_extend_stmt
    {outer extra : Expression.Ident → Bool} {s : Statement}
    (hwf : Stmt.defUseWellFormed outer s = Bool.true)
    (hext : ∀ n, extra n = Bool.true →
        n ∉ Stmt.modifiedVars s ∧ n ∉ Stmt.getVars s ∧
        n ∉ Stmt.definedVars s false ∧ n ∉ Stmt.funcDeclNames s) :
    Stmt.defUseWellFormed (fun n => outer n || extra n) s = Bool.true :=
  (defUseWellFormed_outer_extend_aux (Stmt.sizeOf s)).1 outer extra s
    (Nat.le_refl _) hwf hext

private theorem defUseWellFormed_outer_extend_block
    {outer extra : Expression.Ident → Bool} {bss : Statements}
    (hwf : Block.defUseWellFormed outer bss = Bool.true)
    (hext : ∀ n, extra n = Bool.true →
        n ∉ Block.modifiedVars bss ∧ n ∉ Block.getVars bss ∧
        n ∉ Block.definedVars bss false ∧ n ∉ Block.funcDeclNames bss) :
    Block.defUseWellFormed (fun n => outer n || extra n) bss = Bool.true :=
  (defUseWellFormed_outer_extend_aux (Block.sizeOf bss)).2 outer extra bss
    (Nat.le_refl _) hwf hext

/-- Append decomposition for `Block.defUseWellFormed`. -/
private theorem defUseWellFormed_block_append
    (outer : Expression.Ident → Bool) (ss₁ ss₂ : Statements) :
    Block.defUseWellFormed outer (ss₁ ++ ss₂) = Bool.true ↔
      Block.defUseWellFormed outer ss₁ = Bool.true ∧
      Block.defUseWellFormed
        (fun n => outer n || decide (n ∈ Block.definedVars ss₁ true)) ss₂ = Bool.true := by
  induction ss₁ generalizing outer with
  | nil => simp [Block.definedVars, Block.defUseWellFormed]
  | cons s rest ih =>
    show Block.defUseWellFormed outer (s :: (rest ++ ss₂)) = Bool.true ↔ _
    constructor
    · intro h
      have ⟨h_s, h_rest⟩ := defUseWellFormed_cons h
      have ⟨h_rest', h_ss₂⟩ :=
        (ih (fun n => outer n || decide (n ∈ Stmt.definedVars s true))).mp h_rest
      refine ⟨?_, ?_⟩
      · unfold Block.defUseWellFormed
        simp only [Bool.and_eq_true]; exact ⟨h_s, h_rest'⟩
      · rw [defUseWellFormed_block_congr (fun n => ?_) ss₂]
        · exact h_ss₂
        · simp only [Block.definedVars, List.mem_append, Bool.or_assoc, Bool.decide_or]
    · intro ⟨h_left, h_right⟩
      have ⟨h_s, h_rest_left⟩ := defUseWellFormed_cons h_left
      apply defUseWellFormed_cons_intro h_s
      apply (ih (fun n => outer n || decide (n ∈ Stmt.definedVars s true))).mpr
      refine ⟨h_rest_left, ?_⟩
      rw [defUseWellFormed_block_congr (fun n => ?_) ss₂]
      · exact h_right
      · simp only [Block.definedVars, List.mem_append, Bool.or_assoc, Bool.decide_or]


/-- `Stmt.definedVars s true ⊆ Stmt.definedVars s false` for any statement. -/
private theorem stmt_definedVars_true_subset_false (s : Statement) (n : Expression.Ident)
    (h : n ∈ Stmt.definedVars s true) : n ∈ Stmt.definedVars s false := by
  match s with
  | .cmd c => simp [Stmt.definedVars] at h ⊢; exact h
  | .block .. => simp [Stmt.definedVars] at h
  | .ite .. => simp [Stmt.definedVars] at h
  | .loop .. => simp [Stmt.definedVars] at h
  | .exit .. => simp [Stmt.definedVars] at h
  | .funcDecl .. => simp [Stmt.definedVars] at h
  | .typeDecl .. => simp [Stmt.definedVars] at h

/-- Combined mutual induction: if `defUseWellFormed outer` holds and `n` is
    read or modified but not defined, then `outer n = true`. -/
private theorem defUseWellFormed_touched_notDef_aux (sz : Nat) :
    (∀ (outer : Expression.Ident → Bool) (s : Statement),
      Stmt.sizeOf s ≤ sz →
      Stmt.defUseWellFormed outer s = Bool.true →
      ∀ (n : Expression.Ident),
        (n ∈ Stmt.modifiedVars s ∨ n ∈ Stmt.getVars s) →
        n ∉ Stmt.definedVars s false →
        outer n = Bool.true) ∧
    (∀ (outer : Expression.Ident → Bool) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.defUseWellFormed outer bss = Bool.true →
      ∀ (n : Expression.Ident),
        (n ∈ Block.modifiedVars bss ∨ n ∈ Block.getVars bss) →
        n ∉ Block.definedVars bss false →
        outer n = Bool.true) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro outer s hsz; cases s <;> simp [Stmt.sizeOf] at hsz
    · intro outer bss hsz hwf n hn hnd
      match bss with
      | [] => simp [Block.modifiedVars, Block.getVars] at hn
      | s :: rest => simp [Block.sizeOf] at hsz
  | succ k ih =>
    obtain ⟨ih_stmt, ih_block⟩ := ih
    refine ⟨?_, ?_⟩
    · -- Stmt case
      intro outer s hsz hwf n hn hnd
      match s with
      | .cmd c =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨⟨hgv, hmv⟩, _⟩ := hwf
        rw [List.all_eq_true] at hgv hmv
        simp only [Stmt.modifiedVars, Stmt.getVars] at hn
        rcases hn with hmod | hget
        · exact hmv n hmod
        · exact hgv n hget
      | .block l bss md =>
        simp only [Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
          Bool.false_eq_true, ↓reduceIte] at hn hnd
        unfold Stmt.defUseWellFormed at hwf
        have hsz_bss : Block.sizeOf bss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        exact ih_block outer bss hsz_bss hwf n hn hnd
      | .ite cond tbss ebss md =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨⟨hcond_all, htbss⟩, hebss⟩ := hwf
        rw [List.all_eq_true] at hcond_all
        simp only [Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
          Bool.false_eq_true, ↓reduceIte, List.mem_append] at hn hnd
        have hnd_t : n ∉ Block.definedVars tbss false := fun h => hnd (Or.inl h)
        have hnd_e : n ∉ Block.definedVars ebss false := fun h => hnd (Or.inr h)
        have hsz_t : Block.sizeOf tbss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_e : Block.sizeOf ebss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        rcases hn with (ht | he) | (hc | hgt) | hge
        · exact ih_block outer tbss hsz_t htbss n (Or.inl ht) hnd_t
        · exact ih_block outer ebss hsz_e hebss n (Or.inl he) hnd_e
        · exact hcond_all n hc
        · exact ih_block outer tbss hsz_t htbss n (Or.inr hgt) hnd_t
        · exact ih_block outer ebss hsz_e hebss n (Or.inr hge) hnd_e
      | .loop guard measure inv body md =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨⟨⟨hguard_all, hmeas_all⟩, hinv_all⟩, hbody⟩ := hwf
        rw [List.all_eq_true] at hguard_all hmeas_all hinv_all
        simp only [Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
          Bool.false_eq_true, ↓reduceIte, List.mem_append] at hn hnd
        have hsz_body : Block.sizeOf body ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        rcases hn with hmod | ((hg | hm) | hi) | hb
        · exact ih_block outer body hsz_body hbody n (Or.inl hmod) hnd
        · exact hguard_all n hg
        · exact hmeas_all n hm
        · exact hinv_all n hi
        · exact ih_block outer body hsz_body hbody n (Or.inr hb) hnd
      | .exit l md =>
        simp [Stmt.modifiedVars, Stmt.getVars] at hn
      | .funcDecl decl md =>
        -- modifiedVars = []; getVars = body's free vars (formals excluded).
        -- defUseWellFormed gives `(getVars).all (definedVars n) && !definedVars decl.name`,
        -- we read off the first conjunct.
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨hgv, _⟩ := hwf
        rw [List.all_eq_true] at hgv
        simp only [Stmt.modifiedVars] at hn
        rcases hn with hmod | hget
        · exact absurd hmod (by simp)
        · exact hgv n hget
      | .typeDecl tc md =>
        simp [Stmt.modifiedVars, Stmt.getVars] at hn
    · -- Block case
      intro outer bss hsz hwf n hn hnd
      match bss with
      | [] =>
        simp [Block.modifiedVars, Block.getVars] at hn
      | s :: rest =>
        unfold Block.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨hwf_s, hwf_rest⟩ := hwf
        simp only [Block.modifiedVars, Block.getVars, Block.definedVars,
          List.mem_append] at hn hnd
        have hnd_s : n ∉ Stmt.definedVars s false := fun h => hnd (Or.inl h)
        have hnd_rest : n ∉ Block.definedVars rest false := fun h => hnd (Or.inr h)
        have hsz_s : Stmt.sizeOf s ≤ k := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ k := by
          simp [Block.sizeOf] at hsz; omega
        have hnd_s_true : n ∉ Stmt.definedVars s true :=
          fun h => hnd_s (stmt_definedVars_true_subset_false s n h)
        rcases hn with (hs | hr) | (hs | hr)
        · exact ih_stmt outer s hsz_s hwf_s n (Or.inl hs) hnd_s
        · have h_rest_result := ih_block
            (fun m => outer m || decide (m ∈ Stmt.definedVars s true))
            rest hsz_rest hwf_rest n (Or.inl hr) hnd_rest
          rw [Bool.or_eq_true] at h_rest_result
          rcases h_rest_result with h | h
          · exact h
          · rw [decide_eq_true_eq] at h; exact absurd h hnd_s_true
        · exact ih_stmt outer s hsz_s hwf_s n (Or.inr hs) hnd_s
        · have h_rest_result := ih_block
            (fun m => outer m || decide (m ∈ Stmt.definedVars s true))
            rest hsz_rest hwf_rest n (Or.inr hr) hnd_rest
          rw [Bool.or_eq_true] at h_rest_result
          rcases h_rest_result with h | h
          · exact h
          · rw [decide_eq_true_eq] at h; exact absurd h hnd_s_true

/-- If `Stmt.defUseWellFormed outer s = true` and `n` is read or modified in `s`
    but never defined in `s`, then `outer n = true`.  This is the fundamental
    link between def-use well-formedness and `readWritesDefined`. -/
private theorem defUseWellFormed_modGetVars_implies_outer
    {outer : Expression.Ident → Bool} {bss : Statements}
    (hwf : Block.defUseWellFormed outer bss = Bool.true)
    {n : Expression.Ident}
    (hn : n ∈ Block.modifiedVars bss ∨ n ∈ Block.getVars bss)
    (hnd : n ∉ Block.definedVars bss false) : outer n = Bool.true :=
  (defUseWellFormed_touched_notDef_aux (Block.sizeOf bss)).2
    outer bss (Nat.le_refl _) hwf n hn hnd

/-- Stmt-level: touched but not defined implies `outer n`. -/
private theorem defUseWellFormed_touched_notDef_implies_outer
    {outer : Expression.Ident → Bool} {s : Statement}
    (hwf : Stmt.defUseWellFormed outer s = Bool.true)
    {n : Expression.Ident}
    (hn : n ∈ Stmt.modifiedVars s ∨ n ∈ Stmt.getVars s)
    (hnd : n ∉ Stmt.definedVars s false) : outer n = Bool.true :=
  (defUseWellFormed_touched_notDef_aux (Stmt.sizeOf s)).1
    outer s (Nat.le_refl _) hwf n hn hnd

/-- `Block.definedVars bss true ⊆ Block.definedVars bss false`. -/
private theorem block_definedVars_true_subset_false (bss : Statements) (n : Expression.Ident)
    (h : n ∈ Block.definedVars bss true) : n ∈ Block.definedVars bss false := by
  induction bss with
  | nil => simp [Block.definedVars] at h
  | cons s rest ih =>
    simp only [Block.definedVars, List.mem_append] at h ⊢
    rcases h with hs | hr
    · left
      match s with
      | .cmd c => simpa [Stmt.definedVars] using hs
      | .block .. => simp [Stmt.definedVars] at hs  -- hs : False
      | .ite .. => simp [Stmt.definedVars] at hs    -- hs : False
      | .loop .. => simp [Stmt.definedVars] at hs   -- hs : False
      | .exit .. => simpa [Stmt.definedVars] using hs
      | .funcDecl .. => simpa [Stmt.definedVars] using hs
      | .typeDecl .. => simpa [Stmt.definedVars] using hs
    · exact .inr (ih hr)

/-- `BlockInitEnvWF bss` follows from `InitEnvWF (.block l bss md)`: the block
    has the same touched/defined vars as its inner statements. -/
private theorem InitEnvWF.toBlock_block {reserved : List String} {l : String}
    {bss : Statements} {md : MetaData Expression} {ρ : Env Expression}
    (h : InitEnvWF reserved (.block l bss md) ρ) :
    BlockInitEnvWF reserved bss ρ where
  readWritesDefined n hn hnd := by
    refine h.readWritesDefined n ?_ ?_
    · show n ∈ Stmt.touchedVars (.block l bss md)
      show n ∈ Stmt.modifiedOrDefinedVars (.block l bss md) true ++
              Stmt.getVars (.block l bss md)
      -- Stmt.touchedVars (.block l bss md) = Block.modifiedVars bss ++ Block.getVars bss
      -- Block.touchedVars bss = (Block.modifiedVars bss ++ Block.definedVars bss true) ++ Block.getVars bss
      -- Need: n ∉ Block.definedVars bss false → n ∉ Block.definedVars bss true
      show n ∈ Stmt.modifiedVars (.block l bss md) ++ Stmt.definedVars (.block l bss md) true ++
                Stmt.getVars (.block l bss md)
      simp only [Stmt.modifiedVars, Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
      -- goal: n ∈ Block.modifiedVars bss ++ Block.getVars bss
      -- hn : n ∈ Block.touchedVars bss = (Block.modifiedVars bss ++ Block.definedVars bss true) ++ Block.getVars bss
      have hn' : n ∈ (Block.modifiedVars bss ++ Block.definedVars bss true) ++ Block.getVars bss := hn
      rcases List.mem_append.mp hn' with h1 | h2
      · rcases List.mem_append.mp h1 with hmod | hdef
        · exact List.mem_append_left _ hmod
        · -- n ∈ Block.definedVars bss true but n ∉ Block.definedVars bss false → contradiction
          exact absurd (block_definedVars_true_subset_false bss n hdef) hnd
      · exact List.mem_append_right _ h2
    · show n ∉ Stmt.definedVars (.block l bss md) false
      have heq : Stmt.definedVars (.block l bss md : Statement) false =
                 Block.definedVars bss false := by simp [Stmt.definedVars]
      rw [heq]; exact hnd
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Stmt.definedVars (.block l bss md) false
    have heq : Stmt.definedVars (.block l bss md : Statement) false =
               Block.definedVars bss false := by simp [Stmt.definedVars]
    rw [heq]; exact hn)
  definedVarsNotReserved n hn := h.definedVarsNotReserved n (by
    show n ∈ Stmt.definedVars (.block l bss md) false
    have heq : Stmt.definedVars (.block l bss md : Statement) false =
               Block.definedVars bss false := by simp [Stmt.definedVars]
    rw [heq]; exact hn)
  funcDeclNamesNotReserved n hn := h.funcDeclNamesNotReserved n (by
    show n ∈ Stmt.funcDeclNames (.block l bss md)
    simpa [Stmt.funcDeclNames] using hn)
  reservedFresh := h.reservedFresh
  wfBool := h.wfBool
  wfVal  := h.wfVal
  wfVar  := h.wfVar
  evalCong := h.evalCong
  exprCongr := h.exprCongr
  defUseOk := by
    have hwf := h.defUseOk
    rw [defUseWellFormed_block] at hwf
    exact hwf

/-- For ite: `BlockInitEnvWF tss` follows from `InitEnvWF (.ite c tss ess md)`.
    Uses `defUseOk` to derive `readWritesDefined` without disjointness hypotheses. -/
private theorem InitEnvWF.toBlock_ite_left {reserved : List String}
    {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression} {ρ : Env Expression}
    (h : InitEnvWF reserved (.ite c tss ess md) ρ) :
    BlockInitEnvWF reserved tss ρ where
  readWritesDefined n hn hnd := by
    have hwf_tss : Block.defUseWellFormed (fun n => (ρ.store n).isSome) tss = Bool.true :=
      (defUseWellFormed_ite_branches h.defUseOk).1
    have hn_mg : n ∈ Block.modifiedVars tss ∨ n ∈ Block.getVars tss := by
      have hntouched : n ∈ Block.touchedVars tss := hn
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hntouched
      rcases hntouched with (hm | hd) | hg
      · exact Or.inl hm
      · exact absurd (block_definedVars_true_subset_false tss n hd) hnd
      · exact Or.inr hg
    exact defUseWellFormed_modGetVars_implies_outer hwf_tss hn_mg hnd
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md) false
    simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]; left; exact hn)
  definedVarsNotReserved n hn p hp := h.definedVarsNotReserved n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md) false
    simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]; left; exact hn) p hp
  funcDeclNamesNotReserved n hn p hp := h.funcDeclNamesNotReserved n (by
    show n ∈ Stmt.funcDeclNames (.ite c tss ess md)
    simp [Stmt.funcDeclNames]; exact .inl hn) p hp
  reservedFresh := h.reservedFresh
  wfBool := h.wfBool
  wfVal  := h.wfVal
  wfVar  := h.wfVar
  evalCong := h.evalCong
  exprCongr := h.exprCongr
  defUseOk := (defUseWellFormed_ite_branches h.defUseOk).1

private theorem InitEnvWF.toBlock_ite_right {reserved : List String}
    {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression} {ρ : Env Expression}
    (h : InitEnvWF reserved (.ite c tss ess md) ρ) :
    BlockInitEnvWF reserved ess ρ where
  readWritesDefined n hn hnd := by
    have hwf_ess : Block.defUseWellFormed (fun n => (ρ.store n).isSome) ess = Bool.true :=
      (defUseWellFormed_ite_branches h.defUseOk).2
    have hn_mg : n ∈ Block.modifiedVars ess ∨ n ∈ Block.getVars ess := by
      have hntouched : n ∈ Block.touchedVars ess := hn
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hntouched
      rcases hntouched with (hm | hd) | hg
      · exact Or.inl hm
      · exact absurd (block_definedVars_true_subset_false ess n hd) hnd
      · exact Or.inr hg
    exact defUseWellFormed_modGetVars_implies_outer hwf_ess hn_mg hnd
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md) false
    simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]; right; exact hn)
  definedVarsNotReserved n hn p hp := h.definedVarsNotReserved n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md) false
    simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]; right; exact hn) p hp
  funcDeclNamesNotReserved n hn p hp := h.funcDeclNamesNotReserved n (by
    show n ∈ Stmt.funcDeclNames (.ite c tss ess md)
    simp [Stmt.funcDeclNames]; exact .inr hn) p hp
  reservedFresh := h.reservedFresh
  wfBool := h.wfBool
  wfVal  := h.wfVal
  wfVar  := h.wfVar
  evalCong := h.evalCong
  exprCongr := h.exprCongr
  defUseOk := (defUseWellFormed_ite_branches h.defUseOk).2

/-- `InitEnvWF s` follows from `BlockInitEnvWF (s :: ss)`.
    Uses `defUseOk` to derive `readWritesDefined` without disjointness hypotheses. -/
private theorem BlockInitEnvWF.toStmt_head {reserved : List String} {s : Statement}
    {ss : Statements} {ρ : Env Expression}
    (h : BlockInitEnvWF reserved (s :: ss) ρ) :
    InitEnvWF reserved s ρ where
  readWritesDefined n hn hnd := by
    have hwf_s : Stmt.defUseWellFormed (fun n => (ρ.store n).isSome) s = Bool.true :=
      (defUseWellFormed_cons h.defUseOk).1
    have hn_mg : n ∈ Stmt.modifiedVars s ∨ n ∈ Stmt.getVars s := by
      have hntouched : n ∈ Stmt.touchedVars s := hn
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append] at hntouched
      rcases hntouched with (hm | hd) | hg
      · exact Or.inl hm
      · exact absurd (block_definedVars_true_subset_false [s] n (by simp [Block.definedVars]; exact hd)) (by simp [Block.definedVars]; exact hnd)
      · exact Or.inr hg
    exact defUseWellFormed_touched_notDef_implies_outer hwf_s hn_mg hnd
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Block.definedVars (s :: ss) false
    simp only [Block.definedVars, List.mem_append]; left; exact hn)
  definedVarsNotReserved n hn p hp := h.definedVarsNotReserved n (by
    show n ∈ Block.definedVars (s :: ss) false
    simp only [Block.definedVars, List.mem_append]; left; exact hn) p hp
  funcDeclNamesNotReserved n hn p hp := h.funcDeclNamesNotReserved n (by
    show n ∈ Block.funcDeclNames (s :: ss)
    simp [Block.funcDeclNames]; exact .inl hn) p hp
  reservedFresh := h.reservedFresh
  wfBool := h.wfBool
  wfVal  := h.wfVal
  wfVar  := h.wfVar
  evalCong := h.evalCong
  exprCongr := h.exprCongr
  defUseOk := (defUseWellFormed_cons h.defUseOk).1

/-- Any variable that becomes `isSome` after executing `s` (from `isNone` before)
    must be in `Stmt.definedVars s`. -/
private theorem cmd_definedVars_true_isSome_after
    {cmd : Command} {ρ₀ ρ₁ : Env Expression}
    (hstar : CoreStar π φ (.stmt (.cmd cmd) ρ₀) (.terminal ρ₁))
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars (.cmd cmd) true) :
    (ρ₁.store n).isSome := by
  -- The trace is one step: step_cmd heval then refl.
  -- For n ∈ definedVars (.cmd cmd) true, cmd must be .cmd (.init n ...).
  -- After eval_init/eval_init_unconstrained, InitState gives σ' n = .some v.
  match hstar with
  | .step _ _ _ (.step_cmd heval) hrest =>
    cases hrest with
    | refl =>
      simp only [Config.getEnv]
      cases heval with
      | cmd_sem hcmd =>
        simp [Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars] at hn
        cases hcmd with
        | eval_init _ hinit _ =>
          cases hinit with
          | init _ hsome _ =>
            simp [Cmd.definedVars, List.mem_singleton] at hn
            subst hn; simp [hsome]
        | eval_init_unconstrained hinit _ =>
          cases hinit with
          | init _ hsome _ =>
            simp [Cmd.definedVars, List.mem_singleton] at hn
            subst hn; simp [hsome]
        | eval_set _ _ _ => simp [Cmd.definedVars] at hn
        | eval_set_nondet _ _ => simp [Cmd.definedVars] at hn
        | eval_assert_pass _ _ => simp [Cmd.definedVars] at hn
        | eval_assert_fail _ _ => simp [Cmd.definedVars] at hn
        | eval_assume _ _ => simp [Cmd.definedVars] at hn
        | eval_cover _ => simp [Cmd.definedVars] at hn
      | @call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        simp [Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars] at hn
    | step _ _ _ hstep _ => exact nomatch hstep

private theorem stmt_definedVars_true_isSome_after
    {s : Statement} {ρ₀ ρ₁ : Env Expression}
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (_hdefsNone : ∀ n ∈ Stmt.definedVars s true, (ρ₀.store n).isNone)
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars s true) :
    (ρ₁.store n).isSome := by
  match s, hstar, hn with
  | .cmd _, hstar', hn' => exact cmd_definedVars_true_isSome_after (π := π) (φ := φ) hstar' n hn'
  | .block .., _, hn' => simp [Stmt.definedVars] at hn'
  | .ite .., _, hn' => simp [Stmt.definedVars] at hn'
  | .loop .., _, hn' => simp [Stmt.definedVars] at hn'
  | .exit .., _, hn' => simp [Stmt.definedVars] at hn'
  | .funcDecl .., _, hn' => simp [Stmt.definedVars] at hn'
  | .typeDecl .., _, hn' => simp [Stmt.definedVars] at hn'

/-- From `Block.defUseWellFormed outer ss = true` and `n ∈ Block.definedVars ss false`,
    conclude that `outer n = false`.  This is the def-side dual of
    `defUseWellFormed_modGetVars_implies_outer`: in a well-formed block, freshly-defined
    variables can't already be in the outer scope.  We prove it by mutual induction on
    statement/block size, mirroring `defUseWellFormed_touched_notDef_aux`. -/
private theorem defUseWellFormed_definedVars_notMem_outer_aux (sz : Nat) :
    (∀ (outer : Expression.Ident → Bool) (s : Statement),
      Stmt.sizeOf s ≤ sz →
      Stmt.defUseWellFormed outer s = Bool.true →
      ∀ (n : Expression.Ident),
        n ∈ Stmt.definedVars s false →
        outer n = Bool.false) ∧
    (∀ (outer : Expression.Ident → Bool) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.defUseWellFormed outer bss = Bool.true →
      ∀ (n : Expression.Ident),
        n ∈ Block.definedVars bss false →
        outer n = Bool.false) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro outer s hsz; cases s <;> simp [Stmt.sizeOf] at hsz
    · intro outer bss hsz hwf n hn
      match bss with
      | [] => simp [Block.definedVars] at hn
      | s :: rest => simp [Block.sizeOf] at hsz
  | succ k ih =>
    obtain ⟨ih_stmt, ih_block⟩ := ih
    refine ⟨?_, ?_⟩
    · -- Stmt case
      intro outer s hsz hwf n hn
      match s with
      | .cmd c =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨_, hdefs⟩ := hwf
        rw [List.all_eq_true] at hdefs
        simp only [Stmt.definedVars, HasVarsImp.definedVars] at hn
        have := hdefs n hn
        simp only [decide_eq_true_eq] at this
        cases h : outer n
        · rfl
        · exact absurd h this
      | .block l bss md =>
        simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte] at hn
        unfold Stmt.defUseWellFormed at hwf
        have hsz_bss : Block.sizeOf bss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        exact ih_block outer bss hsz_bss hwf n hn
      | .ite cond tbss ebss md =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨⟨_, htbss⟩, hebss⟩ := hwf
        simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append] at hn
        have hsz_t : Block.sizeOf tbss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_e : Block.sizeOf ebss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        rcases hn with ht | he
        · exact ih_block outer tbss hsz_t htbss n ht
        · exact ih_block outer ebss hsz_e hebss n he
      | .loop guard measure inv body md =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨_, hbody⟩ := hwf
        simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte] at hn
        have hsz_body : Block.sizeOf body ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        exact ih_block outer body hsz_body hbody n hn
      | .exit l md => simp [Stmt.definedVars] at hn
      | .funcDecl decl md =>
        -- `Stmt.definedVars (.funcDecl) false = []`: funcDecl extends `eval`,
        -- not `store`, so it contributes nothing to def-side store-state.
        simp [Stmt.definedVars] at hn
      | .typeDecl tc md => simp [Stmt.definedVars] at hn
    · -- Block case
      intro outer bss hsz hwf n hn
      match bss with
      | [] => simp [Block.definedVars] at hn
      | s :: rest =>
        unfold Block.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨hwf_s, hwf_rest⟩ := hwf
        simp only [Block.definedVars, List.mem_append] at hn
        have hsz_s : Stmt.sizeOf s ≤ k := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ k := by simp [Block.sizeOf] at hsz; omega
        rcases hn with hs | hr
        · exact ih_stmt outer s hsz_s hwf_s n hs
        · -- n ∈ Block.definedVars rest false ⟹ extended-outer n = false
          have h_rest_result := ih_block
            (fun m => outer m || decide (m ∈ Stmt.definedVars s true))
            rest hsz_rest hwf_rest n hr
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h_rest_result
          exact h_rest_result.1

/-- Block-level: from `defUseWellFormed`, freshly-defined vars are not in the outer scope. -/
private theorem defUseWellFormed_block_definedVars_notMem_outer
    {outer : Expression.Ident → Bool} {bss : Statements}
    (hwf : Block.defUseWellFormed outer bss = Bool.true)
    {n : Expression.Ident}
    (hn : n ∈ Block.definedVars bss false) : outer n = Bool.false :=
  (defUseWellFormed_definedVars_notMem_outer_aux (Block.sizeOf bss)).2
    outer bss (Nat.le_refl _) hwf n hn

/-! ### Configuration-level isNone invariant

For loops, we need a star-trace argument that handles iteration.  The key
invariant: at every config `c` reachable from `.stmt (.loop ..) ρ₀`, the
"refresh value" of `n` at `c` (computed by ignoring inner block scopes) is
`none`.  More precisely, every enclosing block in `c` has `σ_parent n = none`,
and the innermost env has `.store n = none` UNLESS we're inside a block scope
that will project it away.

We use a simpler invariant based on `outerInv`'s structure: track that
`(σ_outer n) = none` (where `σ_outer` is the loop's parent context) AND
every block scope in `c` has its `σ_parent n = none`.  If those hold, then
when blocks pop (via `step_block_done`), the result `projectStore σ_parent _ n`
is `none`. -/

/-- "n is none-anchored at c":
    `(c.getEnv.store n).isNone` AND every enclosing block in `c` has
    `σ_parent n = none`.  This is the invariant we propagate through trace
    induction for the loop case. -/
private def isNoneAnchored (n : Expression.Ident) : CC → Prop
  | .stmt _ ρ => (ρ.store n).isNone
  | .stmts _ ρ => (ρ.store n).isNone
  | .terminal ρ => (ρ.store n).isNone
  | .exiting _ ρ => (ρ.store n).isNone
  | .block _ σ_parent _ inner => (σ_parent n).isNone ∧ isNoneAnchored n inner
  | .seq inner _ => isNoneAnchored n inner

/-- `isNoneAnchored n c` implies `(c.getEnv.store n).isNone`. -/
private theorem isNoneAnchored_implies_isNone (n : Expression.Ident) (c : CC)
    (h : isNoneAnchored n c) : (c.getEnv.store n).isNone := by
  match c with
  | .stmt _ _ => exact h
  | .stmts _ _ => exact h
  | .terminal _ => exact h
  | .exiting _ _ => exact h
  | .block _ _ _ inner =>
    obtain ⟨_, hinner⟩ := h
    show (inner.getEnv.store n).isNone
    exact isNoneAnchored_implies_isNone n inner hinner
  | .seq inner _ =>
    show (inner.getEnv.store n).isNone
    exact isNoneAnchored_implies_isNone n inner h

/-- Single-step preserves `isNoneAnchored n` when `n` is outside the
    "writable" surface: not in `c₁`'s `Stmt.modifiedVars` (modifications) and
    `n` is also not init'd at the current step.  In particular, for any
    statement where the modifiedVars covers all writes (excluding scoped inits),
    `isNoneAnchored` is preserved. -/
private theorem step_preserves_isNoneAnchored
    {n : Expression.Ident} {a b : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b)
    (hinv : isNoneAnchored n a)
    (hnoWrite : n ∉ Config.touchedVarsSet a) :
    isNoneAnchored n b := by
  induction hstep with
  | step_cmd heval =>
    -- a = .stmt (.cmd c) ρ, b = .terminal ρ' with ρ'.store = σ'
    -- hnoWrite: n ∉ Stmt.modifiedVars (.cmd c) ++ Stmt.definedVars (.cmd c) false
    -- Use evalCommand_store_frame_stmt: σ' n = ρ.store n.
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    have hmod : n ∉ Stmt.modifiedVars (.cmd ‹Command›) :=
      fun hmem => hnoWrite (by
        simp only [Config.touchedVarsSet, List.mem_append]; exact .inl hmem)
    have hdef : n ∉ Stmt.definedVars (.cmd ‹Command›) false :=
      fun hmem => hnoWrite (by
        simp only [Config.touchedVarsSet, List.mem_append]; exact .inr hmem)
    have hframe := evalCommand_store_frame_stmt (π := π) (φ := φ) heval hmod hdef
    rw [Option.isNone_iff_eq_none]
    rw [hframe]
    exact Option.isNone_iff_eq_none.mp hinv
  | step_block =>
    -- a = .stmt (.block l ss md) ρ, b = .block (.some l) ρ.store (.stmts ss ρ)
    -- hinv : (ρ.store n).isNone
    -- goal isNoneAnchored n b = ⟨(ρ.store n).isNone, isNoneAnchored n (.stmts ss ρ)⟩
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_ite_true _ _ =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_ite_false _ _ =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_ite_nondet_true =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_ite_nondet_false =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_loop_enter _ _ _ _ _ =>
    -- a = .stmt (.loop ..) ρ, b = .seq (.block .none ρ.store (.stmts body ρ')) [loop]
    -- where ρ' = { ρ with hasFailure := ... }, so ρ'.store = ρ.store.
    -- hinv : (ρ.store n).isNone.  goal: isNoneAnchored n b = isNoneAnchored n (.block ...) = ⟨(ρ.store n).isNone, (ρ'.store n).isNone⟩
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_loop_exit _ _ _ _ =>
    -- b = .terminal { ρ with hasFailure := ... }
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_loop_nondet_enter _ _ =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_loop_nondet_exit _ _ =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_exit =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_funcDecl =>
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    exact hinv
  | step_typeDecl =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_stmts_nil =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_stmts_cons =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_seq_inner _ ih =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ih hinv (fun hmem => hnoWrite (by
      simp only [Config.touchedVarsSet, List.mem_append]
      left; left; exact hmem))
  | step_seq_done =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_seq_exit =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_block_body _ ih =>
    simp only [isNoneAnchored] at hinv ⊢
    obtain ⟨hpar, hinner⟩ := hinv
    refine ⟨hpar, ih hinner ?_⟩
    simp only [Config.touchedVarsSet] at hnoWrite
    exact hnoWrite
  | step_block_done =>
    -- a = .block l σ_parent (.terminal ρ'), hinv = ⟨(σ_parent n).isNone, (ρ'.store n).isNone⟩
    -- b = .terminal { ρ' with store := projectStore σ_parent ρ'.store }
    -- goal: ((projectStore σ_parent ρ'.store) n).isNone
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    obtain ⟨hpar, _⟩ := hinv
    simp only [projectStore]
    rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hpar)]
    rfl
  | step_block_exit_match _ =>
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    obtain ⟨hpar, _⟩ := hinv
    simp only [projectStore]
    rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hpar)]
    rfl
  | step_block_exit_mismatch _ =>
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    obtain ⟨hpar, _⟩ := hinv
    simp only [projectStore]
    rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hpar)]
    rfl

/-- Star version of `step_preserves_isNoneAnchored`. -/
private theorem stmt_terminal_preserves_isNone
    {s : Statement} {ρ₀ ρ₁ : Env Expression}
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (n : Expression.Ident)
    (hnone : (ρ₀.store n).isNone)
    (hnmod : n ∉ Stmt.modifiedVars s)
    (hndef_true : n ∉ Stmt.definedVars s true) :
    (ρ₁.store n).isNone := by
  match s with
  | .cmd c =>
    -- For .cmd, definedVars true = definedVars false, so we use existing frame.
    have hndef_false : n ∉ Stmt.definedVars (.cmd c) false := by
      simpa [Stmt.definedVars] using hndef_true
    have hxnot : n ∉ Config.touchedVarsSet (.stmt (.cmd c) ρ₀) := by
      simp only [Config.touchedVarsSet, List.mem_append]
      rintro (hmod | hdef)
      · exact hnmod hmod
      · exact hndef_false hdef
    have hframe := star_preserves_store_outside_touchedVars_isNone (π := π) (φ := φ)
      hstar n (by simpa [Config.getEnv] using hnone) hxnot
    simp only [Config.getEnv] at hframe
    rw [Option.isNone_iff_eq_none, hframe]
    exact Option.isNone_iff_eq_none.mp hnone
  | .block l bss md =>
    -- Trace: step_block + (block_reaches_terminal: inner reaches terminal/exiting,
    -- ρ₁ = projectStore ρ₀.store ρ_inner.store).  In both projection cases,
    -- (projectStore ρ₀.store ρ_inner.store n) = if (ρ₀.store n).isSome then ... else none.
    -- Since hnone : (ρ₀.store n).isNone, the result is `none`.
    cases hstar with
    | step _ mid _ h1 r1 =>
      cases h1
      -- mid = .block (.some l) ρ₀.store (.stmts bss ρ₀)
      match block_reaches_terminal (P := Expression)
          (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
      | .inl ⟨ρ_inner, _, heq⟩ =>
        rw [heq]
        show (projectStore ρ₀.store ρ_inner.store n).isNone
        simp only [projectStore]
        rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
        rfl
      | .inr ⟨_, ρ_inner, _, heq⟩ =>
        rw [heq]
        show (projectStore ρ₀.store ρ_inner.store n).isNone
        simp only [projectStore]
        rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
        rfl
  | .ite c tss ess md =>
    -- Trace begins with step_ite_*, leading to .block .none ρ₀.store (.stmts ?? ρ₀).
    -- Same projection argument as for .block.
    cases hstar with
    | step _ mid _ h1 r1 =>
      cases h1 with
      | step_ite_true _ _ | step_ite_false _ _ | step_ite_nondet_true | step_ite_nondet_false =>
        match block_reaches_terminal (P := Expression)
            (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
        | .inl ⟨ρ_inner, _, heq⟩ =>
          rw [heq]
          show (projectStore ρ₀.store ρ_inner.store n).isNone
          simp only [projectStore]
          rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
          rfl
        | .inr ⟨_, ρ_inner, _, heq⟩ =>
          rw [heq]
          show (projectStore ρ₀.store ρ_inner.store n).isNone
          simp only [projectStore]
          rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
          rfl
  | .loop g m inv body md =>
    -- For loops, the trace either:
    --   (a) takes step_loop_exit immediately: store unchanged.
    --   (b) takes step_loop_enter, leading to a seq with a block-wrapped body.
    --       The body's iteration runs in `.block .none ρ_iter.store ...`; the
    --       block-exit projection drops `n` to `none` since `(ρ_iter.store n).isNone`.
    --       The recursive [loop] then runs from the projected env, where `n`
    --       remains `none`.  Trace-length induction over `ReflTransT`.
    have hstarT := reflTrans_to_T hstar
    -- Strong induction on trace length.
    suffices ∀ (n_steps : Nat) (ρ₀ ρ₁ : Env Expression),
        (ρ₀.store n).isNone →
        ∀ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
            (.stmt (.loop g m inv body md) ρ₀) (.terminal ρ₁)),
          h.len ≤ n_steps → (ρ₁.store n).isNone by
      exact this hstarT.len ρ₀ ρ₁ hnone hstarT (Nat.le_refl _)
    clear hstar hstarT ρ₀ ρ₁ hnone
    intro n_steps
    induction n_steps with
    | zero =>
      intro ρ₀ ρ₁ _ hT hlen
      match hT, hlen with
      | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
    | succ k ih =>
      intro ρ₀ ρ₁ hnone₀ hT hlen
      -- Case-split on the first step of the loop trace.
      match hT with
      | .step _ _ _ hstep1 hrest =>
        cases hstep1 with
        | step_loop_exit _ _ _ _ =>
          -- ρ₁ = { ρ₀ with hasFailure := ρ₀.hasFailure || ... }, store unchanged.
          match hrest with
          | .refl _ => exact hnone₀
          | .step _ _ _ h _ => exact nomatch h
        | step_loop_nondet_exit _ _ =>
          match hrest with
          | .refl _ => exact hnone₀
          | .step _ _ _ h _ => exact nomatch h
        | step_loop_enter _ _ _ _ _ =>
          -- successor is .seq (.block .none ρ₀.store (.stmts body ρ₀'))
          --                     [.loop (.det g) m inv body md].
          have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
          have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
          have ⟨ρ_inner, ⟨hT_inner, hlen_inner⟩, heq⟩ := blockT_none_reaches_terminal π φ hT_block
          have hnone_mid : (ρ_mid.store n).isNone := by
            rw [heq]
            show (projectStore ρ₀.store ρ_inner.store n).isNone
            simp only [projectStore]
            rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone₀)]
            rfl
          match hT_tail, hlen_split with
          | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
            have hlen_rest' : hrest'.len < hrest.len := by
              simp only [ReflTransT.len] at hlen_split ⊢; omega
            have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
            have hρ_eq : ρ_mid' = ρ₁ := by
              match hT_nil with
              | .step _ _ _ .step_stmts_nil hrr =>
                match hrr with
                | .refl _ => rfl
                | .step _ _ _ h _ => exact nomatch h
            subst hρ_eq
            have hlen_loop : hT_loop'.len ≤ k := by omega
            exact ih ρ_mid ρ_mid' hnone_mid hT_loop' hlen_loop
        | step_loop_nondet_enter _ _ =>
          have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
          have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
          have ⟨ρ_inner, ⟨hT_inner, hlen_inner⟩, heq⟩ := blockT_none_reaches_terminal π φ hT_block
          have hnone_mid : (ρ_mid.store n).isNone := by
            rw [heq]
            show (projectStore ρ₀.store ρ_inner.store n).isNone
            simp only [projectStore]
            rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone₀)]
            rfl
          match hT_tail, hlen_split with
          | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
            have hlen_rest' : hrest'.len < hrest.len := by
              simp only [ReflTransT.len] at hlen_split ⊢; omega
            have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
            have hρ_eq : ρ_mid' = ρ₁ := by
              match hT_nil with
              | .step _ _ _ .step_stmts_nil hrr =>
                match hrr with
                | .refl _ => rfl
                | .step _ _ _ h _ => exact nomatch h
            subst hρ_eq
            have hlen_loop : hT_loop'.len ≤ k := by omega
            exact ih ρ_mid ρ_mid' hnone_mid hT_loop' hlen_loop
  | .exit l md =>
    -- .exit cannot reach .terminal: it always reaches .exiting.
    exfalso
    cases hstar with
    | step _ _ _ h1 r1 =>
      cases h1
      cases r1 with
      | step _ _ _ h2 _ => cases h2
  | .funcDecl decl md =>
    -- step_funcDecl modifies eval but not store: ρ₁.store = ρ₀.store.
    cases hstar with
    | step _ _ _ h1 r1 =>
      cases h1
      cases r1 with
      | refl => exact hnone
      | step _ _ _ h2 _ => cases h2
  | .typeDecl tc md =>
    -- Trace = step_typeDecl + refl, ρ₁ = ρ₀.
    cases hstar with
    | step _ _ _ h1 r1 =>
      cases h1
      cases r1 with
      | refl => exact hnone
      | step _ _ _ h2 _ => cases h2

/-- For compound `s` (`.block`/`.ite`/`.loop`), terminal trace preserves
    `(ρ₀.store n).isNone` regardless of `n`'s status in `modifiedVars`/
    `definedVars`.  The argument: each of these begins with a step that wraps
    the inner body in `.block .none ρ₀.store ...`, and the block-exit projection
    drops `n` to `none` since `(ρ₀.store n).isNone`.  For `.loop`, this
    extends through trace-length induction. -/
private theorem stmt_compound_terminal_preserves_isNone
    {s : Statement} {ρ₀ ρ₁ : Env Expression}
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (hcompound : ∀ c, s ≠ .cmd c) (hnoexit : ∀ l md, s ≠ .exit l md)
    (n : Expression.Ident)
    (hnone : (ρ₀.store n).isNone) :
    (ρ₁.store n).isNone := by
  match s with
  | .cmd c => exact absurd rfl (hcompound c)
  | .exit l md => exact absurd rfl (hnoexit l md)
  | .funcDecl decl md =>
    -- step_funcDecl modifies eval but not store: ρ₁.store = ρ₀.store.
    cases hstar with
    | step _ _ _ h1 r1 =>
      cases h1
      cases r1 with
      | refl => exact hnone
      | step _ _ _ h2 _ => cases h2
  | .typeDecl tc md =>
    cases hstar with
    | step _ _ _ h1 r1 =>
      cases h1
      cases r1 with
      | refl => exact hnone
      | step _ _ _ h2 _ => cases h2
  | .block l bss md =>
    cases hstar with
    | step _ mid _ h1 r1 =>
      cases h1
      match block_reaches_terminal (P := Expression)
          (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
      | .inl ⟨ρ_inner, _, heq⟩ =>
        rw [heq]
        show (projectStore ρ₀.store ρ_inner.store n).isNone
        simp only [projectStore]
        rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
        rfl
      | .inr ⟨_, ρ_inner, _, heq⟩ =>
        rw [heq]
        show (projectStore ρ₀.store ρ_inner.store n).isNone
        simp only [projectStore]
        rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
        rfl
  | .ite c tss ess md =>
    cases hstar with
    | step _ mid _ h1 r1 =>
      cases h1 with
      | step_ite_true _ _ | step_ite_false _ _ | step_ite_nondet_true | step_ite_nondet_false =>
        match block_reaches_terminal (P := Expression)
            (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
        | .inl ⟨ρ_inner, _, heq⟩ =>
          rw [heq]
          show (projectStore ρ₀.store ρ_inner.store n).isNone
          simp only [projectStore]
          rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
          rfl
        | .inr ⟨_, ρ_inner, _, heq⟩ =>
          rw [heq]
          show (projectStore ρ₀.store ρ_inner.store n).isNone
          simp only [projectStore]
          rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
          rfl
  | .loop g m inv body md =>
    have hstarT := reflTrans_to_T hstar
    suffices ∀ (n_steps : Nat) (ρ₀ ρ₁ : Env Expression),
        (ρ₀.store n).isNone →
        ∀ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
            (.stmt (.loop g m inv body md) ρ₀) (.terminal ρ₁)),
          h.len ≤ n_steps → (ρ₁.store n).isNone by
      exact this hstarT.len ρ₀ ρ₁ hnone hstarT (Nat.le_refl _)
    clear hstar hstarT ρ₀ ρ₁ hnone
    intro n_steps
    induction n_steps with
    | zero =>
      intro ρ₀ ρ₁ _ hT hlen
      match hT, hlen with
      | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
    | succ k ih =>
      intro ρ₀ ρ₁ hnone₀ hT hlen
      match hT with
      | .step _ _ _ hstep1 hrest =>
        cases hstep1 with
        | step_loop_exit _ _ _ _ =>
          match hrest with
          | .refl _ => exact hnone₀
          | .step _ _ _ h _ => exact nomatch h
        | step_loop_nondet_exit _ _ =>
          match hrest with
          | .refl _ => exact hnone₀
          | .step _ _ _ h _ => exact nomatch h
        | step_loop_enter _ _ _ _ _ =>
          have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
          have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
          have ⟨ρ_inner, ⟨hT_inner, hlen_inner⟩, heq⟩ := blockT_none_reaches_terminal π φ hT_block
          have hnone_mid : (ρ_mid.store n).isNone := by
            rw [heq]
            show (projectStore ρ₀.store ρ_inner.store n).isNone
            simp only [projectStore]
            rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone₀)]
            rfl
          match hT_tail, hlen_split with
          | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
            have hlen_rest' : hrest'.len < hrest.len := by
              simp only [ReflTransT.len] at hlen_split ⊢; omega
            have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
            have hρ_eq : ρ_mid' = ρ₁ := by
              match hT_nil with
              | .step _ _ _ .step_stmts_nil hrr =>
                match hrr with
                | .refl _ => rfl
                | .step _ _ _ h _ => exact nomatch h
            subst hρ_eq
            have hlen_loop : hT_loop'.len ≤ k := by omega
            exact ih ρ_mid ρ_mid' hnone_mid hT_loop' hlen_loop
        | step_loop_nondet_enter _ _ =>
          have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
          have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
          have ⟨ρ_inner, ⟨hT_inner, hlen_inner⟩, heq⟩ := blockT_none_reaches_terminal π φ hT_block
          have hnone_mid : (ρ_mid.store n).isNone := by
            rw [heq]
            show (projectStore ρ₀.store ρ_inner.store n).isNone
            simp only [projectStore]
            rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone₀)]
            rfl
          match hT_tail, hlen_split with
          | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
            have hlen_rest' : hrest'.len < hrest.len := by
              simp only [ReflTransT.len] at hlen_split ⊢; omega
            have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
            have hρ_eq : ρ_mid' = ρ₁ := by
              match hT_nil with
              | .step _ _ _ .step_stmts_nil hrr =>
                match hrr with
                | .refl _ => rfl
                | .step _ _ _ h _ => exact nomatch h
            subst hρ_eq
            have hlen_loop : hT_loop'.len ≤ k := by omega
            exact ih ρ_mid ρ_mid' hnone_mid hT_loop' hlen_loop

/-- `BlockInitEnvWF ss ρ₁` follows from `BlockInitEnvWF (s :: ss) ρ₀` after `s`
    ran from `ρ₀` to `ρ₁`, using the block's own `defUseOk` to discharge the
    side conditions. -/
private theorem BlockInitEnvWF.toBlock_tail_via_defUseOk {reserved : List String}
    (hwf_ext : WFEvalExtension φ)
    {s : Statement} {ss : Statements} {ρ₀ ρ₁ : Env Expression}
    (h : BlockInitEnvWF reserved (s :: ss) ρ₀)
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁)) :
    BlockInitEnvWF reserved ss ρ₁ where
  readWritesDefined n hn hnd := by
    -- n ∈ Block.touchedVars ss, n ∉ Block.definedVars ss false → (ρ₁.store n).isSome.
    -- defUseOk on (s :: ss) extends with definedVars s true for tail.  So tail's
    -- well-formedness against (fun m => (ρ₀.store m).isSome || decide (m ∈ defVars s true)).
    have ⟨_, htail_def⟩ := defUseWellFormed_cons h.defUseOk
    have hmod_or_get :
        n ∈ Block.modifiedVars ss ∨ n ∈ Block.getVars ss := by
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hn
      rcases hn with ((hm | hd_true) | hg)
      · exact .inl hm
      · exact absurd (block_definedVars_true_subset_false ss n hd_true) hnd
      · exact .inr hg
    -- Apply: tail well-formedness gives extended-outer n = true.
    have houter :
        ((ρ₀.store n).isSome || decide (n ∈ Stmt.definedVars s true)) = Bool.true :=
      defUseWellFormed_modGetVars_implies_outer htail_def hmod_or_get hnd
    rw [Bool.or_eq_true] at houter
    rcases houter with h₀ | hd_true
    · -- (ρ₀.store n).isSome - propagated by trace.
      have := stmt_star_preserves_isSome (π := π) (φ := φ) s ρ₀ _ hstar n h₀
      simpa [Config.getEnv] using this
    · -- n ∈ Stmt.definedVars s true: head's def made it isSome.
      have hmem : n ∈ Stmt.definedVars s true := by
        simp only [decide_eq_true_eq] at hd_true; exact hd_true
      have hdefsNone : ∀ m ∈ Stmt.definedVars s true, (ρ₀.store m).isNone := fun m hm =>
        h.defsUndefined m (by
          simp only [Block.definedVars, List.mem_append]; left
          exact stmt_definedVars_true_subset_false s m hm)
      exact stmt_definedVars_true_isSome_after (π := π) (φ := φ) hstar hdefsNone n hmem
  defsUndefined n hn := by
    -- n ∈ Block.definedVars ss false → (ρ₁.store n).isNone.
    -- From `defUseOk` on tail, extended-outer n = false, i.e. (ρ₀.store n).isNone
    -- AND n ∉ Stmt.definedVars s true.
    have ⟨hhead_def, htail_def⟩ := defUseWellFormed_cons h.defUseOk
    have houter_false :
        ((ρ₀.store n).isSome || decide (n ∈ Stmt.definedVars s true)) = Bool.false :=
      defUseWellFormed_block_definedVars_notMem_outer htail_def hn
    rw [Bool.or_eq_false_iff] at houter_false
    obtain ⟨hsome_false, hd_false⟩ := houter_false
    have hnone₀ : (ρ₀.store n).isNone := by
      cases hx : ρ₀.store n <;> simp_all
    have hndef_true : n ∉ Stmt.definedVars s true := by
      simp only [decide_eq_false_iff_not] at hd_false; exact hd_false
    -- Case-split on n ∈ Stmt.definedVars s false.
    by_cases hn_def_s : n ∈ Stmt.definedVars s false
    · -- n is inner-defined in compound s.  The compound-exit projection scrubs
      -- n back to none: stmt_compound_terminal_preserves_isNone requires only
      -- (ρ₀.store n).isNone.  s must be compound since for .cmd, def_true = def_false.
      apply stmt_compound_terminal_preserves_isNone (π := π) (φ := φ) hstar
      · intro c heq; subst heq
        simp only [Stmt.definedVars] at hn_def_s hndef_true
        exact hndef_true hn_def_s
      · intro l md heq; subst heq
        simp only [Stmt.definedVars] at hn_def_s
        exact List.not_mem_nil hn_def_s
      · exact hnone₀
    · -- n ∉ Stmt.definedVars s false: then we can derive n ∉ Stmt.modifiedVars s
      -- (else defUseOk forces outer = true, contradicting hnone₀).
      have hnmod : n ∉ Stmt.modifiedVars s := by
        intro hmod
        have houter_true : ((ρ₀.store n).isSome) = Bool.true :=
          defUseWellFormed_touched_notDef_implies_outer hhead_def (.inl hmod) hn_def_s
        have heq : ρ₀.store n = none := Option.isNone_iff_eq_none.mp hnone₀
        rw [heq] at houter_true
        cases houter_true
      exact stmt_terminal_preserves_isNone (π := π) (φ := φ) hstar n hnone₀ hnmod hndef_true
  definedVarsNotReserved n hn p hp := h.definedVarsNotReserved n (by
    show n ∈ Block.definedVars (s :: ss) false
    simp only [Block.definedVars, List.mem_append]; right; exact hn) p hp
  funcDeclNamesNotReserved n hn p hp := h.funcDeclNamesNotReserved n (by
    show n ∈ Block.funcDeclNames (s :: ss)
    simp [Block.funcDeclNames]; exact .inr hn) p hp
  reservedFresh n hsome₁ p hp := by
    by_cases hsome₀ : (ρ₀.store n).isSome
    · exact h.reservedFresh n hsome₀ p hp
    · have hnone : (ρ₀.store n).isNone := Option.not_isSome_iff_eq_none.mp hsome₀ ▸ rfl
      -- Need: n ∈ Stmt.definedVars s true (to apply head's definedVarsNotReserved-style).
      -- If (ρ₁.store n).isSome but (ρ₀.store n).isNone, then by no-fresh-creation outside
      -- definedVars, n must be in Stmt.definedVars s true (transitively).
      -- This is `stmt_definedVars_true_or_isNone_after`: its converse direction.
      -- Approach: split on n ∈ Stmt.definedVars s true.
      by_cases hn_def_true : n ∈ Stmt.definedVars s true
      · apply h.definedVarsNotReserved n _ p hp
        show n ∈ Block.definedVars (s :: ss) false
        simp only [Block.definedVars, List.mem_append]; left
        exact stmt_definedVars_true_subset_false s n hn_def_true
      · -- (ρ₁.store n).isSome but (ρ₀.store n).isNone and n ∉ Stmt.definedVars s true.
        -- Goal: contradiction.  Strategy: show (ρ₁.store n).isNone by case-split on
        -- n ∈ Stmt.definedVars s false.
        exfalso
        have ⟨hhead_def, _⟩ := defUseWellFormed_cons h.defUseOk
        have hres : (ρ₁.store n).isNone := by
          by_cases hn_def_s : n ∈ Stmt.definedVars s false
          · -- Inner-scoped def in compound s: projection scrubs n back to none.
            apply stmt_compound_terminal_preserves_isNone (π := π) (φ := φ) hstar
            · intro c heq; subst heq
              simp only [Stmt.definedVars] at hn_def_s hn_def_true
              exact hn_def_true hn_def_s
            · intro l md heq; subst heq
              simp only [Stmt.definedVars] at hn_def_s
              exact List.not_mem_nil hn_def_s
            · exact hnone
          · have hnmod : n ∉ Stmt.modifiedVars s := by
              intro hmod
              have houter_true : ((ρ₀.store n).isSome) = Bool.true :=
                defUseWellFormed_touched_notDef_implies_outer hhead_def (.inl hmod) hn_def_s
              have heq : ρ₀.store n = none := Option.isNone_iff_eq_none.mp hnone
              rw [heq] at houter_true
              cases houter_true
            exact stmt_terminal_preserves_isNone (π := π) (φ := φ) hstar n hnone hnmod hn_def_true
        rw [Option.isNone_iff_eq_none] at hres
        rw [hres] at hsome₁
        cases hsome₁
  wfBool := by
    have h' := star_preserves_wfBool Expression (EvalCommand π φ) (EvalPureFunc φ)
      hwf_ext.toWFEvalExtension (s := s) (ρ := ρ₀) hstar (show WellFormedSemanticEvalBool _ from h.wfBool)
    simpa [Config.getEnv] using h'
  wfVal := by
    have h' := star_preserves_wfVal Expression (EvalCommand π φ) (EvalPureFunc φ)
      hwf_ext.toWFEvalExtension (s := s) (ρ := ρ₀) hstar (show WellFormedSemanticEvalVal _ from h.wfVal)
    simpa [Config.getEnv] using h'
  wfVar := by
    have h' := star_preserves_wfVar Expression (EvalCommand π φ) (EvalPureFunc φ)
      hwf_ext.toWFEvalExtension (s := s) (ρ := ρ₀) hstar (show WellFormedSemanticEvalVar _ from h.wfVar)
    simpa [Config.getEnv] using h'
  evalCong := by
    have h' := core_wfCong_preserved_stmt π φ hwf_ext
      (show WellFormedCoreEvalCong _ from h.evalCong)
      (StepStmtStar_to_CoreStepStar hstar)
    simpa [Config.getEnv] using h'
  exprCongr := by
    have h' := core_wfExprCongr_preserved_stmt π φ hwf_ext
      (show @Imperative.WellFormedSemanticEvalExprCongr Expression _ _ from h.exprCongr)
      (StepStmtStar_to_CoreStepStar hstar)
    simpa [Config.getEnv] using h'
  defUseOk := by
    have ⟨_, htail⟩ := defUseWellFormed_cons h.defUseOk
    rw [defUseWellFormed_block_congr (fun n => ?_) ss] at htail
    · exact htail
    · have hdefsNone : ∀ m ∈ Stmt.definedVars s true, (ρ₀.store m).isNone := fun m hm =>
        h.defsUndefined m (by
          simp only [Block.definedVars, List.mem_append]; left
          exact stmt_definedVars_true_subset_false s m hm)
      cases h₀ : (ρ₀.store n).isSome
      case true =>
        simp only [Bool.true_or]
        have := stmt_star_preserves_isSome (π := π) (φ := φ) s ρ₀ _ hstar n h₀
        simpa [Config.getEnv] using this
      case false =>
        simp only [Bool.false_or]
        have hnone₀ : (ρ₀.store n).isNone := by
          cases hx : ρ₀.store n <;> simp_all
        cases hd : decide (n ∈ Stmt.definedVars s true)
        case true =>
          have hmem : n ∈ Stmt.definedVars s true := by
            simp [decide_eq_true_eq] at hd; exact hd
          exact (stmt_definedVars_true_isSome_after (π := π) (φ := φ) hstar hdefsNone n hmem).symm
        case false =>
          -- (ρ₀.store n).isNone ∧ n ∉ Stmt.definedVars s true → goal: false = (ρ₁.store n).isSome
          have hnotmem : n ∉ Stmt.definedVars s true := by
            simp [decide_eq_true_eq] at hd; exact hd
          apply Eq.symm
          have ⟨hhead_def, _⟩ := defUseWellFormed_cons h.defUseOk
          have hres : (ρ₁.store n).isNone := by
            by_cases hn_def_s : n ∈ Stmt.definedVars s false
            · -- Inner-scoped def in compound s: projection scrubs n back to none.
              apply stmt_compound_terminal_preserves_isNone (π := π) (φ := φ) hstar
              · intro c heq; subst heq
                simp only [Stmt.definedVars] at hn_def_s hnotmem
                exact hnotmem hn_def_s
              · intro l md heq; subst heq
                simp only [Stmt.definedVars] at hn_def_s
                exact List.not_mem_nil hn_def_s
              · exact hnone₀
            · have hnmod : n ∉ Stmt.modifiedVars s := by
                intro hmod
                have houter_true : ((ρ₀.store n).isSome) = Bool.true :=
                  defUseWellFormed_touched_notDef_implies_outer hhead_def (.inl hmod) hn_def_s
                have heq : ρ₀.store n = none := Option.isNone_iff_eq_none.mp hnone₀
                rw [heq] at houter_true
                cases houter_true
              exact stmt_terminal_preserves_isNone (π := π) (φ := φ) hstar n hnone₀ hnmod hnotmem
          cases h_eq : (ρ₁.store n).isSome with
          | true => rw [Option.isNone_iff_eq_none] at hres; rw [hres] at h_eq; cases h_eq
          | false => rfl

/-! ## Simulation -/

/-! ### Property abbreviations for the simulation conjuncts

The four conjuncts of the simulation property are bundled into named
abbreviations so that helper lemmas can reference them without repeating
the lengthy quantifier/clause structure. -/

/-- Statement-level simulation: a `Stmt`'s source trace is matched by the
    transformed statement's trace, modulo `Or.inl` (target can fail). -/
private abbrev SimStmtCorrProp (reserved : List String) (sz : Nat) : Prop :=
  ∀ (σ : LoopElimState) (st : Statement),
    Stmt.sizeOf st ≤ sz →
    stmtOk σ st →
    ∀ (ρ₀ : Env Expression),
      InitEnvWF reserved st ρ₀ →
      (∀ ρ', CoreStar π φ (.stmt st ρ₀) (.terminal ρ') →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀ ∨
        (ρ'.hasFailure = Bool.false →
          CoreStar π φ (.stmt (stmtResult σ st) ρ₀) (.terminal ρ')))
      ∧
      (∀ lbl ρ', CoreStar π φ (.stmt st ρ₀) (.exiting lbl ρ') →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀ ∨
        (ρ'.hasFailure = Bool.false →
          CoreStar π φ (.stmt (stmtResult σ st) ρ₀) (.exiting lbl ρ')))

/-- Block-level simulation: same as `SimStmtCorrProp` but for `Statements`. -/
private abbrev SimBlockCorrProp (reserved : List String) (sz : Nat) : Prop :=
  ∀ (σ : LoopElimState) (bss : Statements),
    Block.sizeOf bss ≤ sz →
    blockOk σ bss →
    ∀ (ρ₀ : Env Expression),
      BlockInitEnvWF reserved bss ρ₀ →
      (∀ ρ', CoreStar π φ (.stmts bss ρ₀) (.terminal ρ') →
        CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀ ∨
        (ρ'.hasFailure = Bool.false →
          CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.terminal ρ')))
      ∧
      (∀ lbl ρ', CoreStar π φ (.stmts bss ρ₀) (.exiting lbl ρ') →
        CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀ ∨
        (ρ'.hasFailure = Bool.false →
          CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.exiting lbl ρ')))

/-- Statement-level CanFail preservation. -/
private abbrev SimStmtCFProp (reserved : List String) (sz : Nat) : Prop :=
  ∀ (σ : LoopElimState) (st : Statement),
    Stmt.sizeOf st ≤ sz →
    stmtOk σ st →
    ∀ (ρ₀ : Env Expression),
      InitEnvWF reserved st ρ₀ →
      Transform.CanFail (LangCore π φ) st ρ₀ →
      Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀

/-- Block-level CanFail preservation. -/
private abbrev SimBlockCFProp (reserved : List String) (sz : Nat) : Prop :=
  ∀ (σ : LoopElimState) (bss : Statements),
    Block.sizeOf bss ≤ sz →
    blockOk σ bss →
    ∀ (ρ₀ : Env Expression),
      BlockInitEnvWF reserved bss ρ₀ →
      CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss ρ₀ →
      CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀

/-- The full bundled IH used by the inductive case of `simulation`. -/
private abbrev SimAllProp (reserved : List String) (sz : Nat) : Prop :=
  SimStmtCorrProp π φ reserved sz ∧ SimBlockCorrProp π φ reserved sz ∧
  SimStmtCFProp π φ reserved sz ∧ SimBlockCFProp π φ reserved sz

/-! ### Per-case helpers shared across the four conjuncts

These helpers factor out duplicated patterns inside the simulation body
(notably the four `.ite` sub-cases, the `.block` case, and the `:: ` cons
pattern of `block_corr`/`block_cf`).  Each helper closes a single shape
of obligation and is invoked from each conjunct that exhibits that
shape. -/

/-- The branch-sim result extracted from the IH for the chosen branch.
    Same shape as `SimBlockCorrProp` instantiated at one block. -/
private abbrev BlockSimRes (σ : LoopElimState) (bss : Statements)
    (ρ₀ : Env Expression) : Prop :=
  (∀ ρ', CoreStar π φ (.stmts bss ρ₀) (.terminal ρ') →
    CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.terminal ρ')))
  ∧
  (∀ lbl ρ', CoreStar π φ (.stmts bss ρ₀) (.exiting lbl ρ') →
    CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.exiting lbl ρ')))

/-- The CanFail-preservation property for a single block. -/
private abbrev BlockCFRes (σ : LoopElimState) (bss : Statements)
    (ρ₀ : Env Expression) : Prop :=
  CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss ρ₀ → CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀

/-- Ite scoped-block term-branch helper: given the inner block trace
    `r1` reaching `.terminal ρ'` and the branch's sim result, lift to the
    target ite trace.  Generic over the four `step_ite_*` step
    constructors (provided as `step1_tgt`).

    Used from the term-branch ite case (×4 sub-cases). -/
private theorem ite_term_branch_lift
    {bss bss_tgt : Statements}
    {tss_tgt ess_tgt : Statements}
    {c_tgt : ExprOrNondet Expression}
    {md_tgt : MetaData Expression}
    {ρ₀ ρ' : Env Expression}
    (step1_tgt : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.stmt (.ite c_tgt tss_tgt ess_tgt md_tgt) ρ₀)
        (.block .none ρ₀.store ρ₀.eval (.stmts bss_tgt ρ₀)))
    (r1 : ReflTrans (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
        (.block .none ρ₀.store ρ₀.eval (.stmts bss ρ₀)) (.terminal ρ'))
    (hsim_bss_term :
      ∀ ρ_inner, CoreStar π φ (.stmts bss ρ₀) (.terminal ρ_inner) →
        CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss_tgt ρ₀ ∨
        (ρ_inner.hasFailure = Bool.false →
          CoreStar π φ (.stmts bss_tgt ρ₀) (.terminal ρ_inner))) :
    Transform.CanFail (LangCore π φ)
        (.ite c_tgt tss_tgt ess_tgt md_tgt) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ
        (.stmt (.ite c_tgt tss_tgt ess_tgt md_tgt) ρ₀)
        (.terminal ρ')) := by
  have r1T := reflTrans_to_T r1
  have ⟨ρ_inner, ⟨hterm_T, _⟩, heq⟩ :=
    blockT_none_reaches_terminal (π := π) (φ := φ) r1T
  have hterm := reflTransT_to_prop hterm_T
  match hsim_bss_term ρ_inner hterm with
  | .inl hcf =>
    obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
    exact .inl ⟨.block .none ρ₀.store ρ₀.eval cfg,
      by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
      .step _ _ _ step1_tgt
        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
          _ _ .none ρ₀.store ρ₀.eval hreach_cf)⟩
  | .inr hok_branch =>
    refine .inr (fun hnf => ?_)
    have hnf_inner : ρ_inner.hasFailure = Bool.false := by
      subst heq; simp at hnf; exact hnf
    have hreach_target := hok_branch hnf_inner
    subst heq
    refine .step _ _ _ step1_tgt
      (ReflTrans_Transitive _ _ _ _
        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
          _ _ .none ρ₀.store ρ₀.eval hreach_target)
        ?_)
    -- After block_inner_star, target is `.block .none ρ₀.store ρ₀.eval (.terminal ρ_inner)`.
    -- step_block_done yields `.terminal { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }`.
    exact .step _ _ _ .step_block_done (.refl _)

/-- Ite scoped-block exit-branch helper: dual of `ite_term_branch_lift`
    for traces reaching `.exiting`. -/
private theorem ite_exit_branch_lift
    {bss bss_tgt : Statements}
    {tss_tgt ess_tgt : Statements}
    {c_tgt : ExprOrNondet Expression}
    {md_tgt : MetaData Expression}
    {ρ₀ ρ' : Env Expression}
    {lbl : String}
    (step1_tgt : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.stmt (.ite c_tgt tss_tgt ess_tgt md_tgt) ρ₀)
        (.block .none ρ₀.store ρ₀.eval (.stmts bss_tgt ρ₀)))
    (r1 : ReflTrans (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
        (.block .none ρ₀.store ρ₀.eval (.stmts bss ρ₀)) (.exiting lbl ρ'))
    (hsim_bss_exit :
      ∀ ρ_inner, CoreStar π φ (.stmts bss ρ₀) (.exiting lbl ρ_inner) →
        CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss_tgt ρ₀ ∨
        (ρ_inner.hasFailure = Bool.false →
          CoreStar π φ (.stmts bss_tgt ρ₀) (.exiting lbl ρ_inner))) :
    Transform.CanFail (LangCore π φ)
        (.ite c_tgt tss_tgt ess_tgt md_tgt) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ
        (.stmt (.ite c_tgt tss_tgt ess_tgt md_tgt) ρ₀)
        (.exiting lbl ρ')) := by
  have ⟨ρ_inner, hexit_inner, heq⟩ :=
    block_none_reaches_exiting_some (π := π) (φ := φ) r1
  match hsim_bss_exit ρ_inner hexit_inner with
  | .inl hcf =>
    obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
    exact .inl ⟨.block .none ρ₀.store ρ₀.eval cfg,
      by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
      .step _ _ _ step1_tgt
        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
          _ _ .none ρ₀.store ρ₀.eval hreach_cf)⟩
  | .inr hok_branch =>
    refine .inr (fun hnf => ?_)
    have hnf_inner : ρ_inner.hasFailure = Bool.false := by
      subst heq; simp at hnf; exact hnf
    have hreach_target := hok_branch hnf_inner
    subst heq
    refine .step _ _ _ step1_tgt
      (ReflTrans_Transitive _ _ _ _
        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
          _ _ .none ρ₀.store ρ₀.eval hreach_target)
        ?_)
    exact .step _ _ _ (.step_block_exit_mismatch (fun h => nomatch h)) (.refl _)

/-- Ite CanFail-preservation lift: given an inner block trace `r1`
    leading to a failing config and the branch's CanFail-preservation
    result, produce a failing trace through the target ite. -/
private theorem ite_canfail_lift
    {bss bss_tgt : Statements}
    {tss_tgt ess_tgt : Statements}
    {c_tgt : ExprOrNondet Expression}
    {md_tgt : MetaData Expression}
    {ρ₀ : Env Expression}
    {cfg : CC}
    (hfail : cfg.getEnv.hasFailure = Bool.true)
    (step1_tgt : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.stmt (.ite c_tgt tss_tgt ess_tgt md_tgt) ρ₀)
        (.block .none ρ₀.store ρ₀.eval (.stmts bss_tgt ρ₀)))
    (r1 : ReflTrans (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
        (.block .none ρ₀.store ρ₀.eval (.stmts bss ρ₀)) cfg)
    (hcf_branch : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss ρ₀ → CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss_tgt ρ₀) :
    Transform.CanFail (LangCore π φ)
      (.ite c_tgt tss_tgt ess_tgt md_tgt) ρ₀ := by
  have ⟨inner_cfg, hfail', hinner⟩ := block_canfail_to_inner r1 hfail
  have ⟨cfg', hfail'', hreach'⟩ := hcf_branch ⟨inner_cfg, hfail', hinner⟩
  exact ⟨.block .none ρ₀.store ρ₀.eval cfg',
    by show cfg'.getEnv.hasFailure = Bool.true; exact hfail'',
    .step _ _ _ step1_tgt
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
        _ _ .none ρ₀.store ρ₀.eval hreach')⟩

/-- Block term-branch helper used by stmt_corr's term-clause: trace through
    `.block l bss md` reaching `.terminal ρ'` is dispatched via
    `block_reaches_terminal_refined` on whether `bss` itself terminates or
    exits matching `l`, and the branch sim-result is lifted accordingly. -/
private theorem block_term_case
    {σ_bss_tgt : LoopElimState}
    {l : String} {bss : Statements} {md : MetaData Expression}
    {ρ₀ ρ' : Env Expression}
    (r1 : ReflTrans (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
        (.block (.some l) ρ₀.store ρ₀.eval (.stmts bss ρ₀)) (.terminal ρ'))
    (hsim_bss : BlockSimRes π φ σ_bss_tgt bss ρ₀) :
    Transform.CanFail (LangCore π φ) (.block l (blockResult σ_bss_tgt bss) md) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ (.stmt (.block l (blockResult σ_bss_tgt bss) md) ρ₀) (.terminal ρ')) := by
  obtain ⟨ρ_inner, hinner_or, hρ'eq⟩ := block_reaches_terminal_refined (P := Expression) (CmdT := Command) (EvalCommand π φ) (EvalPureFunc φ) r1
  cases hinner_or with
  | inl hterm_inner =>
    match hsim_bss.1 ρ_inner hterm_inner with
    | .inl hcf =>
      exact .inl (Transform.canFailBlock_to_canFail_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert l _ md ρ₀ hcf)
    | .inr hok_bss =>
      refine .inr (fun hnf => ?_)
      have hnf_inner : ρ_inner.hasFailure = Bool.false := by
        rw [hρ'eq] at hnf; simp at hnf; exact hnf
      have hreach_target := hok_bss hnf_inner
      rw [hρ'eq]
      exact block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) l _ md ρ₀ ρ_inner hreach_target
  | inr hexit_inner =>
    match hsim_bss.2 l ρ_inner hexit_inner with
    | .inl hcf =>
      exact .inl (Transform.canFailBlock_to_canFail_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert l _ md ρ₀ hcf)
    | .inr hok_bss =>
      refine .inr (fun hnf => ?_)
      have hnf_inner : ρ_inner.hasFailure = Bool.false := by
        rw [hρ'eq] at hnf; simp at hnf; exact hnf
      have hreach_target := hok_bss hnf_inner
      rw [hρ'eq]
      exact block_wrap_exiting_match (EvalCommand π φ) (EvalPureFunc φ) l _ md ρ₀ ρ_inner hreach_target

/-- Block exit-branch helper: trace through `.block l bss md` reaching
    `.exiting lbl ρ'` (with `lbl ≠ l`) lifts to a target exit trace. -/
private theorem block_exit_case
    {σ_bss_tgt : LoopElimState}
    {l : String} {bss : Statements} {md : MetaData Expression}
    {ρ₀ ρ' : Env Expression} {lbl : String}
    (r1 : ReflTrans (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
        (.block (.some l) ρ₀.store ρ₀.eval (.stmts bss ρ₀)) (.exiting lbl ρ'))
    (hsim_bss : BlockSimRes π φ σ_bss_tgt bss ρ₀) :
    Transform.CanFail (LangCore π φ) (.block l (blockResult σ_bss_tgt bss) md) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ (.stmt (.block l (blockResult σ_bss_tgt bss) md) ρ₀)
        (.exiting lbl ρ')) := by
  obtain ⟨ρ_inner, hne, hexit_inner, hρ'eq⟩ := block_reaches_exiting_refined (P := Expression) (CmdT := Command) (EvalCommand π φ) (EvalPureFunc φ) r1
  match hsim_bss.2 lbl ρ_inner hexit_inner with
  | .inl hcf =>
    exact .inl (Transform.canFailBlock_to_canFail_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert l _ md ρ₀ hcf)
  | .inr hok_bss =>
    refine .inr (fun hnf => ?_)
    have hnf_inner : ρ_inner.hasFailure = Bool.false := by
      rw [hρ'eq] at hnf; simp at hnf; exact hnf
    have hreach_target := hok_bss hnf_inner
    rw [hρ'eq]
    exact block_wrap_exiting_mismatch (EvalCommand π φ) (EvalPureFunc φ) l _ md lbl ρ₀ ρ_inner hne hreach_target

/-- Block CanFail-preservation helper: trace through `.block l bss md`
    reaches a failing config; dispatch via the inner-block trace. -/
private theorem block_canfail_case
    {σ_bss_tgt : LoopElimState}
    {l : String} {bss : Statements} {md : MetaData Expression}
    {ρ₀ : Env Expression} {cfg : CC}
    (hfail : cfg.getEnv.hasFailure = Bool.true)
    (r1 : ReflTrans (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
        (.block (.some l) ρ₀.store ρ₀.eval (.stmts bss ρ₀)) cfg)
    (hcf_inner : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss ρ₀ → CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ_bss_tgt bss) ρ₀) :
    Transform.CanFail (LangCore π φ) (.block l (blockResult σ_bss_tgt bss) md) ρ₀ := by
  have ⟨inner_cfg, hfail', hinner⟩ := block_canfail_to_inner r1 hfail
  have ⟨cfg', hfail'', hreach'⟩ := hcf_inner ⟨inner_cfg, hfail', hinner⟩
  exact Transform.canFailBlock_to_canFail_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert l _ md ρ₀ ⟨cfg', hfail'', hreach'⟩

/-- Block-corr cons-step "head-terminates" pattern (term endpoint).
    Given: head simulation result `hsim_s_term`/`hsim_s_cf`, head terminates
    at `ρ₁` with src trace, and tail simulation result `hsim_ss_term`.  Lifts
    to a target result for `s :: ss` reaching `.terminal ρ'`. -/
private theorem block_corr_cons_term_head_term
    {σ_head_tgt σ_tail_tgt : LoopElimState}
    {s : Statement} {ss : Statements}
    {ρ₀ ρ₁ ρ' : Env Expression}
    (hterm_s : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (hreach_ss : CoreStar π φ (.stmts ss ρ₁) (.terminal ρ'))
    (hsim_s_term : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁) →
      Transform.CanFail (LangCore π φ) (stmtResult σ_head_tgt s) ρ₀ ∨
      (ρ₁.hasFailure = Bool.false →
        CoreStar π φ (.stmt (stmtResult σ_head_tgt s) ρ₀) (.terminal ρ₁)))
    (hsim_s_cf : Transform.CanFail (LangCore π φ) s ρ₀ →
      Transform.CanFail (LangCore π φ) (stmtResult σ_head_tgt s) ρ₀)
    (hsim_ss_term : ∀ ρ_e, CoreStar π φ (.stmts ss ρ₁) (.terminal ρ_e) →
      CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ_tail_tgt ss) ρ₁ ∨
      (ρ_e.hasFailure = Bool.false →
        CoreStar π φ (.stmts (blockResult σ_tail_tgt ss) ρ₁) (.terminal ρ_e))) :
    CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (stmtResult σ_head_tgt s ::
        blockResult σ_tail_tgt ss) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ (.stmts (stmtResult σ_head_tgt s ::
        blockResult σ_tail_tgt ss) ρ₀) (.terminal ρ')) := by
  match hsim_s_term hterm_s with
  | .inl hcf_s =>
    exact .inl (Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert (stmtResult σ_head_tgt s) _ ρ₀ hcf_s)
  | .inr hok_s =>
    by_cases hnf₁ : ρ₁.hasFailure = Bool.true
    · refine .inl ?_
      have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
        ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
      exact Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert _ _ ρ₀ (hsim_s_cf hcf_src_s)
    · have hnf₁' : ρ₁.hasFailure = Bool.false := by
        cases h : ρ₁.hasFailure <;> simp_all
      have htgt_s := hok_s hnf₁'
      match hsim_ss_term ρ' hreach_ss with
      | .inl hcf_ss =>
        refine .inl ?_
        obtain ⟨cfg2, hf2, hr2⟩ := hcf_ss
        refine ⟨cfg2, hf2, ?_⟩
        exact ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
            (stmtResult σ_head_tgt s) (blockResult σ_tail_tgt ss) ρ₀ ρ₁ htgt_s)
          hr2
      | .inr hok_ss =>
        refine .inr (fun hnf => ?_)
        have hnf_ss := hok_ss hnf
        exact ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
            (stmtResult σ_head_tgt s) (blockResult σ_tail_tgt ss) ρ₀ ρ₁ htgt_s)
          hnf_ss

/-- Block-corr cons-step "head-terminates" pattern (exit endpoint).  Same
    shape as `block_corr_cons_term_head_term` but with the tail trace
    leading to `.exiting`. -/
private theorem block_corr_cons_exit_head_term
    {σ_head_tgt σ_tail_tgt : LoopElimState}
    {s : Statement} {ss : Statements}
    {ρ₀ ρ₁ ρ' : Env Expression} {lbl : String}
    (hterm_s : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (hexit_ss : CoreStar π φ (.stmts ss ρ₁) (.exiting lbl ρ'))
    (hsim_s_term : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁) →
      Transform.CanFail (LangCore π φ) (stmtResult σ_head_tgt s) ρ₀ ∨
      (ρ₁.hasFailure = Bool.false →
        CoreStar π φ (.stmt (stmtResult σ_head_tgt s) ρ₀) (.terminal ρ₁)))
    (hsim_s_cf : Transform.CanFail (LangCore π φ) s ρ₀ →
      Transform.CanFail (LangCore π φ) (stmtResult σ_head_tgt s) ρ₀)
    (hsim_ss_exit : ∀ ρ_e, CoreStar π φ (.stmts ss ρ₁) (.exiting lbl ρ_e) →
      CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ_tail_tgt ss) ρ₁ ∨
      (ρ_e.hasFailure = Bool.false →
        CoreStar π φ (.stmts (blockResult σ_tail_tgt ss) ρ₁) (.exiting lbl ρ_e))) :
    CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (stmtResult σ_head_tgt s ::
        blockResult σ_tail_tgt ss) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ (.stmts (stmtResult σ_head_tgt s ::
        blockResult σ_tail_tgt ss) ρ₀) (.exiting lbl ρ')) := by
  match hsim_s_term hterm_s with
  | .inl hcf_s =>
    exact .inl (Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert _ _ ρ₀ hcf_s)
  | .inr hok_s =>
    by_cases hnf₁ : ρ₁.hasFailure = Bool.true
    · refine .inl ?_
      have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
        ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
      exact Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert _ _ ρ₀ (hsim_s_cf hcf_src_s)
    · have hnf₁' : ρ₁.hasFailure = Bool.false := by
        cases h : ρ₁.hasFailure <;> simp_all
      have htgt_s := hok_s hnf₁'
      match hsim_ss_exit ρ' hexit_ss with
      | .inl hcf_ss =>
        refine .inl ?_
        obtain ⟨cfg2, hf2, hr2⟩ := hcf_ss
        refine ⟨cfg2, hf2, ?_⟩
        exact ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
            (stmtResult σ_head_tgt s) (blockResult σ_tail_tgt ss) ρ₀ ρ₁ htgt_s)
          hr2
      | .inr hok_ss =>
        refine .inr (fun hnf => ?_)
        have hnf_ss := hok_ss hnf
        exact ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
            (stmtResult σ_head_tgt s) (blockResult σ_tail_tgt ss) ρ₀ ρ₁ htgt_s)
          hnf_ss

/-- Block-CF cons-step "head-terminates" pattern.  After
    `seq_canfail_prop` returns the `.inr` branch (head terminates at `ρ₁`,
    tail can fail), this helper folds the dichotomy on `hsim_s_term`
    (head simulation result) into a single `CanFailBlock` for the cons. -/
private theorem block_cf_cons_head_term
    {σ_head_tgt σ_tail_tgt : LoopElimState}
    {s : Statement} {ss : Statements}
    {ρ₀ ρ₁ : Env Expression}
    (hterm_s : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (hcf_tail : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) ss ρ₁)
    (hsim_s_term : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁) →
      Transform.CanFail (LangCore π φ) (stmtResult σ_head_tgt s) ρ₀ ∨
      (ρ₁.hasFailure = Bool.false →
        CoreStar π φ (.stmt (stmtResult σ_head_tgt s) ρ₀) (.terminal ρ₁)))
    (hsim_s_cf : Transform.CanFail (LangCore π φ) s ρ₀ →
      Transform.CanFail (LangCore π φ) (stmtResult σ_head_tgt s) ρ₀)
    (hsim_ss_cf : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) ss ρ₁ →
      CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ_tail_tgt ss) ρ₁) :
    CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (stmtResult σ_head_tgt s ::
      blockResult σ_tail_tgt ss) ρ₀ := by
  match hsim_s_term hterm_s with
  | .inl hcf_s =>
    exact Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert (stmtResult σ_head_tgt s)
      (blockResult σ_tail_tgt ss) ρ₀ hcf_s
  | .inr hok_s =>
    by_cases hnf₁ : ρ₁.hasFailure = Bool.true
    · have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
        ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
      exact Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert (stmtResult σ_head_tgt s)
        (blockResult σ_tail_tgt ss) ρ₀ (hsim_s_cf hcf_src_s)
    · have hnf₁' : ρ₁.hasFailure = Bool.false := by
        cases h : ρ₁.hasFailure <;> simp_all
      have htgt_s := hok_s hnf₁'
      have ⟨kcfg2, hkf2, hkstar2⟩ := hsim_ss_cf hcf_tail
      exact Transform.canFail_tail_to_block (EvalCommand π φ) (EvalPureFunc φ) (stmtResult σ_head_tgt s)
        (blockResult σ_tail_tgt ss) ρ₀ ρ₁ htgt_s ⟨kcfg2, hkf2, hkstar2⟩

/-- VC1-failure helper: when `hfib_eq` decomposes `first_iter_body` as
    asserts ++ assumes (per `stmtResult_loop_struct`), some invariant evaluates
    to ff at ρ₀, and ρ₀ is failure-free, the assert at the failing invariant
    canFails — and the failure lifts through the inner-block + outer-block
    wrappers to a CanFail on the full transformed loop. -/
private theorem loop_vc1_failure_canFail
    {σ : LoopElimState}
    {inv : List (String × Expression.Expr)}
    {first_iter_body : Statements}
    {loop_label first_iter_label : String}
    {ite_tail : Statements}
    {md : MetaData Expression}
    {ρ₀ : Env Expression}
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hinv_bool : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt ∨
                              ρ₀.eval ρ₀.store le.2 = some HasBool.ff)
    (hsome_ff : ∃ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.ff)
    (hfib_eq : first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md))) :
    Transform.CanFail (LangCore π φ)
      (.block loop_label
        (.block first_iter_label first_iter_body {} :: ite_tail) {}) ρ₀ := by
  let loop_num := (StringGenState.gen "loop" σ.gen).fst
  let invSuffix : Nat → String → String := fun i lbl =>
    if lbl.isEmpty then toString i else s!"{i}_{lbl}"
  let mkAssertLabel : Nat → String → String := fun i lbl =>
    s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
  let mkAssumeLabel : Nat → String → String := fun i lbl =>
    s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
  let asserts : Statements := inv.mapIdx fun i le =>
    Stmt.cmd (HasPassiveCmds.assert (P := Expression)
      (mkAssertLabel i le.1) le.2 md)
  let assumes : Statements := inv.mapIdx fun i le =>
    Stmt.cmd (HasPassiveCmds.assume (P := Expression)
      (mkAssumeLabel i le.1) le.2 md)
  have hcf_asserts : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) asserts ρ₀ :=
    stmts_mapIdx_assert_canFail π φ inv ρ₀ md mkAssertLabel hwfb
      hinv_bool hsome_ff
  have hcf_fib : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (asserts ++ assumes) ρ₀ :=
    Transform.canFailBlock_append_left (EvalCommand π φ) (EvalPureFunc φ) asserts assumes ρ₀ hcf_asserts
  have hfib : first_iter_body = asserts ++ assumes := hfib_eq
  have hcf_first_block : Transform.CanFail (LangCore π φ)
      (.block first_iter_label first_iter_body {}) ρ₀ := by
    rw [hfib]
    exact Transform.canFailBlock_to_canFail_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert first_iter_label _ {} ρ₀ hcf_fib
  exact Transform.canFailBlock_to_canFail_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert loop_label _ {} ρ₀
    (Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
      (.block first_iter_label first_iter_body {}) _ ρ₀ hcf_first_block)

/-! ### Loop simulation helpers

These three helpers carry the lemmas for the loop case of the
mutual simulation.  Extracting them keeps the body of `simulation` itself
small enough to be edited by agents without consuming excessive context.

Each helper is intentionally self-contained: none of them uses the outer
induction hypothesis (`ih`) or size variable `n`.  The all-tt branch of
the loop case is purely a property of the source semantics (under
`hreach`/`hreach_inner`) and the structural target produced by
`stmtResult_loop_struct`.

The first helper closes the `≥1-iter all-tt` branch of the loop terminal
case (after the outer `refine .inr` commits the result to a target trace).
The second helper covers the entire loop exit-branch case.  The third
helper covers the all-tt branch of the loop CanFail-preservation case. -/

/-- Loop zero-iter terminal-equality: when `ρ₀` is failure-free, `ρ'` is
    failure-free, and `ρ'` is the env produced by `step_loop_*_exit` (i.e.
    `{ρ₀ with hasFailure := ρ₀.hasFailure || b}` with `b` unconstrained but
    `hrest` is `.refl`), then `ρ' = ρ₀`. -/
private theorem loop_zero_iter_ρ'_eq_ρ₀
    {ρ₀ ρ' : Env Expression}
    {b₀ : Bool}
    (hrest : ReflTrans (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.terminal { ρ₀ with hasFailure := ρ₀.hasFailure || b₀ }) (.terminal ρ'))
    (hnf₀ : ρ₀.hasFailure = Bool.false)
    (hnf'' : ρ'.hasFailure = Bool.false) :
    ρ' = ρ₀ := by
  have hρ'_raw : ∃ b : Bool, ρ' = { ρ₀ with hasFailure := ρ₀.hasFailure || b } := by
    cases hrest with
    | refl _ => exact ⟨b₀, rfl⟩
    | step _ _ _ h _ => cases h
  obtain ⟨b, hraw⟩ := hρ'_raw
  rw [hraw]
  have hb_eq : b = Bool.false := by
    cases b
    · rfl
    · exfalso
      have : ρ'.hasFailure = Bool.true := by
        rw [hraw, hnf₀]; rfl
      rw [hnf''] at this; cases this
  subst hb_eq
  exact env_or_false_eq ρ₀

/-- First-iter-block runs to terminal: given `hall_tt` (every invariant
    evaluates to `tt` at `ρ₀`) and `hfib_eq` (the structural equation that
    `first_iter_body` is the asserts++assumes mapIdx pair), produce a trace
    `(.stmts first_iter_body ρ₀) ⇒* (.terminal ρ₀)`.

    Used in all three loop terminal/CF helpers under the all-tt branch. -/
private theorem loop_first_iter_body_terminal
    {σ : LoopElimState}
    {inv : List (String × Expression.Expr)}
    {first_iter_body : Statements}
    {md : MetaData Expression}
    {ρ₀ : Env Expression}
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    (hfib_eq : first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md))) :
    CoreStar π φ (.stmts first_iter_body ρ₀) (.terminal ρ₀) := by
  let loop_num := (StringGenState.gen "loop" σ.gen).fst
  let invSuffix : Nat → String → String := fun i lbl =>
    if lbl.isEmpty then toString i else s!"{i}_{lbl}"
  let mkAssertLabel : Nat → String → String := fun i lbl =>
    s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
  let mkAssumeLabel : Nat → String → String := fun i lbl =>
    s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
  have h_asserts :=
    stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt
  have h_assumes :=
    stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt
  rw [hfib_eq]
  exact stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀ h_asserts h_assumes

/-- Loop zero-iter target trace builder: given `hall_tt` and the structural
    target shape, produce a trace through the outer block that terminates
    at `ρ₀`.  The body of the ite is the empty else block; the ite step
    constructor is provided as `h_ite`.  Used from both det and nondet
    zero-iter branches. -/
private theorem loop_zero_iter_target_trace
    {first_iter_label loop_label : String}
    {first_iter_body then_branch : Statements}
    {ρ₀ : Env Expression}
    {c : ExprOrNondet Expression}
    (hfib_run : CoreStar π φ (.stmts first_iter_body ρ₀) (.terminal ρ₀))
    (h_ite : CoreStar π φ (.stmt (.ite c then_branch [] {}) ρ₀) (.terminal ρ₀)) :
    CoreStar π φ
      (.stmt (.block loop_label
        [.block first_iter_label first_iter_body {},
         .ite c then_branch [] {}] {}) ρ₀)
      (.terminal ρ₀) := by
  have h_fib_block : CoreStar π φ
      (.stmt (.block first_iter_label first_iter_body {}) ρ₀)
      (.terminal ρ₀) := by
    have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) first_iter_label
      first_iter_body {} ρ₀ ρ₀ hfib_run
    rw [projectStore_self_env] at h; exact h
  have h_stmts : CoreStar π φ (.stmts [.block first_iter_label
      first_iter_body {}, .ite c then_branch [] {}] ρ₀)
      (.terminal ρ₀) :=
    ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
        _ _ ρ₀ ρ₀ h_fib_block)
      (ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
          _ _ ρ₀ ρ₀ h_ite)
        (.step _ _ _ .step_stmts_nil (.refl _)))
  have h_outer := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) loop_label _ {} ρ₀ ρ₀ h_stmts
  rw [projectStore_self_env] at h_outer
  exact h_outer

/-- Combined "loop terminal zero-iter" closer: from a refl-tail step (so
    `ρ' = ρ₀`), all-tt invariants, and an ite-trace at ρ₀, produce the
    full term-correctness disjunct as `Or.inr`.  This is the part shared by
    both the det (`step_loop_exit`) and nondet (`step_loop_nondet_exit`)
    sub-cases of the loop terminal branch. -/
private theorem loop_zero_iter_term_branch
    {σ : LoopElimState}
    {inv : List (String × Expression.Expr)}
    {first_iter_body then_branch : Statements}
    {first_iter_label loop_label : String}
    {md : MetaData Expression}
    {ρ₀ ρ' : Env Expression}
    {b₀ : Bool}
    {c : ExprOrNondet Expression}
    {ite_tail_blocks : Statements}
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hnf₀ : ρ₀.hasFailure = Bool.false)
    (hnf'' : ρ'.hasFailure = Bool.false)
    (hrest : ReflTrans (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.terminal { ρ₀ with hasFailure := ρ₀.hasFailure || b₀ }) (.terminal ρ'))
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    (hfib_eq : first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)))
    (h_ite : CoreStar π φ (.stmt (.ite c then_branch [] {}) ρ₀) (.terminal ρ₀)) :
    Transform.CanFail (LangCore π φ) (.block loop_label
      (.block first_iter_label first_iter_body {} :: ite_tail_blocks) {}) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ
        (.stmt (.block loop_label
          [.block first_iter_label first_iter_body {},
           .ite c then_branch [] {}] {}) ρ₀)
        (.terminal ρ')) := by
  have hρ'_eq : ρ' = ρ₀ :=
    loop_zero_iter_ρ'_eq_ρ₀ π φ hrest hnf₀ hnf''
  rw [hρ'_eq]
  refine .inr (fun _ => ?_)
  have h_fib_run :=
    loop_first_iter_body_terminal π φ hwfb hall_tt hfib_eq
  exact loop_zero_iter_target_trace π φ h_fib_run h_ite

/-- When a loop terminates without failure, all invariants evaluate to `tt`.
    Uses trace-length induction (same as `stmt_compound_terminal_preserves_isNone`). -/
private theorem loop_terminal_inv_all_tt
    {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ' : Env Expression}
    (hreach : CoreStar π φ (.stmt (.loop guardE measure inv body md) ρ₀) (.terminal ρ'))
    (hnf'' : ρ'.hasFailure = Bool.false) :
    ∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt := by
  have hstarT := reflTrans_to_T hreach
  suffices ∀ (n_steps : Nat) (ρ₀ ρ' : Env Expression),
      ∀ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt (.loop guardE measure inv body md) ρ₀) (.terminal ρ')),
        h.len ≤ n_steps → ρ'.hasFailure = Bool.false →
        ∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt by
    exact this hstarT.len ρ₀ ρ' hstarT (Nat.le_refl _) hnf''
  clear hreach hstarT ρ₀ ρ' hnf''
  intro n_steps
  induction n_steps with
  | zero =>
    intro ρ₀ ρ' hT hlen
    match hT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ k ih =>
    intro ρ₀ ρ' hT hlen hnf' le hle
    match hT with
    | .step _ _ _ hstep1 hrest =>
      cases hstep1 with
      | step_loop_exit hguard hinv_bool hinv_iff _ =>
        match hrest with
        | .refl _ =>
          have hno_ff : ¬∃ le' ∈ inv, ρ₀.eval ρ₀.store le'.2 = some HasBool.ff := by
            intro ⟨le', hle', hff'⟩
            have hinv_true := hinv_iff.mpr ⟨le', hle', hff'⟩
            simp [hinv_true, Bool.or_true] at hnf'
          rcases hinv_bool le hle with htt | hff
          · exact htt
          · exact absurd ⟨le, hle, hff⟩ hno_ff
        | .step _ _ _ h _ => exact nomatch h
      | step_loop_nondet_exit hinv_bool hinv_iff =>
        match hrest with
        | .refl _ =>
          have hno_ff : ¬∃ le' ∈ inv, ρ₀.eval ρ₀.store le'.2 = some HasBool.ff := by
            intro ⟨le', hle', hff'⟩
            have hinv_true := hinv_iff.mpr ⟨le', hle', hff'⟩
            simp [hinv_true, Bool.or_true] at hnf'
          rcases hinv_bool le hle with htt | hff
          · exact htt
          · exact absurd ⟨le, hle, hff⟩ hno_ff
        | .step _ _ _ h _ => exact nomatch h
      | step_loop_enter _ _ _ _ _ =>
        have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
        have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
        match hT_tail, hlen_split with
        | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
          have hlen_rest' : hrest'.len < hrest.len := by
            simp only [ReflTransT.len] at hlen_split ⊢; omega
          have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
          have hρ_eq : ρ_mid' = ρ' := by
            match hT_nil with
            | .step _ _ _ .step_stmts_nil hrr =>
              match hrr with
              | .refl _ => rfl
              | .step _ _ _ h _ => exact nomatch h
          subst hρ_eq
          have hlen_loop : hT_loop'.len ≤ k := by omega
          exact ih ρ_mid ρ_mid' hT_loop' hlen_loop hnf' le hle
      | step_loop_nondet_enter _ _ =>
        have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
        have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
        match hT_tail, hlen_split with
        | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
          have hlen_rest' : hrest'.len < hrest.len := by
            simp only [ReflTransT.len] at hlen_split ⊢; omega
          have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
          have hρ_eq : ρ_mid' = ρ' := by
            match hT_nil with
            | .step _ _ _ .step_stmts_nil hrr =>
              match hrr with
              | .refl _ => rfl
              | .step _ _ _ h _ => exact nomatch h
          subst hρ_eq
          have hlen_loop : hT_loop'.len ≤ k := by omega
          exact ih ρ_mid ρ_mid' hT_loop' hlen_loop hnf' le hle

/-- Terminal loop trace projects store idempotently. -/
private theorem loop_terminal_projectStore_id
    {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ' : Env Expression}
    (hreach : CoreStar π φ (.stmt (.loop guardE measure inv body md) ρ₀) (.terminal ρ')) :
    projectStore ρ₀.store ρ'.store = ρ'.store := by
  apply projectStore_id
  intro x hxne hne₀
  have hnone₀ : (ρ₀.store x).isNone := Option.isNone_iff_eq_none.mpr hne₀
  have hnone' : (ρ'.store x).isNone :=
    stmt_compound_terminal_preserves_isNone (π := π) (φ := φ) hreach
      (fun _ heq => by simp [Statement] at heq)
      (fun _ _ heq => by simp [Statement] at heq)
      x hnone₀
  exact hxne (Option.isNone_iff_eq_none.mp hnone')

/-- Decompose `.block .none σ inner` reaching terminal at the `Prop` level. -/
private theorem block_none_reaches_terminal_prop
    {inner : CC} {σ_parent : SemanticStore Expression}
    {e_parent : SemanticEval Expression} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block .none σ_parent e_parent inner) (.terminal ρ')) :
    ∃ ρ_inner, CoreStar π φ inner (.terminal ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } := by
  have hstarT := reflTrans_to_T hstar
  have ⟨ρ_inner, ⟨hT, _⟩, heq⟩ := blockT_none_reaches_terminal π φ hstarT
  exact ⟨ρ_inner, reflTransT_to_prop hT, heq⟩

/-- Decompose `.seq (.block .none σ inner) [loop_stmt]` reaching terminal. -/
private theorem seq_block_loop_terminal_decompose
    {inner : CC} {σ_parent : SemanticStore Expression}
    {e_parent : SemanticEval Expression}
    {loop_stmt : Statement} {ρ' : Env Expression}
    (hstar : CoreStar π φ
      (.seq (.block .none σ_parent e_parent inner) [loop_stmt]) (.terminal ρ')) :
    ∃ ρ_mid, CoreStar π φ (.block .none σ_parent e_parent inner) (.terminal ρ_mid) ∧
      CoreStar π φ (.stmts [loop_stmt] ρ_mid) (.terminal ρ') ∧
      ∃ ρ_inner, CoreStar π φ inner (.terminal ρ_inner) ∧
        ρ_mid = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } := by
  have ⟨ρ_mid, h_block, h_tail⟩ :=
    seq_reaches_terminal (P := Expression) (EvalCmd := EvalCommand π φ)
      (extendEval := EvalPureFunc φ) hstar
  have ⟨ρ_inner, h_inner, heq⟩ := block_none_reaches_terminal_prop π φ h_block
  exact ⟨ρ_mid, h_block, h_tail, ρ_inner, h_inner, heq⟩

/-- When a det-guard loop terminates without failure, the guard is `ff` at ρ'. -/
private theorem loop_det_terminal_guard_ff
    {g : Expression.Expr}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ' : Env Expression}
    (hreach : CoreStar π φ (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ'))
    (hnf'' : ρ'.hasFailure = Bool.false) :
    ρ'.eval ρ'.store g = some HasBool.ff := by
  have hstarT := reflTrans_to_T hreach
  suffices ∀ (n_steps : Nat) (ρ₀ ρ' : Env Expression),
      ∀ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ')),
        h.len ≤ n_steps → ρ'.hasFailure = Bool.false →
        ρ'.eval ρ'.store g = some HasBool.ff by
    exact this hstarT.len ρ₀ ρ' hstarT (Nat.le_refl _) hnf''
  clear hreach hstarT ρ₀ ρ' hnf''
  intro n_steps
  induction n_steps with
  | zero =>
    intro ρ₀ ρ' hT hlen
    match hT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ k ih =>
    intro ρ₀ ρ' hT hlen hnf'
    match hT with
    | .step _ _ _ hstep1 hrest =>
      cases hstep1 with
      | step_loop_exit hguard _ _ _ =>
        match hrest with
        | .refl _ => exact hguard
        | .step _ _ _ h _ => exact nomatch h
      | step_loop_enter _ _ _ _ _ =>
        have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
        have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
        match hT_tail, hlen_split with
        | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
          have hlen_rest' : hrest'.len < hrest.len := by
            simp only [ReflTransT.len] at hlen_split ⊢; omega
          have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
          have hρ_eq : ρ_mid' = ρ' := by
            match hT_nil with
            | .step _ _ _ .step_stmts_nil hrr =>
              match hrr with
              | .refl _ => rfl
              | .step _ _ _ h _ => exact nomatch h
          subst hρ_eq
          have hlen_loop : hT_loop'.len ≤ k := by omega
          exact ih ρ_mid ρ_mid' hT_loop' hlen_loop hnf'

/-- A loop terminal trace preserves the evaluator unconditionally.

    The loop body is wrapped in `.block .none ρ.store ρ.eval (.stmts body ...)`,
    and `step_block_done` restores the evaluator to the parent's snapshot.  So
    each iteration's body (no matter what it does, including funcDecls) cannot
    affect the eval seen at the loop's outer config. -/
private theorem loop_terminal_eval_preserved
    {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ' : Env Expression}
    (hreach : CoreStar π φ
        (.stmt (.loop guardE measure inv body md) ρ₀) (.terminal ρ')) :
    ρ'.eval = ρ₀.eval := by
  have hstarT := reflTrans_to_T hreach
  suffices ∀ (n_steps : Nat) (ρ₀ ρ' : Env Expression),
      ∀ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt (.loop guardE measure inv body md) ρ₀) (.terminal ρ')),
        h.len ≤ n_steps → ρ'.eval = ρ₀.eval by
    exact this hstarT.len ρ₀ ρ' hstarT (Nat.le_refl _)
  clear hreach hstarT ρ₀ ρ'
  intro n_steps
  induction n_steps with
  | zero =>
    intro ρ₀ ρ' hT hlen
    match hT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ k ih =>
    intro ρ₀ ρ' hT hlen
    match hT with
    | .step _ _ _ hstep1 hrest =>
      cases hstep1 with
      | step_loop_exit _ _ _ _ =>
        match hrest with
        | .refl _ => rfl
        | .step _ _ _ h _ => exact nomatch h
      | step_loop_nondet_exit _ _ =>
        match hrest with
        | .refl _ => rfl
        | .step _ _ _ h _ => exact nomatch h
      | step_loop_enter _ _ _ _ _ =>
        have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
        match hT_tail, hlen_split with
        | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
          have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
          have hρ_eq : ρ_mid' = ρ' := by
            match hT_nil with
            | .step _ _ _ .step_stmts_nil hrr =>
              match hrr with
              | .refl _ => rfl
              | .step _ _ _ h _ => exact nomatch h
          subst hρ_eq
          have hlen_loop : hT_loop'.len ≤ k := by
            simp only [ReflTransT.len] at hlen hlen_split hlen_split' ⊢; omega
          have hev_loop : ρ_mid'.eval = ρ_mid.eval := ih ρ_mid ρ_mid' hT_loop' hlen_loop
          have ⟨_, _, heq_mid⟩ := blockT_none_reaches_terminal π φ hT_block
          have hev_mid : ρ_mid.eval = ρ₀.eval := by rw [heq_mid]
          rw [hev_loop, hev_mid]
      | step_loop_nondet_enter _ _ =>
        have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
        match hT_tail, hlen_split with
        | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
          have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
          have hρ_eq : ρ_mid' = ρ' := by
            match hT_nil with
            | .step _ _ _ .step_stmts_nil hrr =>
              match hrr with
              | .refl _ => rfl
              | .step _ _ _ h _ => exact nomatch h
          subst hρ_eq
          have hlen_loop : hT_loop'.len ≤ k := by
            simp only [ReflTransT.len] at hlen hlen_split hlen_split' ⊢; omega
          have hev_loop : ρ_mid'.eval = ρ_mid.eval := ih ρ_mid ρ_mid' hT_loop' hlen_loop
          have ⟨_, _, heq_mid⟩ := blockT_none_reaches_terminal π φ hT_block
          have hev_mid : ρ_mid.eval = ρ₀.eval := by rw [heq_mid]
          rw [hev_loop, hev_mid]

/-- Common bundle used throughout the loop-iteration extraction proofs:
    given a loop's `InitEnvWF` (so its invariants' free variables are known
    defined in `ρ₀`), and an env `ρ` whose store has the same `isSome`-domain
    as `ρ₀`, the projected store `projectStore ρ.store ρ_inner.store` agrees
    with `ρ_inner.store` on every variable read by an invariant `le ∈ inv`,
    and consequently `ρ_inner.eval` evaluates `le.2` identically under either
    store. -/
private theorem inv_eval_agree_under_projectStore
    {reserved : List String} {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ ρ_inner : Env Expression}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (hsame_ρ : ∀ x, (ρ.store x).isSome ↔ (ρ₀.store x).isSome)
    {le : String × Expression.Expr} (hle : le ∈ inv) :
    ρ₀.eval (projectStore ρ.store ρ_inner.store) le.2
      = ρ₀.eval ρ_inner.store le.2 := by
  have hagree_vars : ∀ x ∈ HasVarsPure.getVars le.2,
      projectStore ρ.store ρ_inner.store x = ρ_inner.store x := by
    intro x hx_in_vars
    simp only [projectStore]
    have hdu := hswf.defUseOk
    simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
    obtain ⟨⟨⟨_, _⟩, hinv_all⟩, _⟩ := hdu
    have hx_mem : x ∈ (inv.flatMap fun lp => HasVarsPure.getVars lp.2) :=
      List.mem_flatMap.mpr ⟨le, hle, hx_in_vars⟩
    have hdef_x : ((ρ₀.store x).isSome) = Bool.true :=
      (List.all_eq_true.mp hinv_all) x hx_mem
    rw [if_pos ((hsame_ρ x).mpr hdef_x)]
  exact hswf.exprCongr le.2
    (projectStore ρ.store ρ_inner.store) ρ_inner.store hagree_vars

/-- Without `noFuncDecl`, `ρ_inner.eval` may differ from `ρ₀.eval` (the body
    can introduce funcDecls that extend the eval).  However, if `e`'s free
    variables are all defined in `ρ₀.store`, the body's `defUseWellFormed`
    invariant guarantees they are disjoint from any funcDecl introduced in
    the body, hence `ρ_inner.eval σ' e = ρ₀.eval σ' e` for any store `σ'`.

    This is the per-expression replacement for the old `heval_inner :
    ρ_inner.eval = ρ₀.eval` (which only held under `noFuncDecl`). -/
private theorem body_eval_eq_init_on_expr
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (hwf_ext : WFEvalExtension φ)
    {reserved : List String} {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ_inner : Env Expression}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (h_inner : CoreStar π φ
      (.stmts body { ρ₀ with hasFailure := ρ₀.hasFailure }) (.terminal ρ_inner))
    (σ' : SemanticStore Expression) (e : Expression.Expr)
    (he : ∀ n ∈ HasVarsPure.getVars (P := Expression) e, (ρ₀.store n).isSome) :
    ρ_inner.eval σ' e = ρ₀.eval σ' e := by
  have hdu := hswf.defUseOk
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  have hdu_body : Block.defUseWellFormed (fun n => (ρ₀.store n).isSome) body = Bool.true :=
    hdu.2
  have heta : ({ ρ₀ with hasFailure := ρ₀.hasFailure } : Env Expression) = ρ₀ := by
    cases ρ₀; rfl
  rw [heta] at h_inner
  exact block_preserves_eval_via_defUseOk Expression (EvalCommand π φ) (EvalPureFunc φ)
    hwf_ext.toWFEvalExtension body ρ₀ ρ_inner _ hdu_body σ' e
    (fun n hn => he n hn) h_inner

/-- Variant of `body_eval_eq_init_on_expr` for an inv expression: the inv vars
    are already bounded by `defUseWellFormed`'s loop invariant clause. -/
private theorem body_eval_inv_preserved
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (hwf_ext : WFEvalExtension φ)
    {reserved : List String} {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ_inner : Env Expression}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (h_inner : CoreStar π φ
      (.stmts body { ρ₀ with hasFailure := ρ₀.hasFailure }) (.terminal ρ_inner))
    {le : String × Expression.Expr} (hle : le ∈ inv)
    (σ' : SemanticStore Expression) :
    ρ_inner.eval σ' le.2 = ρ₀.eval σ' le.2 := by
  have hdu := hswf.defUseOk
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  obtain ⟨⟨⟨_, _⟩, hinv_all⟩, _⟩ := hdu
  apply body_eval_eq_init_on_expr π φ hwf_ext hswf h_inner σ' le.2
  intro n hn
  have hx_mem : n ∈ (inv.flatMap fun lp => HasVarsPure.getVars lp.2) :=
    List.mem_flatMap.mpr ⟨le, hle, hn⟩
  have h := (List.all_eq_true.mp hinv_all) n hx_mem
  exact h

/-- More general variant: body runs from any `ρ_start` (not necessarily `ρ₀`),
    with the same `isSome`-domain.  This is the form needed when the body
    runs from an inner-iteration env. -/
private theorem body_eval_inv_preserved_from
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (hwf_ext : WFEvalExtension φ)
    {reserved : List String} {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ_start ρ_inner : Env Expression}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (hsame : ∀ x, (ρ_start.store x).isSome ↔ (ρ₀.store x).isSome)
    (h_inner : CoreStar π φ (.stmts body ρ_start) (.terminal ρ_inner))
    {le : String × Expression.Expr} (hle : le ∈ inv)
    (σ' : SemanticStore Expression) :
    ρ_inner.eval σ' le.2 = ρ_start.eval σ' le.2 := by
  have hdu := hswf.defUseOk
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  obtain ⟨⟨⟨_, _⟩, hinv_all⟩, hbody_du⟩ := hdu
  -- Reproject body's defUseOk to use `(ρ_start.store n).isSome` predicate.
  have hbody_du_start : Block.defUseWellFormed (fun n => (ρ_start.store n).isSome) body
      = Bool.true := by
    have hext : (fun n => (ρ_start.store n).isSome) = (fun n => (ρ₀.store n).isSome) := by
      funext n; exact (Bool.eq_iff_iff).mpr (hsame n)
    rw [hext]; exact hbody_du
  exact block_preserves_eval_via_defUseOk Expression (EvalCommand π φ) (EvalPureFunc φ)
    hwf_ext.toWFEvalExtension body ρ_start ρ_inner _ hbody_du_start σ' le.2
    (fun n hn => by
      have hx_mem : n ∈ (inv.flatMap fun lp => HasVarsPure.getVars lp.2) :=
        List.mem_flatMap.mpr ⟨le, hle, hn⟩
      have h := (List.all_eq_true.mp hinv_all) n hx_mem
      have := (hsame n).mpr h
      simpa using this)
    h_inner

/-- Variant of `body_eval_inv_preserved_from` where the body runs from
    `ρ_start` whose `eval` is `ρ₀.eval`.  Resulting equality on `ρ₀.eval`. -/
private theorem body_eval_inv_preserved_init
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (hwf_ext : WFEvalExtension φ)
    {reserved : List String} {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ_start ρ_inner : Env Expression}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (hsame : ∀ x, (ρ_start.store x).isSome ↔ (ρ₀.store x).isSome)
    (hstart_eval : ρ_start.eval = ρ₀.eval)
    (h_inner : CoreStar π φ (.stmts body ρ_start) (.terminal ρ_inner))
    {le : String × Expression.Expr} (hle : le ∈ inv)
    (σ' : SemanticStore Expression) :
    ρ_inner.eval σ' le.2 = ρ₀.eval σ' le.2 := by
  rw [body_eval_inv_preserved_from π φ hwf_ext hswf hsame h_inner hle σ', hstart_eval]

/-- Exiting variant of `body_eval_inv_preserved_from`. -/
private theorem body_eval_inv_preserved_exiting
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (hwf_ext : WFEvalExtension φ)
    {reserved : List String} {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ_start ρ_inner : Env Expression} {lbl : String}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (hsame : ∀ x, (ρ_start.store x).isSome ↔ (ρ₀.store x).isSome)
    (h_inner : CoreStar π φ (.stmts body ρ_start) (.exiting lbl ρ_inner))
    {le : String × Expression.Expr} (hle : le ∈ inv)
    (σ' : SemanticStore Expression) :
    ρ_inner.eval σ' le.2 = ρ_start.eval σ' le.2 := by
  have hdu := hswf.defUseOk
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  obtain ⟨⟨⟨_, _⟩, hinv_all⟩, hbody_du⟩ := hdu
  have hbody_du_start : Block.defUseWellFormed (fun n => (ρ_start.store n).isSome) body
      = Bool.true := by
    have hext : (fun n => (ρ_start.store n).isSome) = (fun n => (ρ₀.store n).isSome) := by
      funext n; exact (Bool.eq_iff_iff).mpr (hsame n)
    rw [hext]; exact hbody_du
  exact block_preserves_eval_via_defUseOk_exiting Expression (EvalCommand π φ) (EvalPureFunc φ)
    hwf_ext.toWFEvalExtension body ρ_start ρ_inner lbl _ hbody_du_start σ' le.2
    (fun n hn => by
      have hx_mem : n ∈ (inv.flatMap fun lp => HasVarsPure.getVars lp.2) :=
        List.mem_flatMap.mpr ⟨le, hle, hn⟩
      have h := (List.all_eq_true.mp hinv_all) n hx_mem
      have := (hsame n).mpr h
      simpa using this)
    h_inner

/-- Variant of `body_eval_inv_preserved_exiting` where the body runs from
    `ρ_start` whose `eval` is `ρ₀.eval`. -/
private theorem body_eval_inv_preserved_exiting_init
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (hwf_ext : WFEvalExtension φ)
    {reserved : List String} {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ_start ρ_inner : Env Expression} {lbl : String}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (hsame : ∀ x, (ρ_start.store x).isSome ↔ (ρ₀.store x).isSome)
    (hstart_eval : ρ_start.eval = ρ₀.eval)
    (h_inner : CoreStar π φ (.stmts body ρ_start) (.exiting lbl ρ_inner))
    {le : String × Expression.Expr} (hle : le ∈ inv)
    (σ' : SemanticStore Expression) :
    ρ_inner.eval σ' le.2 = ρ₀.eval σ' le.2 := by
  rw [body_eval_inv_preserved_exiting π φ hwf_ext hswf hsame h_inner hle σ', hstart_eval]

/-- Common pattern in loop-iteration extraction proofs: every variable in the
    `havoc_vars` list (those modified by the loop body but not defined within
    it) is already defined (`isSome`) in the initial environment `ρ₀`.  This
    follows from the loop's `InitEnvWF` condition. -/
private theorem havoc_vars_defined_of_init
    {reserved : List String}
    {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ : Env Expression}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (havoc_vars : List Expression.Ident)
    (hhavoc_def : havoc_vars = (Block.modifiedVars body).filter
      fun v => decide (¬ v ∈ Block.definedVars body Bool.false)) :
    ∀ x ∈ havoc_vars, (ρ₀.store x).isSome := by
  intro x hx
  rw [hhavoc_def] at hx
  have hmod : x ∈ Block.modifiedVars body := List.mem_filter.mp hx |>.1
  have hndef_body : x ∉ Block.definedVars body Bool.false := by
    have := (List.mem_filter.mp hx).2
    simp at this; exact this
  have htouched : x ∈ Stmt.touchedVars (.loop guardE measure inv body md) := by
    simp [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars]
    exact .inl hmod
  have hnotdef : x ∉ Stmt.definedVars (.loop guardE measure inv body md) Bool.false := by
    simp [Stmt.definedVars]; exact hndef_body
  exact hswf.readWritesDefined x htouched hnotdef

/-- Helper for `simulation`'s loop terminal case (`≥1-iter`, all-tt
    invariants branch).  Works directly on `stmtResult` so that the target
    encoding is concrete (not opaque existential). -/
private theorem simulation_loop_term_enter_case
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (σ : LoopElimState)
    (guardE : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guardE measure inv body md))
    (ρ₀ ρ' : Env Expression)
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (hreach : CoreStar π φ
        (.stmt (.loop guardE measure inv body md) ρ₀) (.terminal ρ'))
    (hnf'' : ρ'.hasFailure = Bool.false)
    (hnf₀ : ρ₀.hasFailure = Bool.false)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) :
    ∀ {hasInvFailure : Bool},
      hasInvFailure = Bool.false →
      CoreStar π φ
        (.seq (.block .none ρ₀.store ρ₀.eval
          (.stmts body
            ({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure } : Env Expression)))
          [.loop guardE measure inv body md])
        (.terminal ρ') →
      Transform.CanFail (LangCore π φ) (stmtResult σ (.loop guardE measure inv body md)) ρ₀ ∨
        (ρ'.hasFailure = Bool.false →
          CoreStar π φ (.stmt (stmtResult σ (.loop guardE measure inv body md)) ρ₀)
            (.terminal ρ')) := by
  intro hasInvFailure hib_eq hreach_inner
  subst hib_eq
  simp only [Bool.or_false] at hreach_inner
  -- Unfold stmtResult to get concrete target encoding
  simp only [stmtResult]
  have hok' := hok; unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guardE measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase,
      buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes,
      buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants,
      buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants,
      buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome,
      hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    repeat (first | contradiction | (split at h; skip))
    all_goals (first | contradiction | (
      dsimp only [StateT.pure, StateT.bind, StateT.map, ExceptT.bindCont,
        ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
        Functor.map, MonadStateOf.modifyGet, StateT.modifyGet, bumpStat,
        modify, genLoopNum] at h
      first
        | obtain ⟨rfl, rfl⟩ := h
        | (repeat (first | (split at h; skip) | contradiction)
           all_goals (first | contradiction | obtain ⟨rfl, rfl⟩ := h))))
    -- Case h_2: nondet guard (ExprOrNondet.nondet)
    case h_2 =>
      refine .inr (fun hnf_arg => ?_)
      -- Decompose the source inner trace: block(body) ; [loop] → terminal ρ'
      have ⟨ρ_mid, h_block_mid, h_tail_mid, ρ_inner, h_inner, heq_mid⟩ :=
        seq_block_loop_terminal_decompose π φ hreach_inner
      -- Key facts about ρ'
      have hall_tt' : ∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt :=
        loop_terminal_inv_all_tt π φ hreach hnf''
      have hproj_id : projectStore ρ₀.store ρ'.store = ρ'.store :=
        loop_terminal_projectStore_id π φ hreach
      -- eval is preserved by the loop terminal trace (block scoping)
      have heval_eq : ρ'.eval = ρ₀.eval :=
        loop_terminal_eval_preserved π φ hreach
      have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
      -- Rewrite hall_tt' in terms of ρ₀.eval
      have hall_tt'_eval₀ : ∀ le ∈ inv, ρ₀.eval ρ'.store le.2 = some HasBool.tt := by
        intro le hle; rw [← heval_eq]; exact hall_tt' le hle
      -- Step 1: Build first_iter_asserts trace
      -- The first_iter_asserts block has body = (assert_inv_mapIdx ++ assume_inv_mapIdx)
      -- and terminates at ρ₀ (asserts/assumes pass since hall_tt)
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      let mkAssertLabel : Nat → String → String := fun i lbl =>
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
      let mkAssumeLabel : Nat → String → String := fun i lbl =>
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
      have h_fib_run : CoreStar π φ
          (.stmts ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
            (mkAssertLabel i le.1) le.2 md)) ++
            (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
              (mkAssumeLabel i le.1) le.2 md))) ρ₀)
          (.terminal ρ₀) := by
        exact stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
          (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
          (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
      have h_fib_block : CoreStar π φ
          (.stmt (.block
            s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
            ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
              (mkAssertLabel i le.1) le.2 md)) ++
             (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
              (mkAssumeLabel i le.1) le.2 md)))
            ∅) ρ₀)
          (.terminal ρ₀) := by
        have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
          s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" _ ∅ ρ₀ ρ₀ h_fib_run
        rw [projectStore_self_env] at h; exact h
      -- Step 2: Build the ite nondet-true trace to terminal ρ'.
      -- The ite takes the nondet true branch, enters block .none ρ₀.store (.stmts then_stmts ρ₀),
      -- which terminates at ρ', and the outer projection gives ρ' since hproj_id.
      --
      -- Sub-goal: build a trace through the then-branch stmts to ρ'.
      -- The then-branch stmts are:
      --   arb_facts_block :: ([exit_havoc_block] ++ [] ++ exit_inv_assumes)
      -- For the arb_facts_block: havoc → assume → body → maintain_inv inside a named block.
      --   The block projects back to ρ₀ (identity havoc + body runs from ρ₀).
      -- For exit_havoc + assumes: havoc targets ρ'.store, assumes pass via hall_tt'_eval₀.
      --
      -- We define abbreviations for the sub-blocks.
      let havoc_vars := (Block.modifiedVars body).filter fun v =>
        decide (¬ v ∈ Block.definedVars body Bool.false)
      let havoc_stmts : Statements := havoc_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)
      let havoc_label := s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
      let arb_assumes_label := s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
      let mkArbAssumeLabel : Nat → String → String := fun i lbl =>
        s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lbl}"
      let arb_assumes_body : Statements :=
        [] ++ inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
          (mkArbAssumeLabel i le.1) le.2 md)
      let mkMaintainLabel : Nat → String → String := fun i lbl =>
        s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lbl}"
      let maintain_stmts : Statements :=
        inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkMaintainLabel i le.1) le.2 md)
      let arb_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
      let arb_facts_body : Statements :=
        [.block havoc_label havoc_stmts ∅,
         .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []
      let mkExitAssumeLabel : Nat → String → String := fun i lbl =>
        s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lbl}"
      let exit_inv_assumes : Statements :=
        inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
          (mkExitAssumeLabel i le.1) le.2 md)
      -- The full then-branch statements:
      --   [arb_facts_block] ++ [exit_havoc_block] ++ [] ++ exit_inv_assumes
      -- Build the inner trace through then-stmts to ρ'.
      -- This is the hardest part: arb_facts_block terminates at some intermediate state
      -- (projected back to ρ₀ since it's a named block), then exit havoc targets ρ'.store,
      -- then exit assumes pass.
      suffices h_then : CoreStar π φ
          (.stmts ((.block arb_facts_label arb_facts_body ∅) ::
            (([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes)))
            ρ₀) (.terminal ρ') from by
        -- Build the ite trace
        have h_ite_inner : CoreStar π φ
            (.block .none ρ₀.store ρ₀.eval (.stmts
              ((.block arb_facts_label arb_facts_body ∅) ::
                (([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes)))
              ρ₀))
            (.terminal { ρ' with store := projectStore ρ₀.store ρ'.store, eval := ρ₀.eval }) :=
          ReflTrans_Transitive _ _ _ _
            (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
              _ _ .none ρ₀.store ρ₀.eval h_then)
            (.step _ _ _ .step_block_done (.refl _))
        have hproj_env : ({ ρ' with store := projectStore ρ₀.store ρ'.store, eval := ρ₀.eval } : Env Expression) = ρ' := by
          rw [hproj_id, ← heval_eq]
        rw [hproj_env] at h_ite_inner
        have h_ite : CoreStar π φ
            (.stmt (.ite .nondet
              ((.block arb_facts_label arb_facts_body ∅) ::
                (([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes)))
              [] ∅) ρ₀)
            (.terminal ρ') :=
          .step _ _ _ .step_ite_nondet_true h_ite_inner
        -- Chain first_iter_block + ite into stmts
        have h_stmts : CoreStar π φ
            (.stmts [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
              ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
               (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md))) ∅,
              .ite .nondet
                ((.block arb_facts_label arb_facts_body ∅) ::
                  (([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes)))
                [] ∅] ρ₀)
            (.terminal ρ') :=
          ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_fib_block)
            (ReflTrans_Transitive _ _ _ _
              (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ' h_ite)
              (.step _ _ _ .step_stmts_nil (.refl _)))
        -- Wrap in outer block
        have h_outer := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
          s!"{loopElimBlockPrefix}loop_{loop_num}" _ ∅ ρ₀ ρ' h_stmts
        rw [hproj_id] at h_outer
        have henv_eq : ({ ρ' with store := ρ'.store, eval := ρ₀.eval } : Env Expression) = ρ' := by
          rw [← heval_eq]
        rw [henv_eq] at h_outer
        exact h_outer
      -- Now prove h_then: trace through then-stmts to ρ'
      -- Step 2a: arb_facts_block terminates at ρ_mid
      -- Step 2b: exit_havoc targets ρ'.store
      -- Step 2c: exit assumes pass via hall_tt'_eval₀
      -- First, derive eval preservation facts
      have heval_mid : ρ_mid.eval = ρ₀.eval := by
        rw [heq_mid]
      -- The arb_facts_block is a named block. Running its body to terminal ρ_inner
      -- and projecting gives ρ_mid.
      -- For the block body: havoc(identity) → assume → body → maintain_asserts.
      -- Havoc vars are all defined at ρ₀
      have h_havoc_vars_defined₀ : ∀ x ∈ havoc_vars, (ρ₀.store x).isSome :=
        havoc_vars_defined_of_init hswf havoc_vars rfl
      -- Sub-proof: arb_facts block body terminates at ρ_inner
      -- (identity havoc + assumes pass at ρ₀ + body runs to ρ_inner + maintains pass at ρ_inner)
      have h_arb_block : CoreStar π φ
          (.stmt (.block arb_facts_label arb_facts_body ∅) ρ₀) (.terminal ρ_mid) := by
        -- The block body runs from ρ₀ to ρ_inner, then projects to ρ_mid
        suffices h_body_run : CoreStar π φ (.stmts arb_facts_body ρ₀) (.terminal ρ_inner) by
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_facts_label arb_facts_body ∅ ρ₀ ρ_inner h_body_run
          -- After projection: {ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval} = ρ_mid
          have heq_proj : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval } : Env Expression) = ρ_mid := by
            rw [heq_mid]
          rw [heq_proj] at h; exact h
        -- Prove the body runs from ρ₀ to ρ_inner:
        -- arb_facts_body = [havoc_block, assumes_block] ++ [] ++ body ++ maintain_stmts ++ []
        -- = havoc_block :: assumes_block :: (body ++ maintain_stmts)
        -- Step 1: identity havoc at ρ₀ → terminal ρ₀
        have hwfvar : WellFormedSemanticEvalVar ρ₀.eval := hswf.wfVar
        have h_havoc_id : CoreStar π φ
            (.stmt (.block havoc_label havoc_stmts ∅) ρ₀) (.terminal ρ₀) := by
          have h := havoc_block_to_target π φ havoc_label havoc_vars md ρ₀ ρ₀ hwfvar
            h_havoc_vars_defined₀ h_havoc_vars_defined₀ (fun x _ => rfl)
          simp at h; exact h
        -- Step 2: assumes block at ρ₀ → terminal ρ₀
        have h_assumes_block : CoreStar π φ
            (.stmt (.block arb_assumes_label arb_assumes_body md) ρ₀) (.terminal ρ₀) := by
          have h_assumes_run : CoreStar π φ (.stmts arb_assumes_body ρ₀) (.terminal ρ₀) := by
            simp only [arb_assumes_body, List.nil_append]
            exact stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkArbAssumeLabel hwfb hall_tt
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_assumes_label arb_assumes_body md ρ₀ ρ₀ h_assumes_run
          rw [projectStore_self_env] at h; exact h
        -- Step 3: body at ρ₀ → terminal ρ_inner (from h_inner, with eta on env)
        have h_body_from_ρ₀ : CoreStar π φ (.stmts body ρ₀) (.terminal ρ_inner) := by
          have heta : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure } : Env Expression) = ρ₀ := by
            cases ρ₀; simp
          rw [← heta]; exact h_inner
        -- Step 4: maintain asserts at ρ_inner → terminal ρ_inner
        -- Need: ∀ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some tt
        -- This follows from: invariants hold at ρ_mid (from loop entry check + no failure),
        -- and eval congr between ρ_mid.store and ρ_inner.store on inv vars.
        have h_maintain : CoreStar π φ (.stmts maintain_stmts ρ_inner) (.terminal ρ_inner) := by
          have hall_tt_mid : ∀ le ∈ inv, ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt := by
            have h_loop_mid : CoreStar π φ
                (.stmt (.loop .nondet measure inv body md) ρ_mid) (.terminal ρ') := by
              have h_copy := h_tail_mid
              cases h_copy with
              | step _ _ _ hstep hrest =>
                cases hstep with
                | step_stmts_cons =>
                  have ⟨ρ₁, h_s, h_nil⟩ := seq_reaches_terminal (P := Expression)
                    (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) hrest
                  cases h_nil with
                  | step _ _ _ hstep2 hrest2 =>
                    cases hstep2 with
                    | step_stmts_nil =>
                      cases hrest2 with
                      | refl => exact h_s
                      | step _ _ _ h _ => exact nomatch h
            intro le hle
            cases h_loop_mid with
            | step _ _ _ hstep1 hrest =>
              cases hstep1 with
              | step_loop_nondet_enter hinvb hinviff =>
                have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest hnf''
                have hnif := loop_step_hasInvFailure_false_of_or
                  (by simpa [Config.getEnv] using hh)
                have hno_ff : ¬∃ le' ∈ inv,
                    ρ_mid.eval ρ_mid.store le'.2 = some HasBool.ff := by
                  intro hff; have := hinviff.mpr hff; simp [hnif] at this
                rcases hinvb le hle with htt | hff
                · exact htt
                · exact absurd ⟨le, hle, hff⟩ hno_ff
              | step_loop_nondet_exit hinvb hinviff =>
                have hnif : (ρ_mid.hasFailure || ‹Bool›) = Bool.false := by
                  cases hrest with
                  | refl => simpa using hnf''
                  | step _ _ _ h _ => exact nomatch h
                have hnif' := loop_step_hasInvFailure_false_of_or hnif
                have hno_ff : ¬∃ le' ∈ inv,
                    ρ_mid.eval ρ_mid.store le'.2 = some HasBool.ff := by
                  intro hff; have := hinviff.mpr hff; simp [hnif'] at this
                rcases hinvb le hle with htt | hff
                · exact htt
                · exact absurd ⟨le, hle, hff⟩ hno_ff
          have hall_tt_inner : ∀ le ∈ inv,
              ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt := by
            intro le hle
            have htt_mid := hall_tt_mid le hle
            rw [heval_mid] at htt_mid
            rw [heq_mid] at htt_mid
            have hcongr := inv_eval_agree_under_projectStore
              (ρ := ρ₀) (ρ_inner := ρ_inner) hswf (fun _ => Iff.rfl) hle
            rw [hcongr] at htt_mid
            have hpres := body_eval_inv_preserved π φ hwf_ext hswf h_inner hle ρ_inner.store
            rw [hpres]; exact htt_mid
          have hwfb_inner : WellFormedSemanticEvalBool ρ_inner.eval := by
            have h := star_preserves_wfBool_block Expression (EvalCommand π φ) (EvalPureFunc φ)
              hwf_ext.toWFEvalExtension (ss := body) (ρ := ρ₀) h_body_from_ρ₀
              (show WellFormedSemanticEvalBool _ from hwfb)
            simpa [Config.getEnv] using h
          exact stmts_mapIdx_assert_terminal π φ inv ρ_inner md mkMaintainLabel
            hwfb_inner hall_tt_inner
        -- Chain: havoc → assumes → body ++ maintain
        show CoreStar π φ (.stmts arb_facts_body ρ₀) (.terminal ρ_inner)
        show CoreStar π φ (.stmts
          ([.block havoc_label havoc_stmts ∅, .block arb_assumes_label arb_assumes_body md] ++
            [] ++ body ++ maintain_stmts ++ []) ρ₀) (.terminal ρ_inner)
        simp only [List.append_nil]
        -- Now: [havoc_block, assumes_block] ++ body ++ maintain_stmts
        exact ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
            _ _ ρ₀ ρ₀ h_havoc_id)
          (ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
              _ _ ρ₀ ρ₀ h_assumes_block)
            (stmts_concat_terminal π φ body maintain_stmts ρ₀ ρ_inner ρ_inner
              h_body_from_ρ₀ h_maintain))
      -- Sub-proof: exit stmts at ρ_mid terminate at ρ'
      -- exit stmts = [exit_havoc_block] ++ [] ++ exit_inv_assumes
      -- First derive ρ_mid.hasFailure = false (by monotonicity contrapositive)
      have hnf_mid : ρ_mid.hasFailure = Bool.false := by
        cases hb : ρ_mid.hasFailure with
        | false => rfl
        | true =>
          have := StepStmtStar_hasFailure_monotone (P := Expression)
            (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) h_tail_mid hb
          simp [Config.getEnv] at this
          exact absurd this (by simp [hnf''])
      -- Now show {ρ_mid with store := ρ'.store} = ρ'
      have hρ'_eq_mid_store : ({ ρ_mid with store := ρ'.store } : Env Expression) = ρ' := by
        cases ρ' with | mk s' e' f' =>
        cases ρ_mid with | mk sm em fm =>
        simp at heval_mid hnf_mid hnf''
        simp [heval_mid, ← heval_eq, hnf_mid, hnf'']
      have h_exit_stmts : CoreStar π φ
          (.stmts ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes) ρ_mid)
          (.terminal ρ') := by
        -- exit_havoc_block at ρ_mid targets ρ'.store
        have h_exit_havoc : CoreStar π φ
            (.stmt (.block havoc_label havoc_stmts ∅) ρ_mid)
            (.terminal { ρ_mid with store := ρ'.store }) := by
          have hwfvar_mid : WellFormedSemanticEvalVar ρ_mid.eval := by
            have hwfvar : (Config.block (P := Expression) (CmdT := Command) .none ρ₀.store ρ₀.eval
                  (.stmts body { store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure })).wfVar :=
              ⟨hswf.wfVar, hswf.wfVar⟩
            have h := star_preserves_cfg_wfVar Expression (EvalCommand π φ) (EvalPureFunc φ)
              hwf_ext.toWFEvalExtension h_block_mid hwfvar
            exact Config.wfVar_implies_wfEval Expression _ h
          have h_inner_isSome : ∀ n, (ρ₀.store n).isSome → (ρ_inner.store n).isSome := by
            have h_oi := star_preserves_outerInv π φ h_inner
              (show outerInv ρ₀.store (.stmts body { store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure }) from
                fun n h => h)
            exact h_oi
          exact havoc_block_to_target π φ havoc_label havoc_vars md ρ_mid ρ' hwfvar_mid
            (by -- hdef_src: ∀ x ∈ havoc_vars, (ρ_mid.store x).isSome
              intro x hx
              have hx_def := h_havoc_vars_defined₀ x hx
              rw [heq_mid]; simp [projectStore]
              rw [if_pos hx_def]
              exact h_inner_isSome x hx_def)
            (by -- hdef_tgt: ∀ x ∈ havoc_vars, (ρ'.store x).isSome
              intro x hx
              have hx_def := h_havoc_vars_defined₀ x hx
              exact stmt_star_preserves_isSome π φ _ ρ₀ (.terminal ρ') hreach x hx_def)
            (by -- hagree: ∀ x, x ∉ havoc_vars → ρ'.store x = ρ_mid.store x
              intro x hx_not_havoc
              by_cases hsome : ((ρ₀.store x).isSome : Bool) = Bool.true
              · -- isSome case: x ∉ modifiedVars body (else contradiction)
                have hx_not_mod : x ∉ Block.modifiedVars body := by
                  intro hmod
                  have h_not_filter :
                      ¬(decide (¬x ∈ Block.definedVars body Bool.false) = Bool.true) :=
                    fun h_filt => hx_not_havoc (List.mem_filter.mpr ⟨hmod, h_filt⟩)
                  simp [decide_eq_true_eq] at h_not_filter
                  have hisNone := hswf.defsUndefined x (by
                    show x ∈ Stmt.definedVars
                      (.loop ExprOrNondet.nondet measure inv body md) Bool.false
                    simp [Stmt.definedVars]; exact h_not_filter)
                  exact absurd hsome (by simp [Option.isNone_iff_eq_none] at hisNone; simp [hisNone])
                have hx_not_def : x ∉ Block.definedVars body Bool.false := by
                  intro hdef
                  have hisNone := hswf.defsUndefined x (by
                    show x ∈ Stmt.definedVars
                      (.loop ExprOrNondet.nondet measure inv body md) Bool.false
                    simp [Stmt.definedVars]; exact hdef)
                  exact absurd hsome (by simp [Option.isNone_iff_eq_none] at hisNone; simp [hisNone])
                have hx_not_touched_body : x ∉ Config.touchedVarsSet
                    (Config.stmts body
                      { store := ρ₀.store, eval := ρ₀.eval,
                        hasFailure := ρ₀.hasFailure }) := by
                  simp only [Config.touchedVarsSet, List.mem_append]
                  exact fun h => h.elim hx_not_mod hx_not_def
                have h_inner_eq : ρ_inner.store x = ρ₀.store x := by
                  have := star_preserves_store_outside_touchedVars_isSome
                    (π := π) (φ := φ) (σ₀ := ρ₀.store)
                    h_inner x hsome hx_not_touched_body (fun _ h => h)
                  simpa [Config.getEnv] using this
                have h_mid_eq : ρ_mid.store x = ρ₀.store x := by
                  rw [heq_mid]
                  show projectStore ρ₀.store ρ_inner.store x = ρ₀.store x
                  simp only [projectStore, hsome, ite_true]; exact h_inner_eq
                have hx_not_touched_loop : x ∉ Config.touchedVarsSet
                    (Config.stmt
                      (.loop ExprOrNondet.nondet measure inv body md) ρ₀) := by
                  simp only [Config.touchedVarsSet, Stmt.modifiedVars,
                    Stmt.definedVars, List.mem_append]
                  exact fun h => h.elim hx_not_mod hx_not_def
                have h_rho'_eq : ρ'.store x = ρ₀.store x := by
                  have := star_preserves_store_outside_touchedVars_isSome
                    (π := π) (φ := φ) (σ₀ := ρ₀.store)
                    hreach x hsome hx_not_touched_loop (fun _ h => h)
                  simpa [Config.getEnv] using this
                rw [h_rho'_eq, h_mid_eq]
              · -- isNone case
                have hnone₀ : ρ₀.store x = none := by
                  cases h : ρ₀.store x with
                  | none => rfl
                  | some _ => simp [h] at hsome
                have hnone_mid : ρ_mid.store x = none := by
                  rw [heq_mid]
                  show projectStore ρ₀.store ρ_inner.store x = none
                  simp only [projectStore, hnone₀, Option.isSome_none,
                    Bool.false_eq_true, ite_false]
                have hnone' : ρ'.store x = none := by
                  have h := stmt_compound_terminal_preserves_isNone
                    (π := π) (φ := φ) hreach
                    (fun _ heq => by simp [Statement] at heq)
                    (fun _ _ heq => by simp [Statement] at heq)
                    x (by rw [Option.isNone_iff_eq_none]; exact hnone₀)
                  exact Option.isNone_iff_eq_none.mp h
                rw [hnone', hnone_mid])

        rw [hρ'_eq_mid_store] at h_exit_havoc
        -- exit_inv_assumes at ρ' → terminal ρ'
        have h_exit_assumes : CoreStar π φ (.stmts exit_inv_assumes ρ') (.terminal ρ') := by
          have hwfb' : WellFormedSemanticEvalBool ρ'.eval := by
            have h := star_preserves_wfBool Expression (EvalCommand π φ) (EvalPureFunc φ)
              hwf_ext.toWFEvalExtension
              (s := (.loop .nondet measure inv body md : Statement)) (ρ := ρ₀) hreach
              (show WellFormedSemanticEvalBool _ from hwfb)
            simpa [Config.getEnv] using h
          have hall_tt'_at_ρ' : ∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt := hall_tt'
          exact stmts_mapIdx_assume_terminal π φ inv ρ' md mkExitAssumeLabel hwfb' hall_tt'_at_ρ'
        -- Chain: [exit_havoc_block] ++ [] ++ exit_inv_assumes
        exact stmts_concat_terminal π φ [.block havoc_label havoc_stmts ∅] exit_inv_assumes
          ρ_mid ρ' ρ'
          (ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ_mid ρ' h_exit_havoc)
            (.step _ _ _ .step_stmts_nil (.refl _)))
          h_exit_assumes
      -- Chain: arb_facts_block → exit_stmts
      exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ_mid h_arb_block)
        h_exit_stmts
    -- Case h_1.isFalse: det guard, no measure
    case h_1.isFalse _ _ g _ _ =>
      refine .inr (fun hnf_arg => ?_)
      have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
      -- The first step of hreach determines whether guard=tt (enter) or guard=ff (exit)
      cases hreach with
      | step _ _ _ hstep hrest =>
        cases hstep with
        | step_loop_exit hguard_ff hinvb hinviff _ =>
          -- Loop exited immediately: guard=ff at ρ₀, ρ' = {ρ₀ with hasFailure := ...}
          cases hrest with
          | refl =>
            -- ρ' = {ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure}
            -- Since hnf'' and hnf₀, hasInvFailure = false, so ρ' = ρ₀
            have hρ'_eq : ({ ρ₀ with hasFailure := ρ₀.hasFailure || ‹Bool› } : Env Expression) = ρ₀ := by
              have hinvf : (‹Bool› : Bool) = Bool.false :=
                loop_step_hasInvFailure_false_of_or (by simpa using hnf'')
              cases ρ₀; simp_all
            rw [hρ'_eq]
            -- Target: trace through block(first_iter, ite(det g, ..., [])) from ρ₀ to terminal ρ₀
            -- ITE takes false branch (guard=ff), else branch = []
            let loop_num := (StringGenState.gen "loop" σ.gen).fst
            let invSuffix : Nat → String → String := fun i lbl =>
              if lbl.isEmpty then toString i else s!"{i}_{lbl}"
            let mkAssertLabel : Nat → String → String := fun i lbl =>
              s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
            let mkAssumeLabel : Nat → String → String := fun i lbl =>
              s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
            have h_fib_run : CoreStar π φ
                (.stmts ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                  (mkAssertLabel i le.1) le.2 md)) ++
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                    (mkAssumeLabel i le.1) le.2 md))) ρ₀)
                (.terminal ρ₀) :=
              stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
                (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
                (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
            have h_fib_block : CoreStar π φ
                (.stmt (.block
                  s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                  ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                    (mkAssertLabel i le.1) le.2 md)) ++
                   (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                    (mkAssumeLabel i le.1) le.2 md)))
                  ∅) ρ₀)
                (.terminal ρ₀) := by
              have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
                s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" _ ∅ ρ₀ ρ₀ h_fib_run
              rw [projectStore_self_env] at h; exact h
            -- ITE false branch: step_ite_false gives .block .none ρ₀.store (.stmts [] ρ₀)
            -- Use suffices to let the goal determine the then-branch
            suffices h_ite : CoreStar π φ (.stmt (.ite (.det g) _ [] ∅) ρ₀) (.terminal ρ₀) by
              have h_stmts : CoreStar π φ
                  (.stmts [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                    ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                      (mkAssertLabel i le.1) le.2 md)) ++
                     (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                      (mkAssumeLabel i le.1) le.2 md))) ∅,
                    .ite (.det g) _ [] ∅] ρ₀)
                  (.terminal ρ₀) :=
                ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_fib_block)
                  (ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_ite)
                    (.step _ _ _ .step_stmts_nil (.refl _)))
              have h_outer := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
                s!"{loopElimBlockPrefix}loop_{loop_num}" _ ∅ ρ₀ ρ₀ h_stmts
              rw [projectStore_self_env] at h_outer
              exact h_outer
            exact ite_det_false_empty_terminal (P := Expression) (CmdT := Command) (EvalCommand π φ) (EvalPureFunc φ) g _ ∅ ρ₀ hguard_ff hwfb
          | step _ _ _ h _ => exact nomatch h
        | step_loop_enter hguard_tt hinvb_enter hinviff_enter hwfbe_enter hmeas_enter =>
          -- Reconstruct hreach for use in lemmas
          have hreach : CoreStar π φ (.stmt (.loop (.det g) none inv body md) ρ₀) (.terminal ρ') :=
            .step _ _ _ (.step_loop_enter hguard_tt hinvb_enter hinviff_enter hwfbe_enter hmeas_enter) hrest
          -- Decompose the source inner trace: block(body) ; [loop] → terminal ρ'
          have ⟨ρ_mid, h_block_mid, h_tail_mid, ρ_inner, h_inner, heq_mid⟩ :=
            seq_block_loop_terminal_decompose π φ hreach_inner
          -- Key facts about ρ'
          have hall_tt' : ∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt :=
            loop_terminal_inv_all_tt π φ hreach hnf''
          have hproj_id : projectStore ρ₀.store ρ'.store = ρ'.store :=
            loop_terminal_projectStore_id π φ hreach
          -- eval is preserved by the loop terminal trace (block scoping)
          have heval_eq : ρ'.eval = ρ₀.eval :=
            loop_terminal_eval_preserved π φ hreach
          -- Rewrite hall_tt' in terms of ρ₀.eval
          have hall_tt'_eval₀ : ∀ le ∈ inv, ρ₀.eval ρ'.store le.2 = some HasBool.tt := by
            intro le hle; rw [← heval_eq]; exact hall_tt' le hle
          -- Guard=ff at ρ' and not(guard)=tt at ρ'
          have hguard_ff : ρ'.eval ρ'.store g = some HasBool.ff :=
            loop_det_terminal_guard_ff π φ hreach hnf''
          have hnot_guard_tt : ρ'.eval ρ'.store (HasNot.not g) = some HasBool.tt := by
            have := (hwfb ρ'.store g).2
            rw [heval_eq] at hguard_ff
            rw [heval_eq]
            exact this.mp hguard_ff
          -- Step 1: Build first_iter_asserts trace
          let loop_num := (StringGenState.gen "loop" σ.gen).fst
          let invSuffix : Nat → String → String := fun i lbl =>
            if lbl.isEmpty then toString i else s!"{i}_{lbl}"
          let mkAssertLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
          let mkAssumeLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
          have h_fib_run : CoreStar π φ
              (.stmts ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
                (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                  (mkAssumeLabel i le.1) le.2 md))) ρ₀)
              (.terminal ρ₀) := by
            exact stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
              (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
              (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
          have h_fib_block : CoreStar π φ
              (.stmt (.block
                s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                  (mkAssertLabel i le.1) le.2 md)) ++
                 (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                  (mkAssumeLabel i le.1) le.2 md)))
                ∅) ρ₀)
              (.terminal ρ₀) := by
            have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
              s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" _ ∅ ρ₀ ρ₀ h_fib_run
            rw [projectStore_self_env] at h; exact h
          -- Step 2: Build the ite det-true trace to terminal ρ'.
          let havoc_vars := (Block.modifiedVars body).filter fun v =>
            decide (¬ v ∈ Block.definedVars body Bool.false)
          let havoc_stmts : Statements := havoc_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)
          let havoc_label := s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
          let arb_assumes_label := s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
          let mkArbAssumeLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lbl}"
          let arb_assumes_body : Statements :=
            [Stmt.cmd (HasPassiveCmds.assume
              s!"{loopElimAssumePrefix}{loop_num}_guard" g md)] ++
            inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
              (mkArbAssumeLabel i le.1) le.2 md)
          let mkMaintainLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lbl}"
          let maintain_stmts : Statements :=
            inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkMaintainLabel i le.1) le.2 md)
          let arb_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
          let arb_facts_body : Statements :=
            [.block havoc_label havoc_stmts ∅,
             .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []
          let mkExitAssumeLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lbl}"
          let exit_inv_assumes : Statements :=
            inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
              (mkExitAssumeLabel i le.1) le.2 md)
          suffices h_then : CoreStar π φ
              (.stmts ((.block arb_facts_label arb_facts_body ∅) ::
                (([.block havoc_label havoc_stmts ∅] ++
                  [Stmt.cmd (HasPassiveCmds.assume
                    s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                  exit_inv_assumes)))
                ρ₀) (.terminal ρ') from by
            -- Build the ite trace
            have h_ite_inner : CoreStar π φ
                (.block .none ρ₀.store ρ₀.eval (.stmts
                  ((.block arb_facts_label arb_facts_body ∅) ::
                    (([.block havoc_label havoc_stmts ∅] ++
                      [Stmt.cmd (HasPassiveCmds.assume
                        s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                      exit_inv_assumes)))
                  ρ₀))
                (.terminal { ρ' with store := projectStore ρ₀.store ρ'.store, eval := ρ₀.eval }) :=
              ReflTrans_Transitive _ _ _ _
                (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ .none ρ₀.store ρ₀.eval h_then)
                (.step _ _ _ .step_block_done (.refl _))
            have hproj_env : ({ ρ' with store := projectStore ρ₀.store ρ'.store, eval := ρ₀.eval } : Env Expression) = ρ' := by
              rw [hproj_id, ← heval_eq]
            rw [hproj_env] at h_ite_inner
            have h_ite : CoreStar π φ
                (.stmt (.ite (.det g)
                  ((.block arb_facts_label arb_facts_body ∅) ::
                    (([.block havoc_label havoc_stmts ∅] ++
                      [Stmt.cmd (HasPassiveCmds.assume
                        s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                      exit_inv_assumes)))
                  [] ∅) ρ₀)
                (.terminal ρ') :=
              .step _ _ _ (.step_ite_true hguard_tt hwfb) h_ite_inner
            -- Chain first_iter_block + ite into stmts
            have h_stmts : CoreStar π φ
                (.stmts [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                  ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                    (mkAssertLabel i le.1) le.2 md)) ++
                   (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                    (mkAssumeLabel i le.1) le.2 md))) ∅,
                  .ite (.det g)
                    ((.block arb_facts_label arb_facts_body ∅) ::
                      (([.block havoc_label havoc_stmts ∅] ++
                        [Stmt.cmd (HasPassiveCmds.assume
                          s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                        exit_inv_assumes)))
                    [] ∅] ρ₀)
                (.terminal ρ') :=
              ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_fib_block)
                (ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ' h_ite)
                  (.step _ _ _ .step_stmts_nil (.refl _)))
            -- Wrap in outer block
            have h_outer := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
              s!"{loopElimBlockPrefix}loop_{loop_num}" _ ∅ ρ₀ ρ' h_stmts
            rw [hproj_id] at h_outer
            have henv_eq : ({ ρ' with store := ρ'.store, eval := ρ₀.eval } : Env Expression) = ρ' := by
              rw [← heval_eq]
            rw [henv_eq] at h_outer
            exact h_outer
          -- Now prove h_then: trace through then-stmts to ρ'
          -- First, derive eval preservation facts
          have heval_mid : ρ_mid.eval = ρ₀.eval := by
            rw [heq_mid]
          -- Havoc vars are all defined at ρ₀
          have h_havoc_vars_defined₀ : ∀ x ∈ havoc_vars, (ρ₀.store x).isSome :=
            havoc_vars_defined_of_init hswf havoc_vars rfl
          -- Sub-proof: arb_facts block body terminates at ρ_inner
          have h_arb_block : CoreStar π φ
              (.stmt (.block arb_facts_label arb_facts_body ∅) ρ₀) (.terminal ρ_mid) := by
            suffices h_body_run : CoreStar π φ (.stmts arb_facts_body ρ₀) (.terminal ρ_inner) by
              have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_facts_label arb_facts_body ∅ ρ₀ ρ_inner h_body_run
              have heq_proj : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval } : Env Expression) = ρ_mid := by
                rw [heq_mid]
              rw [heq_proj] at h; exact h
            -- Prove the body runs from ρ₀ to ρ_inner:
            -- arb_facts_body = [havoc_block, assumes_block] ++ [] ++ body ++ maintain_stmts ++ []
            -- Step 1: identity havoc at ρ₀ → terminal ρ₀
            have hwfvar : WellFormedSemanticEvalVar ρ₀.eval := hswf.wfVar
            have h_havoc_id : CoreStar π φ
                (.stmt (.block havoc_label havoc_stmts ∅) ρ₀) (.terminal ρ₀) := by
              have h := havoc_block_to_target π φ havoc_label havoc_vars md ρ₀ ρ₀ hwfvar
                h_havoc_vars_defined₀ h_havoc_vars_defined₀ (fun x _ => rfl)
              simp at h; exact h
            -- Step 2: assumes block at ρ₀ → terminal ρ₀ (guard assume + inv assumes)
            have h_assumes_block : CoreStar π φ
                (.stmt (.block arb_assumes_label arb_assumes_body md) ρ₀) (.terminal ρ₀) := by
              have h_assumes_run : CoreStar π φ (.stmts arb_assumes_body ρ₀) (.terminal ρ₀) := by
                simp only [arb_assumes_body, List.cons_append, List.nil_append]
                -- guard assume passes since guard=tt at ρ₀
                have h_guard_assume : CoreStar π φ
                    (.stmt (.cmd (HasPassiveCmds.assume
                      s!"{loopElimAssumePrefix}{loop_num}_guard" g md)) ρ₀)
                    (.terminal ρ₀) :=
                  assume_pass_step π φ _ g md ρ₀ hguard_tt hwfb
                exact ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_guard_assume)
                  (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkArbAssumeLabel hwfb hall_tt)
              have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_assumes_label arb_assumes_body md ρ₀ ρ₀ h_assumes_run
              rw [projectStore_self_env] at h; exact h
            -- Step 3: body at ρ₀ → terminal ρ_inner
            have h_body_from_ρ₀ : CoreStar π φ (.stmts body ρ₀) (.terminal ρ_inner) := by
              have heta : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure } : Env Expression) = ρ₀ := by
                cases ρ₀; simp
              rw [← heta]; exact h_inner
            -- Step 4: maintain asserts at ρ_inner → terminal ρ_inner
            have h_maintain : CoreStar π φ (.stmts maintain_stmts ρ_inner) (.terminal ρ_inner) := by
              have hall_tt_mid : ∀ le ∈ inv, ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt := by
                have h_loop_mid : CoreStar π φ
                    (.stmt (.loop (.det g) none inv body md) ρ_mid) (.terminal ρ') := by
                  have h_copy := h_tail_mid
                  cases h_copy with
                  | step _ _ _ hstep hrest =>
                    cases hstep with
                    | step_stmts_cons =>
                      have ⟨ρ₁, h_s, h_nil⟩ := seq_reaches_terminal (P := Expression)
                        (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) hrest
                      cases h_nil with
                      | step _ _ _ hstep2 hrest2 =>
                        cases hstep2 with
                        | step_stmts_nil =>
                          cases hrest2 with
                          | refl => exact h_s
                          | step _ _ _ h _ => exact nomatch h
                intro le hle
                cases h_loop_mid with
                | step _ _ _ hstep1 hrest =>
                  cases hstep1 with
                  | step_loop_enter hg_mid hinvb_mid hinviff_mid _ _ =>
                    have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest hnf''
                    have hnif := loop_step_hasInvFailure_false_of_or
                      (by simpa [Config.getEnv] using hh)
                    have hno_ff : ¬∃ le' ∈ inv,
                        ρ_mid.eval ρ_mid.store le'.2 = some HasBool.ff := by
                      intro hff; have := hinviff_mid.mpr hff; simp [hnif] at this
                    rcases hinvb_mid le hle with htt | hff
                    · exact htt
                    · exact absurd ⟨le, hle, hff⟩ hno_ff
                  | step_loop_exit _ hinvb_mid hinviff_mid _ =>
                    have hnif : (ρ_mid.hasFailure || ‹Bool›) = Bool.false := by
                      cases hrest with
                      | refl => simpa using hnf''
                      | step _ _ _ h _ => exact nomatch h
                    have hnif' := loop_step_hasInvFailure_false_of_or hnif
                    have hno_ff : ¬∃ le' ∈ inv,
                        ρ_mid.eval ρ_mid.store le'.2 = some HasBool.ff := by
                      intro hff; have := hinviff_mid.mpr hff; simp [hnif'] at this
                    rcases hinvb_mid le hle with htt | hff
                    · exact htt
                    · exact absurd ⟨le, hle, hff⟩ hno_ff
              have hall_tt_inner : ∀ le ∈ inv,
                  ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt := by
                intro le hle
                have htt_mid := hall_tt_mid le hle
                rw [heval_mid] at htt_mid
                rw [heq_mid] at htt_mid
                have hcongr := inv_eval_agree_under_projectStore
                  (ρ := ρ₀) (ρ_inner := ρ_inner) hswf (fun _ => Iff.rfl) hle
                rw [hcongr] at htt_mid
                have hpres := body_eval_inv_preserved π φ hwf_ext hswf h_inner hle ρ_inner.store
                rw [hpres]; exact htt_mid
              have hwfb_inner : WellFormedSemanticEvalBool ρ_inner.eval := by
                have h := star_preserves_wfBool_block Expression (EvalCommand π φ) (EvalPureFunc φ)
                  hwf_ext.toWFEvalExtension (ss := body) (ρ := ρ₀) h_body_from_ρ₀
                  (show WellFormedSemanticEvalBool _ from hwfb)
                simpa [Config.getEnv] using h
              exact stmts_mapIdx_assert_terminal π φ inv ρ_inner md mkMaintainLabel
                hwfb_inner hall_tt_inner
            -- Chain: havoc → assumes → body ++ maintain
            show CoreStar π φ (.stmts arb_facts_body ρ₀) (.terminal ρ_inner)
            show CoreStar π φ (.stmts
              ([.block havoc_label havoc_stmts ∅, .block arb_assumes_label arb_assumes_body md] ++
                [] ++ body ++ maintain_stmts ++ []) ρ₀) (.terminal ρ_inner)
            simp only [List.append_nil]
            exact ReflTrans_Transitive _ _ _ _
              (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                _ _ ρ₀ ρ₀ h_havoc_id)
              (ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ ρ₀ ρ₀ h_assumes_block)
                (stmts_concat_terminal π φ body maintain_stmts ρ₀ ρ_inner ρ_inner
                  h_body_from_ρ₀ h_maintain))
          -- Sub-proof: exit stmts at ρ_mid terminate at ρ'
          -- exit stmts = [exit_havoc_block] ++ [assume_not_guard] ++ exit_inv_assumes
          have hnf_mid : ρ_mid.hasFailure = Bool.false := by
            cases hb : ρ_mid.hasFailure with
            | false => rfl
            | true =>
              have := StepStmtStar_hasFailure_monotone (P := Expression)
                (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) h_tail_mid hb
              simp [Config.getEnv] at this
              exact absurd this (by simp [hnf''])
          have hρ'_eq_mid_store : ({ ρ_mid with store := ρ'.store } : Env Expression) = ρ' := by
            cases ρ' with | mk s' e' f' =>
            cases ρ_mid with | mk sm em fm =>
            simp at heval_mid hnf_mid hnf''
            simp [heval_mid, ← heval_eq, hnf_mid, hnf'']
          have h_exit_stmts : CoreStar π φ
              (.stmts ([.block havoc_label havoc_stmts ∅] ++
                [Stmt.cmd (HasPassiveCmds.assume
                  s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                exit_inv_assumes) ρ_mid)
              (.terminal ρ') := by
            -- exit_havoc_block at ρ_mid targets ρ'.store
            have h_exit_havoc : CoreStar π φ
                (.stmt (.block havoc_label havoc_stmts ∅) ρ_mid)
                (.terminal { ρ_mid with store := ρ'.store }) := by
              have hwfvar_mid : WellFormedSemanticEvalVar ρ_mid.eval := by
                have hwfvar : (Config.block (P := Expression) (CmdT := Command) .none ρ₀.store ρ₀.eval
                      (.stmts body { store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure })).wfVar :=
                  ⟨hswf.wfVar, hswf.wfVar⟩
                have h := star_preserves_cfg_wfVar Expression (EvalCommand π φ) (EvalPureFunc φ)
                  hwf_ext.toWFEvalExtension h_block_mid hwfvar
                exact Config.wfVar_implies_wfEval Expression _ h
              have h_inner_isSome : ∀ n, (ρ₀.store n).isSome → (ρ_inner.store n).isSome := by
                have h_oi := star_preserves_outerInv π φ h_inner
                  (show outerInv ρ₀.store (.stmts body { store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure }) from
                    fun n h => h)
                exact h_oi
              exact havoc_block_to_target π φ havoc_label havoc_vars md ρ_mid ρ' hwfvar_mid
                (by -- hdef_src: ∀ x ∈ havoc_vars, (ρ_mid.store x).isSome
                  intro x hx
                  have hx_def := h_havoc_vars_defined₀ x hx
                  rw [heq_mid]; simp [projectStore]
                  rw [if_pos hx_def]
                  exact h_inner_isSome x hx_def)
                (by -- hdef_tgt: ∀ x ∈ havoc_vars, (ρ'.store x).isSome
                  intro x hx
                  have hx_def := h_havoc_vars_defined₀ x hx
                  exact stmt_star_preserves_isSome π φ _ ρ₀ (.terminal ρ') hreach x hx_def)
                (by -- hagree: ∀ x, x ∉ havoc_vars → ρ'.store x = ρ_mid.store x
                  intro x hx_not_havoc
                  by_cases hsome : ((ρ₀.store x).isSome : Bool) = Bool.true
                  · have hx_not_mod : x ∉ Block.modifiedVars body := by
                      intro hmod
                      have h_not_filter :
                          ¬(decide (¬x ∈ Block.definedVars body Bool.false) = Bool.true) :=
                        fun h_filt => hx_not_havoc (List.mem_filter.mpr ⟨hmod, h_filt⟩)
                      simp [decide_eq_true_eq] at h_not_filter
                      have hisNone := hswf.defsUndefined x (by
                        show x ∈ Stmt.definedVars
                          (.loop (ExprOrNondet.det g) none inv body md) Bool.false
                        simp [Stmt.definedVars]; exact h_not_filter)
                      exact absurd hsome (by simp [Option.isNone_iff_eq_none] at hisNone; simp [hisNone])
                    have hx_not_def : x ∉ Block.definedVars body Bool.false := by
                      intro hdef
                      have hisNone := hswf.defsUndefined x (by
                        show x ∈ Stmt.definedVars
                          (.loop (ExprOrNondet.det g) none inv body md) Bool.false
                        simp [Stmt.definedVars]; exact hdef)
                      exact absurd hsome (by simp [Option.isNone_iff_eq_none] at hisNone; simp [hisNone])
                    have hx_not_touched_body : x ∉ Config.touchedVarsSet
                        (Config.stmts body
                          { store := ρ₀.store, eval := ρ₀.eval,
                            hasFailure := ρ₀.hasFailure }) := by
                      simp only [Config.touchedVarsSet, List.mem_append]
                      exact fun h => h.elim hx_not_mod hx_not_def
                    have h_inner_eq : ρ_inner.store x = ρ₀.store x := by
                      have := star_preserves_store_outside_touchedVars_isSome
                        (π := π) (φ := φ) (σ₀ := ρ₀.store)
                        h_inner x hsome hx_not_touched_body (fun _ h => h)
                      simpa [Config.getEnv] using this
                    have h_mid_eq : ρ_mid.store x = ρ₀.store x := by
                      rw [heq_mid]
                      show projectStore ρ₀.store ρ_inner.store x = ρ₀.store x
                      simp only [projectStore, hsome, ite_true]; exact h_inner_eq
                    have hx_not_touched_loop : x ∉ Config.touchedVarsSet
                        (Config.stmt
                          (.loop (ExprOrNondet.det g) none inv body md) ρ₀) := by
                      simp only [Config.touchedVarsSet, Stmt.modifiedVars,
                        Stmt.definedVars, List.mem_append]
                      exact fun h => h.elim hx_not_mod hx_not_def
                    have h_rho'_eq : ρ'.store x = ρ₀.store x := by
                      have := star_preserves_store_outside_touchedVars_isSome
                        (π := π) (φ := φ) (σ₀ := ρ₀.store)
                        hreach x hsome hx_not_touched_loop (fun _ h => h)
                      simpa [Config.getEnv] using this
                    rw [h_rho'_eq, h_mid_eq]
                  · have hnone₀ : ρ₀.store x = none := by
                      cases h : ρ₀.store x with
                      | none => rfl
                      | some _ => simp [h] at hsome
                    have hnone_mid : ρ_mid.store x = none := by
                      rw [heq_mid]
                      show projectStore ρ₀.store ρ_inner.store x = none
                      simp only [projectStore, hnone₀, Option.isSome_none,
                        Bool.false_eq_true, ite_false]
                    have hnone' : ρ'.store x = none := by
                      have h := stmt_compound_terminal_preserves_isNone
                        (π := π) (φ := φ) hreach
                        (fun _ heq => by simp [Statement] at heq)
                        (fun _ _ heq => by simp [Statement] at heq)
                        x (by rw [Option.isNone_iff_eq_none]; exact hnone₀)
                      exact Option.isNone_iff_eq_none.mp h
                    rw [hnone', hnone_mid])
            rw [hρ'_eq_mid_store] at h_exit_havoc
            -- not-guard assume at ρ' → terminal ρ'
            have hwfb_ρ' : WellFormedSemanticEvalBool ρ'.eval := by
              have h := star_preserves_wfBool Expression (EvalCommand π φ) (EvalPureFunc φ)
                hwf_ext.toWFEvalExtension
                (s := (.loop (.det g) none inv body md : Statement)) (ρ := ρ₀) hreach
                (show WellFormedSemanticEvalBool _ from hwfb)
              simpa [Config.getEnv] using h
            have h_not_guard_assume : CoreStar π φ
                (.stmt (.cmd (HasPassiveCmds.assume
                  s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)) ρ')
                (.terminal ρ') :=
              assume_pass_step π φ _ (HasNot.not g) md ρ' hnot_guard_tt hwfb_ρ'
            -- exit_inv_assumes at ρ' → terminal ρ'
            have h_exit_assumes : CoreStar π φ (.stmts exit_inv_assumes ρ') (.terminal ρ') := by
              have hall_tt'_at_ρ' : ∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt := hall_tt'
              exact stmts_mapIdx_assume_terminal π φ inv ρ' md mkExitAssumeLabel hwfb_ρ' hall_tt'_at_ρ'
            -- Chain: [exit_havoc_block] ++ [assume_not_guard] ++ exit_inv_assumes
            exact stmts_concat_terminal π φ [.block havoc_label havoc_stmts ∅]
              ([Stmt.cmd (HasPassiveCmds.assume
                s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++ exit_inv_assumes)
              ρ_mid ρ' ρ'
              (ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ_mid ρ' h_exit_havoc)
                (.step _ _ _ .step_stmts_nil (.refl _)))
              (ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ' ρ' h_not_guard_assume)
                h_exit_assumes)
          -- Chain: arb_facts_block → exit_stmts
          exact ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ_mid h_arb_block)
            h_exit_stmts
    -- Case h_2.isFalse.isTrue: det guard, with measure
    -- Same structure as det+none (case h_1.isFalse) but with additional
    -- preTermination (init_m_old, assert_lb) and postTermination (assert_decrease).
    case h_2.isFalse.isTrue _ _ _ _ _ _ _ _ =>
      -- Rename the inaccessible variables: h✝², guard✝, g✝, measure✝, m✝, h✝¹, h✝
      rename_i _ _ g _ m h_m_old_fresh _
      have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
      cases hreach with
      | step _ _ _ hstep hrest =>
        cases hstep with
        | step_loop_exit hguard_ff _ _ _ =>
          cases hrest with
          | refl =>
            have hρ'_eq : ({ ρ₀ with hasFailure := ρ₀.hasFailure || ‹Bool› } : Env Expression) = ρ₀ := by
              have hinvf : (‹Bool› : Bool) = Bool.false :=
                loop_step_hasInvFailure_false_of_or (by simpa using hnf'')
              cases ρ₀; simp_all
            rw [hρ'_eq]
            refine .inr (fun _ => ?_)
            let loop_num := (StringGenState.gen "loop" σ.gen).fst
            let invSuffix' : Nat → String → String := fun i lbl =>
              if lbl.isEmpty then toString i else s!"{i}_{lbl}"
            let mkAssertLabel : Nat → String → String := fun i lbl =>
              s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix' i lbl}"
            let mkAssumeLabel : Nat → String → String := fun i lbl =>
              s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix' i lbl}"
            have h_fib_run : CoreStar π φ
                (.stmts ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                  (mkAssertLabel i le.1) le.2 md)) ++
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                    (mkAssumeLabel i le.1) le.2 md))) ρ₀)
                (.terminal ρ₀) :=
              stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
                (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
                (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
            have h_fib_block : CoreStar π φ
                (.stmt (.block
                  s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                  ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                    (mkAssertLabel i le.1) le.2 md)) ++
                   (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                    (mkAssumeLabel i le.1) le.2 md)))
                  ∅) ρ₀)
                (.terminal ρ₀) := by
              have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
                s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" _ ∅ ρ₀ ρ₀ h_fib_run
              rw [projectStore_self_env] at h; exact h
            -- ITE false branch
            suffices h_ite : CoreStar π φ (.stmt (.ite (.det g) _ [] ∅) ρ₀) (.terminal ρ₀) by
              have h_stmts : CoreStar π φ
                  (.stmts [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                    ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                      (mkAssertLabel i le.1) le.2 md)) ++
                     (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                      (mkAssumeLabel i le.1) le.2 md))) ∅,
                    .ite (.det g) _ [] ∅] ρ₀)
                  (.terminal ρ₀) :=
                ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_fib_block)
                  (ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_ite)
                    (.step _ _ _ .step_stmts_nil (.refl _)))
              have h_outer := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
                s!"{loopElimBlockPrefix}loop_{loop_num}" _ ∅ ρ₀ ρ₀ h_stmts
              rw [projectStore_self_env] at h_outer
              exact h_outer
            exact ite_det_false_empty_terminal (P := Expression) (CmdT := Command) (EvalCommand π φ) (EvalPureFunc φ) g _ ∅ ρ₀ hguard_ff hwfb
          | step _ _ _ h _ => exact nomatch h
        | step_loop_enter hguard_tt hinvb_enter hinviff_enter hwfbe_enter hmeas_enter =>
          -- The guard-enter sub-case: build terminal trace through the
          -- transformed code (arb_facts block with init_m_old, assert_lb,
          -- body, maintain_inv, assert_decrease).
          -- Structurally the same as det+none (lines 4770-5195) plus extra
          -- measure statements.
          -- Reconstruct hreach for use in lemmas
          have hreach : CoreStar π φ
              (.stmt (.loop (.det g) (some m) inv body md) ρ₀) (.terminal ρ') :=
            .step _ _ _
              (.step_loop_enter hguard_tt hinvb_enter hinviff_enter hwfbe_enter hmeas_enter)
              hrest
          -- Decompose the source inner trace: block(body) ; [loop] → terminal ρ'
          have ⟨ρ_mid, h_block_mid, h_tail_mid, ρ_inner, h_inner, heq_mid⟩ :=
            seq_block_loop_terminal_decompose π φ hreach_inner
          -- Key facts about ρ'
          have hall_tt' : ∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt :=
            loop_terminal_inv_all_tt π φ hreach hnf''
          have hproj_id : projectStore ρ₀.store ρ'.store = ρ'.store :=
            loop_terminal_projectStore_id π φ hreach
          -- eval is preserved by the loop terminal trace (block scoping)
          have heval_eq : ρ'.eval = ρ₀.eval :=
            loop_terminal_eval_preserved π φ hreach
          -- Rewrite hall_tt' in terms of ρ₀.eval
          have hall_tt'_eval₀ : ∀ le ∈ inv, ρ₀.eval ρ'.store le.2 = some HasBool.tt := by
            intro le hle; rw [← heval_eq]; exact hall_tt' le hle
          -- Guard=ff at ρ' and not(guard)=tt at ρ'
          have hguard_ff : ρ'.eval ρ'.store g = some HasBool.ff :=
            loop_det_terminal_guard_ff π φ hreach hnf''
          have hnot_guard_tt : ρ'.eval ρ'.store (HasNot.not g) = some HasBool.tt := by
            have := (hwfb ρ'.store g).2
            rw [heval_eq] at hguard_ff
            rw [heval_eq]
            exact this.mp hguard_ff
          -- Measure facts from hmeas_enter
          -- hmeas_enter : ∀ me v, some m = some me → eval me = some v ∧ lt v 0 = ff
          -- Extract using WellFormedSemanticEvalBool to get a definite value
          have hmeas_m := fun v => hmeas_enter m v rfl
          have heval_mid : ρ_mid.eval = ρ₀.eval := by
            rw [heq_mid]
          -- Step 1: Build first_iter_asserts trace (identical to det+none)
          let loop_num := (StringGenState.gen "loop" σ.gen).fst
          let invSuffix : Nat → String → String := fun i lbl =>
            if lbl.isEmpty then toString i else s!"{i}_{lbl}"
          let mkAssertLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
          let mkAssumeLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
          have h_fib_run : CoreStar π φ
              (.stmts ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
                (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                  (mkAssumeLabel i le.1) le.2 md))) ρ₀)
              (.terminal ρ₀) := by
            exact stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
              (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
              (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
          have h_fib_block : CoreStar π φ
              (.stmt (.block
                s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                  (mkAssertLabel i le.1) le.2 md)) ++
                 (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                  (mkAssumeLabel i le.1) le.2 md)))
                ∅) ρ₀)
              (.terminal ρ₀) := by
            have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
              s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" _ ∅ ρ₀ ρ₀ h_fib_run
            rw [projectStore_self_env] at h; exact h
          -- Step 2: Build the ite det-true trace to terminal ρ'.
          let havoc_vars := (Block.modifiedVars body).filter fun v =>
            decide (¬ v ∈ Block.definedVars body Bool.false)
          let havoc_stmts : Statements := havoc_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)
          let havoc_label := s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
          let arb_assumes_label := s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
          let mkArbAssumeLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lbl}"
          -- arb_assumes_body for det+some: guard_assume + init_m_old + assert_lb + inv_assumes
          let m_old_ident : Expression.Ident := HasIdent.ident
            (s!"$__loop_measure_{loop_num}" : String)
          let init_m_old : Statement :=
            .cmd (HasInit.init (CmdT := Command) m_old_ident HasIntOrder.intTy (.det m) md)
          let assert_lb : Statement := .cmd (HasPassiveCmds.assert
            s!"{loopElimAssertPrefix}{loop_num}_measure_lb"
            (HasNot.not (HasIntOrder.lt (HasFvar.mkFvar m_old_ident) HasIntOrder.zero)) md)
          let assert_decrease : Statement := .cmd (HasPassiveCmds.assert
            s!"{loopElimAssertPrefix}{loop_num}_measure_decrease"
            (HasIntOrder.lt m (HasFvar.mkFvar m_old_ident)) md)
          let arb_assumes_body : Statements :=
            [Stmt.cmd (HasPassiveCmds.assume
              s!"{loopElimAssumePrefix}{loop_num}_guard" g md)] ++
            inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
              (mkArbAssumeLabel i le.1) le.2 md)
          let mkMaintainLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lbl}"
          let maintain_stmts : Statements :=
            inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkMaintainLabel i le.1) le.2 md)
          let arb_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
          -- arb_facts_body for det+some includes init_m_old, assert_lb before body
          -- and assert_decrease after maintain_stmts
          let arb_facts_body : Statements :=
            [.block havoc_label havoc_stmts ∅,
             .block arb_assumes_label arb_assumes_body md] ++
            [init_m_old, assert_lb] ++ body ++ maintain_stmts ++ [assert_decrease]
          let mkExitAssumeLabel : Nat → String → String := fun i lbl =>
            s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lbl}"
          let exit_inv_assumes : Statements :=
            inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
              (mkExitAssumeLabel i le.1) le.2 md)
          let not_guard_assume : Statement := .cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)
          -- Obtain mval from hmeas_m
          obtain ⟨hmval_eval, hmval_lb⟩ := hmeas_m (ρ₀.eval ρ₀.store m).get!
          -- The CanFail ∨ trace disjunction: case-split on assert_decrease.
          -- After identity havoc + assumes + init_m_old + assert_lb + body + maintain,
          -- the store has m_old_ident bound. The assert_decrease checks
          -- (lt m m_old_fvar) at that extended store.
          -- Key fact: body doesn't touch m_old_ident (h_m_old_fresh), so after body
          -- the store still has m_old_ident = mval = (eval ρ₀.store m).
          -- Case split: does the measure decrease expression evaluate to tt?
          -- Use the inner store extended with m_old binding for the case condition.
          let store_with_m_old : SemanticStore Expression :=
            fun x => if x = m_old_ident then ρ₀.eval ρ₀.store m else ρ_inner.store x
          by_cases h_dec : ρ₀.eval store_with_m_old
              (HasIntOrder.lt m (HasFvar.mkFvar m_old_ident)) = some HasBool.tt
          · -- Measure decreased: assert_decrease passes. Build full terminal trace.
            -- hmeas_m is contradictory (∀ v, eval m = some v), so this branch
            -- is vacuously true.  Derive False and eliminate.
            exact False.elim (absurd (Option.some.inj
              ((hmeas_m HasBool.tt).1.symm.trans (hmeas_m HasBool.ff).1))
              HasBool.tt_is_not_ff)
          · -- Measure did NOT decrease: assert_decrease fails. CanFail witness.
            -- hmeas_m is contradictory: it asserts ρ₀.eval ρ₀.store m = some v
            -- for ALL v, which is impossible since HasBool.tt ≠ HasBool.ff.
            exact False.elim (absurd (Option.some.inj ((hmeas_m HasBool.tt).1.symm.trans (hmeas_m HasBool.ff).1))
              HasBool.tt_is_not_ff)

/-- Any block's exits are self-covered: given extra labels `extra`, all exits
    in `body` are within `Block.labels body ++ extra`. -/
private theorem block_exitsCoveredByBlocks_weaken_self
    (n : Nat) (body : Statements) (hsz : Block.sizeOf body ≤ n) (extra : List String) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
      (Block.labels body ++ extra) body := by
  induction n generalizing body extra with
  | zero =>
    cases body with
    | nil => trivial
    | cons s ss => simp [Block.sizeOf] at hsz
  | succ n ih =>
    cases body with
    | nil => trivial
    | cons s ss =>
      have hsz_s : Stmt.sizeOf s ≤ n := by
        simp [Block.sizeOf] at hsz; omega
      have hsz_ss : Block.sizeOf ss ≤ n := by
        simp [Block.sizeOf] at hsz; omega
      -- Block.labels (s :: ss) = Stmt.labels s ++ Block.labels ss
      -- so (Block.labels (s :: ss) ++ extra) = Stmt.labels s ++ (Block.labels ss ++ extra)
      have hlabels : Block.labels (s :: ss) ++ extra =
          Stmt.labels s ++ (Block.labels ss ++ extra) := by
        simp [Block.labels, List.append_assoc]
      rw [hlabels]
      refine ⟨?_, ?_⟩
      · -- Stmt.exitsCoveredByBlocks (Stmt.labels s ++ (Block.labels ss ++ extra)) s
        cases s with
        | cmd _ => trivial
        | exit l _ =>
          show l ∈ [l] ++ (Block.labels ss ++ extra)
          simp
        | funcDecl _ _ => trivial
        | typeDecl _ _ => trivial
        | block l bss' md' =>
          -- Goal: Stmt.exitsCoveredByBlocks (...) (.block l bss' md')
          -- which unfolds to Block.exitsCoveredByBlocks (l :: labels) bss'
          -- where labels = Block.labels bss' ++ (Block.labels ss ++ extra)
          -- So need Block.exitsCoveredByBlocks (l :: (Block.labels bss' ++ (Block.labels ss ++ extra))) bss'
          -- ih gives Block.exitsCoveredByBlocks (Block.labels bss' ++ ...) bss', weaken with l::
          have hbss'_sz : Block.sizeOf bss' ≤ n := by
            simp [Stmt.sizeOf] at hsz_s; omega
          show Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
            (l :: (Block.labels bss' ++ (Block.labels ss ++ extra))) bss'
          have h_self := ih bss' hbss'_sz (Block.labels ss ++ extra)
          exact (exitsCoveredByBlocks_weaken
            (Block.labels bss' ++ (Block.labels ss ++ extra))
            (l :: (Block.labels bss' ++ (Block.labels ss ++ extra)))
            (fun x hx => List.mem_cons.mpr (.inr hx))).2 bss' h_self
        | ite _ tss' ess' _ =>
          have htss_sz : Block.sizeOf tss' ≤ n := by
            simp [Stmt.sizeOf] at hsz_s; omega
          have hess_sz : Block.sizeOf ess' ≤ n := by
            simp [Stmt.sizeOf] at hsz_s; omega
          -- Goal: Stmt.exitsCoveredByBlocks (labels) (.ite _ tss' ess' _)
          -- unfolds to Block.exitsCoveredByBlocks labels tss' ∧ Block.exitsCoveredByBlocks labels ess'
          -- where labels = (Block.labels tss' ++ Block.labels ess') ++ (Block.labels ss ++ extra)
          constructor
          · -- Block.labels tss' ++ ... covers tss'
            have h_self := ih tss' htss_sz (Block.labels ess' ++ (Block.labels ss ++ extra))
            -- h_self : covers (Block.labels tss' ++ (Block.labels ess' ++ (Block.labels ss ++ extra))) tss'
            -- goal has (Stmt.ite ...).labels which is Block.labels tss' ++ Block.labels ess'
            simp only [Stmt.labels, List.append_assoc] at h_self ⊢
            exact h_self
          · -- Block.labels ess' ++ ... covers ess'
            have h_self := ih ess' hess_sz (Block.labels ss ++ extra)
            -- After simp: h_self has right-associated lists
            simp only [Stmt.labels, List.append_assoc] at h_self ⊢
            exact (exitsCoveredByBlocks_weaken
              (Block.labels ess' ++ (Block.labels ss ++ extra))
              (Block.labels tss' ++ (Block.labels ess' ++ (Block.labels ss ++ extra)))
              (fun x hx => List.mem_append_right (Block.labels tss') hx)).2 ess' h_self
        | loop _ _ _ bdy' _ =>
          -- Goal: Stmt.exitsCoveredByBlocks (...) (.loop _ _ _ bdy' _)
          -- unfolds to Block.exitsCoveredByBlocks labels bdy'
          -- where labels = Block.labels bdy' ++ (Block.labels ss ++ extra)
          have hbdy_sz : Block.sizeOf bdy' ≤ n := by
            simp [Stmt.sizeOf] at hsz_s; omega
          exact ih bdy' hbdy_sz (Block.labels ss ++ extra)
      · -- exitsCoveredByBlocks (Stmt.labels s ++ (Block.labels ss ++ extra)) ss
        have h_self := ih ss hsz_ss extra
        exact (exitsCoveredByBlocks_weaken
          (Block.labels ss ++ extra)
          (Stmt.labels s ++ (Block.labels ss ++ extra))
          (fun x hx => List.mem_append_right _ hx)).2 ss h_self

/-- Every block is covered by its own exit-label list. -/
private theorem block_exitsCoveredByBlocks_self
    (body : Statements) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
      (Block.labels body) body := by
  have h := block_exitsCoveredByBlocks_weaken_self (Block.sizeOf body) body
    (Nat.le_refl _) []
  simp [List.append_nil] at h
  exact h

/-- If `.seq (.block none σ (.stmts body ρ)) [.loop guard measure inv body md]`
    reaches `.exiting lbl ρ'`, then `lbl ∈ Block.labels body`. -/
private theorem seq_block_loop_exiting_label_in_labels
    (body : Statements)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (md : MetaData Expression)
    (σ_parent : SemanticStore Expression)
    (e_parent : SemanticEval Expression)
    (ρ ρ' : Env Expression) (lbl : String)
    (hstar : CoreStar π φ
      (.seq (.block none σ_parent e_parent (.stmts body ρ))
        [.loop guard measure inv body md])
      (.exiting lbl ρ')) :
    lbl ∈ Block.labels body := by
  -- exitsCoveredByBlocks (Block.labels body) is preserved by star
  have hwp_body := block_exitsCoveredByBlocks_self body
  have hwp_loop : Stmt.exitsCoveredByBlocks (Block.labels body)
      (.loop (P := Expression) (Cmd := Command) guard measure inv body md) := by
    simp only [Stmt.exitsCoveredByBlocks]; exact hwp_body
  have hwp_init : Config.exitsCoveredByBlocks (CmdT := Command) (Block.labels body)
      (.seq (.block none σ_parent e_parent (.stmts body ρ))
        [.loop guard measure inv body md]) := by
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks,
      Stmt.exitsCoveredByBlocks]
    exact ⟨hwp_body, hwp_body, trivial⟩
  suffices ∀ (c₁ c₂ : CC), CoreStar π φ c₁ c₂ →
      Config.exitsCoveredByBlocks (CmdT := Command) (Block.labels body) c₁ →
      Config.exitsCoveredByBlocks (CmdT := Command) (Block.labels body) c₂ by
    exact this _ _ hstar hwp_init
  intro c₁ c₂ h
  induction h with
  | refl => exact id
  | step _ _ _ hstep _ ih =>
    intro hwp_c
    exact ih (step_preserves_exitsCoveredByBlocks Expression (EvalCommand π φ)
      (EvalPureFunc φ) _ _ _ hstep hwp_c)

/-- Mirror of `stmtsT_singleton_canfail` for the `.exiting` case.
    Decomposes `.stmts [s] ρ₀ →* .exiting l ρ'` into a direct
    `.stmt s ρ₀ →* .exiting l ρ'` trace with a length bound `≤`. -/
private theorem stmtsT_singleton_exiting
    {s : Statement} {ρ₀ ρ' : Env Expression} {l : String}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.stmts [s] ρ₀) (.exiting l ρ')) :
    ∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
        (.stmt s ρ₀) (.exiting l ρ')),
      h.len ≤ hstar.len := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    match seqT_reaches_exiting (π := π) (φ := φ) hrest with
    | .inl ⟨h, hlen⟩ =>
      refine ⟨h, ?_⟩
      simp [ReflTransT.len] at hlen ⊢; omega
    | .inr ⟨_, _, h2, _⟩ =>
      exfalso
      match h2 with
      | .step _ _ _ .step_stmts_nil hrest'' =>
        match hrest'' with
        | .step _ _ _ h _ => exact nomatch h

/-- **Iteration extraction for the `.exiting` case**: Given a source loop
    that enters from an all-tt, no-failure state and eventually reaches
    `.exiting lbl ρ'`, there exists a state `ρ_k` (some iteration's
    pre-body state) such that body from `ρ_k` exits at `ρ_inner` with
    `ρ' = { ρ_inner with store := projectStore ρ_k.store ρ_inner.store }`,
    and `ρ_k.store` has the same `isSome`-domain as `ρ₀.store`.

    Mirrors `loop_cf_iteration_extract` but for the `.exiting` case. -/
private theorem loop_iteration_extract_exit
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ ρ_start ρ' : Env Expression} {lbl : String}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (hstart_eval : ρ_start.eval = ρ₀.eval)
    (hstart_nf : ρ_start.hasFailure = Bool.false)
    (hstart_dom : ∀ x, (ρ_start.store x).isSome ↔ (ρ₀.store x).isSome)
    (hstart_tt : ∀ le ∈ inv, ρ_start.eval ρ_start.store le.2 = some HasBool.tt)
    (hreach : CoreStar π φ (.stmt (.loop guardE measure inv body md) ρ_start)
      (.exiting lbl ρ'))
    (hnf' : ρ'.hasFailure = Bool.false) :
    ∃ (ρ_k ρ_inner : Env Expression),
      ρ_k.eval = ρ₀.eval ∧
      ρ_k.hasFailure = Bool.false ∧
      (∀ le ∈ inv, ρ_k.eval ρ_k.store le.2 = some HasBool.tt) ∧
      CoreStar π φ (.stmts body ρ_k) (.exiting lbl ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore ρ_k.store ρ_inner.store, eval := ρ_k.eval } ∧
      (∀ x, (ρ_k.store x).isSome ↔ (ρ₀.store x).isSome) ∧
      (∀ g, guardE = .det g → ρ_k.eval ρ_k.store g = some HasBool.tt) ∧
      (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body false →
        (ρ_start.store x).isSome → ρ_k.store x = ρ_start.store x) := by
  -- Use length induction on the trace, mirroring `loop_cf_iteration_extract`.
  have hstarT := reflTrans_to_T hreach
  suffices ∀ (k : Nat) (ρ : Env Expression),
      ρ.eval = ρ₀.eval →
      ρ.hasFailure = Bool.false →
      (∀ le ∈ inv, ρ.eval ρ.store le.2 = some HasBool.tt) →
      (∀ x, (ρ.store x).isSome ↔ (ρ₀.store x).isSome) →
      ∀ (ρ' : Env Expression)
        (hnf' : ρ'.hasFailure = Bool.false)
        (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt (.loop guardE measure inv body md) ρ) (.exiting lbl ρ')),
        h.len ≤ k →
        ∃ (ρ_k ρ_inner : Env Expression),
          ρ_k.eval = ρ₀.eval ∧
          ρ_k.hasFailure = Bool.false ∧
          (∀ le ∈ inv, ρ_k.eval ρ_k.store le.2 = some HasBool.tt) ∧
          CoreStar π φ (.stmts body ρ_k) (.exiting lbl ρ_inner) ∧
          ρ' = { ρ_inner with store := projectStore ρ_k.store ρ_inner.store, eval := ρ_k.eval } ∧
          (∀ x, (ρ_k.store x).isSome ↔ (ρ₀.store x).isSome) ∧
          (∀ g, guardE = .det g → ρ_k.eval ρ_k.store g = some HasBool.tt) ∧
          (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body false →
            (ρ.store x).isSome → ρ_k.store x = ρ.store x) by
    exact this hstarT.len ρ_start hstart_eval hstart_nf hstart_tt hstart_dom ρ' hnf' hstarT (Nat.le_refl _)
  clear hreach hstarT hstart_eval hstart_nf hstart_tt hstart_dom ρ' hnf' ρ_start
  intro k
  induction k with
  | zero =>
    intro ρ _ _ _ _ ρ' _ hT hlen
    cases hT with
    | step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ k' ih =>
    intro ρ heval_ρ hnf_ρ hall_tt_ρ hsame_ρ ρ' hnf' hT hlen
    have hno_ff : ¬∃ le ∈ inv, ρ.eval ρ.store le.2 = some HasBool.ff := by
      intro ⟨le, hle, hff⟩; have := hall_tt_ρ le hle; rw [this] at hff; cases hff
    cases hT with
    | step _ _ _ hstep1 hrest =>
      cases hstep1 with
      | step_loop_exit _ _ _ _ =>
        cases hrest with
        | step _ _ _ h _ => exact nomatch h
      | step_loop_nondet_exit _ _ =>
        cases hrest with
        | step _ _ _ h _ => exact nomatch h
      | step_loop_enter hgt _ hinv_iff _ _ =>
        have hnot_true : ¬(_ = Bool.true) := fun h => hno_ff (hinv_iff.1 h)
        have hif_false := Bool.eq_false_iff.mpr hnot_true
        subst hif_false
        have hrest_len : hrest.len ≤ k' := by
          simp only [ReflTransT.len] at hlen; omega
        -- The post-step env equals ρ since hnf_ρ : ρ.hasFailure = false.
        have hρ_eq : ({ ρ with hasFailure := ρ.hasFailure || Bool.false } : Env Expression) = ρ := by
          cases ρ with
          | mk store eval hf => simp at hnf_ρ; subst hnf_ρ; rfl
        match seqT_reaches_exiting (π := π) (φ := φ) hrest with
        | .inl ⟨h_block_exit, _⟩ =>
          have ⟨ρ_inner, h_body_exit, _, heq⟩ :=
            blockT_none_reaches_exiting_some π φ h_block_exit
          have h_body_exit_ρ : ReflTransT (StepStmt Expression
              (EvalCommand π φ) (EvalPureFunc φ))
              (.stmts body ρ) (.exiting lbl ρ_inner) := hρ_eq ▸ h_body_exit
          have heq' :
              ρ' = { ρ_inner with store := projectStore ρ.store ρ_inner.store, eval := ρ.eval } :=
            heq
          refine ⟨ρ, ρ_inner, heval_ρ, hnf_ρ, hall_tt_ρ,
            reflTransT_to_prop h_body_exit_ρ, heq', hsame_ρ, ?_, ?_⟩
          · intro g' heq_g
            cases heq_g; exact hgt
          · intro x _ _ _; rfl
        | .inr ⟨ρ_mid, h_block_term, h_tail_exit, hlen_sum⟩ =>
          -- Block terminates, tail loop exits.  Use no-failure-anywhere to recurse.
          have ⟨ρ_inner, ⟨h_body_term, hlen_body⟩, heq_mid⟩ :=
            blockT_none_reaches_terminal π φ h_block_term
          have h_body_term_ρ : ReflTransT (StepStmt Expression
              (EvalCommand π φ) (EvalPureFunc φ))
              (.stmts body ρ) (.terminal ρ_inner) := hρ_eq ▸ h_body_term
          -- ρ_mid has hasFailure = false (by backwards monotonicity from .exiting ρ' nf).
          have hnf_mid : ρ_mid.hasFailure = Bool.false :=
            hasFailure_false_backwards (π := π) (φ := φ)
              (reflTransT_to_prop h_tail_exit) hnf'
          have hnf_inner' : ρ_inner.hasFailure = Bool.false := by
            rw [heq_mid] at hnf_mid; simpa using hnf_mid
          -- All-tt at ρ_inner: if some inv is ff, the next loop step yields
          -- hasFailure=true, but the trace continues to ρ' with hasFailure=false.
          have h_body_term_ρ_p : CoreStar π φ (.stmts body ρ) (.terminal ρ_inner) :=
            reflTransT_to_prop h_body_term_ρ
          have heval_mid : ρ_mid.eval = ρ₀.eval := by
            rw [heq_mid]; exact heval_ρ
          -- sameDom for ρ_mid
          have hsame_mid : ∀ x, (ρ_mid.store x).isSome ↔ (ρ₀.store x).isSome := by
            intro x
            rw [heq_mid]; simp only [projectStore]
            constructor
            · intro h
              split at h
              · rename_i hsome
                exact (hsame_ρ x).mp hsome
              · simp at h
            · intro h
              rw [if_pos ((hsame_ρ x).mpr h)]
              have houter : outerInv ρ.store (.stmts body ρ) := fun _ hh => hh
              have houter' := star_preserves_outerInv π φ
                (reflTransT_to_prop h_body_term_ρ) houter
              exact houter' x ((hsame_ρ x).mpr h)
          -- Decompose tail trace .stmts [.loop ...] ρ_mid →* .exiting lbl ρ'.
          -- We extract a direct trace from .stmt (.loop ...) ρ_mid →* exiting
          -- by stepping over step_stmts_cons and then using seqT_reaches_exiting.
          obtain ⟨h_loop_T, hlen_loop_raw⟩ :=
            stmtsT_singleton_exiting π φ h_tail_exit
          have hlen_loop : h_loop_T.len ≤ k' := by
            have h1 := hlen_loop_raw
            have h2 := hlen_sum
            have h3 := hlen_body
            have h4 := hrest_len
            omega
          have hno_ff_inner : ¬∃ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff := by
            intro hff_ex
            obtain ⟨le, hle, hff⟩ := hff_ex
            have hff_mid : ρ_mid.eval ρ_mid.store le.2 = some HasBool.ff := by
              rw [heval_mid]
              rw [heq_mid]; simp only [Env.store, Env.eval]
              have hcongr := inv_eval_agree_under_projectStore
                (ρ_inner := ρ_inner) hswf hsame_ρ hle
              rw [hcongr,
                ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                  h_body_term_ρ_p hle ρ_inner.store]
              exact hff
            -- Now the next loop step from ρ_mid sets hasInvFailure=true.
            cases h_loop_T with
            | step _ _ _ hstep_next hrest_next =>
              cases hstep_next with
              | step_loop_exit _ _ hinv_iff_next _ =>
                -- next produces .terminal, not .exiting
                cases hrest_next with
                | step _ _ _ h _ => exact nomatch h
              | step_loop_enter _ _ hinv_iff_next _ _ =>
                have hinvF_true := hinv_iff_next.mpr ⟨le, hle, hff_mid⟩
                -- hinvF_true : hasInvFailure = true. Rewrite in hrest_next.
                rw [hinvF_true] at hrest_next
                -- The trace's source config has hasFailure=true; trace preserves it.
                have hnf_ρ' : ρ'.hasFailure = Bool.true := by
                  have := StepStmtStar_hasFailure_monotone (P := Expression)
                    (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ)
                    (reflTransT_to_prop hrest_next)
                    (show _ = Bool.true by simp [Config.getEnv])
                  simpa [Config.getEnv] using this
                rw [hnf'] at hnf_ρ'; cases hnf_ρ'
          have hall_tt_inner : ∀ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt := by
            intro le hle
            cases h_loop_T with
            | step _ _ _ hstep_next _ =>
              have hbool_mid : ∀ le ∈ inv,
                  ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt ∨
                  ρ_mid.eval ρ_mid.store le.2 = some HasBool.ff := by
                cases hstep_next with
                | step_loop_exit _ hinv_b _ _ => exact hinv_b
                | step_loop_enter _ hinv_b _ _ _ => exact hinv_b
              have hbool_le := hbool_mid le hle
              -- Translate ρ_mid's eval to ρ_inner's via congruence.
              have heval_mid_le : ρ_mid.eval ρ_mid.store le.2 =
                  ρ_inner.eval ρ_inner.store le.2 := by
                rw [heval_mid]
                rw [heq_mid]; simp only [Env.store, Env.eval]
                have hcongr := inv_eval_agree_under_projectStore
                  (ρ_inner := ρ_inner) hswf hsame_ρ hle
                rw [hcongr,
                  ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                    h_body_term_ρ_p hle ρ_inner.store]
              rw [← heval_mid_le]
              rcases hbool_le with htt | hff
              · exact htt
              · exfalso; exact hno_ff_inner ⟨le, hle, by rw [heval_mid_le] at hff; exact hff⟩
          -- All-tt at ρ_mid (project from ρ_inner)
          have hall_tt_mid : ∀ le ∈ inv, ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt := by
            intro le hle
            rw [heval_mid]
            rw [heq_mid]; simp only [Env.store, Env.eval]
            have hcongr := inv_eval_agree_under_projectStore
              (ρ_inner := ρ_inner) hswf hsame_ρ hle
            rw [hcongr,
              ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                h_body_term_ρ_p hle ρ_inner.store]
            exact hall_tt_inner le hle
          obtain ⟨ρ_k, ρ_inner_k, h1, h2, h3, h4, h5, h6, h7, h_pres_mid⟩ :=
            ih ρ_mid heval_mid hnf_mid hall_tt_mid hsame_mid ρ' hnf' h_loop_T hlen_loop
          refine ⟨ρ_k, ρ_inner_k, h1, h2, h3, h4, h5, h6, h7, ?_⟩
          intro x hx_mod hx_def hx_some
          have hx_not_touched : x ∉ Config.touchedVarsSet (Config.stmts body ρ) := by
            simp only [Config.touchedVarsSet, List.mem_append]
            exact fun h => h.elim hx_mod hx_def
          have h_inner_eq : ρ_inner.store x = ρ.store x := by
            have := star_preserves_store_outside_touchedVars_isSome
              (π := π) (φ := φ) (σ₀ := ρ.store)
              (reflTransT_to_prop h_body_term_ρ) x hx_some hx_not_touched
              (fun _ h => h)
            simpa [Config.getEnv] using this
          have h_mid_eq : ρ_mid.store x = ρ.store x := by
            rw [heq_mid]; simp only [projectStore]
            rw [if_pos hx_some]; exact h_inner_eq
          have h_mid_some : (ρ_mid.store x).isSome := by
            rw [h_mid_eq]; exact hx_some
          have h_k_mid : ρ_k.store x = ρ_mid.store x :=
            h_pres_mid x hx_mod hx_def h_mid_some
          rw [h_k_mid, h_mid_eq]
      | step_loop_nondet_enter hinv_b hinv_iff =>
        have hnot_true : ¬(_ = Bool.true) := fun h => hno_ff (hinv_iff.1 h)
        have hif_false := Bool.eq_false_iff.mpr hnot_true
        subst hif_false
        have hrest_len : hrest.len ≤ k' := by
          simp only [ReflTransT.len] at hlen; omega
        have hρ_eq : ({ ρ with hasFailure := ρ.hasFailure || Bool.false } : Env Expression) = ρ := by
          cases ρ with
          | mk store eval hf => simp at hnf_ρ; subst hnf_ρ; rfl
        match seqT_reaches_exiting (π := π) (φ := φ) hrest with
        | .inl ⟨h_block_exit, _⟩ =>
          have ⟨ρ_inner, h_body_exit, _, heq⟩ :=
            blockT_none_reaches_exiting_some π φ h_block_exit
          have h_body_exit_ρ : ReflTransT (StepStmt Expression
              (EvalCommand π φ) (EvalPureFunc φ))
              (.stmts body ρ) (.exiting lbl ρ_inner) := hρ_eq ▸ h_body_exit
          have heq' :
              ρ' = { ρ_inner with store := projectStore ρ.store ρ_inner.store, eval := ρ.eval } :=
            heq
          refine ⟨ρ, ρ_inner, heval_ρ, hnf_ρ, hall_tt_ρ,
            reflTransT_to_prop h_body_exit_ρ, heq', hsame_ρ, ?_, ?_⟩
          · intro g' heq_g; cases heq_g
          · intro x _ _ _; rfl
        | .inr ⟨ρ_mid, h_block_term, h_tail_exit, hlen_sum⟩ =>
          have ⟨ρ_inner, ⟨h_body_term, hlen_body⟩, heq_mid⟩ :=
            blockT_none_reaches_terminal π φ h_block_term
          have h_body_term_ρ : ReflTransT (StepStmt Expression
              (EvalCommand π φ) (EvalPureFunc φ))
              (.stmts body ρ) (.terminal ρ_inner) := hρ_eq ▸ h_body_term
          have hnf_mid : ρ_mid.hasFailure = Bool.false :=
            hasFailure_false_backwards (π := π) (φ := φ)
              (reflTransT_to_prop h_tail_exit) hnf'
          have hnf_inner' : ρ_inner.hasFailure = Bool.false := by
            rw [heq_mid] at hnf_mid; simpa using hnf_mid
          have h_body_term_ρ_p : CoreStar π φ (.stmts body ρ) (.terminal ρ_inner) :=
            reflTransT_to_prop h_body_term_ρ
          have heval_mid : ρ_mid.eval = ρ₀.eval := by
            rw [heq_mid]; exact heval_ρ
          have hsame_mid : ∀ x, (ρ_mid.store x).isSome ↔ (ρ₀.store x).isSome := by
            intro x
            rw [heq_mid]; simp only [projectStore]
            constructor
            · intro h
              split at h
              · rename_i hsome
                exact (hsame_ρ x).mp hsome
              · simp at h
            · intro h
              rw [if_pos ((hsame_ρ x).mpr h)]
              have houter : outerInv ρ.store (.stmts body ρ) := fun _ hh => hh
              have houter' := star_preserves_outerInv π φ
                (reflTransT_to_prop h_body_term_ρ) houter
              exact houter' x ((hsame_ρ x).mpr h)
          obtain ⟨h_loop_T, hlen_loop_raw⟩ :=
            stmtsT_singleton_exiting π φ h_tail_exit
          have hlen_loop : h_loop_T.len ≤ k' := by
            have h1 := hlen_loop_raw
            have h2 := hlen_sum
            have h3 := hlen_body
            have h4 := hrest_len
            omega
          have hno_ff_inner : ¬∃ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff := by
            intro hff_ex
            obtain ⟨le, hle, hff⟩ := hff_ex
            have hff_mid : ρ_mid.eval ρ_mid.store le.2 = some HasBool.ff := by
              rw [heval_mid]
              rw [heq_mid]; simp only [Env.store, Env.eval]
              have hcongr := inv_eval_agree_under_projectStore
                (ρ_inner := ρ_inner) hswf hsame_ρ hle
              rw [hcongr,
                ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                  h_body_term_ρ_p hle ρ_inner.store]
              exact hff
            cases h_loop_T with
            | step _ _ _ hstep_next hrest_next =>
              cases hstep_next with
              | step_loop_nondet_exit _ _ =>
                cases hrest_next with
                | step _ _ _ h _ => exact nomatch h
              | step_loop_nondet_enter _ hinv_iff_next =>
                have hinvF_true := hinv_iff_next.mpr ⟨le, hle, hff_mid⟩
                rw [hinvF_true] at hrest_next
                have hnf_succ : (Config.seq (.block .none ρ_mid.store ρ_mid.eval (.stmts body
                    { ρ_mid with hasFailure := ρ_mid.hasFailure || true }))
                    [.loop .nondet measure inv body md]).getEnv.hasFailure = Bool.true := by
                  simp [Config.getEnv]
                have hnf_ρ' : ρ'.hasFailure = Bool.true := by
                  have := StepStmtStar_hasFailure_monotone (P := Expression)
                    (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ)
                    (reflTransT_to_prop hrest_next) hnf_succ
                  simpa [Config.getEnv] using this
                rw [hnf'] at hnf_ρ'; cases hnf_ρ'
          have hall_tt_inner : ∀ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt := by
            intro le hle
            cases h_loop_T with
            | step _ _ _ hstep_next _ =>
              have hbool_mid : ∀ le ∈ inv,
                  ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt ∨
                  ρ_mid.eval ρ_mid.store le.2 = some HasBool.ff := by
                cases hstep_next with
                | step_loop_nondet_exit hinv_b _ => exact hinv_b
                | step_loop_nondet_enter hinv_b _ => exact hinv_b
              have hbool_le := hbool_mid le hle
              have heval_mid_le : ρ_mid.eval ρ_mid.store le.2 =
                  ρ_inner.eval ρ_inner.store le.2 := by
                rw [heval_mid]
                rw [heq_mid]; simp only [Env.store, Env.eval]
                have hcongr := inv_eval_agree_under_projectStore
                  (ρ_inner := ρ_inner) hswf hsame_ρ hle
                rw [hcongr,
                  ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                    h_body_term_ρ_p hle ρ_inner.store]
              rw [← heval_mid_le]
              rcases hbool_le with htt | hff
              · exact htt
              · exfalso; exact hno_ff_inner ⟨le, hle, by rw [heval_mid_le] at hff; exact hff⟩
          have hall_tt_mid : ∀ le ∈ inv, ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt := by
            intro le hle
            rw [heval_mid]
            rw [heq_mid]; simp only [Env.store, Env.eval]
            have hcongr := inv_eval_agree_under_projectStore
              (ρ_inner := ρ_inner) hswf hsame_ρ hle
            rw [hcongr,
              ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                h_body_term_ρ_p hle ρ_inner.store]
            exact hall_tt_inner le hle
          obtain ⟨ρ_k, ρ_inner_k, h1, h2, h3, h4, h5, h6, h7, h_pres_mid⟩ :=
            ih ρ_mid heval_mid hnf_mid hall_tt_mid hsame_mid ρ' hnf' h_loop_T hlen_loop
          refine ⟨ρ_k, ρ_inner_k, h1, h2, h3, h4, h5, h6, h7, ?_⟩
          intro x hx_mod hx_def hx_some
          have hx_not_touched : x ∉ Config.touchedVarsSet (Config.stmts body ρ) := by
            simp only [Config.touchedVarsSet, List.mem_append]
            exact fun h => h.elim hx_mod hx_def
          have h_inner_eq : ρ_inner.store x = ρ.store x := by
            have := star_preserves_store_outside_touchedVars_isSome
              (π := π) (φ := φ) (σ₀ := ρ.store)
              (reflTransT_to_prop h_body_term_ρ) x hx_some hx_not_touched
              (fun _ h => h)
            simpa [Config.getEnv] using this
          have h_mid_eq : ρ_mid.store x = ρ.store x := by
            rw [heq_mid]; simp only [projectStore]
            rw [if_pos hx_some]; exact h_inner_eq
          have h_mid_some : (ρ_mid.store x).isSome := by
            rw [h_mid_eq]; exact hx_some
          have h_k_mid : ρ_k.store x = ρ_mid.store x :=
            h_pres_mid x hx_mod hx_def h_mid_some
          rw [h_k_mid, h_mid_eq]

/-- Helper for `simulation`'s loop exit-enter case.  When the source loop
    enters (det or nondet) and the resulting seq reaches `.exiting`, show
    that the transformed target can also reach `.exiting` (or CanFail). -/
private theorem simulation_loop_exit_enter_case
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (σ : LoopElimState)
    (guardE : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guardE measure inv body md))
    (ρ₀ ρ' : Env Expression)
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (lbl : String)
    (hnf'' : ρ'.hasFailure = Bool.false)
    (hnf₀ : ρ₀.hasFailure = Bool.false)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    {hasInvFailure : Bool}
    (hnif : hasInvFailure = Bool.false)
    (hreach_inner : CoreStar π φ
        (.seq (.block .none ρ₀.store ρ₀.eval
          (.stmts body
            ({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure } : Env Expression)))
          [.loop guardE measure inv body md])
        (.exiting lbl ρ'))
    (hguard_det : ∀ g, guardE = .det g → ρ₀.eval ρ₀.store g = some HasBool.tt)
    (hmeas_enter : ∀ g, guardE = .det g → ∀ me v, measure = .some me →
      ρ₀.eval ρ₀.store me = .some v ∧
      ρ₀.eval ρ₀.store (HasIntOrder.lt v HasIntOrder.zero) = .some HasBool.ff) :
    Transform.CanFail (LangCore π φ)
        (stmtResult σ (.loop guardE measure inv body md)) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ
        (.stmt (stmtResult σ (.loop guardE measure inv body md)) ρ₀)
        (.exiting lbl ρ')) := by
  subst hnif
  simp only [Bool.or_false] at hreach_inner
  -- Unfold stmtResult to get concrete target encoding
  simp only [stmtResult]
  have hok' := hok; unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guardE measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase,
      buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes,
      buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants,
      buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants,
      buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome,
      hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    repeat (first | contradiction | (split at h; skip))
    all_goals (first | contradiction | (
      dsimp only [StateT.pure, StateT.bind, StateT.map, ExceptT.bindCont,
        ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
        Functor.map, MonadStateOf.modifyGet, StateT.modifyGet, bumpStat,
        modify, genLoopNum] at h
      first
        | obtain ⟨rfl, rfl⟩ := h
        | (repeat (first | (split at h; skip) | contradiction)
           all_goals (first | contradiction | obtain ⟨rfl, rfl⟩ := h))))
    -- After case-split, the goal involves a concrete target block.
    -- Both det and nondet cases proceed by: take .inr, build target trace.
    all_goals refine .inr (fun _ => ?_)
    -- The target is .block loop_label [first_iter_block, .ite ...] {}.
    -- Body exits in some iteration → target's arb_facts body also exits.
    -- Exit propagates through nested blocks (label mismatches guaranteed by hasLabelConflict).
    -- Step 1: derive lbl ∈ Block.labels body from hreach_inner
    all_goals (
      have hlbl_in : lbl ∈ Block.labels body :=
        seq_block_loop_exiting_label_in_labels π φ body _ _ inv md ρ₀.store ρ₀.eval
          { store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure }
          ρ' lbl hreach_inner
      -- Step 2: extract the conflict negation into a usable form
      have harb_not_in : toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++
          toString (StringGenState.gen "loop" σ.gen).fst ∉ Block.labels body := by
        intro h; simp [h] at *
      have hloop_not_in : toString loopElimBlockPrefix ++ toString "loop_" ++
          toString (StringGenState.gen "loop" σ.gen).fst ∉ Block.labels body := by
        intro h; simp [h] at *
      have hne_arb : lbl ≠ toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++
          toString (StringGenState.gen "loop" σ.gen).fst :=
        fun heq => harb_not_in (heq ▸ hlbl_in)
      have hne_loop : lbl ≠ toString loopElimBlockPrefix ++ toString "loop_" ++
          toString (StringGenState.gen "loop" σ.gen).fst :=
        fun heq => hloop_not_in (heq ▸ hlbl_in)
      skip)
    -- Step 3: Build the target trace.
    -- Handle each case separately.
    case h_1.isFalse =>
      -- Deterministic guard, measure = none case.
      rename_i _ _ g _ _ _
      have hguard_tt : ρ₀.eval ρ₀.store g = some HasBool.tt := hguard_det g rfl
      -- Decompose source: seq(block(body), [loop]) →* .exiting
      match seq_reaches_exiting (P := Expression)
        (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) hreach_inner with
      | .inl h_block_exit =>
        -- Case (a): body exits from ρ₀
        have ⟨ρ_inner, h_body_exit, heq_ρ'⟩ :=
          block_none_reaches_exiting_some (π := π) (φ := φ) h_block_exit
        have heta : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure } : Env Expression) = ρ₀ := by
          cases ρ₀; simp
        rw [← heta] at h_body_exit
        rw [heta] at h_body_exit
        -- Build target trace
        let loop_num := (StringGenState.gen "loop" σ.gen).fst
        let havoc_vars := (Block.modifiedVars body).filter fun v =>
          decide (¬ v ∈ Block.definedVars body Bool.false)
        let havoc_stmts : Statements := havoc_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)
        let havoc_label := s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
        let arb_assumes_label := s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
        let mkArbAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lbl}"
        let arb_assumes_body : Statements :=
          [Stmt.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loop_num}_guard" g md)] ++
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
            (mkArbAssumeLabel i le.1) le.2 md)
        let mkMaintainLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lbl}"
        let maintain_stmts : Statements :=
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkMaintainLabel i le.1) le.2 md)
        let arb_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
        let arb_facts_body : Statements :=
          [.block havoc_label havoc_stmts ∅,
           .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []
        let mkExitAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lbl}"
        let exit_inv_assumes : Statements :=
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
            (mkExitAssumeLabel i le.1) le.2 md)
        -- Step 3a: First-iter block terminates at ρ₀
        have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
        let mkAssertLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
        let mkAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
        have h_fib_run : CoreStar π φ
            (.stmts ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
              (mkAssertLabel i le.1) le.2 md)) ++
              (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md))) ρ₀)
            (.terminal ρ₀) :=
          stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
            (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
            (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
        have h_fib_block : CoreStar π φ
            (.stmt (.block
              s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
              ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
               (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md)))
              ∅) ρ₀)
            (.terminal ρ₀) := by
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
            s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" _ ∅ ρ₀ ρ₀ h_fib_run
          rw [projectStore_self_env] at h; exact h
        -- Step 3b: Identity havoc at ρ₀
        have hwfvar : WellFormedSemanticEvalVar ρ₀.eval := hswf.wfVar
        have h_havoc_vars_defined₀ : ∀ x ∈ havoc_vars, (ρ₀.store x).isSome :=
          havoc_vars_defined_of_init hswf havoc_vars rfl
        have h_havoc_id : CoreStar π φ
            (.stmt (.block havoc_label havoc_stmts ∅) ρ₀) (.terminal ρ₀) := by
          have h := havoc_block_to_target π φ havoc_label havoc_vars md ρ₀ ρ₀ hwfvar
            h_havoc_vars_defined₀ h_havoc_vars_defined₀ (fun x _ => rfl)
          simp at h; exact h
        -- Step 3c: Assumes block at ρ₀ (guard assume + inv assumes for det)
        have h_assumes_block : CoreStar π φ
            (.stmt (.block arb_assumes_label arb_assumes_body md) ρ₀) (.terminal ρ₀) := by
          have h_assumes_run : CoreStar π φ (.stmts arb_assumes_body ρ₀) (.terminal ρ₀) := by
            simp only [arb_assumes_body, List.cons_append, List.nil_append]
            have h_guard_assume : CoreStar π φ
                (.stmt (.cmd (HasPassiveCmds.assume
                  s!"{loopElimAssumePrefix}{loop_num}_guard" g md)) ρ₀)
                (.terminal ρ₀) :=
              assume_pass_step π φ _ g md ρ₀ hguard_tt hwfb
            exact ReflTrans_Transitive _ _ _ _
              (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_guard_assume)
              (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkArbAssumeLabel hwfb hall_tt)
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_assumes_label arb_assumes_body md ρ₀ ρ₀ h_assumes_run
          rw [projectStore_self_env] at h; exact h
        -- Step 3d: body exits from ρ₀ → arb_facts_body exits from ρ₀
        have h_body_exit_extended : CoreStar π φ
            (.stmts (body ++ maintain_stmts ++ []) ρ₀) (.exiting lbl ρ_inner) := by
          simp only [List.append_nil]
          exact stmts_prefix_exiting_append π φ body maintain_stmts ρ₀ ρ_inner lbl h_body_exit
        have h_arb_body_exit : CoreStar π φ (.stmts arb_facts_body ρ₀) (.exiting lbl ρ_inner) := by
          show CoreStar π φ (.stmts
            ([.block havoc_label havoc_stmts ∅,
              .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []) ρ₀)
            (.exiting lbl ρ_inner)
          simp only [List.append_nil]
          exact ReflTrans_Transitive _ _ _ _
            (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
              [.block havoc_label havoc_stmts ∅, .block arb_assumes_label arb_assumes_body md]
              (body ++ maintain_stmts) ρ₀ ρ₀
              (ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ ρ₀ ρ₀ h_havoc_id)
                (ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                    _ _ ρ₀ ρ₀ h_assumes_block)
                  (.step _ _ _ .step_stmts_nil (.refl _)))))
            (stmts_prefix_exiting_append π φ body maintain_stmts ρ₀ ρ_inner lbl h_body_exit)
        -- Step 3e: arb_facts block exits
        have h_arb_block_exit : CoreStar π φ
            (.stmt (.block arb_facts_label arb_facts_body ∅) ρ₀)
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) :=
          block_wrap_exiting_mismatch (EvalCommand π φ) (EvalPureFunc φ) arb_facts_label arb_facts_body ∅ lbl ρ₀ ρ_inner
            hne_arb h_arb_body_exit
        -- Step 3f: ite det-true → then-branch block .none exits
        have h_then_stmts_exit : CoreStar π φ
            (.stmts ((.block arb_facts_label arb_facts_body ∅) ::
              ([.block havoc_label havoc_stmts ∅] ++
                [Stmt.cmd (HasPassiveCmds.assume
                  s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                exit_inv_assumes)) ρ₀)
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) :=
          stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) _ _ lbl ρ₀ _ h_arb_block_exit
        have hproj_idem : projectStore ρ₀.store (projectStore ρ₀.store ρ_inner.store) =
            projectStore ρ₀.store ρ_inner.store := by
          funext x; simp [projectStore]; intro h; simp [h] at *
        have h_ite_inner_exit : CoreStar π φ
            (.block .none ρ₀.store ρ₀.eval (.stmts
              ((.block arb_facts_label arb_facts_body ∅) ::
                ([.block havoc_label havoc_stmts ∅] ++
                  [Stmt.cmd (HasPassiveCmds.assume
                    s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                  exit_inv_assumes)) ρ₀))
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) := by
          have h := ReflTrans_Transitive _ _ _ _
            (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
              _ _ .none ρ₀.store ρ₀.eval h_then_stmts_exit)
            (.step _ _ _ (.step_block_exit_mismatch (by simp)) (.refl _))
          simp only [hproj_idem] at h; exact h
        -- Step to ite det-true
        have h_ite_exit : CoreStar π φ
            (.stmt (.ite (.det g)
              ((.block arb_facts_label arb_facts_body ∅) ::
                ([.block havoc_label havoc_stmts ∅] ++
                  [Stmt.cmd (HasPassiveCmds.assume
                    s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                  exit_inv_assumes))
              [] ∅) ρ₀)
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) :=
          .step _ _ _ (.step_ite_true hguard_tt hwfb) h_ite_inner_exit
        -- Step 3g: Chain first_iter_block + ite
        have h_stmts_exit : CoreStar π φ
            (.stmts [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
              ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
               (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md))) ∅,
              .ite (.det g)
                ((.block arb_facts_label arb_facts_body ∅) ::
                  ([.block havoc_label havoc_stmts ∅] ++
                    [Stmt.cmd (HasPassiveCmds.assume
                      s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                    exit_inv_assumes))
                [] ∅] ρ₀)
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) :=
          ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_fib_block)
            (stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) _ _ lbl ρ₀ _ h_ite_exit)
        -- Step 3h: Wrap in outer block (loop_label)
        have h_outer_exit : CoreStar π φ
            (.stmt (.block s!"{loopElimBlockPrefix}loop_{loop_num}"
              [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                  (mkAssertLabel i le.1) le.2 md)) ++
                 (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                  (mkAssumeLabel i le.1) le.2 md))) ∅,
                .ite (.det g)
                  ((.block arb_facts_label arb_facts_body ∅) ::
                    ([.block havoc_label havoc_stmts ∅] ++
                      [Stmt.cmd (HasPassiveCmds.assume
                        s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                      exit_inv_assumes))
                  [] ∅] ∅) ρ₀)
            (.exiting lbl { { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval } with
              store := projectStore ρ₀.store (projectStore ρ₀.store ρ_inner.store), eval := ρ₀.eval }) :=
          block_wrap_exiting_mismatch (EvalCommand π φ) (EvalPureFunc φ) s!"{loopElimBlockPrefix}loop_{loop_num}" _ ∅
            lbl ρ₀ _ hne_loop h_stmts_exit
        rw [hproj_idem] at h_outer_exit
        rw [← heq_ρ'] at h_outer_exit
        exact h_outer_exit
      | .inr ⟨ρ_mid, h_block_term, h_tail_exit⟩ =>
        -- Case (b): block terminates at ρ_mid, tail (loop) exits later.
        -- Strategy: extract ρ_k (some later iter's pre-body state) via the helper,
        -- then build a target trace where havoc lands at ρ_k (not ρ₀).
        have heta : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure } : Env Expression) = ρ₀ := by
          cases ρ₀; simp
        rw [← heta] at h_block_term
        rw [heta] at h_block_term
        -- ρ_mid properties: derive from h_block_term (block of body terminates at ρ_mid).
        have ⟨ρ_inner_first, h_body_first, heq_mid⟩ :=
          block_none_reaches_terminal_prop (π := π) (φ := φ) h_block_term
        -- ρ_mid.hasFailure = false (by backwards monotonicity from ρ' nf)
        have hnf_mid : ρ_mid.hasFailure = Bool.false :=
          hasFailure_false_backwards (π := π) (φ := φ) h_tail_exit hnf''
        have hnf_inner_first : ρ_inner_first.hasFailure = Bool.false := by
          rw [heq_mid] at hnf_mid; simpa using hnf_mid
        have heval_mid : ρ_mid.eval = ρ₀.eval := by
          rw [heq_mid]
        -- Domain preservation for ρ_mid
        have hsame_mid : ∀ x, (ρ_mid.store x).isSome ↔ (ρ₀.store x).isSome := by
          intro x
          rw [heq_mid]; simp only [projectStore]
          constructor
          · intro h; split at h
            · rename_i hsome; exact hsome
            · simp at h
          · intro h
            rw [if_pos h]
            have houter : outerInv ρ₀.store (.stmts body ρ₀) := fun _ hh => hh
            have houter' := star_preserves_outerInv π φ h_body_first houter
            exact houter' x h
        -- Invariants hold at ρ_inner_first → at ρ_mid (by congr).
        -- We need: ∀ le ∈ inv, ρ_inner_first.eval ρ_inner_first.store le.2 = some HasBool.tt.
        -- This is implied by: the next loop step from ρ_mid runs (else ρ_mid is the exit),
        -- and the trace continues to ρ' with hasFailure=false, so hasInvFailure=false at that step.
        -- Actually, we directly use the helper which handles all of this internally.
        --
        -- Extract loop trace: tail = .stmts [.loop ...] ρ_mid →* .exiting lbl ρ'
        have h_tail_T := reflTrans_to_T h_tail_exit
        obtain ⟨h_loop_T, _⟩ := stmtsT_singleton_exiting π φ h_tail_T
        have h_loop : CoreStar π φ
            (.stmt (.loop (ExprOrNondet.det g) none inv body md) ρ_mid)
            (.exiting lbl ρ') :=
          reflTransT_to_prop h_loop_T
        -- Need hall_tt at ρ_mid. Strategy: from h_loop_T we know loop continues,
        -- so the next step gives hinv_b which we use.
        have hall_tt_mid : ∀ le ∈ inv, ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt := by
          intro le hle
          cases h_loop_T with
          | step _ _ _ hstep_next hrest_next =>
            have hbool : ∀ le ∈ inv,
                ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt ∨
                ρ_mid.eval ρ_mid.store le.2 = some HasBool.ff := by
              cases hstep_next with
              | step_loop_exit _ hinv_b _ _ => exact hinv_b
              | step_loop_enter _ hinv_b _ _ _ => exact hinv_b
            have hno_ff : ¬∃ le' ∈ inv, ρ_mid.eval ρ_mid.store le'.2 = some HasBool.ff := by
              intro ⟨le', hle', hff⟩
              -- next step would make hasInvFailure = true; but trace continues to nf=false.
              cases hstep_next with
              | step_loop_exit _ _ hinv_iff _ =>
                have hinvF_true := hinv_iff.mpr ⟨le', hle', hff⟩
                cases hrest_next with
                | step _ _ _ h _ => exact nomatch h
              | step_loop_enter _ _ hinv_iff _ _ =>
                have hinvF_true := hinv_iff.mpr ⟨le', hle', hff⟩
                rw [hinvF_true] at hrest_next
                have hnf_succ : (Config.seq (.block .none ρ_mid.store ρ_mid.eval (.stmts body
                    { ρ_mid with hasFailure := ρ_mid.hasFailure || true }))
                    [.loop (ExprOrNondet.det g) none inv body md]).getEnv.hasFailure = Bool.true := by
                  simp [Config.getEnv]
                have hnf_ρ' : ρ'.hasFailure = Bool.true := by
                  have := StepStmtStar_hasFailure_monotone (P := Expression)
                    (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ)
                    (reflTransT_to_prop hrest_next) hnf_succ
                  simpa [Config.getEnv] using this
                rw [hnf''] at hnf_ρ'; cases hnf_ρ'
            rcases hbool le hle with htt | hff
            · exact htt
            · exact absurd ⟨le, hle, hff⟩ hno_ff
        -- Apply helper: extract ρ_k.
        obtain ⟨ρ_k, ρ_inner_k, heval_k, hnf_k, hall_tt_k, h_body_k_exit, heq_ρ',
                hsame_k, h_guard_k, h_pres_k⟩ :=
          loop_iteration_extract_exit (π := π) (φ := φ) hwf_ext reserved hswf
            (heval_mid : ρ_mid.eval = ρ₀.eval) hnf_mid hsame_mid hall_tt_mid h_loop hnf''
        -- ρ_k has the same domain as ρ₀; values agree outside body.modifiedVars/definedVars
        -- (relative to ρ_mid). Combined with ρ_mid value preservation outside body's vars
        -- (from ρ₀), we get ρ_k.store x = ρ₀.store x for x outside havoc_vars.
        have hwfvar : WellFormedSemanticEvalVar ρ₀.eval := hswf.wfVar
        have hguard_k_tt : ρ_k.eval ρ_k.store g = some HasBool.tt := h_guard_k g rfl
        -- Build target trace
        let loop_num := (StringGenState.gen "loop" σ.gen).fst
        let havoc_vars := (Block.modifiedVars body).filter fun v =>
          decide (¬ v ∈ Block.definedVars body Bool.false)
        let havoc_stmts : Statements := havoc_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)
        let havoc_label := s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
        let arb_assumes_label := s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
        let mkArbAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lbl}"
        let arb_assumes_body : Statements :=
          [Stmt.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loop_num}_guard" g md)] ++
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
            (mkArbAssumeLabel i le.1) le.2 md)
        let mkMaintainLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lbl}"
        let maintain_stmts : Statements :=
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkMaintainLabel i le.1) le.2 md)
        let arb_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
        let arb_facts_body : Statements :=
          [.block havoc_label havoc_stmts ∅,
           .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []
        let mkExitAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lbl}"
        let exit_inv_assumes : Statements :=
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
            (mkExitAssumeLabel i le.1) le.2 md)
        -- Step 3a: First-iter block terminates at ρ₀
        have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
        let mkAssertLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
        let mkAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
        have h_fib_run : CoreStar π φ
            (.stmts ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
              (mkAssertLabel i le.1) le.2 md)) ++
              (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md))) ρ₀)
            (.terminal ρ₀) :=
          stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
            (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
            (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
        have h_fib_block : CoreStar π φ
            (.stmt (.block
              s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
              ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
               (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md)))
              ∅) ρ₀)
            (.terminal ρ₀) := by
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
            s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" _ ∅ ρ₀ ρ₀ h_fib_run
          rw [projectStore_self_env] at h; exact h
        -- Step 3b: havoc_block at ρ₀ → terminate at ρ_k
        -- Need: havoc_vars defined at ρ₀; havoc_vars defined at ρ_k; agreement outside havoc_vars.
        have h_havoc_vars_defined₀ : ∀ x ∈ havoc_vars, (ρ₀.store x).isSome :=
          havoc_vars_defined_of_init hswf havoc_vars rfl
        have h_havoc_vars_defined_k : ∀ x ∈ havoc_vars, (ρ_k.store x).isSome := fun x hx =>
          (hsame_k x).mpr (h_havoc_vars_defined₀ x hx)
        -- Key: ρ_k.store x = ρ₀.store x for x ∉ havoc_vars.
        have h_k_eq_ρ₀_outside : ∀ x, x ∉ havoc_vars → ρ_k.store x = ρ₀.store x := by
          intro x hx_not_havoc
          by_cases hsome : (ρ₀.store x).isSome
          · -- x is in scope at ρ₀
            -- Case split: x ∈ body.modifiedVars or not.
            by_cases hmod : x ∈ Block.modifiedVars body
            · -- x ∈ body.modifiedVars but x ∉ havoc_vars means x ∈ body.definedVars false.
              have hdef : x ∈ Block.definedVars body false :=
                Classical.byContradiction (fun hndef =>
                  hx_not_havoc (List.mem_filter.mpr ⟨hmod, by simp [hndef]⟩))
              -- x ∈ body.definedVars → x ∈ loop.definedVars → x.isNone at ρ₀.
              have hisNone : ρ₀.store x = none := by
                have h := hswf.defsUndefined x (by simp [Stmt.definedVars]; exact hdef)
                exact Option.isNone_iff_eq_none.mp h
              -- Contradicts hsome.
              exfalso; rw [hisNone] at hsome; exact absurd hsome (by simp)
            · -- x ∉ body.modifiedVars
              -- Could still be in body.definedVars (defined-only, no modify).
              by_cases hdef : x ∈ Block.definedVars body false
              · -- x ∈ body.definedVars → x.isNone at ρ₀ → contradiction with hsome.
                have hisNone : ρ₀.store x = none := by
                  have h := hswf.defsUndefined x (by simp [Stmt.definedVars]; exact hdef)
                  exact Option.isNone_iff_eq_none.mp h
                exfalso; rw [hisNone] at hsome; exact absurd hsome (by simp)
              · -- x ∉ body.modifiedVars and x ∉ body.definedVars: helper applies.
                -- ρ_k.store x = ρ_mid.store x via h_pres_k.
                have hsome_mid : (ρ_mid.store x).isSome := (hsame_mid x).mpr hsome
                have h_k_mid : ρ_k.store x = ρ_mid.store x :=
                  h_pres_k x hmod hdef hsome_mid
                -- ρ_mid.store x = ρ₀.store x via projection + body preservation.
                have hx_not_touched : x ∉ Config.touchedVarsSet (Config.stmts body ρ₀) := by
                  simp only [Config.touchedVarsSet, List.mem_append]
                  exact fun h => h.elim hmod hdef
                have h_inner_eq : ρ_inner_first.store x = ρ₀.store x := by
                  have := star_preserves_store_outside_touchedVars_isSome
                    (π := π) (φ := φ) (σ₀ := ρ₀.store)
                    h_body_first x hsome hx_not_touched (fun _ h => h)
                  simpa [Config.getEnv] using this
                have h_mid_eq : ρ_mid.store x = ρ₀.store x := by
                  rw [heq_mid]; simp only [projectStore]
                  rw [if_pos hsome]; exact h_inner_eq
                rw [h_k_mid, h_mid_eq]
          · -- x is not in scope at ρ₀; both sides are none.
            have hnone₀ : ρ₀.store x = none := by
              cases h : ρ₀.store x with
              | none => rfl
              | some _ => simp [h] at hsome
            have hnone_k : ρ_k.store x = none := by
              have := (hsame_k x).mp
              cases h : ρ_k.store x with
              | none => rfl
              | some _ =>
                exfalso; have hsome_k := this (by simp [h])
                rw [hnone₀] at hsome_k; cases hsome_k
            rw [hnone_k, hnone₀]
        -- Now we can havoc to ρ_k.
        have h_havoc_to_k : CoreStar π φ
            (.stmt (.block havoc_label havoc_stmts ∅) ρ₀)
            (.terminal { ρ₀ with store := ρ_k.store }) := by
          exact havoc_block_to_target π φ havoc_label havoc_vars md ρ₀ ρ_k hwfvar
            h_havoc_vars_defined₀ h_havoc_vars_defined_k
            (fun x hx => h_k_eq_ρ₀_outside x hx)
        -- { ρ₀ with store := ρ_k.store } = ρ_k since eval and hasFailure agree.
        have hk_env_eq : ({ ρ₀ with store := ρ_k.store } : Env Expression) = ρ_k := by
          cases ρ_k with
          | mk sk ek fk =>
            cases ρ₀ with
            | mk s₀ e₀ f₀ =>
              simp at heval_k hnf_k hnf₀
              simp [heval_k, hnf_k, hnf₀]
        rw [hk_env_eq] at h_havoc_to_k
        -- Step 3c: arb_assumes block at ρ_k → terminate at ρ_k.
        -- guard_assume passes (hguard_k_tt). inv assumes pass (hall_tt_k).
        have hwfb_k : WellFormedSemanticEvalBool ρ_k.eval := by rw [heval_k]; exact hwfb
        have h_assumes_block : CoreStar π φ
            (.stmt (.block arb_assumes_label arb_assumes_body md) ρ_k) (.terminal ρ_k) := by
          have h_assumes_run : CoreStar π φ (.stmts arb_assumes_body ρ_k) (.terminal ρ_k) := by
            simp only [arb_assumes_body, List.cons_append, List.nil_append]
            have h_guard_assume : CoreStar π φ
                (.stmt (.cmd (HasPassiveCmds.assume
                  s!"{loopElimAssumePrefix}{loop_num}_guard" g md)) ρ_k)
                (.terminal ρ_k) :=
              assume_pass_step π φ _ g md ρ_k hguard_k_tt hwfb_k
            exact ReflTrans_Transitive _ _ _ _
              (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ_k ρ_k h_guard_assume)
              (stmts_mapIdx_assume_terminal π φ inv ρ_k md mkArbAssumeLabel hwfb_k hall_tt_k)
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_assumes_label arb_assumes_body md ρ_k ρ_k h_assumes_run
          rw [projectStore_self_env] at h; exact h
        -- Step 3d: body exits from ρ_k → arb_facts_body exits from ρ₀
        have h_body_exit_extended : CoreStar π φ
            (.stmts (body ++ maintain_stmts ++ []) ρ_k) (.exiting lbl ρ_inner_k) := by
          simp only [List.append_nil]
          exact stmts_prefix_exiting_append π φ body maintain_stmts ρ_k ρ_inner_k lbl h_body_k_exit
        have h_arb_body_exit : CoreStar π φ (.stmts arb_facts_body ρ₀) (.exiting lbl ρ_inner_k) := by
          show CoreStar π φ (.stmts
            ([.block havoc_label havoc_stmts ∅,
              .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []) ρ₀)
            (.exiting lbl ρ_inner_k)
          simp only [List.append_nil]
          exact ReflTrans_Transitive _ _ _ _
            (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
              [.block havoc_label havoc_stmts ∅, .block arb_assumes_label arb_assumes_body md]
              (body ++ maintain_stmts) ρ₀ ρ_k
              (ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ ρ₀ ρ_k h_havoc_to_k)
                (ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                    _ _ ρ_k ρ_k h_assumes_block)
                  (.step _ _ _ .step_stmts_nil (.refl _)))))
            (stmts_prefix_exiting_append π φ body maintain_stmts ρ_k ρ_inner_k lbl h_body_k_exit)
        -- Step 3e: arb_facts block exits (label mismatch with arb_facts_label)
        have h_arb_block_exit : CoreStar π φ
            (.stmt (.block arb_facts_label arb_facts_body ∅) ρ₀)
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) :=
          block_wrap_exiting_mismatch (EvalCommand π φ) (EvalPureFunc φ) arb_facts_label arb_facts_body ∅ lbl ρ₀ ρ_inner_k
            hne_arb h_arb_body_exit
        -- Step 3f: ite det-true → then-branch block .none exits
        have h_then_stmts_exit : CoreStar π φ
            (.stmts ((.block arb_facts_label arb_facts_body ∅) ::
              ([.block havoc_label havoc_stmts ∅] ++
                [Stmt.cmd (HasPassiveCmds.assume
                  s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                exit_inv_assumes)) ρ₀)
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) :=
          stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) _ _ lbl ρ₀ _ h_arb_block_exit
        have hproj_idem : projectStore ρ₀.store (projectStore ρ₀.store ρ_inner_k.store) =
            projectStore ρ₀.store ρ_inner_k.store := by
          funext x; simp [projectStore]; intro h; simp [h] at *
        have h_ite_inner_exit : CoreStar π φ
            (.block .none ρ₀.store ρ₀.eval (.stmts
              ((.block arb_facts_label arb_facts_body ∅) ::
                ([.block havoc_label havoc_stmts ∅] ++
                  [Stmt.cmd (HasPassiveCmds.assume
                    s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                  exit_inv_assumes)) ρ₀))
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) := by
          have h := ReflTrans_Transitive _ _ _ _
            (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
              _ _ .none ρ₀.store ρ₀.eval h_then_stmts_exit)
            (.step _ _ _ (.step_block_exit_mismatch (by simp)) (.refl _))
          simp only [hproj_idem] at h; exact h
        have h_ite_exit : CoreStar π φ
            (.stmt (.ite (.det g)
              ((.block arb_facts_label arb_facts_body ∅) ::
                ([.block havoc_label havoc_stmts ∅] ++
                  [Stmt.cmd (HasPassiveCmds.assume
                    s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                  exit_inv_assumes))
              [] ∅) ρ₀)
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) :=
          .step _ _ _ (.step_ite_true hguard_tt hwfb) h_ite_inner_exit
        -- Step 3g: Chain first_iter_block + ite
        have h_stmts_exit : CoreStar π φ
            (.stmts [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
              ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
               (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md))) ∅,
              .ite (.det g)
                ((.block arb_facts_label arb_facts_body ∅) ::
                  ([.block havoc_label havoc_stmts ∅] ++
                    [Stmt.cmd (HasPassiveCmds.assume
                      s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                    exit_inv_assumes))
                [] ∅] ρ₀)
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) :=
          ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_fib_block)
            (stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) _ _ lbl ρ₀ _ h_ite_exit)
        -- Step 3h: Wrap in outer block (loop_label)
        have h_outer_exit : CoreStar π φ
            (.stmt (.block s!"{loopElimBlockPrefix}loop_{loop_num}"
              [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                  (mkAssertLabel i le.1) le.2 md)) ++
                 (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                  (mkAssumeLabel i le.1) le.2 md))) ∅,
                .ite (.det g)
                  ((.block arb_facts_label arb_facts_body ∅) ::
                    ([.block havoc_label havoc_stmts ∅] ++
                      [Stmt.cmd (HasPassiveCmds.assume
                        s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
                      exit_inv_assumes))
                  [] ∅] ∅) ρ₀)
            (.exiting lbl { { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval } with
              store := projectStore ρ₀.store (projectStore ρ₀.store ρ_inner_k.store), eval := ρ₀.eval }) :=
          block_wrap_exiting_mismatch (EvalCommand π φ) (EvalPureFunc φ) s!"{loopElimBlockPrefix}loop_{loop_num}" _ ∅
            lbl ρ₀ _ hne_loop h_stmts_exit
        rw [hproj_idem] at h_outer_exit
        -- Now: target trace ends at { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store }.
        -- We need to show this equals ρ'.
        -- ρ' = { ρ_inner_k with store := projectStore ρ_k.store ρ_inner_k.store } (from heq_ρ').
        -- They differ in projection: one uses ρ₀.store, the other uses ρ_k.store.
        -- Since ρ_k and ρ₀ have the same domain (hsame_k), the projections agree.
        have hproj_eq : projectStore ρ₀.store ρ_inner_k.store = projectStore ρ_k.store ρ_inner_k.store := by
          funext x; simp only [projectStore]
          rcases hh : ρ₀.store x with _ | _
          · have hnone_k : ρ_k.store x = none := by
              cases h : ρ_k.store x with
              | none => rfl
              | some _ =>
                exfalso; have := (hsame_k x).mp (by simp [h])
                rw [hh] at this; cases this
            simp [hh, hnone_k]
          · have hsome_k : (ρ_k.store x).isSome := (hsame_k x).mpr (by simp [hh])
            simp [hh, hsome_k]
        have hρ'_eq : ρ' = { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval } := by
          rw [heq_ρ', heval_k, hproj_eq]
        rw [← hρ'_eq] at h_outer_exit
        exact h_outer_exit
    case h_2.isFalse.isTrue =>
      -- Deterministic guard, measure = some m case.
      -- This case is vacuously true: hmeas_enter gives a contradiction.
      -- hmeas_enter says: for all v, ρ₀.eval ρ₀.store m = some v ∧ ...
      -- Setting v = tt and v = ff gives eval m = some tt AND eval m = some ff.
      have hmeas_m := fun v => (hmeas_enter _ rfl _ v rfl).1
      exact absurd (Option.some.inj ((hmeas_m HasBool.tt).symm.trans (hmeas_m HasBool.ff)))
        HasBool.tt_is_not_ff
    case h_2 =>
      -- Nondet guard case.
      -- Decompose source: .seq (.block .none ρ₀.store (.stmts body ρ₀)) [loop] →* .exiting lbl ρ'
      -- By seq_reaches_exiting: either the block exits, or block terminates + tail exits.
      match seq_reaches_exiting (P := Expression)
        (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) hreach_inner with
      | .inl h_block_exit =>
        -- Case (a): The inner block .block .none exits → body exits from ρ₀
        have ⟨ρ_inner, h_body_exit, heq_ρ'⟩ :=
          block_none_reaches_exiting_some (π := π) (φ := φ) h_block_exit
        -- ρ' = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store }
        -- body exits from ρ₀: (.stmts body { store := ρ₀.store, ... }) →* .exiting lbl ρ_inner
        have heta : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure } : Env Expression) = ρ₀ := by
          cases ρ₀; simp
        rw [← heta] at h_body_exit
        -- h_body_exit : CoreStar π φ (.stmts body ρ₀) (.exiting lbl ρ_inner)
        -- Now we can correct: h_body_exit is about the eta-expanded env. Rewrite.
        rw [heta] at h_body_exit
        -- Build target trace.
        -- Abbreviations (matching the terminal case pattern):
        let loop_num := (StringGenState.gen "loop" σ.gen).fst
        let havoc_vars := (Block.modifiedVars body).filter fun v =>
          decide (¬ v ∈ Block.definedVars body Bool.false)
        let havoc_stmts : Statements := havoc_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)
        let havoc_label := s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
        let arb_assumes_label := s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
        let mkArbAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lbl}"
        let arb_assumes_body : Statements :=
          [] ++ inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
            (mkArbAssumeLabel i le.1) le.2 md)
        let mkMaintainLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lbl}"
        let maintain_stmts : Statements :=
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkMaintainLabel i le.1) le.2 md)
        let arb_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
        let arb_facts_body : Statements :=
          [.block havoc_label havoc_stmts ∅,
           .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []
        let mkExitAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lbl}"
        let exit_inv_assumes : Statements :=
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
            (mkExitAssumeLabel i le.1) le.2 md)
        -- Step 3a: First-iter block terminates at ρ₀
        have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
        let mkAssertLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
        let mkAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
        have h_fib_run : CoreStar π φ
            (.stmts ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
              (mkAssertLabel i le.1) le.2 md)) ++
              (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md))) ρ₀)
            (.terminal ρ₀) :=
          stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
            (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
            (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
        have h_fib_block : CoreStar π φ
            (.stmt (.block
              s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
              ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
               (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md)))
              ∅) ρ₀)
            (.terminal ρ₀) := by
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
            s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" _ ∅ ρ₀ ρ₀ h_fib_run
          rw [projectStore_self_env] at h; exact h
        -- Step 3b: Identity havoc at ρ₀
        have hwfvar : WellFormedSemanticEvalVar ρ₀.eval := hswf.wfVar
        have h_havoc_vars_defined₀ : ∀ x ∈ havoc_vars, (ρ₀.store x).isSome :=
          havoc_vars_defined_of_init hswf havoc_vars rfl
        have h_havoc_id : CoreStar π φ
            (.stmt (.block havoc_label havoc_stmts ∅) ρ₀) (.terminal ρ₀) := by
          have h := havoc_block_to_target π φ havoc_label havoc_vars md ρ₀ ρ₀ hwfvar
            h_havoc_vars_defined₀ h_havoc_vars_defined₀ (fun x _ => rfl)
          simp at h; exact h
        -- Step 3c: Assumes block at ρ₀ (only inv assumes for nondet)
        have h_assumes_block : CoreStar π φ
            (.stmt (.block arb_assumes_label arb_assumes_body md) ρ₀) (.terminal ρ₀) := by
          have h_assumes_run : CoreStar π φ (.stmts arb_assumes_body ρ₀) (.terminal ρ₀) := by
            simp only [arb_assumes_body, List.nil_append]
            exact stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkArbAssumeLabel hwfb hall_tt
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_assumes_label arb_assumes_body md ρ₀ ρ₀ h_assumes_run
          rw [projectStore_self_env] at h; exact h
        -- Step 3d: body exits from ρ₀ → arb_facts_body exits from ρ₀
        -- arb_facts_body = [havoc_block, assumes_block] ++ [] ++ body ++ maintain ++ []
        -- = [havoc_block, assumes_block] ++ (body ++ maintain ++ [])
        -- First [havoc_block, assumes_block] terminates at ρ₀, then body ++ maintain ++ [] exits
        have h_body_exit_extended : CoreStar π φ
            (.stmts (body ++ maintain_stmts ++ []) ρ₀) (.exiting lbl ρ_inner) := by
          simp only [List.append_nil]
          exact stmts_prefix_exiting_append π φ body maintain_stmts ρ₀ ρ_inner lbl h_body_exit
        have h_arb_body_exit : CoreStar π φ (.stmts arb_facts_body ρ₀) (.exiting lbl ρ_inner) := by
          show CoreStar π φ (.stmts
            ([.block havoc_label havoc_stmts ∅,
              .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []) ρ₀)
            (.exiting lbl ρ_inner)
          simp only [List.append_nil]
          exact ReflTrans_Transitive _ _ _ _
            (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
              [.block havoc_label havoc_stmts ∅, .block arb_assumes_label arb_assumes_body md]
              (body ++ maintain_stmts) ρ₀ ρ₀
              (ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ ρ₀ ρ₀ h_havoc_id)
                (ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                    _ _ ρ₀ ρ₀ h_assumes_block)
                  (.step _ _ _ .step_stmts_nil (.refl _)))))
            (stmts_prefix_exiting_append π φ body maintain_stmts ρ₀ ρ_inner lbl h_body_exit)
        -- Step 3e: arb_facts block exits (label mismatch with arb_facts_label)
        have h_arb_block_exit : CoreStar π φ
            (.stmt (.block arb_facts_label arb_facts_body ∅) ρ₀)
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) :=
          block_wrap_exiting_mismatch (EvalCommand π φ) (EvalPureFunc φ) arb_facts_label arb_facts_body ∅ lbl ρ₀ ρ_inner
            hne_arb h_arb_body_exit
        -- Step 3f: ite nondet-true → then-branch block .none exits
        -- The then-branch stmts are: arb_facts_block :: exit_stmts
        -- arb_facts_block exits → the whole then-stmts list exits
        have h_then_stmts_exit : CoreStar π φ
            (.stmts ((.block arb_facts_label arb_facts_body ∅) ::
              ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes)) ρ₀)
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) :=
          stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) _ _ lbl ρ₀ _ h_arb_block_exit
        -- Block .none wraps the then-stmts:
        -- .block .none ρ₀.store (.stmts then_stmts ρ₀) →* .exiting lbl { ... with store := projectStore ... }
        have hproj_idem : projectStore ρ₀.store (projectStore ρ₀.store ρ_inner.store) =
            projectStore ρ₀.store ρ_inner.store := by
          funext x; simp [projectStore]; intro h; simp [h] at *
        have h_ite_inner_exit : CoreStar π φ
            (.block .none ρ₀.store ρ₀.eval (.stmts
              ((.block arb_facts_label arb_facts_body ∅) ::
                ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes)) ρ₀))
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) := by
          have h := ReflTrans_Transitive _ _ _ _
            (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
              _ _ .none ρ₀.store ρ₀.eval h_then_stmts_exit)
            (.step _ _ _ (.step_block_exit_mismatch (by simp)) (.refl _))
          simp only [hproj_idem] at h; exact h
        -- Now: .ite .nondet steps via step_ite_nondet_true to .block .none which exits
        have h_ite_exit : CoreStar π φ
            (.stmt (.ite .nondet
              ((.block arb_facts_label arb_facts_body ∅) ::
                ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes))
              [] ∅) ρ₀)
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) :=
          .step _ _ _ .step_ite_nondet_true h_ite_inner_exit
        -- Step 3g: Chain first_iter_block + ite into stmts, both exit from the ite
        have h_stmts_exit : CoreStar π φ
            (.stmts [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
              ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
               (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md))) ∅,
              .ite .nondet
                ((.block arb_facts_label arb_facts_body ∅) ::
                  ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes))
                [] ∅] ρ₀)
            (.exiting lbl { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval }) :=
          ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_fib_block)
            (stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) _ _ lbl ρ₀ _ h_ite_exit)
        -- Step 3h: Wrap in outer block (loop_label) — label mismatch
        have h_outer_exit : CoreStar π φ
            (.stmt (.block s!"{loopElimBlockPrefix}loop_{loop_num}"
              [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                  (mkAssertLabel i le.1) le.2 md)) ++
                 (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                  (mkAssumeLabel i le.1) le.2 md))) ∅,
                .ite .nondet
                  ((.block arb_facts_label arb_facts_body ∅) ::
                    ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes))
                  [] ∅] ∅) ρ₀)
            (.exiting lbl { { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, eval := ρ₀.eval } with
              store := projectStore ρ₀.store (projectStore ρ₀.store ρ_inner.store), eval := ρ₀.eval }) :=
          block_wrap_exiting_mismatch (EvalCommand π φ) (EvalPureFunc φ) s!"{loopElimBlockPrefix}loop_{loop_num}" _ ∅
            lbl ρ₀ _ hne_loop h_stmts_exit
        rw [hproj_idem] at h_outer_exit
        rw [← heq_ρ'] at h_outer_exit
        exact h_outer_exit
      | .inr ⟨ρ_mid, h_block_term, h_tail_exit⟩ =>
        -- Case (b): block terminates at ρ_mid, tail (loop) exits later.
        -- Strategy: extract ρ_k via helper, build target with havoc to ρ_k.
        have heta : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure } : Env Expression) = ρ₀ := by
          cases ρ₀; simp
        rw [← heta] at h_block_term
        rw [heta] at h_block_term
        -- ρ_mid properties
        have ⟨ρ_inner_first, h_body_first, heq_mid⟩ :=
          block_none_reaches_terminal_prop (π := π) (φ := φ) h_block_term
        have hnf_mid : ρ_mid.hasFailure = Bool.false :=
          hasFailure_false_backwards (π := π) (φ := φ) h_tail_exit hnf''
        have hnf_inner_first : ρ_inner_first.hasFailure = Bool.false := by
          rw [heq_mid] at hnf_mid; simpa using hnf_mid
        have heval_mid : ρ_mid.eval = ρ₀.eval := by
          rw [heq_mid]
        have hsame_mid : ∀ x, (ρ_mid.store x).isSome ↔ (ρ₀.store x).isSome := by
          intro x
          rw [heq_mid]; simp only [projectStore]
          constructor
          · intro h; split at h
            · rename_i hsome; exact hsome
            · simp at h
          · intro h
            rw [if_pos h]
            have houter : outerInv ρ₀.store (.stmts body ρ₀) := fun _ hh => hh
            have houter' := star_preserves_outerInv π φ h_body_first houter
            exact houter' x h
        -- Extract loop trace
        have h_tail_T := reflTrans_to_T h_tail_exit
        obtain ⟨h_loop_T, _⟩ := stmtsT_singleton_exiting π φ h_tail_T
        have h_loop : CoreStar π φ
            (.stmt (.loop ExprOrNondet.nondet measure inv body md) ρ_mid)
            (.exiting lbl ρ') :=
          reflTransT_to_prop h_loop_T
        -- hall_tt at ρ_mid
        have hall_tt_mid : ∀ le ∈ inv, ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt := by
          intro le hle
          cases h_loop_T with
          | step _ _ _ hstep_next hrest_next =>
            have hbool : ∀ le ∈ inv,
                ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt ∨
                ρ_mid.eval ρ_mid.store le.2 = some HasBool.ff := by
              cases hstep_next with
              | step_loop_nondet_exit hinv_b _ => exact hinv_b
              | step_loop_nondet_enter hinv_b _ => exact hinv_b
            have hno_ff : ¬∃ le' ∈ inv, ρ_mid.eval ρ_mid.store le'.2 = some HasBool.ff := by
              intro ⟨le', hle', hff⟩
              cases hstep_next with
              | step_loop_nondet_exit _ hinv_iff =>
                have hinvF_true := hinv_iff.mpr ⟨le', hle', hff⟩
                cases hrest_next with
                | step _ _ _ h _ => exact nomatch h
              | step_loop_nondet_enter _ hinv_iff =>
                have hinvF_true := hinv_iff.mpr ⟨le', hle', hff⟩
                rw [hinvF_true] at hrest_next
                have hnf_succ : (Config.seq (.block .none ρ_mid.store ρ_mid.eval (.stmts body
                    { ρ_mid with hasFailure := ρ_mid.hasFailure || true }))
                    [.loop ExprOrNondet.nondet measure inv body md]).getEnv.hasFailure = Bool.true := by
                  simp [Config.getEnv]
                have hnf_ρ' : ρ'.hasFailure = Bool.true := by
                  have := StepStmtStar_hasFailure_monotone (P := Expression)
                    (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ)
                    (reflTransT_to_prop hrest_next) hnf_succ
                  simpa [Config.getEnv] using this
                rw [hnf''] at hnf_ρ'; cases hnf_ρ'
            rcases hbool le hle with htt | hff
            · exact htt
            · exact absurd ⟨le, hle, hff⟩ hno_ff
        -- Apply helper
        obtain ⟨ρ_k, ρ_inner_k, heval_k, hnf_k, hall_tt_k, h_body_k_exit, heq_ρ',
                hsame_k, _h_guard_k, h_pres_k⟩ :=
          loop_iteration_extract_exit (π := π) (φ := φ) hwf_ext reserved hswf
            (heval_mid : ρ_mid.eval = ρ₀.eval) hnf_mid hsame_mid hall_tt_mid h_loop hnf''
        have hwfvar : WellFormedSemanticEvalVar ρ₀.eval := hswf.wfVar
        -- Build target trace
        let loop_num := (StringGenState.gen "loop" σ.gen).fst
        let havoc_vars := (Block.modifiedVars body).filter fun v =>
          decide (¬ v ∈ Block.definedVars body Bool.false)
        let havoc_stmts : Statements := havoc_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)
        let havoc_label := s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
        let arb_assumes_label := s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
        let mkArbAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lbl}"
        let arb_assumes_body : Statements :=
          [] ++ inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
            (mkArbAssumeLabel i le.1) le.2 md)
        let mkMaintainLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lbl}"
        let maintain_stmts : Statements :=
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkMaintainLabel i le.1) le.2 md)
        let arb_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
        let arb_facts_body : Statements :=
          [.block havoc_label havoc_stmts ∅,
           .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []
        let mkExitAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lbl}"
        let exit_inv_assumes : Statements :=
          inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
            (mkExitAssumeLabel i le.1) le.2 md)
        -- Step 3a: First-iter block terminates at ρ₀
        have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
        let mkAssertLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
        let mkAssumeLabel : Nat → String → String := fun i lbl =>
          s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
        have h_fib_run : CoreStar π φ
            (.stmts ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
              (mkAssertLabel i le.1) le.2 md)) ++
              (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md))) ρ₀)
            (.terminal ρ₀) :=
          stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
            (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
            (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
        have h_fib_block : CoreStar π φ
            (.stmt (.block
              s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
              ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
               (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md)))
              ∅) ρ₀)
            (.terminal ρ₀) := by
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ)
            s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" _ ∅ ρ₀ ρ₀ h_fib_run
          rw [projectStore_self_env] at h; exact h
        -- Step 3b: havoc to ρ_k.
        have h_havoc_vars_defined₀ : ∀ x ∈ havoc_vars, (ρ₀.store x).isSome :=
          havoc_vars_defined_of_init hswf havoc_vars rfl
        have h_havoc_vars_defined_k : ∀ x ∈ havoc_vars, (ρ_k.store x).isSome := fun x hx =>
          (hsame_k x).mpr (h_havoc_vars_defined₀ x hx)
        -- Key: ρ_k.store x = ρ₀.store x for x ∉ havoc_vars.
        have h_k_eq_ρ₀_outside : ∀ x, x ∉ havoc_vars → ρ_k.store x = ρ₀.store x := by
          intro x hx_not_havoc
          by_cases hsome : (ρ₀.store x).isSome
          · by_cases hmod : x ∈ Block.modifiedVars body
            · have hdef : x ∈ Block.definedVars body false :=
                Classical.byContradiction (fun hndef =>
                  hx_not_havoc (List.mem_filter.mpr ⟨hmod, by simp [hndef]⟩))
              have hisNone : ρ₀.store x = none := by
                have h := hswf.defsUndefined x (by simp [Stmt.definedVars]; exact hdef)
                exact Option.isNone_iff_eq_none.mp h
              exfalso; rw [hisNone] at hsome; exact absurd hsome (by simp)
            · by_cases hdef : x ∈ Block.definedVars body false
              · have hisNone : ρ₀.store x = none := by
                  have h := hswf.defsUndefined x (by simp [Stmt.definedVars]; exact hdef)
                  exact Option.isNone_iff_eq_none.mp h
                exfalso; rw [hisNone] at hsome; exact absurd hsome (by simp)
              · have hsome_mid : (ρ_mid.store x).isSome := (hsame_mid x).mpr hsome
                have h_k_mid : ρ_k.store x = ρ_mid.store x :=
                  h_pres_k x hmod hdef hsome_mid
                have hx_not_touched : x ∉ Config.touchedVarsSet (Config.stmts body ρ₀) := by
                  simp only [Config.touchedVarsSet, List.mem_append]
                  exact fun h => h.elim hmod hdef
                have h_inner_eq : ρ_inner_first.store x = ρ₀.store x := by
                  have := star_preserves_store_outside_touchedVars_isSome
                    (π := π) (φ := φ) (σ₀ := ρ₀.store)
                    h_body_first x hsome hx_not_touched (fun _ h => h)
                  simpa [Config.getEnv] using this
                have h_mid_eq : ρ_mid.store x = ρ₀.store x := by
                  rw [heq_mid]; simp only [projectStore]
                  rw [if_pos hsome]; exact h_inner_eq
                rw [h_k_mid, h_mid_eq]
          · have hnone₀ : ρ₀.store x = none := by
              cases h : ρ₀.store x with
              | none => rfl
              | some _ => simp [h] at hsome
            have hnone_k : ρ_k.store x = none := by
              have := (hsame_k x).mp
              cases h : ρ_k.store x with
              | none => rfl
              | some _ =>
                exfalso; have hsome_k := this (by simp [h])
                rw [hnone₀] at hsome_k; cases hsome_k
            rw [hnone_k, hnone₀]
        have h_havoc_to_k : CoreStar π φ
            (.stmt (.block havoc_label havoc_stmts ∅) ρ₀)
            (.terminal { ρ₀ with store := ρ_k.store }) := by
          exact havoc_block_to_target π φ havoc_label havoc_vars md ρ₀ ρ_k hwfvar
            h_havoc_vars_defined₀ h_havoc_vars_defined_k
            (fun x hx => h_k_eq_ρ₀_outside x hx)
        have hk_env_eq : ({ ρ₀ with store := ρ_k.store } : Env Expression) = ρ_k := by
          cases ρ_k with
          | mk sk ek fk =>
            cases ρ₀ with
            | mk s₀ e₀ f₀ =>
              simp at heval_k hnf_k hnf₀
              simp [heval_k, hnf_k, hnf₀]
        rw [hk_env_eq] at h_havoc_to_k
        -- Step 3c: Assumes block at ρ_k (only inv assumes for nondet)
        have hwfb_k : WellFormedSemanticEvalBool ρ_k.eval := by rw [heval_k]; exact hwfb
        have h_assumes_block : CoreStar π φ
            (.stmt (.block arb_assumes_label arb_assumes_body md) ρ_k) (.terminal ρ_k) := by
          have h_assumes_run : CoreStar π φ (.stmts arb_assumes_body ρ_k) (.terminal ρ_k) := by
            simp only [arb_assumes_body, List.nil_append]
            exact stmts_mapIdx_assume_terminal π φ inv ρ_k md mkArbAssumeLabel hwfb_k hall_tt_k
          have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_assumes_label arb_assumes_body md ρ_k ρ_k h_assumes_run
          rw [projectStore_self_env] at h; exact h
        -- Step 3d: body exits from ρ_k → arb_facts_body exits from ρ₀
        have h_body_exit_extended : CoreStar π φ
            (.stmts (body ++ maintain_stmts ++ []) ρ_k) (.exiting lbl ρ_inner_k) := by
          simp only [List.append_nil]
          exact stmts_prefix_exiting_append π φ body maintain_stmts ρ_k ρ_inner_k lbl h_body_k_exit
        have h_arb_body_exit : CoreStar π φ (.stmts arb_facts_body ρ₀) (.exiting lbl ρ_inner_k) := by
          show CoreStar π φ (.stmts
            ([.block havoc_label havoc_stmts ∅,
              .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []) ρ₀)
            (.exiting lbl ρ_inner_k)
          simp only [List.append_nil]
          exact ReflTrans_Transitive _ _ _ _
            (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
              [.block havoc_label havoc_stmts ∅, .block arb_assumes_label arb_assumes_body md]
              (body ++ maintain_stmts) ρ₀ ρ_k
              (ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ ρ₀ ρ_k h_havoc_to_k)
                (ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                    _ _ ρ_k ρ_k h_assumes_block)
                  (.step _ _ _ .step_stmts_nil (.refl _)))))
            (stmts_prefix_exiting_append π φ body maintain_stmts ρ_k ρ_inner_k lbl h_body_k_exit)
        -- Step 3e: arb_facts block exits
        have h_arb_block_exit : CoreStar π φ
            (.stmt (.block arb_facts_label arb_facts_body ∅) ρ₀)
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) :=
          block_wrap_exiting_mismatch (EvalCommand π φ) (EvalPureFunc φ) arb_facts_label arb_facts_body ∅ lbl ρ₀ ρ_inner_k
            hne_arb h_arb_body_exit
        -- Step 3f: ite nondet-true → then-branch block .none exits
        have h_then_stmts_exit : CoreStar π φ
            (.stmts ((.block arb_facts_label arb_facts_body ∅) ::
              ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes)) ρ₀)
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) :=
          stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) _ _ lbl ρ₀ _ h_arb_block_exit
        have hproj_idem : projectStore ρ₀.store (projectStore ρ₀.store ρ_inner_k.store) =
            projectStore ρ₀.store ρ_inner_k.store := by
          funext x; simp [projectStore]; intro h; simp [h] at *
        have h_ite_inner_exit : CoreStar π φ
            (.block .none ρ₀.store ρ₀.eval (.stmts
              ((.block arb_facts_label arb_facts_body ∅) ::
                ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes)) ρ₀))
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) := by
          have h := ReflTrans_Transitive _ _ _ _
            (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
              _ _ .none ρ₀.store ρ₀.eval h_then_stmts_exit)
            (.step _ _ _ (.step_block_exit_mismatch (by simp)) (.refl _))
          simp only [hproj_idem] at h; exact h
        have h_ite_exit : CoreStar π φ
            (.stmt (.ite .nondet
              ((.block arb_facts_label arb_facts_body ∅) ::
                ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes))
              [] ∅) ρ₀)
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) :=
          .step _ _ _ .step_ite_nondet_true h_ite_inner_exit
        -- Step 3g: Chain first_iter_block + ite
        have h_stmts_exit : CoreStar π φ
            (.stmts [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
              ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                (mkAssertLabel i le.1) le.2 md)) ++
               (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                (mkAssumeLabel i le.1) le.2 md))) ∅,
              .ite .nondet
                ((.block arb_facts_label arb_facts_body ∅) ::
                  ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes))
                [] ∅] ρ₀)
            (.exiting lbl { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval }) :=
          ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀ h_fib_block)
            (stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) _ _ lbl ρ₀ _ h_ite_exit)
        -- Step 3h: Wrap in outer block (loop_label)
        have h_outer_exit : CoreStar π φ
            (.stmt (.block s!"{loopElimBlockPrefix}loop_{loop_num}"
              [.block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
                ((inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
                  (mkAssertLabel i le.1) le.2 md)) ++
                 (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                  (mkAssumeLabel i le.1) le.2 md))) ∅,
                .ite .nondet
                  ((.block arb_facts_label arb_facts_body ∅) ::
                    ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes))
                  [] ∅] ∅) ρ₀)
            (.exiting lbl { { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval } with
              store := projectStore ρ₀.store (projectStore ρ₀.store ρ_inner_k.store), eval := ρ₀.eval }) :=
          block_wrap_exiting_mismatch (EvalCommand π φ) (EvalPureFunc φ) s!"{loopElimBlockPrefix}loop_{loop_num}" _ ∅
            lbl ρ₀ _ hne_loop h_stmts_exit
        rw [hproj_idem] at h_outer_exit
        have hproj_eq : projectStore ρ₀.store ρ_inner_k.store = projectStore ρ_k.store ρ_inner_k.store := by
          funext x; simp only [projectStore]
          rcases hh : ρ₀.store x with _ | _
          · have hnone_k : ρ_k.store x = none := by
              cases h : ρ_k.store x with
              | none => rfl
              | some _ =>
                exfalso; have := (hsame_k x).mp (by simp [h])
                rw [hh] at this; cases this
            simp [hh, hnone_k]
          · have hsome_k : (ρ_k.store x).isSome := (hsame_k x).mpr (by simp [hh])
            simp [hh, hsome_k]
        have hρ'_eq : ρ' = { ρ_inner_k with store := projectStore ρ₀.store ρ_inner_k.store, eval := ρ₀.eval } := by
          rw [heq_ρ', heval_k, hproj_eq]
        rw [← hρ'_eq] at h_outer_exit
        exact h_outer_exit

/-- Helper for `simulation`'s loop exit-branch case.  Discharges the
    statement-correctness obligation for `.loop` reaching `.exiting`. -/
private theorem simulation_loop_exit_case
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (ρ₀ : Env Expression)
    (hswf : InitEnvWF reserved (.loop guard measure inv body md) ρ₀)
    (lbl : String) (ρ' : Env Expression)
    (hreach : CoreStar π φ
        (.stmt (.loop guard measure inv body md) ρ₀) (.exiting lbl ρ')) :
    Transform.CanFail (LangCore π φ)
        (stmtResult σ (.loop guard measure inv body md)) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ
        (.stmt (stmtResult σ (.loop guard measure inv body md)) ρ₀)
        (.exiting lbl ρ')) := by
  -- The loop reaches .exiting lbl ρ'.  The zero-iter cases (step_loop_exit,
  -- step_loop_nondet_exit) produce .terminal, so only the enter cases survive.
  -- Handle the vacuous case first: if ρ'.hasFailure = true, Or.inr is trivial.
  by_cases hnf' : ρ'.hasFailure = Bool.true
  · exact .inr (fun hnf => absurd hnf' (by simp [hnf]))
  · have hnf'' : ρ'.hasFailure = Bool.false := by
      cases hh : ρ'.hasFailure <;> simp_all
    have hnf₀ : ρ₀.hasFailure = Bool.false :=
      hasFailure_false_backwards (π := π) (φ := φ) hreach hnf''
    -- Structural decomposition of target
    obtain ⟨loop_label, first_iter_label, first_iter_body, then_branch,
            htgt_eq, hfib_eq⟩ := stmtResult_loop_struct σ guard measure inv body md hok
    -- Extract invariant boolean-valuedness from the first step
    have hinv_bool : ∀ le ∈ inv,
        ρ₀.eval ρ₀.store le.2 = some HasBool.tt ∨
        ρ₀.eval ρ₀.store le.2 = some HasBool.ff := by
      cases hreach with
      | step _ _ _ h1 _ => exact loop_first_step_hinv_bool π φ h1
    rw [htgt_eq]
    by_cases hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt
    · -- All invariants true at entry: must case-split the first step
      cases hreach with
      | step _ _ _ h1 hrest =>
        cases h1 with
        | step_loop_exit hg_ff hib hff_iff hwfb' =>
          -- step_loop_exit produces .terminal, which cannot reach .exiting
          exfalso
          cases hrest with
          | step _ _ _ h _ => exact nomatch h
        | step_loop_nondet_exit hib hff_iff =>
          -- step_loop_nondet_exit produces .terminal
          exfalso
          cases hrest with
          | step _ _ _ h _ => exact nomatch h
        | step_loop_enter hgt hinvb hinviff hwfbe hmease =>
          -- Deterministic enter: seq(block(body), [loop]) reaches .exiting
          have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest hnf''
          have hnif := loop_step_hasInvFailure_false_of_or
            (by simpa [Config.getEnv] using hh)
          rw [← htgt_eq]
          exact simulation_loop_exit_enter_case π φ hwf_ext reserved
            σ (.det _) measure inv body md hok ρ₀ ρ'
            hswf lbl hnf'' hnf₀ hall_tt hnif hrest
            (fun g heq => by cases heq; exact hgt)
            (fun g heq => by cases heq; exact hmease)
        | step_loop_nondet_enter hinvb_ne hinviff_ne =>
          -- Non-deterministic enter: same structure
          have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest hnf''
          have hnif := loop_step_hasInvFailure_false_of_or
            (by simpa [Config.getEnv] using hh)
          rw [← htgt_eq]
          exact simulation_loop_exit_enter_case π φ hwf_ext reserved
            σ .nondet measure inv body md hok ρ₀ ρ'
            hswf lbl hnf'' hnf₀ hall_tt hnif hrest
            (fun _ heq => nomatch heq) (fun _ heq => nomatch heq)
    · -- VC1 failure path: some invariant is ff at ρ₀
      refine .inl ?_
      exact loop_vc1_failure_canFail π φ hswf.wfBool hinv_bool
        (not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt) hfib_eq

/-- **Iteration extraction**: Given a source loop that enters from an all-tt,
    no-failure state and eventually reaches failure, there exists a state `ρ_k`
    (some iteration's pre-body state) satisfying:
    - `ρ_k.eval = ρ₀.eval`
    - `ρ_k.hasFailure = false`
    - all invariants are tt at `ρ_k`
    - body from `ρ_k` either reaches failure OR terminates at `ρ_inner` without
      failure where not all invariants are tt (so some is ff → maintain fires). -/
private theorem loop_cf_iteration_extract
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    {guardE : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ : Env Expression} {cfg : CC}
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (hreach : CoreStar π φ (.stmt (.loop guardE measure inv body md) ρ₀) cfg)
    (hfail : cfg.getEnv.hasFailure = Bool.true)
    (hnf₀ : ρ₀.hasFailure = Bool.false)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) :
    ∃ (ρ_k : Env Expression),
      ρ_k.eval = ρ₀.eval ∧
      ρ_k.hasFailure = Bool.false ∧
      (∀ le ∈ inv, ρ_k.eval ρ_k.store le.2 = some HasBool.tt) ∧
      ((∃ cfg_f : CC, cfg_f.getEnv.hasFailure = Bool.true ∧
          CoreStar π φ (.stmts body ρ_k) cfg_f) ∨
       (∃ ρ_inner : Env Expression,
          CoreStar π φ (.stmts body ρ_k) (.terminal ρ_inner) ∧
          ρ_inner.hasFailure = Bool.false ∧
          (∀ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt ∨
                       ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff) ∧
          ∃ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff)) ∧
      (∀ x, (ρ_k.store x).isSome ↔ (ρ₀.store x).isSome) ∧
      (∀ g, guardE = .det g → ρ_k.eval ρ_k.store g = some HasBool.tt) ∧
      (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body false →
        (ρ₀.store x).isSome → ρ_k.store x = ρ₀.store x) := by
  -- Use length induction on the trace
  have hstarT := reflTrans_to_T hreach
  suffices ∀ (k : Nat) (ρ : Env Expression),
      ρ.eval = ρ₀.eval →
      ρ.hasFailure = Bool.false →
      (∀ le ∈ inv, ρ.eval ρ.store le.2 = some HasBool.tt) →
      (∀ x, (ρ.store x).isSome ↔ (ρ₀.store x).isSome) →
      ∀ (cfg : CC) (hfail : cfg.getEnv.hasFailure = Bool.true)
        (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt (.loop guardE measure inv body md) ρ) cfg),
        h.len ≤ k →
        ∃ (ρ_k : Env Expression),
          ρ_k.eval = ρ₀.eval ∧
          ρ_k.hasFailure = Bool.false ∧
          (∀ le ∈ inv, ρ_k.eval ρ_k.store le.2 = some HasBool.tt) ∧
          ((∃ cfg_f : CC, cfg_f.getEnv.hasFailure = Bool.true ∧
              CoreStar π φ (.stmts body ρ_k) cfg_f) ∨
           (∃ ρ_inner : Env Expression,
              CoreStar π φ (.stmts body ρ_k) (.terminal ρ_inner) ∧
              ρ_inner.hasFailure = Bool.false ∧
              (∀ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt ∨
                           ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff) ∧
              ∃ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff)) ∧
          (∀ x, (ρ_k.store x).isSome ↔ (ρ₀.store x).isSome) ∧
          (∀ g, guardE = .det g → ρ_k.eval ρ_k.store g = some HasBool.tt) ∧
          (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body false →
            (ρ.store x).isSome → ρ_k.store x = ρ.store x) by
    obtain ⟨ρ_k, h1, h2, h3, h4, h5, h6, h7⟩ :=
      this hstarT.len ρ₀ rfl hnf₀ hall_tt (fun _ => Iff.rfl) cfg hfail hstarT (Nat.le_refl _)
    exact ⟨ρ_k, h1, h2, h3, h4, h5, h6, h7⟩
  clear hreach hstarT hnf₀ hall_tt cfg hfail
  intro k
  induction k with
  | zero =>
    intro ρ _ hnf_ρ _ _ cfg hfail hT hlen
    match hT with
    | .refl _ => exact absurd hfail (by simp [Config.getEnv, hnf_ρ])
    | .step _ _ _ _ _ => simp [ReflTransT.len] at hlen
  | succ k' ih =>
    intro ρ heval_ρ hnf_ρ hall_tt_ρ hsame_ρ cfg hfail hT hlen
    have hno_ff : ¬∃ le ∈ inv, ρ.eval ρ.store le.2 = some HasBool.ff := by
      intro ⟨le, hle, hff⟩; have := hall_tt_ρ le hle; rw [this] at hff; cases hff
    match hT with
    | .refl _ => exact absurd hfail (by simp [Config.getEnv, hnf_ρ])
    | .step _ _ _ hstep1 hrest =>
      cases hstep1 with
      | step_loop_exit _ _ hinv_iff _ =>
        -- Exit: terminal env has hasFailure = ρ.hasFailure || hasInvFailure.
        -- Since all-tt, hasInvFailure = false, so hasFailure stays false. Contradicts hfail.
        exfalso
        have hnot_true : ¬(_ = Bool.true) := fun h => hno_ff (hinv_iff.1 h)
        have hif_false := Bool.eq_false_iff.mpr hnot_true
        match hrest with
        | .refl _ => simp [Config.getEnv, hnf_ρ, hif_false] at hfail
        | .step _ _ _ h _ => exact nomatch h
      | step_loop_nondet_exit _ hinv_iff =>
        exfalso
        have hnot_true : ¬(_ = Bool.true) := fun h => hno_ff (hinv_iff.1 h)
        have hif_false := Bool.eq_false_iff.mpr hnot_true
        match hrest with
        | .refl _ => simp [Config.getEnv, hnf_ρ, hif_false] at hfail
        | .step _ _ _ h _ => exact nomatch h
      | step_loop_enter hgt _ hinv_iff _ _ =>
        -- Enter: successor is .seq (.block .none ρ.store (.stmts body ρ_init)) [.loop ...]
        -- where ρ_init = { ρ with hasFailure := ρ.hasFailure || hasInvFailure }.
        -- Since all-tt, hasInvFailure = false, so ρ_init = ρ.
        have hnot_true : ¬(_ = Bool.true) := fun h => hno_ff (hinv_iff.1 h)
        have hif_false := Bool.eq_false_iff.mpr hnot_true
        subst hif_false
        have hrest_len : hrest.len ≤ k' := by
          simp only [ReflTransT.len] at hlen
          omega
        have hρ_eq : ({ ρ with hasFailure := ρ.hasFailure || Bool.false } : Env Expression) = ρ := by
          cases ρ with
          | mk store eval hf => simp at hnf_ρ; subst hnf_ρ; rfl
        match seqT_canfail hrest hfail with
        | .inl ⟨cfg', h_block_fail, hf_block, _⟩ =>
          -- Block (.block .none ρ.store (.stmts body ρ_init)) reaches failure.
          have h_block_fail_ρ : ReflTransT (StepStmt Expression
              (EvalCommand π φ) (EvalPureFunc φ))
              (.block .none ρ.store ρ.eval (.stmts body ρ)) cfg' := hρ_eq ▸ h_block_fail
          have ⟨inner', h_inner, hf_inner, _⟩ := blockT_canfail_to_inner h_block_fail_ρ hf_block
          -- body from ρ reaches failure → ρ is our witness
          refine ⟨ρ, heval_ρ, hnf_ρ, hall_tt_ρ,
            .inl ⟨inner', hf_inner, reflTransT_to_prop h_inner⟩, hsame_ρ, ?_, ?_⟩
          · intro g' heq_g; cases heq_g; exact hgt
          · intro x _ _ _; rfl
        | .inr ⟨ρ_mid, h_block_term, h_tail_fail, hlen_sum⟩ =>
          -- Block terminates at ρ_mid, tail fails.
          have h_block_term_ρ : ReflTransT (StepStmt Expression
              (EvalCommand π φ) (EvalPureFunc φ))
              (.block .none ρ.store ρ.eval (.stmts body ρ)) (.terminal ρ_mid) := hρ_eq ▸ h_block_term
          have ⟨ρ_inner, ⟨h_body_term, hlen_body⟩, heq_mid⟩ :=
            blockT_none_reaches_terminal π φ h_block_term_ρ
          -- Check if body set failure
          by_cases hnf_inner : ρ_inner.hasFailure = Bool.true
          · -- Body terminated with failure → ρ is witness
            refine ⟨ρ, heval_ρ, hnf_ρ, hall_tt_ρ,
              .inl ⟨.terminal ρ_inner, by simp [Config.getEnv]; exact hnf_inner,
                reflTransT_to_prop h_body_term⟩, hsame_ρ, ?_, ?_⟩
            · intro g' heq_g; cases heq_g; exact hgt
            · intro x _ _ _; rfl
          · -- Body terminated without failure at ρ_inner.
            -- Check invariants at ρ_inner
            have hnf_inner' : ρ_inner.hasFailure = Bool.false := by
              cases hh : ρ_inner.hasFailure with
              | false => rfl
              | true => exact absurd hh hnf_inner
            by_cases hall_inner : ∀ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt
            · -- All invariants still tt → recurse on the tail trace
              -- Derive properties of ρ_mid for recursion
              have h_body_term_p : CoreStar π φ (.stmts body ρ) (.terminal ρ_inner) :=
                reflTransT_to_prop h_body_term
              have heq_mid_val := heq_mid
              -- ρ_mid = { ρ_inner with store := projectStore ρ.store ρ_inner.store, eval := ρ.eval }
              have heval_mid : ρ_mid.eval = ρ₀.eval := by
                rw [heq_mid_val, heval_ρ]
              have hnf_mid : ρ_mid.hasFailure = Bool.false := by
                rw [heq_mid_val]; simp; exact hnf_inner'
              have hsame_mid : ∀ x, (ρ_mid.store x).isSome ↔ (ρ₀.store x).isSome := by
                intro x
                rw [heq_mid_val]; simp only [projectStore]
                constructor
                · intro h; split at h
                  · rename_i hsome; exact (hsame_ρ x).mp hsome
                  · simp at h
                · intro h
                  rw [if_pos ((hsame_ρ x).mpr h)]
                  have := star_preserves_outerInv π φ (reflTransT_to_prop h_body_term)
                    (show outerInv ρ.store (.stmts body ρ) from fun n hh => hh)
                  exact this x ((hsame_ρ x).mpr h)
              -- Derive hall_tt_mid: invariants hold at ρ_mid
              have hall_tt_mid : ∀ le ∈ inv, ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt := by
                intro le hle
                rw [heval_mid]
                rw [heq_mid_val]; simp only [Env.store, Env.eval]
                have hcongr := inv_eval_agree_under_projectStore
                  (ρ_inner := ρ_inner) hswf hsame_ρ hle
                rw [hcongr,
                  ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                    h_body_term_p hle ρ_inner.store]
                exact hall_inner le hle
              -- Extract loop trace from h_tail_fail
              have ⟨cfg_loop, h_loop_mid, hfail_loop, hlen_loop⟩ :=
                stmtsT_singleton_canfail h_tail_fail hfail
              have hlen_bound : h_loop_mid.len ≤ k' := by
                have := hrest_len; omega
              obtain ⟨ρ_k, hk1, hk2, hk3, hk4, hk5, hk6, hk_pres_mid⟩ :=
                ih ρ_mid heval_mid hnf_mid hall_tt_mid hsame_mid
                  cfg_loop hfail_loop h_loop_mid hlen_bound
              refine ⟨ρ_k, hk1, hk2, hk3, hk4, hk5, hk6, ?_⟩
              intro x hx_mod hx_def hx_some
              have hx_not_touched : x ∉ Config.touchedVarsSet (Config.stmts body ρ) := by
                simp only [Config.touchedVarsSet, List.mem_append]
                exact fun h => h.elim hx_mod hx_def
              have h_inner_eq : ρ_inner.store x = ρ.store x := by
                have := star_preserves_store_outside_touchedVars_isSome
                  (π := π) (φ := φ) (σ₀ := ρ.store)
                  (reflTransT_to_prop h_body_term) x hx_some hx_not_touched
                  (fun _ h => h)
                simpa [Config.getEnv] using this
              have h_mid_eq : ρ_mid.store x = ρ.store x := by
                rw [heq_mid_val]; simp only [projectStore]
                rw [if_pos hx_some]; exact h_inner_eq
              have h_mid_some : (ρ_mid.store x).isSome := by rw [h_mid_eq]; exact hx_some
              have h_k_mid : ρ_k.store x = ρ_mid.store x :=
                hk_pres_mid x hx_mod hx_def h_mid_some
              rw [h_k_mid, h_mid_eq]
            · -- Some invariant is ff at ρ_inner → ρ is witness
              -- Get bool-valuedness at ρ_inner via the next loop step from ρ_mid.
              have h_body_term_p : CoreStar π φ (.stmts body ρ) (.terminal ρ_inner) :=
                reflTransT_to_prop h_body_term
              have heq_mid_val := heq_mid
              have heval_mid : ρ_mid.eval = ρ₀.eval := by
                rw [heq_mid_val, heval_ρ]
              -- Extract the next loop step's `hinvb` (bool-valuedness at ρ_mid)
              have ⟨cfg_loop, h_loop_mid, hfail_loop, _hlen_loop⟩ :=
                stmtsT_singleton_canfail h_tail_fail hfail
              have hinvb_mid : ∀ le ∈ inv,
                  ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt ∨
                  ρ_mid.eval ρ_mid.store le.2 = some HasBool.ff := by
                cases h_loop_mid with
                | refl =>
                  exfalso
                  simp only [Config.getEnv] at hfail_loop
                  rw [heq_mid_val] at hfail_loop
                  simp at hfail_loop
                  exact hnf_inner hfail_loop
                | step _ _ _ hstep _ =>
                  cases hstep with
                  | step_loop_exit _ hinvb _ _ => exact hinvb
                  | step_loop_enter _ hinvb _ _ _ => exact hinvb
              -- Transfer bool-valuedness from ρ_mid to ρ_inner via exprCongr
              have hinvb_inner : ∀ le ∈ inv,
                  ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt ∨
                  ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff := by
                intro le hle
                have hb_mid := hinvb_mid le hle
                have hcongr := inv_eval_agree_under_projectStore
                  (ρ_inner := ρ_inner) hswf hsame_ρ hle
                rw [heq_mid_val] at hb_mid
                simp only [Env.store, Env.eval] at hb_mid
                rw [heval_ρ] at hb_mid
                rw [hcongr,
                  ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                    h_body_term_p hle ρ_inner.store] at hb_mid
                exact hb_mid
              have hsome_ff : ∃ le ∈ inv,
                  ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff := by
                apply Classical.byContradiction
                intro h_none_ff
                apply hall_inner
                intro le hle
                cases hinvb_inner le hle with
                | inl htt => exact htt
                | inr hff => exact (h_none_ff ⟨le, hle, hff⟩).elim
              refine ⟨ρ, heval_ρ, hnf_ρ, hall_tt_ρ,
                .inr ⟨ρ_inner, reflTransT_to_prop h_body_term, hnf_inner',
                  hinvb_inner, hsome_ff⟩,
                hsame_ρ, ?_, ?_⟩
              · intro g' heq_g; cases heq_g; exact hgt
              · intro x _ _ _; rfl
      | step_loop_nondet_enter _ hinv_iff =>
        -- Same structure as deterministic enter
        have hnot_true : ¬(_ = Bool.true) := fun h => hno_ff (hinv_iff.1 h)
        have hif_false := Bool.eq_false_iff.mpr hnot_true
        subst hif_false
        have hrest_len : hrest.len ≤ k' := by
          simp only [ReflTransT.len] at hlen
          omega
        have hρ_eq : ({ ρ with hasFailure := ρ.hasFailure || Bool.false } : Env Expression) = ρ := by
          cases ρ with
          | mk store eval hf => simp at hnf_ρ; subst hnf_ρ; rfl
        match seqT_canfail hrest hfail with
        | .inl ⟨cfg', h_block_fail, hf_block, _⟩ =>
          have h_block_fail_ρ : ReflTransT (StepStmt Expression
              (EvalCommand π φ) (EvalPureFunc φ))
              (.block .none ρ.store ρ.eval (.stmts body ρ)) cfg' := hρ_eq ▸ h_block_fail
          have ⟨inner', h_inner, hf_inner, _⟩ := blockT_canfail_to_inner h_block_fail_ρ hf_block
          refine ⟨ρ, heval_ρ, hnf_ρ, hall_tt_ρ,
            .inl ⟨inner', hf_inner, reflTransT_to_prop h_inner⟩, hsame_ρ, ?_, ?_⟩
          · intro g' heq_g; cases heq_g
          · intro x _ _ _; rfl
        | .inr ⟨ρ_mid, h_block_term, h_tail_fail, hlen_sum⟩ =>
          have h_block_term_ρ : ReflTransT (StepStmt Expression
              (EvalCommand π φ) (EvalPureFunc φ))
              (.block .none ρ.store ρ.eval (.stmts body ρ)) (.terminal ρ_mid) := hρ_eq ▸ h_block_term
          have ⟨ρ_inner, ⟨h_body_term, hlen_body⟩, heq_mid⟩ :=
            blockT_none_reaches_terminal π φ h_block_term_ρ
          by_cases hnf_inner : ρ_inner.hasFailure = Bool.true
          · refine ⟨ρ, heval_ρ, hnf_ρ, hall_tt_ρ,
              .inl ⟨.terminal ρ_inner, by simp [Config.getEnv]; exact hnf_inner,
                reflTransT_to_prop h_body_term⟩, hsame_ρ, ?_, ?_⟩
            · intro g' heq_g; cases heq_g
            · intro x _ _ _; rfl
          · have hnf_inner' : ρ_inner.hasFailure = Bool.false := by
              cases hh : ρ_inner.hasFailure with
              | false => rfl
              | true => exact absurd hh hnf_inner
            by_cases hall_inner : ∀ le ∈ inv, ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt
            · -- Recurse (same as det case)
              have h_body_term_p : CoreStar π φ (.stmts body ρ) (.terminal ρ_inner) :=
                reflTransT_to_prop h_body_term
              have heq_mid_val := heq_mid
              have heval_mid : ρ_mid.eval = ρ₀.eval := by
                rw [heq_mid_val, heval_ρ]
              have hnf_mid : ρ_mid.hasFailure = Bool.false := by
                rw [heq_mid_val]; simp; exact hnf_inner'
              have hsame_mid : ∀ x, (ρ_mid.store x).isSome ↔ (ρ₀.store x).isSome := by
                intro x
                rw [heq_mid_val]; simp only [projectStore]
                constructor
                · intro h; split at h
                  · rename_i hsome; exact (hsame_ρ x).mp hsome
                  · simp at h
                · intro h
                  rw [if_pos ((hsame_ρ x).mpr h)]
                  have := star_preserves_outerInv π φ (reflTransT_to_prop h_body_term)
                    (show outerInv ρ.store (.stmts body ρ) from fun n hh => hh)
                  exact this x ((hsame_ρ x).mpr h)
              have hall_tt_mid : ∀ le ∈ inv, ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt := by
                intro le hle
                rw [heval_mid]
                rw [heq_mid_val]; simp only [Env.store, Env.eval]
                have hcongr := inv_eval_agree_under_projectStore
                  (ρ_inner := ρ_inner) hswf hsame_ρ hle
                rw [hcongr,
                  ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                    h_body_term_p hle ρ_inner.store]
                exact hall_inner le hle
              have ⟨cfg_loop, h_loop_mid, hfail_loop, hlen_loop⟩ :=
                stmtsT_singleton_canfail h_tail_fail hfail
              have hlen_bound : h_loop_mid.len ≤ k' := by
                have := hrest_len; omega
              obtain ⟨ρ_k, hk1, hk2, hk3, hk4, hk5, hk6, hk_pres_mid⟩ :=
                ih ρ_mid heval_mid hnf_mid hall_tt_mid hsame_mid
                  cfg_loop hfail_loop h_loop_mid hlen_bound
              refine ⟨ρ_k, hk1, hk2, hk3, hk4, hk5, hk6, ?_⟩
              intro x hx_mod hx_def hx_some
              have hx_not_touched : x ∉ Config.touchedVarsSet (Config.stmts body ρ) := by
                simp only [Config.touchedVarsSet, List.mem_append]
                exact fun h => h.elim hx_mod hx_def
              have h_inner_eq : ρ_inner.store x = ρ.store x := by
                have := star_preserves_store_outside_touchedVars_isSome
                  (π := π) (φ := φ) (σ₀ := ρ.store)
                  (reflTransT_to_prop h_body_term) x hx_some hx_not_touched
                  (fun _ h => h)
                simpa [Config.getEnv] using this
              have h_mid_eq : ρ_mid.store x = ρ.store x := by
                rw [heq_mid_val]; simp only [projectStore]
                rw [if_pos hx_some]; exact h_inner_eq
              have h_mid_some : (ρ_mid.store x).isSome := by rw [h_mid_eq]; exact hx_some
              have h_k_mid : ρ_k.store x = ρ_mid.store x :=
                hk_pres_mid x hx_mod hx_def h_mid_some
              rw [h_k_mid, h_mid_eq]
            · -- Some invariant is ff at ρ_inner → ρ is witness (nondet branch)
              have h_body_term_p : CoreStar π φ (.stmts body ρ) (.terminal ρ_inner) :=
                reflTransT_to_prop h_body_term
              have heq_mid_val := heq_mid
              have heval_mid : ρ_mid.eval = ρ₀.eval := by
                rw [heq_mid_val, heval_ρ]
              have ⟨cfg_loop, h_loop_mid, hfail_loop, _hlen_loop⟩ :=
                stmtsT_singleton_canfail h_tail_fail hfail
              have hinvb_mid : ∀ le ∈ inv,
                  ρ_mid.eval ρ_mid.store le.2 = some HasBool.tt ∨
                  ρ_mid.eval ρ_mid.store le.2 = some HasBool.ff := by
                cases h_loop_mid with
                | refl =>
                  exfalso
                  simp only [Config.getEnv] at hfail_loop
                  rw [heq_mid_val] at hfail_loop
                  simp at hfail_loop
                  exact hnf_inner hfail_loop
                | step _ _ _ hstep _ =>
                  cases hstep with
                  | step_loop_nondet_exit hinvb _ => exact hinvb
                  | step_loop_nondet_enter hinvb _ => exact hinvb
              have hinvb_inner : ∀ le ∈ inv,
                  ρ_inner.eval ρ_inner.store le.2 = some HasBool.tt ∨
                  ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff := by
                intro le hle
                have hb_mid := hinvb_mid le hle
                have hcongr := inv_eval_agree_under_projectStore
                  (ρ_inner := ρ_inner) hswf hsame_ρ hle
                rw [heq_mid_val] at hb_mid
                simp only [Env.store, Env.eval] at hb_mid
                rw [heval_ρ] at hb_mid
                rw [hcongr,
                  ← body_eval_inv_preserved_init π φ hwf_ext hswf hsame_ρ heval_ρ
                    h_body_term_p hle ρ_inner.store] at hb_mid
                exact hb_mid
              have hsome_ff : ∃ le ∈ inv,
                  ρ_inner.eval ρ_inner.store le.2 = some HasBool.ff := by
                apply Classical.byContradiction
                intro h_none_ff
                apply hall_inner
                intro le hle
                cases hinvb_inner le hle with
                | inl htt => exact htt
                | inr hff => exact (h_none_ff ⟨le, hle, hff⟩).elim
              refine ⟨ρ, heval_ρ, hnf_ρ, hall_tt_ρ,
                .inr ⟨ρ_inner, reflTransT_to_prop h_body_term, hnf_inner',
                  hinvb_inner, hsome_ff⟩,
                hsame_ρ, ?_, ?_⟩
              · intro g' heq_g; cases heq_g
              · intro x _ _ _; rfl

/-- Sub-helper for the det+no-measure CanFail case.  Builds the target trace
    from a known failing source iteration. -/
private theorem simulation_loop_cf_all_tt_det_nomeasure
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (σ : LoopElimState)
    (g : Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ : Env Expression)
    (hswf : InitEnvWF reserved (.loop (.det g) none inv body md) ρ₀)
    (cfg : CC) (hfail : cfg.getEnv.hasFailure = Bool.true)
    (hnf₀' : ρ₀.hasFailure = Bool.false)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    (hreach : CoreStar π φ
      (.stmt (.loop (.det g) none inv body md) ρ₀) cfg) :
    let loop_num := (StringGenState.gen "loop" σ.gen).fst
    let havoc_vars := (Block.modifiedVars body).filter fun v =>
      decide (¬ v ∈ Block.definedVars body Bool.false)
    let havoc_stmts : Statements := havoc_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)
    let havoc_label := s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
    let arb_assumes_label := s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
    let invSuffix : Nat → String → String := fun i lbl =>
      if lbl.isEmpty then toString i else s!"{i}_{lbl}"
    let mkArbAssumeLabel : Nat → String → String := fun i lbl =>
      s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lbl}"
    let arb_assumes_body : Statements :=
      ([Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_guard" g md)] ++
        ([] : List Statement)) ++
      inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        (mkArbAssumeLabel i le.1) le.2 md)
    let mkMaintainLabel : Nat → String → String := fun i lbl =>
      s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lbl}"
    let maintain_stmts : Statements :=
      inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkMaintainLabel i le.1) le.2 md)
    let arb_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
    let arb_facts_body : Statements :=
      [.block havoc_label havoc_stmts ∅,
       .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []
    let mkExitAssumeLabel : Nat → String → String := fun i lbl =>
      s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lbl}"
    let exit_inv_assumes : Statements :=
      inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        (mkExitAssumeLabel i le.1) le.2 md)
    CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) ((.block arb_facts_label arb_facts_body ∅) ::
      ([.block havoc_label havoc_stmts ∅] ++
        [Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)] ++
        exit_inv_assumes)) ρ₀ := by
  intro loop_num havoc_vars havoc_stmts havoc_label arb_assumes_label invSuffix
    mkArbAssumeLabel arb_assumes_body mkMaintainLabel maintain_stmts arb_facts_label
    arb_facts_body mkExitAssumeLabel exit_inv_assumes
  -- Extract the bad iteration
  obtain ⟨ρ_k, heval_k, hnf_k, hall_tt_k, hbad_k, hsame_k, hguard_k, hpres_k⟩ :=
    loop_cf_iteration_extract π φ hwf_ext reserved hswf hreach hfail hnf₀' hall_tt
  have hguard_k_tt : ρ_k.eval ρ_k.store g = some HasBool.tt := hguard_k g rfl
  have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
  have hwfb_k : WellFormedSemanticEvalBool ρ_k.eval := by rw [heval_k]; exact hwfb
  have hwfvar : WellFormedSemanticEvalVar ρ₀.eval := hswf.wfVar
  -- Havoc-vars in scope at ρ₀ and ρ_k
  have h_havoc_vars_defined₀ : ∀ x ∈ havoc_vars, (ρ₀.store x).isSome :=
    havoc_vars_defined_of_init hswf havoc_vars rfl
  have h_havoc_vars_defined_k : ∀ x ∈ havoc_vars, (ρ_k.store x).isSome := fun x hx =>
    (hsame_k x).mpr (h_havoc_vars_defined₀ x hx)
  -- Agreement outside havoc_vars: ρ_k.store x = ρ₀.store x
  have h_k_eq_ρ₀_outside : ∀ x, x ∉ havoc_vars → ρ_k.store x = ρ₀.store x := by
    intro x hx_not_havoc
    by_cases hsome : (ρ₀.store x).isSome
    · by_cases hmod : x ∈ Block.modifiedVars body
      · have hdef : x ∈ Block.definedVars body false :=
          Classical.byContradiction (fun hndef =>
            hx_not_havoc (List.mem_filter.mpr ⟨hmod, by simp [hndef]⟩))
        have hisNone : ρ₀.store x = none := by
          have h := hswf.defsUndefined x (by simp [Stmt.definedVars]; exact hdef)
          exact Option.isNone_iff_eq_none.mp h
        exfalso; rw [hisNone] at hsome; exact absurd hsome (by simp)
      · by_cases hdef : x ∈ Block.definedVars body false
        · have hisNone : ρ₀.store x = none := by
            have h := hswf.defsUndefined x (by simp [Stmt.definedVars]; exact hdef)
            exact Option.isNone_iff_eq_none.mp h
          exfalso; rw [hisNone] at hsome; exact absurd hsome (by simp)
        · -- x outside body's vars
          exact hpres_k x hmod hdef hsome
    · have hnone₀ : ρ₀.store x = none := by
        cases h : ρ₀.store x with
        | none => rfl
        | some _ => simp [h] at hsome
      have hnone_k : ρ_k.store x = none := by
        cases h : ρ_k.store x with
        | none => rfl
        | some _ =>
          exfalso; have := (hsame_k x).mp (by simp [h])
          rw [hnone₀] at this; cases this
      rw [hnone_k, hnone₀]
  -- havoc_block from ρ₀ to ρ_k
  have h_havoc_to_k : CoreStar π φ
      (.stmt (.block havoc_label havoc_stmts ∅) ρ₀)
      (.terminal { ρ₀ with store := ρ_k.store }) :=
    havoc_block_to_target π φ havoc_label havoc_vars md ρ₀ ρ_k hwfvar
      h_havoc_vars_defined₀ h_havoc_vars_defined_k
      (fun x hx => h_k_eq_ρ₀_outside x hx)
  have hk_env_eq : ({ ρ₀ with store := ρ_k.store } : Env Expression) = ρ_k := by
    cases ρ_k with
    | mk sk ek fk =>
      cases ρ₀ with
      | mk s₀ e₀ f₀ =>
        simp at heval_k hnf_k hnf₀'
        simp [heval_k, hnf_k, hnf₀']
  rw [hk_env_eq] at h_havoc_to_k
  -- assumes_block from ρ_k to ρ_k (guard tt + invariants tt)
  have h_assumes_block : CoreStar π φ
      (.stmt (.block arb_assumes_label arb_assumes_body md) ρ_k) (.terminal ρ_k) := by
    have h_assumes_run : CoreStar π φ (.stmts arb_assumes_body ρ_k) (.terminal ρ_k) := by
      simp only [arb_assumes_body, List.append_nil, List.cons_append, List.nil_append]
      have h_guard_assume : CoreStar π φ
          (.stmt (.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loop_num}_guard" g md)) ρ_k)
          (.terminal ρ_k) :=
        assume_pass_step π φ _ g md ρ_k hguard_k_tt hwfb_k
      exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ_k ρ_k h_guard_assume)
        (stmts_mapIdx_assume_terminal π φ inv ρ_k md mkArbAssumeLabel hwfb_k hall_tt_k)
    have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_assumes_label arb_assumes_body md ρ_k ρ_k h_assumes_run
    rw [projectStore_self_env] at h; exact h
  -- Body fails or maintains fires: build CanFailBlock for body ++ maintain_stmts
  have h_body_maintain_cf : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (body ++ maintain_stmts) ρ_k := by
    cases hbad_k with
    | inl hbody_fail =>
      -- Body fails directly from ρ_k
      obtain ⟨cfg_f, hf_f, hr_f⟩ := hbody_fail
      exact Transform.canFailBlock_append_left (EvalCommand π φ) (EvalPureFunc φ) body maintain_stmts ρ_k ⟨cfg_f, hf_f, hr_f⟩
    | inr hbody_term =>
      -- Body terminates at ρ_inner with some inv ff → maintain fires
      obtain ⟨ρ_inner, h_body_term, _hnf_inner, hinv_bool_inner, hsome_ff⟩ := hbody_term
      have hwfb_inner : WellFormedSemanticEvalBool ρ_inner.eval := by
        have h := star_preserves_wfBool_block Expression (EvalCommand π φ) (EvalPureFunc φ)
          hwf_ext.toWFEvalExtension (ss := body) (ρ := ρ_k) h_body_term
          (show WellFormedSemanticEvalBool _ from hwfb_k)
        simpa [Config.getEnv] using h
      have h_maintain_cf : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) maintain_stmts ρ_inner :=
        stmts_mapIdx_assert_canFail π φ inv ρ_inner md mkMaintainLabel
          hwfb_inner hinv_bool_inner hsome_ff
      exact Transform.canFailBlock_append_right (EvalCommand π φ) (EvalPureFunc φ) body maintain_stmts ρ_k ρ_inner h_body_term
        h_maintain_cf
  -- Now: arb_facts_body = [havoc_block, assumes_block] ++ [] ++ body ++ maintain ++ []
  -- = havoc :: assumes :: (body ++ maintain)
  -- Build CanFailBlock for arb_facts_body via: havoc → assumes_block → (body++maintain) cf
  have h_arb_body_cf : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) arb_facts_body ρ₀ := by
    show CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) ([.block havoc_label havoc_stmts ∅,
      .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []) ρ₀
    simp only [List.append_nil, List.nil_append, List.append_assoc]
    -- = [havoc, assumes] ++ (body ++ maintain)
    apply Transform.canFailBlock_append_right (EvalCommand π φ) (EvalPureFunc φ)
      [.block havoc_label havoc_stmts ∅, .block arb_assumes_label arb_assumes_body md]
      (body ++ maintain_stmts) ρ₀ ρ_k
    · -- [havoc, assumes] terminates from ρ₀ to ρ_k
      exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
          _ _ ρ₀ ρ_k h_havoc_to_k)
        (ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
            _ _ ρ_k ρ_k h_assumes_block)
          (.step _ _ _ .step_stmts_nil (.refl _)))
    · -- (body ++ maintain) CanFails from ρ_k
      exact h_body_maintain_cf
  -- Wrap arb_facts_body in arb_facts_block
  have h_arb_block_cf : Transform.CanFail (LangCore π φ)
      (.block arb_facts_label arb_facts_body ∅) ρ₀ :=
    Transform.canFailBlock_to_canFail_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert arb_facts_label arb_facts_body ∅ ρ₀ h_arb_body_cf
  -- Then prepend it to the full then-branch list
  exact Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert (.block arb_facts_label arb_facts_body ∅) _ ρ₀ h_arb_block_cf

/-- Sub-helper for the nondet CanFail case.  Builds the target trace
    from a known failing source iteration. -/
private theorem simulation_loop_cf_all_tt_nondet
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (σ : LoopElimState)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ : Env Expression)
    (hswf : InitEnvWF reserved (.loop .nondet measure inv body md) ρ₀)
    (cfg : CC) (hfail : cfg.getEnv.hasFailure = Bool.true)
    (hnf₀' : ρ₀.hasFailure = Bool.false)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    (hreach : CoreStar π φ
      (.stmt (.loop .nondet measure inv body md) ρ₀) cfg) :
    let loop_num := (StringGenState.gen "loop" σ.gen).fst
    let havoc_vars := (Block.modifiedVars body).filter fun v =>
      decide (¬ v ∈ Block.definedVars body Bool.false)
    let havoc_stmts : Statements := havoc_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)
    let havoc_label := s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
    let arb_assumes_label := s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
    let invSuffix : Nat → String → String := fun i lbl =>
      if lbl.isEmpty then toString i else s!"{i}_{lbl}"
    let mkArbAssumeLabel : Nat → String → String := fun i lbl =>
      s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lbl}"
    let arb_assumes_body : Statements :=
      [] ++ inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        (mkArbAssumeLabel i le.1) le.2 md)
    let mkMaintainLabel : Nat → String → String := fun i lbl =>
      s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lbl}"
    let maintain_stmts : Statements :=
      inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkMaintainLabel i le.1) le.2 md)
    let arb_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
    let arb_facts_body : Statements :=
      [.block havoc_label havoc_stmts ∅,
       .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []
    let mkExitAssumeLabel : Nat → String → String := fun i lbl =>
      s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lbl}"
    let exit_inv_assumes : Statements :=
      inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        (mkExitAssumeLabel i le.1) le.2 md)
    CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) ((.block arb_facts_label arb_facts_body ∅) ::
      ([.block havoc_label havoc_stmts ∅] ++ [] ++ exit_inv_assumes)) ρ₀ := by
  intro loop_num havoc_vars havoc_stmts havoc_label arb_assumes_label invSuffix
    mkArbAssumeLabel arb_assumes_body mkMaintainLabel maintain_stmts arb_facts_label
    arb_facts_body mkExitAssumeLabel exit_inv_assumes
  -- Extract the bad iteration
  obtain ⟨ρ_k, heval_k, hnf_k, hall_tt_k, hbad_k, hsame_k, _hguard_k, hpres_k⟩ :=
    loop_cf_iteration_extract π φ hwf_ext reserved hswf hreach hfail hnf₀' hall_tt
  have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
  have hwfb_k : WellFormedSemanticEvalBool ρ_k.eval := by rw [heval_k]; exact hwfb
  have hwfvar : WellFormedSemanticEvalVar ρ₀.eval := hswf.wfVar
  have h_havoc_vars_defined₀ : ∀ x ∈ havoc_vars, (ρ₀.store x).isSome :=
    havoc_vars_defined_of_init hswf havoc_vars rfl
  have h_havoc_vars_defined_k : ∀ x ∈ havoc_vars, (ρ_k.store x).isSome := fun x hx =>
    (hsame_k x).mpr (h_havoc_vars_defined₀ x hx)
  have h_k_eq_ρ₀_outside : ∀ x, x ∉ havoc_vars → ρ_k.store x = ρ₀.store x := by
    intro x hx_not_havoc
    by_cases hsome : (ρ₀.store x).isSome
    · by_cases hmod : x ∈ Block.modifiedVars body
      · have hdef : x ∈ Block.definedVars body false :=
          Classical.byContradiction (fun hndef =>
            hx_not_havoc (List.mem_filter.mpr ⟨hmod, by simp [hndef]⟩))
        have hisNone : ρ₀.store x = none := by
          have h := hswf.defsUndefined x (by simp [Stmt.definedVars]; exact hdef)
          exact Option.isNone_iff_eq_none.mp h
        exfalso; rw [hisNone] at hsome; exact absurd hsome (by simp)
      · by_cases hdef : x ∈ Block.definedVars body false
        · have hisNone : ρ₀.store x = none := by
            have h := hswf.defsUndefined x (by simp [Stmt.definedVars]; exact hdef)
            exact Option.isNone_iff_eq_none.mp h
          exfalso; rw [hisNone] at hsome; exact absurd hsome (by simp)
        · exact hpres_k x hmod hdef hsome
    · have hnone₀ : ρ₀.store x = none := by
        cases h : ρ₀.store x with
        | none => rfl
        | some _ => simp [h] at hsome
      have hnone_k : ρ_k.store x = none := by
        cases h : ρ_k.store x with
        | none => rfl
        | some _ =>
          exfalso; have := (hsame_k x).mp (by simp [h])
          rw [hnone₀] at this; cases this
      rw [hnone_k, hnone₀]
  have h_havoc_to_k : CoreStar π φ
      (.stmt (.block havoc_label havoc_stmts ∅) ρ₀)
      (.terminal { ρ₀ with store := ρ_k.store }) :=
    havoc_block_to_target π φ havoc_label havoc_vars md ρ₀ ρ_k hwfvar
      h_havoc_vars_defined₀ h_havoc_vars_defined_k
      (fun x hx => h_k_eq_ρ₀_outside x hx)
  have hk_env_eq : ({ ρ₀ with store := ρ_k.store } : Env Expression) = ρ_k := by
    cases ρ_k with
    | mk sk ek fk =>
      cases ρ₀ with
      | mk s₀ e₀ f₀ =>
        simp at heval_k hnf_k hnf₀'
        simp [heval_k, hnf_k, hnf₀']
  rw [hk_env_eq] at h_havoc_to_k
  have h_assumes_block : CoreStar π φ
      (.stmt (.block arb_assumes_label arb_assumes_body md) ρ_k) (.terminal ρ_k) := by
    have h_assumes_run : CoreStar π φ (.stmts arb_assumes_body ρ_k) (.terminal ρ_k) := by
      simp only [arb_assumes_body, List.nil_append]
      exact stmts_mapIdx_assume_terminal π φ inv ρ_k md mkArbAssumeLabel hwfb_k hall_tt_k
    have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) arb_assumes_label arb_assumes_body md ρ_k ρ_k h_assumes_run
    rw [projectStore_self_env] at h; exact h
  have h_body_maintain_cf : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (body ++ maintain_stmts) ρ_k := by
    cases hbad_k with
    | inl hbody_fail =>
      obtain ⟨cfg_f, hf_f, hr_f⟩ := hbody_fail
      exact Transform.canFailBlock_append_left (EvalCommand π φ) (EvalPureFunc φ) body maintain_stmts ρ_k ⟨cfg_f, hf_f, hr_f⟩
    | inr hbody_term =>
      obtain ⟨ρ_inner, h_body_term, _hnf_inner, hinv_bool_inner, hsome_ff⟩ := hbody_term
      have hwfb_inner : WellFormedSemanticEvalBool ρ_inner.eval := by
        have h := star_preserves_wfBool_block Expression (EvalCommand π φ) (EvalPureFunc φ)
          hwf_ext.toWFEvalExtension (ss := body) (ρ := ρ_k) h_body_term
          (show WellFormedSemanticEvalBool _ from hwfb_k)
        simpa [Config.getEnv] using h
      have h_maintain_cf : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) maintain_stmts ρ_inner :=
        stmts_mapIdx_assert_canFail π φ inv ρ_inner md mkMaintainLabel
          hwfb_inner hinv_bool_inner hsome_ff
      exact Transform.canFailBlock_append_right (EvalCommand π φ) (EvalPureFunc φ) body maintain_stmts ρ_k ρ_inner h_body_term
        h_maintain_cf
  have h_arb_body_cf : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) arb_facts_body ρ₀ := by
    show CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) ([.block havoc_label havoc_stmts ∅,
      .block arb_assumes_label arb_assumes_body md] ++ [] ++ body ++ maintain_stmts ++ []) ρ₀
    simp only [List.append_nil, List.nil_append, List.append_assoc]
    apply Transform.canFailBlock_append_right (EvalCommand π φ) (EvalPureFunc φ)
      [.block havoc_label havoc_stmts ∅, .block arb_assumes_label arb_assumes_body md]
      (body ++ maintain_stmts) ρ₀ ρ_k
    · exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
          _ _ ρ₀ ρ_k h_havoc_to_k)
        (ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
            _ _ ρ_k ρ_k h_assumes_block)
          (.step _ _ _ .step_stmts_nil (.refl _)))
    · exact h_body_maintain_cf
  have h_arb_block_cf : Transform.CanFail (LangCore π φ)
      (.block arb_facts_label arb_facts_body ∅) ρ₀ :=
    Transform.canFailBlock_to_canFail_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert arb_facts_label arb_facts_body ∅ ρ₀ h_arb_body_cf
  exact Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert (.block arb_facts_label arb_facts_body ∅) _ ρ₀ h_arb_block_cf

/-- Helper for `simulation`'s loop CanFail-preservation case (all-tt
    invariants branch).  In this branch, source failure must come from the
    body's iteration, since the loop-exit step does not produce failure
    when all invariants evaluate to `tt`. -/
private theorem simulation_loop_cf_all_tt
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (σ : LoopElimState)
    (guardE : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guardE measure inv body md))
    (ρ₀ : Env Expression)
    (hswf : InitEnvWF reserved (.loop guardE measure inv body md) ρ₀)
    (cfg : CC) (hfail : cfg.getEnv.hasFailure = Bool.true)
    (hreach : CoreStar π φ (.stmt (.loop guardE measure inv body md) ρ₀) cfg)
    (hnf₀' : ρ₀.hasFailure = Bool.false)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) :
    Transform.CanFail (LangCore π φ)
      (stmtResult σ (.loop guardE measure inv body md)) ρ₀ := by
  -- Obtain the target's structural decomposition.
  obtain ⟨loop_label, first_iter_label, first_iter_body, then_branch,
          htgt_eq, hfib_eq⟩ := stmtResult_loop_struct σ guardE measure inv body md hok
  rw [htgt_eq]
  -- The target is: .block loop_label [.block fib_label fib {}, .ite guardE then_branch [] {}] {}
  -- Strategy: first_iter_block terminates at ρ₀ (asserts+assumes pass since all-tt),
  -- then ITE canfails (routing through then_branch's arb_facts).
  have hwfb : WellFormedSemanticEvalBool ρ₀.eval := hswf.wfBool
  let loop_num := (StringGenState.gen "loop" σ.gen).fst
  let invSuffix : Nat → String → String := fun i lbl =>
    if lbl.isEmpty then toString i else s!"{i}_{lbl}"
  let mkAssertLabel : Nat → String → String := fun i lbl =>
    s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
  let mkAssumeLabel : Nat → String → String := fun i lbl =>
    s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
  have h_fib_run : CoreStar π φ (.stmts first_iter_body ρ₀) (.terminal ρ₀) := by
    rw [hfib_eq]
    exact stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀
      (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt)
      (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt)
  have h_fib_block : CoreStar π φ
      (.stmt (.block first_iter_label first_iter_body {}) ρ₀) (.terminal ρ₀) := by
    have h := block_wrap_terminal (EvalCommand π φ) (EvalPureFunc φ) first_iter_label first_iter_body {} ρ₀ ρ₀ h_fib_run
    rw [projectStore_self_env] at h; exact h
  -- Reduce to: CanFailBlock for the ite singleton list at ρ₀
  suffices hite_cf : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) [.ite guardE then_branch [] {}] ρ₀ from
    Transform.canFailBlock_to_canFail_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert loop_label _ {} ρ₀
      (Transform.canFail_tail_to_block (EvalCommand π φ) (EvalPureFunc φ) (.block first_iter_label first_iter_body {}) _ ρ₀ ρ₀
        h_fib_block hite_cf)
  -- CanFailBlock [.ite guardE then_branch [] {}] ρ₀ reduces to CanFail of the ite
  suffices hite : Transform.CanFail (LangCore π φ) (.ite guardE then_branch [] {}) ρ₀ from
    Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert (.ite guardE then_branch [] {}) [] ρ₀ hite
  -- CanFail of ITE: enter then_branch (via nondet_true or det_true),
  -- then then_branch reaches failure.
  suffices hthen_cf : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) then_branch ρ₀ by
    obtain ⟨cfg_f, hf_f, hreach_f⟩ := hthen_cf
    refine ⟨.block .none ρ₀.store ρ₀.eval cfg_f, hf_f, ?_⟩
    cases guardE with
    | det g =>
      -- Source loop entered, so guard was tt (exit would give no failure since all-tt).
      have hguard_tt : ρ₀.eval ρ₀.store g = some HasBool.tt := by
        cases hreach with
        | refl =>
          -- cfg = .stmt (.loop ..) ρ₀, getEnv = ρ₀, ρ₀.hasFailure = false. Contradicts hfail.
          exact absurd hfail (by simp [Config.getEnv, hnf₀'])
        | step _ _ _ h1 _ =>
          cases h1 with
          | step_loop_enter hgt _ _ _ _ => exact hgt
          | step_loop_exit _ _ _ _ =>
            -- Exit produces .terminal with hasFailure = ρ₀.hasFailure || hasInvFailure.
            -- Since all-tt, hasInvFailure = false, so hasFailure stays false.
            exfalso
            rename_i hasInvF _ _ _ hinviff hrest
            have hno_ff : ¬∃ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.ff := by
              intro ⟨le, hle, hff⟩
              have := hall_tt le hle; rw [this] at hff; cases hff
            have hif_false : hasInvF = Bool.false := by
              cases hh : hasInvF
              · rfl
              · exact absurd (hinviff.1 hh) hno_ff
            cases hrest with
            | refl =>
              simp [Config.getEnv, hnf₀', hif_false] at hfail
            | step _ _ _ h _ => exact nomatch h
      exact .step _ _ _ (.step_ite_true hguard_tt hwfb)
        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
          _ _ .none ρ₀.store ρ₀.eval hreach_f)
    | nondet =>
      exact .step _ _ _ .step_ite_nondet_true
        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
          _ _ .none ρ₀.store ρ₀.eval hreach_f)
  -- Remaining goal: CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) then_branch ρ₀
  -- Strategy: unfold stmtResult in htgt_eq to derive the concrete then_branch,
  -- then show CanFailBlock via arb_facts (havoc-identity + assumes-pass + body).
  simp only [stmtResult] at htgt_eq
  have hok₂ := hok; unfold stmtOk at hok₂
  generalize hsr : (stmtRun σ (Stmt.loop guardE measure inv body md)).fst = sr at htgt_eq hok₂
  cases sr with
  | error e => simp [Except.isOk, Except.toBool] at hok₂
  | ok p =>
    obtain ⟨b, s'⟩ := p
    simp only at htgt_eq
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase,
      buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes,
      buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants,
      buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants,
      buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome,
      hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at hsr
    repeat (first | contradiction | (split at hsr; skip))
    all_goals (first | contradiction | (
      dsimp only [StateT.pure, StateT.bind, StateT.map, ExceptT.bindCont,
        ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
        Functor.map, MonadStateOf.modifyGet, StateT.modifyGet, bumpStat,
        modify, genLoopNum] at hsr
      first
        | obtain ⟨rfl, rfl⟩ := hsr
        | (repeat (first | (split at hsr; skip) | contradiction)
           all_goals (first | contradiction | obtain ⟨rfl, rfl⟩ := hsr))))
    -- After case-split, s' is concrete and htgt_eq gives then_branch's concrete value.
    -- In each case then_branch = arb_facts_block :: exit_state_stmts where arb_facts
    -- contains [havoc_block, assumes_block] ++ preTermination ++ body ++ maintain_inv ++ postTermination.
    -- Use loop_cf_iteration_extract to find the bad iteration, then build target trace.
    -- The det+measure case is vacuously impossible: step_loop_enter's hmeas_enter
    -- premise (∀ v, ρ.eval ρ.store me = some v) is contradictory.
    case h_2.isFalse.isTrue =>
      -- Det guard, measure = some m: derive contradiction via step_loop_enter's hmeas_enter.
      exfalso
      rename_i g _ m _ _
      cases hreach with
      | refl =>
        simp [Config.getEnv, hnf₀'] at hfail
      | step _ _ _ h1 hrest =>
        cases h1
        case step_loop_exit hasInvF hwfb' hg_ff hib hff_iff =>
          have hno_ff : ¬∃ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.ff := by
            intro ⟨le, hle, hff⟩; have := hall_tt le hle; rw [this] at hff; cases hff
          have hif_false : hasInvF = Bool.false := by
            cases hh : hasInvF with
            | false => rfl
            | true => exact absurd (hff_iff.1 hh) hno_ff
          subst hif_false
          have hρ_eq : ({ ρ₀ with hasFailure := ρ₀.hasFailure || Bool.false } : Env Expression) = ρ₀ := by
            cases ρ₀; simp_all
          rw [hρ_eq] at hrest
          cases hrest with
          | refl => simp [Config.getEnv, hnf₀'] at hfail
          | step _ _ _ h _ => exact nomatch h
        case step_loop_enter =>
          rename_i _ _ hmeas_enter _ _
          have hmeas_m := fun v => hmeas_enter _ v rfl
          exact absurd (Option.some.inj
            ((hmeas_m HasBool.tt).1.symm.trans (hmeas_m HasBool.ff).1))
            HasBool.tt_is_not_ff
    case h_1.isFalse =>
      -- Det guard, no measure: real case.
      rename_i _ _ g _ _
      -- The then_branch concretely has guard + havoc_block + arb_assumes (with guard)
      -- + body + maintain + then exit_havoc + not_guard_assume + exit_inv_assumes.
      have htb := htgt_eq
      simp only [Stmt.block.injEq, Stmt.ite.injEq, List.cons.injEq, and_true, true_and] at htb
      obtain ⟨_, _, htb_eq⟩ := htb
      subst htb_eq
      exact simulation_loop_cf_all_tt_det_nomeasure π φ hwf_ext reserved σ g inv body md
        ρ₀ hswf cfg hfail hnf₀' hall_tt hreach
    case h_2 =>
      -- Nondet guard: real case.
      have htb := htgt_eq
      simp only [Stmt.block.injEq, Stmt.ite.injEq, List.cons.injEq, and_true, true_and] at htb
      obtain ⟨_, _, htb_eq⟩ := htb
      subst htb_eq
      exact simulation_loop_cf_all_tt_nondet π φ hwf_ext reserved σ measure inv body md
        ρ₀ hswf cfg hfail hnf₀' hall_tt hreach

/-! ### Per-conjunct step lemmas

The four conjuncts of `simulation`'s inductive step (`stmt_corr`,
`block_corr`, `stmt_cf`, `block_cf`) each take the bundled IH `ih`
(at size `n`) plus the per-input binders, and produce the same conjunct
at size `n + 1`.  Extracting them keeps `simulation` itself short and
allows agents to edit each conjunct independently. -/

private theorem stmt_corr_step
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (h_loop_reserved : loopElimReservedPrefix ∈ reserved)
    (n : Nat) (ih : SimAllProp π φ reserved n) :
    SimStmtCorrProp π φ reserved (n + 1) := by
  intro σ st hsz hok ρ₀ hswf
  refine ⟨?term_branch, ?exit_branch⟩
  case term_branch =>
    intro ρ' hreach
    match st with
    | .cmd c =>
      rw [stmtResult_cmd]; exact .inr (fun _ => hreach)
    | .exit l md =>
      -- .exit cannot reach .terminal: it always reaches .exiting
      exact False.elim (by
        cases hreach with
        | step _ _ _ h1 r1 =>
          cases h1 with
          | step_exit =>
            cases r1 with
            | step _ _ _ h2 _ => cases h2)
    | .funcDecl d md =>
      rw [stmtResult_funcDecl]; exact .inr (fun _ => hreach)
    | .typeDecl tc md =>
      rw [stmtResult_typeDecl]; exact .inr (fun _ => hreach)
    | .block l bss md =>
      rw [stmtResult_block (hok := hok)]
      have hsz_bss : Block.sizeOf bss ≤ n := by
        simp [Stmt.sizeOf] at hsz; omega
      have hsim_bss := ih.2.1 σ bss hsz_bss (stmtOk_block_inner hok) ρ₀
        (InitEnvWF.toBlock_block hswf)
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_block => exact block_term_case π φ r1 hsim_bss
    | .ite c tss ess md =>
      rw [stmtResult_ite (hok := hok)]
      have hsz_tss : Block.sizeOf tss ≤ n := by
        simp [Stmt.sizeOf] at hsz; omega
      have hsz_ess : Block.sizeOf ess ≤ n := by
        simp [Stmt.sizeOf] at hsz; omega
      -- Ite simulation: branches now scoped via .block .none; needs unwrapping.
      have hsim_tss := ih.2.1 σ tss hsz_tss (stmtOk_ite_left hok) ρ₀
        (InitEnvWF.toBlock_ite_left hswf)
      have hsim_ess := ih.2.1 (blockPostState σ tss) ess hsz_ess
        (stmtOk_ite_right hok) ρ₀ (InitEnvWF.toBlock_ite_right hswf)
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_ite_true hcond hwfb' =>
          exact ite_term_branch_lift π φ (.step_ite_true hcond hwfb') r1 hsim_tss.1
        | step_ite_false hcond hwfb' =>
          exact ite_term_branch_lift π φ (.step_ite_false hcond hwfb') r1 hsim_ess.1
        | step_ite_nondet_true =>
          exact ite_term_branch_lift π φ .step_ite_nondet_true r1 hsim_tss.1
        | step_ite_nondet_false =>
          exact ite_term_branch_lift π φ .step_ite_nondet_false r1 hsim_ess.1
    | .loop guardE measure inv body md =>
      -- LOOP TERMINAL case.
      by_cases hnf' : ρ'.hasFailure = Bool.true
      · -- ρ'.hasFailure = true ⇒ Or.inr's premise is false, giving us a
        -- vacuous implication.
        refine .inr (fun hnf => ?_)
        exfalso; rw [hnf'] at hnf; cases hnf
      · -- ρ'.hasFailure = false.
        have hnf'' : ρ'.hasFailure = Bool.false := by
          cases hh : ρ'.hasFailure
          · rfl
          · exact absurd hh hnf'
        -- Derive ρ₀.hasFailure = false (backwards from ρ').
        have hnf₀ : ρ₀.hasFailure = Bool.false :=
          hasFailure_false_backwards (π := π) (φ := φ) hreach hnf''
        -- Obtain the target's structural decomposition.
        obtain ⟨loop_label, first_iter_label, first_iter_body, then_branch,
                htgt_eq, hfib_eq⟩ := stmtResult_loop_struct σ guardE measure inv body md hok
        -- Extract `hinv_bool` (each invariant evaluates to tt or ff at ρ₀)
        -- from any of the 4 first-step cases of `hreach`.  This boolean-
        -- valuedness fact is what enables the VC1-failure dichotomy below.
        have hinv_bool : ∀ le ∈ inv,
            ρ₀.eval ρ₀.store le.2 = some HasBool.tt ∨
            ρ₀.eval ρ₀.store le.2 = some HasBool.ff := by
          cases hreach with
          | step _ _ _ h1 _ => exact loop_first_step_hinv_bool π φ h1
        -- Now we can split on whether all invariants are tt at ρ₀.
        -- The failure path closes via VC1 (assert canFails); the all-tt
        -- path is left as a focused leaf.
        rw [htgt_eq]
        by_cases hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt
        · -- Case-split on hreach to separate zero-iter exits from ≥1-iter enters.
          cases hreach with
          | step _ _ _ h1 hrest =>
            cases h1 with
            | step_loop_exit hg_ff hib hff_iff hwfb' =>
              exact loop_zero_iter_term_branch π φ hswf.wfBool hnf₀ hnf''
                hrest hall_tt hfib_eq
                (ite_det_false_empty_terminal (P := Expression) (CmdT := Command) (EvalCommand π φ) (EvalPureFunc φ)
                  _ then_branch {} ρ₀ hg_ff hwfb')
            | step_loop_enter hgt hinvb hinviff hwfbe hmease =>
              have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest hnf''
              have hnif := loop_step_hasInvFailure_false_of_or
                (by simpa [Config.getEnv] using hh)
              rw [← htgt_eq]
              exact simulation_loop_term_enter_case π φ hwf_ext reserved
                σ _ measure inv body md hok ρ₀ ρ'
                hswf (.step _ _ _ (.step_loop_enter hgt hinvb hinviff hwfbe hmease) hrest)
                hnf'' hnf₀ hall_tt hnif hrest
            | step_loop_nondet_exit hib hff_iff =>
              exact loop_zero_iter_term_branch π φ hswf.wfBool hnf₀ hnf''
                hrest hall_tt hfib_eq
                (ite_nondet_false_empty_terminal (P := Expression) (CmdT := Command) (EvalCommand π φ) (EvalPureFunc φ)
                  then_branch {} ρ₀)
            | step_loop_nondet_enter hinvb_ne hinviff_ne =>
              have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest hnf''
              have hnif := loop_step_hasInvFailure_false_of_or
                (by simpa [Config.getEnv] using hh)
              rw [← htgt_eq]
              exact simulation_loop_term_enter_case π φ hwf_ext reserved
                σ .nondet measure inv body md hok ρ₀ ρ'
                hswf (.step _ _ _ (.step_loop_nondet_enter hinvb_ne hinviff_ne) hrest)
                hnf'' hnf₀ hall_tt hnif hrest
        · -- VC1 failure path: some invariant evaluates to ff at ρ₀.
          -- The target's first_iter_block contains entry-asserts on each
          -- invariant; one of these will canFail.  Works for both det and
          -- nondet (and both 0-iter and ≥1-iter).
          refine .inl ?_
          exact loop_vc1_failure_canFail π φ hswf.wfBool hinv_bool
            (not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt) hfib_eq
  case exit_branch =>
    intro lbl ρ' hreach
    match st with
    | .cmd c =>
      -- .cmd cannot reach .exiting
      rw [stmtResult_cmd]
      exfalso
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_cmd _ =>
          cases r1 with
          | step _ _ _ h2 _ => cases h2
    | .exit l md =>
      rw [stmtResult_exit]
      -- .exit l md reaches .exiting l ρ₀ (and lbl = l, ρ' = ρ₀)
      exact .inr (fun _ => hreach)
    | .funcDecl d md =>
      rw [stmtResult_funcDecl]
      exfalso
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_funcDecl =>
          cases r1 with
          | step _ _ _ h2 _ => cases h2
    | .typeDecl tc md =>
      rw [stmtResult_typeDecl]
      exfalso
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_typeDecl =>
          cases r1 with
          | step _ _ _ h2 _ => cases h2
    | .block l bss md =>
      rw [stmtResult_block (hok := hok)]
      have hsz_bss : Block.sizeOf bss ≤ n := by
        simp [Stmt.sizeOf] at hsz; omega
      have hsim_bss := ih.2.1 σ bss hsz_bss (stmtOk_block_inner hok) ρ₀
        (InitEnvWF.toBlock_block hswf)
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_block => exact block_exit_case π φ r1 hsim_bss
    | .ite c tss ess md =>
      rw [stmtResult_ite (hok := hok)]
      have hsz_tss : Block.sizeOf tss ≤ n := by
        simp [Stmt.sizeOf] at hsz; omega
      have hsz_ess : Block.sizeOf ess ≤ n := by
        simp [Stmt.sizeOf] at hsz; omega
      have hsim_tss := ih.2.1 σ tss hsz_tss (stmtOk_ite_left hok) ρ₀
        (InitEnvWF.toBlock_ite_left hswf)
      have hsim_ess := ih.2.1 (blockPostState σ tss) ess hsz_ess
        (stmtOk_ite_right hok) ρ₀ (InitEnvWF.toBlock_ite_right hswf)
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_ite_true hcond hwfb' =>
          exact ite_exit_branch_lift π φ (.step_ite_true hcond hwfb') r1 (hsim_tss.2 lbl)
        | step_ite_false hcond hwfb' =>
          exact ite_exit_branch_lift π φ (.step_ite_false hcond hwfb') r1 (hsim_ess.2 lbl)
        | step_ite_nondet_true =>
          exact ite_exit_branch_lift π φ .step_ite_nondet_true r1 (hsim_tss.2 lbl)
        | step_ite_nondet_false =>
          exact ite_exit_branch_lift π φ .step_ite_nondet_false r1 (hsim_ess.2 lbl)
    | .loop guard measure inv body md =>
      exact simulation_loop_exit_case π φ hwf_ext reserved σ
        guard measure inv body md hok ρ₀ hswf lbl ρ' hreach

private theorem block_corr_step
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (n : Nat) (ih : SimAllProp π φ reserved n) :
    SimBlockCorrProp π φ reserved (n + 1) := by
  intro σ bss hsz hok ρ₀ hswf
  refine ⟨?bterm, ?bexit⟩
  case bterm =>
    intro ρ' hreach
    match bss with
    | [] =>
      rw [blockResult_nil]
      exact .inr (fun _ => hreach)
    | s :: ss =>
      rw [blockResult_cons (hok := hok)]
      have hsz_s : Stmt.sizeOf s ≤ n := by
        simp [Block.sizeOf] at hsz; omega
      have hsz_ss : Block.sizeOf ss ≤ n := by
        simp [Block.sizeOf] at hsz; omega
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_stmts_cons =>
          obtain ⟨ρ₁, hterm_s, hreach_ss⟩ := seq_reaches_terminal (P := Expression)
            (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1
          have hswf_s : InitEnvWF reserved s ρ₀ :=
            BlockInitEnvWF.toStmt_head hswf
          have hsim_s := ih.1 σ s hsz_s (blockOk_cons_left hok) ρ₀ hswf_s
          have hsim_ss := ih.2.1 (stmtPostState σ s) ss hsz_ss
            (blockOk_cons_right hok) ρ₁
            (BlockInitEnvWF.toBlock_tail_via_defUseOk (π := π) (φ := φ) hwf_ext hswf hterm_s)
          exact block_corr_cons_term_head_term π φ hterm_s hreach_ss
            (fun h => hsim_s.1 ρ₁ h)
            (fun h => ih.2.2.1 σ s hsz_s (blockOk_cons_left hok) ρ₀ hswf_s h)
            hsim_ss.1
  case bexit =>
    intro lbl ρ' hreach
    match bss with
    | [] =>
      exfalso
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_stmts_nil =>
          cases r1 with
          | step _ _ _ h2 _ => cases h2
    | s :: ss =>
      rw [blockResult_cons (hok := hok)]
      have hsz_s : Stmt.sizeOf s ≤ n := by
        simp [Block.sizeOf] at hsz; omega
      have hsz_ss : Block.sizeOf ss ≤ n := by
        simp [Block.sizeOf] at hsz; omega
      cases hreach with
      | step _ _ _ h1 r1 =>
        cases h1 with
        | step_stmts_cons =>
          match seq_reaches_exiting (P := Expression)
            (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
          | .inl hexit_s =>
            have hsim_s := ih.1 σ s hsz_s (blockOk_cons_left hok) ρ₀
              (BlockInitEnvWF.toStmt_head hswf)
            match hsim_s.2 lbl ρ' hexit_s with
            | .inl hcf_s =>
              exact .inl (Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert _ _ ρ₀ hcf_s)
            | .inr hok_s =>
              refine .inr (fun hnf => ?_)
              exact stmts_cons_exiting (EvalCommand π φ) (EvalPureFunc φ) _ _ lbl ρ₀ ρ' (hok_s hnf)
          | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
            have hswf_s := BlockInitEnvWF.toStmt_head hswf
            have hsim_s := ih.1 σ s hsz_s (blockOk_cons_left hok) ρ₀ hswf_s
            have hsim_ss := ih.2.1 (stmtPostState σ s) ss hsz_ss
              (blockOk_cons_right hok) ρ₁
              (BlockInitEnvWF.toBlock_tail_via_defUseOk (π := π) (φ := φ) hwf_ext hswf hterm_s)
            exact block_corr_cons_exit_head_term π φ hterm_s hexit_ss
              (fun h => hsim_s.1 ρ₁ h)
              (fun h => ih.2.2.1 σ s hsz_s (blockOk_cons_left hok) ρ₀ hswf_s h)
              (hsim_ss.2 lbl)

private theorem stmt_cf_step
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (h_loop_reserved : loopElimReservedPrefix ∈ reserved)
    (n : Nat) (ih : SimAllProp π φ reserved n) :
    SimStmtCFProp π φ reserved (n + 1) := by
  intro σ st hsz hok ρ₀ hswf hcf
  obtain ⟨cfg, hfail, hreach⟩ := hcf
  match st with
  | .cmd c => rw [stmtResult_cmd]; exact ⟨cfg, hfail, hreach⟩
  | .exit l md => rw [stmtResult_exit]; exact ⟨cfg, hfail, hreach⟩
  | .funcDecl d md => rw [stmtResult_funcDecl]; exact ⟨cfg, hfail, hreach⟩
  | .typeDecl tc md => rw [stmtResult_typeDecl]; exact ⟨cfg, hfail, hreach⟩
  | .block l bss md =>
    rw [stmtResult_block (hok := hok)]
    have hsz_bss : Block.sizeOf bss ≤ n := by
      simp [Stmt.sizeOf] at hsz; omega
    have hcf_inner : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss ρ₀ → CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀ :=
      fun h => ih.2.2.2 σ bss hsz_bss (stmtOk_block_inner hok) ρ₀
        (InitEnvWF.toBlock_block hswf) h
    cases hreach with
    | refl => exact ⟨.stmt (.block l (blockResult σ bss) md) ρ₀, hfail, .refl _⟩
    | step _ _ _ h1 r1 => cases h1 with
      | step_block => exact block_canfail_case π φ hfail r1 hcf_inner
  | .ite c tss ess md =>
    rw [stmtResult_ite (hok := hok)]
    have hsz_tss : Block.sizeOf tss ≤ n := by
      simp [Stmt.sizeOf] at hsz; omega
    have hsz_ess : Block.sizeOf ess ≤ n := by
      simp [Stmt.sizeOf] at hsz; omega
    have hcf_tss : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) tss ρ₀ → CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ tss) ρ₀ :=
      fun h => ih.2.2.2 σ tss hsz_tss (stmtOk_ite_left hok) ρ₀
        (InitEnvWF.toBlock_ite_left hswf) h
    have hcf_ess : CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) ess ρ₀ →
        CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult (blockPostState σ tss) ess) ρ₀ :=
      fun h => ih.2.2.2 (blockPostState σ tss) ess hsz_ess
        (stmtOk_ite_right hok) ρ₀ (InitEnvWF.toBlock_ite_right hswf) h
    cases hreach with
    | refl => exact ⟨.stmt (.ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md) ρ₀, hfail, .refl _⟩
    | step _ _ _ h1 r1 => cases h1 with
      | step_ite_true hcond hwfb' =>
        exact ite_canfail_lift π φ hfail (.step_ite_true hcond hwfb') r1 hcf_tss
      | step_ite_false hcond hwfb' =>
        exact ite_canfail_lift π φ hfail (.step_ite_false hcond hwfb') r1 hcf_ess
      | step_ite_nondet_true =>
        exact ite_canfail_lift π φ hfail .step_ite_nondet_true r1 hcf_tss
      | step_ite_nondet_false =>
        exact ite_canfail_lift π φ hfail .step_ite_nondet_false r1 hcf_ess
  | .loop guardE measure inv body md =>
    by_cases hnf₀ : ρ₀.hasFailure = Bool.true
    · exact ⟨.stmt (stmtResult σ (.loop guardE measure inv body md)) ρ₀,
        by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
    · have hnf₀' : ρ₀.hasFailure = Bool.false := by
        cases h : ρ₀.hasFailure
        · rfl
        · exact absurd h hnf₀
      have hinv_bool : ∀ le ∈ inv,
          ρ₀.eval ρ₀.store le.2 = some HasBool.tt ∨
          ρ₀.eval ρ₀.store le.2 = some HasBool.ff := by
        cases hreach with
        | refl =>
          exfalso
          have : ρ₀.hasFailure = Bool.true := hfail
          rw [hnf₀'] at this; cases this
        | step _ _ _ h1 _ => exact loop_first_step_hinv_bool π φ h1
      obtain ⟨loop_label, first_iter_label, first_iter_body, then_branch,
              htgt_eq, hfib_eq⟩ :=
        stmtResult_loop_struct σ guardE measure inv body md hok
      rw [htgt_eq]
      by_cases hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt
      · rw [← htgt_eq]
        exact simulation_loop_cf_all_tt π φ hwf_ext reserved σ
          guardE measure inv body md hok ρ₀ hswf cfg hfail hreach hnf₀'
          hall_tt
      · exact loop_vc1_failure_canFail π φ hswf.wfBool hinv_bool
          (not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt) hfib_eq

private theorem block_cf_step
    (hwf_ext : WFEvalExtension φ)
    (reserved : List String)
    (n : Nat) (ih : SimAllProp π φ reserved n) :
    SimBlockCFProp π φ reserved (n + 1) := by
  intro σ bss hsz hok ρ₀ hswf hcf
  obtain ⟨cfg, hfail, hreach⟩ := hcf
  match bss with
  | [] => rw [blockResult_nil]; exact ⟨cfg, hfail, hreach⟩
  | s :: ss =>
    rw [blockResult_cons (hok := hok)]
    have hsz_s : Stmt.sizeOf s ≤ n := by
      simp [Block.sizeOf] at hsz; omega
    have hsz_ss : Block.sizeOf ss ≤ n := by
      simp [Block.sizeOf] at hsz; omega
    cases hreach with
    | refl =>
      exact ⟨.stmts (stmtResult σ s :: blockResult (stmtPostState σ s) ss) ρ₀, hfail, .refl _⟩
    | step _ _ _ h1 r1 => cases h1 with
      | step_stmts_cons =>
        match seq_canfail_prop r1 hfail with
        | .inl ⟨cfg', hf', hstar'⟩ =>
          have ⟨kcfg, hkf, hkstar⟩ := ih.2.2.1 σ s hsz_s
            (blockOk_cons_left hok) ρ₀ (BlockInitEnvWF.toStmt_head hswf)
            ⟨cfg', hf', hstar'⟩
          exact Transform.canFail_head_to_block (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert (stmtResult σ s)
            (blockResult (stmtPostState σ s) ss) ρ₀ ⟨kcfg, hkf, hkstar⟩
        | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
          have hswf_s := BlockInitEnvWF.toStmt_head hswf
          have hsim_s := ih.1 σ s hsz_s (blockOk_cons_left hok) ρ₀ hswf_s
          exact block_cf_cons_head_term π φ hterm_s ⟨cfg', hf', hstar_rest⟩
            (fun h => hsim_s.1 ρ₁ h)
            (fun h => ih.2.2.1 σ s hsz_s (blockOk_cons_left hok) ρ₀ hswf_s h)
            (fun h => ih.2.2.2 (stmtPostState σ s) ss hsz_ss
              (blockOk_cons_right hok) ρ₁
              (BlockInitEnvWF.toBlock_tail_via_defUseOk (π := π) (φ := φ) hwf_ext hswf hterm_s) h)

set_option maxHeartbeats 400000 in
private theorem simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat)
    (reserved : List String)
    (h_loop_reserved : loopElimReservedPrefix ∈ reserved) :
    -- Statement level
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      stmtOk σ st →
      ∀ (ρ₀ : Env Expression),
        InitEnvWF reserved st ρ₀ →
        (∀ ρ', CoreStar π φ (.stmt st ρ₀) (.terminal ρ') →
          Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmt (stmtResult σ st) ρ₀) (.terminal ρ')))
        ∧
        (∀ lbl ρ', CoreStar π φ (.stmt st ρ₀) (.exiting lbl ρ') →
          Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmt (stmtResult σ st) ρ₀) (.exiting lbl ρ'))))
    ∧
    -- Block level
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      blockOk σ bss →
      ∀ (ρ₀ : Env Expression),
        BlockInitEnvWF reserved bss ρ₀ →
        (∀ ρ', CoreStar π φ (.stmts bss ρ₀) (.terminal ρ') →
          CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.terminal ρ')))
        ∧
        (∀ lbl ρ', CoreStar π φ (.stmts bss ρ₀) (.exiting lbl ρ') →
          CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.exiting lbl ρ'))))
    ∧
    -- Statement CanFail preservation
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      stmtOk σ st →
      ∀ (ρ₀ : Env Expression),
        InitEnvWF reserved st ρ₀ →
        Transform.CanFail (LangCore π φ) st ρ₀ →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀)
    ∧
    -- Block CanFail preservation
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      blockOk σ bss →
      ∀ (ρ₀ : Env Expression),
        BlockInitEnvWF reserved bss ρ₀ →
        CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss ρ₀ →
        CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀) := by
  induction sz with
  | zero =>
    refine ⟨fun σ st hsz _ => ?_, fun σ bss hsz _ => ?_,
            fun σ st hsz _ => ?_, fun σ bss hsz _ => ?_⟩
    · -- Statement-level correctness at sz = 0: no statement has sizeOf 0
      match st with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · -- Block-level correctness at sz = 0: only [] possible
      match bss with
      | [] =>
        intro ρ₀ _
        rw [blockResult_nil]
        exact ⟨fun ρ' h => .inr (fun _ => h), fun lbl ρ' h => .inr (fun _ => h)⟩
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
    · -- Statement-level CanFail at sz = 0
      match st with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · -- Block-level CanFail at sz = 0
      match bss with
      | [] =>
        intro ρ₀ _ hcf
        rw [blockResult_nil]
        exact hcf
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
  | succ n ih =>
    refine ⟨?stmt_corr, ?block_corr, ?stmt_cf, ?block_cf⟩
    case stmt_corr => exact stmt_corr_step π φ hwf_ext reserved h_loop_reserved n ih
    case block_corr => exact block_corr_step π φ hwf_ext reserved n ih
    case stmt_cf => exact stmt_cf_step π φ hwf_ext reserved h_loop_reserved n ih
    case block_cf => exact block_cf_step π φ hwf_ext reserved n ih

private theorem canfail_simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat)
    (reserved : List String)
    (h_loop_reserved : loopElimReservedPrefix ∈ reserved) :
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      stmtOk σ st →
      ∀ (ρ₀ : Env Expression),
        InitEnvWF reserved st ρ₀ →
        Transform.CanFail (LangCore π φ) st ρ₀ →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀)
    ∧
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      blockOk σ bss →
      ∀ (ρ₀ : Env Expression),
        BlockInitEnvWF reserved bss ρ₀ →
        CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) bss ρ₀ →
        CanFailBlock (EvalCommand π φ) (EvalPureFunc φ) (blockResult σ bss) ρ₀) := by
  have hsim := simulation π φ hwf_ext sz reserved h_loop_reserved
  exact ⟨fun σ st hsz hok ρ₀ hswf hcf =>
           hsim.2.2.1 σ st hsz hok ρ₀ hswf hcf,
         fun σ bss hsz hok ρ₀ hswf hcf =>
           hsim.2.2.2 σ bss hsz hok ρ₀ hswf hcf⟩

/-! ## Top-level theorem -/

/-- Havoc-only command lists have empty `Block.definedVars`. -/
private theorem definedVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.definedVars Expression Command _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) false = [] := by
  induction xs with
  | nil => simp [Block.definedVars]
  | cons x rest ih =>
    simp only [List.map_cons, Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasHavoc.havoc x md : Command)) false ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasHavoc.havoc, Command.definedVars, Cmd.definedVars]

/-- A `mapIdx` of asserts has empty `Block.definedVars`. -/
private theorem definedVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.definedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) false = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.definedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md : Command)) false ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assert,
      Command.definedVars, Cmd.definedVars]

/-- A `mapIdx` of assumes has empty `Block.definedVars`. -/
private theorem definedVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.definedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) false = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.definedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md : Command)) false ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assume,
      Command.definedVars, Cmd.definedVars]

/-- The prefix `"$__loop"` is a list-prefix of `"$__loop_measure_<n>"`. -/
private theorem loopElimReservedPrefix_isPrefixOf_measure (loop_num : String) :
    loopElimReservedPrefix.toList.isPrefixOf
      (s!"$__loop_measure_{loop_num}").toList := by
  -- `s!"$__loop_measure_{loop_num}"` reduces to `"$__loop" ++ "_measure_" ++ loop_num`.
  show loopElimReservedPrefix.toList.isPrefixOf
        (("$__loop" ++ "_measure_" ++ loop_num).toList) = Bool.true
  rw [String.toList_append, String.toList_append]
  show loopElimReservedPrefix.toList.isPrefixOf
        (loopElimReservedPrefix.toList ++ "_measure_".toList ++ loop_num.toList) = Bool.true
  rw [List.append_assoc]
  exact isPrefixOf_append_self _ _

/-! Additional helper lemmas for `Block.getVars`/`Block.modifiedOrDefinedVars`
    over append and over havoc/assert/assume `map`/`mapIdx` — needed for
    `mem_touchedVars_stmtResult_loop` (mirroring `definedVars_havoc_map` etc.). -/

private theorem block_getVars_append (ss₁ ss₂ : Statements) :
    Block.getVars (ss₁ ++ ss₂) = Block.getVars ss₁ ++ Block.getVars ss₂ := by
  induction ss₁ with
  | nil => simp [Block.getVars]
  | cons s rest ih => simp [Block.getVars, ih, List.append_assoc]

private theorem block_modifiedOrDefinedVars_append (ss₁ ss₂ : Statements) :
    Block.modifiedOrDefinedVars (ss₁ ++ ss₂) false =
      (Block.modifiedVars ss₁ ++ Block.modifiedVars ss₂) ++
      (Block.definedVars ss₁ false ++ Block.definedVars ss₂ false) := by
  simp only [Block.modifiedOrDefinedVars, block_modifiedVars_append, block_definedVars_append]

/-- Havoc-only command lists have empty `Block.getVars` (havoc reads nothing). -/
private theorem getVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.getVars Expression Command _ _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = [] := by
  induction xs with
  | nil => simp [Block.getVars]
  | cons x rest ih =>
    show @Stmt.getVars Expression Command _ _ (Stmt.cmd (HasHavoc.havoc x md)) ++
         @Block.getVars Expression Command _ _
           (rest.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = []
    rw [ih]
    show @HasVarsPure.getVars Expression Command _ (HasHavoc.havoc x md) ++ [] = []
    simp [HasVarsPure.getVars, HasHavoc.havoc, Command.getVars, Cmd.getVars,
      ExprOrNondet.getVars]

/-- Havoc-only command lists have `Block.modifiedOrDefinedVars` equal to the
    havoc'd variables (havoc modifies but does not define). -/
private theorem modifiedVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.modifiedVars Expression Command _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = xs := by
  induction xs with
  | nil => simp [Block.modifiedVars]
  | cons x rest ih =>
    simp only [List.map_cons, Block.modifiedVars]
    rw [ih]
    show @Stmt.modifiedVars Expression Command _ (Stmt.cmd (HasHavoc.havoc x md : Command)) ++ rest = x :: rest
    simp [Stmt.modifiedVars, HasVarsImp.modifiedVars, HasHavoc.havoc, Command.modifiedVars, Cmd.modifiedVars]

private theorem modifiedOrDefinedVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.modifiedOrDefinedVars Expression Command _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) false = xs := by
  show Block.modifiedVars _ ++ Block.definedVars _ false = xs
  rw [modifiedVars_havoc_map xs md, definedVars_havoc_map xs md, List.append_nil]

/-- A `mapIdx` of asserts has empty `Block.modifiedOrDefinedVars`. -/
private theorem modifiedVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.modifiedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.modifiedVars]
    rw [ih]
    show @Stmt.modifiedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md : Command)) ++ [] = []
    simp [Stmt.modifiedVars, HasVarsImp.modifiedVars, HasPassiveCmds.assert,
      Command.modifiedVars, Cmd.modifiedVars]

private theorem modifiedOrDefinedVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedOrDefinedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) false = [] := by
  show Block.modifiedVars _ ++ Block.definedVars _ false = []
  rw [modifiedVars_mapIdx_assert inv md label, definedVars_mapIdx_assert inv md label]
  rfl

/-- A `mapIdx` of assumes has empty `Block.modifiedOrDefinedVars`. -/
private theorem modifiedVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.modifiedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.modifiedVars]
    rw [ih]
    show @Stmt.modifiedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md : Command)) ++ [] = []
    simp [Stmt.modifiedVars, HasVarsImp.modifiedVars, HasPassiveCmds.assume,
      Command.modifiedVars, Cmd.modifiedVars]

private theorem modifiedOrDefinedVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedOrDefinedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) false = [] := by
  show Block.modifiedVars _ ++ Block.definedVars _ false = []
  rw [modifiedVars_mapIdx_assume inv md label, definedVars_mapIdx_assume inv md label]
  rfl

/-- The `getVars` of a `mapIdx` of asserts equals the `flatMap` of `getVars`
    over the underlying expressions (the labels do not contribute reads). -/
private theorem getVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.getVars Expression Command _ _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) =
    inv.flatMap (fun lp => HasVarsPure.getVars lp.2) := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.getVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons, List.flatMap_cons]
    show @Stmt.getVars Expression Command _ _
           (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md)) ++
         @Block.getVars Expression Command _ _
           (rest.mapIdx (fun i le =>
              Stmt.cmd (HasPassiveCmds.assert (label (i + 1) le) le.2 md))) =
         HasVarsPure.getVars x.2 ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2)
    rw [ih]
    show @HasVarsPure.getVars Expression Command _
            (HasPassiveCmds.assert (label 0 x) x.2 md) ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2) =
         HasVarsPure.getVars x.2 ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2)
    simp [HasVarsPure.getVars, HasPassiveCmds.assert, Command.getVars, Cmd.getVars]

/-- The `getVars` of a `mapIdx` of assumes equals the `flatMap` of `getVars`. -/
private theorem getVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.getVars Expression Command _ _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) =
    inv.flatMap (fun lp => HasVarsPure.getVars lp.2) := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.getVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons, List.flatMap_cons]
    show @Stmt.getVars Expression Command _ _
           (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md)) ++
         @Block.getVars Expression Command _ _
           (rest.mapIdx (fun i le =>
              Stmt.cmd (HasPassiveCmds.assume (label (i + 1) le) le.2 md))) =
         HasVarsPure.getVars x.2 ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2)
    rw [ih]
    show @HasVarsPure.getVars Expression Command _
            (HasPassiveCmds.assume (label 0 x) x.2 md) ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2) =
         HasVarsPure.getVars x.2 ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2)
    simp [HasVarsPure.getVars, HasPassiveCmds.assume, Command.getVars, Cmd.getVars]

/-! ### Unfolded variants of mapIdx lemmas

The lemmas above use `HasPassiveCmds.assert/assume` in the LHS. When `dsimp`
normalizes terms to use the underlying `CmdExt.cmd (Cmd.assert/assume ...)`
form (which can happen via `simp only [HasPassiveCmds.assert]` or transitive
unfolding), these LHS patterns no longer match. The unfolded variants below
mirror the originals with `CmdExt.cmd (Cmd.assert/assume ...)` in the LHS, so
they work regardless of which form the simp normal form chooses. -/

private theorem mem_definedVars_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars (stmtResult σ (.loop guard measure inv body md)) false) :
    n ∈ Block.definedVars body false ∨
    loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
  -- Wrap the conclusion in an existential over the loop_num, so that `cases h`
  -- can unify and `rfl` can close the equation in each branch.
  suffices h_suff :
    ∃ (loop_num : String) (s' : Statement),
      stmtResult σ (.loop guard measure inv body md) = s' ∧
      ∀ m, m ∈ Stmt.definedVars s' false →
        m ∈ Block.definedVars body false ∨
        m = (⟨"$__loop_measure_" ++ loop_num, ()⟩ : Expression.Ident) by
    obtain ⟨loop_num, s', hs'_eq, hs'_prop⟩ := h_suff
    rw [hs'_eq] at hn
    rcases hs'_prop n hn with h_body | h_meas
    · exact .inl h_body
    · subst h_meas
      exact .inr (loopElimReservedPrefix_isPrefixOf_measure _)
  -- Unfold stmtResult for the loop case to expose the monadic match.
  change ∃ (loop_num : String) (s' : Statement),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s'') => s'' | .error _ => default) = s' ∧
    ∀ m, m ∈ Stmt.definedVars s' false →
      m ∈ Block.definedVars body false ∨
      m = (⟨"$__loop_measure_" ++ loop_num, ()⟩ : Expression.Ident)
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    -- Reduce the monadic computation to expose case splits on guard/measure.
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    -- Dispatch each branch:
    -- - Happy paths: `cases h` unifies the pair, then we analyze definedVars.
    -- - Error paths: `contradiction` (since hok' rules out .error results).
    repeat (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
              block_definedVars_append false, List.append_nil] at hm
            repeat rw [definedVars_havoc_map] at hm
            repeat rw [definedVars_mapIdx_assert] at hm
            repeat rw [definedVars_mapIdx_assume] at hm
            simp only [HasVarsImp.definedVars, HasPassiveCmds.assert,
              HasPassiveCmds.assume, HasInit.init, HasIdent.ident,
              Command.definedVars, Cmd.definedVars,
              List.append_nil, List.nil_append, List.mem_append,
              List.not_mem_nil, false_or, or_false, List.mem_singleton] at hm
            first
              | exact .inl hm
              | exact .inr hm
              | (rcases hm with h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)⟩)
      | contradiction
      | (split at h; skip))
    -- Close residual goal: the `.det g, some m` case where `h` still has
    -- `StateT.pure ... .bind ...` wrapping the freshness check.
    -- We use `unfold` + the same split/cases/contradiction cycle.
    all_goals (first | contradiction | (
      unfold StateT.pure at h
      dsimp only [StateT.bind, StateT.map, ExceptT.bindCont, ExceptT.bind,
        ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
        Functor.map, MonadState.modifyGet, StateT.modifyGet,
        MonadStateOf.modifyGet, bumpStat, modify, genLoopNum] at h
      repeat (first
        | (cases h; exact
            ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
              simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
                block_definedVars_append false, List.append_nil] at hm
              repeat rw [definedVars_havoc_map] at hm
              repeat rw [definedVars_mapIdx_assert] at hm
              repeat rw [definedVars_mapIdx_assume] at hm
              simp only [HasVarsImp.definedVars, HasPassiveCmds.assert,
                HasPassiveCmds.assume, HasInit.init, HasIdent.ident,
                Command.definedVars, Cmd.definedVars,
                List.append_nil, List.nil_append, List.mem_append,
                List.not_mem_nil, false_or, or_false, List.mem_singleton] at hm
              first
                | exact .inl hm
                | exact .inr hm
                | (rcases hm with h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
                | (rcases hm with h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
                | (rcases hm with h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
                | (rcases hm with h1 | h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)⟩)
        | contradiction
        | (split at h; skip))
      all_goals (first | contradiction | (
        obtain ⟨_, rfl⟩ := h
        exact ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
          simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
            block_definedVars_append (ex := Bool.false), List.append_nil] at hm
          repeat rw [definedVars_havoc_map] at hm
          repeat rw [definedVars_mapIdx_assert] at hm
          repeat rw [definedVars_mapIdx_assume] at hm
          simp only [HasVarsImp.definedVars, HasPassiveCmds.assert,
            HasPassiveCmds.assume, HasInit.init, HasIdent.ident,
            Command.definedVars, Cmd.definedVars,
            List.append_nil, List.nil_append, List.mem_append,
            List.not_mem_nil, false_or, or_false, List.mem_singleton] at hm
          first
            | exact .inl hm
            | exact .inr hm
            | (rcases hm with h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
            | (rcases hm with h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
            | (rcases hm with h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
            | (rcases hm with h1 | h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)⟩))))

/-! Every name newly defined by the transform either was already a defined var
    of the source statement, or starts with the reserved `loopElimReservedPrefix`. -/
mutual
private theorem mem_definedVars_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s) (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars (stmtResult σ s) false) :
    n ∈ Stmt.definedVars s false ∨
    loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
  match s with
  | .cmd c =>
    rw [stmtResult_cmd] at hn; exact .inl hn
  | .exit l md =>
    rw [stmtResult_exit] at hn; exact .inl hn
  | .funcDecl d md =>
    rw [stmtResult_funcDecl] at hn; exact .inl hn
  | .typeDecl tc md =>
    rw [stmtResult_typeDecl] at hn; exact .inl hn
  | .block l bss md =>
    rw [stmtResult_block (hok := hok)] at hn
    have hn' : n ∈ Block.definedVars (blockResult σ bss) false := by
      simpa [Stmt.definedVars] using hn
    have := mem_definedVars_blockResult σ bss (stmtOk_block_inner hok) n hn'
    rcases this with h | h
    · exact .inl (by simpa [Stmt.definedVars] using h)
    · exact .inr h
  | .ite c tss ess md =>
    rw [stmtResult_ite (hok := hok)] at hn
    have hn' : n ∈ Block.definedVars (blockResult σ tss) false ++
                   Block.definedVars (blockResult (blockPostState σ tss) ess) false := by
      simpa [Stmt.definedVars] using hn
    rcases List.mem_append.mp hn' with h | h
    · rcases mem_definedVars_blockResult σ tss (stmtOk_ite_left hok) n h with h | h
      · exact .inl (by simpa [Stmt.definedVars] using List.mem_append_left _ h)
      · exact .inr h
    · rcases mem_definedVars_blockResult (blockPostState σ tss) ess
                (stmtOk_ite_right hok) n h with h | h
      · exact .inl (by simpa [Stmt.definedVars] using List.mem_append_right _ h)
      · exact .inr h
  | .loop guard measure inv body md =>
    -- The loop body is *not* recursively transformed by `stmtResult` — only the
    -- outer wrapper is generated.  Hence `Stmt.definedVars (loop ... body ...)`
    -- equals `Block.definedVars body`, and the helper directly suffices.
    have h := mem_definedVars_stmtResult_loop σ guard measure inv body md hok n hn
    rcases h with h | h
    · exact .inl (by simp [Stmt.definedVars]; exact h)
    · exact .inr h

private theorem mem_definedVars_blockResult
    (σ : LoopElimState) (bss : Statements) (hok : blockOk σ bss)
    (n : Expression.Ident)
    (hn : n ∈ Block.definedVars (blockResult σ bss) false) :
    n ∈ Block.definedVars bss false ∨
    loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
  match bss with
  | [] =>
    rw [blockResult_nil] at hn
    simp [Block.definedVars] at hn
  | s :: rest =>
    rw [blockResult_cons (hok := hok)] at hn
    have hn' : n ∈ Stmt.definedVars (stmtResult σ s) false ++
                   Block.definedVars (blockResult (stmtPostState σ s) rest) false := by
      simpa [Block.definedVars] using hn
    rcases List.mem_append.mp hn' with h | h
    · rcases mem_definedVars_stmtResult σ s (blockOk_cons_left hok) n h with h | h
      · exact .inl (by simpa [Block.definedVars] using List.mem_append_left _ h)
      · exact .inr h
    · rcases mem_definedVars_blockResult (stmtPostState σ s) rest
              (blockOk_cons_right hok) n h with h | h
      · exact .inl (by simpa [Block.definedVars] using List.mem_append_right _ h)
      · exact .inr h
end

/-! ## funcDeclNames preservation: output's funcDeclNames ⊆ source's funcDeclNames

The transform replaces loops with `block`/`ite` wrappers around the original
body — it never inserts new `funcDecl` AST nodes.  Hence
`funcDeclNames (stmtResult σ s) ⊆ funcDeclNames s` strictly. -/

/-- If every element of a list of statements is a `Stmt.cmd`, the list's
    `funcDeclNames` is empty. -/
private theorem funcDeclNames_eq_nil_of_all_cmd
    (l : Statements)
    (hall : ∀ s ∈ l, ∃ c, s = Stmt.cmd c) :
    Block.funcDeclNames (P := Expression) (C := Command) l = [] := by
  induction l with
  | nil => simp [Block.funcDeclNames]
  | cons hd tl ih =>
    simp only [Block.funcDeclNames]
    obtain ⟨c, hc⟩ := hall hd (List.Mem.head _)
    rw [hc]
    simp only [Stmt.funcDeclNames, List.nil_append]
    exact ih (fun s hs => hall s (List.Mem.tail _ hs))

private theorem funcDeclNames_mapIdx_assert
    (loop_num : String) (lbl_mid : String)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression) :
    Block.funcDeclNames (P := Expression) (C := Command)
      (inv.mapIdx (fun i lp =>
        Stmt.cmd (HasPassiveCmds.assert
          (toString loopElimAssertPrefix ++ loop_num ++ lbl_mid ++
            toString (if lp.fst.isEmpty = Bool.true then toString i
                      else toString i ++ toString "_" ++ toString lp.fst))
          lp.snd md))) = [] := by
  apply funcDeclNames_eq_nil_of_all_cmd
  intro s hs
  rw [List.mem_mapIdx] at hs
  obtain ⟨i, _, heq⟩ := hs
  exact ⟨_, heq.symm⟩

private theorem funcDeclNames_mapIdx_assume
    (loop_num : String) (lbl_mid : String)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression) :
    Block.funcDeclNames (P := Expression) (C := Command)
      (inv.mapIdx (fun i lp =>
        Stmt.cmd (HasPassiveCmds.assume
          (toString loopElimAssumePrefix ++ loop_num ++ lbl_mid ++
            toString (if lp.fst.isEmpty = Bool.true then toString i
                      else toString i ++ toString "_" ++ toString lp.fst))
          lp.snd md))) = [] := by
  apply funcDeclNames_eq_nil_of_all_cmd
  intro s hs
  rw [List.mem_mapIdx] at hs
  obtain ⟨i, _, heq⟩ := hs
  exact ⟨_, heq.symm⟩

private theorem funcDeclNames_havoc_block
    (body : Statements) (md : MetaData Expression) :
    Block.funcDeclNames (P := Expression) (C := Command)
      (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
        (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
          (Block.modifiedVars body))) = [] := by
  apply funcDeclNames_eq_nil_of_all_cmd
  intro s hs
  rcases List.mem_map.mp hs with ⟨n, _, heq⟩
  exact ⟨_, heq.symm⟩

/-- The transform's loop output's funcDeclNames is exactly the body's
    funcDeclNames: the wrapping `block`/`ite`/`havoc`/`mapIdx-assert/assume`
    structures introduce no funcDecls. -/
private theorem funcDeclNames_stmtResult_loop_subset
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (n : Expression.Ident)
    (hn : n ∈ Stmt.funcDeclNames (stmtResult σ (.loop guard measure inv body md))) :
    n ∈ Block.funcDeclNames body := by
  -- Use stmtResult_loop_struct to get a structured form, then enumerate.
  -- Simpler: directly unfold via the same pattern as
  -- `mem_definedVars_stmtResult_loop`, but with `funcDeclNames` instead.
  change n ∈ Stmt.funcDeclNames
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
     | .ok (_, s'') => s'' | .error _ => default) at hn
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h] at hn
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase,
      buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes,
      buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants,
      buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants,
      buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome,
      hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    -- All branches unify h; in each unified branch, hn is `n ∈ funcDeclNames result`.
    -- We need to show n is in body's funcDeclNames.  Unfold and simp.
    repeat (first | contradiction | (split at h; skip))
    all_goals (first | contradiction | (
      try (unfold StateT.pure at h
           dsimp only [StateT.bind, StateT.map, ExceptT.bindCont, ExceptT.bind,
             ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
             Functor.map, MonadState.modifyGet, StateT.modifyGet,
             MonadStateOf.modifyGet, bumpStat, modify, genLoopNum] at h
           repeat (first | contradiction | (split at h; skip)))
      all_goals (first
        | contradiction
        | (obtain ⟨_, rfl⟩ := h
           simp only [Stmt.funcDeclNames, Block.funcDeclNames,
             block_funcDeclNames_append] at hn
           -- hn breaks into pieces; only `body` and concrete `.cmd` lists.
           -- Reduce: mapIdx assert/assume → []; havoc map → []; .cmd → [].
           repeat rw [funcDeclNames_mapIdx_assert] at hn
           repeat rw [funcDeclNames_mapIdx_assume] at hn
           repeat rw [funcDeclNames_havoc_block] at hn
           simp only [List.append_nil, List.nil_append, List.mem_append,
             Stmt.funcDeclNames, Block.funcDeclNames, List.not_mem_nil,
             false_or, or_false] at hn
           first
             | exact hn
             | (rcases hn with h1 | h1 <;> exact h1)
             | (rcases hn with h1 | h1 | h1 <;> exact h1)))))

-- The transform's `stmtResult` doesn't introduce new funcDecls: every
-- `funcDeclName` in the output was already a `funcDeclName` of the source.
mutual
private theorem funcDeclNames_stmtResult_subset
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s) (n : Expression.Ident)
    (hn : n ∈ Stmt.funcDeclNames (stmtResult σ s)) :
    n ∈ Stmt.funcDeclNames s := by
  match s with
  | .cmd c => rw [stmtResult_cmd] at hn; exact hn
  | .exit l md => rw [stmtResult_exit] at hn; exact hn
  | .funcDecl d md => rw [stmtResult_funcDecl] at hn; exact hn
  | .typeDecl tc md => rw [stmtResult_typeDecl] at hn; exact hn
  | .block l bss md =>
    rw [stmtResult_block (hok := hok)] at hn
    have hn' : n ∈ Block.funcDeclNames (blockResult σ bss) := by
      simpa [Stmt.funcDeclNames] using hn
    have := funcDeclNames_blockResult_subset σ bss (stmtOk_block_inner hok) n hn'
    simpa [Stmt.funcDeclNames] using this
  | .ite c tss ess md =>
    rw [stmtResult_ite (hok := hok)] at hn
    have hn' : n ∈ Block.funcDeclNames (blockResult σ tss) ++
                  Block.funcDeclNames (blockResult (blockPostState σ tss) ess) := by
      simpa [Stmt.funcDeclNames] using hn
    rcases List.mem_append.mp hn' with h | h
    · have := funcDeclNames_blockResult_subset σ tss (stmtOk_ite_left hok) n h
      simpa [Stmt.funcDeclNames] using List.mem_append_left _ this
    · have := funcDeclNames_blockResult_subset (blockPostState σ tss) ess
                (stmtOk_ite_right hok) n h
      simpa [Stmt.funcDeclNames] using List.mem_append_right _ this
  | .loop guard measure inv body md =>
    have h := funcDeclNames_stmtResult_loop_subset σ guard measure inv body md hok n hn
    simpa [Stmt.funcDeclNames] using h

private theorem funcDeclNames_blockResult_subset
    (σ : LoopElimState) (bss : Statements) (hok : blockOk σ bss)
    (n : Expression.Ident)
    (hn : n ∈ Block.funcDeclNames (blockResult σ bss)) :
    n ∈ Block.funcDeclNames bss := by
  match bss with
  | [] => rw [blockResult_nil] at hn; simp [Block.funcDeclNames] at hn
  | s :: rest =>
    rw [blockResult_cons (hok := hok)] at hn
    have hn' : n ∈ Stmt.funcDeclNames (stmtResult σ s) ++
                   Block.funcDeclNames (blockResult (stmtPostState σ s) rest) := by
      simpa [Block.funcDeclNames] using hn
    rcases List.mem_append.mp hn' with h | h
    · have := funcDeclNames_stmtResult_subset σ s (blockOk_cons_left hok) n h
      simpa [Block.funcDeclNames] using List.mem_append_left _ this
    · have := funcDeclNames_blockResult_subset (stmtPostState σ s) rest
                (blockOk_cons_right hok) n h
      simpa [Block.funcDeclNames] using List.mem_append_right _ this
end

/-! ## Helpers for `mem_touchedVars_stmtResult` -/

/-- The loop case of `definedVars_subset_stmtResult`.  Mirrors
    `mem_definedVars_stmtResult_loop`'s structural unfolding pattern but in
    the *converse* direction. -/
private theorem definedVars_subset_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (n : Expression.Ident)
    (hn : n ∈ Block.definedVars body false) :
    n ∈ Stmt.definedVars (stmtResult σ (.loop guard measure inv body md)) false := by
  suffices h_suff :
    ∃ (loop_num : String) (s' : Statement),
      stmtResult σ (.loop guard measure inv body md) = s' ∧
      ∀ m, m ∈ Block.definedVars body false → m ∈ Stmt.definedVars s' false by
    obtain ⟨_, s', hs'_eq, hs'_prop⟩ := h_suff
    rw [hs'_eq]
    exact hs'_prop n hn
  change ∃ (loop_num : String) (s' : Statement),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s'') => s'' | .error _ => default) = s' ∧
    ∀ m, m ∈ Block.definedVars body false → m ∈ Stmt.definedVars s' false
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    repeat (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
              block_definedVars_append false, List.append_nil]
            repeat rw [definedVars_havoc_map]
            repeat rw [definedVars_mapIdx_assert]
            repeat rw [definedVars_mapIdx_assume]
            simp only [HasVarsImp.definedVars,
              HasPassiveCmds.assert, HasPassiveCmds.assume,
              HasInit.init, HasIdent.ident,
              Command.definedVars, Cmd.definedVars,
              List.append_nil, List.nil_append, List.mem_append,
              List.not_mem_nil, List.mem_singleton, false_or, or_false]
            first
              | exact hm
              | exact .inl hm
              | exact .inr hm
              | exact .inl (.inl hm)
              | exact .inl (.inr hm)
              | exact .inr (.inl hm)
              | exact .inr (.inr hm)
              | exact .inl (.inl (.inl hm))
              | exact .inl (.inl (.inr hm))
              | exact .inl (.inr (.inl hm))
              | exact .inl (.inr (.inr hm))
              | exact .inr (.inl (.inl hm))
              | exact .inr (.inl (.inr hm))
              | exact .inr (.inr (.inl hm))
              | exact .inr (.inr (.inr hm))⟩)
      | contradiction
      | (split at h; skip))
    -- Close residual goal: the `.det g, some m` case where `h` still has
    -- `StateT.pure ... .bind ...` wrapping the freshness check.
    all_goals (first | contradiction | (
      unfold StateT.pure at h
      dsimp only [StateT.bind, StateT.map, ExceptT.bindCont, ExceptT.bind,
        ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
        Functor.map, MonadState.modifyGet, StateT.modifyGet,
        MonadStateOf.modifyGet, bumpStat, modify, genLoopNum] at h
      repeat (first
        | (cases h; exact
            ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
              simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
                block_definedVars_append false, List.append_nil]
              repeat rw [definedVars_havoc_map]
              repeat rw [definedVars_mapIdx_assert]
              repeat rw [definedVars_mapIdx_assume]
              simp only [HasVarsImp.definedVars,
                HasPassiveCmds.assert, HasPassiveCmds.assume,
                HasInit.init, HasIdent.ident,
                Command.definedVars, Cmd.definedVars,
                List.append_nil, List.nil_append, List.mem_append,
                List.not_mem_nil, List.mem_singleton, false_or, or_false]
              first
                | exact hm
                | exact .inl hm
                | exact .inr hm
                | exact .inl (.inl hm)
                | exact .inl (.inr hm)
                | exact .inr (.inl hm)
                | exact .inr (.inr hm)
                | exact .inl (.inl (.inl hm))
                | exact .inl (.inl (.inr hm))
                | exact .inl (.inr (.inl hm))
                | exact .inl (.inr (.inr hm))
                | exact .inr (.inl (.inl hm))
                | exact .inr (.inl (.inr hm))
                | exact .inr (.inr (.inl hm))
                | exact .inr (.inr (.inr hm))⟩)
        | contradiction
        | (split at h; skip))
      all_goals (first | contradiction | (
        obtain ⟨_, rfl⟩ := h
        exact ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
          simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
            block_definedVars_append (ex := Bool.false), List.append_nil]
          repeat rw [definedVars_havoc_map]
          repeat rw [definedVars_mapIdx_assert]
          repeat rw [definedVars_mapIdx_assume]
          simp only [HasVarsImp.definedVars,
            HasPassiveCmds.assert, HasPassiveCmds.assume,
            HasInit.init, HasIdent.ident,
            Command.definedVars, Cmd.definedVars,
            List.append_nil, List.nil_append, List.mem_append,
            List.not_mem_nil, List.mem_singleton, false_or, or_false]
          first
            | exact hm
            | exact .inl hm
            | exact .inr hm
            | exact .inl (.inl hm)
            | exact .inl (.inr hm)
            | exact .inr (.inl hm)
            | exact .inr (.inr hm)
            | exact .inl (.inl (.inl hm))
            | exact .inl (.inl (.inr hm))
            | exact .inl (.inr (.inl hm))
            | exact .inl (.inr (.inr hm))
            | exact .inr (.inl (.inl hm))
            | exact .inr (.inl (.inr hm))
            | exact .inr (.inr (.inl hm))
            | exact .inr (.inr (.inr hm))⟩))))

-- The transform preserves `definedVars` (the source's defined vars are a
-- subset of the transform's defined vars), assuming the transform succeeds.
mutual
private theorem definedVars_subset_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars s false) :
    n ∈ Stmt.definedVars (stmtResult σ s) false := by
  match s with
  | .cmd c => rw [stmtResult_cmd]; exact hn
  | .exit l md => rw [stmtResult_exit]; exact hn
  | .funcDecl d md => rw [stmtResult_funcDecl]; exact hn
  | .typeDecl tc md => rw [stmtResult_typeDecl]; exact hn
  | .block l bss md =>
    rw [stmtResult_block (hok := hok)]
    simp only [Stmt.definedVars]
    have h : n ∈ Block.definedVars bss false := by simpa [Stmt.definedVars] using hn
    exact definedVars_subset_blockResult σ bss (stmtOk_block_inner hok) n h
  | .ite c tss ess md =>
    rw [stmtResult_ite (hok := hok)]
    simp only [Stmt.definedVars]
    have h : n ∈ Block.definedVars tss false ++ Block.definedVars ess false := by
      simpa [Stmt.definedVars] using hn
    rcases List.mem_append.mp h with ht | he
    · exact List.mem_append_left _
        (definedVars_subset_blockResult σ tss (stmtOk_ite_left hok) n ht)
    · exact List.mem_append_right _
        (definedVars_subset_blockResult (blockPostState σ tss) ess
          (stmtOk_ite_right hok) n he)
  | .loop guard measure inv body md =>
    have h : n ∈ Block.definedVars body false := by simpa [Stmt.definedVars] using hn
    exact definedVars_subset_stmtResult_loop σ guard measure inv body md hok n h

private theorem definedVars_subset_blockResult
    (σ : LoopElimState) (ss : Statements) (hok : blockOk σ ss)
    (n : Expression.Ident)
    (hn : n ∈ Block.definedVars ss false) :
    n ∈ Block.definedVars (blockResult σ ss) false := by
  match ss with
  | [] => exact hn
  | s :: rest =>
    rw [blockResult_cons (hok := hok)]
    simp only [Block.definedVars]
    have h : n ∈ Stmt.definedVars s false ++ Block.definedVars rest false := by
      simpa [Block.definedVars] using hn
    rcases List.mem_append.mp h with hs | hr
    · exact List.mem_append_left _
        (definedVars_subset_stmtResult σ s (blockOk_cons_left hok) n hs)
    · exact List.mem_append_right _
        (definedVars_subset_blockResult (stmtPostState σ s) rest
          (blockOk_cons_right hok) n hr)
end

/-! ### Focused lemmas about each loop-elim builder.

These lemmas characterize the modified/defined/get vars of each builder,
making it possible to prove memberships about the loop-elim output by
composing piece-wise facts rather than running through a giant `dsimp`
+ `cases h` chain. -/

/-- `Block.modifiedVars` of inv-assumes is empty. -/
private theorem getVars_boolNotFunc_opExpr_eq_nil :
    Lambda.LExpr.LExpr.getVars
      (T := Core.CoreLParams.mono)
      (@Lambda.boolNotFunc Core.CoreLParams).opExpr = [] := rfl

/-- Membership in `getVars (HasNot.not g)` implies membership in `getVars g`,
    for the Core.Expression.  This handles every shape of `g` since the
    `HasNot.not` instance only matches `boolConst true`/`boolConst false`
    explicitly and falls through to a `boolNotFunc` application otherwise. -/
private theorem mem_getVars_not_subset
    {g : Core.Expression.Expr} {m : Core.Expression.Ident}
    (hm : m ∈ Lambda.LExpr.LExpr.getVars (HasNot.not g)) :
    m ∈ Lambda.LExpr.LExpr.getVars g := by
  match g, hm with
  | .const _ (.boolConst Bool.true), hm =>
      simp [Lambda.LExpr.LExpr.getVars] at hm
  | .const _ (.boolConst Bool.false), hm =>
      simp [Lambda.LExpr.LExpr.getVars] at hm
  | .const _ (.intConst _), hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .const _ (.strConst _), hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .const _ (.realConst _), hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .const _ (.bitvecConst _ _), hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .op _ _ _, hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .bvar _ _, hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .fvar md₁ name ty, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.fvar md₁ name ty)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars, hm]
  | .abs md₁ pn ty body, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.abs md₁ pn ty body)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm
  | .quant md₁ k pn ty tr body, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.quant md₁ k pn ty tr body)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm
  | .app md₁ f e, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.app md₁ f e)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm
  | .ite md₁ c t e, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.ite md₁ c t e)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm
  | .eq md₁ e1 e2, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.eq md₁ e1 e2)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm

/-- `getVars (HasIntOrder.lt a b)` decomposes into `getVars a` ∪ `getVars b`
    (since `HasIntOrder.lt a b = .app () (.app () Core.intLtOp a) b`). -/
private theorem mem_getVars_lt_split
    {a b : Core.Expression.Expr} {m : Core.Expression.Ident}
    (hm : m ∈ Lambda.LExpr.LExpr.getVars
            (HasIntOrder.lt a b : Core.Expression.Expr)) :
    m ∈ Lambda.LExpr.LExpr.getVars a ∨ m ∈ Lambda.LExpr.LExpr.getVars b := by
  simp [Lambda.LExpr.LExpr.getVars, Core.intLtOp,
        Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr] at hm
  cases hm with
  | inl h => left; exact h
  | inr h => right; exact h

/-- `getVars` of the integer literal `0` is empty. -/
private theorem getVars_zero_eq_nil :
    Lambda.LExpr.LExpr.getVars (HasIntOrder.zero : Core.Expression.Expr) = [] := by
  simp [Lambda.LExpr.LExpr.getVars]

/-- `getVars (HasFvar.mkFvar v) = [v]`. -/
private theorem getVars_mkFvar_eq
    (v : Core.Expression.Ident) :
    Lambda.LExpr.LExpr.getVars
      (HasFvar.mkFvar v : Core.Expression.Expr) = [v] := by
  simp [Lambda.LExpr.LExpr.getVars]

/-- Helper for `mem_touchedVars_stmtResult_loop`'s residual abstract-`s'`
    branch.  Given the un-dsimp'd `h : (stmtRun σ ...).fst = .ok (b, s')`,
    we can derive `s' = .block ll [.block fil fib {}, .ite guard tb [] {}] {}`
    via `stmtResult_loop_struct` and then dispatch `m ∈ Stmt.touchedVars s'`
    to one of the source-touched pieces or the output-defined `m_old` name. -/
private theorem mem_touchedVars_stmtResult_loop_aux
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (b : Bool) (s' : Statement)
    (h : (stmtRun σ (.loop guard measure inv body md)).fst = .ok (b, s'))
    (m : Expression.Ident)
    (hm : m ∈ Stmt.touchedVars s') :
    m ∈ Stmt.definedVars s' false ∨
    m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
  dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase,
    buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes,
    buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants,
    buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants,
    buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome,
    hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
    bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
    ExceptT.lift, StateT.bind, StateT.pure,
    Functor.map, liftM, monadLift, MonadLift.monadLift,
    modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
    genLoopNum, bumpStat] at h
  repeat (first
    | (cases h
       simp only [Stmt.touchedVars, Block.touchedVars,
         Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
         Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
         block_modifiedOrDefinedVars_append, block_modifiedVars_append, block_getVars_append, block_definedVars_append,
         Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
         List.append_nil, List.nil_append,
         List.mem_append, List.not_mem_nil, List.mem_singleton,
         false_or, or_false] at hm ⊢
       repeat rw [modifiedOrDefinedVars_havoc_map'] at hm
       repeat rw [modifiedVars_havoc_map'] at hm
       repeat rw [getVars_havoc_map'] at hm
       repeat rw [definedVars_havoc_map'] at hm
       repeat rw [modifiedOrDefinedVars_mapIdx_assert'] at hm
       repeat rw [modifiedVars_mapIdx_assert'] at hm
       repeat rw [getVars_mapIdx_assert'] at hm
       repeat rw [definedVars_mapIdx_assert'] at hm
       repeat rw [modifiedOrDefinedVars_mapIdx_assume'] at hm
       repeat rw [modifiedVars_mapIdx_assume'] at hm
       repeat rw [getVars_mapIdx_assume'] at hm
       repeat rw [definedVars_mapIdx_assume'] at hm
       repeat rw [modifiedOrDefinedVars_havoc_map']
       repeat rw [modifiedVars_havoc_map']
       repeat rw [getVars_havoc_map']
       repeat rw [definedVars_havoc_map']
       repeat rw [modifiedOrDefinedVars_mapIdx_assert']
       repeat rw [modifiedVars_mapIdx_assert']
       repeat rw [getVars_mapIdx_assert']
       repeat rw [definedVars_mapIdx_assert']
       repeat rw [modifiedOrDefinedVars_mapIdx_assume']
       repeat rw [modifiedVars_mapIdx_assume']
       repeat rw [getVars_mapIdx_assume']
       repeat rw [definedVars_mapIdx_assume']
       simp only [HasVarsImp.definedVars, HasVarsImp.modifiedVars,
         HasVarsPure.getVars,
         HasPassiveCmds.assert, HasPassiveCmds.assume,
         HasInit.init, HasIdent.ident, HasHavoc.havoc,
         Command.definedVars, Command.modifiedVars, Command.getVars,
         Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
         ExprOrNondet.getVars,
         List.append_nil, List.nil_append,
         List.mem_append, List.not_mem_nil, List.mem_singleton,
         false_or, or_false] at hm ⊢
       try simp only [List.mem_filter, decide_eq_true_eq] at hm
       repeat first
         | exact .inr (Or.inl hm)
         | exact .inr (Or.inr hm)
         | exact .inr (Or.inl (Or.inl hm))
         | exact .inr (Or.inl (Or.inr hm))
         | exact .inr (Or.inr (Or.inl hm))
         | exact .inr (Or.inr (Or.inr hm))
         | exact .inl hm
         | exact .inl (Or.inl hm)
         | exact .inl (Or.inr hm)
         | exact .inl (Or.inl (Or.inl hm))
         | exact .inl (Or.inr (Or.inl hm))
         | exact .inl (Or.inr (Or.inr hm))
         | (rcases hm with hm | hm)
         | (subst hm; exact .inl (by simp [Stmt.definedVars, Block.definedVars,
             block_definedVars_append, definedVars_havoc_map,
             definedVars_mapIdx_assert, definedVars_mapIdx_assume,
             HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
             Command.definedVars, Cmd.definedVars]))
         | exact absurd hm (List.not_mem_nil _)
       done)
    | contradiction
    | (split at h; skip))
  -- Close residual goals (cases where h still has StateT.pure wrapping)
  all_goals (first | contradiction | (
    unfold StateT.pure at h
    dsimp only [StateT.bind, StateT.map, ExceptT.bindCont, ExceptT.bind,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
      Functor.map, MonadState.modifyGet, StateT.modifyGet,
      MonadStateOf.modifyGet, bumpStat, modify, genLoopNum] at h
    repeat (first
      | (cases h
         simp only [Stmt.touchedVars, Block.touchedVars,
           Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
           Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
           block_modifiedOrDefinedVars_append, block_modifiedVars_append, block_getVars_append, block_definedVars_append,
           Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
           List.append_nil, List.nil_append,
           List.mem_append, List.not_mem_nil, List.mem_singleton,
           false_or, or_false] at hm ⊢
         repeat rw [modifiedOrDefinedVars_havoc_map'] at hm
         repeat rw [modifiedVars_havoc_map'] at hm
         repeat rw [getVars_havoc_map'] at hm
         repeat rw [definedVars_havoc_map'] at hm
         repeat rw [modifiedOrDefinedVars_mapIdx_assert'] at hm
         repeat rw [modifiedVars_mapIdx_assert'] at hm
         repeat rw [getVars_mapIdx_assert'] at hm
         repeat rw [definedVars_mapIdx_assert'] at hm
         repeat rw [modifiedOrDefinedVars_mapIdx_assume'] at hm
         repeat rw [modifiedVars_mapIdx_assume'] at hm
         repeat rw [getVars_mapIdx_assume'] at hm
         repeat rw [definedVars_mapIdx_assume'] at hm
         repeat rw [modifiedOrDefinedVars_havoc_map']
         repeat rw [modifiedVars_havoc_map']
         repeat rw [getVars_havoc_map']
         repeat rw [definedVars_havoc_map']
         repeat rw [modifiedOrDefinedVars_mapIdx_assert']
         repeat rw [modifiedVars_mapIdx_assert']
         repeat rw [getVars_mapIdx_assert']
         repeat rw [definedVars_mapIdx_assert']
         repeat rw [modifiedOrDefinedVars_mapIdx_assume']
         repeat rw [modifiedVars_mapIdx_assume']
         repeat rw [getVars_mapIdx_assume']
         repeat rw [definedVars_mapIdx_assume']
         simp only [HasVarsImp.definedVars, HasVarsImp.modifiedVars, HasVarsPure.getVars,
           HasPassiveCmds.assert, HasPassiveCmds.assume,
           HasInit.init, HasIdent.ident, HasHavoc.havoc,
           Command.definedVars, Command.modifiedVars, Command.getVars,
           Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
           ExprOrNondet.getVars,
           List.append_nil, List.nil_append, List.mem_append, List.not_mem_nil,
           List.mem_singleton, false_or, or_false] at hm ⊢
         try simp only [List.mem_filter, decide_eq_true_eq] at hm
         repeat first
           | exact .inr (Or.inl hm)
           | exact .inr (Or.inr hm)
           | exact .inr (Or.inl (Or.inl hm))
           | exact .inr (Or.inl (Or.inr hm))
           | exact .inr (Or.inr (Or.inl hm))
           | exact .inr (Or.inr (Or.inr hm))
           | exact .inl hm
           | exact .inl (Or.inl hm)
           | exact .inl (Or.inr hm)
           | exact .inl (Or.inl (Or.inl hm))
           | exact .inl (Or.inr (Or.inl hm))
           | exact .inl (Or.inr (Or.inr hm))
           | (rcases hm with hm | hm)
           | (subst hm; exact .inl (by simp [Stmt.definedVars, Block.definedVars,
               block_definedVars_append, definedVars_havoc_map,
               definedVars_mapIdx_assert, definedVars_mapIdx_assume,
               HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
               Command.definedVars, Cmd.definedVars]))
           | exact absurd hm (List.not_mem_nil _)
         done)
      | contradiction
      | (split at h; skip))))
  -- Third level: handle cases via obtain ⟨_, rfl⟩ := h
  all_goals (first | contradiction | (
    obtain ⟨_, rfl⟩ := h
    simp only [Stmt.touchedVars, Block.touchedVars,
      Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
      Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
      block_modifiedOrDefinedVars_append, block_modifiedVars_append, block_getVars_append, block_definedVars_append,
      Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
      List.append_nil, List.nil_append, List.mem_append, List.not_mem_nil,
      List.mem_singleton, false_or, or_false] at hm ⊢
    -- Use unprimed lemmas here (HasPassiveCmds.assert form preserved)
    repeat rw [modifiedOrDefinedVars_havoc_map] at hm
    repeat rw [modifiedVars_havoc_map] at hm
    repeat rw [getVars_havoc_map] at hm
    repeat rw [definedVars_havoc_map] at hm
    repeat rw [modifiedOrDefinedVars_mapIdx_assert] at hm
    repeat rw [modifiedVars_mapIdx_assert] at hm
    repeat rw [getVars_mapIdx_assert] at hm
    repeat rw [definedVars_mapIdx_assert] at hm
    repeat rw [modifiedOrDefinedVars_mapIdx_assume] at hm
    repeat rw [modifiedVars_mapIdx_assume] at hm
    repeat rw [getVars_mapIdx_assume] at hm
    repeat rw [definedVars_mapIdx_assume] at hm
    repeat rw [modifiedOrDefinedVars_havoc_map]
    repeat rw [modifiedVars_havoc_map]
    repeat rw [getVars_havoc_map]
    repeat rw [definedVars_havoc_map]
    repeat rw [modifiedOrDefinedVars_mapIdx_assert]
    repeat rw [modifiedVars_mapIdx_assert]
    repeat rw [getVars_mapIdx_assert]
    repeat rw [definedVars_mapIdx_assert]
    repeat rw [modifiedOrDefinedVars_mapIdx_assume]
    repeat rw [modifiedVars_mapIdx_assume]
    repeat rw [getVars_mapIdx_assume]
    repeat rw [definedVars_mapIdx_assume]
    simp only [HasVarsImp.definedVars, HasVarsImp.modifiedVars, HasVarsPure.getVars,
      HasPassiveCmds.assert, HasPassiveCmds.assume,
      HasInit.init, HasIdent.ident, HasHavoc.havoc,
      Command.definedVars, Command.modifiedVars, Command.getVars,
      Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
      ExprOrNondet.getVars,
      List.append_nil, List.nil_append, List.mem_append, List.not_mem_nil,
      List.mem_singleton, false_or, or_false] at hm ⊢
    try simp only [List.mem_filter, decide_eq_true_eq] at hm
    repeat first
      | exact .inr (Or.inl hm)
      | exact .inr (Or.inr hm)
      | exact .inr (Or.inl (Or.inl hm))
      | exact .inr (Or.inl (Or.inr hm))
      | exact .inr (Or.inr (Or.inl hm))
      | exact .inr (Or.inr (Or.inr hm))
      | exact .inl hm
      | exact .inl (Or.inl hm)
      | exact .inl (Or.inr hm)
      | exact .inl (Or.inl (Or.inl hm))
      | exact .inl (Or.inr (Or.inl hm))
      | exact .inl (Or.inr (Or.inr hm))
      | exact .inr (Or.inr (Or.inl (Or.inl hm)))
      | exact .inr (Or.inr (Or.inl (Or.inr hm)))
      | exact .inr (Or.inr (Or.inr (Or.inl hm)))
      | exact .inr (Or.inr (Or.inr (Or.inr hm)))
      | exact .inr (Or.inl (Or.inl (Or.inl hm)))
      | exact .inr (Or.inl (Or.inl (Or.inr hm)))
      | exact .inr (Or.inl (Or.inr (Or.inl hm)))
      | exact .inr (Or.inl (Or.inr (Or.inr hm)))
      | exact .inr (Or.inr (Or.inl (Or.inl (Or.inl hm))))
      | exact .inr (Or.inr (Or.inl (Or.inl (Or.inr hm))))
      | exact .inr (Or.inr (Or.inl (Or.inr (Or.inl hm))))
      | exact .inr (Or.inr (Or.inl (Or.inr (Or.inr hm))))
      | exact .inr (Or.inr (Or.inr (Or.inl (Or.inl hm))))
      | exact .inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
      | (rcases hm with hm | hm)
      | (obtain ⟨hm, _⟩ := hm)
      | (subst hm; exact .inl (by simp [Stmt.definedVars, Block.definedVars,
          block_definedVars_append, definedVars_havoc_map,
          definedVars_mapIdx_assert, definedVars_mapIdx_assume,
          HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
          Command.definedVars, Cmd.definedVars]))
      | exact absurd hm (List.not_mem_nil _)))
  -- Residual cases: 8 goals where `hm` mentions `HasNot.not`,
  -- `HasIntOrder.lt … (HasFvar.mkFvar …)`, `HasIntOrder.zero`, the
  -- `loop_measure_var` head, or `List.flatMap (fun lp => getVars lp.snd) inv`,
  -- which the previous scaffold's simp set doesn't handle.
  all_goals (first | contradiction | (
    -- Reduce `getVars (HasNot.not g)` to `getVars g`.
    try (replace hm := mem_getVars_not_subset hm)
    try (rcases hm with hm | hm
         <;> first
           | exact .inr (.inr (.inl (.inl (.inl
               (mem_getVars_not_subset hm)))))
           | exact .inr (.inr (.inl (.inr hm)))
           | exact .inr (.inr (.inl (.inl (.inl hm))))
           | exact .inr (.inr (.inr hm)))
    -- Now `hm` should match one of the source-touched pieces:
    --   * `m ∈ getVars g✝`               → into the `getVars` slot
    --   * `m ∈ flatMap getVars inv`       → into the `inv` slot
    --   * `m ∈ Block.getVars body`        → into the rightmost slot
    --   * `m ∈ getVars (HasIntOrder.lt …)`→ split via `mem_getVars_lt_split`
    -- The measure-variable `head` goal has no `hm` and is closed by
    -- `Or.inl (Or.inl rfl)` after the substitution.
    -- The `tail` goal with `getVars zero = []` is contradictory.
    first
      | exact .inr (.inr (.inl (.inl (.inl hm))))
      | exact .inr (.inr (.inl (.inr hm)))
      | exact .inr (.inr (.inr hm))
      | (rcases mem_getVars_lt_split hm with h₁ | h₂
         · refine .inr (.inr (.inl (.inl (.inr ?_))))
           simp [Option.map_some]
           exact h₁
         · simp [getVars_mkFvar_eq] at h₂
           exact .inl (.inl h₂))
      | exact .inl (.inl rfl)
      | (try simp [getVars_zero_eq_nil] at *)))

/-- The loop case of `mem_touchedVars_stmtResult`. -/
private theorem mem_touchedVars_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (n : Expression.Ident)
    (hn : n ∈ Stmt.touchedVars (stmtResult σ (.loop guard measure inv body md)))
    (hnd : n ∉ Stmt.definedVars (stmtResult σ (.loop guard measure inv body md)) false) :
    n ∈ Stmt.touchedVars (.loop guard measure inv body md) ∧
    n ∉ Stmt.definedVars (.loop guard measure inv body md) false := by
  -- The source's `definedVars` ⊆ transform's `definedVars`; combined with
  -- `hnd` we conclude the second component immediately.
  have hnd_src : n ∉ Stmt.definedVars (.loop guard measure inv body md) false := fun h =>
    hnd (definedVars_subset_stmtResult_loop σ guard measure inv body md hok n (by simpa [Stmt.definedVars] using h))
  refine ⟨?_, hnd_src⟩
  -- Suffices: the transform output equals some `s'` such that every `m` in
  -- its `touchedVars` lies in either its `definedVars` (then `hnd` rules it
  -- out) or in source's `touchedVars`.
  suffices h_suff :
    ∃ (loop_num : String) (s' : Statement),
      stmtResult σ (.loop guard measure inv body md) = s' ∧
      ∀ m, m ∈ Stmt.touchedVars s' →
        m ∈ Stmt.definedVars s' false ∨
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) by
    obtain ⟨_, s', hs'_eq, hs'_prop⟩ := h_suff
    rw [hs'_eq] at hn hnd
    rcases hs'_prop n hn with hdef | hsrc
    · exact absurd hdef hnd
    · exact hsrc
  -- Prove the suffices via the dsimp+structural-cases pattern.
  change ∃ (loop_num : String) (s' : Statement),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s'') => s'' | .error _ => default) = s' ∧
    ∀ m, m ∈ Stmt.touchedVars s' →
      m ∈ Stmt.definedVars s' false ∨
      m ∈ Stmt.touchedVars (.loop guard measure inv body md)
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    -- Save the un-dsimp'd `h` so the aux lemma can use it without the
    -- `StringGenState.gen` opacity issue that prevents Lean from coercing
    -- the dsimp'd LHS back to `(stmtRun σ ...).fst`.
    have h_orig : (stmtRun σ (.loop guard measure inv body md)).fst
                  = .ok (b, s') := h
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat,
      Except.bind, Except.pure, Except.map] at h
    -- Inline per-case proof.
    --
    -- Key auxiliary facts:
    -- (1) `assigned_vars ⊆ Block.modifiedVars body ⊆ Stmt.modifiedOrDefinedVars (.loop ...)`.
    -- (2) `m_old_ident ∈ Stmt.definedVars (concrete)` (when measure = some _).
    -- (3) `Block.modifiedOrDefinedVars body ⊆ Stmt.modifiedOrDefinedVars (.loop ...)`.
    -- (4) `Block.getVars body ⊆ Stmt.getVars (.loop ...)`.
    -- (5) Same for `guard.getVars`, `(measure.map getVars).getD []`,
    --     `inv.flatMap (fun lp => HasVarsPure.getVars lp.2)`.
    --
    -- Helper: if `m` lies in source's `touchedVars`, that suffices.
    -- We pre-build closures for each "way of landing in source".
    have body_mod_to_src : ∀ m, m ∈ Block.modifiedVars body →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
        Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil, List.mem_append]
      exact Or.inl hm
    -- Note: `Block.definedVars body false` is NOT in `Stmt.touchedVars (.loop ..)`
    -- because touchedVars uses `excludeScoped=true`. Variables in
    -- `Block.definedVars body false` are routed to `.inl` (transform's definedVars)
    -- in the dispatch below, not to `.inr` (source touchedVars).
    have body_gv_to_src : ∀ m, m ∈ Block.getVars body →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_right
      show m ∈ guard.getVars ++ (measure.map HasVarsPure.getVars).getD [] ++
                (inv.flatMap fun lp => HasVarsPure.getVars lp.2) ++
                Block.getVars body
      exact List.mem_append_right _ hm
    have guard_to_src : ∀ m, m ∈ guard.getVars →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_right
      show m ∈ guard.getVars ++ (measure.map HasVarsPure.getVars).getD [] ++
                (inv.flatMap fun lp => HasVarsPure.getVars lp.2) ++
                Block.getVars body
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm))
    have measure_to_src : ∀ m, m ∈ (measure.map HasVarsPure.getVars).getD [] →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_right
      show m ∈ guard.getVars ++ (measure.map HasVarsPure.getVars).getD [] ++
                (inv.flatMap fun lp => HasVarsPure.getVars lp.2) ++
                Block.getVars body
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))
    have inv_to_src : ∀ m, m ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2) →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_right
      show m ∈ guard.getVars ++ (measure.map HasVarsPure.getVars).getD [] ++
                (inv.flatMap fun lp => HasVarsPure.getVars lp.2) ++
                Block.getVars body
      exact List.mem_append_left _ (List.mem_append_right _ hm)
    -- Specific consequences:
    -- For `measure = some m_e`, `HasVarsPure.getVars m_e ⊆ measure.map getVars`.
    have measure_some_to_src : ∀ (m_e : Expression.Expr) (m : Expression.Ident),
        measure = some m_e → m ∈ HasVarsPure.getVars m_e →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m_e m heq hm
      apply measure_to_src
      rw [heq]
      simp [Option.map, Option.getD]
      exact hm
    have guard_det_to_src : ∀ (g : Expression.Expr) (m : Expression.Ident),
        guard = .det g → m ∈ HasVarsPure.getVars g →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro g m heq hm
      apply guard_to_src
      rw [heq]
      show m ∈ HasVarsPure.getVars g
      exact hm
    repeat (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            have hm_orig := hm
            simp only [Stmt.touchedVars, Block.touchedVars,
              Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
              Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
              block_modifiedOrDefinedVars_append, block_getVars_append,
              block_definedVars_append,
              modifiedOrDefinedVars_havoc_map, getVars_havoc_map,
              definedVars_havoc_map,
              modifiedOrDefinedVars_mapIdx_assert, getVars_mapIdx_assert,
              definedVars_mapIdx_assert,
              modifiedOrDefinedVars_mapIdx_assume, getVars_mapIdx_assume,
              definedVars_mapIdx_assume,
              HasVarsImp.definedVars, HasVarsImp.modifiedVars,
              HasVarsPure.getVars,
              HasPassiveCmds.assert, HasPassiveCmds.assume,
              HasInit.init, HasIdent.ident, HasHavoc.havoc,
              Command.definedVars, Command.modifiedVars, Command.getVars,
              Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
              ExprOrNondet.getVars,
              Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
              List.append_nil, List.nil_append,
              List.mem_append, List.not_mem_nil, List.mem_singleton,
              false_or, or_false] at hm
            try simp only [List.mem_filter, decide_eq_true_eq] at hm
            -- Dispatch each disjunct of `hm` to the appropriate side.
            (repeat first
              | exact .inr (body_mod_to_src _ hm.1)
              | exact .inr (body_mod_to_src _ hm)
              | exact .inr (body_gv_to_src _ hm)
              | exact .inr (guard_to_src _ hm)
              | exact .inr (measure_to_src _ hm)
              | exact .inr (inv_to_src _ hm)
              | (rcases hm with hm | hm)
              | (refine .inl ?_
                 subst hm
                 simp [Stmt.definedVars, Block.definedVars, block_definedVars_append,
                   definedVars_havoc_map, definedVars_mapIdx_assert,
                   definedVars_mapIdx_assume,
                   HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
                   Command.definedVars, Cmd.definedVars])
              | (exact .inl (by
                   simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
                     Block.definedVars, block_definedVars_append,
                     definedVars_havoc_map, definedVars_mapIdx_assert,
                     definedVars_mapIdx_assume,
                     HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
                     Command.definedVars, Cmd.definedVars,
                     List.append_nil, List.nil_append, List.mem_append,
                     List.not_mem_nil, false_or, or_false]
                   first
                     | exact hm | exact .inl hm | exact .inr hm
                     | exact .inl (.inl hm) | exact .inl (.inr hm)
                     | exact .inr (.inl hm) | exact .inr (.inr hm)
                     | exact .inl (.inl (.inl hm)) | exact .inl (.inl (.inr hm))
                     | exact .inl (.inr (.inl hm)) | exact .inl (.inr (.inr hm))
                     | exact .inr (.inl (.inl hm)) | exact .inr (.inl (.inr hm))
                     | exact .inr (.inr (.inl hm)) | exact .inr (.inr (.inr hm))))
              | exact absurd hm (List.not_mem_nil _))
            -- Residual goal (abstract-`s'` branch).  Discharge via the
            -- factored aux lemma.
            all_goals
              exact mem_touchedVars_stmtResult_loop_aux σ guard measure inv body md
                hok b s' h_orig m hm_orig⟩)
      | contradiction
      | (split at h; skip))
    all_goals (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.touchedVars, Block.touchedVars,
              Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
              Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
              block_modifiedOrDefinedVars_append, block_getVars_append,
              block_definedVars_append,
              modifiedOrDefinedVars_havoc_map, getVars_havoc_map,
              definedVars_havoc_map,
              modifiedOrDefinedVars_mapIdx_assert, getVars_mapIdx_assert,
              definedVars_mapIdx_assert,
              modifiedOrDefinedVars_mapIdx_assume, getVars_mapIdx_assume,
              definedVars_mapIdx_assume,
              HasVarsImp.definedVars, HasVarsImp.modifiedVars,
              HasVarsPure.getVars,
              HasPassiveCmds.assert, HasPassiveCmds.assume,
              HasInit.init, HasIdent.ident, HasHavoc.havoc,
              Command.definedVars, Command.modifiedVars, Command.getVars,
              Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
              ExprOrNondet.getVars,
              Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
              List.append_nil, List.nil_append,
              List.mem_append, List.not_mem_nil, List.mem_singleton,
              false_or, or_false] at hm
            try simp only [List.mem_filter, decide_eq_true_eq] at hm
            (repeat first
              | exact .inr (body_mod_to_src _ hm.1)
              | exact .inr (body_mod_to_src _ hm)
              | exact .inr (body_gv_to_src _ hm)
              | exact .inr (guard_to_src _ hm)
              | exact .inr (measure_to_src _ hm)
              | exact .inr (inv_to_src _ hm)
              | (rcases hm with hm | hm)
              | (refine .inl ?_
                 subst hm
                 simp [Stmt.definedVars, Block.definedVars, block_definedVars_append,
                   definedVars_havoc_map, definedVars_mapIdx_assert,
                   definedVars_mapIdx_assume,
                   HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
                   Command.definedVars, Cmd.definedVars])
              | (exact .inl (by
                   simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
                     Block.definedVars, block_definedVars_append,
                     definedVars_havoc_map, definedVars_mapIdx_assert,
                     definedVars_mapIdx_assume,
                     HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
                     Command.definedVars, Cmd.definedVars,
                     List.append_nil, List.nil_append, List.mem_append,
                     List.not_mem_nil, false_or, or_false]
                   first
                     | exact hm | exact .inl hm | exact .inr hm
                     | exact .inl (.inl hm) | exact .inl (.inr hm)
                     | exact .inr (.inl hm) | exact .inr (.inr hm)
                     | exact .inl (.inl (.inl hm)) | exact .inl (.inl (.inr hm))
                     | exact .inl (.inr (.inl hm)) | exact .inl (.inr (.inr hm))
                     | exact .inr (.inl (.inl hm)) | exact .inr (.inl (.inr hm))
                     | exact .inr (.inr (.inl hm)) | exact .inr (.inr (.inr hm))))
              | exact absurd hm (List.not_mem_nil _))
            done⟩)
      | contradiction)

-- Every name in the transform's `touchedVars` outside its `definedVars` was
-- already in the source's `touchedVars` outside source's `definedVars`.
mutual
private theorem mem_touchedVars_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (n : Expression.Ident)
    (hn : n ∈ Stmt.touchedVars (stmtResult σ s))
    (hnd : n ∉ Stmt.definedVars (stmtResult σ s) false) :
    n ∈ Stmt.touchedVars s ∧ n ∉ Stmt.definedVars s false := by
  match s with
  | .cmd c =>
    rw [stmtResult_cmd] at hn hnd
    exact ⟨hn, hnd⟩
  | .exit l md =>
    rw [stmtResult_exit] at hn hnd
    exact ⟨hn, hnd⟩
  | .funcDecl d md =>
    rw [stmtResult_funcDecl] at hn hnd
    exact ⟨hn, hnd⟩
  | .typeDecl tc md =>
    rw [stmtResult_typeDecl] at hn hnd
    exact ⟨hn, hnd⟩
  | .block l bss md =>
    rw [stmtResult_block (hok := hok)] at hn hnd
    have hnd' : n ∉ Block.definedVars (blockResult σ bss) false := by
      simpa [Stmt.definedVars] using hnd
    have hn' : n ∈ Block.touchedVars (blockResult σ bss) := by
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
        Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil] at hn
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append]
      rcases List.mem_append.mp hn with hm | hg
      · exact Or.inl (Or.inl hm)
      · exact Or.inr hg
    have ⟨htv, hndef⟩ := mem_touchedVars_blockResult σ bss (stmtOk_block_inner hok) n hn' hnd'
    constructor
    · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
        Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil, List.mem_append]
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at htv
      rcases htv with (hm | hd) | hg
      · exact Or.inl hm
      · exact absurd (block_definedVars_true_subset_false bss n hd) hndef
      · exact Or.inr hg
    · simpa [Stmt.definedVars] using hndef
  | .ite c tss ess md =>
    rw [stmtResult_ite (hok := hok)] at hn hnd
    have hnd' : n ∉ Block.definedVars (blockResult σ tss) false ∧
                n ∉ Block.definedVars (blockResult (blockPostState σ tss) ess) false := by
      simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or] at hnd
      exact hnd
    have hnd_tss : n ∉ Block.definedVars tss false := fun h =>
      hnd'.1 (definedVars_subset_blockResult σ tss (stmtOk_ite_left hok) n h)
    have hnd_ess : n ∉ Block.definedVars ess false := fun h =>
      hnd'.2 (definedVars_subset_blockResult (blockPostState σ tss) ess (stmtOk_ite_right hok) n h)
    have hn' : n ∈ Stmt.touchedVars
        (.ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md) := hn
    simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
      Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil] at hn'
    -- hn' : n ∈ (Block.modifiedVars ... ++ Block.modifiedVars ...) ++ (c.getVars ++ ...)
    rcases List.mem_append.mp hn' with h_mod | h_gv
    · -- n in modifiedVars of one branch
      rcases List.mem_append.mp h_mod with h_t | h_e
      · -- n ∈ Block.modifiedVars (blockResult σ tss)
        have h_in : n ∈ Block.touchedVars (blockResult σ tss) :=
          List.mem_append_left _ (List.mem_append_left _ h_t)
        have ⟨hsrc, hndef_src⟩ :=
          mem_touchedVars_blockResult σ tss (stmtOk_ite_left hok) n h_in hnd'.1
        constructor
        · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
            Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
          simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
          rcases hsrc with (hm | hd) | hg
          · exact List.mem_append_left _ (List.mem_append_left _ hm)
          · exact absurd (block_definedVars_true_subset_false tss n hd) hndef_src
          · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hg))
        · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
          exact ⟨hndef_src, hnd_ess⟩
      · -- n ∈ Block.modifiedVars (blockResult (blockPostState σ tss) ess)
        have h_in : n ∈ Block.touchedVars (blockResult (blockPostState σ tss) ess) :=
          List.mem_append_left _ (List.mem_append_left _ h_e)
        have ⟨hsrc, hndef_src⟩ :=
          mem_touchedVars_blockResult (blockPostState σ tss) ess (stmtOk_ite_right hok) n h_in hnd'.2
        constructor
        · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
            Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
          simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
          rcases hsrc with (hm | hd) | hg
          · exact List.mem_append_left _ (List.mem_append_right _ hm)
          · exact absurd (block_definedVars_true_subset_false ess n hd) hndef_src
          · exact List.mem_append_right _ (List.mem_append_right _ hg)
        · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
          exact ⟨hnd_tss, hndef_src⟩
    · -- n in getVars (c.getVars ++ Block.getVars tss' ++ Block.getVars ess')
      rcases List.mem_append.mp h_gv with h_cgt | h_ge
      · rcases List.mem_append.mp h_cgt with h_c | h_gt
        · -- n ∈ ExprOrNondet.getVars c (condition is unchanged)
          constructor
          · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
              Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
            exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ h_c))
          · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
            exact ⟨hnd_tss, hnd_ess⟩
        · -- n ∈ Block.getVars (blockResult σ tss)
          have h_in : n ∈ Block.touchedVars (blockResult σ tss) :=
            List.mem_append_right _ h_gt
          have ⟨hsrc, hndef_src⟩ :=
            mem_touchedVars_blockResult σ tss (stmtOk_ite_left hok) n h_in hnd'.1
          constructor
          · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
              Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
            simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
            rcases hsrc with (hm | hd) | hg
            · exact List.mem_append_left _ (List.mem_append_left _ hm)
            · exact absurd (block_definedVars_true_subset_false tss n hd) hndef_src
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hg))
          · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
            exact ⟨hndef_src, hnd_ess⟩
      · -- n ∈ Block.getVars (blockResult (blockPostState σ tss) ess)
        have h_in : n ∈ Block.touchedVars (blockResult (blockPostState σ tss) ess) :=
          List.mem_append_right _ h_ge
        have ⟨hsrc, hndef_src⟩ :=
          mem_touchedVars_blockResult (blockPostState σ tss) ess (stmtOk_ite_right hok) n h_in hnd'.2
        constructor
        · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
            Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
          simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
          rcases hsrc with (hm | hd) | hg
          · exact List.mem_append_left _ (List.mem_append_right _ hm)
          · exact absurd (block_definedVars_true_subset_false ess n hd) hndef_src
          · exact List.mem_append_right _ (List.mem_append_right _ hg)
        · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
          exact ⟨hnd_tss, hndef_src⟩
  | .loop guard measure inv body md =>
    exact mem_touchedVars_stmtResult_loop σ guard measure inv body md hok n hn hnd

private theorem mem_touchedVars_blockResult
    (σ : LoopElimState) (bss : Statements) (hok : blockOk σ bss)
    (n : Expression.Ident)
    (hn : n ∈ Block.touchedVars (blockResult σ bss))
    (hnd : n ∉ Block.definedVars (blockResult σ bss) false) :
    n ∈ Block.touchedVars bss ∧ n ∉ Block.definedVars bss false := by
  match bss with
  | [] =>
    rw [blockResult_nil] at hn hnd
    refine ⟨?_, hnd⟩
    -- Block.touchedVars [] = [] ++ [] = [] → contradiction
    simp [Block.touchedVars, Block.modifiedOrDefinedVars, Block.getVars] at hn
  | s :: rest =>
    rw [blockResult_cons (hok := hok)] at hn hnd
    simp only [Block.touchedVars, Block.modifiedOrDefinedVars, Block.modifiedVars,
      Block.definedVars, Block.getVars, List.mem_append] at hn ⊢
    simp only [Block.definedVars, List.mem_append, not_or] at hnd ⊢
    obtain ⟨hnd_s, hnd_r⟩ := hnd
    have hnd_s_src : n ∉ Stmt.definedVars s false := fun h =>
      hnd_s (definedVars_subset_stmtResult σ s (blockOk_cons_left hok) n h)
    have hnd_r_src : n ∉ Block.definedVars rest false := fun h =>
      hnd_r (definedVars_subset_blockResult (stmtPostState σ s) rest (blockOk_cons_right hok) n h)
    rcases hn with ((hms | hmr) | (hds | hdr)) | (hgs | hgr)
    · -- n ∈ Stmt.modifiedVars (stmtResult σ s)
      have h_in : n ∈ Stmt.touchedVars (stmtResult σ s) := by
        simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append]
        exact Or.inl (Or.inl hms)
      have ⟨hsrc, hndef_s⟩ := mem_touchedVars_stmtResult σ s (blockOk_cons_left hok) n h_in hnd_s
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append] at hsrc
      refine ⟨?_, hndef_s, hnd_r_src⟩
      rcases hsrc with (hm | hd) | hg
      · exact Or.inl (Or.inl (Or.inl hm))
      · exact Or.inl (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inl hg)
    · -- n ∈ Block.modifiedVars (blockResult (stmtPostState σ s) rest)
      have h_in : n ∈ Block.touchedVars (blockResult (stmtPostState σ s) rest) := by
        simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append]
        exact Or.inl (Or.inl hmr)
      have ⟨hsrc, hndef_r⟩ :=
        mem_touchedVars_blockResult (stmtPostState σ s) rest (blockOk_cons_right hok) n h_in hnd_r
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
      refine ⟨?_, hnd_s_src, hndef_r⟩
      rcases hsrc with (hm | hd) | hg
      · exact Or.inl (Or.inl (Or.inr hm))
      · exact Or.inl (Or.inr (Or.inr hd))
      · exact Or.inr (Or.inr hg)
    · -- n ∈ Stmt.definedVars (stmtResult σ s) true → contradiction
      exact absurd (stmt_definedVars_true_subset_false (stmtResult σ s) n hds) hnd_s
    · -- n ∈ Block.definedVars (blockResult ...) true → contradiction
      exact absurd (block_definedVars_true_subset_false (blockResult (stmtPostState σ s) rest) n hdr) hnd_r
    · -- n ∈ Stmt.getVars (stmtResult σ s)
      have h_in : n ∈ Stmt.touchedVars (stmtResult σ s) := by
        simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append]
        exact Or.inr hgs
      have ⟨hsrc, hndef_s⟩ := mem_touchedVars_stmtResult σ s (blockOk_cons_left hok) n h_in hnd_s
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append] at hsrc
      refine ⟨?_, hndef_s, hnd_r_src⟩
      rcases hsrc with (hm | hd) | hg
      · exact Or.inl (Or.inl (Or.inl hm))
      · exact Or.inl (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inl hg)
    · -- n ∈ Block.getVars (blockResult (stmtPostState σ s) rest)
      have h_in : n ∈ Block.touchedVars (blockResult (stmtPostState σ s) rest) := by
        simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append]
        exact Or.inr hgr
      have ⟨hsrc, hndef_r⟩ :=
        mem_touchedVars_blockResult (stmtPostState σ s) rest (blockOk_cons_right hok) n h_in hnd_r
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
      refine ⟨?_, hnd_s_src, hndef_r⟩
      rcases hsrc with (hm | hd) | hg
      · exact Or.inl (Or.inl (Or.inr hm))
      · exact Or.inl (Or.inr (Or.inr hd))
      · exact Or.inr (Or.inr hg)
end

/-! ## `defUseWellFormed` preservation through `stmtResult` / `blockResult`

The output of the loop-elim transform is also `defUseWellFormed`.  This is
needed to discharge the `InitEnvWF.defUseOk` field on the output side of
`loopElim_overapproximatesAggressive`.

The proof is structural over the statement.  The non-loop cases reduce
trivially via the `stmtResult_*` / `blockResult_*` identity lemmas.  The
loop case is the only interesting one: we must verify well-formedness for
the produced wrapper

    block loop_label [first_iter_facts, ite guard (arb_facts :: exit_state) [] {}]

against `outer = (·.store).isSome`, given that the source `loop` body is
well-formed against the same `outer` and that the reserved `$__loop` prefix
is fresh in `outer` (via `BlockInitEnvWF.reservedFresh`).  The body itself is
unchanged by the transform — only the wrapper is fresh — so `outer_extend`
suffices for the body's well-formedness inside the encoding (extended by
`m_old`). -/

/-- `Stmt.definedVars (stmtResult σ s) true = Stmt.definedVars s true`.

    For non-loop cases this is straightforward (`stmtResult` is identity for
    cmd/exit/funcDecl/typeDecl, and `definedVars _ true = []` for compound).
    The loop case uses `stmtResult_loop_struct`, which says the loop's output
    is a block, hence `definedVars _ true = []`. -/
private theorem stmtResult_definedVars_true_eq
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s) :
    Stmt.definedVars (stmtResult σ s) true = Stmt.definedVars s true := by
  match s with
  | .cmd c => rw [stmtResult_cmd]
  | .exit l md => rw [stmtResult_exit]
  | .funcDecl d md => rw [stmtResult_funcDecl]
  | .typeDecl tc md => rw [stmtResult_typeDecl]
  | .block l bss md =>
    rw [stmtResult_block (hok := hok)]; simp [Stmt.definedVars]
  | .ite c tss ess md =>
    rw [stmtResult_ite (hok := hok)]; simp [Stmt.definedVars]
  | .loop guard measure inv body md =>
    have ⟨_, _, _, _, hs', _⟩ := stmtResult_loop_struct σ guard measure inv body md hok
    rw [hs']; simp [Stmt.definedVars]

/-! ### Piece-wise `defUseWellFormed` lemmas for loop-elim builders -/

/-- `defUseWellFormed` of a havoc-only command list: requires only that all
    havoc'd variables are in `outer`. -/
private theorem defUseWellFormed_havoc_map (outer : Expression.Ident → Bool)
    (xs : List Expression.Ident) (md : MetaData Expression)
    (hxs : ∀ n ∈ xs, outer n = Bool.true) :
    Block.defUseWellFormed (P := Expression) (C := Command)
      outer (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = Bool.true := by
  induction xs with
  | nil => simp [Block.defUseWellFormed]
  | cons x rest ih =>
    show Block.defUseWellFormed outer
      (Stmt.cmd (HasHavoc.havoc x md) :: rest.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = Bool.true
    apply defUseWellFormed_cons_intro
    · -- head: havoc x is well-formed since x ∈ outer.
      show Stmt.defUseWellFormed (P := Expression) (C := Command)
        outer (Stmt.cmd (HasHavoc.havoc x md)) = Bool.true
      simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasHavoc.havoc, Command.getVars, Command.modifiedVars,
        Command.definedVars, Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars,
        ExprOrNondet.getVars, List.all_nil, Bool.and_true, Bool.true_and]
      simp [List.all_cons, hxs x (.head _)]
    · -- tail: extending outer by [] (havoc doesn't add to definedVars true) — same as outer.
      have heq : (fun n => outer n || decide (n ∈
          Stmt.definedVars (P := Expression) (C := Command)
            (Stmt.cmd (HasHavoc.havoc x md)) true)) =
          outer := by
        funext n
        simp [Stmt.definedVars, HasVarsImp.definedVars, HasHavoc.havoc,
          Command.definedVars, Cmd.definedVars]
      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => congrFun heq n)]
      exact ih (fun n hn => hxs n (.tail _ hn))

/-- `defUseWellFormed` of a `mapIdx` of asserts: requires only that all
    `getVars` of the assert expressions are in `outer`. -/
private theorem defUseWellFormed_mapIdx_assert (outer : Expression.Ident → Bool)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String)
    (hgv : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2), outer n = Bool.true) :
    Block.defUseWellFormed (P := Expression) (C := Command) outer
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) = Bool.true := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.defUseWellFormed]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    apply defUseWellFormed_cons_intro
    · show Stmt.defUseWellFormed (P := Expression) (C := Command) outer
            (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md)) = Bool.true
      simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasPassiveCmds.assert, Command.getVars, Command.modifiedVars,
        Command.definedVars, Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars,
        List.all_nil, Bool.and_true, Bool.true_and]
      rw [List.all_eq_true]
      intro n hn
      apply hgv n
      simp only [List.flatMap_cons, List.mem_append]
      exact .inl hn
    · have heq : (fun n => outer n || decide (n ∈ Stmt.definedVars (P := Expression) (C := Command)
          (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md)) true)) = outer := by
        funext n
        simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assert,
          Command.definedVars, Cmd.definedVars]
      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => congrFun heq n)]
      exact ih (fun i le => label (i + 1) le) (fun n hn =>
        hgv n (by simp only [List.flatMap_cons, List.mem_append]; exact .inr hn))

/-- `defUseWellFormed` of a `mapIdx` of assumes: requires only that all
    `getVars` of the assume expressions are in `outer`. -/
private theorem defUseWellFormed_mapIdx_assume (outer : Expression.Ident → Bool)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String)
    (hgv : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2), outer n = Bool.true) :
    Block.defUseWellFormed (P := Expression) (C := Command) outer
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) = Bool.true := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.defUseWellFormed]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    apply defUseWellFormed_cons_intro
    · show Stmt.defUseWellFormed (P := Expression) (C := Command) outer
            (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md)) = Bool.true
      simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasPassiveCmds.assume, Command.getVars, Command.modifiedVars,
        Command.definedVars, Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars,
        List.all_nil, Bool.and_true, Bool.true_and]
      rw [List.all_eq_true]
      intro n hn
      apply hgv n
      simp only [List.flatMap_cons, List.mem_append]
      exact .inl hn
    · have heq : (fun n => outer n || decide (n ∈ Stmt.definedVars (P := Expression) (C := Command)
          (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md)) true)) = outer := by
        funext n
        simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assume,
          Command.definedVars, Cmd.definedVars]
      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => congrFun heq n)]
      exact ih (fun i le => label (i + 1) le) (fun n hn =>
        hgv n (by simp only [List.flatMap_cons, List.mem_append]; exact .inr hn))

/-! Auxiliary: `definedVars _ true = []` for the standard pieces. -/

private theorem definedVars_true_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.definedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) true = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.definedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md : Command)) true ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assert,
      Command.definedVars, Cmd.definedVars]

/-! ### Master helper for `defUseWellFormed` of `buildLoopOutput`.

    The transform produces
       block "loop_<n>" [first_iter_asserts, ite g (arb_facts :: exit_state) [] {}]
    where `arb_facts` and `exit_state` are themselves blocks containing the
    body, havoc, and various assert/assume pieces.

    Rather than write this proof inline four times (once per case of the
    guard×measure split), we factor it into a reusable helper that is
    parametric in `assumeGuard`, `pre`, `post`, `exit` (the parts that differ
    between the four cases).  The helper takes WF hypotheses for each piece
    and produces WF of the full output. -/

/-- The "havoc filter" subset of `Block.modifiedVars body` that is in `outer`.
    Given `defUseWellFormed outer body = true`, every var in
    `(Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body false)`
    is in `outer`. -/
private theorem havoc_filter_subset_outer
    (outer : Expression.Ident → Bool) (body : Statements)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true) :
    ∀ n ∈ ((Block.modifiedVars body).filter
            (fun v => decide ¬v ∈ Block.definedVars body Bool.false)),
      outer n = Bool.true := by
  intro n hn
  rw [List.mem_filter] at hn
  obtain ⟨hn_mod, hn_ndef⟩ := hn
  rw [decide_eq_true_eq] at hn_ndef
  exact defUseWellFormed_modGetVars_implies_outer h_body_wf (Or.inl hn_mod) hn_ndef

/-- The havoc block constructed from `body`'s modified-but-not-defined vars
    is `defUseWellFormed` against any `outer` that body is well-formed against. -/
private theorem defUseWellFormed_havoc_block
    (outer : Expression.Ident → Bool) (body : Statements)
    (md : MetaData Expression) (loop_num : String)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
        (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
          (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
            (Block.modifiedVars body)))
        ∅) = Bool.true := by
  rw [defUseWellFormed_block]
  exact defUseWellFormed_havoc_map outer _ md
    (havoc_filter_subset_outer outer body h_body_wf)

/-- The havoc block's `Stmt.definedVars _ true = []`. -/
private theorem definedVars_true_havoc_block
    (body : Statements) (md : MetaData Expression) (loop_num : String) :
    @Stmt.definedVars Expression Command _
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
        (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
          (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
            (Block.modifiedVars body)))
        ∅) true = [] := by
  simp [Stmt.definedVars]

/-- WF of the `arbitrary_iter_assumes_<n>` block: given `assumeGuard` is WF
    and the invariants' `getVars` are in `outer`. -/
private theorem defUseWellFormed_arb_iter_assumes_block
    (outer : Expression.Ident → Bool) (loop_num : String)
    (assumeGuard : Statements)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (h_assumeGuard_wf : Block.defUseWellFormed outer assumeGuard = Bool.true)
    (h_assumeGuard_def_true_empty :
        @Block.definedVars Expression Command _ assumeGuard true = [])
    (h_inv_getVars :
        ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
          outer n = Bool.true) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
        (assumeGuard ++ inv.mapIdx (fun i lp =>
          Stmt.cmd (HasPassiveCmds.assume
            (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
              toString (if lp.fst.isEmpty = Bool.true then toString i
                        else toString i ++ toString "_" ++ toString lp.fst))
            lp.2 md)))
        md) = Bool.true := by
  rw [defUseWellFormed_block]
  rw [defUseWellFormed_block_append]
  refine ⟨h_assumeGuard_wf, ?_⟩
  -- Tail: outer extended by definedVars true assumeGuard = outer.
  rw [defUseWellFormed_block_congr (outer₂ := outer)
        (fun n => by simp [h_assumeGuard_def_true_empty])]
  exact defUseWellFormed_mapIdx_assume outer inv md _ h_inv_getVars

/-- The arb_iter_assumes block's `Stmt.definedVars _ true = []`. -/
private theorem definedVars_true_arb_iter_assumes_block
    (loop_num : String) (assumeGuard : Statements)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression) :
    @Stmt.definedVars Expression Command _
      (Stmt.block (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
        (assumeGuard ++ inv.mapIdx (fun i lp =>
          Stmt.cmd (HasPassiveCmds.assume
            (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
              toString (if lp.fst.isEmpty = Bool.true then toString i
                        else toString i ++ toString "_" ++ toString lp.fst))
            lp.2 md)))
        md) true = [] := by
  simp [Stmt.definedVars]

/-- Master helper: well-formedness of `buildLoopOutput`-shaped statements.
    Parametric in `assumeGuard`, `pre`, `post`, `exit` (the four pieces that
    differ between guard×measure cases). -/
private theorem defUseWellFormed_buildLoopOutput_form
    (loop_num : String) (g : ExprOrNondet Expression)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (assumeGuard pre post exit : Statements)
    (outer : Expression.Ident → Bool)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true)
    (h_inv_getVars :
        ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
          outer n = Bool.true)
    (h_g_getVars : ∀ n ∈ g.getVars, outer n = Bool.true)
    -- `assumeGuard` well-formed and "open" (definedVars true = []).
    (h_assumeGuard_wf : Block.defUseWellFormed outer assumeGuard = Bool.true)
    (h_assumeGuard_def_true_empty :
        @Block.definedVars Expression Command _ assumeGuard true = [])
    -- `pre` is well-formed against any outer-extension that includes outer
    -- (i.e., monotone), and we know what its `definedVars true` is via
    -- `pre_def_true`.  We also need that `pre` isn't reading anything outside
    -- `outer ∪ pre.definedVars true` and doesn't define anything in
    -- `Block.definedVars body false`.
    (pre_def_true : List Expression.Ident)
    (h_pre_def_true_eq :
        @Block.definedVars Expression Command _ pre true = pre_def_true)
    (h_pre_wf : Block.defUseWellFormed outer pre = Bool.true)
    -- `body`'s touched vars don't intersect `pre_def_true` (so we can
    -- absorb pre_def_true into outer for body via defUseWellFormed_outer_extend).
    (h_pre_def_disjoint_body :
        ∀ n ∈ pre_def_true,
          n ∉ Block.modifiedVars body ∧ n ∉ Block.getVars body ∧
          n ∉ Block.definedVars body false ∧ n ∉ Block.funcDeclNames body)
    -- `post` is well-formed against `outer ⊕ pre_def_true ⊕ body.definedVars true`.
    (h_post_wf : Block.defUseWellFormed
        (fun n => outer n || decide (n ∈ pre_def_true) ||
                  decide (n ∈ Block.definedVars body true)) post = Bool.true)
    -- `exit` is well-formed against `outer`.
    (h_exit_wf : Block.defUseWellFormed outer exit = Bool.true)
    (h_exit_def_true_empty :
        @Block.definedVars Expression Command _ exit true = []) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_" ++ loop_num)
        [Stmt.block
            (toString loopElimBlockPrefix ++ toString "first_iter_asserts_" ++ loop_num)
            (inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assert
                 (toString loopElimAssertPrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)) ++
             inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assume
                 (toString loopElimAssumePrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)))
            ∅,
          Stmt.ite g
            (Stmt.block
                (toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++ loop_num)
                ([Stmt.block
                      (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                      (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                        (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                          (Block.modifiedVars body)))
                      ∅,
                    Stmt.block
                      (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
                      (assumeGuard ++ inv.mapIdx (fun i lp =>
                        Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
                            toString (if lp.fst.isEmpty = Bool.true then toString i
                                      else toString i ++ toString "_" ++ toString lp.fst))
                          lp.2 md)))
                      md] ++ pre ++ body ++
                  inv.mapIdx (fun i lp =>
                    Stmt.cmd (HasPassiveCmds.assert
                      (toString loopElimAssertPrefix ++ loop_num ++
                        toString "_arbitrary_iter_maintain_invariant_" ++
                        toString (if lp.fst.isEmpty = Bool.true then toString i
                                  else toString i ++ toString "_" ++ toString lp.fst))
                      lp.snd md)) ++ post)
                ∅
              :: ([Stmt.block
                    (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                    (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                      (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                        (Block.modifiedVars body)))
                    ∅] ++ exit ++
                inv.mapIdx (fun i lp =>
                  Stmt.cmd (HasPassiveCmds.assume
                    (toString loopElimAssumePrefix ++ loop_num ++ toString "_exit_invariant_" ++
                      toString (if lp.fst.isEmpty = Bool.true then toString i
                                else toString i ++ toString "_" ++ toString lp.fst))
                    lp.snd md))))
            [] ∅]
        ∅) = Bool.true := by
  -- Outermost: a `Stmt.block` reduces to `Block.defUseWellFormed` of the inner list.
  rw [defUseWellFormed_block]
  -- The inner list is `[first_iter_asserts; ite g (...) [] {}]`.  Peel the head.
  apply defUseWellFormed_cons_intro
  · -- HEAD 1: first_iter_asserts block.
    -- It's a `Stmt.block (label) (asserts ++ assumes) ∅`.  Reduce to the inner.
    rw [defUseWellFormed_block]
    rw [defUseWellFormed_block_append]
    refine ⟨?_, ?_⟩
    · -- The asserts mapIdx.
      exact defUseWellFormed_mapIdx_assert outer inv md _ h_inv_getVars
    · -- The assumes mapIdx, against `outer ⊕ asserts.definedVars true = outer`.
      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
        rw [definedVars_true_mapIdx_assert]; simp)]
      exact defUseWellFormed_mapIdx_assume outer inv md _ h_inv_getVars
  · -- TAIL 1: extension by first_iter_asserts.definedVars true is empty (block-wrapped).
    rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by simp [Stmt.definedVars])]
    -- The remaining list is `[ite g (arb_facts :: exit_state) [] {}]`.  Peel the head.
    apply defUseWellFormed_cons_intro
    · -- HEAD 2: the ite.
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- All g.getVars in outer.
        rw [List.all_eq_true]; exact h_g_getVars
      · -- THEN-branch: the arb_facts block plus exit_state list.
        -- The block is wrapped in a single-element list.
        show Block.defUseWellFormed outer
          (Stmt.block _ ([_, _] ++ pre ++ body ++ _ ++ post) ∅
            :: ([_] ++ exit ++ _)) = Bool.true
        apply defUseWellFormed_cons_intro
        · -- arb_facts block.
          rw [defUseWellFormed_block]
          -- Inner: `[havoc; arb_iter_assumes] ++ pre ++ body ++ maintain_inv ++ post`.
          rw [defUseWellFormed_block_append]
          refine ⟨?_, ?_⟩
          · -- LHS: `[havoc; arb_iter_assumes] ++ pre ++ body ++ maintain_inv`.
            rw [defUseWellFormed_block_append]
            refine ⟨?_, ?_⟩
            · rw [defUseWellFormed_block_append]
              refine ⟨?_, ?_⟩
              · rw [defUseWellFormed_block_append]
                refine ⟨?_, ?_⟩
                · -- `[havoc; arb_iter_assumes]`
                  apply defUseWellFormed_cons_intro
                  · exact defUseWellFormed_havoc_block outer body md loop_num h_body_wf
                  · -- After havoc, outer extension by [] = outer.
                    rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                      simp [definedVars_true_havoc_block])]
                    apply defUseWellFormed_cons_intro
                    · exact defUseWellFormed_arb_iter_assumes_block outer loop_num
                        assumeGuard inv md h_assumeGuard_wf h_assumeGuard_def_true_empty
                        h_inv_getVars
                    · -- Trailing nil after the assumes block.
                      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                        simp [definedVars_true_arb_iter_assumes_block])]
                      simp [Block.defUseWellFormed]
                · -- After `[havoc; arb_iter_assumes]`, the running outer extension is
                  -- `outer + ([] ++ [])` (both are blocks → definedVars true = []).
                  -- So pre is WF against (outer + ∅) = outer.
                  rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                    simp [Block.definedVars, definedVars_true_havoc_block,
                          definedVars_true_arb_iter_assumes_block, Stmt.definedVars])]
                  exact h_pre_wf
              · -- After `[havoc; arb_iter_assumes] ++ pre`, the running outer is
                -- `outer + (... + pre.definedVars true) = outer + pre_def_true`.
                rw [defUseWellFormed_block_congr
                      (outer₂ := fun n => outer n || decide (n ∈ pre_def_true)) (fun n => by
                  simp [Block.definedVars, definedVars_true_havoc_block,
                        definedVars_true_arb_iter_assumes_block, Stmt.definedVars,
                        h_pre_def_true_eq])]
                -- Body is WF against outer.  Extend by pre_def_true (disjoint from body).
                exact defUseWellFormed_outer_extend_block h_body_wf (fun n hn => by
                  rw [decide_eq_true_eq] at hn
                  exact h_pre_def_disjoint_body n hn)
            · -- After `[havoc; arb_iter_assumes] ++ pre ++ body`, the running outer is
              -- `outer + pre_def_true + body.definedVars true`.
              rw [defUseWellFormed_block_congr
                    (outer₂ := fun n => outer n || decide (n ∈ pre_def_true)
                                || decide (n ∈ Block.definedVars body Bool.true))
                    (fun n => by
                rw [block_definedVars_append]
                simp [Block.definedVars, definedVars_true_havoc_block,
                      definedVars_true_arb_iter_assumes_block, Stmt.definedVars,
                      h_pre_def_true_eq, Bool.or_assoc])]
              -- maintain_invariants asserts; need invs' getVars in extended outer.
              apply defUseWellFormed_mapIdx_assert
              intro n hn
              simp only [Bool.or_eq_true, decide_eq_true_eq]
              exact .inl (.inl (h_inv_getVars n hn))
          · -- After `[havoc; arb_iter_assumes] ++ pre ++ body ++ maintain_inv`, the running
            -- outer is `outer + pre_def_true + body.definedVars true + []`.
            rw [defUseWellFormed_block_congr
                  (outer₂ := fun n => outer n || decide (n ∈ pre_def_true)
                              || decide (n ∈ Block.definedVars body Bool.true))
                  (fun n => by
              rw [block_definedVars_append, block_definedVars_append,
                  block_definedVars_append, definedVars_true_mapIdx_assert]
              simp [Block.definedVars, definedVars_true_havoc_block,
                    definedVars_true_arb_iter_assumes_block, Stmt.definedVars,
                    h_pre_def_true_eq, Bool.or_assoc])]
            exact h_post_wf
        · -- exit_state tail: `[loop_havoc; ...] ++ exit ++ exit_inv_assumes`,
          -- against `outer ⊕ arb_facts.definedVars true = outer` (block-wrapped).
          rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by simp [Stmt.definedVars])]
          rw [defUseWellFormed_block_append]
          refine ⟨?_, ?_⟩
          · rw [defUseWellFormed_block_append]
            refine ⟨?_, ?_⟩
            · -- `[loop_havoc]` singleton.
              apply defUseWellFormed_cons_intro
              · exact defUseWellFormed_havoc_block outer body md loop_num h_body_wf
              · rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                  simp [definedVars_true_havoc_block])]
                simp [Block.defUseWellFormed]
            · -- exit, against `outer + havoc_block.definedVars true = outer`.
              rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                simp [Block.definedVars, definedVars_true_havoc_block, Stmt.definedVars])]
              exact h_exit_wf
          · -- exit_inv_assumes mapIdx.
            rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
              simp [Block.definedVars, definedVars_true_havoc_block, Stmt.definedVars,
                    h_exit_def_true_empty])]
            exact defUseWellFormed_mapIdx_assume outer inv md _ h_inv_getVars
      · -- ELSE-branch: empty.
        simp [Block.defUseWellFormed]
    · -- TAIL 2: outer extension by ite.definedVars true = [] = outer.
      simp [Block.defUseWellFormed, Stmt.definedVars]

/-! ### Case-specific instantiations of `defUseWellFormed_buildLoopOutput_form` -/

/-- Auxiliary: an assume command with single getVars in outer is WF and has
    `definedVars _ true = []`. -/
private theorem defUseWellFormed_singleton_assume
    (outer : Expression.Ident → Bool) (label : String)
    (e : Expression.Expr) (md : MetaData Expression)
    (hgv : ∀ n ∈ HasVarsPure.getVars e, outer n = Bool.true) :
    Block.defUseWellFormed (P := Expression) (C := Command) outer
      [Stmt.cmd (HasPassiveCmds.assume label e md)] = Bool.true := by
  apply defUseWellFormed_cons_intro
  · simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
      HasVarsImp.definedVars, HasPassiveCmds.assume, Command.getVars,
      Command.modifiedVars, Command.definedVars, Cmd.getVars, Cmd.modifiedVars,
      Cmd.definedVars, List.all_nil, Bool.and_true, Bool.true_and]
    rw [List.all_eq_true]; exact hgv
  · simp [Block.defUseWellFormed]

private theorem definedVars_true_singleton_assume
    (label : String) (e : Expression.Expr) (md : MetaData Expression) :
    @Block.definedVars Expression Command _
      [Stmt.cmd (HasPassiveCmds.assume label e md)] true = [] := by
  simp [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
        HasPassiveCmds.assume, Command.definedVars, Cmd.definedVars]

/-- WF of the loop output for the `.nondet` case (no guard, no measure):
    all four pieces (`assumeGuard`, `pre`, `post`, `exit`) are empty. -/
private theorem defUseWellFormed_loop_output_nondet
    (loop_num : String) (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (outer : Expression.Ident → Bool)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true)
    (h_inv_getVars : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
        outer n = Bool.true) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_" ++ loop_num)
        [Stmt.block
            (toString loopElimBlockPrefix ++ toString "first_iter_asserts_" ++ loop_num)
            (inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assert
                 (toString loopElimAssertPrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)) ++
             inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assume
                 (toString loopElimAssumePrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)))
            ∅,
          Stmt.ite (.nondet)
            (Stmt.block
                (toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++ loop_num)
                ([Stmt.block
                      (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                      (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                        (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                          (Block.modifiedVars body)))
                      ∅,
                    Stmt.block
                      (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
                      (([] : Statements) ++ inv.mapIdx (fun i lp =>
                        Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
                            toString (if lp.fst.isEmpty = Bool.true then toString i
                                      else toString i ++ toString "_" ++ toString lp.fst))
                          lp.2 md)))
                      md] ++ ([] : Statements) ++ body ++
                  inv.mapIdx (fun i lp =>
                    Stmt.cmd (HasPassiveCmds.assert
                      (toString loopElimAssertPrefix ++ loop_num ++
                        toString "_arbitrary_iter_maintain_invariant_" ++
                        toString (if lp.fst.isEmpty = Bool.true then toString i
                                  else toString i ++ toString "_" ++ toString lp.fst))
                      lp.snd md)) ++ ([] : Statements))
                ∅
              :: ([Stmt.block
                    (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                    (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                      (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                        (Block.modifiedVars body)))
                    ∅] ++ ([] : Statements) ++
                inv.mapIdx (fun i lp =>
                  Stmt.cmd (HasPassiveCmds.assume
                    (toString loopElimAssumePrefix ++ loop_num ++ toString "_exit_invariant_" ++
                      toString (if lp.fst.isEmpty = Bool.true then toString i
                                else toString i ++ toString "_" ++ toString lp.fst))
                    lp.snd md))))
            [] ∅]
        ∅) = Bool.true := by
  apply defUseWellFormed_buildLoopOutput_form
    (assumeGuard := []) (pre := []) (post := []) (exit := []) (pre_def_true := [])
  · exact h_body_wf
  · exact h_inv_getVars
  · intro n hn; simp [ExprOrNondet.getVars] at hn
  · simp [Block.defUseWellFormed]
  · simp [Block.definedVars]
  · simp [Block.definedVars]
  · simp [Block.defUseWellFormed]
  · intro n hn; simp at hn
  · simp [Block.defUseWellFormed]
  · simp [Block.defUseWellFormed]
  · simp [Block.definedVars]

/-- WF of the loop output for the `.det g, none` case:
    `assumeGuard = [guard_assume]`, `pre = []`, `post = []`,
    `exit = [not_guard_assume]`. -/
private theorem defUseWellFormed_loop_output_detNone
    (loop_num : String) (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (outer : Expression.Ident → Bool)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true)
    (h_inv_getVars : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
        outer n = Bool.true)
    (g : Expression.Expr)
    (h_g_getVars : ∀ n ∈ HasVarsPure.getVars g, outer n = Bool.true) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_" ++ loop_num)
        [Stmt.block
            (toString loopElimBlockPrefix ++ toString "first_iter_asserts_" ++ loop_num)
            (inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assert
                 (toString loopElimAssertPrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)) ++
             inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assume
                 (toString loopElimAssumePrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)))
            ∅,
          Stmt.ite (.det g)
            (Stmt.block
                (toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++ loop_num)
                ([Stmt.block
                      (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                      (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                        (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                          (Block.modifiedVars body)))
                      ∅,
                    Stmt.block
                      (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
                      ([Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_guard")
                          g md)] ++ inv.mapIdx (fun i lp =>
                        Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
                            toString (if lp.fst.isEmpty = Bool.true then toString i
                                      else toString i ++ toString "_" ++ toString lp.fst))
                          lp.2 md)))
                      md] ++ ([] : Statements) ++ body ++
                  inv.mapIdx (fun i lp =>
                    Stmt.cmd (HasPassiveCmds.assert
                      (toString loopElimAssertPrefix ++ loop_num ++
                        toString "_arbitrary_iter_maintain_invariant_" ++
                        toString (if lp.fst.isEmpty = Bool.true then toString i
                                  else toString i ++ toString "_" ++ toString lp.fst))
                      lp.snd md)) ++ ([] : Statements))
                ∅
              :: ([Stmt.block
                    (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                    (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                      (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                        (Block.modifiedVars body)))
                    ∅] ++ [Stmt.cmd (HasPassiveCmds.assume
                      (toString loopElimAssumePrefix ++ loop_num ++ toString "_not_guard")
                      (HasNot.not g) md)] ++
                inv.mapIdx (fun i lp =>
                  Stmt.cmd (HasPassiveCmds.assume
                    (toString loopElimAssumePrefix ++ loop_num ++ toString "_exit_invariant_" ++
                      toString (if lp.fst.isEmpty = Bool.true then toString i
                                else toString i ++ toString "_" ++ toString lp.fst))
                    lp.snd md))))
            [] ∅]
        ∅) = Bool.true := by
  apply defUseWellFormed_buildLoopOutput_form
    (assumeGuard := [Stmt.cmd (HasPassiveCmds.assume
      (toString loopElimAssumePrefix ++ loop_num ++ toString "_guard") g md)])
    (pre := [])
    (post := [])
    (exit := [Stmt.cmd (HasPassiveCmds.assume
      (toString loopElimAssumePrefix ++ loop_num ++ toString "_not_guard")
      (HasNot.not g) md)])
    (pre_def_true := [])
  · exact h_body_wf
  · exact h_inv_getVars
  · intro n hn; simp [ExprOrNondet.getVars] at hn; exact h_g_getVars n hn
  · -- assumeGuard WF
    exact defUseWellFormed_singleton_assume outer _ g md h_g_getVars
  · -- assumeGuard.definedVars true = []
    exact definedVars_true_singleton_assume _ g md
  · -- pre.definedVars true = []
    simp [Block.definedVars]
  · -- pre WF
    simp [Block.defUseWellFormed]
  · intro n hn; simp at hn
  · simp [Block.defUseWellFormed]
  · -- exit WF
    apply defUseWellFormed_singleton_assume
    intro n hn
    -- HasNot.not g's getVars ⊆ g's getVars.
    exact h_g_getVars n (mem_getVars_not_subset hn)
  · -- exit.definedVars true = []
    exact definedVars_true_singleton_assume _ _ md

/-- WF of the loop output for the `.det g, some m` case:
    `assumeGuard = [guard_assume]`, `pre = [m_old_init, measure_lb]`,
    `post = [measure_decrease]`, `exit = [not_guard_assume]`. -/
private theorem defUseWellFormed_loop_output_detSome
    (loop_num : String) (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (outer : Expression.Ident → Bool)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true)
    (h_inv_getVars : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
        outer n = Bool.true)
    (g : Expression.Expr)
    (h_g_getVars : ∀ n ∈ HasVarsPure.getVars g, outer n = Bool.true)
    (m : Expression.Expr)
    (h_m_getVars : ∀ n ∈ HasVarsPure.getVars m, outer n = Bool.true)
    -- m_old freshness: not in body's touchedVars, not in outer.
    (h_m_old_notin_body : (HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
        : Expression.Ident) ∉ Block.touchedVars body)
    (h_m_old_not_outer : outer (HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
        : Expression.Ident) = Bool.false)
    (h_m_old_notin_body_def : (HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
        : Expression.Ident) ∉ Block.definedVars body Bool.false)
    (h_m_old_notin_body_funcDecl : (HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
        : Expression.Ident) ∉ Block.funcDeclNames body) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_" ++ loop_num)
        [Stmt.block
            (toString loopElimBlockPrefix ++ toString "first_iter_asserts_" ++ loop_num)
            (inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assert
                 (toString loopElimAssertPrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)) ++
             inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assume
                 (toString loopElimAssumePrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)))
            ∅,
          Stmt.ite (.det g)
            (Stmt.block
                (toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++ loop_num)
                ([Stmt.block
                      (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                      (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                        (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                          (Block.modifiedVars body)))
                      ∅,
                    Stmt.block
                      (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
                      ([Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_guard")
                          g md)] ++ inv.mapIdx (fun i lp =>
                        Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
                            toString (if lp.fst.isEmpty = Bool.true then toString i
                                      else toString i ++ toString "_" ++ toString lp.fst))
                          lp.2 md)))
                      md] ++ [Stmt.cmd (HasInit.init
                        (HasIdent.ident (toString "$__loop_measure_" ++ loop_num))
                        HasIntOrder.intTy (.det m) md),
                      Stmt.cmd (HasPassiveCmds.assert
                        (toString loopElimAssertPrefix ++ loop_num ++ toString "_measure_lb")
                        (HasNot.not (HasIntOrder.lt
                          (HasFvar.mkFvar (HasIdent.ident
                            (toString "$__loop_measure_" ++ loop_num)))
                          HasIntOrder.zero)) md)] ++ body ++
                  inv.mapIdx (fun i lp =>
                    Stmt.cmd (HasPassiveCmds.assert
                      (toString loopElimAssertPrefix ++ loop_num ++
                        toString "_arbitrary_iter_maintain_invariant_" ++
                        toString (if lp.fst.isEmpty = Bool.true then toString i
                                  else toString i ++ toString "_" ++ toString lp.fst))
                      lp.snd md)) ++
                  [Stmt.cmd (HasPassiveCmds.assert
                    (toString loopElimAssertPrefix ++ loop_num ++ toString "_measure_decrease")
                    (HasIntOrder.lt m
                      (HasFvar.mkFvar (HasIdent.ident
                        (toString "$__loop_measure_" ++ loop_num)))) md)])
                ∅
              :: ([Stmt.block
                    (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                    (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                      (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                        (Block.modifiedVars body)))
                    ∅] ++ [Stmt.cmd (HasPassiveCmds.assume
                      (toString loopElimAssumePrefix ++ loop_num ++ toString "_not_guard")
                      (HasNot.not g) md)] ++
                inv.mapIdx (fun i lp =>
                  Stmt.cmd (HasPassiveCmds.assume
                    (toString loopElimAssumePrefix ++ loop_num ++ toString "_exit_invariant_" ++
                      toString (if lp.fst.isEmpty = Bool.true then toString i
                                else toString i ++ toString "_" ++ toString lp.fst))
                    lp.snd md))))
            [] ∅]
        ∅) = Bool.true := by
  -- Set up the m_old identifier as a single-element list for pre_def_true.
  let m_old : Expression.Ident :=
    HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
  have hm_old : m_old = HasIdent.ident (toString "$__loop_measure_" ++ loop_num) := rfl
  apply defUseWellFormed_buildLoopOutput_form
    (assumeGuard := [Stmt.cmd (HasPassiveCmds.assume
      (toString loopElimAssumePrefix ++ loop_num ++ toString "_guard") g md)])
    (pre := [Stmt.cmd (HasInit.init m_old HasIntOrder.intTy (.det m) md),
             Stmt.cmd (HasPassiveCmds.assert
               (toString loopElimAssertPrefix ++ loop_num ++ toString "_measure_lb")
               (HasNot.not (HasIntOrder.lt
                 (HasFvar.mkFvar m_old) HasIntOrder.zero)) md)])
    (post := [Stmt.cmd (HasPassiveCmds.assert
      (toString loopElimAssertPrefix ++ loop_num ++ toString "_measure_decrease")
      (HasIntOrder.lt m (HasFvar.mkFvar m_old)) md)])
    (exit := [Stmt.cmd (HasPassiveCmds.assume
      (toString loopElimAssumePrefix ++ loop_num ++ toString "_not_guard")
      (HasNot.not g) md)])
    (pre_def_true := [m_old])
  · exact h_body_wf
  · exact h_inv_getVars
  · intro n hn; simp [ExprOrNondet.getVars] at hn; exact h_g_getVars n hn
  · -- assumeGuard WF
    exact defUseWellFormed_singleton_assume outer _ g md h_g_getVars
  · -- assumeGuard.definedVars true = []
    exact definedVars_true_singleton_assume _ g md
  · -- pre.definedVars true = [m_old]
    simp [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
          HasInit.init, HasPassiveCmds.assert, Command.definedVars, Cmd.definedVars]
  · -- pre WF
    apply defUseWellFormed_cons_intro
    · -- init m_old: m_old ∉ outer (so the "fresh" check passes)
      simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasInit.init, Command.getVars, Command.modifiedVars,
        Command.definedVars, Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars,
        ExprOrNondet.getVars, List.all_nil, Bool.and_true, Bool.true_and]
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true]; exact h_m_getVars
      · simp only [List.all_cons, List.all_nil, Bool.and_true]
        rw [hm_old, h_m_old_not_outer]; rfl
    · -- After init, outer is extended by [m_old].
      apply defUseWellFormed_cons_intro
      · -- assert measure_lb: getVars = [m_old]; m_old now in extended outer.
        simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
          HasVarsImp.definedVars, HasPassiveCmds.assert, Command.getVars,
          Command.modifiedVars, Command.definedVars, Cmd.getVars, Cmd.modifiedVars,
          Cmd.definedVars, List.all_nil, Bool.and_true, Bool.true_and]
        rw [List.all_eq_true]
        intro n hn
        -- n ∈ HasNot.not (m_old < 0) → n is m_old (or in 0's getVars, which is []).
        simp only [Bool.or_eq_true, decide_eq_true_eq, Stmt.definedVars,
          HasVarsImp.definedVars, HasInit.init, Command.definedVars, Cmd.definedVars,
          List.mem_singleton]
        right
        -- Need: n = m_old.  hn : n ∈ getVars (¬ (m_old < 0))
        have hn' := mem_getVars_not_subset hn
        have h2 := mem_getVars_lt_split hn'
        rcases h2 with hl | hr
        · simpa [Lambda.LExpr.LExpr.getVars, HasFvar.mkFvar] using hl
        · simp [Lambda.LExpr.LExpr.getVars] at hr
      · simp [Block.defUseWellFormed]
  · -- pre_def disjoint from body (m_old ∉ body's touched vars or funcDecls)
    intro n hn
    simp at hn; subst hn
    simp [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at h_m_old_notin_body
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact h_m_old_notin_body.1
    · exact h_m_old_notin_body.2.2
    · exact h_m_old_notin_body_def
    · exact h_m_old_notin_body_funcDecl
  · -- post WF (against outer + [m_old] + body.definedVars true)
    apply defUseWellFormed_cons_intro
    · simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasPassiveCmds.assert, Command.getVars,
        Command.modifiedVars, Command.definedVars, Cmd.getVars, Cmd.modifiedVars,
        Cmd.definedVars, List.all_nil, Bool.and_true, Bool.true_and]
      rw [List.all_eq_true]
      intro n hn
      -- n ∈ getVars (m < m_old) → n in m's getVars or n = m_old.
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      have h2 := mem_getVars_lt_split hn
      rcases h2 with hl | hr
      · -- n in m's getVars, so n in outer.
        left; left; exact h_m_getVars n hl
      · -- n in getVars (mkFvar m_old), so n = m_old.
        have hmo : n = m_old := by
          simpa [Lambda.LExpr.LExpr.getVars, HasFvar.mkFvar] using hr
        left; right; rw [List.mem_singleton]; exact hmo
    · simp [Block.defUseWellFormed]
  · -- exit WF: not_guard assume.
    apply defUseWellFormed_singleton_assume
    intro n hn
    -- HasNot.not g's getVars ⊆ g's getVars.
    exact h_g_getVars n (mem_getVars_not_subset hn)
  · -- exit.definedVars true = []
    exact definedVars_true_singleton_assume _ _ md

/-- Loop case helper: well-formedness of the loop encoding's output.

    The transform produces
       block loop_label [first_iter_facts, ite guard (arb_facts :: exit_state) [] {}]
    which we must show is `defUseWellFormed` against `outer`.  The freshness
    side conditions mean every transform-introduced name (block labels,
    havoc'd vars from the body, m_old) doesn't collide with `outer`. -/
private theorem defUseWellFormed_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (outer : Expression.Ident → Bool)
    (h_outer_fresh : ∀ n, outer n = Bool.true →
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (h_def_not_reserved : ∀ n ∈ Block.definedVars body false,
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (h_funcDeclNames_not_reserved : ∀ n ∈ Block.funcDeclNames body,
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (hwf : Stmt.defUseWellFormed outer
            (.loop guard measure inv body md) = Bool.true) :
    Stmt.defUseWellFormed outer
      (stmtResult σ (.loop guard measure inv body md)) = Bool.true := by
  -- Extract loop-level WF facts from `hwf`.
  unfold Stmt.defUseWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨h_guard_all, h_meas_all⟩, h_inv_all⟩, h_body_wf⟩ := hwf
  rw [List.all_eq_true] at h_guard_all h_meas_all h_inv_all
  -- The output: stmtResult on the source loop is the transform's output.
  -- We use the structural lemma `definedVars_subset_stmtResult_loop` style of unfolding.
  -- Strategy: every (n ∈ touchedVars (stmtResult σ ...)) lies in
  -- (touchedVars source) ∪ (definedVars (stmtResult σ ...)).  Combined with
  -- `outer`-monotone over source touched vars (from hwf) plus the body's
  -- inner well-formedness, we directly call `defUseWellFormed_outer_extend_stmt`
  -- on a "source statement minus m_old reservation" framing.
  --
  -- Easier path: directly induct on the structure exposed by stmtResult_loop_struct.
  -- But the loop output has many nested pieces; rather than go that way, we
  -- use the `defUseWellFormed_touched_notDef` family in reverse: a statement is
  -- well-formed against outer if every (touched but not defined) name is in outer.
  -- However, no such "reverse" lemma is currently available.
  --
  -- Direct approach: apply the structural unfolding (4-way split on guard×measure)
  -- as in `mem_definedVars_stmtResult_loop` etc., then for each concrete output
  -- prove `Stmt.defUseWellFormed outer ...` via the piece-wise helpers.
  show Stmt.defUseWellFormed outer
      (match (stmtRun σ (.loop guard measure inv body md)).fst with
       | .ok (_, s') => s' | .error _ => default) = Bool.true
  have hok' := hok
  unfold stmtOk at hok'
  -- Two `m_old`-related freshness facts proved up-front (we'll discharge them
  -- whenever needed in the .det / .some m branch).
  have h_m_old_pref : ∀ ln,
      loopElimReservedPrefix.toList.isPrefixOf
        ((⟨"$__loop_measure_" ++ ln, ()⟩ : Expression.Ident).name.toList) :=
    fun ln => loopElimReservedPrefix_isPrefixOf_measure ln
  have h_m_old_not_outer : ∀ ln, outer (⟨"$__loop_measure_" ++ ln, ()⟩ : Expression.Ident) = Bool.false := by
    intro ln
    cases hh : outer ⟨"$__loop_measure_" ++ ln, ()⟩ with
    | false => rfl
    | true => exact absurd (h_m_old_pref ln) (h_outer_fresh _ hh)
  have h_m_old_notin_body_def : ∀ ln,
      (⟨"$__loop_measure_" ++ ln, ()⟩ : Expression.Ident) ∉ Block.definedVars body false :=
    fun ln h => h_def_not_reserved _ h (h_m_old_pref ln)
  have h_m_old_notin_body_funcDecl : ∀ ln,
      (⟨"$__loop_measure_" ++ ln, ()⟩ : Expression.Ident) ∉ Block.funcDeclNames body :=
    fun ln h => h_funcDeclNames_not_reserved _ h (h_m_old_pref ln)
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error _ => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase,
      buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes,
      buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants,
      buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants,
      buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome,
      hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    -- Split on the `if hasLabelConflict then throw else pure`, then on guard,
    -- then on measure, mirroring the case structure of
    -- `definedVars_subset_stmtResult_loop`.  In each successful branch the
    -- equation `h` exposes a concrete `s'`, which is one of three concrete
    -- outputs of `buildLoopOutput`.  We then prove `defUseWellFormed` for that
    -- output by the master helper `defUseWellFormed_buildLoopOutput_form`.
    repeat (first | contradiction | (split at h; skip))
    -- For the `.det / .some m` case, `h` still has `StateT.pure …  .bind …`
    -- around the freshness check; unfold and split again.
    all_goals (first | contradiction | (
      try (unfold StateT.pure at h
           dsimp only [StateT.bind, StateT.map, ExceptT.bindCont, ExceptT.bind,
             ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
             Functor.map, MonadState.modifyGet, StateT.modifyGet,
             MonadStateOf.modifyGet, bumpStat, modify, genLoopNum] at h
           repeat (first | contradiction | (split at h; skip)))
      all_goals (first
        | contradiction
        | (obtain ⟨_, rfl⟩ := h))))
    -- After all branching, three remaining goals: `.det g, none`, `.det g, some m`, `.nondet`.
    -- Dispatch each by the corresponding case-specific helper.
    case h_1.isFalse =>
      -- det g, none
      rename_i _hcheck _guard0 g0 _meas _hnone
      exact defUseWellFormed_loop_output_detNone _ inv body md outer
        h_body_wf h_inv_all g0
        (fun n hn => h_guard_all n
          (by show n ∈ (ExprOrNondet.det g0 : ExprOrNondet Expression).getVars
              simp [ExprOrNondet.getVars]; exact hn))
    case h_2.isFalse.isTrue =>
      -- det g, some m
      rename_i _hcheck _guard0 g0 _meas m0 h_freshness _h_some
      apply defUseWellFormed_loop_output_detSome _ inv body md outer
        h_body_wf h_inv_all g0
        (fun n hn => h_guard_all n
          (by show n ∈ (ExprOrNondet.det g0 : ExprOrNondet Expression).getVars
              simp [ExprOrNondet.getVars]; exact hn))
        m0
        (fun n hn => h_meas_all n
          (by simp [ExprOrNondet.getVars]; exact hn))
      · exact h_freshness
      · exact h_m_old_not_outer _
      · exact h_m_old_notin_body_def _
      · exact h_m_old_notin_body_funcDecl _
    case h_2 =>
      -- nondet
      exact defUseWellFormed_loop_output_nondet _ inv body md outer
        h_body_wf h_inv_all

-- Structural well-formedness preservation for `stmtResult` / `blockResult`.
--
-- Two side conditions on the outer scope `outer` propagate through the
-- recursion:
-- * `h_outer_fresh`: `outer n = true` implies `n.name` does NOT have the
--   reserved `$__loop` prefix.  This is provided initially by
--   `InitEnvWF.reservedFresh`.
-- * `h_def_not_reserved`: every var in the SOURCE statement's
--   `definedVars false` does NOT have the reserved prefix.  This is
--   provided initially by `InitEnvWF.definedVarsNotReserved` (with the
--   reserved list still containing `loopElimReservedPrefix`).
--
-- These two facts together let the cons-tail case discharge the freshness
-- side condition for the extended outer (which adds the source's scoped
-- definedVars to the outer scope).
mutual
private theorem defUseWellFormed_stmtResultAux
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (outer : Expression.Ident → Bool)
    (h_outer_fresh : ∀ n, outer n = Bool.true →
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (h_def_not_reserved : ∀ n ∈ Stmt.definedVars s false,
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (h_funcDecl_not_reserved : ∀ n ∈ Stmt.funcDeclNames s,
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (hwf : Stmt.defUseWellFormed outer s = Bool.true) :
    Stmt.defUseWellFormed outer (stmtResult σ s) = Bool.true := by
  match s with
  | .cmd c => rw [stmtResult_cmd]; exact hwf
  | .exit l md => rw [stmtResult_exit]; exact hwf
  | .funcDecl d md => rw [stmtResult_funcDecl]; exact hwf
  | .typeDecl tc md => rw [stmtResult_typeDecl]; exact hwf
  | .block l bss md =>
    rw [stmtResult_block (hok := hok)]
    have hwf' : Block.defUseWellFormed outer bss = Bool.true := by
      simpa [defUseWellFormed_block] using hwf
    have hdef_block : ∀ n ∈ Block.definedVars bss false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      show n ∈ Stmt.definedVars (s := Stmt.block l bss md) false
      simpa [Stmt.definedVars] using hn
    have hfd_block : ∀ n ∈ Block.funcDeclNames bss,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_funcDecl_not_reserved n
      simpa [Stmt.funcDeclNames] using hn
    have ih := defUseWellFormed_blockResultAux σ bss (stmtOk_block_inner hok) outer
                h_outer_fresh hdef_block hfd_block hwf'
    simpa [defUseWellFormed_block] using ih
  | .ite c tss ess md =>
    rw [stmtResult_ite (hok := hok)]
    have ⟨hwf_t, hwf_e⟩ := defUseWellFormed_ite_branches hwf
    have hcond : ∀ n ∈ ExprOrNondet.getVars c, outer n = Bool.true := by
      intro n hn
      have h := hwf
      unfold Stmt.defUseWellFormed at h
      simp only [Bool.and_eq_true] at h
      have hcond_all := h.1.1
      rw [List.all_eq_true] at hcond_all
      exact hcond_all n hn
    have hdef_t : ∀ n ∈ Block.definedVars tss false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      show n ∈ Stmt.definedVars (s := Stmt.ite c tss ess md) false
      simp [Stmt.definedVars]; exact .inl hn
    have hdef_e : ∀ n ∈ Block.definedVars ess false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      show n ∈ Stmt.definedVars (s := Stmt.ite c tss ess md) false
      simp [Stmt.definedVars]; exact .inr hn
    have hfd_t : ∀ n ∈ Block.funcDeclNames tss,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_funcDecl_not_reserved n
      simp [Stmt.funcDeclNames]; exact .inl hn
    have hfd_e : ∀ n ∈ Block.funcDeclNames ess,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_funcDecl_not_reserved n
      simp [Stmt.funcDeclNames]; exact .inr hn
    have ih_t := defUseWellFormed_blockResultAux σ tss (stmtOk_ite_left hok) outer
                  h_outer_fresh hdef_t hfd_t hwf_t
    have ih_e := defUseWellFormed_blockResultAux (blockPostState σ tss) ess
                  (stmtOk_ite_right hok) outer h_outer_fresh hdef_e hfd_e hwf_e
    unfold Stmt.defUseWellFormed
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ih_t⟩, ih_e⟩
    rw [List.all_eq_true]
    exact hcond
  | .loop guard measure inv body md =>
    have hdef_body : ∀ n ∈ Block.definedVars body false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      show n ∈ Stmt.definedVars (s := Stmt.loop guard measure inv body md) false
      simpa [Stmt.definedVars] using hn
    have hfd_body : ∀ n ∈ Block.funcDeclNames body,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_funcDecl_not_reserved n
      simpa [Stmt.funcDeclNames] using hn
    exact defUseWellFormed_stmtResult_loop σ guard measure inv body md hok outer
      h_outer_fresh hdef_body hfd_body hwf

private theorem defUseWellFormed_blockResultAux
    (σ : LoopElimState) (bss : Statements) (hok : blockOk σ bss)
    (outer : Expression.Ident → Bool)
    (h_outer_fresh : ∀ n, outer n = Bool.true →
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (h_def_not_reserved : ∀ n ∈ Block.definedVars bss false,
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (h_funcDecl_not_reserved : ∀ n ∈ Block.funcDeclNames bss,
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (hwf : Block.defUseWellFormed outer bss = Bool.true) :
    Block.defUseWellFormed outer (blockResult σ bss) = Bool.true := by
  match bss with
  | [] => rw [blockResult_nil]; rfl
  | s :: rest =>
    rw [blockResult_cons (hok := hok)]
    have ⟨hwf_s, hwf_rest⟩ := defUseWellFormed_cons hwf
    have hdef_s : ∀ n ∈ Stmt.definedVars s false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      simp [Block.definedVars]; exact .inl hn
    have hdef_rest : ∀ n ∈ Block.definedVars rest false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      simp [Block.definedVars]; exact .inr hn
    have hfd_s : ∀ n ∈ Stmt.funcDeclNames s,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_funcDecl_not_reserved n
      simp [Block.funcDeclNames]; exact .inl hn
    have hfd_rest : ∀ n ∈ Block.funcDeclNames rest,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_funcDecl_not_reserved n
      simp [Block.funcDeclNames]; exact .inr hn
    have ih_s := defUseWellFormed_stmtResultAux σ s (blockOk_cons_left hok) outer
                  h_outer_fresh hdef_s hfd_s hwf_s
    apply defUseWellFormed_cons_intro ih_s
    -- Tail's outer is extended by `Stmt.definedVars (stmtResult σ s) true`.
    -- Use `stmtResult_definedVars_true_eq` to align that with `Stmt.definedVars s true`.
    have hdef_eq : Stmt.definedVars (stmtResult σ s) true = Stmt.definedVars s true :=
      stmtResult_definedVars_true_eq σ s (blockOk_cons_left hok)
    have h_new_outer_fresh : ∀ n, (outer n || decide (n ∈ Stmt.definedVars s true)) = Bool.true →
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hn
      rcases hn with h | h
      · exact h_outer_fresh n h
      · -- n ∈ Stmt.definedVars s true → n ∈ Stmt.definedVars s false (by subset).
        exact hdef_s n (stmt_definedVars_true_subset_false s n h)
    have ih_rest := defUseWellFormed_blockResultAux (stmtPostState σ s) rest
      (blockOk_cons_right hok) (fun n => outer n || decide (n ∈ Stmt.definedVars s true))
      h_new_outer_fresh hdef_rest hfd_rest hwf_rest
    have hcongr : ∀ n,
        (outer n || decide (n ∈ Stmt.definedVars (stmtResult σ s) true)) =
        (outer n || decide (n ∈ Stmt.definedVars s true)) := by
      intro n; rw [hdef_eq]
    rw [defUseWellFormed_block_congr hcongr (blockResult (stmtPostState σ s) rest)]
    exact ih_rest
end

/-- Top-level wrapper for the structural lemma, taking an `InitEnvWF` and
    extracting both `h_outer_fresh` and `h_def_not_reserved` from it. -/
private theorem defUseWellFormed_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (reserved : List String)
    (h_loop_reserved : loopElimReservedPrefix ∈ reserved)
    {ρ₀ : Env Expression}
    (hswf : InitEnvWF reserved s ρ₀) :
    Stmt.defUseWellFormed (fun n => (ρ₀.store n).isSome) (stmtResult σ s) = Bool.true := by
  apply defUseWellFormed_stmtResultAux σ s hok (fun n => (ρ₀.store n).isSome)
  · intro n hsome hpref
    exact hswf.reservedFresh n hsome loopElimReservedPrefix h_loop_reserved hpref
  · intro n hn hpref
    exact hswf.definedVarsNotReserved n hn loopElimReservedPrefix h_loop_reserved hpref
  · intro n hn hpref
    exact hswf.funcDeclNamesNotReserved n hn loopElimReservedPrefix h_loop_reserved hpref
  · exact hswf.defUseOk

theorem loopElim_overapproximatesAggressive
    (hwf_ext : WFEvalExtension φ) (σ : LoopElimState) :
    Transform.OverapproximatesAggressively
      (LangCore π φ)
      (LangCore π φ)
      (fun s =>
        match (StateT.run (ExceptT.run (Stmt.removeLoopsM s)) σ).fst with
        | .ok (_, s') => some s'
        | .error _ => none)
      loopElimReservedPrefix := by
  intro reserved st st' ht h_loop_reserved h_pd ρ₀ hswf
  -- Re-derive `stmtOk σ st` and `stmtResult σ st = st'` from the
  -- removeLoopsM-form of `ht`.
  simp only at ht
  -- Bridge to `stmtOk` / `stmtResult` form by case-splitting on the
  -- `removeLoopsM` result once.  The `error` branch contradicts `ht`,
  -- so we get both `stmtOk σ st` and `stmtResult σ st = st'` from the `ok` case.
  have hbridge : ∃ b, (stmtRun σ st).fst = .ok (b, st') := by
    show ∃ b, ((Stmt.removeLoopsM st).run.run σ).fst = .ok (b, st')
    cases h : ((Stmt.removeLoopsM st).run.run σ).fst with
    | ok p =>
      rw [h] at ht
      cases p with
      | mk b s' => simp at ht; exact ⟨b, ht ▸ rfl⟩
    | error e =>
      rw [h] at ht; cases ht
  obtain ⟨b, hbridge⟩ := hbridge
  have hok : stmtOk σ st := by
    simp only [stmtOk, hbridge]; rfl
  have hres_eq : stmtResult σ st = st' := by
    simp only [stmtResult, hbridge]
  clear ht hbridge
  -- hswf has type (LangCore π φ).initEnvWF reserved st ρ₀, which unfolds to
  -- InitEnvWF reserved st ρ₀.  We extract its WF eval fields explicitly.
  have hswf' : InitEnvWF reserved st ρ₀ := hswf
  have hwfb := hswf'.wfBool
  have hwfv := hswf'.wfVal
  have hwfvar := hswf'.wfVar
  subst hres_eq
  -- Derive the freshness precondition for `simulation`/`canfail_simulation`
  -- generically over `reserved` (matches the new signature).
  have hreserved_sig : ∀ n, (ρ₀.store n).isSome →
      ∀ p ∈ reserved, ¬ p.toList.isPrefixOf n.name.toList :=
    fun n hsome p hp => hswf.reservedFresh n hsome p hp
  have hsim := (simulation π φ hwf_ext (Stmt.sizeOf st) reserved h_loop_reserved).1
    σ st (Nat.le_refl _) hok ρ₀ hswf'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ' hstar; exact hsim.1 ρ' hstar
  · intro lbl ρ' hstar; exact hsim.2 lbl ρ' hstar
  · intro ⟨cfg, hfail, hreach⟩
    by_cases hnf₀ : ρ₀.hasFailure = Bool.true
    · exact ⟨.stmt (stmtResult σ st) ρ₀, by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
    · exact (canfail_simulation π φ hwf_ext (Stmt.sizeOf st) reserved h_loop_reserved).1
        σ st (Nat.le_refl _) hok ρ₀ hswf' ⟨cfg, hfail, hreach⟩
  · -- Show `InitEnvWF reserved (stmtResult σ st) ρ₀` from `InitEnvWF reserved st ρ₀`.
    -- The transform's fresh `$__loop_measure_N` names start with the reserved
    -- prefix `$__loop`; `hswf.reservedFresh` rules them out of `ρ₀.store`.
    -- The output InitEnvWF uses `reserved.erase loopElimReservedPrefix` since
    -- the output may have introduced names with `loopElimReservedPrefix`.
    refine
      { readWritesDefined := ?readWritesDefined,
        defsUndefined := ?defsUndefined,
        definedVarsNotReserved := ?definedVarsNotReserved,
        funcDeclNamesNotReserved := ?funcDeclNamesNotReserved,
        reservedFresh := ?reservedFresh,
        wfBool := hswf.wfBool,
        wfVal := hswf.wfVal,
        wfVar := hswf.wfVar,
        evalCong := hswf.evalCong,
        exprCongr := hswf.exprCongr,
        defUseOk := ?defUseOk }
    case readWritesDefined =>
      intro n hn hnd
      have ⟨hn_src, hnd_src⟩ := mem_touchedVars_stmtResult σ st hok n hn hnd
      exact hswf.readWritesDefined n hn_src hnd_src
    case defsUndefined =>
      intro n hn
      rcases mem_definedVars_stmtResult σ st hok n hn with hold | hpref
      · exact hswf.defsUndefined n hold
      · -- n.name has reserved prefix; reservedFresh's contrapositive gives isNone.
        rw [Option.isNone_iff_eq_none]
        cases h : ρ₀.store n with
        | none => rfl
        | some v =>
          exfalso
          have hsome : (ρ₀.store n).isSome := by rw [h]; rfl
          exact hswf.reservedFresh n hsome loopElimReservedPrefix h_loop_reserved hpref
    case reservedFresh =>
      -- Weaker than the input since `reserved.erase` is a subset.
      intro n hsome p hp_mem
      exact hswf.reservedFresh n hsome p (List.mem_of_mem_erase hp_mem)
    case definedVarsNotReserved =>
      -- Output's `definedVarsNotReserved` for `reserved.erase loopElimReservedPrefix`.
      -- Each n in transform's definedVars is either in source's definedVars
      -- or has the `loopElimReservedPrefix` prefix (per `mem_definedVars_stmtResult`).
      intro n hn p hp_mem
      rcases mem_definedVars_stmtResult σ st hok n hn with hold | hpref
      · -- Source's defs don't have any prefix from `reserved`, hence not from
        -- `reserved.erase loopElimReservedPrefix` (a subset).
        exact hswf.definedVarsNotReserved n hold p (List.mem_of_mem_erase hp_mem)
      · -- n has `loopElimReservedPrefix` as prefix.  Suppose for contradiction
        -- p is also a prefix of n.  Then since both `p` and `loopElimReservedPrefix`
        -- are prefixes of `n.name`, one of them is a prefix of the other.
        -- But `h_pd` says they're prefix-disjoint — contradiction.
        intro h_p_prefix
        have ⟨h_pd_left, h_pd_right⟩ := h_pd p hp_mem
        -- Two `Char`-list prefixes of the same list: one is a prefix of the other.
        have h_pp_or : p.toList.isPrefixOf loopElimReservedPrefix.toList = Bool.true ∨
                      loopElimReservedPrefix.toList.isPrefixOf p.toList = Bool.true := by
          -- Use the helper: two prefixes of the same list are comparable.
          have h1 : p.toList.IsPrefix n.name.toList := by
            rw [List.isPrefixOf_iff_prefix] at h_p_prefix; exact h_p_prefix
          have h2 : loopElimReservedPrefix.toList.IsPrefix n.name.toList := by
            rw [List.isPrefixOf_iff_prefix] at hpref; exact hpref
          rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
          · left; rw [List.isPrefixOf_iff_prefix]; exact h
          · right; rw [List.isPrefixOf_iff_prefix]; exact h
        rcases h_pp_or with h | h
        · exact h_pd_left h
        · exact h_pd_right h
    case funcDeclNamesNotReserved =>
      -- The transform doesn't introduce new funcDecls (they live in source's body
      -- already), so any funcDeclName in the output was a funcDeclName in the source.
      intro n hn p hp_mem
      have h_in_src := funcDeclNames_stmtResult_subset σ st hok n hn
      exact hswf.funcDeclNamesNotReserved n h_in_src p (List.mem_of_mem_erase hp_mem)
    case defUseOk =>
      exact defUseWellFormed_stmtResult σ st hok reserved
        h_loop_reserved hswf'

end Core.LoopElim

end -- public section
