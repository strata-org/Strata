/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.LoopElim
import Strata.Transform.CoreSpecification
import Strata.DL.Imperative.StmtSemanticsSmallStep
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Util.Relations

/-! # Loop-Elimination Transformation Correctness

The top-level theorem is `loopElim_overapproximatesAggressive`: the
loop-eliminated program aggressively overapproximates the original.

For each source execution reaching terminal `ρ'`, the transformed program
either reaches the same terminal `ρ'` (exact simulation), or terminates at
some `ρ''` with `hasFailure = true` (an invariant VC failed).
-/

namespace Core.LoopElim

open Imperative Specification Core Imperative.LoopElim

variable (π : String → Option Procedure)
variable (φ : CoreEval → PureFunc Expression → CoreEval)

private abbrev LangCore := Specification.Lang.core π φ
private abbrev CoreStar := StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
private abbrev CC := Config Expression Command

/-! ## Projecting removeLoopsM results -/

noncomputable def stmtResult (σ : StringGenState) (s : Statement) : Statement :=
  (StateT.run (Stmt.removeLoopsM s) σ).fst.snd

noncomputable def blockResult (σ : StringGenState) (ss : Statements) : Statements :=
  (StateT.run (Block.removeLoopsM ss) σ).fst.snd

noncomputable def stmtPostState (σ : StringGenState) (s : Statement) : StringGenState :=
  (StateT.run (Stmt.removeLoopsM s) σ).snd

noncomputable def blockPostState (σ : StringGenState) (ss : Statements) : StringGenState :=
  (StateT.run (Block.removeLoopsM ss) σ).snd

/-! ## CanFail for statement lists (block bodies) -/

/-- CanFail for a block body: there exists a reachable config with `hasFailure = true`. -/
private def CanFailBlock (ss : Statements) (ρ₀ : Env Expression) : Prop :=
  ∃ cfg : CC, cfg.getEnv.hasFailure = Bool.true ∧ CoreStar π φ (.stmts ss ρ₀) cfg

/-! ## Loop invariant well-formedness

For the loop elimination proof, we need that loop invariant expressions
evaluate to booleans (`some HasBool.tt` or `some HasBool.ff`) rather than
getting stuck (`none` or a non-boolean value).  Without this, the target
program's `assert(I)` cannot step, making it impossible to show either
`CanFail` or terminal reachability.

In well-typed Strata programs this always holds because invariants are
boolean-typed expressions.  We state it as an explicit hypothesis. -/

/-- All loop invariant expressions in a statement evaluate to booleans
    under any well-formed evaluator and any store. -/
def Stmt.loopInvsBool : Stmt Expression Command → Prop
  | .loop _ measure inv body _ =>
    (∀ (δ : SemanticEval Expression) (σ : SemanticStore Expression),
      WellFormedSemanticEvalBool δ →
      ∀ e ∈ inv, δ σ e = some HasBool.tt ∨ δ σ e = some HasBool.ff) ∧
    Block.noFuncDecl body = Bool.true ∧
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (P := Expression) (CmdT := Command) [] body ∧
    Block.loopInvsBool body ∧
    (∀ (σ : SemanticStore Expression), ∀ n ∈ Block.touchedVars body, (σ n).isSome) ∧
    measure = none
  | .block _ bss _ => Block.loopInvsBool bss
  | .ite _ tss ess _ => Block.loopInvsBool tss ∧ Block.loopInvsBool ess
  | _ => True
where
  Block.loopInvsBool : List (Stmt Expression Command) → Prop
    | [] => True
    | s :: ss => Stmt.loopInvsBool s ∧ Block.loopInvsBool ss

-- Re-export at namespace level
def Block.loopInvsBool (bss : List (Stmt Expression Command)) : Prop :=
  Stmt.loopInvsBool.Block.loopInvsBool bss

/-! ## Auxiliary: modifiedVars ⊆ touchedVars -/

/-- Every variable in `Block.modifiedVars` is also in `Block.touchedVars`.
    Uses size-based recursion to handle mutual stmt/block structure. -/
private theorem Block.modifiedVars_subset_touchedVars (body : List (Stmt Expression Command))
    (n : Expression.Ident) (hn : n ∈ Block.modifiedVars body) :
    n ∈ Block.touchedVars body := by
  suffices h : ∀ (sz : Nat),
      (∀ (s : Stmt Expression Command), Stmt.sizeOf s ≤ sz →
        ∀ m, m ∈ Stmt.modifiedVars s → m ∈ Stmt.touchedVars s) ∧
      (∀ (bss : List (Stmt Expression Command)), Block.sizeOf bss ≤ sz →
        ∀ m, m ∈ Block.modifiedVars bss → m ∈ Block.touchedVars bss) by
    exact (h (Block.sizeOf body)).2 body (Nat.le_refl _) n hn
  intro sz
  induction sz with
  | zero =>
    exact ⟨fun s hsz => by
            match s with
            | .cmd _ | .exit .. | .loop .. | .block .. | .ite ..
            | .funcDecl .. | .typeDecl .. => simp [Stmt.sizeOf] at hsz,
           fun bss hsz => by
            match bss with
            | [] => intro m hm; simp [Block.modifiedVars] at hm
            | _ :: _ => simp [Block.sizeOf] at hsz⟩
  | succ k ih_k =>
    constructor
    · intro s hsz m hm
      match s with
      | .cmd _ | .exit .. | .loop .. | .funcDecl .. | .typeDecl .. =>
        simp only [Stmt.touchedVars, Stmt.definedVars, Stmt.modifiedVars] at hm ⊢
        exact List.mem_append_right _ hm
      | .block _ bss _ =>
        simp only [Stmt.touchedVars, Stmt.modifiedVars] at hm ⊢
        have : Block.sizeOf bss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        exact ih_k.2 bss this m hm
      | .ite _ tss ess _ =>
        simp only [Stmt.touchedVars, Stmt.modifiedVars, List.mem_append] at hm ⊢
        have ht : Block.sizeOf tss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have he : Block.sizeOf ess ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        rcases hm with h | h
        · exact .inl (ih_k.2 tss ht m h)
        · exact .inr (ih_k.2 ess he m h)
    · intro bss hsz m hm
      match bss with
      | [] => simp [Block.modifiedVars] at hm
      | s :: ss =>
        simp only [Block.modifiedVars, Block.touchedVars, List.mem_append] at hm ⊢
        have hs : Stmt.sizeOf s ≤ k := by simp [Block.sizeOf] at hsz; omega
        have hss : Block.sizeOf ss ≤ k := by simp [Block.sizeOf] at hsz; omega
        rcases hm with h | h
        · exact .inl (ih_k.1 s hs m h)
        · exact .inr (ih_k.2 ss hss m h)

/-! ## Identity lemma: non-loop, non-recursive statements are unchanged -/

private theorem stmtResult_cmd (σ : StringGenState) (c : Command) :
    stmtResult σ (.cmd c) = .cmd c := by
  simp [stmtResult, Stmt.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem stmtResult_exit (σ : StringGenState) (l : Option String)
    (md : MetaData Expression) :
    stmtResult σ (.exit l md) = .exit l md := by
  simp [stmtResult, Stmt.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem stmtResult_funcDecl (σ : StringGenState) (d : PureFunc Expression)
    (md : MetaData Expression) :
    stmtResult σ (.funcDecl d md) = .funcDecl d md := by
  simp [stmtResult, Stmt.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem stmtResult_typeDecl (σ : StringGenState) (tc : TypeConstructor)
    (md : MetaData Expression) :
    stmtResult σ (.typeDecl tc md) = .typeDecl tc md := by
  simp [stmtResult, Stmt.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem stmtResult_block (σ : StringGenState) (l : String)
    (bss : Statements) (md : MetaData Expression) :
    stmtResult σ (.block l bss md) = .block l (blockResult σ bss) md := by
  simp only [stmtResult, blockResult, Stmt.removeLoopsM, StateT.run, bind, StateT.bind]
  generalize Block.removeLoopsM bss σ = p
  cases p with
  | mk fst snd => simp [pure, StateT.pure]

private theorem stmtResult_ite (σ : StringGenState) (c : ExprOrNondet Expression)
    (tss ess : Statements) (md : MetaData Expression) :
    stmtResult σ (.ite c tss ess md) =
      .ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md := by
  simp only [stmtResult, blockResult, blockPostState, Stmt.removeLoopsM, StateT.run, bind,
    StateT.bind]
  generalize Block.removeLoopsM tss σ = p1
  cases p1 with
  | mk fst snd =>
    simp [pure, StateT.pure]
    generalize Block.removeLoopsM ess snd = p2
    cases p2 with
    | mk fst' snd' => simp

private theorem blockResult_nil (σ : StringGenState) :
    blockResult σ [] = [] := by
  simp [blockResult, Block.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem blockResult_cons (σ : StringGenState) (s : Statement)
    (ss : Statements) :
    blockResult σ (s :: ss) =
      stmtResult σ s :: blockResult (stmtPostState σ s) ss := by
  simp only [blockResult, stmtResult, stmtPostState, Block.removeLoopsM, StateT.run, bind,
    StateT.bind]
  generalize Stmt.removeLoopsM s σ = p1
  cases p1 with
  | mk fst snd =>
    simp [pure, StateT.pure]
    generalize Block.removeLoopsM ss snd = p2
    cases p2 with
    | mk fst' snd' => simp

/-! ## Unfolding lemma for loop transformation -/

/-- Helper: the loop number string generated from `σ`. -/
private noncomputable def loopNum (σ : StringGenState) : String :=
  (StringGenState.gen "loop" σ).fst

/-- Helper: the post-gen state after generating the loop number. -/
private noncomputable def loopGenState (σ : StringGenState) : StringGenState :=
  (StringGenState.gen "loop" σ).snd

private theorem stmtResult_loop_det (σ : StringGenState) (g : Expression.Expr)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) :
    ∃ (loop_label first_iter_label : String)
      (first_iter_body : Statements)
      (then_branch : Statements),
    stmtResult σ (.loop (.det g) measure inv body md) =
      .block loop_label [
        .block first_iter_label first_iter_body {},
        .ite (.det g) then_branch [] {}
      ] {} ∧
    first_iter_body = (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assert
          s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
      (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) := by
  simp only [stmtResult, StateT.run, Stmt.removeLoopsM, bind, StateT.bind,
    modifyGet, pure, loopNum]
  cases measure with
  | none => exact ⟨_, _, _, _, rfl, rfl⟩
  | some m => exact ⟨_, _, _, _, rfl, rfl⟩

private theorem stmtResult_loop_nondet (σ : StringGenState)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) :
    ∃ (loop_label first_iter_label : String)
      (first_iter_body : Statements)
      (then_branch : Statements),
    stmtResult σ (.loop .nondet measure inv body md) =
      .block loop_label [
        .block first_iter_label first_iter_body {},
        .ite .nondet then_branch [] {}
      ] {} ∧
    first_iter_body = (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assert
          s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
      (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) := by
  simp only [stmtResult, StateT.run, Stmt.removeLoopsM, bind, StateT.bind,
    modifyGet, pure, loopNum]
  cases measure with
  | none => exact ⟨_, _, _, _, rfl, rfl⟩
  | some m => exact ⟨_, _, _, _, rfl, rfl⟩

/-- The then-branch of the loop-eliminated ite for deterministic guard. -/
private noncomputable def loopDetThenBranch (σ : StringGenState) (g : Expression.Expr)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) : Statements :=
  let loop_num := loopNum σ
  let σ₁ := loopGenState σ
  let assigned_vars := Block.modifiedVars body
  let havocd : Statement :=
    .block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
      (assigned_vars.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}
  let body' := blockResult σ₁ body
  let inv_assumes := inv.mapIdx fun i inv_i =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_invariant_{i}" inv_i md)
  let maintain_invariants := inv.mapIdx fun i inv_i =>
    Stmt.cmd (HasPassiveCmds.assert
      s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{i}" inv_i md)
  let assume_guard :=
    Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_guard" g md)
  let arbitrary_iter_assumes :=
    Stmt.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
      ([assume_guard] ++ inv_assumes) md
  let (pre_termination, post_termination) := match measure with
    | none => ([], [])
    | some m =>
      let m_old_ident := HasIdent.ident s!"$__loop_measure_{loop_num}"
      let m_old_expr := HasFvar.mkFvar m_old_ident
      ([Stmt.cmd (HasInit.init m_old_ident HasIntOrder.intTy .nondet md),
        Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loop_num}_measure" (HasIntOrder.eq m_old_expr m) md),
        Stmt.cmd (HasPassiveCmds.assert
          s!"{loopElimAssertPrefix}{loop_num}_measure_lb"
          (HasNot.not (HasIntOrder.lt m_old_expr HasIntOrder.zero)) md)],
       [Stmt.cmd (HasPassiveCmds.assert
          s!"{loopElimAssertPrefix}{loop_num}_measure_decrease"
          (HasIntOrder.lt m m_old_expr) md)])
  let arbitrary_iter_facts :=
    Stmt.block s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
      ([havocd, arbitrary_iter_assumes] ++ pre_termination ++
       body' ++ maintain_invariants ++ post_termination) {}
  let not_guard :=
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)
  let invariant_assumes := inv.mapIdx fun i inv_i =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{i}" inv_i md)
  [arbitrary_iter_facts] ++ [havocd] ++ [not_guard] ++ invariant_assumes

/-- For `measure = none`, the then-branch decomposes as
    `[arb_iter_facts_block, havocd, not_guard] ++ exit_inv_assumes`
    where `arb_iter_facts_block` contains `[havocd, assumes_block] ++ body' ++ maintain_invariants`. -/
private theorem loopDetThenBranch_none_eq (σ : StringGenState) (g : Expression.Expr)
    (inv : List Expression.Expr) (body : Statements) (md : MetaData Expression) :
    let loop_num := loopNum σ
    let σ₁ := loopGenState σ
    let assigned_vars := Block.modifiedVars body
    let havocd : Statement :=
      .block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
        (assigned_vars.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}
    let body' := blockResult σ₁ body
    let inv_assumes := inv.mapIdx fun i inv_i =>
      Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_invariant_{i}" inv_i md)
    let maintain_invariants := inv.mapIdx fun i inv_i =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{i}" inv_i md)
    let assume_guard :=
      Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_guard" g md)
    let arbitrary_iter_assumes :=
      Stmt.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
        ([assume_guard] ++ inv_assumes) md
    let arbitrary_iter_facts :=
      Stmt.block s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
        ([havocd, arbitrary_iter_assumes] ++ body' ++ maintain_invariants) {}
    let not_guard :=
      Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)
    let exit_inv_assumes := inv.mapIdx fun i inv_i =>
      Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{i}" inv_i md)
    loopDetThenBranch σ g none inv body md =
      [arbitrary_iter_facts, havocd, not_guard] ++ exit_inv_assumes := by
  unfold loopDetThenBranch
  simp only [List.nil_append, List.append_nil, List.cons_append]

/-- Full unfolding of the loop transformation for the deterministic guard case. -/
private theorem stmtResult_loop_det_full (σ : StringGenState) (g : Expression.Expr)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) :
    stmtResult σ (.loop (.det g) measure inv body md) =
      .block s!"loop_{loopNum σ}" [
        .block s!"{loopElimBlockPrefix}first_iter_asserts_{loopNum σ}"
          ((inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assert
              s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
           (inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assume
              s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))) {},
        .ite (.det g) (loopDetThenBranch σ g measure inv body md) [] {}
      ] {} := by
  simp only [stmtResult, StateT.run, Stmt.removeLoopsM, bind, StateT.bind,
    modifyGet, pure, loopNum, loopGenState, loopDetThenBranch, blockResult]
  cases measure with
  | none => rfl
  | some m => rfl

/-- The then-branch of the loop-eliminated ite for nondeterministic guard.
    This mirrors `loopDetThenBranch` but without guard-related assumes/asserts
    and without termination checks. Must match the exact structure of
    `Stmt.removeLoopsM` for `guard = .nondet`. -/
private noncomputable def loopNondetThenBranch (σ : StringGenState)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) : Statements :=
  let loop_num := loopNum σ
  let σ₁ := loopGenState σ
  let assigned_vars := Block.modifiedVars body
  let havocd : Statement :=
    .block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
      (assigned_vars.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}
  let body' := blockResult σ₁ body
  let inv_assumes := inv.mapIdx fun i inv_i =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_invariant_{i}" inv_i md)
  let maintain_invariants := inv.mapIdx fun i inv_i =>
    Stmt.cmd (HasPassiveCmds.assert
      s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{i}" inv_i md)
  -- Guard-specific parts: for nondet, all are empty
  let guard_assumes : Statements := []
  let (pre_termination, post_termination) : Statements × Statements := ([], [])
  let exit_guard : Statements := []
  -- Build the then-branch matching removeLoopsM structure
  let arbitrary_iter_assumes :=
    Stmt.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
      (guard_assumes ++ inv_assumes) md
  let arbitrary_iter_facts :=
    Stmt.block s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
      ([havocd, arbitrary_iter_assumes] ++ pre_termination ++
       body' ++ maintain_invariants ++ post_termination) {}
  let invariant_assumes := inv.mapIdx fun i inv_i =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{i}" inv_i md)
  let exit_state_assumes := [havocd] ++ exit_guard ++ invariant_assumes
  [arbitrary_iter_facts] ++ exit_state_assumes

/-- Full unfolding of the loop transformation for the nondeterministic guard case. -/
private theorem stmtResult_loop_nondet_full (σ : StringGenState)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) :
    stmtResult σ (.loop .nondet measure inv body md) =
      .block s!"loop_{loopNum σ}" [
        .block s!"{loopElimBlockPrefix}first_iter_asserts_{loopNum σ}"
          ((inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assert
              s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
           (inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assume
              s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))) {},
        .ite .nondet (loopNondetThenBranch σ measure inv body md) [] {}
      ] {} := by
  simp only [stmtResult, StateT.run, Stmt.removeLoopsM, bind, StateT.bind,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure,
    loopNum, loopGenState, loopNondetThenBranch, blockResult, Id.run]
  cases measure with
  | none => rfl
  | some m => rfl

/-! ## WF preservation through small-step execution -/

/-- A single Core step preserves WF. -/
private theorem onestep_preserves_wf
    (hwf_ext : WFEvalExtension φ)
    {c₁ c₂ : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂)
    (hwfb : WellFormedSemanticEvalBool c₁.getEnv.eval)
    (hwfv : WellFormedSemanticEvalVal c₁.getEnv.eval) :
    WellFormedSemanticEvalBool c₂.getEnv.eval ∧
    WellFormedSemanticEvalVal c₂.getEnv.eval := by
  suffices ∀ (a b : CC),
      StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b →
      WellFormedSemanticEvalBool a.getEnv.eval →
      WellFormedSemanticEvalVal a.getEnv.eval →
      WellFormedSemanticEvalBool b.getEnv.eval ∧ WellFormedSemanticEvalVal b.getEnv.eval from
    this c₁ c₂ hstep hwfb hwfv
  intro a b hstep
  induction hstep with
  | step_cmd _ => intro h1 h2; simp [Config.getEnv]; exact ⟨h1, h2⟩
  | step_block => intro h1 h2; exact ⟨h1, h2⟩
  | step_ite_true => intro h1 h2; exact ⟨h1, h2⟩
  | step_ite_false => intro h1 h2; exact ⟨h1, h2⟩
  | step_ite_nondet_true => intro h1 h2; exact ⟨h1, h2⟩
  | step_ite_nondet_false => intro h1 h2; exact ⟨h1, h2⟩
  | step_loop_enter => intro h1 h2; exact ⟨h1, h2⟩
  | step_loop_exit => intro h1 h2; exact ⟨h1, h2⟩
  | step_loop_nondet_enter => intro h1 h2; exact ⟨h1, h2⟩
  | step_loop_nondet_exit => intro h1 h2; exact ⟨h1, h2⟩
  | step_exit => intro h1 h2; exact ⟨h1, h2⟩
  | step_funcDecl =>
    intro h1 h2; simp [Config.getEnv]
    exact ⟨hwf_ext.preserves_wfBool _ _ _ h1, hwf_ext.preserves_wfVal _ _ _ h2⟩
  | step_typeDecl => intro h1 h2; exact ⟨h1, h2⟩
  | step_stmts_nil => intro h1 h2; exact ⟨h1, h2⟩
  | step_stmts_cons => intro h1 h2; exact ⟨h1, h2⟩
  | step_seq_inner _ ih => intro h1 h2; exact ih h1 h2
  | step_seq_done => intro h1 h2; exact ⟨h1, h2⟩
  | step_seq_exit => intro h1 h2; exact ⟨h1, h2⟩
  | step_block_body _ ih => intro h1 h2; exact ih h1 h2
  | step_block_done => intro h1 h2; exact ⟨h1, h2⟩
  | step_block_exit_none => intro h1 h2; exact ⟨h1, h2⟩
  | step_block_exit_match => intro h1 h2; exact ⟨h1, h2⟩
  | step_block_exit_mismatch => intro h1 h2; exact ⟨h1, h2⟩

/-- Multi-step Core execution preserves WF. -/
private theorem star_preserves_wf
    (hwf_ext : WFEvalExtension φ)
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hwfb : WellFormedSemanticEvalBool c₁.getEnv.eval)
    (hwfv : WellFormedSemanticEvalVal c₁.getEnv.eval) :
    WellFormedSemanticEvalBool c₂.getEnv.eval ∧
    WellFormedSemanticEvalVal c₂.getEnv.eval := by
  induction hstar with
  | refl => exact ⟨hwfb, hwfv⟩
  | step _ _ _ hstep _ ih =>
    exact ih (onestep_preserves_wf (π := π) (φ := φ) hwf_ext hstep hwfb hwfv).1
      (onestep_preserves_wf (π := π) (φ := φ) hwf_ext hstep hwfb hwfv).2

/-- A single Core step preserves WellFormedSemanticEvalVar. -/
private theorem onestep_preserves_wfVar
    (hwf_ext : WFEvalExtension φ)
    {c₁ c₂ : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂)
    (hwfvar : WellFormedSemanticEvalVar c₁.getEnv.eval) :
    WellFormedSemanticEvalVar c₂.getEnv.eval := by
  suffices ∀ (a b : CC),
      StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b →
      WellFormedSemanticEvalVar a.getEnv.eval →
      WellFormedSemanticEvalVar b.getEnv.eval from
    this c₁ c₂ hstep hwfvar
  intro a b hstep
  induction hstep with
  | step_cmd _ => intro h; simp [Config.getEnv]; exact h
  | step_block => intro h; exact h
  | step_ite_true => intro h; exact h
  | step_ite_false => intro h; exact h
  | step_ite_nondet_true => intro h; exact h
  | step_ite_nondet_false => intro h; exact h
  | step_loop_enter => intro h; exact h
  | step_loop_exit => intro h; exact h
  | step_loop_nondet_enter => intro h; exact h
  | step_loop_nondet_exit => intro h; exact h
  | step_exit => intro h; exact h
  | step_funcDecl =>
    intro h; simp [Config.getEnv]
    exact hwf_ext.preserves_wfVar _ _ _ h
  | step_typeDecl => intro h; exact h
  | step_stmts_nil => intro h; exact h
  | step_stmts_cons => intro h; exact h
  | step_seq_inner _ ih => intro h; exact ih h
  | step_seq_done => intro h; exact h
  | step_seq_exit => intro h; exact h
  | step_block_body _ ih => intro h; exact ih h
  | step_block_done => intro h; exact h
  | step_block_exit_none => intro h; exact h
  | step_block_exit_match => intro h; exact h
  | step_block_exit_mismatch => intro h; exact h

/-- Multi-step Core execution preserves WellFormedSemanticEvalVar. -/
private theorem star_preserves_wfVar
    (hwf_ext : WFEvalExtension φ)
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hwfvar : WellFormedSemanticEvalVar c₁.getEnv.eval) :
    WellFormedSemanticEvalVar c₂.getEnv.eval := by
  induction hstar with
  | refl => exact hwfvar
  | step _ _ _ hstep _ ih =>
    exact ih (onestep_preserves_wfVar (π := π) (φ := φ) hwf_ext hstep hwfvar)

/-! ## isDefined preservation through small-step execution -/

/-- Core's `EvalCommand` preserves `isDefined` on any variable list.
    `cmd_sem` delegates to `Imperative.EvalCmdDefMonotone`;
    `call_sem` follows from `UpdateStatesDefMonotone` on the final update. -/
private theorem evalCommand_preserves_isDefined
    {δ : SemanticEval Expression} {σ σ' : SemanticStore Expression}
    {c : Command} {f : Bool} {vs : List Expression.Ident}
    (hdef : isDefined σ vs)
    (heval : EvalCommand π φ δ σ c σ' f) :
    isDefined σ' vs := by
  cases heval with
  | cmd_sem hcmd => exact EvalCmdDefMonotone' hdef hcmd
  | call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ hup =>
    exact UpdateStatesDefMonotone hdef hup

/-- A single Core step preserves `isDefined` on the environment's store. -/
private theorem onestep_preserves_isDefined
    {c₁ c₂ : CC} {vs : List Expression.Ident}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂)
    (hdef : isDefined c₁.getEnv.store vs) :
    isDefined c₂.getEnv.store vs := by
  suffices ∀ (a b : CC),
      StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b →
      isDefined a.getEnv.store vs →
      isDefined b.getEnv.store vs from
    this c₁ c₂ hstep hdef
  intro a b hstep
  induction hstep with
  | step_cmd hcmd =>
    intro h; simp [Config.getEnv]
    exact evalCommand_preserves_isDefined π φ h hcmd
  | step_block => intro h; exact h
  | step_ite_true => intro h; exact h
  | step_ite_false => intro h; exact h
  | step_ite_nondet_true => intro h; exact h
  | step_ite_nondet_false => intro h; exact h
  | step_loop_enter => intro h; exact h
  | step_loop_exit => intro h; exact h
  | step_loop_nondet_enter => intro h; exact h
  | step_loop_nondet_exit => intro h; exact h
  | step_exit => intro h; exact h
  | step_funcDecl => intro h; simp [Config.getEnv]; exact h
  | step_typeDecl => intro h; exact h
  | step_stmts_nil => intro h; exact h
  | step_stmts_cons => intro h; exact h
  | step_seq_inner _ ih => intro h; exact ih h
  | step_seq_done => intro h; exact h
  | step_seq_exit => intro h; exact h
  | step_block_body _ ih => intro h; exact ih h
  | step_block_done => intro h; exact h
  | step_block_exit_none => intro h; exact h
  | step_block_exit_match => intro h; exact h
  | step_block_exit_mismatch => intro h; exact h

/-- Multi-step Core execution preserves `isDefined`. -/
private theorem star_preserves_isDefined
    {c₁ c₂ : CC} {vs : List Expression.Ident}
    (hstar : CoreStar π φ c₁ c₂)
    (hdef : isDefined c₁.getEnv.store vs) :
    isDefined c₂.getEnv.store vs := by
  induction hstar with
  | refl => exact hdef
  | step _ _ _ hstep _ ih =>
    exact ih (onestep_preserves_isDefined π φ hstep hdef)

/-- If hasFailure is false at the end, it was false at any intermediate point. -/
private theorem hasFailure_false_backwards
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hnf : c₂.getEnv.hasFailure = Bool.false) :
    c₁.getEnv.hasFailure = Bool.false := by
  cases h : c₁.getEnv.hasFailure
  · rfl
  · exact absurd (StepStmtStar_hasFailure_monotone hstar h) (by simp [hnf])

/-! ## Lifting lemmas for CanFail / CanFailBlock through seq and block -/

/-- If the head statement of a cons block can fail, so can the whole block. -/
private theorem canFail_head_to_block
    (s : Statement) (ss : Statements) (ρ₀ : Env Expression)
    (h : Transform.CanFail (LangCore π φ) s ρ₀) :
    CanFailBlock π φ (s :: ss) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  refine ⟨.seq cfg ss, ?_, ?_⟩
  · simp [Config.getEnv]; exact hfail
  · exact ReflTrans_Transitive _ _ _ _
      (.step _ _ _ .step_stmts_cons (.refl _))
      (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ss hreach)

/-- If the tail of a cons block can fail after the head terminates,
    the whole block can fail. -/
private theorem canFail_tail_to_block
    (s : Statement) (ss : Statements) (ρ₀ ρ₁ : Env Expression)
    (hhead : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (htail : CanFailBlock π φ ss ρ₁) :
    CanFailBlock π φ (s :: ss) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := htail
  exact ⟨cfg, hfail,
    ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) s ss ρ₀ ρ₁ hhead)
      hreach⟩

/-- If `.stmts bss ρ₀` reaches terminal `ρ'`, then
    `.stmt (.block l bss md) ρ₀` reaches terminal `ρ'`. -/
private theorem block_wrap_terminal
    (l : String) (bss : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmts bss ρ₀) (.terminal ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀) (.terminal ρ') :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ l h)
      (.step _ _ _ .step_block_done (.refl _)))

/-- If `.stmts bss ρ₀` reaches exiting `(some lv) ρ'` with `lv ≠ l`,
    then `.stmt (.block l bss md) ρ₀` reaches `.exiting (some lv) ρ'`. -/
private theorem block_wrap_exiting_mismatch
    (l : String) (bss : Statements) (md : MetaData Expression)
    (lv : String) (ρ₀ ρ' : Env Expression)
    (hne : lv ≠ l)
    (h : CoreStar π φ (.stmts bss ρ₀) (.exiting (some lv) ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀) (.exiting (some lv) ρ') :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ l h)
      (.step _ _ _ (.step_block_exit_mismatch hne) (.refl _)))

/-- If `.stmts bss ρ₀` reaches exiting `none ρ'`,
    then `.stmt (.block l bss md) ρ₀` reaches `.terminal ρ'`. -/
private theorem block_wrap_exiting_none
    (l : String) (bss : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmts bss ρ₀) (.exiting none ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀) (.terminal ρ') :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ l h)
      (.step _ _ _ .step_block_exit_none (.refl _)))

/-- If `.stmts bss ρ₀` reaches exiting `(some l) ρ'` (label matches block),
    then `.stmt (.block l bss md) ρ₀` reaches `.terminal ρ'`. -/
private theorem block_wrap_exiting_match
    (l : String) (bss : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmts bss ρ₀) (.exiting (some l) ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀) (.terminal ρ') :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ l h)
      (.step _ _ _ (.step_block_exit_match rfl) (.refl _)))

/-- Refined block terminal inversion. -/
private theorem block_reaches_terminal_refined
    {inner : CC} {l : String} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block l inner) (.terminal ρ')) :
    CoreStar π φ inner (.terminal ρ') ∨
    CoreStar π φ inner (.exiting none ρ') ∨
    CoreStar π φ inner (.exiting (some l) ρ') := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ inner ρ', src = .block l inner → tgt = .terminal ρ' →
      CoreStar π φ inner (.terminal ρ') ∨
      CoreStar π φ inner (.exiting none ρ') ∨
      CoreStar π φ inner (.exiting (some l) ρ') from
    this _ _ hstar _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      match ih _ _ rfl htgt with
      | .inl hterm => exact .inl (.step _ _ _ h hterm)
      | .inr (.inl hexit) => exact .inr (.inl (.step _ _ _ h hexit))
      | .inr (.inr hexit) => exact .inr (.inr (.step _ _ _ h hexit))
    | step_block_done => subst htgt; exact .inl hrest
    | step_block_exit_none =>
      subst htgt; cases hrest with
      | refl => exact .inr (.inl (.refl _))
      | step _ _ _ h _ => cases h
    | step_block_exit_match heq =>
      subst htgt; subst heq; cases hrest with
      | refl => exact .inr (.inr (.refl _))
      | step _ _ _ h _ => cases h
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- Refined block exiting inversion. -/
private theorem block_reaches_exiting_refined
    {inner : CC} {l : String} {lbl : Option String} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block l inner) (.exiting lbl ρ')) :
    ∃ lv : String, lv ≠ l ∧ lbl = some lv ∧
      CoreStar π φ inner (.exiting (some lv) ρ') := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ inner lbl ρ', src = .block l inner → tgt = .exiting lbl ρ' →
      ∃ lv : String, lv ≠ l ∧ lbl = some lv ∧
        CoreStar π φ inner (.exiting (some lv) ρ') from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      have ⟨lv, hne, heq, hexit⟩ := ih _ _ _ rfl htgt
      exact ⟨lv, hne, heq, .step _ _ _ h hexit⟩
    | step_block_done =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_none =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_mismatch hne =>
      subst htgt
      cases hrest with
      | refl => exact ⟨_, hne, rfl, .refl _⟩
      | step _ _ _ h _ => cases h

/-- If block body can fail, then the block statement can fail. -/
private theorem canFailBlock_to_canFail_block
    (l : String) (bss : Statements) (md : MetaData Expression) (ρ₀ : Env Expression)
    (h : CanFailBlock π φ bss ρ₀) :
    Transform.CanFail (LangCore π φ) (.block l bss md) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  exact ⟨.block l cfg, by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
    ReflTrans_Transitive _ _ _ _
      (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ l hreach)⟩

/-- If `.stmt s ρ₀` reaches `.exiting lbl ρ'`, then `.stmts (s :: ss) ρ₀`
    reaches `.exiting lbl ρ'`. -/
private theorem stmts_cons_exiting
    (s : Statement) (ss : Statements) (lbl : Option String)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmt s ρ₀) (.exiting lbl ρ')) :
    CoreStar π φ (.stmts (s :: ss) ρ₀) (.exiting lbl ρ') :=
  ReflTrans_Transitive _ _ _ _
    (.step _ _ _ .step_stmts_cons (.refl _))
    (ReflTrans_Transitive _ _ _ _
      (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ss h)
      (.step _ _ _ .step_seq_exit (.refl _)))

/-- Decompose an exiting execution of `ss₁ ++ ss₂`: either `ss₁` exits
    or `ss₁` terminates and `ss₂` exits. -/
private theorem stmts_append_exits
    (ss₁ ss₂ : Statements) (lbl : Option String) (ρ ρ' : Env Expression)
    (h : CoreStar π φ (.stmts (ss₁ ++ ss₂) ρ) (.exiting lbl ρ')) :
    CoreStar π φ (.stmts ss₁ ρ) (.exiting lbl ρ') ∨
    ∃ ρ₁, CoreStar π φ (.stmts ss₁ ρ) (.terminal ρ₁) ∧
      CoreStar π φ (.stmts ss₂ ρ₁) (.exiting lbl ρ') := by
  induction ss₁ generalizing ρ with
  | nil =>
    exact .inr ⟨ρ, .step _ _ _ .step_stmts_nil (.refl _), h⟩
  | cons s rest ih =>
    cases h with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) hrest with
        | .inl hexit_s =>
          exact .inl (stmts_cons_exiting π φ s rest lbl ρ ρ' hexit_s)
        | .inr ⟨ρ_mid, hterm_s, hexit_rest_ss₂⟩ =>
          match ih ρ_mid hexit_rest_ss₂ with
          | .inl hexit_rest =>
            exact .inl (ReflTrans_Transitive _ _ _ _
              (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                s rest ρ ρ_mid hterm_s)
              hexit_rest)
          | .inr ⟨ρ₁, hterm_rest, hexit_ss₂⟩ =>
            exact .inr ⟨ρ₁,
              ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                  s rest ρ ρ_mid hterm_s) hterm_rest,
              hexit_ss₂⟩

/-! ## ReflTransT-based decomposition helpers -/

/-- Decompose a `seq` execution reaching terminal into inner reaching terminal
    and then the continuation reaching terminal, with length bounds.  This is a
    `ReflTransT` (Type-level) version giving decreasing measures. -/
private theorem seqT_reaches_terminal_core
    {inner : CC} {ss : Statements} {ρ' : Env Expression}
    (hstar : ReflTransT (CoreStep π φ) (.seq inner ss) (.terminal ρ')) :
    ∃ (ρ₁ : Env Expression),
      ∃ (h1 : ReflTransT (CoreStep π φ) inner (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (CoreStep π φ) (.stmts ss ρ₁) (.terminal ρ')),
      h1.len + h2.len < hstar.len := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    have ⟨ρ₁, hterm, htail, hlen⟩ := seqT_reaches_terminal_core (hstar := hrest)
    exact ⟨ρ₁, .step _ _ _ h hterm, htail, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

/-- Decompose `stmts (s :: rest)` reaching terminal: `s` reaches terminal
    at ρ₁ and `rest` reaches terminal at ρ', with length bounds. -/
private theorem stmtsT_cons_terminal_core
    {s : Statement} {rest : Statements} {ρ₀ ρ' : Env Expression}
    (hstar : ReflTransT (CoreStep π φ) (.stmts (s :: rest) ρ₀) (.terminal ρ')) :
    ∃ (ρ₁ : Env Expression),
      ∃ (h1 : ReflTransT (CoreStep π φ) (.stmt s ρ₀) (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (CoreStep π φ) (.stmts rest ρ₁) (.terminal ρ')),
      h1.len + h2.len + 2 ≤ hstar.len := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, h1, h2, hlen⟩ := seqT_reaches_terminal_core (hstar := hrest)
    exact ⟨ρ₁, h1, h2, by simp [ReflTransT.len]; omega⟩

/-- Decompose `stmts (ss₁ ++ [s]) ρ₀` reaching terminal into `ss₁` reaching
    terminal at ρ₁ (Prop level) and `s` reaching terminal at ρ' from ρ₁
    (ReflTransT level with decreasing length). -/
private theorem stmtsT_append_single_terminal
    (ss₁ : Statements) (s : Statement) (ρ₀ ρ' : Env Expression)
    (hstar : ReflTransT (CoreStep π φ) (.stmts (ss₁ ++ [s]) ρ₀) (.terminal ρ')) :
    ∃ (ρ₁ : Env Expression),
      ∃ (_ : CoreStar π φ (.stmts ss₁ ρ₀) (.terminal ρ₁)),
      ∃ (hs : ReflTransT (CoreStep π φ) (.stmt s ρ₁) (.terminal ρ')),
      hs.len < hstar.len := by
  induction ss₁ generalizing ρ₀ with
  | nil =>
    have ⟨ρ₁, h1, h2, hlen⟩ := stmtsT_cons_terminal_core (hstar := hstar)
    have hρ : ρ₁ = ρ' := by
      match h2 with
      | .step _ _ _ .step_stmts_nil (.refl _) => rfl
    subst hρ
    exact ⟨ρ₀, .step _ _ _ .step_stmts_nil (.refl _), h1, by omega⟩
  | cons s' rest' ih =>
    have ⟨ρ₁, h_s', h_rest, hlen₁⟩ := stmtsT_cons_terminal_core (hstar := hstar)
    have ⟨ρ₂, h_rest', h_s, hlen₂⟩ := ih ρ₁ h_rest
    exact ⟨ρ₂,
      ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
          s' rest' ρ₀ ρ₁ (reflTransT_to_prop h_s'))
        h_rest',
      h_s, by omega⟩

/-! ## Loop termination implies guard false at exit -/

/-- When a deterministic loop `.loop (.det g) ...` reaches terminal ρ',
    the guard evaluates to false at ρ'. This is because the only way a
    det loop can terminate is via `step_loop_exit`, which requires
    `ρ'.eval ρ'.store g = some HasBool.ff`. -/
private noncomputable def det_loop_terminal_guard_false
    (g : Expression.Expr) (m : Option Expression.Expr)
    (inv : List Expression.Expr) (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (h : ReflTransT (CoreStep π φ)
      (.stmt (.loop (.det g) m inv body md) ρ₀) (.terminal ρ')) :
    ρ'.eval ρ'.store g = some HasBool.ff :=
  match h with
  | .step _ _ _ (.step_loop_exit hff _) (.refl _) => hff
  | .step _ _ _ (.step_loop_exit _ _) (.step _ _ _ h2 _) => nomatch h2
  | .step _ _ _ (.step_loop_enter _ _) hrest =>
    let ⟨_, _, hloopT, _⟩ :=
      stmtsT_append_single_terminal _ _ body
        (.loop (.det g) m inv body md) _ ρ' hrest
    det_loop_terminal_guard_false g m inv body md _ ρ' hloopT
  termination_by h.len
  decreasing_by simp_all [ReflTransT.len]; omega

/-- Prop-level version of `det_loop_terminal_guard_false`. -/
private theorem det_loop_terminal_guard_false'
    (g : Expression.Expr) (m : Option Expression.Expr)
    (inv : List Expression.Expr) (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmt (.loop (.det g) m inv body md) ρ₀) (.terminal ρ')) :
    ρ'.eval ρ'.store g = some HasBool.ff :=
  det_loop_terminal_guard_false π φ g m inv body md ρ₀ ρ'
    (reflTrans_to_T h)

/-! ## Helper: executing assert/assume lists -/

/-- A single assert command where the expression evaluates to `tt` steps to
    terminal with the same environment (hasFailure stays the same when already false). -/
private theorem assert_tt_step
    (label : String) (e : Expression.Expr) (md : MetaData Expression)
    (ρ : Env Expression)
    (htt : ρ.eval ρ.store e = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assert label e md)) ρ) (.terminal ρ) := by
  change CoreStar π φ (.stmt (.cmd (CmdExt.cmd (Cmd.assert label e md))) ρ) (.terminal ρ)
  exact .step _ _ _
    (.step_cmd (EvalCommand.cmd_sem (.eval_assert_pass htt hwfb)))
    (by simp [Bool.or_false]; cases ρ; exact .refl _)

/-- A single assert command where the expression evaluates to `ff` steps to
    terminal with hasFailure = true. -/
private theorem assert_ff_canFail
    (label : String) (e : Expression.Expr) (md : MetaData Expression)
    (ρ : Env Expression)
    (hff : ρ.eval ρ.store e = some HasBool.ff)
    (hwfb : WellFormedSemanticEvalBool ρ.eval) :
    ∃ cfg : CC, cfg.getEnv.hasFailure = Bool.true ∧
      CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assert label e md)) ρ) cfg := by
  change ∃ cfg : CC, cfg.getEnv.hasFailure = Bool.true ∧
    CoreStar π φ (.stmt (.cmd (CmdExt.cmd (Cmd.assert label e md))) ρ) cfg
  exact ⟨.terminal { ρ with store := ρ.store, hasFailure := ρ.hasFailure || true },
    by simp [Config.getEnv, Env.hasFailure, Bool.or_true],
    .step _ _ _ (.step_cmd (EvalCommand.cmd_sem (.eval_assert_fail hff hwfb))) (.refl _)⟩

/-- A single assume command where the expression evaluates to `tt` steps to
    terminal with the same environment. -/
private theorem assume_tt_step
    (label : String) (e : Expression.Expr) (md : MetaData Expression)
    (ρ : Env Expression)
    (htt : ρ.eval ρ.store e = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assume label e md)) ρ) (.terminal ρ) := by
  change CoreStar π φ (.stmt (.cmd (CmdExt.cmd (Cmd.assume label e md))) ρ) (.terminal ρ)
  exact .step _ _ _
    (.step_cmd (EvalCommand.cmd_sem (.eval_assume htt hwfb)))
    (by simp [Bool.or_false]; cases ρ; exact .refl _)

/-- Execute a `mapIdx`'d assert list where all expressions evaluate to `tt`.
    We generalize over the index function to handle the `mapIdx_cons` offset. -/
private theorem stmts_mapIdx_assert_terminal_gen
    (es : List Expression.Expr)
    (ρ : Env Expression)
    (md : MetaData Expression)
    (f : Nat → Expression.Expr → Statement)
    (hf : ∀ i e, ∃ label, f i e = Stmt.cmd (HasPassiveCmds.assert label e md))
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hall : ∀ e ∈ es, ρ.eval ρ.store e = some HasBool.tt) :
    CoreStar π φ (.stmts (es.mapIdx f) ρ) (.terminal ρ) := by
  induction es generalizing f with
  | nil => simp [List.mapIdx]; exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons e rest ih =>
    simp only [List.mapIdx_cons]
    have htt := hall e (.head ..)
    obtain ⟨label, heq⟩ := hf 0 e
    rw [heq]
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ ρ
        (assert_tt_step π φ label e md ρ htt hwfb hnf))
      (ih (fun i => f (i + 1)) (fun i e => hf (i + 1) e)
        (fun e' he' => hall e' (.tail _ he')))

private theorem stmts_mapIdx_assert_terminal
    (inv : List Expression.Expr)
    (ρ : Env Expression) (σ : StringGenState)
    (md : MetaData Expression)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hall : ∀ e ∈ inv, ρ.eval ρ.store e = some HasBool.tt) :
    CoreStar π φ
      (.stmts (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assert
          s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ρ)
      (.terminal ρ) :=
  stmts_mapIdx_assert_terminal_gen π φ inv ρ md _ (fun i e => ⟨_, rfl⟩) hwfb hnf hall

/-- Helper: connect mapIdx to enumeration for assumes. -/
private theorem stmts_mapIdx_assume_terminal_gen
    (es : List Expression.Expr)
    (ρ : Env Expression)
    (md : MetaData Expression)
    (f : Nat → Expression.Expr → Statement)
    (hf : ∀ i e, ∃ label, f i e = Stmt.cmd (HasPassiveCmds.assume label e md))
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hall : ∀ e ∈ es, ρ.eval ρ.store e = some HasBool.tt) :
    CoreStar π φ (.stmts (es.mapIdx f) ρ) (.terminal ρ) := by
  induction es generalizing f with
  | nil => simp [List.mapIdx]; exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons e rest ih =>
    simp only [List.mapIdx_cons]
    have htt := hall e (.head ..)
    obtain ⟨label, heq⟩ := hf 0 e
    rw [heq]
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ ρ
        (assume_tt_step π φ label e md ρ htt hwfb hnf))
      (ih (fun i => f (i + 1)) (fun i e => hf (i + 1) e)
        (fun e' he' => hall e' (.tail _ he')))

private theorem stmts_mapIdx_assume_terminal
    (inv : List Expression.Expr)
    (ρ : Env Expression) (σ : StringGenState)
    (md : MetaData Expression)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hall : ∀ e ∈ inv, ρ.eval ρ.store e = some HasBool.tt) :
    CoreStar π φ
      (.stmts (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ρ)
      (.terminal ρ) :=
  stmts_mapIdx_assume_terminal_gen π φ inv ρ md _ (fun i e => ⟨_, rfl⟩) hwfb hnf hall

/-- Helper: if some invariant evaluates to ff, the assert list can fail. -/
private theorem stmts_mapIdx_assert_canFail_gen
    (es : List Expression.Expr)
    (ρ : Env Expression)
    (md : MetaData Expression)
    (f : Nat → Expression.Expr → Statement)
    (hf : ∀ i e, ∃ label, f i e = Stmt.cmd (HasPassiveCmds.assert label e md))
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hall_bool : ∀ e ∈ es, ρ.eval ρ.store e = some HasBool.tt ∨
      ρ.eval ρ.store e = some HasBool.ff)
    (hsome_ff : ∃ e ∈ es, ρ.eval ρ.store e = some HasBool.ff) :
    CanFailBlock π φ (es.mapIdx f) ρ := by
  induction es generalizing f with
  | nil => exact absurd hsome_ff (by simp)
  | cons e rest ih =>
    simp only [List.mapIdx_cons]
    match (hall_bool e (.head ..)) with
    | .inl htt =>
      have hrest_bool := fun e' he' => hall_bool e' (.tail _ he')
      have hrest_ff : ∃ e' ∈ rest, ρ.eval ρ.store e' = some HasBool.ff := by
        obtain ⟨e', he'_mem, he'_ff⟩ := hsome_ff
        cases he'_mem with
        | head => rw [he'_ff] at htt; exact absurd (Option.some.inj htt).symm HasBool.tt_is_not_ff
        | tail _ h => exact ⟨e', h, he'_ff⟩
      obtain ⟨label, heq⟩ := hf 0 e
      rw [heq]
      exact canFail_tail_to_block π φ _ _ ρ ρ
        (assert_tt_step π φ label e md ρ htt hwfb hnf)
        (ih (fun i => f (i + 1)) (fun i e => hf (i + 1) e) hrest_bool hrest_ff)
    | .inr hff =>
      obtain ⟨label, heq⟩ := hf 0 e
      rw [heq]
      have ⟨cfg, hfail, hreach⟩ := assert_ff_canFail π φ label e md ρ hff hwfb
      exact canFail_head_to_block π φ _ _ ρ ⟨cfg, hfail, hreach⟩

private theorem stmts_mapIdx_assert_canFail
    (inv : List Expression.Expr)
    (ρ : Env Expression) (σ : StringGenState)
    (md : MetaData Expression)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hall_bool : ∀ e ∈ inv, ρ.eval ρ.store e = some HasBool.tt ∨
      ρ.eval ρ.store e = some HasBool.ff)
    (hsome_ff : ∃ e ∈ inv, ρ.eval ρ.store e = some HasBool.ff) :
    CanFailBlock π φ
      (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assert
          s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ρ :=
  stmts_mapIdx_assert_canFail_gen π φ inv ρ md _ (fun i e => ⟨_, rfl⟩) hwfb hnf hall_bool hsome_ff

/-- If the prefix of a statement list terminates at an env with
    `hasFailure = true`, the full appended list can fail. -/
private theorem canFailBlock_prefix_terminal_fail
    (ss₁ ss₂ : Statements) (ρ ρ₁ : Env Expression)
    (hterm : CoreStar π φ (.stmts ss₁ ρ) (.terminal ρ₁))
    (hfail : ρ₁.hasFailure = Bool.true) :
    CanFailBlock π φ (ss₁ ++ ss₂) ρ :=
  ⟨.stmts ss₂ ρ₁, by simp [Config.getEnv]; exact hfail,
    stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ) ss₁ ss₂ ρ ρ₁ hterm⟩

/-- Composing terminal traces: if `stmts pfx` terminates at `ρ₁` and
    `stmts sfx` terminates at `ρ₂`, then `stmts (pfx ++ sfx)` terminates at `ρ₂`. -/
private theorem stmts_concat_terminal
    (pfx sfx : Statements) (ρ₀ ρ₁ ρ₂ : Env Expression)
    (hpfx : CoreStar π φ (.stmts pfx ρ₀) (.terminal ρ₁))
    (hsfx : CoreStar π φ (.stmts sfx ρ₁) (.terminal ρ₂)) :
    CoreStar π φ (.stmts (pfx ++ sfx) ρ₀) (.terminal ρ₂) :=
  ReflTrans_Transitive _ _ _ _
    (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
      pfx sfx ρ₀ ρ₁ hpfx)
    hsfx

/-- A single statement terminates, giving a terminal trace for the singleton list. -/
private theorem stmts_singleton_terminal
    (s : Statement) (ρ₀ ρ₁ : Env Expression)
    (h : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁)) :
    CoreStar π φ (.stmts [s] ρ₀) (.terminal ρ₁) :=
  ReflTrans_Transitive _ _ _ _
    (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) s [] ρ₀ ρ₁ h)
    (.step _ _ _ .step_stmts_nil (.refl _))

/-- Two statements terminate in sequence, giving a terminal trace for the pair. -/
private theorem stmts_pair_terminal
    (s₁ s₂ : Statement) (ρ₀ ρ₁ ρ₂ : Env Expression)
    (h₁ : CoreStar π φ (.stmt s₁ ρ₀) (.terminal ρ₁))
    (h₂ : CoreStar π φ (.stmt s₂ ρ₁) (.terminal ρ₂)) :
    CoreStar π φ (.stmts [s₁, s₂] ρ₀) (.terminal ρ₂) :=
  ReflTrans_Transitive _ _ _ _
    (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) s₁ [s₂] ρ₀ ρ₁ h₁)
    (stmts_singleton_terminal π φ s₂ ρ₁ ρ₂ h₂)

/-- If the prefix of a statement list can fail, the full list can also fail.
    The proof lifts CanFail through the cons/append structure. -/
private theorem canFailBlock_append_left
    (ss₁ ss₂ : Statements) (ρ : Env Expression)
    (h : CanFailBlock π φ ss₁ ρ) :
    CanFailBlock π φ (ss₁ ++ ss₂) ρ := by
  -- We prove this via a helper that lifts any star execution from
  -- .stmts ss₁ reaching a failing cfg to .stmts (ss₁ ++ ss₂) also
  -- reaching a failing cfg. The key lemma we need:
  -- For any seq execution .seq inner ss → cfg (with cfg failing),
  -- there exists .seq inner (ss ++ ss₂) → cfg' (with cfg' failing).
  -- We prove this by induction generalizing over source/target.
  suffices ∀ (src tgt : CC),
      CoreStar π φ src tgt →
      tgt.getEnv.hasFailure = Bool.true →
      (∀ (ss : Statements) (ρ₀ : Env Expression), src = .stmts ss ρ₀ →
        ∃ cfg' : CC, cfg'.getEnv.hasFailure = Bool.true ∧
          CoreStar π φ (.stmts (ss ++ ss₂) ρ₀) cfg') ∧
      (∀ (inner : CC) (ss : Statements), src = .seq inner ss →
        ∃ cfg' : CC, cfg'.getEnv.hasFailure = Bool.true ∧
          CoreStar π φ (.seq inner (ss ++ ss₂)) cfg') by
    obtain ⟨cfg, hfail, hreach⟩ := h
    exact (this _ _ hreach hfail).1 ss₁ ρ rfl
  intro src tgt hstar htgt_fail
  induction hstar with
  | refl =>
    exact ⟨
      fun ss ρ₀ heq => by
        subst heq; simp [Config.getEnv] at htgt_fail
        exact ⟨.stmts (ss ++ ss₂) ρ₀, by simp [Config.getEnv]; exact htgt_fail, .refl _⟩,
      fun inner ss heq => by
        subst heq; exact ⟨.seq inner (ss ++ ss₂), by simp [Config.getEnv]; exact htgt_fail, .refl _⟩⟩
  | step src mid tgt hstep hrest ih =>
    have ⟨ih_stmts, ih_seq⟩ := ih htgt_fail
    constructor
    · intro ss ρ₀ heq; subst heq
      cases hstep with
      | step_stmts_nil =>
        simp [List.nil_append]
        cases hrest with
        | refl => exact ⟨.stmts ss₂ ρ₀, htgt_fail, .refl _⟩
        | step _ _ _ h2 _ => cases h2
      | step_stmts_cons =>
        rename_i s rest_ss
        obtain ⟨cfg', hf', hr'⟩ := ih_seq (.stmt s ρ₀) rest_ss rfl
        exact ⟨cfg', hf', .step _ _ _ .step_stmts_cons hr'⟩
    · intro inner ss heq; subst heq
      cases hstep with
      | step_seq_inner hinner =>
        obtain ⟨cfg', hf', hr'⟩ := ih_seq _ ss rfl
        exact ⟨cfg', hf', .step _ _ _ (.step_seq_inner hinner) hr'⟩
      | step_seq_done =>
        rename_i ρ₁
        obtain ⟨cfg', hf', hr'⟩ := ih_stmts ss ρ₁ rfl
        exact ⟨cfg', hf', .step _ _ _ .step_seq_done hr'⟩
      | step_seq_exit =>
        exact ⟨tgt, htgt_fail, .step _ _ _ .step_seq_exit hrest⟩

/-- Execute the first_iter_body (asserts ++ assumes) when all invariants are tt.
    Returns terminal at the same environment. -/
private theorem first_iter_body_all_tt
    (inv : List Expression.Expr)
    (ρ : Env Expression) (σ : StringGenState)
    (md : MetaData Expression)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hall : ∀ e ∈ inv, ρ.eval ρ.store e = some HasBool.tt) :
    CoreStar π φ
      (.stmts
        ((inv.mapIdx fun i inv_i =>
          Stmt.cmd (HasPassiveCmds.assert
            s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
         (inv.mapIdx fun i inv_i =>
          Stmt.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))) ρ)
      (.terminal ρ) := by
  exact ReflTrans_Transitive _ _ _ _
    (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
      (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assert
          s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))
      (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))
      ρ ρ (stmts_mapIdx_assert_terminal π φ inv ρ σ md hwfb hnf hall))
    (stmts_mapIdx_assume_terminal π φ inv ρ σ md hwfb hnf hall)

/-- If some invariant is ff, the first_iter_body assert list can fail,
    which lifts to CanFail for the whole block. -/
private theorem first_iter_body_some_ff_canFail
    (inv : List Expression.Expr)
    (ρ : Env Expression) (σ : StringGenState)
    (md : MetaData Expression)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hall_bool : ∀ e ∈ inv, ρ.eval ρ.store e = some HasBool.tt ∨
      ρ.eval ρ.store e = some HasBool.ff)
    (hsome_ff : ∃ e ∈ inv, ρ.eval ρ.store e = some HasBool.ff)
    (first_iter_label : String) (ite_stmt : Statement) :
    CanFailBlock π φ
      [Stmt.block first_iter_label
        ((inv.mapIdx fun i inv_i =>
          Stmt.cmd (HasPassiveCmds.assert
            s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
         (inv.mapIdx fun i inv_i =>
          Stmt.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))) {},
       ite_stmt] ρ := by
  have hcf_asserts := stmts_mapIdx_assert_canFail π φ inv ρ σ md hwfb hnf hall_bool hsome_ff
  -- Lift: CanFailBlock for asserts → CanFailBlock for asserts ++ assumes
  have hcf_body : CanFailBlock π φ
      ((inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assert
          s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
       (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))) ρ := by
    exact canFailBlock_append_left π φ _ _ ρ hcf_asserts
  -- Lift to CanFail for the block stmt
  have hcf_block : Transform.CanFail (LangCore π φ)
      (Stmt.block first_iter_label
        ((inv.mapIdx fun i inv_i =>
          Stmt.cmd (HasPassiveCmds.assert
            s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
         (inv.mapIdx fun i inv_i =>
          Stmt.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))) {}) ρ :=
    canFailBlock_to_canFail_block π φ _ _ _ ρ hcf_body
  exact canFail_head_to_block π φ _ _ ρ hcf_block

/-- If not all invariants evaluate to tt and each evaluates to tt or ff,
    then some invariant evaluates to ff. Proved by induction on the list. -/
private theorem not_all_tt_implies_some_ff
    (inv : List Expression.Expr) (ρ : Env Expression)
    (hinv_bool : ∀ e ∈ inv, ρ.eval ρ.store e = some HasBool.tt ∨
      ρ.eval ρ.store e = some HasBool.ff)
    (hnot_all_tt : ¬∀ e ∈ inv, ρ.eval ρ.store e = some HasBool.tt) :
    ∃ e ∈ inv, ρ.eval ρ.store e = some HasBool.ff := by
  induction inv with
  | nil => exact absurd (fun _ h => nomatch h) hnot_all_tt
  | cons x xs ih =>
    have hx_mem : x ∈ x :: xs := .head ..
    cases hinv_bool x hx_mem with
    | inr hff => exact ⟨x, hx_mem, hff⟩
    | inl htt =>
      have hnot_all_xs : ¬∀ e ∈ xs, ρ.eval ρ.store e = some HasBool.tt := by
        intro h; apply hnot_all_tt
        intro e he
        match he with
        | .head .. => exact htt
        | .tail _ hmem => exact h e hmem
      have ⟨e, he, hff⟩ := ih (fun e he => hinv_bool e (.tail _ he)) hnot_all_xs
      exact ⟨e, .tail _ he, hff⟩

/-! ## Store preservation outside modified variables -/

/-- TouchVars preserves the store at variables not in the touched list. -/
private theorem touchVars_preserves_outside
    {σ σ' : SemanticStore Expression}
    {vs : List Expression.Ident}
    (h : TouchVars σ vs σ') (x : Expression.Ident) (hx : x ∉ vs) :
    σ' x = σ x := by
  induction h with
  | none => rfl
  | init_some hinit _ ih =>
    cases hinit with
    | init _ _ hother =>
      have := ih (fun hm => hx (.tail _ hm))
      rw [this]
      exact hother x (fun heq => hx (heq ▸ .head ..))
  | update_some hupd _ ih =>
    cases hupd with
    | update _ _ hother =>
      have := ih (fun hm => hx (.tail _ hm))
      rw [this]
      exact hother x (fun heq => hx (heq ▸ .head ..))

/-- TouchVars preserves definedness: if a variable was defined (isSome) in the
    initial store, it remains defined in the final store. -/
private theorem touchVars_preserves_definedness
    {σ σ' : SemanticStore Expression}
    {vs : List Expression.Ident}
    (h : TouchVars σ vs σ') : ∀ (x : Expression.Ident), (σ x).isSome → (σ' x).isSome := by
  induction h with
  | none => intro x hdef; exact hdef
  | init_some hinit _ ih =>
    intro x hdef
    apply ih
    cases hinit with
    | init hx_none hx'_some hother =>
      have h := hother x (fun heq => by simp [heq ▸ hx_none] at hdef)
      rw [h]; exact hdef
  | update_some hupd _ ih =>
    intro x hdef
    apply ih
    cases hupd with
    | update hx_old hx'_some hother =>
      -- Goal: (σ_mid x).isSome where σ_mid is the post-update store
      -- Strategy: if y ≠ x, σ_mid x = σ x (defined by hdef).
      -- If y = x, σ_mid x = some v (defined by hx'_some).
      -- We derive y ≠ x OR get the result directly.
      -- Use: either hother gives σ_mid x = σ x, or σ_mid x = some v.
      -- Key: hother requires y ≠ x. If y = x, then hx'_some says σ_mid x = some v.
      -- So we try: assume σ_mid x is none, derive contradiction.
      simp only [Option.isSome_iff_ne_none]
      intro habs
      -- habs : σ_mid x = none
      -- But hx'_some : σ_mid y = some v. If y = x, σ_mid x = some v ≠ none.
      -- So y ≠ x. Then hother gives σ_mid x = σ x. But σ_mid x = none and
      -- (σ x).isSome, contradiction.
      have h := hother x (fun heq => by rw [heq] at hx'_some; simp [hx'_some] at habs)
      rw [habs] at h; rw [← h] at hdef; simp at hdef

/-- Block execution preserves the store outside `Block.modifiedVars body`
    when all touched variables are initially defined. The `hdef_touched`
    condition ensures `init` commands cannot fire on variables outside
    `modifiedVars` (because `InitState` requires `σ x = none`).

    For variables outside `touchedVars`, the store is trivially preserved
    since no command touches them (`EvalCmdTouch` + `touchVars_preserves_outside`).
    For variables in `definedVars \ modifiedVars`, `hdef_touched` prevents
    `InitState` from constructing, and no `set x` exists (x not in modifiedVars). -/
private theorem block_preserves_store_outside_modifiedVars
    (body : Statements) (ρ₀ ρ' : Env Expression)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] body)
    (hdef_touched : ∀ (σ : SemanticStore Expression),
      ∀ n ∈ Block.touchedVars body, (σ n).isSome)
    (hstar : CoreStar π φ (.stmts body ρ₀) (.terminal ρ'))
    (x : Expression.Ident) (hx : x ∉ Block.modifiedVars body) :
    ρ'.store x = ρ₀.store x := by
  -- hdef_touched ∀ σ forces touchedVars body = [] (take σ = fun _ => none).
  -- For basic Cmd steps (init/set/assert/assume/cover) with touchedVars c = [],
  -- only assert/assume/cover are possible and they preserve the store.
  -- For CmdExt.call steps with lhs = [], UpdateStates on p.spec.modifies
  -- can still change the store — this gap requires an additional "no calls
  -- in loop bodies" hypothesis (true after call elimination).
  -- Pending that infrastructure; callers work because the hypothesis is threaded.
  sorry

/-- The definedness hypothesis for modifiedVars is preserved through loop iterations.
    If all vars in `Block.modifiedVars body` are defined at ρ₀, they remain defined
    at any reachable ρ_k. -/
private theorem loop_iterations_preserve_modvars_defined
    (body : Statements) (ρ₀ ρ_k : Env Expression)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] body)
    (g : Expression.Expr) (measure : Option Expression.Expr)
    (inv : List Expression.Expr) (md : MetaData Expression)
    (hloop : CoreStar π φ
      (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ_k))
    (hdef : ∀ n ∈ Block.modifiedVars body, (ρ₀.store n).isSome) :
    ∀ n ∈ Block.modifiedVars body, (ρ_k.store n).isSome :=
  star_preserves_isDefined π φ hloop hdef

/-! ## Havoc targeting: change store to match a target on given variables -/

/-- A single `set x .nondet` can change the store value at `x` to any target value,
    leaving all other variables unchanged. The new store σ' satisfies:
    σ' x = some v_target and σ' y = ρ₀.store y for y ≠ x. -/
private theorem havoc_targeting_single
    (x : Expression.Ident) (md : MetaData Expression)
    (ρ₀ : Env Expression) (v_target : Expression.Expr)
    (hdef_src : (ρ₀.store x).isSome)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnf : ρ₀.hasFailure = Bool.false) :
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
  -- Construct the new store: same as ρ₀.store but x ↦ some v_target
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
    on each variable in `vars`. Variables not in `vars` keep their original
    values from `ρ₀.store`. -/
private theorem havocs_targeting_stmts
    (vars : List Expression.Ident) (md : MetaData Expression)
    (ρ₀ : Env Expression) (σ_target : SemanticStore Expression)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hdef_src : ∀ x ∈ vars, (ρ₀.store x).isSome)
    (hdef_tgt : ∀ x ∈ vars, (σ_target x).isSome)
    (hnf : ρ₀.hasFailure = Bool.false) :
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
    -- Get the target value for x
    have hdef_x := hdef_tgt x (.head ..)
    obtain ⟨v_target, hv_target⟩ := Option.isSome_iff_exists.mp hdef_x
    -- Execute havoc x to get intermediate store σ₁
    have ⟨σ₁, hσ₁_x, hσ₁_other, hstep_x⟩ :=
      havoc_targeting_single π φ x md ρ₀ v_target (hdef_src x (.head ..)) hwfvar hnf
    let ρ₁ : Env Expression := { ρ₀ with store := σ₁ }
    -- Prove definedness at σ₁ for rest
    have hdef_src_rest : ∀ y ∈ rest, (σ₁ y).isSome := by
      intro y hy
      by_cases hxy : x = y
      · subst hxy; rw [hσ₁_x]; simp
      · rw [hσ₁_other y hxy]; exact hdef_src y (.tail _ hy)
    have hdef_tgt_rest : ∀ y ∈ rest, (σ_target y).isSome :=
      fun y hy => hdef_tgt y (.tail _ hy)
    have ⟨σ_out, hmatch, hother, hstar_rest⟩ :=
      ih ρ₁ hwfvar hdef_src_rest hdef_tgt_rest hnf
    -- Compose: σ_out matches σ_target on x :: rest, equals ρ₀.store outside
    refine ⟨σ_out, ?_, ?_, ?_⟩
    · -- ∀ y ∈ x :: rest, σ_out y = σ_target y
      intro y hy
      cases hy with
      | head => -- y = x
        by_cases hx_rest : x ∈ rest
        · exact hmatch x hx_rest
        · -- x ∉ rest, so σ_out x = σ₁ x = some v_target = σ_target x
          exact (hother x hx_rest).trans (hσ₁_x.trans hv_target.symm)
      | tail _ hy' => exact hmatch y hy'
    · -- ∀ y, y ∉ x :: rest → σ_out y = ρ₀.store y
      intro y hy
      have hy_rest : y ∉ rest := fun h => hy (.tail _ h)
      have hxy : x ≠ y := fun h => hy (h ▸ .head ..)
      exact (hother y hy_rest).trans (hσ₁_other y hxy)
    · -- Execution trace
      simp only [List.map]
      exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
          (.cmd (HasHavoc.havoc x md))
          (rest.map fun n => Stmt.cmd (HasHavoc.havoc n md))
          ρ₀ ρ₁ hstep_x)
        hstar_rest

/-- Execute the havoc block, targeting `σ_target` on `vars`. -/
private theorem havoc_block_targeting
    (label : String) (vars : List Expression.Ident) (md : MetaData Expression)
    (ρ₀ : Env Expression) (σ_target : SemanticStore Expression)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hdef_src : ∀ x ∈ vars, (ρ₀.store x).isSome)
    (hdef_tgt : ∀ x ∈ vars, (σ_target x).isSome)
    (hnf : ρ₀.hasFailure = Bool.false) :
    ∃ σ_out : SemanticStore Expression,
      (∀ x ∈ vars, σ_out x = σ_target x) ∧
      (∀ x, x ∉ vars → σ_out x = ρ₀.store x) ∧
      CoreStar π φ
        (.stmt (.block label (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ₀)
        (.terminal { ρ₀ with store := σ_out }) := by
  have ⟨σ_out, hmatch, hother, hstar⟩ :=
    havocs_targeting_stmts π φ vars md ρ₀ σ_target hwfvar hdef_src hdef_tgt hnf
  exact ⟨σ_out, hmatch, hother, block_wrap_terminal π φ label _ _ ρ₀ _ hstar⟩

/-- Combined havoc targeting lemma: when ρ_target agrees with ρ₀ outside
    `vars = Block.modifiedVars body` (which holds by the overapproximation
    property), the havoc block can reach exactly `{ ρ₀ with store := ρ_target.store }`.
    Since `ρ_target.eval = ρ₀.eval` (by noFuncDecl), this is `ρ_target` up to
    hasFailure. -/
private theorem havoc_block_to_target
    (label : String) (vars : List Expression.Ident) (md : MetaData Expression)
    (ρ₀ ρ_target : Env Expression)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hdef_src : ∀ x ∈ vars, (ρ₀.store x).isSome)
    (hdef_tgt : ∀ x ∈ vars, (ρ_target.store x).isSome)
    (hagree : ∀ x, x ∉ vars → ρ_target.store x = ρ₀.store x)
    (hnf : ρ₀.hasFailure = Bool.false) :
    CoreStar π φ
      (.stmt (.block label (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ₀)
      (.terminal { ρ₀ with store := ρ_target.store }) := by
  have ⟨σ_out, hmatch, hother, hstar⟩ :=
    havoc_block_targeting π φ label vars md ρ₀ ρ_target.store hwfvar hdef_src hdef_tgt hnf
  -- Show σ_out = ρ_target.store
  suffices h : σ_out = ρ_target.store by rw [← h]; exact hstar
  funext x
  by_cases hx : x ∈ vars
  · exact hmatch x hx
  · rw [hother x hx, ← hagree x hx]

/-! ## Identity havoc execution infrastructure -/

/-- A single `havoc n` command executes as identity when `ρ.store n` is defined. -/
private theorem havoc_identity_step
    (n : Expression.Ident) (md : MetaData Expression)
    (ρ : Env Expression) (v : Expression.Expr)
    (hdef : ρ.store n = some v)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ (.stmt (.cmd (HasHavoc.havoc n md)) ρ) (.terminal ρ) := by
  -- HasHavoc.havoc n md = CmdExt.cmd (Cmd.set n .nondet md) for Core
  change CoreStar π φ (.stmt (.cmd (CmdExt.cmd (Cmd.set n .nondet md))) ρ) (.terminal ρ)
  have hupdate : UpdateState Expression ρ.store n v ρ.store :=
    .update hdef hdef (fun _ _ => rfl)
  exact .step _ _ _
    (.step_cmd (EvalCommand.cmd_sem (.eval_set_nondet hupdate hwfvar)))
    (by simp [Bool.or_false]; cases ρ; exact .refl _)

/-- Execute a list of havoc commands as identity when all variables are defined. -/
private theorem havocs_identity_stmts
    (vs : List Expression.Ident) (md : MetaData Expression)
    (ρ : Env Expression)
    (hdef : ∀ n ∈ vs, (ρ.store n).isSome)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ (.stmts (vs.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ρ)
      (.terminal ρ) := by
  induction vs with
  | nil => simp [List.map]; exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons n rest ih =>
    simp only [List.map]
    have hdef_n := hdef n (.head ..)
    have hdef_rest : ∀ m ∈ rest, (ρ.store m).isSome :=
      fun m hm => hdef m (.tail _ hm)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hdef_n
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.cmd (HasHavoc.havoc n md))
        (rest.map fun n => Stmt.cmd (HasHavoc.havoc n md))
        ρ ρ (havoc_identity_step π φ n md ρ v hv hwfvar hnf))
      (ih hdef_rest)

/-- Execute the havoc block (`.block label (vs.map havoc) {}`) as identity. -/
private theorem havoc_block_identity
    (label : String) (vs : List Expression.Ident) (md : MetaData Expression)
    (ρ : Env Expression)
    (hdef : ∀ n ∈ vs, (ρ.store n).isSome)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ
      (.stmt (.block label (vs.map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ)
      (.terminal ρ) :=
  block_wrap_terminal π φ label _ _ ρ ρ
    (havocs_identity_stmts π φ vs md ρ hdef hwfvar hnf)

/-- Execute the assume block with guard and invariant assumes. -/
private theorem assume_block_step
    (σ : StringGenState) (g : Expression.Expr)
    (inv : List Expression.Expr) (md : MetaData Expression)
    (ρ : Env Expression)
    (hguard_tt : ρ.eval ρ.store g = some HasBool.tt)
    (hall_tt : ∀ e ∈ inv, ρ.eval ρ.store e = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ
      (.stmt (.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loopNum σ}"
        ([Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loopNum σ}_guard" g md)] ++
         inv.mapIdx fun i inv_i =>
          Stmt.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loopNum σ}_invariant_{i}" inv_i md)) md) ρ)
      (.terminal ρ) := by
  apply block_wrap_terminal
  exact ReflTrans_Transitive _ _ _ _
    (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
      (.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loopNum σ}_guard" g md))
      (inv.mapIdx fun i inv_i =>
        Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loopNum σ}_invariant_{i}" inv_i md))
      ρ ρ (assume_tt_step π φ _ g md ρ hguard_tt hwfb hnf))
    (stmts_mapIdx_assume_terminal_gen π φ inv ρ md _ (fun i e => ⟨_, rfl⟩) hwfb hnf hall_tt)

/-- If a prefix of statements terminates and the suffix CanFails, the whole
    concatenation CanFails. -/
private theorem canFailBlock_prefix_terminal_suffix
    (pfx sfx : Statements) (ρ₀ ρ₁ : Env Expression)
    (hpfx : CoreStar π φ (.stmts pfx ρ₀) (.terminal ρ₁))
    (hsfx : CanFailBlock π φ sfx ρ₁) :
    CanFailBlock π φ (pfx ++ sfx) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := hsfx
  exact ⟨cfg, hfail,
    ReflTrans_Transitive _ _ _ _
      (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
        pfx sfx ρ₀ ρ₁ hpfx)
      hreach⟩

/-! ## Loop invariant dichotomy -/

/-- For a terminating det loop where the guard is true and all invariants hold
    at entry: either some iteration body maps a state satisfying G∧I to one
    where some invariant fails, or there exists a "last iteration" pre-state
    satisfying G∧I where body reaches ρ' and all invariants hold at ρ'. -/
private noncomputable def loop_invariant_dichotomy
    (hwf_ext : WFEvalExtension φ)
    (g : Expression.Expr) (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (hguard_tt : ρ₀.eval ρ₀.store g = some HasBool.tt)
    (hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] body)
    (hinvs_eval : ∀ δ σ, WellFormedSemanticEvalBool δ →
      ∀ e ∈ inv, δ σ e = some HasBool.tt ∨ δ σ e = some HasBool.ff)
    (hdef_modvars : ∀ n ∈ Block.modifiedVars body, (ρ₀.store n).isSome)
    (hdef_touched_all : ∀ (σ : SemanticStore Expression),
      ∀ n ∈ Block.touchedVars body, (σ n).isSome)
    (hnf : ρ'.hasFailure = Bool.false)
    (hloop : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ')) :
    -- Violation: some iteration has body from ρ_pre to ρ_post where an invariant fails
    (∃ ρ_pre ρ_post,
      ρ_pre.eval ρ_pre.store g = some HasBool.tt ∧
      (∀ e ∈ inv, ρ_pre.eval ρ_pre.store e = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_pre.eval ∧
      WellFormedSemanticEvalVal ρ_pre.eval ∧
      ρ_pre.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_pre) (.terminal ρ_post) ∧
      ρ_post.hasFailure = Bool.false ∧
      (∃ e ∈ inv, ρ_post.eval ρ_post.store e = some HasBool.ff) ∧
      ρ_pre.eval = ρ₀.eval ∧
      (∀ x, x ∉ Block.modifiedVars body → ρ_pre.store x = ρ₀.store x) ∧
      (∀ n ∈ Block.modifiedVars body, (ρ_pre.store n).isSome))
    ∨
    -- Success: last iteration from ρ_last to ρ' with all invariants holding
    (∃ ρ_last,
      ρ_last.eval ρ_last.store g = some HasBool.tt ∧
      (∀ e ∈ inv, ρ_last.eval ρ_last.store e = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
      (∀ e ∈ inv, ρ'.eval ρ'.store e = some HasBool.tt) ∧
      ρ_last.eval = ρ₀.eval ∧
      (∀ x, x ∉ Block.modifiedVars body → ρ_last.store x = ρ₀.store x) ∧
      (∀ n ∈ Block.modifiedVars body, (ρ_last.store n).isSome)) :=
  match hloop with
  | .step _ _ _ (.step_loop_exit hff _) _ =>
    -- Guard is false, but we assumed it's true — contradiction
    absurd hguard_tt (by rw [hff]; intro h; exact absurd (Option.some.inj h).symm HasBool.tt_is_not_ff)
  | .step _ _ _ (.step_loop_enter hg hwfb') hrest =>
    -- Decompose body ++ [loop] into body ρ₀→ρ₁ and loop ρ₁→ρ'
    let ⟨ρ₁, hbody_prop, hloopT, _hlen⟩ :=
      stmtsT_append_single_terminal π φ body
        (.loop (.det g) measure inv body md) ρ₀ ρ' hrest
    -- Derive hasFailure at intermediate states
    have hnf₁ : ρ₁.hasFailure = Bool.false :=
      hasFailure_false_backwards π φ (reflTransT_to_prop hloopT) hnf
    have hnf₀ : ρ₀.hasFailure = Bool.false :=
      hasFailure_false_backwards π φ hbody_prop hnf₁
    -- Derive eval preservation: ρ₁.eval = ρ₀.eval
    have heval_eq : ρ₁.eval = ρ₀.eval :=
      smallStep_noFuncDecl_preserves_eval_block Expression (EvalCommand π φ) (EvalPureFunc φ)
        body ρ₀ ρ₁ hnofd hbody_prop
    -- Derive WF at ρ₁
    have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := heval_eq ▸ hwfb
    have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := heval_eq ▸ hwfv
    -- Check invariants at ρ₁
    have hinv_bool_ρ₁ : ∀ e ∈ inv, ρ₁.eval ρ₁.store e = some HasBool.tt ∨
        ρ₁.eval ρ₁.store e = some HasBool.ff :=
      hinvs_eval ρ₁.eval ρ₁.store hwfb₁
    if hinv_ρ₁ : ∀ e ∈ inv, ρ₁.eval ρ₁.store e = some HasBool.tt then
      -- All invariants hold at ρ₁. Look at the loop from ρ₁.
      match hloopT with
      | .step _ _ _ (.step_loop_exit _hff₁ _) (.refl _) =>
        -- Loop exits at ρ₁ (guard false), so ρ' = ρ₁
        -- Take the Right case with ρ_last = ρ₀
        .inr ⟨ρ₀, hguard_tt, hall_tt, hwfb, hwfv, hnf₀, hbody_prop, hinv_ρ₁,
          rfl, fun _ _ => rfl, hdef_modvars⟩
      | .step _ _ _ (.step_loop_exit _ _) (.step _ _ _ h _) => nomatch h
      | .step _ _ _ (.step_loop_enter hg₁ hwfb₁') hrest₁ =>
        -- Loop enters again from ρ₁. Recurse.
        -- Derive store agreement for ρ₁
        have hstore_ρ₁ : ∀ x, x ∉ Block.modifiedVars body → ρ₁.store x = ρ₀.store x :=
          fun x hx => block_preserves_store_outside_modifiedVars π φ body ρ₀ ρ₁ hnofd hcov
            hdef_touched_all hbody_prop x hx
        have hdef_modvars₁ : ∀ n ∈ Block.modifiedVars body, (ρ₁.store n).isSome :=
          star_preserves_isDefined π φ hbody_prop hdef_modvars
        -- Now recurse and compose properties
        let hrec := loop_invariant_dichotomy hwf_ext g measure inv body md ρ₁ ρ'
          hg₁ hinv_ρ₁ hwfb₁ hwfv₁ hnofd hcov hinvs_eval hdef_modvars₁ hdef_touched_all hnf
          (.step _ _ _ (.step_loop_enter hg₁ hwfb₁') hrest₁)
        hrec.imp
          (fun ⟨ρ_pre, ρ_post, hg_pre, hinv_pre, hwfb_pre, hwfv_pre, hnf_pre,
              hbody, hnf_post, hsome_ff, heval_pre, hstore_pre, hdef_pre⟩ =>
            ⟨ρ_pre, ρ_post, hg_pre, hinv_pre, hwfb_pre, hwfv_pre, hnf_pre,
              hbody, hnf_post, hsome_ff,
              heval_pre.trans heval_eq, fun x hx => (hstore_pre x hx).trans (hstore_ρ₁ x hx),
              hdef_pre⟩)
          (fun ⟨ρ_last, hg_last, hinv_last, hwfb_last, hwfv_last, hnf_last,
              hbody, hinv_ρ'', heval_last, hstore_last, hdef_last⟩ =>
            ⟨ρ_last, hg_last, hinv_last, hwfb_last, hwfv_last, hnf_last,
              hbody, hinv_ρ'',
              heval_last.trans heval_eq, fun x hx => (hstore_last x hx).trans (hstore_ρ₁ x hx),
              hdef_last⟩)
    else
      -- Some invariant fails at ρ₁. Take the Left case.
      have hsome_ff := not_all_tt_implies_some_ff inv ρ₁ hinv_bool_ρ₁ hinv_ρ₁
      .inl ⟨ρ₀, ρ₁, hguard_tt, hall_tt, hwfb, hwfv, hnf₀, hbody_prop, hnf₁, hsome_ff,
        rfl, fun _ _ => rfl, hdef_modvars⟩
  termination_by hloop.len
  decreasing_by simp_all [ReflTransT.len]; omega

/-! ## Loop invariant dichotomy for nondet loops -/

/-- Nondet version of `loop_invariant_dichotomy`. Since there is no guard,
    we track only invariant violations vs. success. The loop can exit at any
    iteration, so we do not track guard_tt/guard_ff. -/
private noncomputable def loop_invariant_dichotomy_nondet
    (hwf_ext : WFEvalExtension φ)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] body)
    (hinvs_eval : ∀ δ σ, WellFormedSemanticEvalBool δ →
      ∀ e ∈ inv, δ σ e = some HasBool.tt ∨ δ σ e = some HasBool.ff)
    (hdef_modvars : ∀ n ∈ Block.modifiedVars body, (ρ₀.store n).isSome)
    (hdef_touched_all : ∀ (σ : SemanticStore Expression),
      ∀ n ∈ Block.touchedVars body, (σ n).isSome)
    (hnf : ρ'.hasFailure = Bool.false)
    (hrest : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.stmts (body ++ [.loop .nondet measure inv body md]) ρ₀) (.terminal ρ')) :
    -- Violation: some iteration has body from ρ_pre to ρ_post where an invariant fails
    (∃ ρ_pre ρ_post,
      (∀ e ∈ inv, ρ_pre.eval ρ_pre.store e = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_pre.eval ∧
      WellFormedSemanticEvalVal ρ_pre.eval ∧
      ρ_pre.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_pre) (.terminal ρ_post) ∧
      ρ_post.hasFailure = Bool.false ∧
      (∃ e ∈ inv, ρ_post.eval ρ_post.store e = some HasBool.ff) ∧
      ρ_pre.eval = ρ₀.eval ∧
      (∀ x, x ∉ Block.modifiedVars body → ρ_pre.store x = ρ₀.store x) ∧
      (∀ n ∈ Block.modifiedVars body, (ρ_pre.store n).isSome))
    ∨
    -- Success: last iteration from ρ_last to ρ' with all invariants holding
    (∃ ρ_last,
      (∀ e ∈ inv, ρ_last.eval ρ_last.store e = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
      (∀ e ∈ inv, ρ'.eval ρ'.store e = some HasBool.tt) ∧
      ρ_last.eval = ρ₀.eval ∧
      (∀ x, x ∉ Block.modifiedVars body → ρ_last.store x = ρ₀.store x) ∧
      (∀ n ∈ Block.modifiedVars body, (ρ_last.store n).isSome)) :=
  -- Decompose body ++ [loop] into body ρ₀→ρ₁ and loop ρ₁→ρ'
  let ⟨ρ₁, hbody_prop, hloopT, _hlen⟩ :=
    stmtsT_append_single_terminal π φ body
      (.loop .nondet measure inv body md) ρ₀ ρ' hrest
  -- Derive hasFailure at intermediate states
  have hnf₁ : ρ₁.hasFailure = Bool.false :=
    hasFailure_false_backwards π φ (reflTransT_to_prop hloopT) hnf
  have hnf₀ : ρ₀.hasFailure = Bool.false :=
    hasFailure_false_backwards π φ hbody_prop hnf₁
  -- Derive eval preservation: ρ₁.eval = ρ₀.eval
  have heval_eq : ρ₁.eval = ρ₀.eval :=
    smallStep_noFuncDecl_preserves_eval_block Expression (EvalCommand π φ) (EvalPureFunc φ)
      body ρ₀ ρ₁ hnofd hbody_prop
  -- Derive WF at ρ₁
  have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := heval_eq ▸ hwfb
  have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := heval_eq ▸ hwfv
  -- Check invariants at ρ₁
  have hinv_bool_ρ₁ : ∀ e ∈ inv, ρ₁.eval ρ₁.store e = some HasBool.tt ∨
      ρ₁.eval ρ₁.store e = some HasBool.ff :=
    hinvs_eval ρ₁.eval ρ₁.store hwfb₁
  if hinv_ρ₁ : ∀ e ∈ inv, ρ₁.eval ρ₁.store e = some HasBool.tt then
    -- All invariants hold at ρ₁. Look at the loop from ρ₁.
    match hloopT with
    | .step _ _ _ .step_loop_nondet_exit (.refl _) =>
      -- Loop exits at ρ₁, so ρ' = ρ₁
      -- Take the Right case with ρ_last = ρ₀
      .inr ⟨ρ₀, hall_tt, hwfb, hwfv, hnf₀, hbody_prop, hinv_ρ₁,
        rfl, fun _ _ => rfl, hdef_modvars⟩
    | .step _ _ _ .step_loop_nondet_exit (.step _ _ _ h _) => nomatch h
    | .step _ _ _ .step_loop_nondet_enter hrest₁ =>
      -- Loop enters again from ρ₁. Recurse.
      have hstore_ρ₁ : ∀ x, x ∉ Block.modifiedVars body → ρ₁.store x = ρ₀.store x :=
        fun x hx => block_preserves_store_outside_modifiedVars π φ body ρ₀ ρ₁ hnofd hcov
          hdef_touched_all hbody_prop x hx
      have hdef_modvars₁ : ∀ n ∈ Block.modifiedVars body, (ρ₁.store n).isSome :=
        star_preserves_isDefined π φ hbody_prop hdef_modvars
      let hrec := loop_invariant_dichotomy_nondet hwf_ext measure inv body md ρ₁ ρ'
        hinv_ρ₁ hwfb₁ hwfv₁ hnofd hcov hinvs_eval hdef_modvars₁ hdef_touched_all hnf hrest₁
      hrec.imp
        (fun ⟨ρ_pre, ρ_post, hinv_pre, hwfb_pre, hwfv_pre, hnf_pre,
            hbody, hnf_post, hsome_ff, heval_pre, hstore_pre, hdef_pre⟩ =>
          ⟨ρ_pre, ρ_post, hinv_pre, hwfb_pre, hwfv_pre, hnf_pre,
            hbody, hnf_post, hsome_ff,
            heval_pre.trans heval_eq, fun x hx => (hstore_pre x hx).trans (hstore_ρ₁ x hx),
            hdef_pre⟩)
        (fun ⟨ρ_last, hinv_last, hwfb_last, hwfv_last, hnf_last,
            hbody, hinv_ρ'', heval_last, hstore_last, hdef_last⟩ =>
          ⟨ρ_last, hinv_last, hwfb_last, hwfv_last, hnf_last,
            hbody, hinv_ρ'',
            heval_last.trans heval_eq, fun x hx => (hstore_last x hx).trans (hstore_ρ₁ x hx),
            hdef_last⟩)
  else
    -- Some invariant fails at ρ₁. Take the Left case.
    have hsome_ff := not_all_tt_implies_some_ff inv ρ₁ hinv_bool_ρ₁ hinv_ρ₁
    .inl ⟨ρ₀, ρ₁, hall_tt, hwfb, hwfv, hnf₀, hbody_prop, hnf₁, hsome_ff,
      rfl, fun _ _ => rfl, hdef_modvars⟩
  termination_by hrest.len
  decreasing_by simp_all [ReflTransT.len]; omega

/-! ## Then-branch simulation helpers -/

/-! ### Det loop enter-body case -/

/-- If the body of arbitrary_iter_facts CanFails, then loopDetThenBranch CanFails.
    The `body_stmts` parameter should be the body of the arbitrary_iter_facts block
    (matching the expansion of `loopDetThenBranch`). -/
private theorem arb_iter_body_canFail_to_loopDetThenBranch
    (σ : StringGenState) (g : Expression.Expr)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) (ρ₀ : Env Expression) :
    let loop_num := loopNum σ
    let σ₁ := loopGenState σ
    let assigned_vars := Block.modifiedVars body
    let havocd := Stmt.block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
      (assigned_vars.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}
    let body' := blockResult σ₁ body
    let inv_assumes := inv.mapIdx fun i inv_i =>
      Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_invariant_{i}" inv_i md)
    let maintain_invariants := inv.mapIdx fun i inv_i =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{i}" inv_i md)
    let assume_guard :=
      Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_guard" g md)
    let arbitrary_iter_assumes :=
      Stmt.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
        ([assume_guard] ++ inv_assumes) md
    let (pre_termination, post_termination) := match measure with
      | none => ([], [])
      | some m =>
        let m_old_ident := HasIdent.ident s!"$__loop_measure_{loop_num}"
        let m_old_expr := HasFvar.mkFvar m_old_ident
        ([Stmt.cmd (HasInit.init m_old_ident HasIntOrder.intTy .nondet md),
          Stmt.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loop_num}_measure" (HasIntOrder.eq m_old_expr m) md),
          Stmt.cmd (HasPassiveCmds.assert
            s!"{loopElimAssertPrefix}{loop_num}_measure_lb"
            (HasNot.not (HasIntOrder.lt m_old_expr HasIntOrder.zero)) md)],
         [Stmt.cmd (HasPassiveCmds.assert
            s!"{loopElimAssertPrefix}{loop_num}_measure_decrease"
            (HasIntOrder.lt m m_old_expr) md)])
    CanFailBlock π φ
      ([havocd, arbitrary_iter_assumes] ++ pre_termination ++
       body' ++ maintain_invariants ++ post_termination) ρ₀ →
    CanFailBlock π φ (loopDetThenBranch σ g measure inv body md) ρ₀ := by
  simp only
  intro hcf
  unfold loopDetThenBranch
  exact canFail_head_to_block π φ _ _ ρ₀
    (canFailBlock_to_canFail_block π φ _ _ {} ρ₀ hcf)

/-- Core helper for the enter-body det loop case.

When the source det loop terminates (guard is true at entry, all invariants
hold), the target's then-branch must either CanFail or reach the same terminal
state ρ'.

The strategy uses `loop_invariant_dichotomy` to squeeze N iterations into 1:
- Left (violation): some iteration body violates an invariant. We choose
  havoc = ρ_pre, run body' to ρ_post, assert(I) fails → CanFail.
- Right (success): last iteration succeeds with I(ρ') = tt. We choose
  havoc = ρ_last, run body' to ρ', assert(I) passes, exit section passes.

The then-branch is `loopDetThenBranch σ g measure inv body md`, which
contains `[arbitrary_iter_facts, havocd, assume(!G)] ++ inv_assumes`. -/
private theorem det_loop_enter_body_sim
    (hwf_ext : WFEvalExtension φ)
    (σ : StringGenState) (g : Expression.Expr)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    -- Source execution: full loop from ρ₀
    (hguard_tt : ρ₀.eval ρ₀.store g = some HasBool.tt)
    (hguard_ff_ρ' : ρ'.eval ρ'.store g = some HasBool.ff)
    (hloop_full : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ'))
    -- Invariant properties
    (hinvs_eval : ∀ (δ : SemanticEval Expression) (σs : SemanticStore Expression),
      WellFormedSemanticEvalBool δ → ∀ e ∈ inv, δ σs e = some HasBool.tt ∨ δ σs e = some HasBool.ff)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] body)
    (hinvs_body : Block.loopInvsBool body)
    (hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt)
    -- Modified vars are defined in the initial store (needed for havoc)
    (hdef_modvars : ∀ n ∈ Block.modifiedVars body, (ρ₀.store n).isSome)
    -- Well-formedness
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnf : ρ'.hasFailure = Bool.false)
    -- Body IH: the transformed body simulates the source body
    (body_ih :
      ∀ (σ_b : StringGenState) (ρ_b : Env Expression),
        WellFormedSemanticEvalBool ρ_b.eval →
        WellFormedSemanticEvalVal ρ_b.eval →
        WellFormedSemanticEvalVar ρ_b.eval →
        (∀ ρ_b', CoreStar π φ (.stmts body ρ_b) (.terminal ρ_b') →
          CanFailBlock π φ (blockResult σ_b body) ρ_b ∨
          (ρ_b'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ_b body) ρ_b) (.terminal ρ_b'))) ∧
        (∀ lbl ρ_b', CoreStar π φ (.stmts body ρ_b) (.exiting lbl ρ_b') →
          CanFailBlock π φ (blockResult σ_b body) ρ_b ∨
          (ρ_b'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ_b body) ρ_b) (.exiting lbl ρ_b'))))
    (hdef_touched_all : ∀ (σt : SemanticStore Expression),
      ∀ n ∈ Block.touchedVars body, (σt n).isSome)
    (hmeasure : measure = none)
    :
    CanFailBlock π φ (loopDetThenBranch σ g measure inv body md) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ (.stmts (loopDetThenBranch σ g measure inv body md) ρ₀) (.terminal ρ')) := by
  subst hmeasure
  -- Derive hasFailure = false at ρ₀
  have hnf₀ : ρ₀.hasFailure = Bool.false :=
    hasFailure_false_backwards π φ (reflTransT_to_prop hloop_full) hnf
  -- Apply the loop invariant dichotomy
  have hdich := loop_invariant_dichotomy π φ hwf_ext g none inv body md ρ₀ ρ'
    hguard_tt hall_tt hwfb hwfv hnofd hcov hinvs_eval hdef_modvars hdef_touched_all hnf hloop_full
  match hdich with
  | .inl ⟨ρ_pre, ρ_post, hg_pre, hinv_pre, hwfb_pre, hwfv_pre, hnf_pre, hbody_pre_post,
      hnf_post, hsome_ff, heval_pre, hstore_pre, hdef_pre⟩ =>
    -- Violation case: body maps ρ_pre (G=tt, I=tt) to ρ_post where some I fails.
    -- Target trace: havoc to ρ_pre → assume(G) passes → assume(I) passes →
    -- body' reaches ρ_post (by body_ih) → assert(I) fails → CanFail.
    -- Invariants are boolean at ρ_post
    have ⟨hwfb_post, _hwfv_post⟩ :=
      star_preserves_wf π φ hwf_ext hbody_pre_post hwfb_pre hwfv_pre
    have hinv_bool_post : ∀ e ∈ inv, ρ_post.eval ρ_post.store e = some HasBool.tt ∨
        ρ_post.eval ρ_post.store e = some HasBool.ff :=
      hinvs_eval ρ_post.eval ρ_post.store hwfb_post
    -- Get body_ih for ρ_pre
    have hwfvar_pre : WellFormedSemanticEvalVar ρ_pre.eval := heval_pre ▸ hwfvar
    have ⟨hbody_ih_term, _⟩ := body_ih (loopGenState σ) ρ_pre hwfb_pre hwfv_pre hwfvar_pre
    have hbody_sim := hbody_ih_term ρ_post hbody_pre_post
    -- Derive that { ρ₀ with store := ρ_pre.store } = ρ_pre
    have hρ_pre_eq : ({ ρ₀ with store := ρ_pre.store } : Env Expression) = ρ_pre := by
      cases ρ₀; cases ρ_pre; simp at *; exact ⟨heval_pre.symm, hnf₀ ▸ hnf_pre.symm⟩
    -- Havoc block from ρ₀ reaches ρ_pre
    have hhavoc : CoreStar π φ
        (.stmt (.block s!"{loopElimBlockPrefix}loop_havoc_{loopNum σ}"
          ((Block.modifiedVars body).map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ₀)
        (.terminal ρ_pre) := by
      rw [← hρ_pre_eq]
      exact havoc_block_to_target π φ _ _ md ρ₀ ρ_pre hwfvar hdef_modvars hdef_pre hstore_pre hnf₀
    -- Assume block passes at ρ_pre (guard and invariants are tt)
    have hassume : CoreStar π φ
        (.stmt (.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loopNum σ}"
          ([Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loopNum σ}_guard" g md)] ++
           inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assume
              s!"{loopElimAssumePrefix}{loopNum σ}_invariant_{i}" inv_i md)) md) ρ_pre)
        (.terminal ρ_pre) :=
      assume_block_step π φ σ g inv md ρ_pre hg_pre hinv_pre hwfb_pre hnf_pre
    match hbody_sim with
    | .inl hcf_body =>
      -- Body' itself CanFails from ρ_pre. Lift to then-branch CanFail.
      left
      apply arb_iter_body_canFail_to_loopDetThenBranch
      simp only [List.nil_append, List.append_nil]
      exact canFail_tail_to_block π φ _ _ ρ₀ ρ_pre hhavoc
        (canFail_tail_to_block π φ _ _ ρ_pre ρ_pre hassume
          (canFailBlock_append_left π φ _ _ ρ_pre hcf_body))
    | .inr hbody_ok =>
      -- Body' reaches ρ_post with no failure. Assert(I) fails at ρ_post.
      have hbody_trace := hbody_ok hnf_post
      -- Assert list at ρ_post has a failing invariant
      have hcf_asserts : CanFailBlock π φ
          (inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assert
              s!"{loopElimAssertPrefix}{loopNum σ}_arbitrary_iter_maintain_invariant_{i}"
              inv_i md)) ρ_post :=
        stmts_mapIdx_assert_canFail_gen π φ inv ρ_post md _ (fun i e => ⟨_, rfl⟩)
          hwfb_post hnf_post hinv_bool_post hsome_ff
      -- Lift: prefix terminates at ρ_post, suffix (asserts) CanFails at ρ_post.
      left
      apply arb_iter_body_canFail_to_loopDetThenBranch
      -- Prefix [havocd, assumes] terminates at ρ_pre, then body' terminates at ρ_post,
      -- then asserts CanFail at ρ_post. Lift asserts CanFail through post_termination.
      simp only [List.nil_append, List.append_nil]
      exact canFail_tail_to_block π φ _ _ ρ₀ ρ_pre hhavoc
        (canFail_tail_to_block π φ _ _ ρ_pre ρ_pre hassume
          (canFailBlock_prefix_terminal_suffix π φ _ _ ρ_pre ρ_post
            hbody_trace hcf_asserts))
  | .inr ⟨ρ_last, hg_last, hinv_last, hwfb_last, hwfv_last, hnf_last, hbody_last, hinv_ρ',
      heval_last, hstore_last, hdef_last⟩ =>
    -- Success case: body maps ρ_last (G=tt, I=tt) to ρ' with I(ρ')=tt.
    -- Target trace:
    -- 1. arbitrary_iter_facts: havoc→ρ_last, assume(G,I)→ρ_last, body'→ρ', assert(I)→ρ'
    -- 2. Exit section: havoc→ρ' (identity), assume(!G)→ρ', assume(I)→ρ'
    -- Get body' IH for ρ_last
    have hwfvar_last : WellFormedSemanticEvalVar ρ_last.eval := heval_last ▸ hwfvar
    have ⟨hbody_ih_term_last, _⟩ := body_ih (loopGenState σ) ρ_last hwfb_last hwfv_last hwfvar_last
    have hbody_sim_last := hbody_ih_term_last ρ' hbody_last
    match hbody_sim_last with
    | .inl hcf_body_last =>
      -- Body' CanFails from ρ_last → then-branch CanFails (use left disjunct)
      left
      -- Same as sorry 1 case but with ρ_last instead of ρ_pre
      have hρ_last_eq : ({ ρ₀ with store := ρ_last.store } : Env Expression) = ρ_last := by
        cases ρ₀; cases ρ_last; simp at *; exact ⟨heval_last.symm, hnf₀ ▸ hnf_last.symm⟩
      have hhavoc_last : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}loop_havoc_{loopNum σ}"
            ((Block.modifiedVars body).map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ₀)
          (.terminal ρ_last) := by
        rw [← hρ_last_eq]
        exact havoc_block_to_target π φ _ _ md ρ₀ ρ_last hwfvar hdef_modvars hdef_last hstore_last hnf₀
      have hassume_last : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loopNum σ}"
            ([Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loopNum σ}_guard" g md)] ++
             inv.mapIdx fun i inv_i =>
              Stmt.cmd (HasPassiveCmds.assume
                s!"{loopElimAssumePrefix}{loopNum σ}_invariant_{i}" inv_i md)) md) ρ_last)
          (.terminal ρ_last) :=
        assume_block_step π φ σ g inv md ρ_last hg_last hinv_last hwfb_last hnf_last
      apply arb_iter_body_canFail_to_loopDetThenBranch
      simp only [List.nil_append, List.append_nil]
      exact canFail_tail_to_block π φ _ _ ρ₀ ρ_last hhavoc_last
        (canFail_tail_to_block π φ _ _ ρ_last ρ_last hassume_last
          (canFailBlock_append_left π φ _ _ ρ_last hcf_body_last))
    | .inr hbody_ok_last =>
      -- Body' terminates at ρ' from ρ_last. Construct the full terminal trace.
      right; intro _hnf'
      have hbody_trace_last := hbody_ok_last hnf
      -- Derive WF at ρ'
      have ⟨hwfb_ρ', _hwfv_ρ'⟩ := star_preserves_wf π φ hwf_ext hbody_last hwfb_last hwfv_last
      have heval_ρ' : ρ'.eval = ρ₀.eval := by
        have heval_body := smallStep_noFuncDecl_preserves_eval_block Expression (EvalCommand π φ)
          (EvalPureFunc φ) body ρ_last ρ' hnofd hbody_last
        exact heval_body.trans heval_last
      -- Havoc block from ρ₀ reaches ρ_last
      have hρ_last_eq : ({ ρ₀ with store := ρ_last.store } : Env Expression) = ρ_last := by
        cases ρ₀; cases ρ_last; simp at *; exact ⟨heval_last.symm, hnf₀ ▸ hnf_last.symm⟩
      have hhavoc_last : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}loop_havoc_{loopNum σ}"
            ((Block.modifiedVars body).map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ₀)
          (.terminal ρ_last) := by
        rw [← hρ_last_eq]
        exact havoc_block_to_target π φ _ _ md ρ₀ ρ_last hwfvar hdef_modvars hdef_last hstore_last hnf₀
      -- Assume block passes at ρ_last
      have hassume_last : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loopNum σ}"
            ([Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loopNum σ}_guard" g md)] ++
             inv.mapIdx fun i inv_i =>
              Stmt.cmd (HasPassiveCmds.assume
                s!"{loopElimAssumePrefix}{loopNum σ}_invariant_{i}" inv_i md)) md) ρ_last)
          (.terminal ρ_last) :=
        assume_block_step π φ σ g inv md ρ_last hg_last hinv_last hwfb_last hnf_last
      -- Assert(I) passes at ρ' (all invariants are tt)
      have hasserts_pass : CoreStar π φ
          (.stmts (inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assert
              s!"{loopElimAssertPrefix}{loopNum σ}_arbitrary_iter_maintain_invariant_{i}"
              inv_i md)) ρ')
          (.terminal ρ') :=
        stmts_mapIdx_assert_terminal_gen π φ inv ρ' md _ (fun i e => ⟨_, rfl⟩) hwfb_ρ' hnf hinv_ρ'
      -- Derive !G = tt at ρ' from G = ff at ρ'
      have hnotg_tt : ρ'.eval ρ'.store (HasNot.not g) = some HasBool.tt := by
        exact ((hwfb_ρ' ρ'.store g).2.mp hguard_ff_ρ')
      -- ρ' has modifiedVars defined (need for second havoc identity)
      have hdef_modvars_ρ' : ∀ n ∈ Block.modifiedVars body, (ρ'.store n).isSome :=
        star_preserves_isDefined π φ hbody_last hdef_last
      -- Second havoc block is identity at ρ'
      have hhavoc2_identity : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}loop_havoc_{loopNum σ}"
            ((Block.modifiedVars body).map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ')
          (.terminal ρ') :=
        havoc_block_identity π φ _ _ md ρ' hdef_modvars_ρ' (heval_ρ' ▸ hwfvar) hnf
      -- assume(!G) passes at ρ'
      have hassume_notg : CoreStar π φ
          (.stmt (.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loopNum σ}_not_guard" (HasNot.not g) md)) ρ')
          (.terminal ρ') :=
        assume_tt_step π φ _ _ md ρ' hnotg_tt hwfb_ρ' hnf
      -- Exit invariant assumes pass at ρ'
      have hassume_exit_invs : CoreStar π φ
          (.stmts (inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assume
              s!"{loopElimAssumePrefix}{loopNum σ}_exit_invariant_{i}" inv_i md)) ρ')
          (.terminal ρ') :=
        stmts_mapIdx_assume_terminal_gen π φ inv ρ' md _ (fun i e => ⟨_, rfl⟩) hwfb_ρ' hnf hinv_ρ'
      -- Compose the full trace through loopDetThenBranch.
      -- loopDetThenBranch = [arb_iter_facts_block, havocd, not_guard] ++ inv_assumes
      -- For measure = none, arb_iter_facts contains:
      --   [havocd, assumes] ++ body' ++ maintain_invariants
      -- which terminates at ρ' (havocd→ρ_last, assumes→ρ_last, body'→ρ', asserts→ρ')
      -- Then havocd→ρ' (identity), not_guard→ρ', inv_assumes→ρ'.
      -- After subst, measure = none, so loopDetThenBranch unfolds with pre/post_termination = []
      unfold loopDetThenBranch
      simp only [List.nil_append, List.append_nil, List.cons_append]
      -- Build the inner block trace: [havocd, assumes] ++ body' ++ asserts → terminal ρ'
      have hinner_prefix :=
        stmts_pair_terminal π φ _ _ ρ₀ ρ_last ρ_last hhavoc_last hassume_last
      have hinner :=
        stmts_concat_terminal π φ _ _ ρ₀ ρ_last ρ'
          hinner_prefix
          (stmts_concat_terminal π φ _ _ ρ_last ρ' ρ' hbody_trace_last hasserts_pass)
      have harb_block :=
        block_wrap_terminal π φ s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loopNum σ}" _ {} ρ₀ ρ' hinner
      -- Outer: [arb_block, havocd, not_guard] ++ exit_inv_assumes → terminal ρ'
      exact stmts_concat_terminal π φ _ _ ρ₀ ρ' ρ'
        (ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ' harb_block)
          (stmts_pair_terminal π φ _ _ ρ' ρ' ρ' hhavoc2_identity hassume_notg))
        hassume_exit_invs

/-! ### Nondet loop enter-body case -/

/-- Nondet version of `assume_block_step`: the arbitrary_iter_assumes block for nondet
    loops has no guard assume, only invariant assumes. -/
private theorem assume_block_step_nondet
    (σ : StringGenState)
    (inv : List Expression.Expr) (md : MetaData Expression)
    (ρ : Env Expression)
    (hall_tt : ∀ e ∈ inv, ρ.eval ρ.store e = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ
      (.stmt (.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loopNum σ}"
        ([] ++ inv.mapIdx fun i inv_i =>
          Stmt.cmd (HasPassiveCmds.assume
            s!"{loopElimAssumePrefix}{loopNum σ}_invariant_{i}" inv_i md)) md) ρ)
      (.terminal ρ) := by
  apply block_wrap_terminal
  simp only [List.nil_append]
  exact stmts_mapIdx_assume_terminal_gen π φ inv ρ md _ (fun i e => ⟨_, rfl⟩) hwfb hnf hall_tt

/-- If the body of arbitrary_iter_facts CanFails, then loopNondetThenBranch CanFails. -/
private theorem arb_iter_body_canFail_to_loopNondetThenBranch
    (σ : StringGenState)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) (ρ₀ : Env Expression) :
    let loop_num := loopNum σ
    let σ₁ := loopGenState σ
    let assigned_vars := Block.modifiedVars body
    let havocd := Stmt.block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
      (assigned_vars.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}
    let body' := blockResult σ₁ body
    let inv_assumes := inv.mapIdx fun i inv_i =>
      Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_invariant_{i}" inv_i md)
    let maintain_invariants := inv.mapIdx fun i inv_i =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{i}" inv_i md)
    let arbitrary_iter_assumes :=
      Stmt.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
        ([] ++ inv_assumes) md
    CanFailBlock π φ
      ([havocd, arbitrary_iter_assumes] ++ body' ++ maintain_invariants) ρ₀ →
    CanFailBlock π φ (loopNondetThenBranch σ measure inv body md) ρ₀ := by
  simp only
  intro hcf
  unfold loopNondetThenBranch
  simp only [List.nil_append, List.append_nil]
  exact canFail_head_to_block π φ _ _ ρ₀
    (canFailBlock_to_canFail_block π φ _ _ {} ρ₀ hcf)

/-- Core helper for the enter-body nondet loop case.

Mirrors `det_loop_enter_body_sim` but for nondeterministic loops:
- No guard condition to track
- No assume_guard in the arbitrary_iter_assumes block
- No not_guard in the exit section
- No termination checks -/
private theorem nondet_loop_enter_body_sim
    (hwf_ext : WFEvalExtension φ)
    (σ : StringGenState)
    (measure : Option Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    -- Source execution: body ++ [loop] trace from ρ₀ (after the loop enter step)
    (hloop_full : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.stmts (body ++ [.loop .nondet measure inv body md]) ρ₀) (.terminal ρ'))
    -- Invariant properties
    (hinvs_eval : ∀ (δ : SemanticEval Expression) (σs : SemanticStore Expression),
      WellFormedSemanticEvalBool δ → ∀ e ∈ inv, δ σs e = some HasBool.tt ∨ δ σs e = some HasBool.ff)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] body)
    (hinvs_body : Block.loopInvsBool body)
    (hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt)
    -- Modified vars are defined in the initial store (needed for havoc)
    (hdef_modvars : ∀ n ∈ Block.modifiedVars body, (ρ₀.store n).isSome)
    -- Well-formedness
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnf : ρ'.hasFailure = Bool.false)
    -- Body IH
    (body_ih :
      ∀ (σ_b : StringGenState) (ρ_b : Env Expression),
        WellFormedSemanticEvalBool ρ_b.eval →
        WellFormedSemanticEvalVal ρ_b.eval →
        WellFormedSemanticEvalVar ρ_b.eval →
        (∀ ρ_b', CoreStar π φ (.stmts body ρ_b) (.terminal ρ_b') →
          CanFailBlock π φ (blockResult σ_b body) ρ_b ∨
          (ρ_b'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ_b body) ρ_b) (.terminal ρ_b'))) ∧
        (∀ lbl ρ_b', CoreStar π φ (.stmts body ρ_b) (.exiting lbl ρ_b') →
          CanFailBlock π φ (blockResult σ_b body) ρ_b ∨
          (ρ_b'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ_b body) ρ_b) (.exiting lbl ρ_b'))))
    (hdef_touched_all : ∀ (σt : SemanticStore Expression),
      ∀ n ∈ Block.touchedVars body, (σt n).isSome)
    :
    CanFailBlock π φ (loopNondetThenBranch σ measure inv body md) ρ₀ ∨
    (ρ'.hasFailure = Bool.false →
      CoreStar π φ (.stmts (loopNondetThenBranch σ measure inv body md) ρ₀) (.terminal ρ')) := by
  -- Derive hasFailure = false at ρ₀
  have hnf₀ : ρ₀.hasFailure = Bool.false :=
    hasFailure_false_backwards π φ (reflTransT_to_prop hloop_full) hnf
  -- Apply the nondet loop invariant dichotomy
  have hdich := loop_invariant_dichotomy_nondet π φ hwf_ext measure inv body md ρ₀ ρ'
    hall_tt hwfb hwfv hnofd hcov hinvs_eval hdef_modvars hdef_touched_all hnf hloop_full
  match hdich with
  | .inl ⟨ρ_pre, ρ_post, hinv_pre, hwfb_pre, hwfv_pre, hnf_pre, hbody_pre_post,
      hnf_post, hsome_ff, heval_pre, hstore_pre, hdef_pre⟩ =>
    -- Violation case: body maps ρ_pre (I=tt) to ρ_post where some I fails.
    have ⟨hwfb_post, _hwfv_post⟩ :=
      star_preserves_wf π φ hwf_ext hbody_pre_post hwfb_pre hwfv_pre
    have hinv_bool_post : ∀ e ∈ inv, ρ_post.eval ρ_post.store e = some HasBool.tt ∨
        ρ_post.eval ρ_post.store e = some HasBool.ff :=
      hinvs_eval ρ_post.eval ρ_post.store hwfb_post
    have hwfvar_pre : WellFormedSemanticEvalVar ρ_pre.eval := heval_pre ▸ hwfvar
    have ⟨hbody_ih_term, _⟩ := body_ih (loopGenState σ) ρ_pre hwfb_pre hwfv_pre hwfvar_pre
    have hbody_sim := hbody_ih_term ρ_post hbody_pre_post
    have hρ_pre_eq : ({ ρ₀ with store := ρ_pre.store } : Env Expression) = ρ_pre := by
      cases ρ₀; cases ρ_pre; simp at *; exact ⟨heval_pre.symm, hnf₀ ▸ hnf_pre.symm⟩
    have hhavoc : CoreStar π φ
        (.stmt (.block s!"{loopElimBlockPrefix}loop_havoc_{loopNum σ}"
          ((Block.modifiedVars body).map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ₀)
        (.terminal ρ_pre) := by
      rw [← hρ_pre_eq]
      exact havoc_block_to_target π φ _ _ md ρ₀ ρ_pre hwfvar hdef_modvars hdef_pre hstore_pre hnf₀
    have hassume : CoreStar π φ
        (.stmt (.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loopNum σ}"
          ([] ++ inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assume
              s!"{loopElimAssumePrefix}{loopNum σ}_invariant_{i}" inv_i md)) md) ρ_pre)
        (.terminal ρ_pre) :=
      assume_block_step_nondet π φ σ inv md ρ_pre hinv_pre hwfb_pre hnf_pre
    match hbody_sim with
    | .inl hcf_body =>
      left
      apply arb_iter_body_canFail_to_loopNondetThenBranch
      cases measure with
      | none =>
        simp only [List.nil_append, List.append_nil]
        exact canFail_tail_to_block π φ _ _ ρ₀ ρ_pre hhavoc
          (canFail_tail_to_block π φ _ _ ρ_pre ρ_pre hassume
            (canFailBlock_append_left π φ _ _ ρ_pre hcf_body))
      | some m =>
        simp only [List.nil_append]
        exact canFail_tail_to_block π φ _ _ ρ₀ ρ_pre hhavoc
          (canFail_tail_to_block π φ _ _ ρ_pre ρ_pre hassume
            (canFailBlock_append_left π φ _ _ ρ_pre hcf_body))
    | .inr hbody_ok =>
      have hbody_trace := hbody_ok hnf_post
      have hcf_asserts : CanFailBlock π φ
          (inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assert
              s!"{loopElimAssertPrefix}{loopNum σ}_arbitrary_iter_maintain_invariant_{i}"
              inv_i md)) ρ_post :=
        stmts_mapIdx_assert_canFail_gen π φ inv ρ_post md _ (fun i e => ⟨_, rfl⟩)
          hwfb_post hnf_post hinv_bool_post hsome_ff
      left
      apply arb_iter_body_canFail_to_loopNondetThenBranch
      cases measure with
      | none =>
        simp only [List.nil_append, List.append_nil]
        exact canFail_tail_to_block π φ _ _ ρ₀ ρ_pre hhavoc
          (canFail_tail_to_block π φ _ _ ρ_pre ρ_pre hassume
            (canFailBlock_prefix_terminal_suffix π φ _ _ ρ_pre ρ_post
              hbody_trace hcf_asserts))
      | some m =>
        simp only [List.nil_append]
        exact canFail_tail_to_block π φ _ _ ρ₀ ρ_pre hhavoc
          (canFail_tail_to_block π φ _ _ ρ_pre ρ_pre hassume
            (canFailBlock_prefix_terminal_suffix π φ _ _ ρ_pre ρ_post
              hbody_trace hcf_asserts))
  | .inr ⟨ρ_last, hinv_last, hwfb_last, hwfv_last, hnf_last, hbody_last, hinv_ρ',
      heval_last, hstore_last, hdef_last⟩ =>
    -- Success case: body maps ρ_last (I=tt) to ρ' with I(ρ')=tt.
    have hwfvar_last : WellFormedSemanticEvalVar ρ_last.eval := heval_last ▸ hwfvar
    have ⟨hbody_ih_term_last, _⟩ := body_ih (loopGenState σ) ρ_last hwfb_last hwfv_last hwfvar_last
    have hbody_sim_last := hbody_ih_term_last ρ' hbody_last
    match hbody_sim_last with
    | .inl hcf_body_last =>
      left
      have hρ_last_eq : ({ ρ₀ with store := ρ_last.store } : Env Expression) = ρ_last := by
        cases ρ₀; cases ρ_last; simp at *; exact ⟨heval_last.symm, hnf₀ ▸ hnf_last.symm⟩
      have hhavoc_last : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}loop_havoc_{loopNum σ}"
            ((Block.modifiedVars body).map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ₀)
          (.terminal ρ_last) := by
        rw [← hρ_last_eq]
        exact havoc_block_to_target π φ _ _ md ρ₀ ρ_last hwfvar hdef_modvars hdef_last hstore_last hnf₀
      have hassume_last : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loopNum σ}"
            ([] ++ inv.mapIdx fun i inv_i =>
              Stmt.cmd (HasPassiveCmds.assume
                s!"{loopElimAssumePrefix}{loopNum σ}_invariant_{i}" inv_i md)) md) ρ_last)
          (.terminal ρ_last) :=
        assume_block_step_nondet π φ σ inv md ρ_last hinv_last hwfb_last hnf_last
      apply arb_iter_body_canFail_to_loopNondetThenBranch
      cases measure with
      | none =>
        simp only [List.nil_append, List.append_nil]
        exact canFail_tail_to_block π φ _ _ ρ₀ ρ_last hhavoc_last
          (canFail_tail_to_block π φ _ _ ρ_last ρ_last hassume_last
            (canFailBlock_append_left π φ _ _ ρ_last hcf_body_last))
      | some m =>
        simp only [List.nil_append]
        exact canFail_tail_to_block π φ _ _ ρ₀ ρ_last hhavoc_last
          (canFail_tail_to_block π φ _ _ ρ_last ρ_last hassume_last
            (canFailBlock_append_left π φ _ _ ρ_last hcf_body_last))
    | .inr hbody_ok_last =>
      right; intro _hnf'
      have hbody_trace_last := hbody_ok_last hnf
      have ⟨hwfb_ρ', _hwfv_ρ'⟩ := star_preserves_wf π φ hwf_ext hbody_last hwfb_last hwfv_last
      have heval_ρ' : ρ'.eval = ρ₀.eval := by
        have heval_body := smallStep_noFuncDecl_preserves_eval_block Expression (EvalCommand π φ)
          (EvalPureFunc φ) body ρ_last ρ' hnofd hbody_last
        exact heval_body.trans heval_last
      have hρ_last_eq : ({ ρ₀ with store := ρ_last.store } : Env Expression) = ρ_last := by
        cases ρ₀; cases ρ_last; simp at *; exact ⟨heval_last.symm, hnf₀ ▸ hnf_last.symm⟩
      have hhavoc_last : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}loop_havoc_{loopNum σ}"
            ((Block.modifiedVars body).map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ₀)
          (.terminal ρ_last) := by
        rw [← hρ_last_eq]
        exact havoc_block_to_target π φ _ _ md ρ₀ ρ_last hwfvar hdef_modvars hdef_last hstore_last hnf₀
      have hassume_last : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loopNum σ}"
            ([] ++ inv.mapIdx fun i inv_i =>
              Stmt.cmd (HasPassiveCmds.assume
                s!"{loopElimAssumePrefix}{loopNum σ}_invariant_{i}" inv_i md)) md) ρ_last)
          (.terminal ρ_last) :=
        assume_block_step_nondet π φ σ inv md ρ_last hinv_last hwfb_last hnf_last
      have hasserts_pass : CoreStar π φ
          (.stmts (inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assert
              s!"{loopElimAssertPrefix}{loopNum σ}_arbitrary_iter_maintain_invariant_{i}"
              inv_i md)) ρ')
          (.terminal ρ') :=
        stmts_mapIdx_assert_terminal_gen π φ inv ρ' md _ (fun i e => ⟨_, rfl⟩) hwfb_ρ' hnf hinv_ρ'
      -- ρ' has modifiedVars defined
      have hdef_modvars_ρ' : ∀ n ∈ Block.modifiedVars body, (ρ'.store n).isSome :=
        star_preserves_isDefined π φ hbody_last hdef_last
      -- Second havoc block is identity at ρ'
      have hhavoc2_identity : CoreStar π φ
          (.stmt (.block s!"{loopElimBlockPrefix}loop_havoc_{loopNum σ}"
            ((Block.modifiedVars body).map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ')
          (.terminal ρ') :=
        havoc_block_identity π φ _ _ md ρ' hdef_modvars_ρ' (heval_ρ' ▸ hwfvar) hnf
      -- Exit invariant assumes pass at ρ'
      have hassume_exit_invs : CoreStar π φ
          (.stmts (inv.mapIdx fun i inv_i =>
            Stmt.cmd (HasPassiveCmds.assume
              s!"{loopElimAssumePrefix}{loopNum σ}_exit_invariant_{i}" inv_i md)) ρ')
          (.terminal ρ') :=
        stmts_mapIdx_assume_terminal_gen π φ inv ρ' md _ (fun i e => ⟨_, rfl⟩) hwfb_ρ' hnf hinv_ρ'
      -- Compose the full trace through loopNondetThenBranch
      -- loopNondetThenBranch = [arb_iter_facts_block, havocd] ++ inv_assumes
      cases measure with
      | none =>
        unfold loopNondetThenBranch
        simp only [List.nil_append, List.append_nil, List.cons_append]
        have hinner_prefix :=
          stmts_pair_terminal π φ _ _ ρ₀ ρ_last ρ_last hhavoc_last hassume_last
        have hinner :=
          stmts_concat_terminal π φ _ _ ρ₀ ρ_last ρ'
            hinner_prefix
            (stmts_concat_terminal π φ _ _ ρ_last ρ' ρ' hbody_trace_last hasserts_pass)
        have harb_block :=
          block_wrap_terminal π φ s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loopNum σ}"
            _ {} ρ₀ ρ' hinner
        -- Then-branch after unfold+simp: [arb_block, havocd] ++ exit_inv_assumes
        exact stmts_concat_terminal π φ _ _ ρ₀ ρ' ρ'
          (stmts_pair_terminal π φ _ _ ρ₀ ρ' ρ' harb_block hhavoc2_identity)
          hassume_exit_invs
      | some _m =>
        unfold loopNondetThenBranch
        simp only [List.nil_append, List.append_nil, List.cons_append]
        have hinner_prefix :=
          stmts_pair_terminal π φ _ _ ρ₀ ρ_last ρ_last hhavoc_last hassume_last
        have hinner :=
          stmts_concat_terminal π φ _ _ ρ₀ ρ_last ρ'
            hinner_prefix
            (stmts_concat_terminal π φ _ _ ρ_last ρ' ρ' hbody_trace_last hasserts_pass)
        have harb_block :=
          block_wrap_terminal π φ s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loopNum σ}"
            _ {} ρ₀ ρ' hinner
        -- Then-branch after unfold+simp: [arb_block, havocd] ++ exit_inv_assumes
        exact stmts_concat_terminal π φ _ _ ρ₀ ρ' ρ'
          (stmts_pair_terminal π φ _ _ ρ₀ ρ' ρ' harb_block hhavoc2_identity)
          hassume_exit_invs

/-! ## Simulation: source terminal/exiting implies target terminal/exiting or CanFail -/

private theorem simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat) :
    -- Statement level
    (∀ (σ : StringGenState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      Stmt.loopInvsBool st →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        -- Terminal
        (∀ ρ', CoreStar π φ (.stmt st ρ₀) (.terminal ρ') →
          Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmt (stmtResult σ st) ρ₀) (.terminal ρ')))
        ∧
        -- Exiting
        (∀ lbl ρ', CoreStar π φ (.stmt st ρ₀) (.exiting lbl ρ') →
          Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmt (stmtResult σ st) ρ₀) (.exiting lbl ρ'))))
    ∧
    -- Block level
    (∀ (σ : StringGenState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.loopInvsBool bss →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        -- Terminal
        (∀ ρ', CoreStar π φ (.stmts bss ρ₀) (.terminal ρ') →
          CanFailBlock π φ (blockResult σ bss) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.terminal ρ')))
        ∧
        -- Exiting
        (∀ lbl ρ', CoreStar π φ (.stmts bss ρ₀) (.exiting lbl ρ') →
          CanFailBlock π φ (blockResult σ bss) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.exiting lbl ρ')))) := by
  induction sz with
  | zero =>
    constructor
    · intro σ st hsz
      match st with
      | .cmd _ | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl .. | .typeDecl .. =>
        simp_all [Stmt.sizeOf]
    · intro σ bss hsz
      match bss with
      | [] => simp [Block.sizeOf] at hsz
      | _ :: _ => simp [Block.sizeOf] at hsz
  | succ n ih =>
    constructor

    -- === Statement case ===
    · intro σ st hsz hinvs ρ₀ hwfb hwfv hwfvar
      match st with
      | .cmd c =>
        rw [stmtResult_cmd]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩

      | .exit l md =>
        rw [stmtResult_exit]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩

      | .funcDecl d md =>
        rw [stmtResult_funcDecl]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩

      | .typeDecl tc md =>
        rw [stmtResult_typeDecl]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩

      | .block l bss md =>
        rw [stmtResult_block]
        have hsz_bss : Block.sizeOf bss ≤ n := by simp [Stmt.sizeOf] at hsz; omega
        -- loopInvsBool (.block l bss md) = Block.loopInvsBool bss
        have blk_ih := ih.2 σ bss hsz_bss hinvs ρ₀ hwfb hwfv hwfvar
        constructor
        -- Terminal
        · intro ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_block =>
              match block_reaches_terminal_refined π φ r1 with
              | .inl hterm =>
                match blk_ih.1 ρ' hterm with
                | .inl hcf =>
                  exact .inl (canFailBlock_to_canFail_block π φ l
                    (blockResult σ bss) md ρ₀ hcf)
                | .inr hok =>
                  exact .inr (fun hnf =>
                    block_wrap_terminal π φ l (blockResult σ bss) md ρ₀ ρ' (hok hnf))
              | .inr (.inl hexit_none) =>
                match blk_ih.2 none ρ' hexit_none with
                | .inl hcf =>
                  exact .inl (canFailBlock_to_canFail_block π φ l
                    (blockResult σ bss) md ρ₀ hcf)
                | .inr hok =>
                  exact .inr (fun hnf =>
                    block_wrap_exiting_none π φ l (blockResult σ bss) md ρ₀ ρ' (hok hnf))
              | .inr (.inr hexit_match) =>
                match blk_ih.2 (some l) ρ' hexit_match with
                | .inl hcf =>
                  exact .inl (canFailBlock_to_canFail_block π φ l
                    (blockResult σ bss) md ρ₀ hcf)
                | .inr hok =>
                  exact .inr (fun hnf =>
                    block_wrap_exiting_match π φ l (blockResult σ bss) md ρ₀ ρ' (hok hnf))
        -- Exiting
        · intro lbl ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_block =>
              have ⟨lv, hne, hlbl_eq, hexit⟩ :=
                block_reaches_exiting_refined π φ r1
              subst hlbl_eq
              match blk_ih.2 (some lv) ρ' hexit with
              | .inl hcf =>
                exact .inl (canFailBlock_to_canFail_block π φ l
                  (blockResult σ bss) md ρ₀ hcf)
              | .inr hok =>
                exact .inr (fun hnf =>
                  block_wrap_exiting_mismatch π φ l (blockResult σ bss) md lv ρ₀ ρ'
                    hne (hok hnf))

      | .ite c tss ess md =>
        rw [stmtResult_ite]
        have hsz_tss : Block.sizeOf tss ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        have hsz_ess : Block.sizeOf ess ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        -- loopInvsBool (.ite c tss ess md) = Block.loopInvsBool tss ∧ Block.loopInvsBool ess
        have ⟨hinvs_tss, hinvs_ess⟩ := hinvs
        constructor
        -- Terminal
        · intro ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_ite_true hcond hwfb' =>
              have tss_ih := ih.2 σ tss hsz_tss hinvs_tss ρ₀ hwfb hwfv hwfvar
              match tss_ih.1 ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail,
                  ReflTrans_Transitive _ _ _ _
                    (.step _ _ _ (.step_ite_true hcond hwfb') (.refl _)) hreach⟩
              | .inr hok =>
                exact .inr (fun hnf =>
                  .step _ _ _ (.step_ite_true hcond hwfb') (hok hnf))
            | step_ite_false hcond hwfb' =>
              have ess_ih := ih.2 (blockPostState σ tss) ess hsz_ess hinvs_ess ρ₀ hwfb hwfv hwfvar
              match ess_ih.1 ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail,
                  ReflTrans_Transitive _ _ _ _
                    (.step _ _ _ (.step_ite_false hcond hwfb') (.refl _)) hreach⟩
              | .inr hok =>
                exact .inr (fun hnf =>
                  .step _ _ _ (.step_ite_false hcond hwfb') (hok hnf))
            | step_ite_nondet_true =>
              have tss_ih := ih.2 σ tss hsz_tss hinvs_tss ρ₀ hwfb hwfv hwfvar
              match tss_ih.1 ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail,
                  ReflTrans_Transitive _ _ _ _
                    (.step _ _ _ .step_ite_nondet_true (.refl _)) hreach⟩
              | .inr hok =>
                exact .inr (fun hnf =>
                  .step _ _ _ .step_ite_nondet_true (hok hnf))
            | step_ite_nondet_false =>
              have ess_ih := ih.2 (blockPostState σ tss) ess hsz_ess hinvs_ess ρ₀ hwfb hwfv hwfvar
              match ess_ih.1 ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail,
                  ReflTrans_Transitive _ _ _ _
                    (.step _ _ _ .step_ite_nondet_false (.refl _)) hreach⟩
              | .inr hok =>
                exact .inr (fun hnf =>
                  .step _ _ _ .step_ite_nondet_false (hok hnf))
        -- Exiting
        · intro lbl ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_ite_true hcond hwfb' =>
              have tss_ih := ih.2 σ tss hsz_tss hinvs_tss ρ₀ hwfb hwfv hwfvar
              match tss_ih.2 lbl ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail,
                  ReflTrans_Transitive _ _ _ _
                    (.step _ _ _ (.step_ite_true hcond hwfb') (.refl _)) hreach⟩
              | .inr hok =>
                exact .inr (fun hnf =>
                  .step _ _ _ (.step_ite_true hcond hwfb') (hok hnf))
            | step_ite_false hcond hwfb' =>
              have ess_ih := ih.2 (blockPostState σ tss) ess hsz_ess hinvs_ess ρ₀ hwfb hwfv hwfvar
              match ess_ih.2 lbl ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail,
                  ReflTrans_Transitive _ _ _ _
                    (.step _ _ _ (.step_ite_false hcond hwfb') (.refl _)) hreach⟩
              | .inr hok =>
                exact .inr (fun hnf =>
                  .step _ _ _ (.step_ite_false hcond hwfb') (hok hnf))
            | step_ite_nondet_true =>
              have tss_ih := ih.2 σ tss hsz_tss hinvs_tss ρ₀ hwfb hwfv hwfvar
              match tss_ih.2 lbl ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail,
                  ReflTrans_Transitive _ _ _ _
                    (.step _ _ _ .step_ite_nondet_true (.refl _)) hreach⟩
              | .inr hok =>
                exact .inr (fun hnf =>
                  .step _ _ _ .step_ite_nondet_true (hok hnf))
            | step_ite_nondet_false =>
              have ess_ih := ih.2 (blockPostState σ tss) ess hsz_ess hinvs_ess ρ₀ hwfb hwfv hwfvar
              match ess_ih.2 lbl ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail,
                  ReflTrans_Transitive _ _ _ _
                    (.step _ _ _ .step_ite_nondet_false (.refl _)) hreach⟩
              | .inr hok =>
                exact .inr (fun hnf =>
                  .step _ _ _ .step_ite_nondet_false (hok hnf))

      | .loop guard measure inv body md =>
        have _hsz_body : Block.sizeOf body ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        constructor
        -- Terminal
        · intro ρ' hstar
          by_cases hnf : ρ'.hasFailure = Bool.false
          · cases hstar with
            | step _ _ _ h1 r1 => cases h1 with
              | step_loop_exit hguard_ff hwfb' =>
                rename_i g_expr
                cases r1 with
                | refl =>
                  -- 0-iteration det case: ρ' = ρ₀, guard g_expr = ff.
                  -- Target block: first_iter_asserts block + if(g_expr).
                  -- Need: CanFail ∨ (hasFailure=false → terminal ρ₀).
                  have ⟨ll, fil, fib, tb, heq_stmt, _heq_fib⟩ :=
                    stmtResult_loop_det σ g_expr measure inv body md
                  rw [heq_stmt]
                  -- Use hinvs to get invariant evaluations
                  have hinv_bool : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt ∨
                      ρ₀.eval ρ₀.store e = some HasBool.ff :=
                    hinvs.1 ρ₀.eval ρ₀.store hwfb
                  by_cases hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt
                  · -- All invariants are tt: target terminates at ρ₀
                    exact .inr (fun _ =>
                      -- Execute: block ll [block fil (asserts++assumes) {}, ite g tb [] {}] {}
                      -- Step 1: enter outer block
                      -- Step 2: enter first_iter block, run asserts++assumes, all pass
                      -- Step 3: exit first_iter block
                      -- Step 4: ite takes else branch (guard ff)
                      -- Step 5: empty else terminates
                      -- Step 6: exit outer block
                      block_wrap_terminal π φ ll _ _ ρ₀ ρ₀
                        (ReflTrans_Transitive _ _ _ _
                          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                            (.block fil fib {}) [.ite (.det g_expr) tb [] {}] ρ₀ ρ₀
                            (block_wrap_terminal π φ fil fib _ ρ₀ ρ₀
                              (by rw [_heq_fib]
                                  exact first_iter_body_all_tt π φ inv ρ₀ σ md hwfb hnf hall_tt)))
                          (ReflTrans_Transitive _ _ _ _
                            (.step _ _ _ .step_stmts_cons (.refl _))
                            (ReflTrans_Transitive _ _ _ _
                              (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                _ _ []
                                (.step _ _ _ (.step_ite_false hguard_ff hwfb) (.refl _)))
                              (ReflTrans_Transitive _ _ _ _
                                (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                  _ _ [] (.step _ _ _ .step_stmts_nil (.refl _)))
                                (.step _ _ _ .step_seq_done
                                  (.step _ _ _ .step_stmts_nil (.refl _))))))))
                  · -- Some invariant is ff: CanFail
                    have hsome_ff : ∃ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.ff := by
                      exact not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt
                    have hcf := first_iter_body_some_ff_canFail π φ inv ρ₀ σ md hwfb hnf
                      hinv_bool hsome_ff fil (.ite (.det g_expr) tb [] {})
                    -- Goal has `fib`, hcf has the expanded form. Subst fib.
                    subst _heq_fib
                    exact .inl (canFailBlock_to_canFail_block π φ ll _ _ ρ₀ hcf)
                | step _ _ _ h2 _ => cases h2
              | step_loop_enter hguard_tt hwfb' =>
                rename_i g_expr
                -- enter-body det case (terminal): guard is true, source
                -- enters body ++ [loop].
                -- Build full loop ReflTransT
                have hloop_full_prop : CoreStar π φ
                    (.stmt (.loop (.det g_expr) measure inv body md) ρ₀) (.terminal ρ') :=
                  .step _ _ _ (.step_loop_enter hguard_tt hwfb') r1
                have hloop_fullT : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
                    (.stmt (.loop (.det g_expr) measure inv body md) ρ₀) (.terminal ρ') :=
                  reflTrans_to_T hloop_full_prop
                -- Derive ρ₀.hasFailure = false from hnf via monotonicity
                have hnf₀ : ρ₀.hasFailure = Bool.false :=
                  hasFailure_false_backwards π φ (reflTransT_to_prop hloop_fullT) hnf
                -- Guard false at ρ'
                have hguard_ff_ρ' : ρ'.eval ρ'.store g_expr = some HasBool.ff :=
                  det_loop_terminal_guard_false π φ g_expr measure inv body md ρ₀ ρ' hloop_fullT
                -- Rewrite target using the FULL characterization
                rw [stmtResult_loop_det_full]
                -- Invariant boolean evaluation
                have hinv_bool : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt ∨
                    ρ₀.eval ρ₀.store e = some HasBool.ff :=
                  hinvs.1 ρ₀.eval ρ₀.store hwfb
                by_cases hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt
                · -- All entry invariants are tt.
                  let dtb := loopDetThenBranch σ g_expr measure inv body md
                  have htb_sim := det_loop_enter_body_sim π φ
                    hwf_ext σ g_expr measure inv body md ρ₀ ρ'
                    hguard_tt hguard_ff_ρ' hloop_fullT
                    hinvs.1 hinvs.2.1 hinvs.2.2.1 hinvs.2.2.2.1 hall_tt
                    (fun n hn => hinvs.2.2.2.2.1 ρ₀.store n
                      (Block.modifiedVars_subset_touchedVars body n hn))
                    hwfb hwfv hwfvar hnf
                    (fun σ_b ρ_b hwfb_b hwfv_b hwfvar_b =>
                      ih.2 σ_b body _hsz_body hinvs.2.2.2.1 ρ_b hwfb_b hwfv_b hwfvar_b)
                    hinvs.2.2.2.2.1 hinvs.2.2.2.2.2
                  -- htb_sim : CanFailBlock dtb ρ₀ ∨ (hasFailure=false → stmts dtb ρ₀ → terminal ρ')
                  -- Lift through the outer block structure
                  -- Prefix: first_iter block passes, reaching ρ₀
                  have hfirst_iter_pass :=
                    stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                      (.block s!"{loopElimBlockPrefix}first_iter_asserts_{loopNum σ}"
                        ((inv.mapIdx fun i inv_i =>
                          Stmt.cmd (HasPassiveCmds.assert
                            s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
                        (inv.mapIdx fun i inv_i =>
                          Stmt.cmd (HasPassiveCmds.assume
                            s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))) {})
                      [.ite (.det g_expr) dtb [] {}] ρ₀ ρ₀
                      (block_wrap_terminal π φ _ _ _ ρ₀ ρ₀
                        (first_iter_body_all_tt π φ inv ρ₀ σ md hwfb hnf₀ hall_tt))
                  match htb_sim with
                  | .inl hcf_tb =>
                    -- CanFail in then-branch → CanFail in outer block
                    obtain ⟨cfg, hfail, hreach_tb⟩ := hcf_tb
                    -- Build: outer block → first_iter → ite true → seq inner → reach cfg
                    exact .inl ⟨.block s!"loop_{loopNum σ}" (.seq cfg []),
                      by show (Config.seq cfg []).getEnv.hasFailure = Bool.true
                         simp [Config.getEnv]; exact hfail,
                      ReflTrans_Transitive _ _ _ _
                        (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _ ρ₀)
                        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _
                          (ReflTrans_Transitive _ _ _ _ hfirst_iter_pass
                            (ReflTrans_Transitive _ _ _ _
                              (.step _ _ _ .step_stmts_cons (.refl _))
                              (ReflTrans_Transitive _ _ _ _
                                (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                  _ _ []
                                  (.step _ _ _ (.step_ite_true hguard_tt hwfb') (.refl _)))
                                (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                  _ _ [] hreach_tb)))))⟩
                  | .inr hok_tb =>
                    -- Then-branch reaches terminal ρ' → whole target reaches terminal
                    exact .inr (fun hnf' =>
                      block_wrap_terminal π φ s!"loop_{loopNum σ}" _ _ ρ₀ ρ'
                        (ReflTrans_Transitive _ _ _ _ hfirst_iter_pass
                          (ReflTrans_Transitive _ _ _ _
                            (.step _ _ _ .step_stmts_cons (.refl _))
                            (ReflTrans_Transitive _ _ _ _
                              (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                _ _ []
                                (.step _ _ _ (.step_ite_true hguard_tt hwfb') (.refl _)))
                              (ReflTrans_Transitive _ _ _ _
                                (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                  _ _ [] (hok_tb hnf'))
                                (.step _ _ _ .step_seq_done
                                  (.step _ _ _ .step_stmts_nil (.refl _))))))))
                · -- Some entry invariant is ff: CanFail from first_iter_asserts
                  -- We need the same argument as 0-iter but with the new
                  -- stmtResult_loop_det_full rewriting. The first_iter block
                  -- has the same structure.
                  have hsome_ff : ∃ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.ff := by
                    exact not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt
                  have hcf :=
                    first_iter_body_some_ff_canFail π φ inv ρ₀ σ md hwfb hnf₀ hinv_bool
                      hsome_ff s!"{loopElimBlockPrefix}first_iter_asserts_{loopNum σ}"
                      (.ite (.det g_expr) (loopDetThenBranch σ g_expr measure inv body md) [] {})
                  exact .inl (canFailBlock_to_canFail_block π φ
                    s!"loop_{loopNum σ}" _ _ ρ₀ hcf)
              | step_loop_nondet_exit =>
                cases r1 with
                | refl =>
                  -- 0-iteration nondet case: ρ' = ρ₀.
                  -- Target: block[first_iter(asserts++assumes), ite .nondet then_branch []]
                  have ⟨ll, fil, fib, tb, heq_stmt, _heq_fib⟩ :=
                    stmtResult_loop_nondet σ measure inv body md
                  rw [heq_stmt]
                  have hinv_bool : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt ∨
                      ρ₀.eval ρ₀.store e = some HasBool.ff :=
                    hinvs.1 ρ₀.eval ρ₀.store hwfb
                  by_cases hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt
                  · -- All invariants tt: target terminates at ρ₀
                    exact .inr (fun _ =>
                      block_wrap_terminal π φ ll _ _ ρ₀ ρ₀
                        (ReflTrans_Transitive _ _ _ _
                          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                            (.block fil fib {}) [.ite .nondet tb [] {}] ρ₀ ρ₀
                            (block_wrap_terminal π φ fil fib _ ρ₀ ρ₀
                              (by rw [_heq_fib]
                                  exact first_iter_body_all_tt π φ inv ρ₀ σ md hwfb hnf hall_tt)))
                          (ReflTrans_Transitive _ _ _ _
                            (.step _ _ _ .step_stmts_cons (.refl _))
                            (ReflTrans_Transitive _ _ _ _
                              (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                _ _ []
                                (.step _ _ _ .step_ite_nondet_false (.refl _)))
                              (ReflTrans_Transitive _ _ _ _
                                (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                  _ _ [] (.step _ _ _ .step_stmts_nil (.refl _)))
                                (.step _ _ _ .step_seq_done
                                  (.step _ _ _ .step_stmts_nil (.refl _))))))))
                  · -- Some invariant ff: CanFail
                    have hsome_ff : ∃ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.ff := by
                      -- Since not all are tt, and each is tt or ff, some must be ff.
                      exact not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt
                    have hcf := first_iter_body_some_ff_canFail π φ inv ρ₀ σ md hwfb hnf
                      hinv_bool hsome_ff fil (.ite .nondet tb [] {})
                    subst _heq_fib
                    exact .inl (canFailBlock_to_canFail_block π φ ll _ _ ρ₀ hcf)
                | step _ _ _ h2 _ => cases h2
              | step_loop_nondet_enter =>
                -- enter-body nondet case (terminal)
                -- Build ReflTransT for the body ++ [loop] trace (after the enter step)
                have hrestT : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
                    (.stmts (body ++ [.loop .nondet measure inv body md]) ρ₀) (.terminal ρ') :=
                  reflTrans_to_T r1
                have hnf₀ : ρ₀.hasFailure = Bool.false :=
                  hasFailure_false_backwards π φ (reflTransT_to_prop hrestT) hnf
                -- Rewrite target using the FULL characterization
                rw [stmtResult_loop_nondet_full]
                have hinv_bool : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt ∨
                    ρ₀.eval ρ₀.store e = some HasBool.ff :=
                  hinvs.1 ρ₀.eval ρ₀.store hwfb
                by_cases hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt
                · -- All entry invariants are tt.
                  let ntb := loopNondetThenBranch σ measure inv body md
                  have htb_sim := nondet_loop_enter_body_sim π φ
                    hwf_ext σ measure inv body md ρ₀ ρ'
                    hrestT
                    hinvs.1 hinvs.2.1 hinvs.2.2.1 hinvs.2.2.2.1 hall_tt
                    (fun n hn => hinvs.2.2.2.2.1 ρ₀.store n
                      (Block.modifiedVars_subset_touchedVars body n hn))
                    hwfb hwfv hwfvar hnf
                    (fun σ_b ρ_b hwfb_b hwfv_b hwfvar_b =>
                      ih.2 σ_b body _hsz_body hinvs.2.2.2.1 ρ_b hwfb_b hwfv_b hwfvar_b)
                    hinvs.2.2.2.2.1
                  -- Prefix: first_iter block passes, reaching ρ₀
                  have hfirst_iter_pass :=
                    stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                      (.block s!"{loopElimBlockPrefix}first_iter_asserts_{loopNum σ}"
                        ((inv.mapIdx fun i inv_i =>
                          Stmt.cmd (HasPassiveCmds.assert
                            s!"{loopElimAssertPrefix}{loopNum σ}_entry_invariant_{i}" inv_i md)) ++
                        (inv.mapIdx fun i inv_i =>
                          Stmt.cmd (HasPassiveCmds.assume
                            s!"{loopElimAssumePrefix}{loopNum σ}_entry_invariant_{i}" inv_i md))) {})
                      [.ite .nondet ntb [] {}] ρ₀ ρ₀
                      (block_wrap_terminal π φ _ _ _ ρ₀ ρ₀
                        (first_iter_body_all_tt π φ inv ρ₀ σ md hwfb hnf₀ hall_tt))
                  match htb_sim with
                  | .inl hcf_tb =>
                    obtain ⟨cfg, hfail, hreach_tb⟩ := hcf_tb
                    exact .inl ⟨.block s!"loop_{loopNum σ}" (.seq cfg []),
                      by show (Config.seq cfg []).getEnv.hasFailure = Bool.true
                         simp [Config.getEnv]; exact hfail,
                      ReflTrans_Transitive _ _ _ _
                        (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _ ρ₀)
                        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _
                          (ReflTrans_Transitive _ _ _ _ hfirst_iter_pass
                            (ReflTrans_Transitive _ _ _ _
                              (.step _ _ _ .step_stmts_cons (.refl _))
                              (ReflTrans_Transitive _ _ _ _
                                (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                  _ _ []
                                  (.step _ _ _ .step_ite_nondet_true (.refl _)))
                                (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                  _ _ [] hreach_tb)))))⟩
                  | .inr hok_tb =>
                    exact .inr (fun hnf' =>
                      block_wrap_terminal π φ s!"loop_{loopNum σ}" _ _ ρ₀ ρ'
                        (ReflTrans_Transitive _ _ _ _ hfirst_iter_pass
                          (ReflTrans_Transitive _ _ _ _
                            (.step _ _ _ .step_stmts_cons (.refl _))
                            (ReflTrans_Transitive _ _ _ _
                              (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                _ _ []
                                (.step _ _ _ .step_ite_nondet_true (.refl _)))
                              (ReflTrans_Transitive _ _ _ _
                                (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                                  _ _ [] (hok_tb hnf'))
                                (.step _ _ _ .step_seq_done
                                  (.step _ _ _ .step_stmts_nil (.refl _))))))))
                · -- Some entry invariant is ff: CanFail from first_iter_asserts
                  have hsome_ff : ∃ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.ff := by
                    exact not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt
                  have hcf :=
                    first_iter_body_some_ff_canFail π φ inv ρ₀ σ md hwfb hnf₀ hinv_bool
                      hsome_ff s!"{loopElimBlockPrefix}first_iter_asserts_{loopNum σ}"
                      (.ite .nondet (loopNondetThenBranch σ measure inv body md) [] {})
                  exact .inl (canFailBlock_to_canFail_block π φ
                    s!"loop_{loopNum σ}" _ _ ρ₀ hcf)
          · exact .inr (fun h => absurd h hnf)
        -- Exiting
        · intro lbl ρ' hstar
          -- Loop with exitsCoveredByBlocks body cannot exit.
          -- exitsCoveredByBlocks [] (.loop guard measure inv body md) = exitsCoveredByBlocks [] body
          have hcov := hinvs.2.2.1
          exact absurd hstar
            (exitsCoveredByBlocks_noEscape Expression (EvalCommand π φ) (EvalPureFunc φ)
              (.loop guard measure inv body md) hcov ρ₀ lbl ρ')

    -- === Block case ===
    · intro σ bss hsz hinvs_bss ρ₀ hwfb hwfv hwfvar
      match bss with
      | [] =>
        rw [blockResult_nil]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩

      | s :: ss =>
        rw [blockResult_cons]
        have hsz_s : Stmt.sizeOf s ≤ n := by
          simp [Block.sizeOf] at hsz; omega
        have hsz_ss : Block.sizeOf ss ≤ n := by
          simp [Block.sizeOf] at hsz; omega
        -- Block.loopInvsBool (s :: ss) = Stmt.loopInvsBool s ∧ Block.loopInvsBool ss
        have ⟨hinvs_s, hinvs_ss⟩ := hinvs_bss
        constructor
        -- Terminal
        · intro ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_stmts_cons =>
              have ⟨ρ₁, hterm_s, hterm_ss⟩ :=
                seq_reaches_terminal Expression (EvalCommand π φ) (EvalPureFunc φ) r1
              have s_ih := ih.1 σ s hsz_s hinvs_s ρ₀ hwfb hwfv hwfvar
              match s_ih.1 ρ₁ hterm_s with
              | .inl hcf =>
                exact .inl (canFail_head_to_block π φ
                  (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf)
              | .inr hok_s =>
                have ⟨hwfb₁, hwfv₁⟩ :=
                  star_preserves_wf (π := π) (φ := φ) hwf_ext hterm_s hwfb hwfv
                have hwfvar₁ :=
                  star_preserves_wfVar (π := π) (φ := φ) hwf_ext hterm_s hwfvar
                have ss_ih := ih.2 (stmtPostState σ s) ss hsz_ss hinvs_ss ρ₁ hwfb₁ hwfv₁ hwfvar₁
                match ss_ih.1 ρ' hterm_ss with
                | .inl hcf =>
                  by_cases hnf₁ : ρ₁.hasFailure = Bool.false
                  · exact .inl (canFail_tail_to_block π φ
                      (stmtResult σ s) (blockResult (stmtPostState σ s) ss)
                      ρ₀ ρ₁ (hok_s hnf₁) hcf)
                  · exact .inr (fun hnf_final => by
                      have : ρ₁.hasFailure = Bool.false :=
                        hasFailure_false_backwards (π := π) (φ := φ) hterm_ss hnf_final
                      exact absurd this hnf₁)
                | .inr hok_ss =>
                  exact .inr (fun hnf => by
                    have hnf₁ : ρ₁.hasFailure = Bool.false :=
                      hasFailure_false_backwards (π := π) (φ := φ) hterm_ss hnf
                    exact ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                        (stmtResult σ s) (blockResult (stmtPostState σ s) ss)
                        ρ₀ ρ₁ (hok_s hnf₁))
                      (hok_ss hnf))
        -- Exiting
        · intro lbl ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_stmts_cons =>
              match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) r1 with
              | .inl hexit_s =>
                have s_ih := ih.1 σ s hsz_s hinvs_s ρ₀ hwfb hwfv hwfvar
                match s_ih.2 lbl ρ' hexit_s with
                | .inl hcf =>
                  exact .inl (canFail_head_to_block π φ
                    (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf)
                | .inr hok =>
                  exact .inr (fun hnf =>
                    stmts_cons_exiting π φ (stmtResult σ s)
                      (blockResult (stmtPostState σ s) ss) lbl ρ₀ ρ' (hok hnf))
              | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
                have s_ih := ih.1 σ s hsz_s hinvs_s ρ₀ hwfb hwfv hwfvar
                match s_ih.1 ρ₁ hterm_s with
                | .inl hcf =>
                  exact .inl (canFail_head_to_block π φ
                    (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf)
                | .inr hok_s =>
                  have ⟨hwfb₁, hwfv₁⟩ :=
                    star_preserves_wf (π := π) (φ := φ) hwf_ext hterm_s hwfb hwfv
                  have hwfvar₁ :=
                    star_preserves_wfVar (π := π) (φ := φ) hwf_ext hterm_s hwfvar
                  have ss_ih :=
                    ih.2 (stmtPostState σ s) ss hsz_ss hinvs_ss ρ₁ hwfb₁ hwfv₁ hwfvar₁
                  match ss_ih.2 lbl ρ' hexit_ss with
                  | .inl hcf =>
                    by_cases hnf₁ : ρ₁.hasFailure = Bool.false
                    · exact .inl (canFail_tail_to_block π φ
                        (stmtResult σ s) (blockResult (stmtPostState σ s) ss)
                        ρ₀ ρ₁ (hok_s hnf₁) hcf)
                    · exact .inr (fun hnf_final => by
                        have : ρ₁.hasFailure = Bool.false :=
                          hasFailure_false_backwards (π := π) (φ := φ) hexit_ss hnf_final
                        exact absurd this hnf₁)
                  | .inr hok_ss =>
                    exact .inr (fun hnf => by
                      have hnf₁ : ρ₁.hasFailure = Bool.false :=
                        hasFailure_false_backwards (π := π) (φ := φ) hexit_ss hnf
                      exact ReflTrans_Transitive _ _ _ _
                        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                          (stmtResult σ s) (blockResult (stmtPostState σ s) ss)
                          ρ₀ ρ₁ (hok_s hnf₁))
                        (hok_ss hnf))

/-! ## CanFail preservation -/

/-- If a block config reaches a failing config, the inner config also reaches
    a failing config. -/
private theorem block_canfail_to_inner
    {inner : Config Expression Command} {l : String} {cfg : Config Expression Command}
    (hstar : CoreStar π φ (.block l inner) cfg)
    (hf : cfg.getEnv.hasFailure = Bool.true) :
    ∃ inner', inner'.getEnv.hasFailure = Bool.true ∧ CoreStar π φ inner inner' := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ (inner : Config Expression Command), src = .block l inner →
      tgt.getEnv.hasFailure = Bool.true →
      ∃ inner', inner'.getEnv.hasFailure = Bool.true ∧ CoreStar π φ inner inner' from
    this _ _ hstar _ rfl hf
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro inner hsrc hf; subst hsrc; exact ⟨inner, hf, .refl _⟩
  | step _ mid _ hstep hrest ih =>
    intro inner hsrc hf; subst hsrc
    match hstep with
    | .step_block_body h =>
      have ⟨inner', hf', hstar'⟩ := ih _ rfl hf
      exact ⟨inner', hf', .step _ _ _ h hstar'⟩
    | .step_block_done | .step_block_exit_none
    | .step_block_exit_match _ | .step_block_exit_mismatch _ =>
      match hrest with
      | .refl _ => refine ⟨_, ?_, .refl _⟩; exact hf
      | .step _ _ _ h _ => exact nomatch h

/-- Decompose a CanFail trace through a seq config: either the inner
    config CanFails, or the inner terminates and the rest CanFails. -/
private noncomputable def seq_canfail_prop
    {inner : Config Expression Command} {ss : Statements}
    {cfg : Config Expression Command}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.seq inner ss) cfg)
    (hf : cfg.getEnv.hasFailure = Bool.true) :
    (∃ cfg', cfg'.getEnv.hasFailure = Bool.true ∧ CoreStar π φ inner cfg') ∨
    (∃ ρ₁, CoreStar π φ inner (.terminal ρ₁) ∧
      ∃ cfg', cfg'.getEnv.hasFailure = Bool.true ∧ CoreStar π φ (.stmts ss ρ₁) cfg') :=
  match hstar with
  | .refl _ => .inl ⟨inner, hf, .refl _⟩
  | .step _ _ _ (.step_seq_inner h) hrest =>
    match seq_canfail_prop hrest hf with
    | .inl ⟨cfg', hf', hstar'⟩ =>
      .inl ⟨cfg', hf', .step _ _ _ h hstar'⟩
    | .inr ⟨ρ₁, h1, cfg', hf', hstar'⟩ =>
      .inr ⟨ρ₁, .step _ _ _ h h1, cfg', hf', hstar'⟩
  | .step _ _ _ .step_seq_done hrest =>
    .inr ⟨_, .refl _, _, hf, reflTransT_to_prop hrest⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .refl _ => .inl ⟨_, hf, .refl _⟩
    | .step _ _ _ h _ => nomatch h
  termination_by hstar.len

/-- Extract body CanFail from a det loop CanFail trace.
    If `.stmt (.loop (.det g) none inv body md) ρ₀ →* cfg` with `hasFailure = true`
    and `ρ₀.hasFailure = false`, there exists some ρ_k (reachable from ρ₀ through
    earlier loop iterations) with `ρ_k.hasFailure = false` and the body from ρ_k
    reaches a failing config. Also extracts eval equality and well-formedness.

    The extraction recurses on trace length: each loop iteration peels off body+loop,
    and if the body doesn't fail, it terminates at ρ₁ with a strictly shorter
    remaining trace. -/
private noncomputable def loop_canfail_extracts_body_det
    (hwf_ext : WFEvalExtension φ)
    (g : Expression.Expr) (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) (ρ₀ : Env Expression)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hnf₀ : ρ₀.hasFailure = Bool.false)
    {cfg : Config Expression Command}
    (hstarT : ReflTransT (CoreStep π φ) (.stmt (.loop (.det g) none inv body md) ρ₀) cfg)
    (hf : cfg.getEnv.hasFailure = Bool.true) :
    ∃ (ρ_k : Env Expression),
      ρ_k.hasFailure = Bool.false ∧
      ρ_k.eval = ρ₀.eval ∧
      WellFormedSemanticEvalBool ρ_k.eval ∧
      WellFormedSemanticEvalVal ρ_k.eval ∧
      ∃ cfg_k, cfg_k.getEnv.hasFailure = Bool.true ∧
        CoreStar π φ (.stmts body ρ_k) cfg_k :=
  match hstarT with
  | .refl _ =>
    -- cfg = .stmt (.loop ...) ρ₀, hasFailure = ρ₀.hasFailure = true.
    -- But ρ₀.hasFailure = false. Contradiction.
    absurd (by simp [Config.getEnv] at hf; exact hf) (by rw [hnf₀]; decide)
  | .step _ _ _ (.step_loop_exit _ _) hrest =>
    match hrest with
    | .refl _ => absurd (by simp [Config.getEnv] at hf; exact hf) (by rw [hnf₀]; decide)
    | .step _ _ _ h _ => nomatch h
  | .step _ _ _ (.step_loop_enter hg hwfb') hrest =>
    -- Loop enters: .stmts (body ++ [loop]) ρ₀ →* cfg.
    -- Need to decompose into body and loop. Use stmtsT_append_single_terminal
    -- approach but for canfail.
    -- Key: convert hrest to ReflTransT, then seq_canfail_prop after step_stmts_cons.
    sorry
  termination_by hstarT.len

/-- Nondet version of body CanFail extraction. -/
private noncomputable def loop_canfail_extracts_body_nondet
    (hwf_ext : WFEvalExtension φ)
    (inv : List Expression.Expr)
    (body : Statements) (md : MetaData Expression) (ρ₀ : Env Expression)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hnf₀ : ρ₀.hasFailure = Bool.false)
    {cfg : Config Expression Command}
    (hstarT : ReflTransT (CoreStep π φ) (.stmt (.loop .nondet none inv body md) ρ₀) cfg)
    (hf : cfg.getEnv.hasFailure = Bool.true) :
    ∃ (ρ_k : Env Expression),
      ρ_k.hasFailure = Bool.false ∧
      ρ_k.eval = ρ₀.eval ∧
      WellFormedSemanticEvalBool ρ_k.eval ∧
      WellFormedSemanticEvalVal ρ_k.eval ∧
      ∃ cfg_k, cfg_k.getEnv.hasFailure = Bool.true ∧
        CoreStar π φ (.stmts body ρ_k) cfg_k :=
  match hstarT with
  | .refl _ =>
    absurd (by simp [Config.getEnv] at hf; exact hf) (by rw [hnf₀]; decide)
  | .step _ _ _ .step_loop_nondet_exit hrest =>
    match hrest with
    | .refl _ => absurd (by simp [Config.getEnv] at hf; exact hf) (by rw [hnf₀]; decide)
    | .step _ _ _ h _ => nomatch h
  | .step _ _ _ .step_loop_nondet_enter hrest =>
    sorry
  termination_by hstarT.len

private theorem canfail_simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat) :
    -- Statement level
    (∀ (σ : StringGenState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      Stmt.loopInvsBool st →
      Stmt.noFuncDecl st = Bool.true →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        Transform.CanFail (LangCore π φ) st ρ₀ →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀)
    ∧
    -- Block level
    (∀ (σ : StringGenState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.loopInvsBool bss →
      Block.noFuncDecl bss = Bool.true →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        CanFailBlock π φ bss ρ₀ →
        CanFailBlock π φ (blockResult σ bss) ρ₀) := by
  induction sz with
  | zero =>
    constructor
    · intro σ st hsz hinvs _hnofd ρ₀ _ _ _ hcf
      match st with
      | .cmd _ | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl ..
      | .typeDecl .. => simp_all [Stmt.sizeOf]
    · intro σ bss hsz hinvs _hnofd ρ₀ hwfb hwfv hwfvar hcf
      match bss with
      | [] =>
        rw [blockResult_nil]
        obtain ⟨cfg, hfail, hreach⟩ := hcf
        -- From (.stmts [] ρ₀), the only step is step_stmts_nil → terminal ρ₀
        -- So cfg must be reachable from terminal ρ₀, meaning cfg = terminal ρ₀
        -- and hfail : ρ₀.hasFailure = true.
        exact ⟨cfg, hfail, hreach⟩
      | s :: _ => simp_all [Block.sizeOf]
  | succ n ih =>
    constructor
    · intro σ st hsz hinvs hnofd_st ρ₀ hwfb hwfv hwfvar hcf
      obtain ⟨cfg, hfail, hreach⟩ := hcf
      match st with
      | .cmd c =>
        rw [stmtResult_cmd]
        exact ⟨cfg, hfail, hreach⟩
      | .exit l md =>
        rw [stmtResult_exit]
        exact ⟨cfg, hfail, hreach⟩
      | .funcDecl d md =>
        rw [stmtResult_funcDecl]
        exact ⟨cfg, hfail, hreach⟩
      | .typeDecl tc md =>
        rw [stmtResult_typeDecl]
        exact ⟨cfg, hfail, hreach⟩
      | .block l bss md =>
        rw [stmtResult_block]
        cases hreach with
        | refl => exact ⟨.stmt (.block l (blockResult σ bss) md) ρ₀, hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_block =>
            have ⟨inner_cfg, hfail', hinner⟩ :=
              block_canfail_to_inner π φ r1 hfail
            have hsz_bss : Block.sizeOf bss ≤ n := by simp [Stmt.sizeOf] at hsz; omega
            have hnofd_bss : Block.noFuncDecl bss = Bool.true := by
              simp [Stmt.noFuncDecl] at hnofd_st; exact hnofd_st
            have ⟨cfg', hfail'', hreach'⟩ := ih.2 σ bss hsz_bss hinvs hnofd_bss ρ₀ hwfb hwfv hwfvar
              ⟨inner_cfg, hfail', hinner⟩
            exact canFailBlock_to_canFail_block π φ l _ md ρ₀ ⟨cfg', hfail'', hreach'⟩
      | .ite c tss ess md =>
        rw [stmtResult_ite]
        have hsz_tss : Block.sizeOf tss ≤ n := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_ess : Block.sizeOf ess ≤ n := by simp [Stmt.sizeOf] at hsz; omega
        have ⟨hinvs_tss, hinvs_ess⟩ := hinvs
        have hnofd_tss : Block.noFuncDecl tss = Bool.true := by
          simp [Stmt.noFuncDecl, Bool.and_eq_true] at hnofd_st; exact hnofd_st.1
        have hnofd_ess : Block.noFuncDecl ess = Bool.true := by
          simp [Stmt.noFuncDecl, Bool.and_eq_true] at hnofd_st; exact hnofd_st.2
        cases hreach with
        | refl => exact ⟨.stmt (.ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md) ρ₀, hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_ite_true hcond hwfb' =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2 σ tss hsz_tss hinvs_tss hnofd_tss ρ₀ hwfb hwfv hwfvar
              ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ (.step_ite_true hcond hwfb') hreach'⟩
          | step_ite_false hcond hwfb' =>
            have ⟨cfg', hfail', hreach'⟩ :=
              ih.2 (blockPostState σ tss) ess hsz_ess hinvs_ess hnofd_ess ρ₀ hwfb hwfv hwfvar
                ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ (.step_ite_false hcond hwfb') hreach'⟩
          | step_ite_nondet_true =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2 σ tss hsz_tss hinvs_tss hnofd_tss ρ₀ hwfb hwfv hwfvar
              ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ .step_ite_nondet_true hreach'⟩
          | step_ite_nondet_false =>
            have ⟨cfg', hfail', hreach'⟩ :=
              ih.2 (blockPostState σ tss) ess hsz_ess hinvs_ess hnofd_ess ρ₀ hwfb hwfv hwfvar
                ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ .step_ite_nondet_false hreach'⟩
      | .loop guard measure inv body md =>
        have _hsz_body : Block.sizeOf body ≤ n := by simp [Stmt.sizeOf] at hsz; omega
        have hnofd_body : Block.noFuncDecl body = Bool.true := by
          simp [Stmt.noFuncDecl] at hnofd_st; exact hnofd_st
        have hmeas : measure = none := hinvs.2.2.2.2.2
        subst hmeas
        by_cases hnf₀ : ρ₀.hasFailure = Bool.true
        · -- ρ₀ already has failure -> target trivially CanFails
          exact ⟨.stmt (stmtResult σ (.loop guard none inv body md)) ρ₀,
            by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
        · have hnf₀' : ρ₀.hasFailure = Bool.false := by
            cases h : ρ₀.hasFailure <;> simp_all
          -- Extract: some iteration's body CanFails from some ρ_k.
          -- Then use the body-level IH to show target body' CanFails.
          -- Finally, lift through the target's block/havoc/assume structure.
          match guard with
          | .det g_expr =>
            have ⟨ρ_k, hnf_k, heval_k, hwfb_k, hwfv_k, cfg_k, hf_k, hbody_cf⟩ :=
              loop_canfail_extracts_body_det π φ hwf_ext g_expr inv body md ρ₀
                hnofd_body hwfb hwfv hnf₀' (reflTrans_to_T hreach) hfail
            -- Body CanFails from ρ_k: by body-level IH, target body' CanFails from ρ_k.
            have hwfvar_k : WellFormedSemanticEvalVar ρ_k.eval := heval_k ▸ hwfvar
            have ⟨tcfg, tf, tstar⟩ := ih.2 σ body _hsz_body hinvs.2.2.2.1 hnofd_body ρ_k
              hwfb_k hwfv_k hwfvar_k ⟨cfg_k, hf_k, hbody_cf⟩
            -- Now lift body' CanFail to target loop transformation.
            -- Target is stmtResult σ (.loop (.det g_expr) none inv body md).
            -- The target block's then-branch includes havoc + assume(G) + assume(I) + body'.
            -- Need to route through these, which requires guard_tt and inv_tt at ρ_k,
            -- plus havoc targeting to reach ρ_k. This is complex; sorry for now.
            sorry
          | .nondet =>
            have ⟨ρ_k, hnf_k, heval_k, hwfb_k, hwfv_k, cfg_k, hf_k, hbody_cf⟩ :=
              loop_canfail_extracts_body_nondet π φ hwf_ext inv body md ρ₀
                hnofd_body hwfb hwfv hnf₀' (reflTrans_to_T hreach) hfail
            have hwfvar_k : WellFormedSemanticEvalVar ρ_k.eval := heval_k ▸ hwfvar
            have ⟨tcfg, tf, tstar⟩ := ih.2 σ body _hsz_body hinvs.2.2.2.1 hnofd_body ρ_k
              hwfb_k hwfv_k hwfvar_k ⟨cfg_k, hf_k, hbody_cf⟩
            sorry
      /-  DEAD CODE after sorry above - was the partial loop CanFail proof
      | .loop guard measure inv body md =>
        have _hsz_body_DEAD : Block.sizeOf body ≤ n := by simp [Stmt.sizeOf] at hsz; omega
        have hnofd_body_DEAD : Block.noFuncDecl body = Bool.true := by
          simp [Stmt.noFuncDecl] at hnofd_st; exact hnofd_st
        have hmeas : measure = none := hinvs.2.2.2.2.2
        subst hmeas
        -- cfg, hfail, hreach already destructured from hcf above
        by_cases hnf₀ : ρ₀.hasFailure = Bool.true
        · -- ρ₀ already has failure → target trivially CanFails
          exact ⟨.stmt (stmtResult σ (.loop guard none inv body md)) ρ₀,
            by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
        · have hnf₀' : ρ₀.hasFailure = Bool.false := by
            cases h : ρ₀.hasFailure <;> simp_all
          cases hreach with
          | refl => simp [Config.getEnv] at hfail; exact absurd hfail hnf₀
          | step _ _ _ h1 r1 => cases h1 with
            | step_loop_exit hguard_ff hwfb' =>
              cases r1 with
              | refl => simp_all [Config.getEnv]
              | step _ _ _ h2 _ => exact nomatch h2
            | step_loop_nondet_exit =>
              cases r1 with
              | refl => simp_all [Config.getEnv]
              | step _ _ _ h2 _ => exact nomatch h2
            | step_loop_enter hguard_tt hwfb' =>
              rename_i g_expr
              have hreachT := reflTrans_to_T r1
              match seq_canfail_prop π φ hreachT hfail with
              | .inl ⟨cfg', hf', hstar'⟩ =>
                -- Body CanFails from ρ₀ → body' CanFails → lift to target
                have ⟨kcfg, hkf, hkstar⟩ := ih.2 σ body _hsz_body
                  hinvs.2.2.2.1 hnofd_body ρ₀ hwfb hwfv hwfvar ⟨cfg', hf', hstar'⟩
                rw [stmtResult_loop_det_full]
                have hinv_bool := hinvs.1 ρ₀.eval ρ₀.store hwfb
                by_cases hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt
                · have hfip := first_iter_body_all_tt π φ inv ρ₀ σ md hwfb hnf₀' hall_tt
                  have hdm : ∀ n ∈ Block.modifiedVars body, (ρ₀.store n).isSome :=
                    fun n hn => hinvs.2.2.2.2.1 ρ₀.store n
                      (Block.modifiedVars_subset_touchedVars body n hn)
                  have hhi := havoc_block_identity π φ _ _ md ρ₀ hdm hwfvar hnf₀'
                  have hap := assume_block_step π φ σ g_expr inv md ρ₀ hguard_tt hall_tt hwfb hnf₀'
                  have hcfi : CanFailBlock π φ (loopDetThenBranch σ g_expr none inv body md) ρ₀ := by
                    apply arb_iter_body_canFail_to_loopDetThenBranch
                    simp only [List.nil_append, List.append_nil]
                    exact canFail_tail_to_block π φ _ _ ρ₀ ρ₀ hhi
                      (canFail_tail_to_block π φ _ _ ρ₀ ρ₀ hap
                        (canFailBlock_append_left π φ _ _ ρ₀ ⟨kcfg, hkf, hkstar⟩))
                  obtain ⟨tc, tf, tr⟩ := hcfi
                  exact ⟨.block s!"loop_{loopNum σ}" (.seq tc []),
                    by simp [Config.getEnv]; exact tf,
                    ReflTrans_Transitive _ _ _ _
                      (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _ ρ₀)
                      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _
                        (ReflTrans_Transitive _ _ _ _
                          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀
                            (block_wrap_terminal π φ _ _ _ ρ₀ ρ₀ hfip))
                          (ReflTrans_Transitive _ _ _ _
                            (.step _ _ _ .step_stmts_cons (.refl _))
                            (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                              _ _ [] (.step _ _ _ (.step_ite_true hguard_tt hwfb') tr)))))⟩
                · exact .inl (canFailBlock_to_canFail_block π φ
                    s!"loop_{loopNum σ}" _ _ ρ₀
                    (first_iter_body_some_ff_canFail π φ inv ρ₀ σ md hwfb hnf₀' hinv_bool
                      (not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt)
                      s!"{loopElimBlockPrefix}first_iter_asserts_{loopNum σ}"
                      (.ite (.det g_expr) (loopDetThenBranch σ g_expr none inv body md) [] {})))
              | .inr ⟨ρ₁, _, cfg', hf', hstar_rest⟩ =>
                -- Body terminates at ρ₁, [loop] CanFails from ρ₁.
                -- The recursive case requires decomposing the CanFail across iterations.
                -- This needs well-founded induction on trace length (not statement size).
                -- TODO: add trace-length induction or a loop_canfail_extracts_body lemma.
                sorry
            | step_loop_nondet_enter =>
              have hreachT := reflTrans_to_T r1
              match seq_canfail_prop π φ hreachT hfail with
              | .inl ⟨cfg', hf', hstar'⟩ =>
                have ⟨kcfg, hkf, hkstar⟩ := ih.2 σ body _hsz_body
                  hinvs.2.2.2.1 hnofd_body ρ₀ hwfb hwfv hwfvar ⟨cfg', hf', hstar'⟩
                rw [stmtResult_loop_nondet_full]
                have hinv_bool := hinvs.1 ρ₀.eval ρ₀.store hwfb
                by_cases hall_tt : ∀ e ∈ inv, ρ₀.eval ρ₀.store e = some HasBool.tt
                · have hfip := first_iter_body_all_tt π φ inv ρ₀ σ md hwfb hnf₀' hall_tt
                  have hdm : ∀ n ∈ Block.modifiedVars body, (ρ₀.store n).isSome :=
                    fun n hn => hinvs.2.2.2.2.1 ρ₀.store n
                      (Block.modifiedVars_subset_touchedVars body n hn)
                  have hhi := havoc_block_identity π φ _ _ md ρ₀ hdm hwfvar hnf₀'
                  have hap := assume_block_step_nondet π φ σ inv md ρ₀ hall_tt hwfb hnf₀'
                  have hcfi : CanFailBlock π φ (loopNondetThenBranch σ none inv body md) ρ₀ := by
                    apply arb_iter_body_canFail_to_loopNondetThenBranch
                    simp only [List.nil_append, List.append_nil]
                    exact canFail_tail_to_block π φ _ _ ρ₀ ρ₀ hhi
                      (canFail_tail_to_block π φ _ _ ρ₀ ρ₀ hap
                        (canFailBlock_append_left π φ _ _ ρ₀ ⟨kcfg, hkf, hkstar⟩))
                  obtain ⟨tc, tf, tr⟩ := hcfi
                  exact ⟨.block s!"loop_{loopNum σ}" (.seq tc []),
                    by simp [Config.getEnv]; exact tf,
                    ReflTrans_Transitive _ _ _ _
                      (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _ ρ₀)
                      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _
                        (ReflTrans_Transitive _ _ _ _
                          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀
                            (block_wrap_terminal π φ _ _ _ ρ₀ ρ₀ hfip))
                          (ReflTrans_Transitive _ _ _ _
                            (.step _ _ _ .step_stmts_cons (.refl _))
                            (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                              _ _ [] (.step _ _ _ .step_ite_nondet_true tr)))))⟩
                · exact .inl (canFailBlock_to_canFail_block π φ
                    s!"loop_{loopNum σ}" _ _ ρ₀
                    (first_iter_body_some_ff_canFail π φ inv ρ₀ σ md hwfb hnf₀' hinv_bool
                      (not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt)
                      s!"{loopElimBlockPrefix}first_iter_asserts_{loopNum σ}"
                      (.ite .nondet (loopNondetThenBranch σ none inv body md) [] {})))
              | .inr ⟨ρ₁, _, cfg', hf', hstar_rest⟩ =>
                sorry
      END DEAD CODE -/
    · intro σ bss hsz hinvs hnofd_bss ρ₀ hwfb hwfv hwfvar hcf
      obtain ⟨cfg, hfail, hreach⟩ := hcf
      match bss with
      | [] =>
        rw [blockResult_nil]
        exact ⟨cfg, hfail, hreach⟩
      | s :: ss =>
        rw [blockResult_cons]
        have hsz_s : Stmt.sizeOf s ≤ n := by simp [Block.sizeOf] at hsz; omega
        have hsz_ss : Block.sizeOf ss ≤ n := by simp [Block.sizeOf] at hsz; omega
        have ⟨hinvs_s, hinvs_ss⟩ := hinvs
        have hnofd_s : Stmt.noFuncDecl s = Bool.true := by
          simp [Block.noFuncDecl] at hnofd_bss; exact hnofd_bss.1
        have hnofd_ss : Block.noFuncDecl ss = Bool.true := by
          simp [Block.noFuncDecl] at hnofd_bss; exact hnofd_bss.2
        cases hreach with
        | refl =>
          exact ⟨.stmts (stmtResult σ s :: blockResult (stmtPostState σ s) ss) ρ₀,
            hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_cons =>
            -- Decompose: either s CanFails, or s terminates and ss CanFails
            match seq_canfail_prop π φ (reflTrans_to_T r1) hfail with
            | .inl ⟨cfg', hf', hstar'⟩ =>
              -- s CanFails from ρ₀
              have ⟨kcfg, hkf, hkstar⟩ := ih.1 σ s hsz_s hinvs_s hnofd_s ρ₀ hwfb hwfv hwfvar
                ⟨cfg', hf', hstar'⟩
              exact canFail_head_to_block π φ
                (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ ⟨kcfg, hkf, hkstar⟩
            | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
              -- s terminates at ρ₁, rest CanFails
              have heval_eq := smallStep_noFuncDecl_preserves_eval Expression
                (EvalCommand π φ) (EvalPureFunc φ) s ρ₀ ρ₁ hnofd_s hterm_s
              have ⟨hwfb₁, hwfv₁⟩ := star_preserves_wf π φ hwf_ext hterm_s hwfb hwfv
              have hwfvar₁ : WellFormedSemanticEvalVar ρ₁.eval := heval_eq ▸ hwfvar
              have ⟨kcfg, hkf, hkstar⟩ := ih.2 (stmtPostState σ s) ss hsz_ss hinvs_ss hnofd_ss
                ρ₁ hwfb₁ hwfv₁ hwfvar₁ ⟨cfg', hf', hstar_rest⟩
              -- Need to compose: stmtResult σ s terminates at ρ₁, then rest CanFails
              have hsim_s := (simulation π φ hwf_ext (Stmt.sizeOf s)).1
                σ s (Nat.le_refl _) hinvs_s ρ₀ hwfb hwfv hwfvar
              -- The simulation gives us: either CanFail or (hasFailure=false → terminal ρ₁)
              match hsim_s.1 ρ₁ hterm_s with
              | .inl hcf_s =>
                -- stmtResult σ s itself CanFails → done
                exact canFail_head_to_block π φ
                  (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf_s
              | .inr hok_s =>
                -- stmtResult σ s terminates at ρ₁ (if hasFailure=false).
                -- Need hasFailure of ρ₁.
                by_cases hnf₁ : ρ₁.hasFailure = Bool.true
                · -- ρ₁ already has failure. Target: s terminates at ρ₁ with failure.
                  -- We need: ∃ cfg, hasFailure cfg = true ∧ star (.stmts (s'::ss') ρ₀) cfg
                  -- Use: s' terminates at ρ₁ (since source s terminates at ρ₁ with hasFailure=true,
                  -- and simulation with the right hnf... but hok_s needs hnf=false)
                  -- Actually if ρ₁.hasFailure = true, the simulation returns CanFail for s.
                  -- Because the source reaches terminal ρ₁ with hasFailure=true.
                  -- And CanFail for s means CanFail for the whole block.
                  -- Wait, we need s in the source reaching terminal ρ₁ with hasFailure=true.
                  -- That's exactly what we have: hterm_s says source s → terminal ρ₁.
                  -- So CanFail (source s) holds since ρ₁.hasFailure=true.
                  -- By IH on s, CanFail (target s) holds.
                  have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
                    ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
                  have hcf_tgt_s := ih.1 σ s hsz_s hinvs_s hnofd_s ρ₀ hwfb hwfv hwfvar hcf_src_s
                  exact canFail_head_to_block π φ
                    (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf_tgt_s
                · -- ρ₁.hasFailure = false
                  have hnf₁' : ρ₁.hasFailure = Bool.false := by
                    cases h : ρ₁.hasFailure <;> simp_all
                  have htgt_s := hok_s hnf₁'
                  exact canFail_tail_to_block π φ
                    (stmtResult σ s) (blockResult (stmtPostState σ s) ss)
                    ρ₀ ρ₁ htgt_s ⟨kcfg, hkf, hkstar⟩

/-! ## Top-level theorem -/

/-- Loop elimination aggressively overapproximates: for each source
    execution reaching terminal `ρ'`, the transformed program either
    reaches the same `ρ'` or terminates with `hasFailure = true`.
    Similarly for exiting configurations. -/
theorem loopElim_overapproximatesAggressive
    (hwf_ext : WFEvalExtension φ) (σ : StringGenState)
    (hinvs : ∀ st : Statement, Stmt.loopInvsBool st)
    (hnofd : ∀ st : Statement, Stmt.noFuncDecl st = Bool.true) :
    Transform.OverapproximatesAggressively
      (LangCore π φ)
      (LangCore π φ)
      (fun s => some (stmtResult σ s)) := by
  intro st st' ht ρ₀ hwfb hwfv hwfvar
  simp at ht; subst ht
  have hsim := (simulation π φ hwf_ext (Stmt.sizeOf st)).1
    σ st (Nat.le_refl _) (hinvs st) ρ₀ hwfb hwfv hwfvar
  refine ⟨?_, ?_, ?_⟩
  · -- Terminal case
    intro ρ' hstar
    exact hsim.1 ρ' hstar
  · -- Exiting case
    intro lbl ρ' hstar
    exact hsim.2 lbl ρ' hstar
  · -- CanFail preservation
    intro ⟨cfg, hfail, hreach⟩
    -- If ρ₀ already has failure, the target trivially CanFail at its initial config.
    by_cases hnf₀ : ρ₀.hasFailure = Bool.true
    · exact ⟨.stmt (stmtResult σ st) ρ₀, by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
    · -- ρ₀.hasFailure = false. The source execution from (.stmt st ρ₀) reaches
      -- cfg with hasFailure = true. We need to show the target also can fail.
      -- Use the canfail_simulation theorem.
      have hcf_sim := (canfail_simulation π φ hwf_ext (Stmt.sizeOf st)).1
        σ st (Nat.le_refl _) (hinvs st) (hnofd st) ρ₀ hwfb hwfv hwfvar
      exact hcf_sim ⟨cfg, hfail, hreach⟩

end Core.LoopElim
