/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.GoalRewrite
import all Strata.DL.Imperative.BigStep.GoalRewrite

/-! # Rewriting goals under facts preserves failures: the proofs

A sound pass (`GoalRewrite.Sound`) keeps the runs and reaches of a list whose commands it
is sound on (`CmdsOk`) in both directions,
with corresponding events from the source to the rewrite (`Pass.run_fwd`, `Pass.run_bwd`,
`Pass.reach_fwd`, `Pass.reach_bwd`), so a failure of the source is a failure of the rewrite
of the same target (`Pass.fails_of_fails`), and conversely where the source's goals have
values (`Pass.fails_of_fails_out`). The proofs read the big-step semantics (`BRun`,
`BReach`) by recursion on the program.

Key theorems: `Pass.run_fwd`, `Pass.run_bwd`, `Pass.reach_fwd`, `Pass.reach_bwd`,
`Pass.fails_of_fails`, `Pass.fails_of_fails_out`, `Pass.stmts_noLoops`. -/

namespace Imperative
namespace BigStep
namespace GoalRewrite

public section

variable {P : PureExpr} {D : Type}

/-! ## Events -/

/-- Corresponding traces appended correspond. -/
private theorem rel₂_append {a a' b b' : List (Event P)} (ha : List.Rel₂ EvRel a a')
    (hb : List.Rel₂ EvRel b b') : List.Rel₂ EvRel (a ++ b) (a' ++ b') := by
  induction ha with
  | nil => exact hb
  | cons h _ ih => exact .cons h ih

/-- The traces of a list split as the list does. -/
private theorem rel₂_append_inv {a b : List (Event P)} {c' : List (Event P)}
    (h : List.Rel₂ EvRel (a ++ b) c') :
    ∃ a' b', c' = a' ++ b' ∧ List.Rel₂ EvRel a a' ∧ List.Rel₂ EvRel b b' := by
  induction a generalizing c' with
  | nil => exact ⟨[], c', rfl, .nil, h⟩
  | cons x a ih =>
    cases h with
    | cons hx hr =>
      obtain ⟨a', b', rfl, ha, hb⟩ := ih hr
      exact ⟨_ :: a', b', rfl, .cons hx ha, hb⟩

/-- The traces corresponding to an appended trace split as it does. -/
private theorem rel₂_append_inv' {a' b' : List (Event P)} {c : List (Event P)}
    (h : List.Rel₂ EvRel c (a' ++ b')) :
    ∃ a b, c = a ++ b ∧ List.Rel₂ EvRel a a' ∧ List.Rel₂ EvRel b b' := by
  induction a' generalizing c with
  | nil => exact ⟨[], c, rfl, .nil, h⟩
  | cons x a' ih =>
    cases h with
    | cons hx hr =>
      obtain ⟨a, b, rfl, ha, hb⟩ := ih hr
      exact ⟨_ :: a, b, rfl, .cons hx ha, hb⟩

mutual

/-- The rewrite of a list without loops has no loops. -/
theorem Pass.stmts_noLoops (π : Pass P D) : ∀ (ss : PStmts P) (d : D),
    Block.noLoops ss = true → Block.noLoops (π.stmts d ss).1 = true
  | [], _, _ => by simp [Pass.stmts, Block.noLoops, Block.allSubstmts]
  | s :: rest, d, h => by
    simp only [Block.noLoops, Block.allSubstmts, Bool.and_eq_true, Pass.stmts] at h ⊢
    exact ⟨π.stmt_noLoops s d h.1, π.stmts_noLoops rest _ h.2⟩

/-- The rewrite of a statement without loops has no loops. -/
private theorem Pass.stmt_noLoops (π : Pass P D) : ∀ (s : PStmt P) (d : D),
    Stmt.noLoops s = true → Stmt.noLoops (π.stmt d s).1 = true
  | .cmd (.cmd _), _, _ => by simp [Pass.stmt, Stmt.noLoops, Stmt.allSubstmts, Stmt.isNotLoop]
  | .cmd (.call ..), _, _ => by simp [Pass.stmt, Stmt.noLoops, Stmt.allSubstmts, Stmt.isNotLoop]
  | .block _ ss _, d, h => by
    simp only [Stmt.noLoops, Stmt.allSubstmts, Stmt.isNotLoop, Bool.true_and,
      Pass.stmt] at h ⊢
    exact π.stmts_noLoops ss d h
  | .ite _ ts es _, d, h => by
    simp only [Stmt.noLoops, Stmt.allSubstmts, Stmt.isNotLoop, Bool.true_and,
      Bool.and_eq_true, Pass.stmt] at h ⊢
    exact ⟨π.stmts_noLoops ts d h.1, π.stmts_noLoops es d h.2⟩
  | .loop .., _, h => by simp [Stmt.noLoops, Stmt.allSubstmts, Stmt.isNotLoop] at h
  | .exit .., _, _ => by simp [Pass.stmt, Stmt.noLoops, Stmt.allSubstmts, Stmt.isNotLoop]
  | .typeDecl .., _, _ => by simp [Pass.stmt, Stmt.noLoops, Stmt.allSubstmts, Stmt.isNotLoop]

end

variable [HasBool P] [HasFvar P]
omit [HasFvar P] in
/-- Corresponding traces have the same assumptions. -/
private theorem assumeOk_of_rel₂ {evs evs' : List (Event P)} (h : List.Rel₂ EvRel evs evs')
    (hA : AssumeOk evs) : AssumeOk evs' := by
  intro c hc
  induction h with
  | nil => simp at hc
  | @cons e e' es es' he _ ih =>
    rcases List.mem_cons.mp hc with hc | hc
    · subst hc
      cases e <;> simp only [EvRel] at he
      subst he
      exact hA _ (List.mem_cons_self ..)
    · exact ih (fun c h => hA c (List.mem_cons_of_mem _ h)) hc

omit [HasFvar P] in
/-- The traces corresponding to a trace have its assumptions. -/
private theorem assumeOk_of_rel₂_rev {evs evs' : List (Event P)}
    (h : List.Rel₂ EvRel evs evs') (hA : AssumeOk evs') : AssumeOk evs := by
  intro c hc
  induction h with
  | nil => simp at hc
  | @cons e e' es es' he _ ih =>
    rcases List.mem_cons.mp hc with hc | hc
    · subst hc
      cases e' <;> simp only [EvRel] at he
      subst he
      exact hA _ (List.mem_cons_self ..)
    · exact ih (fun c h => hA c (List.mem_cons_of_mem _ h)) hc

omit [HasFvar P] in
/-- The assumptions of an appended trace hold in each part. -/
private theorem assumeOk_append {a b : List (Event P)} (h : AssumeOk (a ++ b)) :
    AssumeOk a ∧ AssumeOk b :=
  ⟨fun c hc => h c (List.mem_append_left _ hc), fun c hc => h c (List.mem_append_right _ hc)⟩

/-! ## Commands -/

/-- A command run corresponds to a run of the command related to it, from the same
    store to the same store. -/
private theorem cmd_fwd {F : P.Factory} {R : P.Expr → P.Expr → Prop} {c c' : Cmd P}
    {σ σ' : SemanticStore P} {evs : List (Event P)} (hR : ∀ e e', R e e' →
      ∀ v, P.eval F σ e = some v → P.eval F σ e' = some v)
    (hc : CmdRel R c c') (h : EvalCmdE P F σ c σ' evs) :
    ∃ evs', EvalCmdE P F σ c' σ' evs' ∧ List.Rel₂ EvRel evs evs' := by
  cases hc with
  | same =>
    refine ⟨evs, h, ?_⟩
    clear hR
    cases h <;> repeat first | exact .nil | refine .cons ?_ .nil
    all_goals simp [EvRel, ArgRel]
  | assert he =>
    cases h
    exact ⟨_, .eval_assert, .cons ⟨rfl, rfl, rfl, rfl, hR _ _ he⟩ .nil⟩
  | cover he =>
    cases h
    exact ⟨_, .eval_cover, .cons ⟨rfl, rfl, rfl, rfl, hR _ _ he⟩ .nil⟩

/-- A run of the related command corresponds to a run of the command. -/
private theorem cmd_bwd {F : P.Factory} {R : P.Expr → P.Expr → Prop} {c c' : Cmd P}
    {σ σ' : SemanticStore P} {evs' : List (Event P)} (hR : ∀ e e', R e e' →
      ∀ v, P.eval F σ e = some v → P.eval F σ e' = some v)
    (hc : CmdRel R c c') (h : EvalCmdE P F σ c' σ' evs') :
    ∃ evs, EvalCmdE P F σ c σ' evs ∧ List.Rel₂ EvRel evs evs' := by
  cases hc with
  | same =>
    refine ⟨evs', h, ?_⟩
    clear hR
    cases h <;> repeat first | exact .nil | refine .cons ?_ .nil
    all_goals simp [EvRel, ArgRel]
  | assert he =>
    cases h
    exact ⟨_, .eval_assert, .cons ⟨rfl, rfl, rfl, rfl, hR _ _ he⟩ .nil⟩
  | cover he =>
    cases h
    exact ⟨_, .eval_cover, .cons ⟨rfl, rfl, rfl, rfl, hR _ _ he⟩ .nil⟩


/-! ## Runs and reaches -/

variable {F : P.Factory} {π : Pass P D} {γ : D → SemanticStore P → Prop}
  {ok : Cmd P → Prop}

mutual

/-- **A run of a list is a run of its rewrite**, with corresponding events and the same
    outcome; the facts after the list hold at its normal end. -/
theorem Pass.run_fwd (hS : Sound F π γ ok) : ∀ (ss : PStmts P) {d : D} {σ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P}, γ d σ → BRun F ss σ evs o → AssumeOk evs →
    CmdsOk ok ss →
    ∃ evs', BRun F (π.stmts d ss).1 σ evs' o ∧ List.Rel₂ EvRel evs evs' ∧
      ∀ σ1, o = .normal σ1 → γ (π.stmts d ss).2 σ1
  | [], _, _, _, _, hγ, h, _, hok => by
    cases h
    exact ⟨[], .nil, .nil, fun _ h => by cases h; exact hγ⟩
  | s :: rest, _, _, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmts]
    cases h with
    | cons_normal h1 h2 =>
      obtain ⟨hA1, hA2⟩ := assumeOk_append hA
      obtain ⟨e1, r1, m1, p1⟩ := Pass.runS_fwd hS s hγ h1 hA1 hok.1
      obtain ⟨e2, r2, m2, p2⟩ := Pass.run_fwd hS rest (p1 _ rfl) h2 hA2 hok.2
      exact ⟨e1 ++ e2, .cons_normal r1 r2, rel₂_append m1 m2, p2⟩
    | cons_exit h1 =>
      obtain ⟨e1, r1, m1, _⟩ := Pass.runS_fwd hS s hγ h1 hA hok.1
      exact ⟨e1, .cons_exit r1, m1, fun _ h => by cases h⟩

/-- **A run of a statement is a run of its rewrite**: `Pass.run_fwd` for one statement. -/
private theorem Pass.runS_fwd (hS : Sound F π γ ok) : ∀ (s : PStmt P) {d : D} {σ : SemanticStore P}
    {evs : List (Event P)} {o : Outcome P}, γ d σ → BRunS F s σ evs o → AssumeOk evs →
    StmtCmdsOk ok s →
    ∃ evs', BRunS F (π.stmt d s).1 σ evs' o ∧ List.Rel₂ EvRel evs evs' ∧
      ∀ σ1, o = .normal σ1 → γ (π.stmt d s).2 σ1
  | .cmd (.cmd c), d, σ, evs, _, hγ, h, hA, hok => by
    simp only [Pass.stmt]
    cases h with
    | cmd h =>
      obtain ⟨evs', h', hr⟩ := cmd_fwd (fun _ _ he => he σ hγ) (hS.cmd_rel d c hok) h
      exact ⟨evs', .cmd h', hr, fun _ he => by cases he; exact hS.cmd_post d c σ _ evs hok hγ h hA⟩
  | .cmd (.call ..), _, _, _, _, _, h, _, hok => by
    cases h with
    | cmd h => exact h.elim
  | .block l ss md, d, σ, evs, _, hγ, h, hA, hok => by
    have h0 := h
    simp only [Pass.stmt]
    cases h with
    | block h =>
      obtain ⟨e', r, m, _⟩ := Pass.run_fwd hS ss hγ h hA hok
      exact ⟨e', .block r, m, fun σ1 he => hS.forget_post d _ σ evs σ1 hγ (he ▸ h0)⟩
  | .ite c ts es md, d, σ, evs, _, hγ, h, hA, hok => by
    have h0 := h
    simp only [Pass.stmt]
    cases h with
    | ite_true hc h =>
      obtain ⟨e', r, m, _⟩ := Pass.run_fwd hS ts hγ h hA hok.1
      exact ⟨e', .ite_true hc r, m, fun σ1 he => hS.forget_post d _ σ evs σ1 hγ (he ▸ h0)⟩
    | ite_false hc h =>
      obtain ⟨e', r, m, _⟩ := Pass.run_fwd hS es hγ h hA hok.2
      exact ⟨e', .ite_false hc r, m, fun σ1 he => hS.forget_post d _ σ evs σ1 hγ (he ▸ h0)⟩
    | ite_nondet_true h =>
      obtain ⟨e', r, m, _⟩ := Pass.run_fwd hS ts hγ h hA hok.1
      exact ⟨e', .ite_nondet_true r, m, fun σ1 he => hS.forget_post d _ σ evs σ1 hγ (he ▸ h0)⟩
    | ite_nondet_false h =>
      obtain ⟨e', r, m, _⟩ := Pass.run_fwd hS es hγ h hA hok.2
      exact ⟨e', .ite_nondet_false r, m, fun σ1 he => hS.forget_post d _ σ evs σ1 hγ (he ▸ h0)⟩
  | .loop .., _, _, _, _, _, h, _, hok => by cases h
  | .exit .., _, _, _, _, _, h, _, hok => by
    cases h
    exact ⟨[], .exit, .nil, fun _ h => by cases h⟩
  | .typeDecl .., _, _, _, _, hγ, h, _, hok => by
    cases h
    exact ⟨[], .typeDecl, .nil, fun _ h => by cases h; exact hγ⟩

end

mutual

/-- **A run of the rewrite of a list is a run of the list**, with corresponding events and
    the same outcome; the facts after the list hold at its normal end. -/
theorem Pass.run_bwd (hS : Sound F π γ ok) : ∀ (ss : PStmts P) {d : D} {σ : SemanticStore P}
    {evs' : List (Event P)} {o : Outcome P}, γ d σ → BRun F (π.stmts d ss).1 σ evs' o →
    AssumeOk evs' →
    CmdsOk ok ss →
    ∃ evs, BRun F ss σ evs o ∧ List.Rel₂ EvRel evs evs' ∧
      ∀ σ1, o = .normal σ1 → γ (π.stmts d ss).2 σ1
  | [], _, _, _, _, hγ, h, _, hok => by
    simp only [Pass.stmts] at h ⊢
    cases h
    exact ⟨[], .nil, .nil, fun _ h => by cases h; exact hγ⟩
  | s :: rest, _, _, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmts] at h ⊢
    cases h with
    | cons_normal h1 h2 =>
      obtain ⟨hA1, hA2⟩ := assumeOk_append hA
      obtain ⟨e1, r1, m1, p1⟩ := Pass.runS_bwd hS s hγ h1 hA1 hok.1
      obtain ⟨e2, r2, m2, p2⟩ := Pass.run_bwd hS rest (p1 _ rfl) h2 hA2 hok.2
      exact ⟨e1 ++ e2, .cons_normal r1 r2, rel₂_append m1 m2, p2⟩
    | cons_exit h1 =>
      obtain ⟨e1, r1, m1, _⟩ := Pass.runS_bwd hS s hγ h1 hA hok.1
      exact ⟨e1, .cons_exit r1, m1, fun _ h => by cases h⟩

/-- **A run of the rewrite of a statement is a run of it**: `Pass.run_bwd` for one
    statement. -/
private theorem Pass.runS_bwd (hS : Sound F π γ ok) : ∀ (s : PStmt P) {d : D} {σ : SemanticStore P}
    {evs' : List (Event P)} {o : Outcome P}, γ d σ → BRunS F (π.stmt d s).1 σ evs' o →
    AssumeOk evs' →
    StmtCmdsOk ok s →
    ∃ evs, BRunS F s σ evs o ∧ List.Rel₂ EvRel evs evs' ∧
      ∀ σ1, o = .normal σ1 → γ (π.stmt d s).2 σ1
  | .cmd (.cmd c), d, σ, evs', _, hγ, h, hA, hok => by
    simp only [Pass.stmt] at h ⊢
    cases h with
    | cmd h =>
      obtain ⟨evs, h', hr⟩ := cmd_bwd (fun _ _ he => he σ hγ) (hS.cmd_rel d c hok) h
      exact ⟨evs, .cmd h', hr, fun _ he => by
        cases he; exact hS.cmd_post d c σ _ evs hok hγ h' (assumeOk_of_rel₂_rev hr hA)⟩
  | .cmd (.call ..), _, _, _, _, _, h, _, hok => by
    simp only [Pass.stmt] at h
    cases h with
    | cmd h => exact h.elim
  | .block l ss md, d, σ, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmt] at h ⊢
    cases h with
    | block h =>
      obtain ⟨e, r, m, _⟩ := Pass.run_bwd hS ss hγ h hA hok
      exact ⟨e, .block r, m, fun σ1 he => hS.forget_post d _ σ e σ1 hγ (he ▸ .block r)⟩
  | .ite c ts es md, d, σ, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmt] at h ⊢
    cases h with
    | ite_true hc h =>
      obtain ⟨e, r, m, _⟩ := Pass.run_bwd hS ts hγ h hA hok.1
      exact ⟨e, .ite_true hc r, m, fun σ1 he =>
        hS.forget_post d _ σ e σ1 hγ (he ▸ .ite_true hc r)⟩
    | ite_false hc h =>
      obtain ⟨e, r, m, _⟩ := Pass.run_bwd hS es hγ h hA hok.2
      exact ⟨e, .ite_false hc r, m, fun σ1 he =>
        hS.forget_post d _ σ e σ1 hγ (he ▸ .ite_false hc r)⟩
    | ite_nondet_true h =>
      obtain ⟨e, r, m, _⟩ := Pass.run_bwd hS ts hγ h hA hok.1
      exact ⟨e, .ite_nondet_true r, m, fun σ1 he =>
        hS.forget_post d _ σ e σ1 hγ (he ▸ .ite_nondet_true r)⟩
    | ite_nondet_false h =>
      obtain ⟨e, r, m, _⟩ := Pass.run_bwd hS es hγ h hA hok.2
      exact ⟨e, .ite_nondet_false r, m, fun σ1 he =>
        hS.forget_post d _ σ e σ1 hγ (he ▸ .ite_nondet_false r)⟩
  | .loop .., _, _, _, _, _, h, _, hok => by
    simp only [Pass.stmt] at h
    cases h
  | .exit .., _, _, _, _, _, h, _, hok => by
    simp only [Pass.stmt] at h ⊢
    cases h
    exact ⟨[], .exit, .nil, fun _ h => by cases h⟩
  | .typeDecl .., _, _, _, _, hγ, h, _, hok => by
    simp only [Pass.stmt] at h ⊢
    cases h
    exact ⟨[], .typeDecl, .nil, fun _ h => by cases h; exact hγ⟩

end


mutual

/-- **A reach of a list is a reach of its rewrite**, with corresponding events. -/
theorem Pass.reach_fwd (hS : Sound F π γ ok) : ∀ (ss : PStmts P) {d : D} {σ : SemanticStore P}
    {evs : List (Event P)}, γ d σ → BReach F ss σ evs → AssumeOk evs →
    CmdsOk ok ss →
    ∃ evs', BReach F (π.stmts d ss).1 σ evs' ∧ List.Rel₂ EvRel evs evs'
  | [], _, _, _, _, h, _, hok => by cases h
  | s :: rest, _, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmts]
    cases h with
    | here h =>
      obtain ⟨e, r, m⟩ := Pass.reachS_fwd hS s hγ h hA hok.1
      exact ⟨e, .here r, m⟩
    | later h1 h2 =>
      obtain ⟨hA1, hA2⟩ := assumeOk_append hA
      obtain ⟨e1, r1, m1, p1⟩ := Pass.runS_fwd hS s hγ h1 hA1 hok.1
      obtain ⟨e2, r2, m2⟩ := Pass.reach_fwd hS rest (p1 _ rfl) h2 hA2 hok.2
      exact ⟨e1 ++ e2, .later r1 r2, rel₂_append m1 m2⟩

/-- **A reach of a statement is a reach of its rewrite**: `Pass.reach_fwd` for one
    statement. -/
private theorem Pass.reachS_fwd (hS : Sound F π γ ok) : ∀ (s : PStmt P) {d : D} {σ : SemanticStore P}
    {evs : List (Event P)}, γ d σ → BReachS F s σ evs → AssumeOk evs →
    StmtCmdsOk ok s →
    ∃ evs', BReachS F (π.stmt d s).1 σ evs' ∧ List.Rel₂ EvRel evs evs'
  | .cmd (.cmd c), d, σ, _, hγ, h, _, hok => by
    simp only [Pass.stmt]
    cases h with
    | cmd h =>
      obtain ⟨evs', h', hr⟩ := cmd_fwd (fun _ _ he => he σ hγ) (hS.cmd_rel d c hok) h
      exact ⟨evs', .cmd h', hr⟩
  | .cmd (.call ..), _, _, _, _, h, _, hok => by
    cases h with
    | cmd h => exact h.elim
  | .block _ ss _, _, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmt]
    cases h with
    | block h =>
      obtain ⟨e, r, m⟩ := Pass.reach_fwd hS ss hγ h hA hok
      exact ⟨e, .block r, m⟩
  | .ite _ ts es _, _, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmt]
    cases h with
    | ite_true hc h =>
      obtain ⟨e, r, m⟩ := Pass.reach_fwd hS ts hγ h hA hok.1
      exact ⟨e, .ite_true hc r, m⟩
    | ite_false hc h =>
      obtain ⟨e, r, m⟩ := Pass.reach_fwd hS es hγ h hA hok.2
      exact ⟨e, .ite_false hc r, m⟩
    | ite_nondet_true h =>
      obtain ⟨e, r, m⟩ := Pass.reach_fwd hS ts hγ h hA hok.1
      exact ⟨e, .ite_nondet_true r, m⟩
    | ite_nondet_false h =>
      obtain ⟨e, r, m⟩ := Pass.reach_fwd hS es hγ h hA hok.2
      exact ⟨e, .ite_nondet_false r, m⟩
  | .loop .., _, _, _, _, h, _, hok => by cases h
  | .exit .., _, _, _, _, h, _, hok => by cases h
  | .typeDecl .., _, _, _, _, h, _, hok => by cases h

end

mutual

/-- **A reach of the rewrite of a list is a reach of the list**, with corresponding
    events. -/
theorem Pass.reach_bwd (hS : Sound F π γ ok) : ∀ (ss : PStmts P) {d : D} {σ : SemanticStore P}
    {evs' : List (Event P)}, γ d σ → BReach F (π.stmts d ss).1 σ evs' → AssumeOk evs' →
    CmdsOk ok ss →
    ∃ evs, BReach F ss σ evs ∧ List.Rel₂ EvRel evs evs'
  | [], _, _, _, _, h, _, hok => by
    simp only [Pass.stmts] at h
    cases h
  | s :: rest, _, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmts] at h
    cases h with
    | here h =>
      obtain ⟨e, r, m⟩ := Pass.reachS_bwd hS s hγ h hA hok.1
      exact ⟨e, .here r, m⟩
    | later h1 h2 =>
      obtain ⟨hA1, hA2⟩ := assumeOk_append hA
      obtain ⟨e1, r1, m1, p1⟩ := Pass.runS_bwd hS s hγ h1 hA1 hok.1
      obtain ⟨e2, r2, m2⟩ := Pass.reach_bwd hS rest (p1 _ rfl) h2 hA2 hok.2
      exact ⟨e1 ++ e2, .later r1 r2, rel₂_append m1 m2⟩

/-- **A reach of the rewrite of a statement is a reach of it**: `Pass.reach_bwd` for one
    statement. -/
private theorem Pass.reachS_bwd (hS : Sound F π γ ok) : ∀ (s : PStmt P) {d : D} {σ : SemanticStore P}
    {evs' : List (Event P)}, γ d σ → BReachS F (π.stmt d s).1 σ evs' → AssumeOk evs' →
    StmtCmdsOk ok s →
    ∃ evs, BReachS F s σ evs ∧ List.Rel₂ EvRel evs evs'
  | .cmd (.cmd c), d, σ, _, hγ, h, _, hok => by
    simp only [Pass.stmt] at h
    cases h with
    | cmd h =>
      obtain ⟨evs, h', hr⟩ := cmd_bwd (fun _ _ he => he σ hγ) (hS.cmd_rel d c hok) h
      exact ⟨evs, .cmd h', hr⟩
  | .cmd (.call ..), _, _, _, _, h, _, hok => by
    simp only [Pass.stmt] at h
    cases h with
    | cmd h => exact h.elim
  | .block _ ss _, _, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmt] at h
    cases h with
    | block h =>
      obtain ⟨e, r, m⟩ := Pass.reach_bwd hS ss hγ h hA hok
      exact ⟨e, .block r, m⟩
  | .ite _ ts es _, _, _, _, hγ, h, hA, hok => by
    simp only [Pass.stmt] at h
    cases h with
    | ite_true hc h =>
      obtain ⟨e, r, m⟩ := Pass.reach_bwd hS ts hγ h hA hok.1
      exact ⟨e, .ite_true hc r, m⟩
    | ite_false hc h =>
      obtain ⟨e, r, m⟩ := Pass.reach_bwd hS es hγ h hA hok.2
      exact ⟨e, .ite_false hc r, m⟩
    | ite_nondet_true h =>
      obtain ⟨e, r, m⟩ := Pass.reach_bwd hS ts hγ h hA hok.1
      exact ⟨e, .ite_nondet_true r, m⟩
    | ite_nondet_false h =>
      obtain ⟨e, r, m⟩ := Pass.reach_bwd hS es hγ h hA hok.2
      exact ⟨e, .ite_nondet_false r, m⟩
  | .loop .., _, _, _, _, h, _, hok => by
    simp only [Pass.stmt] at h
    cases h
  | .exit .., _, _, _, _, h, _, hok => by
    simp only [Pass.stmt] at h
    cases h
  | .typeDecl .., _, _, _, _, h, _, hok => by
    simp only [Pass.stmt] at h
    cases h

end

/-! ## Failures -/
omit [HasFvar P] in
/-- A failing event is no assumption, so it adds none to a trace. -/
private theorem assumeOk_snoc {evs : List (Event P)} {ev : Event P} {t : AssertId P}
    {e : P.Expr} (hA : AssumeOk evs) (he : FailsAt t e ev) : AssumeOk (evs ++ [ev]) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hA c hc
  · cases ev <;> simp_all [FailsAt]

omit [HasFvar P] in
/-- The event corresponding to a failing event fails the same target, with its own
    condition. -/
private theorem failsAt_rel {ev ev' : Event P} {t : AssertId P} {e : P.Expr}
    (he : FailsAt t e ev) (hr : EvRel ev ev') : FailsAt t ev'.condition.expr ev' := by
  cases ev <;> cases ev' <;> simp only [EvRel, ArgRel, FailsAt, Event.condition] at he hr ⊢
  all_goals first
    | exact he.elim
    | exact hr.elim
    | (obtain ⟨h1, h2, h3, h4, h5⟩ := hr
       obtain ⟨hl, hm, -, hv⟩ := he
       have hv' := h5 _ hv
       rw [h1, h2] at hv'
       exact ⟨h3 ▸ hl, h4 ▸ hm, trivial, hv'⟩)

omit [HasFvar P] in
/-- A trace that corresponds to a trace ending in a failure of `t` ends in a failure of
    `t`. -/
private theorem fails_rel {evs : List (Event P)} {ev : Event P} {t : AssertId P} {e : P.Expr}
    {c : List (Event P)} (hr : List.Rel₂ EvRel (evs ++ [ev]) c) (hA : AssumeOk evs)
    (he : FailsAt t e ev) :
    ∃ evs' ev', c = evs' ++ [ev'] ∧ AssumeOk evs' ∧ FailsAt t ev'.condition.expr ev' := by
  obtain ⟨evs', l, rfl, hr1, hr2⟩ := rel₂_append_inv hr
  cases hr2 with
  | cons he' hn =>
    cases hn
    exact ⟨evs', _, rfl, assumeOk_of_rel₂ hr1 hA, failsAt_rel he he'⟩

/-- **Rewriting keeps failures.** If the facts `d` hold at `σ`, every command of `ss`
    satisfies `ok`, and `ss` fails `t` from `σ`, its rewrite fails `t` from `σ`, with the
    rewritten condition. -/
theorem Pass.fails_of_fails (hS : Sound F π γ ok) {ss : PStmts P} {d : D} {σ : SemanticStore P}
    (hγ : γ d σ) (hok : CmdsOk ok ss) {t : AssertId P} {e : P.Expr} (h : Fails F ss σ t e) :
    ∃ e', Fails F (π.stmts d ss).1 σ t e' := by
  obtain ⟨evs, ev, hb, hA, he⟩ := h
  obtain ⟨c, hb', hr⟩ := Pass.reach_fwd hS ss hγ hb (assumeOk_snoc hA he) hok
  obtain ⟨evs', ev', rfl, hA', he'⟩ := fails_rel hr hA he
  exact ⟨_, evs', ev', hb', hA', he'⟩

omit [HasFvar P] in
/-- An event whose corresponding event fails `t` fails `t` too, with its own condition,
    when its condition has a value. -/
private theorem failsAt_rel_rev {ev ev' : Event P} {t : AssertId P} {e' : P.Expr}
    (he : FailsAt t e' ev') (hr : EvRel ev ev')
    (hdef : ∃ v, P.eval ev.condition.factory ev.condition.store ev.condition.expr = some v) :
    FailsAt t ev.condition.expr ev := by
  cases ev <;> cases ev' <;> simp only [EvRel, ArgRel, FailsAt, Event.condition] at he hr hdef ⊢
  all_goals first
    | exact he.elim
    | exact hr.elim
    | (obtain ⟨h1, h2, h3, h4, h5⟩ := hr
       obtain ⟨hl, hm, -, hv⟩ := he
       obtain ⟨w, hw⟩ := hdef
       have hw' := h5 w hw
       rw [← h1, ← h2] at hv
       rw [hv] at hw'
       cases hw'
       exact ⟨h3.symm ▸ hl, h4.symm ▸ hm, trivial, h1 ▸ hw⟩)

/-- **Rewriting adds no failures where the goals have values.** If the facts `d` hold at
    `σ`, every command of `ss` satisfies `ok`, the goals of `ss` have values
    (`GoalsDefined`), and the rewrite of `ss` fails `t`
    from `σ`, then `ss` fails `t` from `σ`, with the original condition. -/
theorem Pass.fails_of_fails_out (hS : Sound F π γ ok) {ss : PStmts P} {d : D}
    {σ : SemanticStore P} (hγ : γ d σ) (hok : CmdsOk ok ss) (hdef : GoalsDefined F ss σ)
    {t : AssertId P}
    {e' : P.Expr} (h : Fails F (π.stmts d ss).1 σ t e') : ∃ e, Fails F ss σ t e := by
  obtain ⟨evs', ev', hb, hA, he⟩ := h
  obtain ⟨c, hb', hr⟩ := Pass.reach_bwd hS ss hγ hb (assumeOk_snoc hA he) hok
  obtain ⟨evs, l, rfl, hr1, hr2⟩ := rel₂_append_inv' hr
  cases hr2 with
  | cons hev hn =>
    cases hn
    rename_i ev
    have hgoal : ∀ a, ev ≠ .assume a := by
      rintro a rfl
      cases ev' <;> simp only [EvRel, FailsAt] at hev he
    exact ⟨_, evs, ev, hb', assumeOk_of_rel₂_rev hr1 hA,
      failsAt_rel_rev he hev (hdef evs ev hb' hgoal)⟩

end -- public section

end GoalRewrite
end BigStep
end Imperative
