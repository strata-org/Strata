/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.Cmd
public import Strata.DL.Util.Relations

---------------------------------------------------------------------

namespace Imperative

public section

section

variable
  {CmdT : Type}
  (P : PureExpr)
  [HasBool P] [HasNot P]
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)

/-! ## Basic Properties and Theorems -/

/-- Empty statement list evaluation. -/
theorem evalStmtsSmallNil
    (ρ : Env P) :
    EvalStmtsSmall P EvalCmd extendEval ρ [] ρ := by
  unfold EvalStmtsSmall
  exact .step _ _ _ StepStmt.step_stmts_nil (.refl _)

/-- Terminal configurations are indeed terminal. -/
theorem terminalIsTerminal
    (ρ : Env P) :
    IsTerminal P EvalCmd extendEval (.terminal ρ) := by
  unfold IsTerminal
  intro c' h
  cases h

/-!
### Stepping through a statement list

When executing `.stmts (s :: ss) ρ`, the semantics first enters a
`.seq` context (via `step_stmts_cons`), executes `s` to terminal, then
resumes with `.stmts ss ρ'`.

The proof proceeds in two parts:
1. A helper lemma (`seq_inner_star`) showing that multi-step execution of
   the inner config lifts to multi-step execution of the enclosing `.seq`.
2. The main theorem (`stmts_cons_step`) composing the pieces.
-/

/-- Helper: if the inner config of a `.seq` takes multiple steps, the
    enclosing `.seq` takes the same number of steps.
    Proved by induction on the multi-step derivation. -/
theorem seq_inner_star
    (inner inner' : Config P CmdT)
    (ss : List (Stmt P CmdT))
    (h : StepStmtStar P EvalCmd extendEval inner inner') :
    StepStmtStar P EvalCmd extendEval
      (.seq inner ss)
      (.seq inner' ss) := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih =>
    exact .step _ _ _ (.step_seq_inner hstep) ih

/-- Helper: if the inner config of a `.block` takes multiple steps, the
    enclosing `.block` takes the same number of steps. -/
theorem block_inner_star
    (inner inner' : Config P CmdT)
    (label : Option String)
    (σ_parent : SemanticStore P)
    (h : StepStmtStar P EvalCmd extendEval inner inner') :
    StepStmtStar P EvalCmd extendEval (.block label σ_parent inner) (.block label σ_parent inner') := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih => exact .step _ _ _ (.step_block_body hstep) ih

/-- When executing `.stmts (s :: ss) ρ`, if the head statement `s`
    multi-steps to `.terminal ρ'`, then the whole list multi-steps to
    `.stmts ss ρ'`.

    This captures the fundamental sequencing behaviour of statement lists
    in the small-step semantics. -/
theorem stmts_cons_step
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT))
    (ρ ρ' : Env P)
    (hstmt : StepStmtStar P EvalCmd extendEval
      (.stmt s ρ) (.terminal ρ')) :
    StepStmtStar P EvalCmd extendEval
      (.stmts (s :: ss) ρ)
      (.stmts ss ρ') := by
  -- Step 1: .stmts (s :: ss) ρ  →  .seq (.stmt s ρ) ss
  --         via step_stmts_cons
  apply ReflTrans.step _ (.seq (.stmt s ρ) ss)
  · exact .step_stmts_cons
  -- Step 2: .seq (.stmt s ρ) ss  →*  .seq (.terminal ρ') ss
  --         by lifting hstmt through the seq context
  have h2 := seq_inner_star P EvalCmd extendEval _ _ ss hstmt
  -- Step 3: .seq (.terminal ρ') ss  →  .stmts ss ρ'
  --         via step_seq_done, then chain with h2 by induction
  suffices h3 : StepStmtStar P EvalCmd extendEval
      (.seq (.terminal ρ') ss) (.stmts ss ρ') from
    ReflTrans_Transitive _ _ _ _ h2 h3
  exact .step _ _ _ .step_seq_done (.refl _)

/-! ## Inversion lemmas for seq and block execution -/

/-- Invert a seq execution reaching terminal: the inner terminates,
    then the tail stmts run to terminal. -/
theorem seq_reaches_terminal
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.seq inner ss) (.terminal ρ')) :
    ∃ ρ₁, StepStmtStar P EvalCmd extendEval inner (.terminal ρ₁) ∧
      StepStmtStar P EvalCmd extendEval (.stmts ss ρ₁) (.terminal ρ') := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner ss ρ', src = .seq inner ss → tgt = .terminal ρ' →
      ∃ ρ₁, StepStmtStar P EvalCmd extendEval inner (.terminal ρ₁) ∧
        StepStmtStar P EvalCmd extendEval (.stmts ss ρ₁) (.terminal ρ') from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ss ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_seq_inner h =>
      have ⟨ρ₁, hterm, htail⟩ := ih _ _ _ rfl htgt
      exact ⟨ρ₁, .step _ _ _ h hterm, htail⟩
    | step_seq_done => subst htgt; exact ⟨_, .refl _, hrest⟩
    | step_seq_exit => subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- Invert a seq execution reaching exiting: either the inner exited
    (propagated), or the inner terminated and the tail exited. -/
theorem seq_reaches_exiting
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {lbl : String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.seq inner ss) (.exiting lbl ρ')) :
    (StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ')) ∨
    (∃ ρ₁, StepStmtStar P EvalCmd extendEval inner (.terminal ρ₁) ∧
      StepStmtStar P EvalCmd extendEval (.stmts ss ρ₁) (.exiting lbl ρ')) := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner ss lbl ρ', src = .seq inner ss → tgt = .exiting lbl ρ' →
      (StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ')) ∨
      (∃ ρ₁, StepStmtStar P EvalCmd extendEval inner (.terminal ρ₁) ∧
        StepStmtStar P EvalCmd extendEval (.stmts ss ρ₁) (.exiting lbl ρ')) from
    this _ _ hstar _ _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ss lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_seq_inner h =>
      match ih _ _ _ _ rfl htgt with
      | .inl hexit => exact .inl (.step _ _ _ h hexit)
      | .inr ⟨ρ₁, hterm, htail⟩ => exact .inr ⟨ρ₁, .step _ _ _ h hterm, htail⟩
    | step_seq_done => subst htgt; exact .inr ⟨_, .refl _, hrest⟩
    | step_seq_exit => exact .inl (htgt ▸ hrest)

/-- Invert a block execution reaching terminal: the inner either
    terminated or exited (caught by the block).  In both cases the inner
    reaches a config whose env projects to `ρ'` via the parent store. -/
theorem block_reaches_terminal
    {inner : Config P CmdT} {l : Option String} {σ_parent : SemanticStore P} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.block l σ_parent inner) (.terminal ρ')) :
    (∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.terminal ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store }) ∨
    (∃ lbl ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store }) := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner ρ', src = .block l σ_parent inner → tgt = .terminal ρ' →
      (∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.terminal ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store }) ∨
      (∃ lbl ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store }) from
    this _ _ hstar _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      match ih _ _ rfl htgt with
      | .inl ⟨ρ_inner, hterm, heq⟩ => exact .inl ⟨ρ_inner, .step _ _ _ h hterm, heq⟩
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ => exact .inr ⟨lbl, ρ_inner, .step _ _ _ h hexit, heq⟩
    | step_block_done =>
      subst htgt; cases hrest with
      | refl => exact .inl ⟨_, .refl _, rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_match =>
      subst htgt; cases hrest with
      | refl => exact .inr ⟨_, _, .refl _, rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- Stronger inversion of `.block (.some label) σ_parent inner → .terminal`:
    when the block has an explicit label, the second disjunct (exit-match)
    constrains the inner exit-label to equal the block's label.  This is
    needed for downstream simulation lemmas that look up the exit's
    continuation in `exitConts` keyed by the matching label. -/
theorem block_some_reaches_terminal
    {inner : Config P CmdT} {label : String} {σ_parent : SemanticStore P} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval
      (.block (.some label) σ_parent inner) (.terminal ρ')) :
    (∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.terminal ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store }) ∨
    (∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting label ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store }) := by
  -- Same structure as block_reaches_terminal, but specialized to .some label.
  -- At step_block_exit_match, the rule's `l` is unified with `label` (because
  -- the rule premise `.some label = .some l` forces this).
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner ρ', src = .block (.some label) σ_parent inner → tgt = .terminal ρ' →
      (∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.terminal ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store }) ∨
      (∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting label ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store }) from
    this _ _ hstar _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      match ih _ _ rfl htgt with
      | .inl ⟨ρ_inner, hterm, heq⟩ => exact .inl ⟨ρ_inner, .step _ _ _ h hterm, heq⟩
      | .inr ⟨ρ_inner, hexit, heq⟩ => exact .inr ⟨ρ_inner, .step _ _ _ h hexit, heq⟩
    | step_block_done =>
      subst htgt; cases hrest with
      | refl => exact .inl ⟨_, .refl _, rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_match heq =>
      -- heq : .some label = .some l (where l is implicit and must equal label)
      -- The constructor's premise unifies l with label via injection on heq.
      -- After unification, the inner config is .exiting label _.
      injection heq with h_eq
      subst h_eq
      subst htgt; cases hrest with
      | refl => exact .inr ⟨_, .refl _, rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- Invert a block execution reaching exiting: the inner must have
    exited with a label that didn't match the block.  The env is projected. -/
theorem block_reaches_exiting
    {inner : Config P CmdT} {l : Option String} {σ_parent : SemanticStore P} {lbl : String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.block l σ_parent inner) (.exiting lbl ρ')) :
    ∃ lbl_inner ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl_inner ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner lbl ρ', src = .block l σ_parent inner → tgt = .exiting lbl ρ' →
      ∃ lbl_inner ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl_inner ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      have ⟨lbl_inner, ρ_inner, hexit, heq⟩ := ih _ _ _ rfl htgt
      exact ⟨lbl_inner, ρ_inner, .step _ _ _ h hexit, heq⟩
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with
      | refl => exact ⟨_, _, .refl _, rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_done | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- Strengthened block-exit inversion: a `.block l σ_parent inner` reaching
`.exiting lbl ρ'` must have had its inner body exit with the *same* label `lbl`
(the mismatch rule propagates the label unchanged), and that label does *not*
match the block's own label `l` (otherwise it would have been caught,
terminating the block).  The env is projected through the parent store. -/
theorem block_reaches_exiting_strong
    {inner : Config P CmdT} {l : Option String} {σ_parent : SemanticStore P} {lbl : String} {ρ' : Env P}
    (hstar : StepStmtStar P EvalCmd extendEval (.block l σ_parent inner) (.exiting lbl ρ')) :
    ∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_inner) ∧
      l ≠ .some lbl ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ inner lbl ρ', src = .block l σ_parent inner → tgt = .exiting lbl ρ' →
      ∃ ρ_inner, StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_inner) ∧
        l ≠ .some lbl ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      obtain ⟨ρ_inner, hexit, hne, heq⟩ := ih _ _ _ rfl htgt
      exact ⟨ρ_inner, .step _ _ _ h hexit, hne, heq⟩
    | step_block_exit_mismatch hne =>
      subst htgt; cases hrest with
      | refl => exact ⟨_, .refl _, hne, rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_done | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-! ## Trace construction helpers -/

/-- Entering a block: a single step from `.stmt (.block l body md) ρ`
    to `.block (.some l) (.stmts body ρ)`. -/
theorem step_block_enter (l : String) (body : List (Stmt P CmdT))
    (md : MetaData P) (ρ : Env P) :
    StepStmtStar P EvalCmd extendEval
      (.stmt (.block l body md) ρ) (.block (.some l) ρ.store (.stmts body ρ)) :=
  .step _ _ _ .step_block (.refl _)

/-- If a prefix of a statement list terminates, the full list steps
    to the suffix starting from the terminal environment. -/
theorem stmts_prefix_terminal_append
    (pfx sfx : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmd extendEval (.stmts pfx ρ) (.terminal ρ')) :
    StepStmtStar P EvalCmd extendEval (.stmts (pfx ++ sfx) ρ) (.stmts sfx ρ') := by
  induction pfx generalizing ρ with
  | nil =>
    cases h with
    | step _ _ _ h_step h_rest => cases h_step with
      | step_stmts_nil => cases h_rest with
        | refl => exact .refl _
        | step _ _ _ h _ => exact nomatch h
  | cons s rest ih =>
    cases h with
    | step _ _ _ h_step h_rest => cases h_step with
      | step_stmts_cons =>
        have ⟨ρ₁, h_s, h_r⟩ := seq_reaches_terminal P EvalCmd extendEval h_rest
        exact ReflTrans_Transitive _ _ _ _
          (stmts_cons_step P EvalCmd extendEval s (rest ++ sfx) ρ ρ₁ h_s) (ih ρ₁ h_r)

/-- If a prefix of a statement list exits, the full list exits at the
    same label/env (the suffix is never reached). -/
theorem stmts_prefix_exiting_append
    (pfx sfx : List (Stmt P CmdT)) (ρ ρ' : Env P) (lbl : String)
    (h : StepStmtStar P EvalCmd extendEval (.stmts pfx ρ) (.exiting lbl ρ')) :
    StepStmtStar P EvalCmd extendEval (.stmts (pfx ++ sfx) ρ) (.exiting lbl ρ') := by
  induction pfx generalizing ρ with
  | nil =>
    -- `.stmts [] ρ` can only step to `.terminal ρ`, never to `.exiting`.
    exfalso
    cases h with
    | step _ _ _ h_step h_rest => cases h_step with
      | step_stmts_nil => cases h_rest with
        | step _ _ _ h_bad _ => cases h_bad
  | cons s rest ih =>
    cases h with
    | step _ _ _ h_step h_rest => cases h_step with
      | step_stmts_cons =>
        match seq_reaches_exiting P EvalCmd extendEval h_rest with
        | .inl h_inner_exit =>
          -- Head `.stmt s ρ ⟶* .exiting lbl ρ'`; lift to `.stmts (s :: (rest ++ sfx)) ρ`.
          refine ReflTrans.step _ _ _ StepStmt.step_stmts_cons ?_
          have h_seq := seq_inner_star (P := P) EvalCmd extendEval _ _
                          (rest ++ sfx) h_inner_exit
          exact ReflTrans_Transitive _ _ _ _ h_seq
            (.step _ _ _ StepStmt.step_seq_exit (.refl _))
        | .inr ⟨ρ_mid, h_s_term, h_rest_exit⟩ =>
          -- Head terminates; recurse on rest.
          refine ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P EvalCmd extendEval s (rest ++ sfx) ρ ρ_mid h_s_term)
            ?_
          exact ih ρ_mid h_rest_exit

/-- Decompose a terminating execution of `ss₁ ++ ss₂` into a terminating
    execution of `ss₁` followed by a terminating execution of `ss₂`. -/
theorem stmts_append_terminates
    (ss₁ ss₂ : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmd extendEval (.stmts (ss₁ ++ ss₂) ρ) (.terminal ρ')) :
    ∃ ρ₁, StepStmtStar P EvalCmd extendEval (.stmts ss₁ ρ) (.terminal ρ₁) ∧
           StepStmtStar P EvalCmd extendEval (.stmts ss₂ ρ₁) (.terminal ρ') := by
  induction ss₁ generalizing ρ with
  | nil =>
    exact ⟨ρ, .step _ _ _ .step_stmts_nil (.refl _), h⟩
  | cons s rest ih =>
    cases h with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ_mid, h_s, h_rest_ss₂⟩ :=
          seq_reaches_terminal P EvalCmd extendEval hrest
        have ⟨ρ₁, h_rest, h_ss₂⟩ := ih ρ_mid h_rest_ss₂
        exact ⟨ρ₁, ReflTrans_Transitive _ _ _ _
          (stmts_cons_step P EvalCmd extendEval
            s rest ρ ρ_mid h_s) h_rest, h_ss₂⟩

/-- Try every non-recursive `StepStmt` constructor, using `‹_›` (term-level
    assumption) to fill arguments so that no hypothesis names are needed. -/
local macro "apply_step" : tactic => `(tactic| first
  | exact .step_cmd ‹_›        | exact .step_ite_true ‹_› ‹_›
  | exact .step_ite_false ‹_› ‹_›
  | exact .step_loop_enter ‹_› ‹_› ‹_› ‹_›
  | exact .step_loop_exit ‹_› ‹_› ‹_› ‹_›
  | exact .step_block
  | exact .step_exit            | exact .step_funcDecl
  | exact .step_typeDecl        | exact .step_stmts_nil
  | exact .step_stmts_cons)

/-! ## Store/eval simulation and hasFailure irrelevance -/

/-- Two configs agree on store/eval (may differ on hasFailure). -/
private def ConfigSE : Config P CmdT → Config P CmdT → Prop
  | .stmt s₁ ρ₁, .stmt s₂ ρ₂ => s₁ = s₂ ∧ ρ₁.store = ρ₂.store ∧ ρ₁.eval = ρ₂.eval
  | .stmts ss₁ ρ₁, .stmts ss₂ ρ₂ => ss₁ = ss₂ ∧ ρ₁.store = ρ₂.store ∧ ρ₁.eval = ρ₂.eval
  | .terminal ρ₁, .terminal ρ₂ => ρ₁.store = ρ₂.store ∧ ρ₁.eval = ρ₂.eval
  | .exiting l₁ ρ₁, .exiting l₂ ρ₂ => l₁ = l₂ ∧ ρ₁.store = ρ₂.store ∧ ρ₁.eval = ρ₂.eval
  | .block l₁ σ₁ i₁, .block l₂ σ₂ i₂ => l₁ = l₂ ∧ σ₁ = σ₂ ∧ ConfigSE i₁ i₂
  | .seq i₁ ss₁, .seq i₂ ss₂ => ss₁ = ss₂ ∧ ConfigSE i₁ i₂
  | _, _ => False

/-- Single-step simulation: if two configs agree on store/eval and one steps,
    the other can take the same step with store/eval preserved. -/
private def step_simulation
    (c₁ c₁' c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₁')
    (heq : ConfigSE P c₁ c₂) :
    ∃ c₂', StepStmt P EvalCmd extendEval c₂ c₂' ∧ ConfigSE P c₁' c₂' := by
  cases hstep with
  -- Non-recursive cases where c₁ is `.stmt` or `.stmts`: exactly one c₂
  -- constructor is valid, and the output ConfigSE follows by `simp_all`.
  | step_cmd _ | step_block | step_ite_true _ _ | step_ite_false _ _
  | step_loop_enter _ _ _ _ | step_loop_exit _ _ _ _
  | step_exit | step_funcDecl | step_typeDecl | step_stmts_nil | step_stmts_cons =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; subst hs; subst he
    exact ⟨_, by apply_step, by simp_all [ConfigSE]⟩
  | step_ite_nondet_true =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; simp at hs he; subst hs; subst he
    exact ⟨_, .step_ite_nondet_true, by simp [ConfigSE]⟩
  | step_ite_nondet_false =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; simp at hs he; subst hs; subst he
    exact ⟨_, .step_ite_nondet_false, by simp [ConfigSE]⟩
  | step_loop_nondet_enter _ _ =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; simp at hs he; subst hs; subst he
    exact ⟨_, .step_loop_nondet_enter ‹_› ‹_›, by simp_all [ConfigSE]⟩
  | step_loop_nondet_exit _ _ =>
    cases c₂ <;> try contradiction
    obtain ⟨rfl, hs, he⟩ := heq; rename_i ρ₂; cases ρ₂; simp at hs he; subst hs; subst he
    exact ⟨_, .step_loop_nondet_exit ‹_› ‹_›, by simp_all [ConfigSE]⟩
  | step_seq_inner h =>
    cases c₂ with
    | seq i₂ _ =>
      have hrs := heq.1; subst hrs
      have ⟨c₂', h₂, heq₂⟩ := step_simulation _ _ _ h heq.2
      exact ⟨_, .step_seq_inner h₂, ⟨rfl, heq₂⟩⟩
    | _ => exact nomatch heq
  | step_seq_done =>
    cases c₂ with
    | seq i₂ _ =>
      have hrs := heq.1; subst hrs
      cases i₂ with
      | terminal ρ₂ => exact ⟨_, .step_seq_done, ⟨rfl, heq.2.1, heq.2.2⟩⟩
      | _ => exact nomatch heq.2
    | _ => exact nomatch heq
  | step_seq_exit =>
    cases c₂ with
    | seq i₂ _ =>
      cases i₂ with
      | exiting _ _ => exact ⟨_, .step_seq_exit, ⟨heq.2.1, heq.2.2.1, heq.2.2.2⟩⟩
      | _ => exact nomatch heq.2
    | _ => exact nomatch heq
  | step_block_body h =>
    cases c₂ with
    | block _ _ i₂ =>
      have hrs := heq.1; subst hrs
      have hσ := heq.2.1; subst hσ
      have ⟨c₂', h₂, heq₂⟩ := step_simulation _ _ _ h heq.2.2
      exact ⟨_, .step_block_body h₂, ⟨rfl, rfl, heq₂⟩⟩
    | _ => exact nomatch heq
  | step_block_done =>
    cases c₂ with
    | block _ _ i₂ =>
      have hrs := heq.1; subst hrs
      have hσ := heq.2.1; subst hσ
      cases i₂ with
      | terminal ρ₂ =>
        have hse := heq.2.2
        exact ⟨_, .step_block_done, ⟨congrArg (projectStore _) hse.1, hse.2⟩⟩
      | _ => exact nomatch heq.2.2
    | _ => exact nomatch heq
  | step_block_exit_match hl =>
    cases c₂ with
    | block _ _ i₂ =>
      have hlb := heq.1; subst hlb
      have hσ := heq.2.1; subst hσ
      cases i₂ with
      | exiting l₂ ρ₂ =>
        have hl₂ := heq.2.2.1; subst hl₂
        have hse := heq.2.2.2
        exact ⟨_, .step_block_exit_match hl, ⟨congrArg (projectStore _) hse.1, hse.2⟩⟩
      | _ => exact nomatch heq.2.2
    | _ => exact nomatch heq
  | step_block_exit_mismatch hl =>
    cases c₂ with
    | block _ _ i₂ =>
      have hlb := heq.1; subst hlb
      have hσ := heq.2.1; subst hσ
      cases i₂ with
      | exiting l₂ ρ₂ =>
        have hl₂ := heq.2.2.1; subst hl₂
        have hse := heq.2.2.2
        exact ⟨_, .step_block_exit_mismatch hl, ⟨rfl, congrArg (projectStore _) hse.1, hse.2⟩⟩
      | _ => exact nomatch heq.2.2
    | _ => exact nomatch heq

/-- The terminal state's store and eval are independent of the starting
    `hasFailure` flag.  Proved by simulation: each step preserves
    store/eval equivalence, so the terminal states agree. -/
theorem smallStep_hasFailure_irrel
    (s : Stmt P CmdT) (ρ ρ' : Env P)
    (h : StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.terminal ρ')) :
    ∀ (ρ₂ : Env P), ρ₂.store = ρ.store → ρ₂.eval = ρ.eval →
    ∃ ρ₂', StepStmtStar P EvalCmd extendEval (.stmt s ρ₂) (.terminal ρ₂') ∧
      ρ₂'.store = ρ'.store ∧ ρ₂'.eval = ρ'.eval := by
  intro ρ₂ hs he
  suffices ∀ (c₁ c₂ : Config P CmdT),
      ConfigSE P c₁ c₂ →
      ∀ c₁', StepStmtStar P EvalCmd extendEval c₁ c₁' →
      ∃ c₂', StepStmtStar P EvalCmd extendEval c₂ c₂' ∧ ConfigSE P c₁' c₂' by
    have heq_init : ConfigSE P (.stmt s ρ) (.stmt s ρ₂) := ⟨rfl, hs.symm, he.symm⟩
    have ⟨c₂', hstar₂, heq₂⟩ := this _ _ heq_init _ h
    match c₂', heq₂ with
    | .terminal ρ₂', heq_t => exact ⟨ρ₂', hstar₂, heq_t.1.symm, heq_t.2.symm⟩
  intro c₁ c₂ heq c₁' hstar
  induction hstar generalizing c₂ with
  | refl => exact ⟨c₂, .refl _, heq⟩
  | step _ mid _ hstep _ ih =>
    have ⟨mid₂, hstep₂, heq_mid⟩ := step_simulation P EvalCmd extendEval _ _ _ hstep heq
    have ⟨c₂', hstar₂, heq_final⟩ := ih _ heq_mid
    exact ⟨c₂', .step _ _ _ hstep₂ hstar₂, heq_final⟩

/-! ## Well-paired exits: preservation and no-escape -/

omit [HasBool P] [HasNot P] in
/-- Helper: when the inner of a block reaches `.exiting l` and the
    block's label (if some) doesn't match `l`, then `l` must be in the outer
    labels list.  The conclusion is `l ∈ labels`, which is exactly the
    `Config.exitsCoveredByBlocks` of `.exiting l ρ''` for any ρ''. -/
private theorem block_exit_mismatch_unfold {labels : List String}
    {label : Option String} {σ_parent : SemanticStore P} {l : String} {ρ' ρ'' : Env P}
    (h : Config.exitsCoveredByBlocks labels
          (.block label σ_parent (.exiting l ρ' : Config P CmdT)))
    (hne : label ≠ .some l) :
    Config.exitsCoveredByBlocks labels (.exiting l ρ'' : Config P CmdT) := by
  show l ∈ labels
  cases label with
  | none => exact h
  | some lb =>
    have h' : l ∈ lb :: labels := h
    rw [List.mem_cons] at h'
    rcases h' with hh | hh
    · exact absurd (by rw [hh]) hne
    · exact hh

/-- A single step preserves `Config.exitsCoveredByBlocks`. -/
private theorem step_preserves_exitsCoveredByBlocks
    (labels : List String)
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂)
    (hwp : c₁.exitsCoveredByBlocks labels) :
    c₂.exitsCoveredByBlocks labels := by
  -- Prove a generalized version where labels is universally quantified,
  -- so the IH works at any nesting depth (needed for step_block_body).
  suffices ∀ c₁ c₂, StepStmt P EvalCmd extendEval c₁ c₂ →
      ∀ labels, c₁.exitsCoveredByBlocks labels → c₂.exitsCoveredByBlocks labels by
    exact this c₁ c₂ hstep labels hwp
  intro c₁ c₂ hstep
  induction hstep with
  | step_cmd => intro _ _; trivial
  | step_block => intro _ hwp; exact hwp
  | step_ite_true => intro _ hwp; exact hwp.1
  | step_ite_false => intro _ hwp; exact hwp.2
  | step_ite_nondet_true => intro _ hwp; exact hwp.1
  | step_ite_nondet_false => intro _ hwp; exact hwp.2
  | step_loop_enter _ _ =>
    intro labels hwp
    -- Goal: .seq (.block .none ρ.store (.stmts body ρ')) [.loop ...] covers labels.
    -- The .block .none label doesn't extend the labels list (Config.exitsCoveredByBlocks's
    -- .block none case just descends).
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    exact ⟨hwp, hwp, True.intro⟩
  | step_loop_exit => intro _ _; trivial
  | step_loop_nondet_enter =>
    intro labels hwp
    simp only [Config.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks] at hwp ⊢
    exact ⟨hwp, hwp, True.intro⟩
  | step_loop_nondet_exit => intro _ _; trivial
  | step_exit =>
    intro labels hwp
    -- hwp : l ∈ labels (from .stmt (.exit l)), goal: .exiting (.some l) covers labels = l ∈ labels
    exact hwp
  | step_funcDecl => intro _ _; trivial
  | step_typeDecl => intro _ _; trivial
  | step_stmts_nil => intro _ _; trivial
  | step_stmts_cons => intro _ hwp; exact ⟨hwp.1, hwp.2⟩
  | step_seq_inner _ ih => intro labels hwp; exact ⟨ih labels hwp.1, hwp.2⟩
  | step_seq_done => intro _ hwp; exact hwp.2
  | step_seq_exit => intro _ hwp; exact hwp.1
  | step_block_body _ ih =>
    intro labels hwp
    rename_i inner inner' label σ_parent _
    cases label with
    | none => exact ih labels hwp
    | some l => exact ih (l :: labels) hwp
  | step_block_done => intro _ _; trivial
  | step_block_exit_match => intro _ _; trivial
  | step_block_exit_mismatch hne =>
    intro labels hwp
    exact block_exit_mismatch_unfold (P := P) (CmdT := CmdT) hwp hne

/-- Well-paired statements cannot escape via `.exiting`:
    if all exits in `s` are caught by enclosing blocks
    (`s.exitsCoveredByBlocks []`), then `s` never reaches `.exiting`. -/
theorem exitsCoveredByBlocks_noEscape
    (s : Stmt P CmdT)
    (hwp : s.exitsCoveredByBlocks []) :
    ∀ (ρ : Env P) (lbl : String) (ρ' : Env P),
      ¬ StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.exiting lbl ρ') := by
  intro ρ lbl ρ' hstar
  -- Prove Config.exitsCoveredByBlocks [] is preserved, then show .exiting contradicts it.
  suffices ∀ c₁ c₂,
      c₁.exitsCoveredByBlocks ([] : List String) →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.exitsCoveredByBlocks ([] : List String) by
    have hwp' := this _ _ (show Config.exitsCoveredByBlocks [] (.stmt s ρ) from hwp) hstar
    -- Config.exitsCoveredByBlocks [] (.exiting lbl ρ') requires lbl ∈ [] (False).
    exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
  intro c₁ c₂ hwp_c hstar_c
  induction hstar_c with
  | refl => exact hwp_c
  | step _ _ _ hstep _ ih =>
    exact ih (step_preserves_exitsCoveredByBlocks P EvalCmd extendEval [] _ _ hstep hwp_c)

/-- Well-paired statement lists cannot escape via `.exiting`:
    if all exits in `bss` are caught by enclosing blocks
    (`Block.exitsCoveredByBlocks [] bss`), then `.stmts bss ρ` never reaches `.exiting`. -/
theorem block_exitsCoveredByBlocks_noEscape
    (bss : List (Stmt P CmdT))
    (hwp : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks [] bss) :
    ∀ (ρ : Env P) (lbl : String) (ρ' : Env P),
      ¬ StepStmtStar P EvalCmd extendEval (.stmts bss ρ) (.exiting lbl ρ') := by
  intro ρ lbl ρ' hstar
  suffices ∀ c₁ c₂,
      c₁.exitsCoveredByBlocks ([] : List String) →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.exitsCoveredByBlocks ([] : List String) by
    have hwp' := this _ _ (show Config.exitsCoveredByBlocks [] (.stmts bss ρ) from hwp) hstar
    exact absurd hwp' (by simp [Config.exitsCoveredByBlocks])
  intro c₁ c₂ hwp_c hstar_c
  induction hstar_c with
  | refl => exact hwp_c
  | step _ _ _ hstep _ ih =>
    exact ih (step_preserves_exitsCoveredByBlocks P EvalCmd extendEval [] _ _ hstep hwp_c)

/-- If `.block l inner →* cfg`, the inner config never reaches `.exiting`,
    and `cfg` is neither terminal nor exiting, then `cfg = .block l inner'`
    for some `inner'` with `inner →* inner'`. -/
theorem block_star_extract_inner
    {l : Option String} {σ_parent : SemanticStore P} {inner cfg : Config P CmdT}
    (h_star : StepStmtStar P EvalCmd extendEval (.block l σ_parent inner) cfg)
    (h_no_exit : ∀ lbl ρ', ¬ StepStmtStar P EvalCmd extendEval
        inner (.exiting lbl ρ'))
    (h_not_terminal : ∀ ρ', cfg ≠ .terminal ρ')
    (h_not_exiting : ∀ lbl ρ', cfg ≠ .exiting lbl ρ') :
    ∃ inner', cfg = .block l σ_parent inner' ∧
      StepStmtStar P EvalCmd extendEval inner inner' := by
  suffices ∀ c₁ c₂,
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      ∀ inner₀, c₁ = .block l σ_parent inner₀ →
      (∀ lbl ρ', ¬ StepStmtStar P EvalCmd extendEval inner₀ (.exiting lbl ρ')) →
      (∀ ρ', c₂ ≠ .terminal ρ') → (∀ lbl ρ', c₂ ≠ .exiting lbl ρ') →
      ∃ inner', c₂ = .block l σ_parent inner' ∧
        StepStmtStar P EvalCmd extendEval inner₀ inner' from
    this _ _ h_star _ rfl h_no_exit h_not_terminal h_not_exiting
  intro c₁ c₂ h_star
  induction h_star with
  | refl => intro inner₀ heq _ _ _; subst heq; exact ⟨inner₀, rfl, .refl _⟩
  | step _ mid _ hstep hrest ih =>
    intro inner₀ heq h_ne h_nt h_nx; subst heq
    cases hstep with
    | step_block_body h_inner_step =>
      have h_ne' : ∀ lbl ρ', ¬ StepStmtStar P EvalCmd extendEval _ (.exiting lbl ρ') :=
        fun lbl ρ' h => h_ne lbl ρ' (.step _ _ _ h_inner_step h)
      obtain ⟨inner', rfl, h_inner_star⟩ := ih _ rfl h_ne' h_nt h_nx
      exact ⟨inner', rfl, .step _ _ _ h_inner_step h_inner_star⟩
    | step_block_done =>
      cases hrest with
      | refl => exact absurd rfl (h_nt _)
      | step _ _ _ h _ => exact nomatch h
    | step_block_exit_match => exact absurd (.refl _) (h_ne _ _)
    | step_block_exit_mismatch => exact absurd (.refl _) (h_ne _ _)

/-! ## noFuncDecl preserves eval (small-step) -/

/-- A single step preserves eval when noFuncDecl holds.
    The only step that changes eval is step_funcDecl, which is excluded. -/
private theorem step_preserves_eval_noFuncDecl
    (c₁ c₂ : Config P CmdT)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂)
    (hnofd : Config.noFuncDecl c₁) :
    c₂.getEnv.eval = c₁.getEnv.eval ∧ Config.noFuncDecl c₂ := by
  suffices ∀ c₁ c₂, StepStmt P EvalCmd extendEval c₁ c₂ →
      ∀ (_ : Config.noFuncDecl c₁),
      c₂.getEnv.eval = c₁.getEnv.eval ∧ Config.noFuncDecl c₂ by
    exact this c₁ c₂ hstep hnofd
  intro c₁ c₂ hstep
  induction hstep with
  | step_cmd => intro _; exact ⟨rfl, trivial⟩
  | step_block =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd ⊢
    exact ⟨rfl, hnofd⟩
  | step_ite_true =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.1⟩
  | step_ite_false =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.2⟩
  | step_ite_nondet_true =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.1⟩
  | step_ite_nondet_false =>
    intro hnofd
    simp only [Config.noFuncDecl, Stmt.noFuncDecl, Bool.and_eq_true] at hnofd
    exact ⟨rfl, hnofd.2⟩
  | step_loop_enter =>
    intro hnofd
    refine ⟨rfl, ?_, ?_⟩
    · -- Goal: inner Config has noFuncDecl
      simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd ⊢
      exact hnofd
    · -- Goal: rest = [loop ...] has Block.noFuncDecl
      simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd ⊢
      simp [Block.noFuncDecl, Stmt.noFuncDecl, hnofd]
  | step_loop_exit => intro _; exact ⟨rfl, trivial⟩
  | step_loop_nondet_enter =>
    intro hnofd
    refine ⟨rfl, ?_, ?_⟩
    · simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd ⊢; exact hnofd
    · simp only [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd ⊢
      simp [Block.noFuncDecl, Stmt.noFuncDecl, hnofd]
  | step_loop_nondet_exit => intro _; exact ⟨rfl, trivial⟩
  | step_exit => intro _; exact ⟨rfl, trivial⟩
  | step_funcDecl =>
    intro hnofd; simp [Config.noFuncDecl, Stmt.noFuncDecl] at hnofd
  | step_typeDecl => intro _; exact ⟨rfl, trivial⟩
  | step_stmts_nil => intro _; exact ⟨rfl, trivial⟩
  | step_stmts_cons =>
    intro hnofd
    refine ⟨rfl, ?_⟩
    simp only [Config.noFuncDecl, Block.noFuncDecl, Bool.and_eq_true] at hnofd ⊢
    exact hnofd
  | step_seq_inner _ ih =>
    intro hnofd
    have ⟨heq, hnofd'⟩ := ih hnofd.1
    exact ⟨heq, hnofd', hnofd.2⟩
  | step_seq_done => intro hnofd; exact ⟨rfl, hnofd.2⟩
  | step_seq_exit => intro _; exact ⟨rfl, trivial⟩
  | step_block_body _ ih => intro hnofd; exact ih hnofd
  | step_block_done => intro _; exact ⟨rfl, trivial⟩
  | step_block_exit_match => intro _; exact ⟨rfl, trivial⟩
  | step_block_exit_mismatch => intro _; exact ⟨rfl, trivial⟩

/-- When a statement has no function declarations, small-step execution
    preserves the evaluator. -/
theorem smallStep_noFuncDecl_preserves_eval
    (s : Stmt P CmdT) (ρ ρ' : Env P)
    (hnofd : Stmt.noFuncDecl s = true)
    (hstar : StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.terminal ρ')) :
    ρ'.eval = ρ.eval := by
  suffices ∀ c₁ c₂,
      Config.noFuncDecl c₁ →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.getEnv.eval = c₁.getEnv.eval by
    exact this _ _ (show Config.noFuncDecl (.stmt s ρ) from hnofd) hstar
  intro c₁ c₂ hnofd_c hstar_c
  induction hstar_c with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have ⟨heq, hnofd_mid⟩ := step_preserves_eval_noFuncDecl P EvalCmd extendEval _ _ hstep hnofd_c
    rw [ih hnofd_mid, heq]

/-- When a block has no function declarations, small-step execution
    preserves the evaluator. -/
theorem smallStep_noFuncDecl_preserves_eval_block
    (bss : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (hnofd : Block.noFuncDecl bss = true)
    (hstar : StepStmtStar P EvalCmd extendEval (.stmts bss ρ) (.terminal ρ')) :
    ρ'.eval = ρ.eval := by
  suffices ∀ c₁ c₂,
      Config.noFuncDecl c₁ →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.getEnv.eval = c₁.getEnv.eval by
    exact this _ _ (show Config.noFuncDecl (.stmts bss ρ) from hnofd) hstar
  intro c₁ c₂ hnofd_c hstar_c
  induction hstar_c with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have ⟨heq, hnofd_mid⟩ := step_preserves_eval_noFuncDecl P EvalCmd extendEval _ _ hstep hnofd_c
    rw [ih hnofd_mid, heq]

/-- Alias for `smallStep_noFuncDecl_preserves_eval_block`, matching the
    `Block.noFuncDecl` naming convention. -/
theorem block_noFuncDecl_preserves_eval
    (ss : List (Stmt P CmdT)) (ρ ρ' : Env P)
    (hnofd : Block.noFuncDecl ss = true)
    (hterm : StepStmtStar P EvalCmd extendEval (.stmts ss ρ) (.terminal ρ')) :
    ρ'.eval = ρ.eval :=
  smallStep_noFuncDecl_preserves_eval_block P EvalCmd extendEval ss ρ ρ' hnofd hterm

/-- When a block has no function declarations, small-step execution
    preserves the evaluator (variant for `.exiting` target). -/
theorem smallStep_noFuncDecl_preserves_eval_block_exiting
    (bss : List (Stmt P CmdT)) (ρ ρ' : Env P) (lbl : String)
    (hnofd : Block.noFuncDecl bss = true)
    (hstar : StepStmtStar P EvalCmd extendEval (.stmts bss ρ) (.exiting lbl ρ')) :
    ρ'.eval = ρ.eval := by
  suffices ∀ c₁ c₂,
      Config.noFuncDecl c₁ →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.getEnv.eval = c₁.getEnv.eval by
    exact this _ _ (show Config.noFuncDecl (.stmts bss ρ) from hnofd) hstar
  intro c₁ c₂ hnofd_c hstar_c
  induction hstar_c with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have ⟨heq, hnofd_mid⟩ := step_preserves_eval_noFuncDecl P EvalCmd extendEval _ _ hstep hnofd_c
    rw [ih hnofd_mid, heq]

/-- When a statement has no function declarations, small-step execution
    preserves the evaluator (variant for `.exiting` target). -/
theorem smallStep_noFuncDecl_preserves_eval_exiting
    (s : Stmt P CmdT) (ρ ρ' : Env P) (lbl : String)
    (hnofd : Stmt.noFuncDecl s = true)
    (hstar : StepStmtStar P EvalCmd extendEval (.stmt s ρ) (.exiting lbl ρ')) :
    ρ'.eval = ρ.eval := by
  suffices ∀ c₁ c₂,
      Config.noFuncDecl c₁ →
      StepStmtStar P EvalCmd extendEval c₁ c₂ →
      c₂.getEnv.eval = c₁.getEnv.eval by
    exact this _ _ (show Config.noFuncDecl (.stmt s ρ) from hnofd) hstar
  intro c₁ c₂ hnofd_c hstar_c
  induction hstar_c with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have ⟨heq, hnofd_mid⟩ := step_preserves_eval_noFuncDecl P EvalCmd extendEval _ _ hstep hnofd_c
    rw [ih hnofd_mid, heq]

/-! ### hasFailure monotonicity and irrelevance

`hasFailure` is never consulted by any `StepStmt` premise,
so it is both *monotone* (once `true`, stays `true`) and *irrelevant*
(changing only `hasFailure` in the input env yields an execution with the
same `store` and `eval` in the output).
-/

private theorem step_hasFailure_monotone
  {c c' : Config P CmdT}
  (hstep : StepStmt P EvalCmd extendEval c c')
  (hf : c.getEnv.hasFailure = true) :
  c'.getEnv.hasFailure = true := by
  induction hstep with
  | step_cmd _ => simp [Config.getEnv]; left; exact hf
  | step_block => simp [Config.getEnv]; exact hf
  | step_ite_true _ _ => exact hf
  | step_ite_false _ _ => exact hf
  | step_ite_nondet_true => exact hf
  | step_ite_nondet_false => exact hf
  | step_loop_enter _ _ _ _ =>
    simp [Config.getEnv]; left; exact hf
  | step_loop_exit _ _ _ _ =>
    simp [Config.getEnv]; left; exact hf
  | step_loop_nondet_enter _ _ =>
    simp [Config.getEnv]; left; exact hf
  | step_loop_nondet_exit _ _ =>
    simp [Config.getEnv]; left; exact hf
  | step_exit => exact hf
  | step_funcDecl => simp [Config.getEnv]; exact hf
  | step_typeDecl => exact hf
  | step_stmts_nil => exact hf
  | step_stmts_cons => exact hf
  | step_seq_inner _ ih => exact ih hf
  | step_seq_done => exact hf
  | step_seq_exit => exact hf
  | step_block_body _ ih => exact ih hf
  | step_block_done => exact hf
  | step_block_exit_match _ => exact hf
  | step_block_exit_mismatch _ => exact hf

theorem EvalStmtSmall_hasFailure_monotone
  {ρ ρ' : Env P} {s : Stmt P CmdT} :
  EvalStmtSmall P EvalCmd extendEval ρ s ρ' →
  ρ.hasFailure = true → ρ'.hasFailure = true := by
  intro Heval Hf
  suffices ∀ c c', StepStmtStar P EvalCmd extendEval c c' →
      c.getEnv.hasFailure = true → c'.getEnv.hasFailure = true by
    exact this _ _ Heval Hf
  intro c c' hstar hf
  induction hstar with
  | refl => exact hf
  | step _ _ _ hstep _ ih => exact ih (step_hasFailure_monotone P EvalCmd extendEval hstep hf)

theorem EvalStmtsSmall_hasFailure_monotone
  {ρ ρ' : Env P} {ss : List (Stmt P CmdT)} :
  EvalStmtsSmall P EvalCmd extendEval ρ ss ρ' →
  ρ.hasFailure = true → ρ'.hasFailure = true := by
  intro Heval Hf
  suffices ∀ c c', StepStmtStar P EvalCmd extendEval c c' →
      c.getEnv.hasFailure = true → c'.getEnv.hasFailure = true by
    exact this _ _ Heval Hf
  intro c c' hstar hf
  induction hstar with
  | refl => exact hf
  | step _ _ _ hstep _ ih => exact ih (step_hasFailure_monotone P EvalCmd extendEval hstep hf)

theorem StepStmtStar_hasFailure_monotone
  {c c' : Config P CmdT}
  (hstar : StepStmtStar P EvalCmd extendEval c c')
  (hf : c.getEnv.hasFailure = true) :
  c'.getEnv.hasFailure = true := by
  induction hstar with
  | refl => exact hf
  | step _ _ _ hstep _ ih => exact ih (step_hasFailure_monotone P EvalCmd extendEval hstep hf)

theorem EvalStmtSmall_hasFailure_irrel
  {ρ ρ' : Env P} {s : Stmt P CmdT} :
  EvalStmtSmall P EvalCmd extendEval ρ s ρ' →
  ∀ (ρ₂ : Env P), ρ₂.store = ρ.store → ρ₂.eval = ρ.eval →
  ∃ ρ₂', EvalStmtSmall P EvalCmd extendEval ρ₂ s ρ₂' ∧
    ρ₂'.store = ρ'.store ∧ ρ₂'.eval = ρ'.eval :=
  smallStep_hasFailure_irrel P EvalCmd extendEval s ρ ρ'

theorem EvalStmtsSmall_hasFailure_irrel
  {ρ ρ' : Env P} {ss : List (Stmt P CmdT)} :
  EvalStmtsSmall P EvalCmd extendEval ρ ss ρ' →
  ∀ (ρ₂ : Env P), ρ₂.store = ρ.store → ρ₂.eval = ρ.eval →
  ∃ ρ₂', EvalStmtsSmall P EvalCmd extendEval ρ₂ ss ρ₂' ∧
    ρ₂'.store = ρ'.store ∧ ρ₂'.eval = ρ'.eval := by
  intro Heval ρ₂ Hstore Heval_eq
  suffices ∀ (c₁ c₂ : Config P CmdT),
      ConfigSE P c₁ c₂ →
      ∀ c₁', StepStmtStar P EvalCmd extendEval c₁ c₁' →
      ∃ c₂', StepStmtStar P EvalCmd extendEval c₂ c₂' ∧ ConfigSE P c₁' c₂' by
    have heq_init : ConfigSE P (.stmts ss ρ) (.stmts ss ρ₂) := ⟨rfl, Hstore.symm, Heval_eq.symm⟩
    have ⟨c₂', hstar₂, heq₂⟩ := this _ _ heq_init _ Heval
    match c₂', heq₂ with
    | .terminal ρ₂', heq_t => exact ⟨ρ₂', hstar₂, heq_t.1.symm, heq_t.2.symm⟩
  intro c₁ c₂ heq c₁' hstar
  induction hstar generalizing c₂ with
  | refl => exact ⟨c₂, .refl _, heq⟩
  | step _ mid _ hstep _ ih =>
    have ⟨mid₂, hstep₂, heq_mid⟩ := step_simulation P EvalCmd extendEval _ _ _ hstep heq
    have ⟨c₂', hstar₂, heq_final⟩ := ih _ heq_mid
    exact ⟨c₂', .step _ _ _ hstep₂ hstar₂, heq_final⟩

end -- section

section

variable (P : PureExpr) [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
variable (extendEval : ExtendEval P)

omit [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr] in
/-- If a config has no matching assert, then `isAtAssert` doesn't match. -/
private theorem noMatchingAssert_not_isAtAssert
    (cfg : Config P (Cmd P)) (label : String) (expr : P.Expr)
    (hno : cfg.noMatchingAssert label) :
    ¬ isAtAssert P cfg ⟨label, expr⟩ := by
  match cfg with
  | .stmt (.cmd (.assert l _ _)) _ =>
    simp [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno
    simp [isAtAssert]; exact fun h _ => hno (h ▸ rfl)
  | .stmt (.cmd (.init ..)) _ | .stmt (.cmd (.set ..)) _
  | .stmt (.cmd (.assume ..)) _
  | .stmt (.cmd (.cover ..)) _
  | .stmt (.block ..) _ | .stmt (.ite ..) _
  | .stmt (.exit ..) _ | .stmt (.funcDecl ..) _ | .stmt (.typeDecl ..) _ =>
    simp [isAtAssert]
  | .stmt (.loop _ _ inv _ _) _ =>
    simp [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno
    intro hat
    exact hno.1 label expr hat rfl
  | .stmts [] _ => simp [isAtAssert]
  | .stmts ((.cmd (.assert l _ _)) :: _) _ =>
    simp [Config.noMatchingAssert, Stmt.noMatchingAssert.Stmts.noMatchingAssert, Stmt.noMatchingAssert] at hno
    simp [isAtAssert]; exact fun h _ => hno.1 (h ▸ rfl)
  | .stmts ((.cmd (.init ..)) :: _) _ | .stmts ((.cmd (.set ..)) :: _) _
  | .stmts ((.cmd (.assume ..)) :: _) _
  | .stmts ((.cmd (.cover ..)) :: _) _
  | .stmts ((.block ..) :: _) _ | .stmts ((.ite ..) :: _) _
  | .stmts ((.exit ..) :: _) _
  | .stmts ((.funcDecl ..) :: _) _ | .stmts ((.typeDecl ..) :: _) _ =>
    simp [isAtAssert]
  | .stmts ((.loop _ _ inv _ _) :: _) _ =>
    simp [Config.noMatchingAssert, Stmt.noMatchingAssert.Stmts.noMatchingAssert,
      Stmt.noMatchingAssert] at hno
    intro hat
    exact hno.1.1 label expr hat rfl
  | .terminal _ | .exiting _ _ => simp [isAtAssert]
  | .block _ _ inner => exact noMatchingAssert_not_isAtAssert inner label expr hno
  | .seq inner _ => exact noMatchingAssert_not_isAtAssert inner label expr hno.1

omit [HasFvar P] [HasBool P] [HasNot P] in
/-- Helper: `Stmts.noMatchingAssert` for concatenation. -/
private theorem stmts_noMatchingAssert_append
    (ss₁ ss₂ : List (Stmt P (Cmd P))) (label : String)
    (h₁ : Stmt.noMatchingAssert.Stmts.noMatchingAssert ss₁ label)
    (h₂ : Stmt.noMatchingAssert.Stmts.noMatchingAssert ss₂ label) :
    Stmt.noMatchingAssert.Stmts.noMatchingAssert (ss₁ ++ ss₂) label := by
  induction ss₁ with
  | nil => exact h₂
  | cons s ss ih =>
    exact ⟨h₁.1, ih h₁.2⟩

/-- A single step preserves `Config.noMatchingAssert`. -/
private def step_preserves_noMatchingAssert
    (c₁ c₂ : Config P (Cmd P)) (label : String)
    (hstep : StepStmt P (EvalCmd P) extendEval c₁ c₂)
    (hno : c₁.noMatchingAssert label) :
    c₂.noMatchingAssert label := by
  cases hstep with
  | step_cmd => trivial
  | step_block => exact hno
  | step_ite_true => exact hno.1
  | step_ite_false => exact hno.2
  | step_ite_nondet_true => exact hno.1
  | step_ite_nondet_false => exact hno.2
  | step_loop_enter =>
    -- New shape: .seq (.block .none ρ.store (.stmts body ρ')) [loop]
    -- noMatchingAssert: inner covers, AND [loop] covers.
    simp only [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno ⊢
    exact ⟨hno.2, hno, True.intro⟩
  | step_loop_exit => trivial
  | step_loop_nondet_enter =>
    simp only [Config.noMatchingAssert, Stmt.noMatchingAssert] at hno ⊢
    exact ⟨hno.2, hno, True.intro⟩
  | step_loop_nondet_exit => trivial
  | step_exit => trivial
  | step_funcDecl => trivial
  | step_typeDecl => trivial
  | step_stmts_nil => trivial
  | step_stmts_cons => exact ⟨hno.1, hno.2⟩
  | step_seq_inner h =>
    constructor
    · apply step_preserves_noMatchingAssert; exact h; exact hno.1
    · exact hno.2
  | step_seq_done => exact hno.2
  | step_seq_exit => trivial
  | step_block_body h =>
    have := step_preserves_noMatchingAssert (c₁ := _) (c₂ := _) (label := _) h hno
    exact this
  | step_block_done => trivial
  | step_block_exit_match => trivial
  | step_block_exit_mismatch => trivial

/-- The syntactic check implies that no reachable config from `st`
    satisfies `isAtAssert` for the given label and expression. -/
theorem noMatchingAssert_implies_no_reachable_assert
    (st : Stmt P (Cmd P)) (label : String) (expr : P.Expr)
    (hno : st.noMatchingAssert label) :
    ∀ (ρ : Env P) (cfg : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ) cfg →
      ¬ isAtAssert P cfg ⟨label, expr⟩ := by
  intro ρ cfg hstar
  suffices ∀ (c₁ c₂ : Config P (Cmd P)),
      c₁.noMatchingAssert label →
      StepStmtStar P (EvalCmd P) extendEval c₁ c₂ →
      c₂.noMatchingAssert label from
    noMatchingAssert_not_isAtAssert P cfg label expr
      (this (.stmt st ρ) cfg (show Config.noMatchingAssert (.stmt st ρ) label from hno) hstar)
  intro c₁ c₂ hno_c hstar_c
  induction hstar_c with
  | refl => exact hno_c
  | step _ _ _ hstep _ ih =>
    exact ih (@step_preserves_noMatchingAssert P _ _ _ _ extendEval _ _ _ hstep hno_c)

/-! ## isAtAssert inversion lemmas -/

/-- If execution inside a block reaches a config where isAtAssert holds,
    then the config must be `.block label inner` where `inner` is reachable
    from the block's body and satisfies `isAtAssert`. -/
theorem block_isAtAssert_inner
    (label : String) (σ_parent : SemanticStore P) (inner₀ cfg : Config P (Cmd P)) (a : AssertId P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.block label σ_parent inner₀) cfg)
    (hat : isAtAssert P cfg a) :
    ∃ inner, cfg = .block label σ_parent inner ∧
      StepStmtStar P (EvalCmd P) extendEval inner₀ inner ∧
      isAtAssert P inner a := by
  generalize hsrc : Config.block label σ_parent inner₀ = src at hstar
  induction hstar generalizing inner₀ with
  | refl => subst hsrc; exact ⟨inner₀, rfl, .refl _, hat⟩
  | step _ mid _ hstep hrest ih =>
    subst hsrc; cases hstep with
    | step_block_body hinner =>
      have ⟨inner, heq, hreach, hat'⟩ := ih _ hat rfl
      exact ⟨inner, heq, .step _ _ _ hinner hreach, hat'⟩
    | step_block_done => cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ h _ => exact absurd h (by intro h; cases h)
    | step_block_exit_match => cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ h _ => exact absurd h (by intro h; cases h)
    | step_block_exit_mismatch => cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ h _ => exact absurd h (by intro h; cases h)

/-- If execution inside a seq reaches a config where isAtAssert holds,
    then either the inner config matches (first disjunct), or the inner
    completed and we're in the tail (second disjunct). -/
theorem seq_isAtAssert_cases
    (inner₀ cfg : Config P (Cmd P)) (ss : List (Stmt P (Cmd P))) (a : AssertId P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.seq inner₀ ss) cfg)
    (hat : isAtAssert P cfg a) :
    (∃ inner, cfg = .seq inner ss ∧
      StepStmtStar P (EvalCmd P) extendEval inner₀ inner ∧
      isAtAssert P inner a) ∨
    (∃ ρ', StepStmtStar P (EvalCmd P) extendEval inner₀ (.terminal ρ') ∧
      StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ') cfg ∧
      isAtAssert P cfg a) := by
  generalize hsrc : Config.seq inner₀ ss = src at hstar
  induction hstar generalizing inner₀ ss with
  | refl => subst hsrc; exact .inl ⟨inner₀, rfl, .refl _, hat⟩
  | step _ mid _ hstep hrest ih =>
    subst hsrc; cases hstep with
    | step_seq_inner hinner =>
      match ih _ _ hat rfl with
      | .inl ⟨inner, heq, hreach, hat'⟩ =>
        exact .inl ⟨inner, heq, .step _ _ _ hinner hreach, hat'⟩
      | .inr ⟨ρ', hterm, hstmts, hat'⟩ =>
        exact .inr ⟨ρ', .step _ _ _ hinner hterm, hstmts, hat'⟩
    | step_seq_done =>
      exact .inr ⟨_, .refl _, hrest, hat⟩
    | step_seq_exit => cases hrest with
      | refl => exact absurd hat (by simp [isAtAssert])
      | step _ _ _ h _ => exact absurd h (by intro h; cases h)

/-- For a single assert command, any config reachable from `.stmts [assert] ρ`
    that satisfies `isAtAssert` has getEval = ρ.eval and getStore = ρ.store. -/
theorem assert_tail_getEvalStore
    (ρ : Env P) (l : String) (e : P.Expr) (md : MetaData P)
    (cfg : Config P (Cmd P)) (a : AssertId P)
    (hstar : StepStmtStar P (EvalCmd P) extendEval
      (.stmts [Stmt.cmd (Cmd.assert l e md)] ρ) cfg)
    (hat : isAtAssert P cfg a) :
    cfg.getEval = ρ.eval ∧ cfg.getStore = ρ.store := by
  cases hstar with
  | refl => exact ⟨rfl, rfl⟩
  | step _ _ _ h1 hr1 => cases h1 with
    | step_stmts_cons => cases hr1 with
      | refl => exact ⟨rfl, rfl⟩
      | step _ _ _ h2 hr2 =>
        cases h2 with
        | step_seq_inner hi =>
          cases hi with
          | step_cmd =>
            cases hr2 with
            | refl => exact absurd hat (by simp [isAtAssert])
            | step _ _ _ h3 hr3 =>
              cases h3 with
              | step_seq_inner h_t => exact absurd h_t (by intro h; cases h)
              | step_seq_done =>
                cases hr3 with
                | refl => exact absurd hat (by simp [isAtAssert])
                | step _ _ _ h4 hr4 =>
                  cases h4 with
                  | step_stmts_nil =>
                    cases hr4 with
                    | refl => exact absurd hat (by simp [isAtAssert])
                    | step _ _ _ h5 _ => exact absurd h5 (by intro h; cases h)

/-! ## hasFailure preservation

The lemmas below are abstract over the command type `CmdT`, the command
evaluator `EvalCmd`, and an `IsAtAssert` predicate.  Language extensions
(such as Core, whose commands are `CmdExt Expression`) supply their own
`IsAtAssert` predicate together with a few simple hypotheses relating it
to the loop / seq / block structure of configurations. -/

omit [HasFvar P] in
/-- Helper: when all asserts at a loop config pass (via `hv`), the
    loop-step's `hasInvFailure` boolean is forced to `false`. -/
theorem loop_step_hasInvFailure_false
    {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
    (IsAtAssert : Config P CmdT → AssertId P → Prop)
    (h_IsAtAssert_loop : ∀ {g m inv body md ρ lbl e},
      (lbl, e) ∈ inv →
      IsAtAssert (.stmt (.loop g m inv body md) ρ) ⟨lbl, e⟩)
    {c : Config P CmdT} {ρ : Env P}
    {inv : List (String × P.Expr)} {guard : ExprOrNondet P}
    {m : Option P.Expr} {body : List (Stmt P CmdT)} {md : MetaData P}
    {hasInvFailure : Bool}
    (hc_shape : c = .stmt (.loop guard m inv body md) ρ)
    (hv : ∀ a cfg, StepStmtStar P EvalCmd extendEval c cfg →
      IsAtAssert cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt)
    (hff_iff : hasInvFailure = true ↔ ∃ le, le ∈ inv ∧
      ρ.eval ρ.store le.snd = some HasBool.ff) :
    hasInvFailure = false := by
  cases hb : hasInvFailure with
  | false => rfl
  | true =>
    exfalso
    rw [hb] at hff_iff
    have ⟨⟨lbl, e⟩, hmem, he_ff⟩ := hff_iff.mp rfl
    have hat : IsAtAssert c ⟨lbl, e⟩ := hc_shape ▸ h_IsAtAssert_loop hmem
    have htt := hv ⟨lbl, e⟩ c (.refl _) hat
    rw [hc_shape] at htt
    simp only [Config.getEval, Config.getStore, Config.getEnv] at htt
    rw [he_ff] at htt
    exact absurd (Option.some.inj htt) HasBool.tt_is_not_ff.symm

omit [HasFvar P] in
/-- Single-step: if hasFailure is false and all reachable asserts pass,
    then hasFailure stays false after one step.

    Parameterized over an abstract `IsAtAssert` predicate so the lemma
    applies to both the base Imperative dialect and language extensions
    (e.g., Core). -/
theorem step_preserves_noFailure
    {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
    (IsAtAssert : Config P CmdT → AssertId P → Prop)
    (h_failure_implies_assert_ff :
      ∀ {ρ : Env P} {c : CmdT} {σ'},
        EvalCmd ρ.eval ρ.store c σ' true →
        ∃ a : AssertId P, IsAtAssert (.stmt (.cmd c) ρ) a ∧
          ρ.eval ρ.store a.expr = some HasBool.ff)
    (h_IsAtAssert_loop : ∀ {g m inv body md ρ lbl e},
      (lbl, e) ∈ inv →
      IsAtAssert (.stmt (.loop g m inv body md) ρ) ⟨lbl, e⟩)
    (h_IsAtAssert_seq : ∀ {inner ss a},
      IsAtAssert inner a → IsAtAssert (.seq inner ss) a)
    (h_IsAtAssert_block : ∀ {label σ_parent inner a},
      IsAtAssert inner a → IsAtAssert (.block label σ_parent inner) a)
    (c₁ c₂ : Config P CmdT)
    (hv : ∀ a cfg, StepStmtStar P EvalCmd extendEval c₁ cfg →
      IsAtAssert cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt)
    (hnf : c₁.getEnv.hasFailure = false)
    (hstep : StepStmt P EvalCmd extendEval c₁ c₂) :
    c₂.getEnv.hasFailure = false := by
  induction hstep with
  | step_cmd hcmd =>
    simp only [Config.getEnv] at hnf ⊢
    -- The per-command failure flag can be either true or false.
    match h : ‹Bool› with
    | false => simp [hnf, h]
    | true =>
      exfalso
      have ⟨a, hat, hff⟩ := h_failure_implies_assert_ff (h ▸ hcmd)
      have htt := hv a _ (.refl _) hat
      simp only [Config.getEval, Config.getStore, Config.getEnv] at htt
      rw [hff] at htt
      exact absurd (Option.some.inj htt) HasBool.tt_is_not_ff.symm
  | step_block | step_funcDecl => simp [Config.getEnv]; exact hnf
  | step_loop_enter _ _ hff_iff _ | step_loop_exit _ _ hff_iff _
  | step_loop_nondet_enter _ hff_iff | step_loop_nondet_exit _ hff_iff =>
    simp only [Config.getEnv]
    have hinv := loop_step_hasInvFailure_false (P := P) (extendEval := extendEval)
      IsAtAssert h_IsAtAssert_loop rfl hv hff_iff
    simp [Config.getEnv] at hnf
    rw [hnf, Bool.false_or]; exact hinv
  | step_seq_inner h ih =>
    exact ih
      (fun a cfg hr hat =>
        hv a (.seq cfg _) (seq_inner_star P EvalCmd extendEval _ _ _ hr) (h_IsAtAssert_seq hat)) hnf
  | step_block_body h ih =>
    exact ih
      (fun a cfg hr hat =>
        hv a (.block _ _ cfg) (block_inner_star P EvalCmd extendEval _ _ _ _ hr) (h_IsAtAssert_block hat)) hnf
  | _ => intros; exact hnf

theorem allAssertsValid_preserves_noFailure
    {ρ₀ ρ' : Env P}
    (st : Stmt P (Cmd P))
    (hvalid : ∀ (a : AssertId P) (cfg : Config P (Cmd P)),
      StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) cfg →
      isAtAssert P cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt)
    (hf₀ : ρ₀.hasFailure = false)
    (hstar : StepStmtStar P (EvalCmd P) extendEval (.stmt st ρ₀) (.terminal ρ')) :
    ρ'.hasFailure = false := by
  suffices ∀ c₁ c₂,
      (∀ a cfg, StepStmtStar P (EvalCmd P) extendEval c₁ cfg →
        isAtAssert P cfg a → cfg.getEval cfg.getStore a.expr = some HasBool.tt) →
      c₁.getEnv.hasFailure = false →
      StepStmtStar P (EvalCmd P) extendEval c₁ c₂ →
      c₂.getEnv.hasFailure = false by
    exact this _ _ hvalid hf₀ hstar
  intro c₁ c₂ hv hnf hstar_c
  induction hstar_c with
  | refl => exact hnf
  | step _ mid _ hstep _ ih =>
    refine ih
      (fun a cfg h hat => hv a _ (.step _ _ _ hstep h) hat)
      (step_preserves_noFailure (P := P) (extendEval := extendEval)
        (isAtAssert P)
        (fun hcmd => by
          cases hcmd with
          | eval_assert_fail hff _ _ => exact ⟨⟨_, _⟩, ⟨rfl, rfl⟩, hff⟩)
        (fun hmem => hmem)
        (fun h => h)
        (fun h => h)
        _ _ hv hnf hstep)

end -- section

section AssertSetProps

/-! ### Assert command properties (statement-level) -/

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVarsPure P P.Expr]
variable {extendEval : ExtendEval P}

theorem eval_stmt_assert_store_cst :
  EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l e md)) ρ' → ρ.store = ρ'.store := by
  intro Heval
  unfold EvalStmtSmall at Heval
  match Heval with
  | .step _ _ _ (.step_cmd hcmd) hrest =>
    cases hrest with
    | refl => simp; exact eval_assert_store_cst hcmd
    | step _ _ _ hstep _ => exact absurd hstep (by intro h; cases h)

theorem eval_stmt_assert_eval_cst :
  EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l e md)) ρ' → ρ.eval = ρ'.eval := by
  intro Heval
  unfold EvalStmtSmall at Heval
  match Heval with
  | .step _ _ _ (.step_cmd _) hrest =>
    cases hrest with
    | refl => simp
    | step _ _ _ hstep _ => exact absurd hstep (by intro h; cases h)

theorem eval_stmts_assert_store_cst :
  EvalStmtsSmall P (EvalCmd P) extendEval ρ [(.cmd (Cmd.assert l e md))] ρ' → ρ.store = ρ'.store := by
  intro Heval
  have hstmt : EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l e md)) ρ' := by
    unfold EvalStmtsSmall at Heval
    unfold EvalStmtSmall
    match Heval with
    | .step _ _ _ .step_stmts_cons hrest =>
      have ⟨ρ₁, hterm, htail⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
      match htail with
      | .step _ _ _ .step_stmts_nil hrest' =>
        cases hrest' with
        | refl => exact hterm
        | step _ _ _ h _ => exact absurd h (by intro h; cases h)
  exact eval_stmt_assert_store_cst hstmt

theorem eval_stmt_assert_eq_of_pure_expr_eq :
  WellFormedSemanticEvalBool ρ.eval →
  (EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l1 e md1)) ρ' ↔
  EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l2 e md2)) ρ') := by
  intro Hwf
  constructor <;>
  (
    intro Heval
    unfold EvalStmtSmall at Heval ⊢
    match Heval with
    | .step _ _ _ (.step_cmd hcmd) hrest =>
      cases hrest with
      | refl =>
        cases hcmd with
        | eval_assert_pass htt _ hcongr =>
          exact .step _ _ _ (.step_cmd (EvalCmd.eval_assert_pass htt Hwf hcongr)) (.refl _)
        | eval_assert_fail hne _ hcongr =>
          exact .step _ _ _ (.step_cmd (EvalCmd.eval_assert_fail hne Hwf hcongr)) (.refl _)
      | step _ _ _ hstep _ => exact absurd hstep (by intro h; cases h)
  )

/-! ### Assert elimination -/

theorem eval_stmts_assert_elim :
  WellFormedSemanticEvalBool ρ.eval →
  EvalStmtsSmall P (EvalCmd P) extendEval ρ (.cmd (.assert l1 e md1) :: cmds) ρ' →
  ∃ ρ'', EvalStmtsSmall P (EvalCmd P) extendEval ρ cmds ρ'' ∧
    ρ''.store = ρ'.store ∧ ρ''.eval = ρ'.eval ∧
    (ρ'.hasFailure = false → ρ''.hasFailure = false) := by
  intro Hwf Heval
  unfold EvalStmtsSmall at Heval
  match Heval with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, hterm_assert, htail⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
    have ⟨hcmd, hσ, hδ⟩ : (∃ σ' f, EvalCmd P ρ.eval ρ.store (.assert l1 e md1) σ' f) ∧
        ρ.store = ρ₁.store ∧ ρ.eval = ρ₁.eval := by
      match hterm_assert with
      | .step _ _ _ (.step_cmd hcmd) (.refl _) =>
        exact ⟨⟨_, _, hcmd⟩, eval_assert_store_cst hcmd, rfl⟩
    have ⟨ρ'', Hblock, Hstore, Heval_eq⟩ :=
      EvalStmtsSmall_hasFailure_irrel P (EvalCmd P) extendEval htail ρ hσ hδ
    match hterm_assert with
    | .step _ _ _ (.step_cmd hcmd) (.refl _) =>
      cases hcmd with
      | eval_assert_pass =>
        exists ρ'
        refine ⟨?_, rfl, rfl, id⟩
        show StepStmtStar P (EvalCmd P) extendEval (.stmts cmds ρ) (.terminal ρ')
        have : ρ = { store := ρ.store, eval := ρ.eval, hasFailure := ρ.hasFailure || false } := by
          cases ρ; simp
        rw [this]; exact htail
      | eval_assert_fail =>
        exists ρ''
        refine ⟨Hblock, Hstore, Heval_eq, ?_⟩
        intro Hf
        have hf1 : (Env.mk ρ.store ρ.eval (ρ.hasFailure || true)).hasFailure = true := by simp
        exact absurd (EvalStmtsSmall_hasFailure_monotone P (EvalCmd P) extendEval htail hf1)
          (by simp [Hf])

theorem assert_elim :
  WellFormedSemanticEvalBool ρ.eval →
  EvalStmtsSmall P (EvalCmd P) extendEval ρ (.cmd (.assert l1 e md1) :: [.cmd (.assert l2 e md2)]) ρ' →
  EvalStmtsSmall P (EvalCmd P) extendEval ρ [.cmd (.assert l3 e md3)] ρ' := by
  intro Hwf Heval
  unfold EvalStmtsSmall at Heval ⊢
  match Heval with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, hterm1, htail1⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
    match hterm1 with
    | .step _ _ _ (.step_cmd hcmd1) (.refl _) =>
      match htail1 with
      | .step _ _ _ .step_stmts_cons hrest2 =>
        have ⟨ρ₂, hterm2, htail2⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest2
        match hterm2 with
        | .step _ _ _ (.step_cmd hcmd2) (.refl _) =>
          match htail2 with
          | .step _ _ _ .step_stmts_nil (.refl _) =>
            cases hcmd1 with
            | eval_assert_pass h1 _ hcongr =>
              cases hcmd2 with
              | eval_assert_pass _ _ _ =>
                apply ReflTrans.step _ _ _ .step_stmts_cons
                apply ReflTrans.step _ _ _ (.step_seq_inner (.step_cmd (EvalCmd.eval_assert_pass h1 Hwf hcongr)))
                apply ReflTrans.step _ _ _ .step_seq_done
                apply ReflTrans.step _ _ _ .step_stmts_nil
                simp_all [Bool.or_false]; exact .refl _
              | eval_assert_fail h2 _ _ =>
                simp at h2
                exact absurd (h1.symm.trans h2)
                  (by exact fun h => HasBool.tt_is_not_ff (Option.some.inj h))
            | eval_assert_fail h1 _ hcongr =>
              cases hcmd2 with
              | eval_assert_pass h2 _ _ =>
                simp at h2
                exact absurd (h2.symm.trans h1)
                  (by exact fun h => HasBool.tt_is_not_ff (Option.some.inj h))
              | eval_assert_fail _ _ _ =>
                apply ReflTrans.step _ _ _ .step_stmts_cons
                apply ReflTrans.step _ _ _ (.step_seq_inner (.step_cmd (EvalCmd.eval_assert_fail h1 Hwf hcongr)))
                apply ReflTrans.step _ _ _ .step_seq_done
                apply ReflTrans.step _ _ _ .step_stmts_nil
                simp_all [Bool.or_true]; exact .refl _

/-! ### Set command commutation -/

theorem eval_stmt_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasVal P] [DecidableEq P.Ident]:
  WellFormedSemanticEvalExprCongr ρ.eval →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasVarsPure.getVars v2 →
  ¬ x2 ∈ HasVarsPure.getVars v1 →
  EvalStmtSmall P (EvalCmd P) evalFun ρ (.cmd (Cmd.set x1 (.det v1) md1)) ρ1 →
  EvalStmtSmall P (EvalCmd P) evalFun ρ1 (.cmd (Cmd.set x2 (.det v2) md2)) ρ' →
  EvalStmtSmall P (EvalCmd P) evalFun ρ (.cmd (Cmd.set x2 (.det v2) md2')) ρ2 →
  EvalStmtSmall P (EvalCmd P) evalFun ρ2 (.cmd (Cmd.set x1 (.det v1) md1')) ρ'' →
  ρ'.store = ρ''.store := by
  intro Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4
  unfold EvalStmtSmall at Hs1 Hs2 Hs3 Hs4
  match Hs1, Hs2, Hs3, Hs4 with
  | .step _ _ _ (.step_cmd Hc1) (.refl _),
    .step _ _ _ (.step_cmd Hc2) (.refl _),
    .step _ _ _ (.step_cmd Hc3) (.refl _),
    .step _ _ _ (.step_cmd Hc4) (.refl _) =>
    simp
    exact eval_cmd_set_comm Hwf Hneq Hnin1 Hnin2 Hc1 Hc2 Hc3 Hc4

theorem eval_stmts_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasVal P] [DecidableEq P.Ident] :
  WellFormedSemanticEvalExprCongr ρ.eval →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasVarsPure.getVars v2 →
  ¬ x2 ∈ HasVarsPure.getVars v1 →
  EvalStmtsSmall P (EvalCmd P) evalFun ρ [(.cmd (Cmd.set x1 (.det v1) md1)), (.cmd (Cmd.set x2 (.det v2) md2))] ρ' →
  EvalStmtsSmall P (EvalCmd P) evalFun ρ [(.cmd (Cmd.set x2 (.det v2) md2')), (.cmd (Cmd.set x1 (.det v1) md1'))] ρ'' →
  ρ'.store = ρ''.store := by
  intro Hwf Hneq Hnin1 Hnin2 Heval1 Heval2
  have extract := fun (s1 s2 : Stmt P (Cmd P)) (ρ₀ ρ_final : Env P)
      (h : EvalStmtsSmall P (EvalCmd P) evalFun ρ₀ [s1, s2] ρ_final) =>
    show ∃ ρ_mid, EvalStmtSmall P (EvalCmd P) evalFun ρ₀ s1 ρ_mid ∧
        EvalStmtSmall P (EvalCmd P) evalFun ρ_mid s2 ρ_final from by
      unfold EvalStmtsSmall EvalStmtSmall at *
      match h with
      | .step _ _ _ .step_stmts_cons hrest =>
        have ⟨ρ₁, hterm1, htail1⟩ := seq_reaches_terminal P (EvalCmd P) evalFun hrest
        match htail1 with
        | .step _ _ _ .step_stmts_cons hrest2 =>
          have ⟨ρ₂, hterm2, htail2⟩ := seq_reaches_terminal P (EvalCmd P) evalFun hrest2
          match htail2 with
          | .step _ _ _ .step_stmts_nil (.refl _) =>
            exact ⟨ρ₁, hterm1, hterm2⟩
  have ⟨ρ_mid1, Hs1, Hs2⟩ := extract _ _ _ _ Heval1
  have ⟨ρ_mid2, Hs3, Hs4⟩ := extract _ _ _ _ Heval2
  exact eval_stmt_set_comm Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4

end AssertSetProps

end -- public section
end Imperative
