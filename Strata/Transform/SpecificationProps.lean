/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.Transform.Specification
import all Strata.DL.Imperative.CmdSemantics
import Strata.DL.Util.ListUtils
import Strata.DL.Imperative.SemanticsProps

/-! # Soundness Specification — Theorems

This module contains the theorems associated with the definitions in
`Strata.Transform.Specification`. See that file's module docstring for the
overall structure of the soundness-specification framework.
-/

public section

namespace Imperative

namespace Specification

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P]
variable (L : Lang P)


namespace Hoare

/-! ## Parametric Hoare rules -/

omit [HasVal P] in
/-- False precondition proves anything -/
theorem false_pre (s : L.StmtT) (Post : Env P → Prop) :
    Triple L (fun _ => False) s Post := by
  intro _ _ hpre; exact absurd hpre id

omit [HasVal P] in
/-- Consequence (weakening): strengthen precondition, weaken postconditions. -/
theorem consequence
    {Pre Pre' : Env P → Prop} {Post Post' : Env P → Prop} {s : L.StmtT}
    (h : Triple L Pre s Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple L Pre' s Post' := by
  intro ρ₀ ρ' hpre' hwfb hf₀ hstar
  have ⟨hp, hf⟩ := h ρ₀ ρ' (hpre ρ₀ hpre') hwfb hf₀ hstar
  exact ⟨hpost ρ' hp, hf⟩


/-! ## Structural Hoare rules (Imperative-specific) -/

section StmtRules

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

 omit [HasFvar P] [HasVal P] in
/-- Empty statement list is skip. -/
theorem skip_block (Pre : Env P → Prop) :
    TripleBlock evalCmd extendEval Pre [] Pre := by
  intro ρ₀ ρ' hpre _ hf₀ hstar
  match hstar with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ h1 r1 => cases h1 with
      | step_stmts_nil => cases r1 with
        | refl => exact ⟨hpre, hf₀⟩
        | step _ _ _ h _ => exact nomatch h
  | .inr ⟨_, hexit⟩ =>
    cases hexit with
    | step _ _ _ h _ => cases h with
      | step_stmts_nil => rename_i r; cases r with | step _ _ _ h _ => cases h

omit [HasVal P] in
/-- A single command. -/
theorem cmd (c : CmdT) (Pre Post : Env P → Prop)
    (h : ∀ ρ₀ σ' f, Pre ρ₀ → WellFormedSemanticEvalBool ρ₀.eval → ρ₀.hasFailure = false →
      evalCmd ρ₀.eval ρ₀.store c σ' f →
      Post { ρ₀ with store := σ', hasFailure := f } ∧ f = false) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.cmd c) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_cmd hcmd =>
      cases r1 with
      | refl =>
        have ⟨hp, hfeq⟩ := h ρ₀ _ _ hpre hwfb hf₀ hcmd
        simp [hf₀] at hp ⊢; exact ⟨hp, hfeq⟩
      | step _ _ _ h _ => exact nomatch h

omit [HasVal P] in
/-- Sequential cons. -/
theorem seq_cons {s : Stmt P CmdT} {ss : List (Stmt P CmdT)}
    {Pre Mid Post : Env P → Prop}
    (h₁ : Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre s Mid)
    (h₂ : TripleBlock evalCmd extendEval Mid ss Post)
    (hnofd : Stmt.noFuncDecl s = true)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock evalCmd extendEval Pre (s :: ss) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hdone
  have hwfb_preserved : ∀ ρ₁, StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
      WellFormedSemanticEvalBool ρ₁.eval := by
    intro ρ₁ hterm
    have this := smallStep_noFuncDecl_preserves_eval P evalCmd extendEval s ρ₀ ρ₁ hnofd hterm
    rw [this]; exact hwfb
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_ss⟩ := seq_reaches_terminal P evalCmd extendEval hrest
        have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hwfb hf₀ hterm_s
        exact h₂ ρ₁ ρ' hmid (hwfb_preserved ρ₁ hterm_s) hf₁ (.inl hrest_ss)
  | .inr ⟨lbl, hexit⟩ =>
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P evalCmd extendEval hrest with
        | .inl hexit_inner =>
          exact absurd hexit_inner
            (exitsCoveredByBlocks_noEscape P evalCmd extendEval s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
          have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hwfb hf₀ hterm_s
          exact h₂ ρ₁ ρ' hmid (hwfb_preserved ρ₁ hterm_s) hf₁ (.inr ⟨lbl, hexit_ss⟩)

omit [HasVal P] in
/-- Lift a `TripleBlock` to a `Triple` by wrapping in a block.
    The postcondition `Post` is required to be stable under `projectStore`
    (it only references variables defined before the block). -/
theorem TripleBlock.toTriple {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h : TripleBlock evalCmd extendEval Pre ss Post)
    (hpost_proj : PostWF Post) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.block l ss md) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  cases hstar with
  | step _ _ _ hstep hrest => cases hstep with
    | step_block =>
      match block_reaches_terminal P evalCmd extendEval hrest with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := h ρ₀ ρ_inner hpre hwfb hf₀ (.inl hterm)
        subst heq; exact hpost_proj ρ_inner _ hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := h ρ₀ ρ_inner hpre hwfb hf₀ (.inr ⟨lbl, hexit⟩)
        subst heq; exact hpost_proj ρ_inner _ hpost hf

omit [HasVal P] in
/-- Lift a `Triple` to a `TripleBlock` for a singleton list. -/
theorem Triple.toTripleBlock {s : Stmt P CmdT}
    {Pre Post : Env P → Prop}
    (h : Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre s Post)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock evalCmd extendEval Pre [s] Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hdone
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_nil⟩ := seq_reaches_terminal P evalCmd extendEval hrest
        have ⟨hp, hf⟩ := h ρ₀ ρ₁ hpre hwfb hf₀ hterm_s
        cases hrest_nil with
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_nil => cases r1 with
            | refl => exact ⟨hp, hf⟩
            | step _ _ _ h _ => exact nomatch h
  | .inr ⟨lbl, hexit⟩ =>
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P evalCmd extendEval hrest with
        | .inl hexit_s =>
          exact absurd hexit_s
            (exitsCoveredByBlocks_noEscape P evalCmd extendEval s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_nil⟩ =>
          cases hexit_nil with
          | step _ _ _ h _ => cases h with
            | step_stmts_nil => rename_i r; cases r with | step _ _ _ h _ => cases h

omit [HasVal P] in
/-- Empty block is skip. -/
theorem skip (l : String) (md : MetaData P) (Pre : Env P → Prop)
    (hpre_proj : PostWF Pre) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.block l [] md) Pre :=
  TripleBlock.toTriple evalCmd extendEval isAtAssertFn (skip_block evalCmd extendEval Pre) hpre_proj

omit [HasVal P] in
/-- If-then-else rule. -/
theorem ite {c : P.Expr} {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (ht : TripleBlock evalCmd extendEval (fun ρ => Pre ρ ∧ ρ.eval ρ.store c = some HasBool.tt) tss Post)
    (he : TripleBlock evalCmd extendEval (fun ρ => Pre ρ ∧ ρ.eval ρ.store c = some HasBool.ff) ess Post)
    (hpost_proj : PostWF Post) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.ite (.det c) tss ess md) Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_ite_true hc _ =>
      match block_reaches_terminal P evalCmd extendEval r1 with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := ht ρ₀ ρ_inner ⟨hpre, hc⟩ hwfb hf₀ (.inl hterm)
        subst heq; exact hpost_proj ρ_inner _ hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := ht ρ₀ ρ_inner ⟨hpre, hc⟩ hwfb hf₀ (.inr ⟨lbl, hexit⟩)
        subst heq; exact hpost_proj ρ_inner _ hpost hf
    | step_ite_false hc _ =>
      match block_reaches_terminal P evalCmd extendEval r1 with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := he ρ₀ ρ_inner ⟨hpre, hc⟩ hwfb hf₀ (.inl hterm)
        subst heq; exact hpost_proj ρ_inner _ hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := he ρ₀ ρ_inner ⟨hpre, hc⟩ hwfb hf₀ (.inr ⟨lbl, hexit⟩)
        subst heq; exact hpost_proj ρ_inner _ hpost hf

/- TODO: the WHILE rule -/

end StmtRules


/-! ## Connection between HoareTriple and AssertValid (standard Lang) -/

section StandardConnection

variable (P' : PureExpr) [HasFvar P'] [HasBool P'] [HasNot P'] [HasIntOrder P']
variable (extendEval : ExtendEval P')

/-- **Direction 1**: Hoare triple implies assert validity for `PredicatedStmt`. -/
theorem hoareTriple_implies_assertValid
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hoare : Triple (Lang.standard P' extendEval)
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt))
    (hno : st.noMatchingAssert post_label) :
    AssertValid (Lang.standard P' extendEval)
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩ := by
  intro ρ₀ cfg _ hreach hat
  have hno_match := noMatchingAssert_implies_no_reachable_assert P' extendEval st post_label post_expr hno
  unfold PredicatedStmt at hreach
  cases hreach with
  | refl => exact absurd hat (by simp [isAtAssert])
  | step _ _ _ hstep hrest =>
    cases hstep with
    | step_block =>
      have ⟨inner, heq_cfg, hinner_star, hat_inner⟩ :=
        block_isAtAssert_inner P' extendEval _ _ _ _ _ hrest hat
      subst heq_cfg
      cases hinner_star with
      | refl => exact absurd hat_inner (by simp [isAtAssert])
      | step _ _ _ hstep2 hrest2 =>
        cases hstep2 with
        | step_stmts_cons =>
          match seq_isAtAssert_cases P' extendEval _ _ _ _ hrest2 hat_inner with
          | .inl ⟨_, _, hreach_assume, hat_assume⟩ =>
            cases hreach_assume with
            | refl => exact absurd hat_assume (by simp [isAtAssert])
            | step _ _ _ h _ => cases h with
              | step_cmd => rename_i hr; cases hr with
                | refl => exact absurd hat_assume (by simp [isAtAssert])
                | step _ _ _ h _ => exact absurd h (by intro h; cases h)
          | .inr ⟨ρ₁, hterm_assume, hrest_stmts, hat_stmts⟩ =>
            cases hrest_stmts with
            | refl =>
              have : ¬ isAtAssert P' (.stmts (st :: [.cmd (.assert post_label post_expr post_md)]) ρ₁)
                  ⟨post_label, post_expr⟩ := by
                intro h_at
                match st with
                | .cmd (.assert l e md') =>
                  have h := hno_match ρ₁ (.stmt (.cmd (.assert l e md')) ρ₁) (.refl _)
                  simp [isAtAssert] at h h_at
                  exact h h_at.1 h_at.2
                | .loop _ _ inv _ _ =>
                  -- loop's isAtAssert: ∃ e, (post_label, e) ∈ inv ∧ post_expr = e
                  have h := hno_match ρ₁ (.stmt (.loop _ _ inv _ _) ρ₁) (.refl _)
                  exact h h_at
                | .cmd (.init ..) | .cmd (.set ..) | .cmd (.assume ..)
                | .cmd (.cover ..) | .block .. | .ite .. | .exit .. | .funcDecl ..
                | .typeDecl .. =>
                  simp [isAtAssert] at h_at
              exact absurd hat_stmts this
            | step _ _ _ hstep3 hrest3 =>
              cases hstep3 with
              | step_stmts_cons =>
                match seq_isAtAssert_cases P' extendEval _ _ _ _ hrest3 hat_stmts with
                | .inl ⟨_, _, hreach_st, hat_st⟩ =>
                  exact absurd hat_st (hno_match ρ₁ _ hreach_st)
                | .inr ⟨ρ', hterm_st, hrest_assert, hat_assert⟩ =>
                  cases hterm_assume with
                  | step _ _ _ h_assume_step h_assume_rest =>
                    cases h_assume_step with
                    | step_cmd hcmd =>
                      cases hcmd with
                      | eval_assume hpre hwfb =>
                        cases h_assume_rest with
                        | refl =>
                          have ⟨ρ'_clean, hterm_clean, hs_eq, he_eq⟩ :=
                            smallStep_hasFailure_irrel P' (EvalCmd P') extendEval
                              st _ ρ' hterm_st { ρ₀ with hasFailure := false } rfl rfl
                          have ⟨hpost, _⟩ := hoare { ρ₀ with hasFailure := false } ρ'_clean
                            hpre hwfb rfl hterm_clean
                          simp only [hs_eq, he_eq] at hpost
                          have ⟨he, hs⟩ := assert_tail_getEvalStore P' extendEval
                            ρ' post_label post_expr post_md inner ⟨post_label, post_expr⟩
                            hrest_assert hat_inner
                          dsimp [Config.getEval, Config.getStore, Config.getEnv] at he hs ⊢
                          rw [he, hs]; exact hpost
                        | step _ _ _ h _ => exact absurd h (by intro h; cases h)


/-- **Direction 2**: Assert validity for `PredicatedStmt` implies Hoare triple. -/
theorem allAssertsValid_implies_hoareTriple
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hvalid : AllAssertsValid (Lang.standard P' extendEval)
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)) :
    Triple (Lang.standard P' extendEval)
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt) := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  let assume_stmt : Stmt P' (Cmd P') := .cmd (.assume pre_label pre_expr pre_md)
  let assert_stmt : Stmt P' (Cmd P') := .cmd (.assert post_label post_expr post_md)
  let body : List (Stmt P' (Cmd P')) := [assume_stmt, st, assert_stmt]
  have hvalid_st : ∀ (a : AssertId P') (cfg : Config P' (Cmd P')),
      StepStmtStar P' (EvalCmd P') extendEval (.stmt st ρ₀) cfg →
      isAtAssert P' cfg a →
      cfg.getEval cfg.getStore a.expr = some HasBool.tt := by
    intro a cfg hstar_st hat
    have h_assume : StepStmtStar P' (EvalCmd P') extendEval
        (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
      .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
    have h_ρ₁_eq : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure || false } : Env P') = ρ₀ := by
      cases ρ₀; simp [Bool.or_false]
    have h1 := stmts_cons_step P' (EvalCmd P') extendEval assume_stmt [st, assert_stmt] ρ₀ _ h_assume
    rw [h_ρ₁_eq] at h1
    have h2 : StepStmtStar P' (EvalCmd P') extendEval
        (.stmts [st, assert_stmt] ρ₀) (.seq (.stmt st ρ₀) [assert_stmt]) :=
      .step _ _ _ StepStmt.step_stmts_cons (.refl _)
    have h3 := seq_inner_star P' (EvalCmd P') extendEval _ _ [assert_stmt] hstar_st
    have h_inner := ReflTrans_Transitive _ _ _ _ (ReflTrans_Transitive _ _ _ _ h1 h2) h3
    have h_block := block_inner_star P' (EvalCmd P') extendEval _ _ (.some block_label) ρ₀.store h_inner
    have h_start : StepStmtStar P' (EvalCmd P') extendEval
        (.stmt (.block block_label body block_md) ρ₀) (.block (.some block_label) ρ₀.store (.stmts body ρ₀)) :=
      .step _ _ _ StepStmt.step_block (.refl _)
    have h_full := ReflTrans_Transitive _ _ _ _ h_start h_block
    have h_result := hvalid a ρ₀ _ trivial h_full hat
    dsimp [Config.getEval, Config.getStore, Config.getEnv] at h_result ⊢
    exact h_result
  have h_assume : StepStmtStar P' (EvalCmd P') extendEval
      (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
  have h_ρ₁_eq : ({ store := ρ₀.store, eval := ρ₀.eval, hasFailure := ρ₀.hasFailure || false } : Env P') = ρ₀ := by
    cases ρ₀; simp [Bool.or_false]
  have h1 := stmts_cons_step P' (EvalCmd P') extendEval assume_stmt [st, assert_stmt] ρ₀ _ h_assume
  rw [h_ρ₁_eq] at h1
  have h2 := stmts_cons_step P' (EvalCmd P') extendEval st [assert_stmt] ρ₀ ρ' hstar
  have h3 : StepStmtStar P' (EvalCmd P') extendEval
      (.stmts [assert_stmt] ρ') (.seq (.stmt assert_stmt ρ') []) :=
    .step _ _ _ StepStmt.step_stmts_cons (.refl _)
  have h_inner := ReflTrans_Transitive _ _ _ _ (ReflTrans_Transitive _ _ _ _ h1 h2) h3
  have h_block := block_inner_star P' (EvalCmd P') extendEval _ _ (.some block_label) ρ₀.store h_inner
  have h_start : StepStmtStar P' (EvalCmd P') extendEval
      (.stmt (.block block_label body block_md) ρ₀) (.block (.some block_label) ρ₀.store (.stmts body ρ₀)) :=
    .step _ _ _ StepStmt.step_block (.refl _)
  have h_full := ReflTrans_Transitive _ _ _ _ h_start h_block
  have h_at : isAtAssert P' (.block (.some block_label) ρ₀.store (.seq (.stmt assert_stmt ρ') [])) ⟨post_label, post_expr⟩ := by
    simp [isAtAssert, assert_stmt]
  have h_result := hvalid ⟨post_label, post_expr⟩ ρ₀ _ trivial h_full h_at
  dsimp [Config.getEval, Config.getStore, Config.getEnv] at h_result
  exact ⟨h_result, allAssertsValid_preserves_noFailure P' extendEval
    (ρ₀ := ρ₀) (ρ' := ρ') st hvalid_st hf₀ hstar⟩

end StandardConnection

end Hoare


namespace Transform

omit [HasVal P] in
theorem sound_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (h₁ : Sound L₁ L₂ T₁) (h₂ : Sound L₂ L₃ T₂) :
    Sound L₁ L₃ (fun s => T₁ s >>= T₂) := by
  intro s s'' a hrun hvalid
  simp [bind, Option.bind] at hrun
  match h1 : T₁ s with
  | some s' => rw [h1] at hrun; exact h₁ s s' a h1 (h₂ s' s'' a hrun hvalid)
  | none => rw [h1] at hrun; exact absurd hrun (by nofun)

omit [HasVal P] in
theorem sound_assertValid (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (a : AssertId P)
    (s : L₁.StmtT) (s' : L₂.StmtT)
    (ht : T s = some s') (hsound : Sound L₁ L₂ T) (hvalid : AssertValid L₂ s' a) :
    AssertValid L₁ s a := hsound s s' a ht hvalid

omit [HasVal P] in
theorem sound_allAsserts (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (s : L₁.StmtT) (s' : L₂.StmtT) (ht : T s = some s')
    (hsound : Sound L₁ L₂ T) (hvalid : AllAssertsValid L₂ s') :
    AllAssertsValid L₁ s := fun a => hsound s s' a ht (hvalid a)

omit [HasVal P] in
theorem sound_id : Sound L L some := by
  intro s s' a ht hvalid; simp at ht; subst ht; exact hvalid

/-- If `T` overapproximates and a Hoare triple holds on `T(st)` in L₂,
    then the triple holds on `st` in L₁. -/
theorem overapproximates_triple (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (newPrefix : String)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : Overapproximates L₁ L₂ T newPrefix)
    {Pre Post : Env P → Prop}
    (htriple : Hoare.Triple L₂ Pre s' Post)
    (hswf : ∀ ρ₀ : Env P, Pre ρ₀ → L₁.initEnvWF [newPrefix] st ρ₀) :
    Hoare.Triple L₁ Pre st Post := by
  intro ρ₀ ρ' hpre hwfb hf₀ hstar
  have hmem : newPrefix ∈ [newPrefix] := List.mem_singleton.mpr rfl
  -- After erasing `newPrefix` from `[newPrefix]`, we get `[]`, so
  -- `PrefixDisjoint` is vacuously true.
  have hpd : PrefixDisjoint newPrefix ([newPrefix].erase newPrefix) := by
    intro p hp; simp [List.erase_cons_head] at hp
  have hr := hsem [newPrefix] st s' ht hmem hpd ρ₀ (hswf ρ₀ hpre)
  exact htriple ρ₀ ρ' hpre hwfb hf₀ (hr.1 ρ' |>.1 hstar)

/-- `Overapproximates` implies `OverapproximatesAggressively`. -/
theorem Overapproximates.toAggressive (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (newPrefix : String)
    (h : Overapproximates L₁ L₂ T newPrefix) :
    OverapproximatesAggressively L₁ L₂ T newPrefix := by
  intro prefixIdents st s' ht hmem hpd ρ₀ hswf
  have hr := h prefixIdents st s' ht hmem hpd ρ₀ hswf
  refine ⟨?_, ?_, hr.2.1, hr.2.2⟩
  · intro ρ' hstar
    exact .inr (fun _ => (hr.1 ρ').1 hstar)
  · intro lbl ρ' hstar
    exact .inr (fun _ => (hr.1 ρ').2 lbl hstar)

/-! ## Statement-list overapproximation (Imperative-specific)

Uses `Overapproximates L L T` (single-language): the proof decomposes
seq execution into terminal/exiting outcomes of individual statements,
which is exactly what `Overapproximates` provides. -/

section ImperativeStmts

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

omit [HasFvar P] [HasVal P] in
/-- Decompose a seq execution reaching a config with `hasFailure = true`:
    either the inner config reaches a failing config, or the inner terminates
    and the tail stmts reach a failing config. -/
private theorem seq_hasFailure_cases
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {cfg : Config P CmdT}
    (hstar : StepStmtStar P evalCmd extendEval (.seq inner ss) cfg)
    (hfail : cfg.getEnv.hasFailure = true) :
    (∃ inner_cfg, inner_cfg.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendEval inner inner_cfg)
    ∨
    (∃ ρ₁, StepStmtStar P evalCmd extendEval inner (.terminal ρ₁) ∧
      ∃ tail_cfg, tail_cfg.getEnv.hasFailure = true ∧
        StepStmtStar P evalCmd extendEval (.stmts ss ρ₁) tail_cfg) := by
  suffices ∀ src dst, StepStmtStar P evalCmd extendEval src dst →
      ∀ inner ss, src = .seq inner ss → dst.getEnv.hasFailure = true →
      (∃ inner_cfg, inner_cfg.getEnv.hasFailure = true ∧
        StepStmtStar P evalCmd extendEval inner inner_cfg)
      ∨
      (∃ ρ₁, StepStmtStar P evalCmd extendEval inner (.terminal ρ₁) ∧
        ∃ tail_cfg, tail_cfg.getEnv.hasFailure = true ∧
          StepStmtStar P evalCmd extendEval (.stmts ss ρ₁) tail_cfg) from
    this _ _ hstar _ _ rfl hfail
  intro src dst hstar_g
  induction hstar_g with
  | refl =>
    intro inner ss hsrc hf
    subst hsrc; simp [Config.getEnv] at hf
    exact Or.inl ⟨inner, hf, .refl _⟩
  | step _ mid _ hstep hrest ih =>
    intro inner ss hsrc hf; subst hsrc
    cases hstep with
    | step_seq_inner h =>
      match ih _ _ rfl hf with
      | Or.inl ⟨inner_cfg, hfi, hreach⟩ =>
        exact Or.inl ⟨inner_cfg, hfi, .step _ _ _ h hreach⟩
      | Or.inr ⟨ρ₁, hterm, tail_cfg, hft, htail⟩ =>
        exact Or.inr ⟨ρ₁, .step _ _ _ h hterm, tail_cfg, hft, htail⟩
    | step_seq_done =>
      exact Or.inr ⟨_, .refl _, _, hf, hrest⟩
    | step_seq_exit =>
      cases hrest with
      | refl => exact Or.inl ⟨.exiting _ _, hf, .refl _⟩
      | step _ _ _ h _ => cases h

/-- CanFail preservation for statement-list overapproximation. -/
private theorem overapproximates_stmts_canfail
    (hwf_ext : WFEvalExtension P extendEval)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (newPrefix : String)
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T newPrefix)
    (prefixIdents : List String) (hmem : newPrefix ∈ prefixIdents)
    (hpd : PrefixDisjoint newPrefix (prefixIdents.erase newPrefix))
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ : Env P),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss ρ₀ →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss' ρ₀ := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ _ _ _ ⟨cfg, hfail, hreach⟩
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this
    exact ⟨cfg, hfail, hreach⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, hreach⟩
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    cases hreach with
    | refl =>
      simp [Config.getEnv] at hfail
      exact ⟨.stmts (s' :: rest') ρ₀, by simp [Config.getEnv, hfail], .refl _⟩
    | step _ _ _ hstep hrest_exec =>
      cases hstep with
      | step_stmts_cons =>
        match seq_hasFailure_cases evalCmd extendEval hrest_exec hfail with
        | .inl ⟨inner_cfg, hf_inner, hreach_inner⟩ =>
          have hcanfail_s : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s ρ₀ :=
            ⟨inner_cfg, hf_inner, hreach_inner⟩
          have hcanfail_s' := (hsem prefixIdents s s' hs hmem hpd ρ₀ trivial).2.1 hcanfail_s
          obtain ⟨cfg', hf', hreach'⟩ := hcanfail_s'
          exact ⟨.seq cfg' rest', by simp [Config.getEnv]; exact hf',
            .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach')⟩
        | .inr ⟨ρ₁, hterm_s, tail_cfg, hf_tail, htail⟩ =>
          -- WF eval preservation across `s`'s execution: use `WFEvalExtension` (no
          -- `noFuncDecl` requirement; works even when `s` contains funcDecls).
          have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval :=
            star_preserves_wfBool P evalCmd extendEval hwf_ext hterm_s hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval :=
            star_preserves_wfVal P evalCmd extendEval hwf_ext hterm_s hwfv
          have hwfvar₁ : WellFormedSemanticEvalVar ρ₁.eval :=
            star_preserves_wfVar P evalCmd extendEval hwf_ext hterm_s hwfvar
          have hcanfail_rest : CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) rest ρ₁ :=
            ⟨tail_cfg, hf_tail, htail⟩
          have hcanfail_rest' := ih rest' hrm ρ₁ hwfb₁ hwfv₁ hwfvar₁ hcanfail_rest
          obtain ⟨cfg', hf', hreach'⟩ := hcanfail_rest'
          have hterm_s' := (hsem prefixIdents s s' hs hmem hpd ρ₀ trivial).1 ρ₁ |>.1 hterm_s
          exact ⟨cfg', hf',
            ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ hterm_s')
              hreach'⟩

private theorem overapproximates_stmts_aux
    (hwf_ext : WFEvalExtension P extendEval)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (newPrefix : String)
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T newPrefix)
    (prefixIdents : List String) (hmem : newPrefix ∈ prefixIdents)
    (hpd : PrefixDisjoint newPrefix (prefixIdents.erase newPrefix))
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        (StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.terminal ρ') →
         StepStmtStar P evalCmd extendEval (.stmts ss' ρ₀) (.terminal ρ'))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.exiting lbl ρ') →
                StepStmtStar P evalCmd extendEval (.stmts ss' ρ₀) (.exiting lbl ρ')) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ' _ _ _
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this; exact ⟨id, fun _ => id⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ' hwfb hwfv hwfvar
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have eval_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
        WellFormedSemanticEvalBool ρ₁.eval ∧ WellFormedSemanticEvalVal ρ₁.eval ∧
        WellFormedSemanticEvalVar ρ₁.eval := by
      intro ρ₁ hterm_s
      exact ⟨star_preserves_wfBool P evalCmd extendEval hwf_ext hterm_s hwfb,
             star_preserves_wfVal P evalCmd extendEval hwf_ext hterm_s hwfv,
             star_preserves_wfVar P evalCmd extendEval hwf_ext hterm_s hwfvar⟩
    constructor
    · intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendEval hrest_exec
          have ⟨hwfb₁, hwfv₁, hwfvar₁⟩ := eval_preserved ρ₁ hterm_s
          exact ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁
              ((hsem prefixIdents s s' hs hmem hpd ρ₀ trivial).1 ρ₁ |>.1 hterm_s))
            ((ih rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfvar₁).1 hterm_rest)
    · intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendEval hrest_exec with
          | .inl hexit_s =>
            exact .step _ _ _ .step_stmts_cons
              (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendEval _ _ rest'
                ((hsem prefixIdents s s' hs hmem hpd ρ₀ trivial).1 ρ' |>.2 lbl hexit_s))
                (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have ⟨hwfb₁, hwfv₁, hwfvar₁⟩ := eval_preserved ρ₁ hterm_s
            exact ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁
                ((hsem prefixIdents s s' hs hmem hpd ρ₀ trivial).1 ρ₁ |>.1 hterm_s))
              ((ih rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfvar₁).2 lbl hexit_rest)

theorem overapproximates_stmts
    (hwf_ext : WFEvalExtension P extendEval)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (newPrefix : String)
    (hsem : Overapproximates
        (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
        (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T newPrefix) :
    Overapproximates
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (fun ss => ss.mapM T) newPrefix := by
  intro prefixIdents ss ss' hmap hmem hpd ρ₀ hwf
  obtain ⟨hwfb, hwfv, hwfvar⟩ := hwf
  refine ⟨fun ρ' => overapproximates_stmts_aux evalCmd extendEval isAtAssertFn hwf_ext T newPrefix
    hsem prefixIdents hmem hpd ss ss' hmap ρ₀ ρ' hwfb hwfv hwfvar, ?_, ⟨hwfb, hwfv, hwfvar⟩⟩
  exact overapproximates_stmts_canfail evalCmd extendEval isAtAssertFn hwf_ext T newPrefix
    hsem prefixIdents hmem hpd ss ss' hmap ρ₀ hwfb hwfv hwfvar

private theorem overapproximatesAggressively_stmts_canfail
    (hwf_ext : WFEvalExtension P extendEval)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (newPrefix : String)
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T newPrefix)
    (prefixIdents : List String) (hmem : newPrefix ∈ prefixIdents)
    (hpd : PrefixDisjoint newPrefix (prefixIdents.erase newPrefix))
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ : Env P),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss ρ₀ →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss' ρ₀ := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ _ _ _ ⟨cfg, hfail, hreach⟩
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this
    exact ⟨cfg, hfail, hreach⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, hreach⟩
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    cases hreach with
    | refl =>
      simp [Config.getEnv] at hfail
      exact ⟨.stmts (s' :: rest') ρ₀, by simp [Config.getEnv, hfail], .refl _⟩
    | step _ _ _ hstep hrest_exec =>
      cases hstep with
      | step_stmts_cons =>
        match seq_hasFailure_cases evalCmd extendEval hrest_exec hfail with
        | .inl ⟨inner_cfg, hf_inner, hreach_inner⟩ =>
          have hcanfail_s : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s ρ₀ :=
            ⟨inner_cfg, hf_inner, hreach_inner⟩
          have hcanfail_s' := (hsem prefixIdents s s' hs hmem hpd ρ₀ trivial).2.2.1 hcanfail_s
          obtain ⟨cfg', hf', hreach'⟩ := hcanfail_s'
          exact ⟨.seq cfg' rest', by simp [Config.getEnv]; exact hf',
            .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach')⟩
        | .inr ⟨ρ₁, hterm_s, tail_cfg, hf_tail, htail⟩ =>
          have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval :=
            star_preserves_wfBool P evalCmd extendEval hwf_ext hterm_s hwfb
          have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval :=
            star_preserves_wfVal P evalCmd extendEval hwf_ext hterm_s hwfv
          have hwfvar₁ : WellFormedSemanticEvalVar ρ₁.eval :=
            star_preserves_wfVar P evalCmd extendEval hwf_ext hterm_s hwfvar
          have hcanfail_rest : CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) rest ρ₁ :=
            ⟨tail_cfg, hf_tail, htail⟩
          have hcanfail_rest' := ih rest' hrm ρ₁ hwfb₁ hwfv₁ hwfvar₁ hcanfail_rest
          obtain ⟨cfg', hf', hreach'⟩ := hcanfail_rest'
          -- hsem gives CanFail ∨ (hasFailure = false → terminates) for s' at ρ₁
          match (hsem prefixIdents s s' hs hmem hpd ρ₀ trivial).1 ρ₁ hterm_s with
          | .inl canfail_s' =>
            obtain ⟨cfg'', hf'', hreach''⟩ := canfail_s'
            exact ⟨.seq cfg'' rest', by simp [Config.getEnv]; exact hf'',
              .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach'')⟩
          | .inr hterm_s' =>
            by_cases hf₁ : ρ₁.hasFailure = false
            · exact ⟨cfg', hf',
                ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                  hreach'⟩
            · have hf₁' : ρ₁.hasFailure = true := by
                cases h : ρ₁.hasFailure <;> simp_all
              have hcanfail_s : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s ρ₀ :=
                ⟨.terminal ρ₁, by simp [Config.getEnv]; exact hf₁', hterm_s⟩
              have hcanfail_s' := (hsem prefixIdents s s' hs hmem hpd ρ₀ trivial).2.2.1 hcanfail_s
              obtain ⟨cfg'', hf'', hreach''⟩ := hcanfail_s'
              exact ⟨.seq cfg'' rest', by simp [Config.getEnv]; exact hf'',
                .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach'')⟩

omit [HasVal P] in
/-- Lifting CanFail from a head statement to a block (cons of statement list). -/
theorem canFail_head_to_block
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (ρ₀ : Env P)
    (h : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s ρ₀) :
    CanFailBlock evalCmd extendEval (s :: ss) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  refine ⟨.seq cfg ss, ?_, ?_⟩
  · simp [Config.getEnv]; exact hfail
  · exact ReflTrans_Transitive _ _ _ _
      (.step _ _ _ .step_stmts_cons (.refl _))
      (seq_inner_star P evalCmd extendEval _ _ ss hreach)

omit [HasFvar P] [HasVal P] in
/-- Lifting CanFail from a tail block to the cons block, given the head terminates. -/
theorem canFail_tail_to_block
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (ρ₀ ρ₁ : Env P)
    (hhead : StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁))
    (htail : CanFailBlock evalCmd extendEval ss ρ₁) :
    CanFailBlock evalCmd extendEval (s :: ss) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := htail
  exact ⟨cfg, hfail,
    ReflTrans_Transitive _ _ _ _
      (stmts_cons_step P evalCmd extendEval s ss ρ₀ ρ₁ hhead)
      hreach⟩

omit [HasVal P] in
/-- A failing block body lifts to a failing block statement. -/
theorem canFailBlock_to_canFail_block
    (l : String) (bss : List (Stmt P CmdT)) (md : MetaData P) (ρ₀ : Env P)
    (h : CanFailBlock evalCmd extendEval bss ρ₀) :
    CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) (.block l bss md) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  exact ⟨.block (.some l) ρ₀.store cfg, by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
    ReflTrans_Transitive _ _ _ _
      (step_block_enter P evalCmd extendEval l bss md ρ₀)
      (block_inner_star P evalCmd extendEval _ _ (.some l) ρ₀.store hreach)⟩

omit [HasFvar P] [HasVal P] in
/-- CanFail in a prefix lifts to CanFail in `prefix ++ suffix`. -/
theorem canFailBlock_append_left
    (ss₁ ss₂ : List (Stmt P CmdT)) (ρ₀ : Env P)
    (h : CanFailBlock evalCmd extendEval ss₁ ρ₀) :
    CanFailBlock evalCmd extendEval (ss₁ ++ ss₂) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  by_cases hnf : ρ₀.hasFailure = Bool.true
  · exact ⟨.stmts (ss₁ ++ ss₂) ρ₀, by simp [Config.getEnv]; exact hnf, .refl _⟩
  · suffices ∀ src tgt, StepStmtStar P evalCmd extendEval src tgt →
        tgt.getEnv.hasFailure = Bool.true →
        (∀ ss ρ, src = .stmts ss ρ →
          ∃ tgt', tgt'.getEnv.hasFailure = Bool.true ∧
            StepStmtStar P evalCmd extendEval (.stmts (ss ++ ss₂) ρ) tgt') ∧
        (∀ inner ss, src = .seq inner ss →
          ∃ tgt', tgt'.getEnv.hasFailure = Bool.true ∧
            StepStmtStar P evalCmd extendEval (.seq inner (ss ++ ss₂)) tgt') by
      have ⟨tgt', hf', hr'⟩ := (this _ _ hreach hfail).1 ss₁ ρ₀ rfl
      exact ⟨tgt', hf', hr'⟩
    intro src tgt hstar hf
    induction hstar with
    | refl =>
      exact ⟨fun ss ρ heq => by subst heq; exact ⟨_, by simp [Config.getEnv] at hf ⊢; exact hf, .refl _⟩,
             fun inner ss heq => by subst heq; exact ⟨_, by simp [Config.getEnv] at hf ⊢; exact hf, .refl _⟩⟩
    | step _ mid _ hstep hrest ih =>
      have ⟨ih1, ih2⟩ := ih hf
      exact ⟨fun ss ρ heq => by
        subst heq; cases hstep with
        | step_stmts_nil =>
          have hf_ρ : ρ.hasFailure = Bool.true := by
            cases hrest with
            | refl => simp [Config.getEnv] at hf; exact hf
            | step _ _ _ hstep' _ => cases hstep'
          exact ⟨.stmts ss₂ ρ, by simp [Config.getEnv]; exact hf_ρ, .refl _⟩
        | step_stmts_cons =>
          have ⟨tgt', hf', hr'⟩ := ih2 _ _ rfl
          exact ⟨tgt', hf', .step _ _ _ .step_stmts_cons hr'⟩,
      fun inner ss heq => by
        subst heq; cases hstep with
        | step_seq_inner h =>
          have ⟨tgt', hf', hr'⟩ := ih2 _ _ rfl
          exact ⟨tgt', hf', .step _ _ _ (.step_seq_inner h) hr'⟩
        | step_seq_done =>
          have ⟨tgt', hf', hr'⟩ := ih1 _ _ rfl
          exact ⟨tgt', hf', .step _ _ _ .step_seq_done hr'⟩
        | step_seq_exit =>
          cases hrest with
          | refl =>
            exact ⟨_, hf, .step _ _ _ .step_seq_exit (.refl _)⟩
          | step _ _ _ h _ => cases h⟩

omit [HasFvar P] [HasVal P] in
/-- CanFail in a suffix lifts to CanFail in `prefix ++ suffix`, given the prefix terminates. -/
theorem canFailBlock_append_right
    (ss₁ ss₂ : List (Stmt P CmdT)) (ρ₀ ρ₁ : Env P)
    (hpfx : StepStmtStar P evalCmd extendEval (.stmts ss₁ ρ₀) (.terminal ρ₁))
    (h : CanFailBlock evalCmd extendEval ss₂ ρ₁) :
    CanFailBlock evalCmd extendEval (ss₁ ++ ss₂) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  exact ⟨cfg, hfail, ReflTrans_Transitive _ _ _ _
    (stmts_prefix_terminal_append P evalCmd extendEval ss₁ ss₂ ρ₀ ρ₁ hpfx)
    hreach⟩

private theorem overapproximatesAggressively_stmts_aux
    (hwf_ext : WFEvalExtension P extendEval)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (newPrefix : String)
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T newPrefix)
    (prefixIdents : List String) (hmem : newPrefix ∈ prefixIdents)
    (hpd : PrefixDisjoint newPrefix (prefixIdents.erase newPrefix))
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        (StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.terminal ρ') →
          CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss' ρ₀ ∨
          (ρ'.hasFailure = false →
            StepStmtStar P evalCmd extendEval (.stmts ss' ρ₀) (.terminal ρ')))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendEval (.stmts ss ρ₀) (.exiting lbl ρ') →
          CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) ss' ρ₀ ∨
          (ρ'.hasFailure = false →
            StepStmtStar P evalCmd extendEval (.stmts ss' ρ₀) (.exiting lbl ρ'))) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ' _ _ _
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this; exact ⟨fun h => .inr (fun _ => h), fun lbl h => .inr (fun _ => h)⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ' hwfb hwfv hwfvar
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have eval_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
        WellFormedSemanticEvalBool ρ₁.eval ∧ WellFormedSemanticEvalVal ρ₁.eval
        ∧ WellFormedSemanticEvalVar ρ₁.eval := by
      intro ρ₁ hterm_s
      exact ⟨star_preserves_wfBool P evalCmd extendEval hwf_ext hterm_s hwfb,
             star_preserves_wfVal P evalCmd extendEval hwf_ext hterm_s hwfv,
             star_preserves_wfVar P evalCmd extendEval hwf_ext hterm_s hwfvar⟩
    have ⟨hsem_term, hsem_exit, hsem_fail, _hsem_swf⟩ :=
      hsem prefixIdents s s' hs hmem hpd ρ₀ trivial
    -- Helper for the common pattern: ρ₁.hasFailure = true → s can fail → s' can fail → lift
    have canfail_from_failure : ∀ (ρ₁ : Env P),
        StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
        ρ₁.hasFailure = true →
        CanFail (Lang.imperativeBlock evalCmd extendEval isAtAssertFn) (s' :: rest') ρ₀ := by
      intro ρ₁ hterm_s hf₁
      have hcanfail_s : CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) s ρ₀ :=
        ⟨.terminal ρ₁, by simp [Config.getEnv]; exact hf₁, hterm_s⟩
      exact canFail_head_to_block evalCmd extendEval isAtAssertFn s' rest' ρ₀
        (hsem_fail hcanfail_s)
    constructor
    · -- Terminal case
      intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendEval hrest_exec
          have ⟨hwfb₁, hwfv₁, hwfvar₁⟩ := eval_preserved ρ₁ hterm_s
          match hsem_term ρ₁ hterm_s with
          | .inl canfail_s' =>
            exact .inl (canFail_head_to_block evalCmd extendEval isAtAssertFn s' rest' ρ₀ canfail_s')
          | .inr hterm_s' =>
            -- First check if ρ₁.hasFailure = false; if not, we get CanFail directly
            by_cases hf₁ : ρ₁.hasFailure = false
            · -- ρ₁ has no failure, so s' terminates at ρ₁
              have ih_result := (ih rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfvar₁).1 hterm_rest
              match ih_result with
              | .inl canfail_rest' =>
                obtain ⟨cfg', hf', hreach'⟩ := canfail_rest'
                exact .inl ⟨cfg', hf',
                  ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                    hreach'⟩
              | .inr hterm_rest' =>
                exact .inr fun hf =>
                  ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                    (hterm_rest' hf)
            · -- ρ₁.hasFailure = true, so s can fail → s' can fail → lift to whole list
              have hf₁' : ρ₁.hasFailure = true := by
                rcases Bool.eq_false_or_eq_true ρ₁.hasFailure with h | h
                · exact h
                · exact absurd h hf₁
              exact .inl (canfail_from_failure ρ₁ hterm_s hf₁')
    · -- Exiting case
      intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendEval hrest_exec with
          | .inl hexit_s =>
            match hsem_exit lbl ρ' hexit_s with
            | .inl canfail_s' =>
              exact .inl (canFail_head_to_block evalCmd extendEval isAtAssertFn s' rest' ρ₀ canfail_s')
            | .inr hexit_s' =>
              exact .inr fun hf =>
                .step _ _ _ .step_stmts_cons
                  (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendEval _ _ rest'
                    (hexit_s' hf))
                    (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have ⟨hwfb₁, hwfv₁, hwfvar₁⟩ := eval_preserved ρ₁ hterm_s
            match hsem_term ρ₁ hterm_s with
            | .inl canfail_s' =>
              exact .inl (canFail_head_to_block evalCmd extendEval isAtAssertFn s' rest' ρ₀ canfail_s')
            | .inr hterm_s' =>
              have ih_result := (ih rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfvar₁).2 lbl hexit_rest
              match ih_result with
              | .inl canfail_rest' =>
                by_cases hf₁ : ρ₁.hasFailure = false
                · obtain ⟨cfg', hf', hreach'⟩ := canfail_rest'
                  exact .inl ⟨cfg', hf',
                    ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                      hreach'⟩
                · have hf₁' : ρ₁.hasFailure = true := by
                    rcases Bool.eq_false_or_eq_true ρ₁.hasFailure with h | h
                    · exact h
                    · exact absurd h hf₁
                  exact .inl (canfail_from_failure ρ₁ hterm_s hf₁')
              | .inr hexit_rest' =>
                exact .inr fun hf => by
                  by_cases hf₁ : ρ₁.hasFailure = false
                  · exact ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                      (hexit_rest' hf)
                  · exfalso
                    have hf₁' : ρ₁.hasFailure = true := by
                      rcases Bool.eq_false_or_eq_true ρ₁.hasFailure with h | h
                      · exact h
                      · exact absurd h hf₁
                    have : ρ'.hasFailure = true :=
                      StepStmtStar_hasFailure_monotone hexit_rest hf₁'
                    exact absurd hf (by simp [this])

theorem overapproximatesAggressively_stmts
    (hwf_ext : WFEvalExtension P extendEval)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (newPrefix : String)
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T newPrefix) :
    OverapproximatesAggressively
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (fun ss => ss.mapM T) newPrefix := by
  intro prefixIdents ss ss' hmap hmem hpd ρ₀ hwf
  obtain ⟨hwfb, hwfv, hwfvar⟩ := hwf
  refine ⟨fun ρ' hstar => ?_, fun lbl ρ' hstar => ?_, ?_, ⟨hwfb, hwfv, hwfvar⟩⟩
  · exact (overapproximatesAggressively_stmts_aux evalCmd extendEval isAtAssertFn hwf_ext T newPrefix
      hsem prefixIdents hmem hpd ss ss' hmap ρ₀ ρ' hwfb hwfv hwfvar).1 hstar
  · exact (overapproximatesAggressively_stmts_aux evalCmd extendEval isAtAssertFn hwf_ext T newPrefix
      hsem prefixIdents hmem hpd ss ss' hmap ρ₀ ρ' hwfb hwfv hwfvar).2 lbl hstar
  · exact overapproximatesAggressively_stmts_canfail evalCmd extendEval isAtAssertFn hwf_ext T
      newPrefix hsem prefixIdents hmem hpd ss ss' hmap ρ₀ hwfb hwfv hwfvar

end ImperativeStmts

end Transform
end Specification
end Imperative

end -- public section
