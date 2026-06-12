/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.Transform.Specification
import all Strata.Transform.Specification
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Util.ListUtils

/-! # Soundness Specification — Theorems

This module contains the theorems associated with the definitions in
`Strata.Transform.Specification`. See that file's module docstring for the
overall structure of the soundness-specification framework.
-/

public section

namespace Imperative

namespace Specification

variable {P : PureExpr} [HasFvar P] [HasOps P] [HasBool P] [HasBoolOps P] [HasVal P]
variable (L : Lang P)



namespace Hoare

/-! ## Parametric Hoare rules -/

omit [HasVal P] [HasOps P] [HasFvar P] [HasBool P] [HasBoolOps P] in
/-- False precondition proves anything -/
theorem false_pre (params : L.InitEnvWFParamsTy) (s : L.StmtT) (Post : Env P → Prop) :
    Triple L params (fun _ => False) s Post := by
  intro _ _ hpre; exact absurd hpre id

omit [HasVal P] [HasOps P] [HasFvar P] [HasBool P] [HasBoolOps P] in
/-- Consequence (weakening): strengthen precondition, weaken postconditions. -/
theorem consequence (params : L.InitEnvWFParamsTy)
    {Pre Pre' : Env P → Prop} {Post Post' : Env P → Prop} {s : L.StmtT}
    (h : Triple L params Pre s Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple L params Pre' s Post' := by
  intro ρ₀ ρ' hpre' hinit hf₀ hstar
  have ⟨hp, hf⟩ := h ρ₀ ρ' (hpre ρ₀ hpre') hinit hf₀ hstar
  exact ⟨hpost ρ' hp, hf⟩


/-! ## Structural Hoare rules (Imperative-specific) -/

section StmtRules

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

 omit [HasOps P] in
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

omit [HasOps P] in
/-- A single command. -/
theorem cmd (params : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    (c : CmdT) (Pre Post : Env P → Prop)
    (h : ∀ ρ₀ σ' f, Pre ρ₀ → WellFormedSemanticEvalBool ρ₀.eval →
      evalCmd ρ₀.eval ρ₀.store c σ' f →
      Post { ρ₀ with store := σ', hasFailure := f } ∧ f = false) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) params Pre (.cmd c) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_cmd hcmd =>
      cases r1 with
      | refl =>
        have ⟨hp, hfeq⟩ := h ρ₀ _ _ hpre hinit.wfBool hcmd
        simp [hf₀] at hp ⊢; exact ⟨hp, hfeq⟩
      | step _ _ _ h _ => exact nomatch h

/-- Sequential cons. -/
theorem seq_cons (params : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    {s : Stmt P CmdT} {ss : List (Stmt P CmdT)}
    {Pre Mid Post : Env P → Prop}
    (hwf_ext : WFEvalExtension P extendEval)
    (h₁ : Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) params Pre s Mid)
    (h₂ : TripleBlock evalCmd extendEval Mid ss Post)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock evalCmd extendEval Pre (s :: ss) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  -- `InitEnvWF`'s conditions only mention `ρ.eval`, and `WFEvalExtension`
  -- guarantees each is preserved along `s`'s execution (even through funcDecls).
  have hinit_preserved : ∀ ρ₁, StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
      InitEnvWF ρ₁ := by
    intro ρ₁ hterm
    exact ⟨star_preserves_wfBool P evalCmd extendEval hwf_ext hterm hinit.wfBool,
           star_preserves_wfVal P evalCmd extendEval hwf_ext hterm hinit.wfVal,
           star_preserves_wfVar P evalCmd extendEval hwf_ext hterm hinit.wfVar⟩
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_ss⟩ := seq_reaches_terminal P evalCmd extendEval hrest
        have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hinit hf₀ hterm_s
        exact h₂ ρ₁ ρ' hmid (hinit_preserved ρ₁ hterm_s) hf₁ (.inl hrest_ss)
  | .inr ⟨lbl, hexit⟩ =>
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P evalCmd extendEval hrest with
        | .inl hexit_inner =>
          exact absurd hexit_inner
            (exitsCoveredByBlocks_noEscape P evalCmd extendEval s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
          have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hinit hf₀ hterm_s
          exact h₂ ρ₁ ρ' hmid (hinit_preserved ρ₁ hterm_s) hf₁ (.inr ⟨lbl, hexit_ss⟩)

omit [HasOps P] in
/-- Lift a `TripleBlock` to a `Triple` by wrapping in a block.
    The postcondition `Post` is required to be stable under `projectStore`
    (it only references variables defined before the block). -/
theorem TripleBlock.toTriple
    (params : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h : TripleBlock evalCmd extendEval Pre ss Post)
    (hpost_proj : PostWF extendEval Post) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) params Pre (.block l ss md) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  cases hstar with
  | step _ _ _ hstep hrest => cases hstep with
    | step_block =>
      -- At block entry the inner is `.stmts ss ρ₀` whose eval is `ρ₀.eval`,
      -- which is exactly `e_parent`.  So `evalExtendsOf ρ₀.eval inner` is
      -- reflexive, and `star_preserves_evalExtendsOf` lifts the inner trace.
      have hinv₀ : Config.evalExtendsOf P extendEval ρ₀.eval (.stmts ss ρ₀) := by
        simp only [Config.evalExtendsOf]; exact .refl
      match block_reaches_terminal P evalCmd extendEval hrest with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := h ρ₀ ρ_inner hpre hinit hf₀ (.inl hterm)
        have hext : EvalExtensionOf extendEval ρ₀.eval ρ_inner.eval :=
          star_preserves_evalExtendsOf P evalCmd extendEval hinv₀ hterm
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := h ρ₀ ρ_inner hpre hinit hf₀ (.inr ⟨lbl, hexit⟩)
        have hext : EvalExtensionOf extendEval ρ₀.eval ρ_inner.eval :=
          star_preserves_evalExtendsOf P evalCmd extendEval hinv₀ hexit
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf

omit [HasOps P] in
/-- Lift a `Triple` to a `TripleBlock` for a singleton list. -/
theorem Triple.toTripleBlock
    (params : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    {s : Stmt P CmdT}
    {Pre Post : Env P → Prop}
    (h : Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) params Pre s Post)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock evalCmd extendEval Pre [s] Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_nil⟩ := seq_reaches_terminal P evalCmd extendEval hrest
        have ⟨hp, hf⟩ := h ρ₀ ρ₁ hpre hinit hf₀ hterm_s
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

omit [HasOps P] in
/-- Empty block is skip. -/
theorem skip (params : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    (l : String) (md : MetaData P) (Pre : Env P → Prop)
    (hpre_proj : PostWF extendEval Pre) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) params Pre (.block l [] md) Pre :=
  TripleBlock.toTriple evalCmd extendEval isAtAssertFn params (skip_block evalCmd extendEval Pre) hpre_proj

omit [HasOps P] in
/-- If-then-else rule. -/
theorem ite (params : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    {c : P.Expr} {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (ht : TripleBlock evalCmd extendEval (fun ρ => Pre ρ ∧ ρ.eval ρ.store c = some HasBool.tt) tss Post)
    (he : TripleBlock evalCmd extendEval (fun ρ => Pre ρ ∧ ρ.eval ρ.store c = some HasBool.ff) ess Post)
    (hpost_proj : PostWF extendEval Post) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) params Pre (.ite (.det c) tss ess md) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_ite_true hc _ =>
      have hinv₀ : Config.evalExtendsOf P extendEval ρ₀.eval (.stmts tss ρ₀) := by
        simp only [Config.evalExtendsOf]; exact .refl
      match block_reaches_terminal P evalCmd extendEval r1 with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := ht ρ₀ ρ_inner ⟨hpre, hc⟩ hinit hf₀ (.inl hterm)
        have hext := star_preserves_evalExtendsOf P evalCmd extendEval hinv₀ hterm
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := ht ρ₀ ρ_inner ⟨hpre, hc⟩ hinit hf₀ (.inr ⟨lbl, hexit⟩)
        have hext := star_preserves_evalExtendsOf P evalCmd extendEval hinv₀ hexit
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf
    | step_ite_false hc _ =>
      have hinv₀ : Config.evalExtendsOf P extendEval ρ₀.eval (.stmts ess ρ₀) := by
        simp only [Config.evalExtendsOf]; exact .refl
      match block_reaches_terminal P evalCmd extendEval r1 with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := he ρ₀ ρ_inner ⟨hpre, hc⟩ hinit hf₀ (.inl hterm)
        have hext := star_preserves_evalExtendsOf P evalCmd extendEval hinv₀ hterm
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := he ρ₀ ρ_inner ⟨hpre, hc⟩ hinit hf₀ (.inr ⟨lbl, hexit⟩)
        have hext := star_preserves_evalExtendsOf P evalCmd extendEval hinv₀ hexit
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf

/- TODO: the WHILE rule -/

end StmtRules


/-! ## Connection between HoareTriple and AssertValid (standard Lang) -/

section StandardConnection

variable (P' : PureExpr) [HasFvar P'] [HasFvars P'] [HasOps P'] [HasBool P'] [HasBoolOps P']
variable (extendEval : ExtendEval P')

omit [HasOps P'] in
/-- **Direction 1**: Hoare triple implies assert validity for `PredicatedStmt`. -/
theorem hoareTriple_implies_assertValid (params : (Lang.standard P' extendEval).InitEnvWFParamsTy)
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hoare : Triple (Lang.standard P' extendEval) params
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt))
    (hno : st.noMatchingAssert post_label) :
    AssertValidWhen (Lang.standard P' extendEval)
      InitEnvWF
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩ := by
  intro ρ₀ cfg hwhen hreach hat
  have hno_match := noMatchingAssert_implies_no_reachable_assert P' extendEval st post_label post_expr hno
  unfold PredicatedStmt at hreach
  cases hreach with
  | refl => exact absurd hat (by simp [isAtAssert])
  | step _ _ _ hstep hrest =>
    cases hstep with
    | step_block =>
      have ⟨inner, heq_cfg, hinner_star, hat_inner⟩ :=
        block_isAtAssert_inner P' extendEval _ _ _ _ _ _ hrest hat
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
                            hpre ⟨hwhen.wfBool, hwhen.wfVal, hwhen.wfVar⟩ rfl hterm_clean
                          simp only [hs_eq, he_eq] at hpost
                          have ⟨he, hs⟩ := assert_tail_getEvalStore P' extendEval
                            ρ' post_label post_expr post_md inner ⟨post_label, post_expr⟩
                            hrest_assert hat_inner
                          dsimp [Config.getEval, Config.getStore, Config.getEnv] at he hs ⊢
                          rw [he, hs]; exact hpost
                        | step _ _ _ h _ => exact absurd h (by intro h; cases h)


omit [HasOps P'] in
/-- **Direction 2**: Assert validity for `PredicatedStmt` implies Hoare triple. -/
theorem allAssertsValid_implies_hoareTriple
    (params : (Lang.standard P' extendEval).InitEnvWFParamsTy)
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hvalid : AllAssertsValid (Lang.standard P' extendEval)
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)) :
    Triple (Lang.standard P' extendEval) params
      (fun ρ => ρ.eval ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => ρ.eval ρ.store post_expr = some HasBool.tt) := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  have hwfb := hinit.wfBool
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
    have h_block := block_inner_star P' (EvalCmd P') extendEval _ _ (.some block_label) ρ₀.store ρ₀.eval h_inner
    have h_start : StepStmtStar P' (EvalCmd P') extendEval
        (.stmt (.block block_label body block_md) ρ₀)
        (.block (.some block_label) ρ₀.store ρ₀.eval (.stmts body ρ₀)) :=
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
  have h_block := block_inner_star P' (EvalCmd P') extendEval _ _ (.some block_label) ρ₀.store ρ₀.eval h_inner
  have h_start : StepStmtStar P' (EvalCmd P') extendEval
      (.stmt (.block block_label body block_md) ρ₀)
      (.block (.some block_label) ρ₀.store ρ₀.eval (.stmts body ρ₀)) :=
    .step _ _ _ StepStmt.step_block (.refl _)
  have h_full := ReflTrans_Transitive _ _ _ _ h_start h_block
  have h_at : isAtAssert P' (.block (.some block_label) ρ₀.store ρ₀.eval (.seq (.stmt assert_stmt ρ') [])) ⟨post_label, post_expr⟩ := by
    simp [isAtAssert, assert_stmt]
  have h_result := hvalid ⟨post_label, post_expr⟩ ρ₀ _ trivial h_full h_at
  dsimp [Config.getEval, Config.getStore, Config.getEnv] at h_result
  exact ⟨h_result, allAssertsValid_preserves_noFailure P' extendEval
    (ρ₀ := ρ₀) (ρ' := ρ') st hvalid_st hf₀ hstar⟩

end StandardConnection

end Hoare


namespace Transform

/-! ## Connection between Sound, AssertValid and AllAssertsValid -/

omit [HasVal P] [HasOps P] [HasBoolOps P] [HasFvar P] in
theorem sound_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (h₁ : Sound L₁ L₂ T₁) (h₂ : Sound L₂ L₃ T₂) :
    Sound L₁ L₃ (fun s => T₁ s >>= T₂) := by
  intro s s'' a hrun hvalid
  simp [bind, Option.bind] at hrun
  match h1 : T₁ s with
  | some s' => rw [h1] at hrun; exact h₁ s s' a h1 (h₂ s' s'' a hrun hvalid)
  | none => rw [h1] at hrun; exact absurd hrun (by nofun)

omit [HasVal P] [HasOps P] [HasBoolOps P] [HasFvar P] in
theorem sound_assertValid (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (a : AssertId P)
    (s : L₁.StmtT) (s' : L₂.StmtT)
    (ht : T s = some s') (hsound : Sound L₁ L₂ T) (hvalid : AssertValid L₂ s' a) :
    AssertValid L₁ s a := hsound s s' a ht hvalid

omit [HasVal P] [HasOps P] [HasBoolOps P] [HasFvar P] in
theorem sound_allAsserts (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (s : L₁.StmtT) (s' : L₂.StmtT) (ht : T s = some s')
    (hsound : Sound L₁ L₂ T) (hvalid : AllAssertsValid L₂ s') :
    AllAssertsValid L₁ s := fun a => hsound s s' a ht (hvalid a)

omit [HasVal P] [HasOps P] [HasBoolOps P] [HasFvar P] in
theorem sound_id : Sound L L some := by
  intro s s' a ht hvalid; simp at ht; subst ht; exact hvalid

/-! ## Connection between Overapproximates{When} and Hoare.Triple -/

omit [HasOps P] [HasVal P] [HasFvar P] [HasBool P] [HasBoolOps P] in
/-- Destructor recovering the "subset" shape of `OverapproximatesWhen` from its
    `Eq`-relational definition: the source-reachable terminal/exiting env is
    reachable from the target at the *same* env (no relational witness). -/
theorem OverapproximatesWhen.dest {L₁ L₂ : Lang P} {T : L₁.StmtT → Option L₂.StmtT}
    {pre : L₁.StmtT → Prop} {params₁ : L₁.InitEnvWFParamsTy} {params₂ : L₂.InitEnvWFParamsTy}
    (h : OverapproximatesWhen L₁ L₂ T pre params₁ params₂)
    {st : L₁.StmtT} {st' : L₂.StmtT} (ht : T st = some st') (hpre : pre st)
    (ρ₀ : Env P) (hinit : L₁.initEnvWF params₁ st ρ₀) :
    (∀ (ρ' : Env P),
      (L₁.star (L₁.stmtCfg st ρ₀) (L₁.terminalCfg ρ') →
        L₂.star (L₂.stmtCfg st' ρ₀) (L₂.terminalCfg ρ'))
      ∧
      (∀ lbl, L₁.star (L₁.stmtCfg st ρ₀) (L₁.exitingCfg lbl ρ') →
              L₂.star (L₂.stmtCfg st' ρ₀) (L₂.exitingCfg lbl ρ')))
    ∧ (CanFail L₁ st ρ₀ → CanFail L₂ st' ρ₀)
    ∧ L₂.initEnvWF params₂ st' ρ₀ := by
  have hr := h st st' ht hpre ρ₀ ρ₀ rfl hinit
  refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩, hr.2.1, hr.2.2⟩
  · obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').1 hstar; exact heq ▸ hstar'
  · obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').2 lbl hstar; exact heq ▸ hstar'

omit [HasOps P] [HasVal P] [HasFvar P] [HasBool P] [HasBoolOps P] in
/-- If `T` overapproximates and a Hoare triple holds on `T(st)` in L₂,
    then the triple holds on `st` in L₁. -/
theorem overapproximates_triple (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    {Pre Post : Env P → Prop}
    (htriple : Hoare.Triple L₂ params₂ Pre s' Post)
    (hsem : Overapproximates L₁ L₂ T params₁ params₂) :
    Hoare.Triple L₁ params₁ Pre st Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  have hr := hsem.dest ht trivial ρ₀ hinit
  exact htriple ρ₀ ρ' hpre hr.2.2 hf₀ (hr.1 ρ' |>.1 hstar)

omit [HasOps P] [HasVal P] [HasFvar P] [HasBool P] [HasBoolOps P] in
/-- Hoare-triple corollary for `OverapproximatesWhen`: if
    (1) `T` overapproximates when `oPre` holds,
    (2) `oPre st` holds where `st` is the input program,
    then a Hoare triple on `st2 = T(st)` in L₂ lifts to a Hoare triple on `st` in L₁. -/
theorem overapproximatesWhen_triple (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (oPre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (st2 : L₂.StmtT) (ht : T st = some st2)
    {Pre Post : Env P → Prop}
    (htriple : Hoare.Triple L₂ params₂ Pre st2 Post)
    (hsem : OverapproximatesWhen L₁ L₂ T oPre params₁ params₂)
    (hsource_pre : oPre st) :
    Hoare.Triple L₁ params₁ Pre st Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  have hr := hsem.dest ht hsource_pre ρ₀ hinit
  exact htriple ρ₀ ρ' hpre hr.2.2 hf₀ (hr.1 ρ' |>.1 hstar)

/-! ## Connection between Overapproximates{When} and OverapproximatesAggressively{When} -/

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- `OverapproximatesWhen` implies `OverapproximatesAggressivelyWhen` (same
    precondition).  An exact transform that handles all preconditioned inputs
    is also an aggressive transform that handles them. -/
theorem OverapproximatesWhen.toAggressivelyWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : OverapproximatesWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂ := by
  intro st s' ht hpre ρ₀ hswf
  have hr := h.dest ht hpre ρ₀ hswf
  refine ⟨?_, ?_, hr.2.1, hr.2.2⟩
  · intro ρ' hstar
    exact .inr (fun _ => (hr.1 ρ').1 hstar)
  · intro lbl ρ' hstar
    exact .inr (fun _ => (hr.1 ρ').2 lbl hstar)

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- `Overapproximates` implies `OverapproximatesAggressively`. -/
theorem Overapproximates.toAggressive (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : Overapproximates L₁ L₂ T params₁ params₂) :
    OverapproximatesAggressively L₁ L₂ T params₁ params₂ :=
  OverapproximatesWhen.toAggressivelyWhen L₁ L₂ T (fun _ => True) params₁ params₂ h

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- Precondition strengthening for `OverapproximatesWhen` -/
theorem OverapproximatesWhen.strengthen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) {pre pre' : L₁.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (himp : ∀ st, pre' st → pre st)
    (h : OverapproximatesWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesWhen L₁ L₂ T pre' params₁ params₂ := by
  intro st st' ht hpre' ρ₀ ρ₀' hR hswf
  exact h st st' ht (himp st hpre') ρ₀ ρ₀' hR hswf

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- Precondition strengthening for `OverapproximatesAggressivelyWhen`. -/
theorem OverapproximatesAggressivelyWhen.strengthen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) {pre pre' : L₁.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (himp : ∀ st, pre' st → pre st)
    (h : OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre' params₁ params₂ := by
  intro st st' ht hpre' ρ₀ hswf
  exact h st st' ht (himp st hpre') ρ₀ hswf

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- An unconditional `Overapproximates` is the strongest case: it gives
    `OverapproximatesWhen` for ANY precondition. -/
theorem Overapproximates.toWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : Overapproximates L₁ L₂ T params₁ params₂) :
    OverapproximatesWhen L₁ L₂ T pre params₁ params₂ :=
  OverapproximatesWhen.strengthen L₁ L₂ T params₁ params₂ (fun _ _ => trivial) h

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- An unconditional `OverapproximatesAggressively` likewise gives
    `OverapproximatesAggressivelyWhen` for any precondition. -/
theorem OverapproximatesAggressively.toWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : OverapproximatesAggressively L₁ L₂ T params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂ :=
  OverapproximatesAggressivelyWhen.strengthen L₁ L₂ T params₁ params₂ (fun _ _ => trivial) h

/-! ## Overapproximation up to a relation (`OverapproximatesUpto*`) -/

section Upto

open scoped Relations  -- `R₁ ∘ R₂` for relation composition (`RComp`)

/-! ### Connection to `OverapproximatesWhen`

`OverapproximatesWhen` is *definitionally* `OverapproximatesUptoWhen (· = ·)`,
so the connection lemmas are reflexivity. -/

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- `OverapproximatesWhen` is `OverapproximatesUptoWhen` at the equality
    relation (definitional). -/
theorem overapproximatesWhen_iff_uptoWhen_eq (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) :
    OverapproximatesWhen L₁ L₂ T pre params₁ params₂ ↔
      OverapproximatesUptoWhen (· = ·) L₁ L₂ T pre params₁ params₂ :=
  Iff.rfl

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- Unconditional version: `Overapproximates` is `OverapproximatesUpto` at
    equality (definitional). -/
theorem overapproximates_iff_upto_eq (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) :
    Overapproximates L₁ L₂ T params₁ params₂ ↔
      OverapproximatesUpto (· = ·) L₁ L₂ T params₁ params₂ :=
  Iff.rfl

/-! ### Monotonicity in the relation -/

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- Rewriting the relation `R → R'`.  Since `R` is used both as an input
    hypothesis (antitone) and an output witness (monotone), the change requires
    `R' ⊆ R` (for the input) *and* `R ⊆ R'` (for the output). -/
theorem OverapproximatesUptoWhen.mono (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    {R R' : Relation (Env P)}
    (hin : ∀ a b, R' a b → R a b)
    (hout : ∀ a b, R a b → R' a b)
    (h : OverapproximatesUptoWhen R L₁ L₂ T pre params₁ params₂) :
    OverapproximatesUptoWhen R' L₁ L₂ T pre params₁ params₂ := by
  intro st st' ht hpre ρ₀ ρ₀' hR' hwf
  have hr := h st st' ht hpre ρ₀ ρ₀' (hin _ _ hR') hwf
  refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩, hr.2.1, hr.2.2⟩
  · obtain ⟨ρ'', hR, hstar'⟩ := (hr.1 ρ').1 hstar; exact ⟨ρ'', hout _ _ hR, hstar'⟩
  · obtain ⟨ρ'', hR, hstar'⟩ := (hr.1 ρ').2 lbl hstar; exact ⟨ρ'', hout _ _ hR, hstar'⟩

/-! ### Precondition strengthening and identity -/

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- Precondition strengthening. -/
theorem OverapproximatesUptoWhen.strengthen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) {pre pre' : L₁.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    {R : Relation (Env P)}
    (himp : ∀ st, pre' st → pre st)
    (h : OverapproximatesUptoWhen R L₁ L₂ T pre params₁ params₂) :
    OverapproximatesUptoWhen R L₁ L₂ T pre' params₁ params₂ := by
  intro st st' ht hpre' ρ₀ ρ₀' hR hwf
  exact h st st' ht (himp st hpre') ρ₀ ρ₀' hR hwf

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- The identity transform is an overapproximation up to `Eq` (reflexivity).
    This is the unit for `comp`. -/
theorem OverapproximatesUpto.id (L : Lang P) (params : L.InitEnvWFParamsTy) :
    OverapproximatesUpto (· = ·) L L some params params := by
  intro st st' ht _ ρ₀ ρ₀' heq hwf
  simp only [Option.some.injEq] at ht; subst ht; subst heq
  exact ⟨fun ρ' => ⟨fun hstar => ⟨ρ', rfl, hstar⟩, fun lbl hstar => ⟨ρ', rfl, hstar⟩⟩,
         (fun h => h), hwf⟩

/-! ### Compositionality -/

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- **Compositionality** (general form): composing transforms composes the
    relations via `RComp`.  No conditions on the relations are needed at this
    level of generality — they only appear when collapsing the composite
    `RComp R₁ R₂` back into a single relation (see
    `OverapproximatesUptoWhen.comp_preorder`). -/
theorem OverapproximatesUptoWhen.comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {R₁ R₂ : Relation (Env P)}
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesUptoWhen R₁ L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesUptoWhen R₂ L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesUptoWhen (R₁ ∘ R₂)
      L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ := by
  intro st st'' ht hpre₁ ρ₀ ρ₀'' hR hwf
  -- Decompose the composed transform and the composed input relation.
  simp only [bind, Option.bind] at ht
  match hT₁ : T₁ st with
  | none => rw [hT₁] at ht; exact absurd ht (by nofun)
  | some st' =>
    rw [hT₁] at ht
    obtain ⟨ρ₀', hR₁, hR₂⟩ := hR
    have hr₁ := h₁ st st' hT₁ hpre₁ ρ₀ ρ₀' hR₁ hwf
    have hr₂ := h₂ st' st'' ht (hpre st st' hT₁ hpre₁) ρ₀' ρ₀'' hR₂ hr₁.2.2
    refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩,
            fun hcf => hr₂.2.1 (hr₁.2.1 hcf), hr₂.2.2⟩
    · obtain ⟨ρ'₂, hR₁', hstar₂⟩ := (hr₁.1 ρ').1 hstar
      obtain ⟨ρ'₃, hR₂', hstar₃⟩ := (hr₂.1 ρ'₂).1 hstar₂
      exact ⟨ρ'₃, ⟨ρ'₂, hR₁', hR₂'⟩, hstar₃⟩
    · obtain ⟨ρ'₂, hR₁', hstar₂⟩ := (hr₁.1 ρ').2 lbl hstar
      obtain ⟨ρ'₃, hR₂', hstar₃⟩ := (hr₂.1 ρ'₂).2 lbl hstar₂
      exact ⟨ρ'₃, ⟨ρ'₂, hR₁', hR₂'⟩, hstar₃⟩

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- **Compositionality** (single-relation form): if `R` is a *preorder*
    (`Reflexive` and `Transitive`) then composing two `OverapproximatesUptoWhen R`
    transforms yields another `OverapproximatesUptoWhen R` transform.

    The preorder conditions are exactly what is needed to collapse `RComp R R`
    back into `R`: *reflexivity* witnesses `R ⊆ RComp R R` on inputs (antitone
    side), and *transitivity* witnesses `RComp R R ⊆ R` on outputs (monotone
    side). -/
theorem OverapproximatesUptoWhen.comp_preorder (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    {pre₁ : L₁.StmtT → Prop} {pre₂ : L₂.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {R : Relation (Env P)}
    (hrefl : Reflexive R)
    (htrans : Transitive R)
    (hpre : ∀ st st', T₁ st = some st' → pre₁ st → pre₂ st')
    (h₁ : OverapproximatesUptoWhen R L₁ L₂ T₁ pre₁ params₁ params₂)
    (h₂ : OverapproximatesUptoWhen R L₂ L₃ T₂ pre₂ params₂ params₃) :
    OverapproximatesUptoWhen R L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃ :=
  -- The composite holds for `RComp R R`; reflexivity/transitivity collapse it to `R`.
  OverapproximatesUptoWhen.mono L₁ L₃ (fun s => T₁ s >>= T₂) pre₁ params₁ params₃
    (fun a _ hab => ⟨a, hrefl a, hab⟩)
    (fun _ _ h => RComp.collapse htrans (fun _ _ => _root_.id) (fun _ _ => _root_.id) h)
    (OverapproximatesUptoWhen.comp L₁ L₂ L₃ T₁ T₂ params₁ params₂ params₃ hpre h₁ h₂)

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- **Compositionality** for the unconditional `OverapproximatesUpto` under a
    preorder `R`.  The precondition obligation vanishes since `pre = fun _ => True`. -/
theorem OverapproximatesUpto.comp_preorder (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    {R : Relation (Env P)}
    (hrefl : Reflexive R)
    (htrans : Transitive R)
    (h₁ : OverapproximatesUpto R L₁ L₂ T₁ params₁ params₂)
    (h₂ : OverapproximatesUpto R L₂ L₃ T₂ params₂ params₃) :
    OverapproximatesUpto R L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ :=
  OverapproximatesUptoWhen.comp_preorder L₁ L₂ L₃ T₁ T₂ params₁ params₂ params₃
    hrefl htrans (fun _ _ _ _ => trivial) h₁ h₂

omit [HasOps P] [HasVal P] [HasBool P] [HasBoolOps P] [HasFvar P] in
/-- Recover plain `Overapproximates` compositionality from the relational
    version: composing two `Overapproximates` transforms (each `Upto Eq`) gives
    an `Overapproximates` transform.  `Eq` is a preorder, so `comp_preorder`
    applies. -/
theorem overapproximates_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : Overapproximates L₁ L₂ T₁ params₁ params₂)
    (h₂ : Overapproximates L₂ L₃ T₂ params₂ params₃) :
    Overapproximates L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ :=
  (overapproximates_iff_upto_eq L₁ L₃ _ params₁ params₃).mpr
    (OverapproximatesUpto.comp_preorder L₁ L₂ L₃ T₁ T₂ params₁ params₂ params₃
      (fun _ => rfl) (fun _ _ _ h h' => h.trans h')
      ((overapproximates_iff_upto_eq L₁ L₂ T₁ params₁ params₂).mp h₁)
      ((overapproximates_iff_upto_eq L₂ L₃ T₂ params₂ params₃).mp h₂))

end Upto

/-! ## Statement-list overapproximation (Imperative-specific)

Uses `Overapproximates L L T` (single-language): the proof decomposes
seq execution into terminal/exiting outcomes of individual statements,
which is exactly what `Overapproximates` provides. -/

section ImperativeStmts

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

omit [HasVal P] [HasOps P] [HasFvar P] in
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
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T params₁ params₂)
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
          have hcanfail_s' := (hsem.dest hs trivial ρ₀ ⟨hwfb, hwfv, hwfvar⟩).2.1 hcanfail_s
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
          have hterm_s' := (hsem.dest hs trivial ρ₀ ⟨hwfb, hwfv, hwfvar⟩).1 ρ₁ |>.1 hterm_s
          exact ⟨cfg', hf',
            ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁ hterm_s')
              hreach'⟩

private theorem overapproximates_stmts_aux
    (hwf_ext : WFEvalExtension P extendEval)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T params₁ params₂)
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
              ((hsem.dest hs trivial ρ₀ ⟨hwfb, hwfv, hwfvar⟩).1 ρ₁ |>.1 hterm_s))
            ((ih rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfvar₁).1 hterm_rest)
    · intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendEval hrest_exec with
          | .inl hexit_s =>
            exact .step _ _ _ .step_stmts_cons
              (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendEval _ _ rest'
                ((hsem.dest hs trivial ρ₀ ⟨hwfb, hwfv, hwfvar⟩).1 ρ' |>.2 lbl hexit_s))
                (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have ⟨hwfb₁, hwfv₁, hwfvar₁⟩ := eval_preserved ρ₁ hterm_s
            exact ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁
                ((hsem.dest hs trivial ρ₀ ⟨hwfb, hwfv, hwfvar⟩).1 ρ₁ |>.1 hterm_s))
              ((ih rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfvar₁).2 lbl hexit_rest)

theorem overapproximates_stmts
    (hwf_ext : WFEvalExtension P extendEval)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    (hsem : Overapproximates
        (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
        (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T params₁ params₂) :
    Overapproximates
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (fun ss => ss.mapM T) params₁ params₂ := by
  intro ss ss' hmap _ ρ₀ ρ₀' heq hwf
  -- `Overapproximates` unfolds to `OverapproximatesUptoWhen (· = ·)`: the input
  -- relation forces `ρ₀' = ρ₀`, and each output env `ρ'` is its own witness.
  subst heq
  obtain ⟨hwfb, hwfv, hwfvar⟩ := hwf
  have haux := overapproximates_stmts_aux evalCmd extendEval isAtAssertFn hwf_ext T params₁ params₂
    hsem ss ss' hmap ρ₀
  refine ⟨fun ρ' => ⟨fun hstar => ⟨ρ', rfl, (haux ρ' hwfb hwfv hwfvar).1 hstar⟩,
                     fun lbl hstar => ⟨ρ', rfl, (haux ρ' hwfb hwfv hwfvar).2 lbl hstar⟩⟩, ?_,
          ⟨hwfb, hwfv, hwfvar⟩⟩
  exact overapproximates_stmts_canfail evalCmd extendEval isAtAssertFn hwf_ext T params₁ params₂
    hsem ss ss' hmap ρ₀ hwfb hwfv hwfvar

/-! ## Statement-list aggressive overapproximation (Imperative-specific) -/

private theorem overapproximatesAggressively_stmts_canfail
    (hwf_ext : WFEvalExtension P extendEval)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T params₁ params₂)
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
          have hcanfail_s' := (hsem s s' hs trivial ρ₀ ⟨hwfb, hwfv, hwfvar⟩).2.2.1 hcanfail_s
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
          match (hsem s s' hs trivial ρ₀ ⟨hwfb, hwfv, hwfvar⟩).1 ρ₁ hterm_s with
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
              have hcanfail_s' := (hsem s s' hs trivial ρ₀ ⟨hwfb, hwfv, hwfvar⟩).2.2.1 hcanfail_s
              obtain ⟨cfg'', hf'', hreach''⟩ := hcanfail_s'
              exact ⟨.seq cfg'' rest', by simp [Config.getEnv]; exact hf'',
                .step _ _ _ .step_stmts_cons (seq_inner_star P evalCmd extendEval _ _ rest' hreach'')⟩

/- Block / ite execution helpers (generic over `CmdT`/`evalCmd`/`extendEval`) -/

omit [HasFvar P] [HasVal P] [HasOps P] in
/-- A terminal execution of the block body lifts to a terminal execution of
    the enclosing block statement (with parent-store projection applied). -/
theorem block_wrap_terminal
    (l : String) (bss : List (Stmt P CmdT)) (md : MetaData P)
    (ρ₀ ρ' : Env P)
    (h : StepStmtStar P evalCmd extendEval (.stmts bss ρ₀) (.terminal ρ')) :
    StepStmtStar P evalCmd extendEval (.stmt (.block l bss md) ρ₀)
      (.terminal { ρ' with store := projectStore ρ₀.store ρ'.store, eval := ρ₀.eval }) :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter P evalCmd extendEval l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star P evalCmd extendEval _ _ (some l) ρ₀.store ρ₀.eval h)
      (.step _ _ _ .step_block_done (.refl _)))

omit [HasFvar P] [HasVal P] [HasOps P] in
/-- Taking the false/else branch of a det-ite with empty else-block terminates at the
    same env (after scoped-ite projection, which is identity on self). -/
theorem ite_det_false_empty_terminal
    (g : P.Expr) (then_branch : List (Stmt P CmdT)) (md : MetaData P)
    (ρ₀ : Env P)
    (hg_ff : ρ₀.eval ρ₀.store g = some HasBool.ff)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval) :
    StepStmtStar P evalCmd extendEval
      (.stmt (.ite (.det g) then_branch [] md) ρ₀) (.terminal ρ₀) := by
  have h_inner : StepStmtStar P evalCmd extendEval
      (.stmts ([] : List (Stmt P CmdT)) ρ₀) (.terminal ρ₀) :=
    .step _ _ _ .step_stmts_nil (.refl _)
  have h_block : StepStmtStar P evalCmd extendEval
      (.block .none ρ₀.store ρ₀.eval (.stmts ([] : List (Stmt P CmdT)) ρ₀))
      (.terminal { ρ₀ with store := projectStore ρ₀.store ρ₀.store, eval := ρ₀.eval }) :=
    ReflTrans_Transitive _ _ _ _
      (block_inner_star P evalCmd extendEval _ _ .none ρ₀.store ρ₀.eval h_inner)
      (.step _ _ _ .step_block_done (.refl _))
  rw [projectStore_self_env] at h_block
  have henv : ({ ρ₀ with store := ρ₀.store, eval := ρ₀.eval } : Env P) = ρ₀ := by cases ρ₀; rfl
  rw [henv] at h_block
  exact .step _ _ _ (.step_ite_false hg_ff hwfb) h_block

omit [HasFvar P] [HasVal P] [HasOps P] in
/-- Taking the false/else branch of a nondet-ite with empty else-block terminates at the
    same env (after scoped-ite projection, which is identity on self). -/
theorem ite_nondet_false_empty_terminal
    (then_branch : List (Stmt P CmdT)) (md : MetaData P)
    (ρ₀ : Env P) :
    StepStmtStar P evalCmd extendEval
      (.stmt (.ite .nondet then_branch [] md) ρ₀) (.terminal ρ₀) := by
  have h_inner : StepStmtStar P evalCmd extendEval
      (.stmts ([] : List (Stmt P CmdT)) ρ₀) (.terminal ρ₀) :=
    .step _ _ _ .step_stmts_nil (.refl _)
  have h_block : StepStmtStar P evalCmd extendEval
      (.block .none ρ₀.store ρ₀.eval (.stmts ([] : List (Stmt P CmdT)) ρ₀))
      (.terminal { ρ₀ with store := projectStore ρ₀.store ρ₀.store, eval := ρ₀.eval }) :=
    ReflTrans_Transitive _ _ _ _
      (block_inner_star P evalCmd extendEval _ _ .none ρ₀.store ρ₀.eval h_inner)
      (.step _ _ _ .step_block_done (.refl _))
  rw [projectStore_self_env] at h_block
  have henv : ({ ρ₀ with store := ρ₀.store, eval := ρ₀.eval } : Env P) = ρ₀ := by cases ρ₀; rfl
  rw [henv] at h_block
  exact .step _ _ _ .step_ite_nondet_false h_block

omit [HasFvar P] [HasVal P] [HasOps P] in
/-- An exiting execution of the block body whose label does NOT match the
    block's label lifts to an exiting execution of the enclosing block. -/
theorem block_wrap_exiting_mismatch
    (l : String) (bss : List (Stmt P CmdT)) (md : MetaData P)
    (lv : String) (ρ₀ ρ' : Env P)
    (hne : lv ≠ l)
    (h : StepStmtStar P evalCmd extendEval (.stmts bss ρ₀) (.exiting lv ρ')) :
    StepStmtStar P evalCmd extendEval (.stmt (.block l bss md) ρ₀)
      (.exiting lv { ρ' with store := projectStore ρ₀.store ρ'.store, eval := ρ₀.eval }) :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter P evalCmd extendEval l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star P evalCmd extendEval _ _ (some l) ρ₀.store ρ₀.eval h)
      (.step _ _ _ (.step_block_exit_mismatch (fun h => hne (Option.some.inj h).symm)) (.refl _)))

omit [HasFvar P] [HasVal P] [HasOps P] in
/-- An exiting execution of the block body whose label matches the
    block's label lifts to a TERMINAL execution of the enclosing block. -/
theorem block_wrap_exiting_match
    (l : String) (bss : List (Stmt P CmdT)) (md : MetaData P)
    (ρ₀ ρ' : Env P)
    (h : StepStmtStar P evalCmd extendEval (.stmts bss ρ₀) (.exiting l ρ')) :
    StepStmtStar P evalCmd extendEval (.stmt (.block l bss md) ρ₀)
      (.terminal { ρ' with store := projectStore ρ₀.store ρ'.store, eval := ρ₀.eval }) :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter P evalCmd extendEval l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star P evalCmd extendEval _ _ (some l) ρ₀.store ρ₀.eval h)
      (.step _ _ _ (.step_block_exit_match rfl) (.refl _)))

omit [HasFvar P] [HasVal P] [HasOps P] in
/-- Refined inversion of `.block` reaching `.terminal`: the inner config either
    terminates or exits with the matching label, and the final env is the parent
    projection of that inner env. -/
theorem block_reaches_terminal_refined
    {inner : Config P CmdT} {l : String} {σ_parent : SemanticStore P}
    {e_parent : SemanticEval P} {ρ' : Env P}
    (hstar : StepStmtStar P evalCmd extendEval
      (.block (some l) σ_parent e_parent inner) (.terminal ρ')) :
    ∃ ρ_inner, (StepStmtStar P evalCmd extendEval inner (.terminal ρ_inner) ∨
      StepStmtStar P evalCmd extendEval inner (.exiting l ρ_inner)) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } := by
  suffices ∀ src tgt, StepStmtStar P evalCmd extendEval src tgt →
      ∀ inner σ_parent e_parent ρ',
        src = .block (some l) σ_parent e_parent inner → tgt = .terminal ρ' →
      ∃ ρ_inner, (StepStmtStar P evalCmd extendEval inner (.terminal ρ_inner) ∨
        StepStmtStar P evalCmd extendEval inner (.exiting l ρ_inner)) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } from
    this _ _ hstar _ _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner σ_parent e_parent ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      obtain ⟨ρ_inner, hinner, heq⟩ := ih _ _ _ _ rfl htgt
      exact ⟨ρ_inner, hinner.elim
        (fun hterm => .inl (.step _ _ _ h hterm))
        (fun hexit_match => .inr (.step _ _ _ h hexit_match)), heq⟩
    | step_block_done =>
      subst htgt; cases hrest with
      | refl => exact ⟨_, .inl (.refl _), rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_match heq =>
      subst htgt; cases heq; cases hrest with
      | refl => exact ⟨_, .inr (.refl _), rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

omit [HasFvar P] [HasVal P] [HasOps P] in
/-- Refined inversion of `.block` reaching `.exiting`: the inner config exits
    with the SAME label (forced different from the block's label), and the
    final env is the parent projection of that inner env. -/
theorem block_reaches_exiting_refined
    {inner : Config P CmdT} {l : String} {σ_parent : SemanticStore P}
    {e_parent : SemanticEval P} {lbl : String} {ρ' : Env P}
    (hstar : StepStmtStar P evalCmd extendEval
      (.block (some l) σ_parent e_parent inner) (.exiting lbl ρ')) :
    ∃ ρ_inner, lbl ≠ l ∧
      StepStmtStar P evalCmd extendEval inner (.exiting lbl ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } := by
  suffices ∀ src tgt, StepStmtStar P evalCmd extendEval src tgt →
      ∀ inner σ_parent e_parent lbl ρ',
        src = .block (some l) σ_parent e_parent inner → tgt = .exiting lbl ρ' →
      ∃ ρ_inner, lbl ≠ l ∧
        StepStmtStar P evalCmd extendEval inner (.exiting lbl ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store, eval := e_parent } from
    this _ _ hstar _ _ _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner σ_parent e_parent lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      obtain ⟨ρ_inner, hne, hexit, hproj⟩ := ih _ _ _ _ _ rfl htgt
      exact ⟨ρ_inner, hne, .step _ _ _ h hexit, hproj⟩
    | step_block_done =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_mismatch hne =>
      subst htgt
      cases hrest with
      | refl => exact ⟨_, fun heq => hne (congrArg Option.some heq.symm), .refl _, rfl⟩
      | step _ _ _ h _ => cases h

omit [HasFvar P] [HasVal P] [HasOps P] in
/-- A head statement that exits causes the cons list to exit with the same label. -/
theorem stmts_cons_exiting
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (lbl : String)
    (ρ₀ ρ' : Env P)
    (h : StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.exiting lbl ρ')) :
    StepStmtStar P evalCmd extendEval (.stmts (s :: ss) ρ₀) (.exiting lbl ρ') :=
  ReflTrans_Transitive _ _ _ _
    (.step _ _ _ .step_stmts_cons (.refl _))
    (ReflTrans_Transitive _ _ _ _
      (seq_inner_star P evalCmd extendEval _ _ ss h)
      (.step _ _ _ .step_seq_exit (.refl _)))

omit [HasOps P] in
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

omit [HasFvar P] [HasVal P] [HasOps P] in
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

omit [HasOps P] in
/-- A failing block body lifts to a failing block statement. -/
theorem canFailBlock_to_canFail_block
    (l : String) (bss : List (Stmt P CmdT)) (md : MetaData P) (ρ₀ : Env P)
    (h : CanFailBlock evalCmd extendEval bss ρ₀) :
    CanFail (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) (.block l bss md) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  exact ⟨.block (.some l) ρ₀.store ρ₀.eval cfg,
    by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
    ReflTrans_Transitive _ _ _ _
      (step_block_enter P evalCmd extendEval l bss md ρ₀)
      (block_inner_star P evalCmd extendEval _ _ (.some l) ρ₀.store ρ₀.eval hreach)⟩

omit [HasFvar P] [HasVal P] [HasOps P] in
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

omit [HasFvar P] [HasVal P] [HasOps P] in
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
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T params₁ params₂)
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
      hsem s s' hs trivial ρ₀ ⟨hwfb, hwfv, hwfvar⟩
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
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn).InitEnvWFParamsTy)
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T params₁ params₂) :
    OverapproximatesAggressively
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (fun ss => ss.mapM T) params₁ params₂ := by
  intro ss ss' hmap _ ρ₀ hwf
  obtain ⟨hwfb, hwfv, hwfvar⟩ := hwf
  refine ⟨fun ρ' hstar => ?_, fun lbl ρ' hstar => ?_, ?_, ⟨hwfb, hwfv, hwfvar⟩⟩
  · exact (overapproximatesAggressively_stmts_aux evalCmd extendEval isAtAssertFn hwf_ext T params₁ params₂
      hsem ss ss' hmap ρ₀ ρ' hwfb hwfv hwfvar).1 hstar
  · exact (overapproximatesAggressively_stmts_aux evalCmd extendEval isAtAssertFn hwf_ext T params₁ params₂
      hsem ss ss' hmap ρ₀ ρ' hwfb hwfv hwfvar).2 lbl hstar
  · exact overapproximatesAggressively_stmts_canfail evalCmd extendEval isAtAssertFn hwf_ext T
      params₁ params₂ hsem ss ss' hmap ρ₀ hwfb hwfv hwfvar

end ImperativeStmts

end Transform
end Specification
end Imperative

end -- public section
