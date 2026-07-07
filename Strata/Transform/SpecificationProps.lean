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

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P]
    [HasInt P] [HasIntOps P]
variable (L : Lang P)



namespace Hoare

/-! ## Parametric Hoare rules -/

omit [HasOps P] [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] in
/-- False precondition proves anything -/
theorem false_pre (params : L.InitEnvWFParamsTy) (s : L.StmtT) (Post : Env P → Prop) :
    Triple L params (fun _ => False) s Post := by
  intro _ _ hpre; exact absurd hpre id

omit [HasOps P] [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] in
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

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendFactory : ExtendFactory P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

omit [HasOps P] in
/-- Empty statement list is skip. -/
theorem skip_block (Pre : Env P → Prop) :
    TripleBlock evalCmd extendFactory Pre [] Pre := by
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
theorem cmd (params : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (c : CmdT) (Pre Post : Env P → Prop)
    (h : ∀ ρ₀ σ' f, Pre ρ₀ → WellFormedSemanticEvalBool (P := P) ρ₀.factory →
      evalCmd ρ₀.factory ρ₀.store c σ' f →
      Post { ρ₀ with store := σ', hasFailure := f } ∧ f = false) :
    Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) params Pre (.cmd c) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_cmd hcmd =>
      cases r1 with
      | refl =>
        have ⟨hp, hfeq⟩ := h ρ₀ _ _ hpre hinit.bool hcmd
        simp [hf₀] at hp ⊢; exact ⟨hp, hfeq⟩
      | step _ _ _ h _ => exact nomatch h

/-- Sequential cons. -/
theorem seq_cons (params : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    {s : Stmt P CmdT} {ss : List (Stmt P CmdT)}
    {Pre Mid Post : Env P → Prop}
    (hwf_ext : WFFactoryExtension P extendFactory)
    (h₁ : Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) params Pre s Mid)
    (h₂ : TripleBlock evalCmd extendFactory Mid ss Post)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock evalCmd extendFactory Pre (s :: ss) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  -- `WellFormedSemanticEval`'s conditions only mention `ρ.factory`, and
  -- `WFFactoryExtension` guarantees each is preserved along `s`'s execution
  -- (even through funcDecls).
  have hinit_preserved : ∀ ρ₁, StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
      WellFormedSemanticEval (P := P) ρ₁.factory := by
    intro ρ₁ hterm
    exact star_preserves_wfEval P evalCmd extendFactory hwf_ext hterm hinit
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_ss⟩ := seq_reaches_terminal P evalCmd extendFactory hrest
        have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hinit hf₀ hterm_s
        exact h₂ ρ₁ ρ' hmid (hinit_preserved ρ₁ hterm_s) hf₁ (.inl hrest_ss)
  | .inr ⟨lbl, hexit⟩ =>
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P evalCmd extendFactory hrest with
        | .inl hexit_inner =>
          exact absurd hexit_inner
            (exitsCoveredByBlocks_noEscape P evalCmd extendFactory s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
          have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hinit hf₀ hterm_s
          exact h₂ ρ₁ ρ' hmid (hinit_preserved ρ₁ hterm_s) hf₁ (.inr ⟨lbl, hexit_ss⟩)

omit [HasOps P] in
/-- Lift a `TripleBlock` to a `Triple` by wrapping in a block.
    The postcondition `Post` is required to be stable under `projectStore`
    (it only references variables defined before the block). -/
theorem TripleBlock.toTriple
    (params : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h : TripleBlock evalCmd extendFactory Pre ss Post)
    (hpost_proj : PostWF extendFactory Post) :
    Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) params Pre (.block l ss md) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  cases hstar with
  | step _ _ _ hstep hrest => cases hstep with
    | step_block =>
      -- At block entry the inner is `.stmts ss ρ₀` whose eval is `ρ₀.eval`,
      -- which is exactly `e_parent`.  So `evalExtendsOf ρ₀.eval inner` is
      -- reflexive, and `star_preserves_factoryExtendsOf` lifts the inner trace.
      have hinv₀ : Config.factoryExtendsOf P extendFactory ρ₀.factory (.stmts ss ρ₀) := by
        simp only [Config.factoryExtendsOf]; exact .refl
      match block_reaches_terminal P evalCmd extendFactory hrest with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := h ρ₀ ρ_inner hpre hinit hf₀ (.inl hterm)
        have hext : FactoryExtensionOf extendFactory ρ₀.factory ρ_inner.factory :=
          star_preserves_factoryExtendsOf P evalCmd extendFactory hinv₀ hterm
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := h ρ₀ ρ_inner hpre hinit hf₀ (.inr ⟨lbl, hexit⟩)
        have hext : FactoryExtensionOf extendFactory ρ₀.factory ρ_inner.factory :=
          star_preserves_factoryExtendsOf P evalCmd extendFactory hinv₀ hexit
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf

omit [HasOps P] in
/-- Lift a `Triple` to a `TripleBlock` for a singleton list. -/
theorem Triple.toTripleBlock
    (params : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    {s : Stmt P CmdT}
    {Pre Post : Env P → Prop}
    (h : Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) params Pre s Post)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock evalCmd extendFactory Pre [s] Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_nil⟩ := seq_reaches_terminal P evalCmd extendFactory hrest
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
        match seq_reaches_exiting P evalCmd extendFactory hrest with
        | .inl hexit_s =>
          exact absurd hexit_s
            (exitsCoveredByBlocks_noEscape P evalCmd extendFactory s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_nil⟩ =>
          cases hexit_nil with
          | step _ _ _ h _ => cases h with
            | step_stmts_nil => rename_i r; cases r with | step _ _ _ h _ => cases h

omit [HasOps P] in
/-- Empty block is skip. -/
theorem skip (params : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (l : String) (md : MetaData P) (Pre : Env P → Prop)
    (hpre_proj : PostWF extendFactory Pre) :
    Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) params Pre (.block l [] md) Pre :=
  TripleBlock.toTriple evalCmd extendFactory isAtAssertFn params (skip_block evalCmd extendFactory Pre) hpre_proj

omit [HasOps P] in
/-- If-then-else rule. -/
theorem ite (params : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    {c : P.Expr} {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (ht : TripleBlock evalCmd extendFactory (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store c = some HasBool.tt) tss Post)
    (he : TripleBlock evalCmd extendFactory (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store c = some HasBool.ff) ess Post)
    (hpost_proj : PostWF extendFactory Post) :
    Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) params Pre (.ite (.det c) tss ess md) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_ite_true hc _ =>
      have hinv₀ : Config.factoryExtendsOf P extendFactory ρ₀.factory (.stmts tss ρ₀) := by
        simp only [Config.factoryExtendsOf]; exact .refl
      match block_reaches_terminal P evalCmd extendFactory r1 with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := ht ρ₀ ρ_inner ⟨hpre, hc⟩ hinit hf₀ (.inl hterm)
        have hext := star_preserves_factoryExtendsOf P evalCmd extendFactory hinv₀ hterm
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := ht ρ₀ ρ_inner ⟨hpre, hc⟩ hinit hf₀ (.inr ⟨lbl, hexit⟩)
        have hext := star_preserves_factoryExtendsOf P evalCmd extendFactory hinv₀ hexit
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf
    | step_ite_false hc _ =>
      have hinv₀ : Config.factoryExtendsOf P extendFactory ρ₀.factory (.stmts ess ρ₀) := by
        simp only [Config.factoryExtendsOf]; exact .refl
      match block_reaches_terminal P evalCmd extendFactory r1 with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := he ρ₀ ρ_inner ⟨hpre, hc⟩ hinit hf₀ (.inl hterm)
        have hext := star_preserves_factoryExtendsOf P evalCmd extendFactory hinv₀ hterm
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := he ρ₀ ρ_inner ⟨hpre, hc⟩ hinit hf₀ (.inr ⟨lbl, hexit⟩)
        have hext := star_preserves_factoryExtendsOf P evalCmd extendFactory hinv₀ hexit
        subst heq; exact hpost_proj ρ_inner _ _ hext hpost hf

/- TODO: the WHILE rule -/

end StmtRules


/-! ## Connection between HoareTriple and AssertValid (standard Lang) -/

section StandardConnection

variable (P' : PureExpr) [HasFvar P'] [HasFvars P'] [HasOps P'] [HasBool P'] [HasBoolOps P']
    [HasInt P'] [HasIntOps P']
variable (extendFactory : ExtendFactory P')

omit [HasOps P'] in
/-- **Direction 1**: Hoare triple implies assert validity for `PredicatedStmt`. -/
theorem hoareTriple_implies_assertValid (params : (Lang.standard P' extendFactory).InitEnvWFParamsTy)
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hoare : Triple (Lang.standard P' extendFactory) params
      (fun ρ => P'.eval ρ.factory ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => P'.eval ρ.factory ρ.store post_expr = some HasBool.tt))
    (hno : st.noMatchingAssert post_label) :
    AssertValidWhen (Lang.standard P' extendFactory)
      (fun ρ => WellFormedSemanticEval (P := P') ρ.factory)
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩ := by
  intro ρ₀ cfg hwhen hreach hat
  have hno_match := noMatchingAssert_implies_no_reachable_assert P' extendFactory st post_label post_expr hno
  unfold PredicatedStmt at hreach
  cases hreach with
  | refl => exact absurd hat (by simp [isAtAssert])
  | step _ _ _ hstep hrest =>
    cases hstep with
    | step_block =>
      have ⟨inner, heq_cfg, hinner_star, hat_inner⟩ :=
        block_isAtAssert_inner P' extendFactory _ _ _ _ _ _ hrest hat
      subst heq_cfg
      cases hinner_star with
      | refl => exact absurd hat_inner (by simp [isAtAssert])
      | step _ _ _ hstep2 hrest2 =>
        cases hstep2 with
        | step_stmts_cons =>
          match seq_isAtAssert_cases P' extendFactory _ _ _ _ hrest2 hat_inner with
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
                match seq_isAtAssert_cases P' extendFactory _ _ _ _ hrest3 hat_stmts with
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
                            smallStep_hasFailure_irrel P' (EvalCmd P') extendFactory
                              st _ ρ' hterm_st { ρ₀ with hasFailure := false } rfl rfl
                          have ⟨hpost, _⟩ := hoare { ρ₀ with hasFailure := false } ρ'_clean
                            hpre hwhen rfl hterm_clean
                          simp only [hs_eq, he_eq] at hpost
                          have ⟨hs, he⟩ := assert_tail_getStore P' extendFactory
                            ρ' post_label post_expr post_md inner ⟨post_label, post_expr⟩
                            hrest_assert hat_inner
                          dsimp [Config.getStore, Config.getEnv] at he hs ⊢
                          rw [he, hs]; exact hpost
                        | step _ _ _ h _ => exact absurd h (by intro h; cases h)


omit [HasOps P'] in
/-- **Direction 2**: Assert validity for `PredicatedStmt` implies Hoare triple. -/
theorem allAssertsValid_implies_hoareTriple
    (params : (Lang.standard P' extendFactory).InitEnvWFParamsTy)
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hvalid : AllAssertsValid (Lang.standard P' extendFactory)
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)) :
    Triple (Lang.standard P' extendFactory) params
      (fun ρ => P'.eval ρ.factory ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => P'.eval ρ.factory ρ.store post_expr = some HasBool.tt) := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  have hwfb := hinit.bool
  let assume_stmt : Stmt P' (Cmd P') := .cmd (.assume pre_label pre_expr pre_md)
  let assert_stmt : Stmt P' (Cmd P') := .cmd (.assert post_label post_expr post_md)
  let body : List (Stmt P' (Cmd P')) := [assume_stmt, st, assert_stmt]
  have hvalid_st : ∀ (a : AssertId P') (cfg : Config P' (Cmd P')),
      StepStmtStar P' (EvalCmd P') extendFactory (.stmt st ρ₀) cfg →
      isAtAssert P' cfg a →
      P'.eval cfg.getEnv.factory cfg.getStore a.expr = some HasBool.tt := by
    intro a cfg hstar_st hat
    have h_assume : StepStmtStar P' (EvalCmd P') extendFactory
        (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
      .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
    have h_ρ₁_eq : ({ store := ρ₀.store, factory := ρ₀.factory, hasFailure := ρ₀.hasFailure || false } : Env P') = ρ₀ := by
      cases ρ₀; simp [Bool.or_false]
    have h1 := stmts_cons_step P' (EvalCmd P') extendFactory assume_stmt [st, assert_stmt] ρ₀ _ h_assume
    rw [h_ρ₁_eq] at h1
    have h2 : StepStmtStar P' (EvalCmd P') extendFactory
        (.stmts [st, assert_stmt] ρ₀) (.seq (.stmt st ρ₀) [assert_stmt]) :=
      .step _ _ _ StepStmt.step_stmts_cons (.refl _)
    have h3 := seq_inner_star P' (EvalCmd P') extendFactory _ _ [assert_stmt] hstar_st
    have h_inner := ReflTrans_Transitive _ _ _ _ (ReflTrans_Transitive _ _ _ _ h1 h2) h3
    have h_block := block_inner_star P' (EvalCmd P') extendFactory _ _ (.some block_label) ρ₀.store ρ₀.factory h_inner
    have h_start : StepStmtStar P' (EvalCmd P') extendFactory
        (.stmt (.block block_label body block_md) ρ₀)
        (.block (.some block_label) ρ₀.store ρ₀.factory (.stmts body ρ₀)) :=
      .step _ _ _ StepStmt.step_block (.refl _)
    have h_full := ReflTrans_Transitive _ _ _ _ h_start h_block
    have h_result := hvalid a ρ₀ _ trivial h_full hat
    dsimp [Config.getStore, Config.getEnv] at h_result ⊢
    exact h_result
  have h_assume : StepStmtStar P' (EvalCmd P') extendFactory
      (.stmt assume_stmt ρ₀) (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb)) (.refl _)
  have h_ρ₁_eq : ({ store := ρ₀.store, factory := ρ₀.factory, hasFailure := ρ₀.hasFailure || false } : Env P') = ρ₀ := by
    cases ρ₀; simp [Bool.or_false]
  have h1 := stmts_cons_step P' (EvalCmd P') extendFactory assume_stmt [st, assert_stmt] ρ₀ _ h_assume
  rw [h_ρ₁_eq] at h1
  have h2 := stmts_cons_step P' (EvalCmd P') extendFactory st [assert_stmt] ρ₀ ρ' hstar
  have h3 : StepStmtStar P' (EvalCmd P') extendFactory
      (.stmts [assert_stmt] ρ') (.seq (.stmt assert_stmt ρ') []) :=
    .step _ _ _ StepStmt.step_stmts_cons (.refl _)
  have h_inner := ReflTrans_Transitive _ _ _ _ (ReflTrans_Transitive _ _ _ _ h1 h2) h3
  have h_block := block_inner_star P' (EvalCmd P') extendFactory _ _ (.some block_label) ρ₀.store ρ₀.factory h_inner
  have h_start : StepStmtStar P' (EvalCmd P') extendFactory
      (.stmt (.block block_label body block_md) ρ₀)
      (.block (.some block_label) ρ₀.store ρ₀.factory (.stmts body ρ₀)) :=
    .step _ _ _ StepStmt.step_block (.refl _)
  have h_full := ReflTrans_Transitive _ _ _ _ h_start h_block
  have h_at : isAtAssert P' (.block (.some block_label) ρ₀.store ρ₀.factory (.seq (.stmt assert_stmt ρ') [])) ⟨post_label, post_expr⟩ := by
    simp [isAtAssert, assert_stmt]
  have h_result := hvalid ⟨post_label, post_expr⟩ ρ₀ _ trivial h_full h_at
  dsimp [Config.getStore, Config.getEnv] at h_result
  exact ⟨h_result, allAssertsValid_preserves_noFailure P' extendFactory
    (ρ₀ := ρ₀) (ρ' := ρ') st hvalid_st hf₀ hstar⟩

end StandardConnection

end Hoare


namespace Transform

/-! ## Connection between Sound, AssertValid and AllAssertsValid -/

omit [HasOps P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] in
theorem sound_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (h₁ : Sound L₁ L₂ T₁) (h₂ : Sound L₂ L₃ T₂) :
    Sound L₁ L₃ (fun s => T₁ s >>= T₂) := by
  intro s s'' a hrun hvalid
  simp [bind, Option.bind] at hrun
  match h1 : T₁ s with
  | some s' => rw [h1] at hrun; exact h₁ s s' a h1 (h₂ s' s'' a hrun hvalid)
  | none => rw [h1] at hrun; exact absurd hrun (by nofun)

omit [HasOps P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] in
theorem sound_assertValid (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (a : AssertId P)
    (s : L₁.StmtT) (s' : L₂.StmtT)
    (ht : T s = some s') (hsound : Sound L₁ L₂ T) (hvalid : AssertValid L₂ s' a) :
    AssertValid L₁ s a := hsound s s' a ht hvalid

omit [HasOps P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] in
theorem sound_allAsserts (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (s : L₁.StmtT) (s' : L₂.StmtT) (ht : T s = some s')
    (hsound : Sound L₁ L₂ T) (hvalid : AllAssertsValid L₂ s') :
    AllAssertsValid L₁ s := fun a => hsound s s' a ht (hvalid a)

omit [HasOps P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] in
theorem sound_id : Sound L L some := by
  intro s s' a ht hvalid; simp at ht; subst ht; exact hvalid

/-! ## Connection between `Overapproximates` and `Hoare.Triple` -/

omit [HasOps P] [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- If `T` overapproximates and a Hoare triple holds on `T(st)` in L₂,
    then the triple holds on `st` in L₁. -/
theorem overapproximates_triple (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : Overapproximates L₁ L₂ T params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Hoare.Triple L₂ params₂ Pre s' Post) :
    Hoare.Triple L₁ params₁ Pre st Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  have hr := hsem st s' ht ρ₀ hinit
  exact htriple ρ₀ ρ' hpre hr.2 hf₀ ((hr.1 ρ').1 hstar)

omit [HasOps P] [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
theorem overapproximates_id (L₁ : Lang P) (params₁ : L₁.InitEnvWFParamsTy) :
    Overapproximates L₁ L₁ some params₁ params₁ := by
  intro st s' ht ρ₀ hinit
  simp at ht; subst ht
  exact ⟨fun _ => ⟨id, fun _ => id⟩, hinit⟩

omit [HasOps P] [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P] in
/-- Composition of two overapproximations: the intermediate WF passed to `h₂`
    is exactly the target-WF conclusion of `h₁`, so no extra bridging
    hypothesis is needed. -/
theorem overapproximates_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : Overapproximates L₁ L₂ T₁ params₁ params₂)
    (h₂ : Overapproximates L₂ L₃ T₂ params₂ params₃) :
    Overapproximates L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  intro st s'' ht ρ₀ hinit
  simp [bind, Option.bind] at ht
  match h : T₁ st with
  | some s' =>
    rw [h] at ht
    have hr₁ := h₁ st s' h ρ₀ hinit
    have hr₂ := h₂ s' s'' ht ρ₀ hr₁.2
    refine ⟨fun ρ' => ?_, hr₂.2⟩
    refine ⟨?_, ?_⟩
    · intro hstar; exact (hr₂.1 ρ').1 ((hr₁.1 ρ').1 hstar)
    · intro lbl hstar; exact (hr₂.1 ρ').2 lbl ((hr₁.1 ρ').2 lbl hstar)
  | none => rw [h] at ht; exact absurd ht (by nofun)

/-! ## Statement-list overapproximation (Imperative-specific)

Uses `Overapproximates L L T` (single-language): the proof decomposes
seq execution into terminal/exiting outcomes of individual statements,
which is exactly what `Overapproximates` provides. -/

section ImperativeStmts

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendFactory : ExtendFactory P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

omit [HasFvar P] [HasOps P] [HasBool P] [HasBoolOps P] [HasFvars P] in
private theorem mapM_noFuncDecl
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hnofd_T : ∀ s s', T s = some s' → Stmt.noFuncDecl s = true)
    (ss : List (Stmt P CmdT)) (ss' : List (Stmt P CmdT))
    (hmap : ss.mapM T = some ss') :
    Block.noFuncDecl ss = true := by
  induction ss generalizing ss' with
  | nil => simp [Block.noFuncDecl]
  | cons s rest ih =>
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    simp [Block.noFuncDecl, hnofd_T s s' hs, ih rest' hrm]

omit [HasOps P] in
private theorem overapproximates_stmts_aux
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) T params₁ params₂)
    (ss : List (Stmt P CmdT))
    (hnofd : Block.noFuncDecl ss = true) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEval (P := P) ρ₀.factory →
        (StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.terminal ρ') →
         StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) (.terminal ρ'))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.exiting lbl ρ') →
                StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) (.exiting lbl ρ')) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ' _
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this; exact ⟨id, fun _ => id⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ' hwf
    simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd
    have ⟨hnofd_s, hnofd_rest⟩ := hnofd
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have wf_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
        WellFormedSemanticEval (P := P) ρ₁.factory := by
      intro ρ₁ hterm_s
      have hfac := stmt_noFuncDecl_preserves_factory P evalCmd extendFactory s ρ₀ ρ₁ hnofd_s hterm_s
      exact hfac ▸ hwf
    -- `Lang.imperative`'s `initEnvWF` unfolds to `WellFormedSemanticEval ρ.factory`,
    -- so `hwf` directly satisfies the source-side WF gate of `hsem`.
    have hsem_s : ∀ (ρ₁ : Env P),
        (StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
         StepStmtStar P evalCmd extendFactory (.stmt s' ρ₀) (.terminal ρ₁))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.exiting lbl ρ₁) →
                StepStmtStar P evalCmd extendFactory (.stmt s' ρ₀) (.exiting lbl ρ₁)) := by
      intro ρ₁
      exact (hsem s s' hs ρ₀ hwf).1 ρ₁
    constructor
    · intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendFactory hrest_exec
          have hwf₁ := wf_preserved ρ₁ hterm_s
          exact ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁
              ((hsem_s ρ₁).1 hterm_s))
            ((ih hnofd_rest rest' hrm ρ₁ ρ' hwf₁).1 hterm_rest)
    · intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendFactory hrest_exec with
          | .inl hexit_s =>
            exact .step _ _ _ .step_stmts_cons
              (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendFactory _ _ rest'
                ((hsem_s ρ').2 lbl hexit_s))
                (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have hwf₁ := wf_preserved ρ₁ hterm_s
            exact ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁
                ((hsem_s ρ₁).1 hterm_s))
              ((ih hnofd_rest rest' hrm ρ₁ ρ' hwf₁).2 lbl hexit_rest)

omit [HasOps P] in
theorem overapproximates_stmts
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) T params₁ params₂)
    (hnofd_T : ∀ s s', T s = some s' → Stmt.noFuncDecl s = true) :
    Overapproximates
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn)
      (fun ss => ss.mapM T) () () := by
  intro ss ss' hmap ρ₀ hwf
  refine ⟨fun ρ' => overapproximates_stmts_aux evalCmd extendFactory isAtAssertFn T
    params₁ params₂ hsem ss
    (mapM_noFuncDecl T hnofd_T ss ss' hmap) ss' hmap ρ₀ ρ' hwf, hwf⟩

end ImperativeStmts

end Transform
end Specification
end Imperative

end -- public section
