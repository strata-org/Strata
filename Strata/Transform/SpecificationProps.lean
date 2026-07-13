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

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasOps P] [HasBool P] [HasBoolOps P] [HasSubstFvar P]
    [HasInt P] [HasIntOps P]
variable (L : Lang P)



namespace Hoare

/-! ## Parametric Hoare rules -/

section

omit [HasOps P] [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasSubstFvar P]

/-- False precondition proves anything -/
theorem false_pre (params : L.InitEnvWFParamsTy) (s : L.StmtT) (Post : Env P → Prop) :
    Triple L params (fun _ => False) s Post := by
  intro _ _ hpre; exact absurd hpre id

/-- Consequence (weakening): strengthen precondition, weaken postconditions. -/
theorem consequence (params : L.InitEnvWFParamsTy)
    {Pre Pre' : Env P → Prop} {Post Post' : Env P → Prop} {s : L.StmtT}
    (h : Triple L params Pre s Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple L params Pre' s Post' := by
  intro ρ₀ ρ' hpre' hinit hf₀ hstar
  have ⟨hp, hf⟩ := h ρ₀ ρ' (hpre ρ₀ hpre') hinit hf₀ hstar
  exact ⟨hpost ρ' hp, hf⟩

end

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

variable (P' : PureExpr) [HasFvar P'] [HasFvars P'] [HasOps P'] [HasBool P'] [HasBoolOps P'] [HasSubstFvar P']
    [HasInt P'] [HasIntOps P']
variable (extendFactory : ExtendFactory P')

omit [HasOps P']

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

section Connection
omit [HasOps P] [HasBoolOps P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasSubstFvar P]

theorem sound_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : Sound L₁ L₂ T₁ params₁ params₂) (h₂ : Sound L₂ L₃ T₂ params₂ params₃) :
    Sound L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  intro s s'' a hrun hvalid
  simp [bind, Option.bind] at hrun
  match h1 : T₁ s with
  | some s' => rw [h1] at hrun; exact h₁ s s' a h1 (h₂ s' s'' a hrun hvalid)
  | none => rw [h1] at hrun; exact absurd hrun (by nofun)

theorem sound_assertValid (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (a : AssertId P)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (s : L₁.StmtT) (s' : L₂.StmtT)
    (ht : T s = some s') (hsound : Sound L₁ L₂ T params₁ params₂)
    (hvalid : AssertValidWhen L₂ (L₂.initEnvWF params₂ s') s' a) :
    AssertValidWhen L₁ (L₁.initEnvWF params₁ s) s a := hsound s s' a ht hvalid

theorem sound_allAsserts (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (s : L₁.StmtT) (s' : L₂.StmtT) (ht : T s = some s')
    (hsound : Sound L₁ L₂ T params₁ params₂)
    (hvalid : AllAssertsValidWhen L₂ (L₂.initEnvWF params₂ s') s') :
    AllAssertsValidWhen L₁ (L₁.initEnvWF params₁ s) s := fun a => hsound s s' a ht (hvalid a)

theorem sound_id (params : L.InitEnvWFParamsTy) : Sound L L some params params := by
  intro s s' a ht hvalid; simp at ht; subst ht; exact hvalid

end Connection


/-! ## Connection between the `Overapproximates` family and `Hoare.Triple` -/

section OverapproxHoareConnection
omit [HasOps P] [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P]

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
  have hr := hsem st s' ht trivial ρ₀ ρ₀ rfl hinit
  exact htriple ρ₀ ρ' hpre hr.2.2 hf₀ (by obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').1 hstar; subst heq; exact hstar')

/-- Hoare-triple corollary for `OverapproximatesWhen`: if `T` overapproximates
    when `pre` holds and `pre st` is satisfied, then a Hoare triple on `T(st)`
    in `L₂` lifts to a Hoare triple on `st` in `L₁`.

    This generalizes `overapproximates_triple` to a nontrivial precondition
    (recover the latter with `pre := fun _ => True` and `hsource_pre := trivial`).
    Well-formedness of the source initial env is supplied by `L₁`'s own triple
    gate (`hinit`), so no separate WF-bridging hypothesis is needed. -/
theorem overapproximatesWhen_triple (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesWhen L₁ L₂ T pre params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Hoare.Triple L₂ params₂ Pre s' Post)
    (hsource_pre : pre st) :
    Hoare.Triple L₁ params₁ Pre st Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  have hr := hsem st s' ht hsource_pre ρ₀ ρ₀ rfl hinit
  exact htriple ρ₀ ρ' hpre hr.2.2 hf₀
    (by obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').1 hstar; subst heq; exact hstar')

end OverapproxHoareConnection


/-! ## Properties of the `Overapproximates` family. -/

section OverapproxProps
omit [HasOps P] [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasInt P] [HasIntOps P] [HasSubstFvar P]

theorem overapproximates_id (L₁ : Lang P) (params₁ : L₁.InitEnvWFParamsTy) :
    Overapproximates L₁ L₁ some params₁ params₁ := by
  intro st s' ht _ ρ₀ ρ₀' heq hinit
  simp at ht; subst ht; subst heq
  exact ⟨fun ρ' => ⟨fun h => ⟨ρ', rfl, h⟩, fun _ h => ⟨ρ', rfl, h⟩⟩, fun h => h, hinit⟩

/-- Composition of two overapproximations under relation composition. -/
theorem overapproximatesUpto_comp (L₁ L₂ L₃ : Lang P)
    (R₁ R₂ : Relation (Env P))
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : OverapproximatesUpto R₁ L₁ L₂ T₁ params₁ params₂)
    (h₂ : OverapproximatesUpto R₂ L₂ L₃ T₂ params₂ params₃) :
    OverapproximatesUpto (RComp R₁ R₂) L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  intro st s'' ht _ ρ₀ ρ₀'' hR hinit
  obtain ⟨ρmid, hR₁mid, hR₂mid⟩ := hR
  simp [bind, Option.bind] at ht
  match h : T₁ st with
  | some s' =>
    rw [h] at ht
    have hr₁ := h₁ st s' h trivial ρ₀ ρmid hR₁mid hinit
    have hr₂ := h₂ s' s'' ht trivial ρmid ρ₀'' hR₂mid hr₁.2.2
    refine ⟨fun ρ' => ⟨?_, ?_⟩, ?_, hr₂.2.2⟩
    · intro hstar
      obtain ⟨ρ'm, hRm, hsm⟩ := (hr₁.1 ρ').1 hstar
      obtain ⟨ρ'', hR2, hs2⟩ := (hr₂.1 ρ'm).1 hsm
      exact ⟨ρ'', ⟨ρ'm, hRm, hR2⟩, hs2⟩
    · intro lbl hstar
      obtain ⟨ρ'm, hRm, hsm⟩ := (hr₁.1 ρ').2 lbl hstar
      obtain ⟨ρ'', hR2, hs2⟩ := (hr₂.1 ρ'm).2 lbl hsm
      exact ⟨ρ'', ⟨ρ'm, hRm, hR2⟩, hs2⟩
    · intro hfail; exact hr₂.2.1 (hr₁.2.1 hfail)
  | none => rw [h] at ht; exact absurd ht (by nofun)

/-- Composition of two overapproximations. -/
theorem overapproximates_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : Overapproximates L₁ L₂ T₁ params₁ params₂)
    (h₂ : Overapproximates L₂ L₃ T₂ params₂ params₃) :
    Overapproximates L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  have hcomp := overapproximatesUpto_comp L₁ L₂ L₃ (· = ·) (· = ·) T₁ T₂
    params₁ params₂ params₃ h₁ h₂
  intro st s'' ht _ ρ₀ ρ₀' heq hinit
  subst heq
  have hr := hcomp st s'' ht trivial ρ₀ ρ₀ ⟨ρ₀, rfl, rfl⟩ hinit
  refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩, hr.2.1, hr.2.2⟩
  · obtain ⟨ρ'', ⟨b, hb₁, hb₂⟩, hstar''⟩ := (hr.1 ρ').1 hstar
    exact ⟨ρ'', hb₁.trans hb₂, hstar''⟩
  · obtain ⟨ρ'', ⟨b, hb₁, hb₂⟩, hstar''⟩ := (hr.1 ρ').2 lbl hstar
    exact ⟨ρ'', hb₁.trans hb₂, hstar''⟩

/-- Composition of two aggressive overapproximations. -/
theorem overapproximatesAggressively_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (params₃ : L₃.InitEnvWFParamsTy)
    (h₁ : OverapproximatesAggressively L₁ L₂ T₁ params₁ params₂)
    (h₂ : OverapproximatesAggressively L₂ L₃ T₂ params₂ params₃) :
    OverapproximatesAggressively L₁ L₃ (fun s => T₁ s >>= T₂) params₁ params₃ := by
  intro st s'' ht _ ρ₀ hinit
  simp [bind, Option.bind] at ht
  match hT₁ : T₁ st with
  | some s' =>
    rw [hT₁] at ht
    have ha₁ := h₁ st s' hT₁ trivial ρ₀ hinit
    have ha₂ := h₂ s' s'' ht trivial ρ₀ ha₁.2.2.2
    refine ⟨?_, ?_, fun hcf => ha₂.2.2.1 (ha₁.2.2.1 hcf), ha₂.2.2.2⟩
    · -- Terminal case
      intro ρ' hstar
      match ha₁.1 ρ' hstar with
      | .inl hcf₂ => exact .inl (ha₂.2.2.1 hcf₂)
      | .inr hmid =>
        by_cases hf : ρ'.hasFailure = false
        · match ha₂.1 ρ' (hmid hf) with
          | .inl hcf₃ => exact .inl hcf₃
          | .inr hstep₃ => exact .inr (fun _ => hstep₃ hf)
        · exact .inr (fun hf' => absurd hf' hf)
    · -- Exiting case
      intro lbl ρ' hstar
      match ha₁.2.1 lbl ρ' hstar with
      | .inl hcf₂ => exact .inl (ha₂.2.2.1 hcf₂)
      | .inr hmid =>
        by_cases hf : ρ'.hasFailure = false
        · match ha₂.2.1 lbl ρ' (hmid hf) with
          | .inl hcf₃ => exact .inl hcf₃
          | .inr hstep₃ => exact .inr (fun _ => hstep₃ hf)
        · exact .inr (fun hf' => absurd hf' hf)
  | none => rw [hT₁] at ht; exact absurd ht (by nofun)

/-- `Underapproximates` identity: the identity transform under-approximates
    itself.  Dual of `overapproximates_id`. -/
theorem underapproximates_id (L₁ : Lang P) (params₁ : L₁.InitEnvWFParamsTy) :
    Underapproximates L₁ L₁ some params₁ params₁ := by
  intro st s' ht ρ₀ hinit
  simp at ht; subst ht
  exact ⟨fun ρ' => ⟨id, fun _ => id⟩, fun h => h, hinit⟩

/-- `SemanticallyEquivalent` identity: the identity transform is semantically
    equivalent to itself.  Follows from `overapproximates_id` and
    `underapproximates_id`. -/
theorem semanticallyEquivalent_id (L₁ : Lang P) (params₁ : L₁.InitEnvWFParamsTy) :
    SemanticallyEquivalent L₁ L₁ some params₁ params₁ :=
  ⟨overapproximates_id L₁ params₁, underapproximates_id L₁ params₁⟩


/-! ## Relating `Overapproximates`, `OverapproximatesWhen`, and their aggressive variants

The lemmas below organize the overapproximation family into a lattice of
implications:
- dropping the exactness requirement (`… → …Aggressively…`);
- strengthening the precondition (`strengthen`);
- specializing an unconditional relation to any precondition (`toWhen`);
and a Hoare-triple corollary generalizing `overapproximates_triple` to a
precondition. -/

/-- `OverapproximatesWhen` implies `OverapproximatesAggressivelyWhen` (same
    precondition).  An exact transform that handles all preconditioned inputs
    is also an aggressive transform that handles them: the exact target
    execution reaching `ρ'` witnesses the `hasFailure = false` disjunct. -/
theorem OverapproximatesWhen.toAggressivelyWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : OverapproximatesWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂ := by
  intro st s' ht hpre ρ₀ hswf
  have hr := h st s' ht hpre ρ₀ ρ₀ rfl hswf
  refine ⟨?_, ?_, hr.2.1, hr.2.2⟩
  · intro ρ' hstar
    exact .inr (fun _ => by
      obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').1 hstar; subst heq; exact hstar')
  · intro lbl ρ' hstar
    exact .inr (fun _ => by
      obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').2 lbl hstar; subst heq; exact hstar')

/-- `Overapproximates` implies `OverapproximatesAggressively`. -/
theorem Overapproximates.toAggressive (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : Overapproximates L₁ L₂ T params₁ params₂) :
    OverapproximatesAggressively L₁ L₂ T params₁ params₂ :=
  OverapproximatesWhen.toAggressivelyWhen L₁ L₂ T (fun _ => True) params₁ params₂ h

/-- Precondition strengthening for `OverapproximatesWhen`: a relation that holds
    under `pre` also holds under any stronger precondition `pre'`. -/
theorem OverapproximatesWhen.strengthen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) {pre pre' : L₁.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (himp : ∀ st, pre' st → pre st)
    (h : OverapproximatesWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesWhen L₁ L₂ T pre' params₁ params₂ := by
  intro st st' ht hpre' ρ₀ ρ₀' hR hswf
  exact h st st' ht (himp st hpre') ρ₀ ρ₀' hR hswf

/-- Precondition strengthening for `OverapproximatesAggressivelyWhen`. -/
theorem OverapproximatesAggressivelyWhen.strengthen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) {pre pre' : L₁.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (himp : ∀ st, pre' st → pre st)
    (h : OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre' params₁ params₂ := by
  intro st st' ht hpre' ρ₀ hswf
  exact h st st' ht (himp st hpre') ρ₀ hswf

/-- An unconditional `Overapproximates` is the strongest case: it gives
    `OverapproximatesWhen` for ANY precondition. -/
theorem Overapproximates.toWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : Overapproximates L₁ L₂ T params₁ params₂) :
    OverapproximatesWhen L₁ L₂ T pre params₁ params₂ :=
  OverapproximatesWhen.strengthen L₁ L₂ T params₁ params₂ (fun _ _ => trivial) h

/-- An unconditional `OverapproximatesAggressively` likewise gives
    `OverapproximatesAggressivelyWhen` for any precondition. -/
theorem OverapproximatesAggressively.toWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : OverapproximatesAggressively L₁ L₂ T params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂ :=
  OverapproximatesAggressivelyWhen.strengthen L₁ L₂ T params₁ params₂ (fun _ _ => trivial) h

end OverapproxProps


/-! ## Structured statements-specific results -/

section StructuredStmts

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendFactory : ExtendFactory P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

private theorem overapproximates_stmts_aux
    (hwf_ext : WFFactoryExtension P extendFactory)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) T params₁ params₂)
    (ss : List (Stmt P CmdT)) :
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
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have wf_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
        WellFormedSemanticEval (P := P) ρ₁.factory := by
      intro ρ₁ hterm_s
      exact star_preserves_wfEval P evalCmd extendFactory hwf_ext hterm_s hwf
    -- `Lang.imperative`'s `initEnvWF` unfolds to `WellFormedSemanticEval ρ.factory`,
    -- so `hwf` directly satisfies the source-side WF gate of `hsem`.
    have hsem_s : ∀ (ρ₁ : Env P),
        (StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
         StepStmtStar P evalCmd extendFactory (.stmt s' ρ₀) (.terminal ρ₁))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.exiting lbl ρ₁) →
                StepStmtStar P evalCmd extendFactory (.stmt s' ρ₀) (.exiting lbl ρ₁)) := by
      intro ρ₁
      have hr := (hsem s s' hs trivial ρ₀ ρ₀ rfl hwf).1 ρ₁
      exact ⟨fun h => by obtain ⟨ρ'', heq, hstar⟩ := hr.1 h; subst heq; exact hstar,
             fun lbl h => by obtain ⟨ρ'', heq, hstar⟩ := hr.2 lbl h; subst heq; exact hstar⟩
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
            ((ih rest' hrm ρ₁ ρ' hwf₁).1 hterm_rest)
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
              ((ih rest' hrm ρ₁ ρ' hwf₁).2 lbl hexit_rest)

private theorem overapproximates_stmts_canfail
    (hwf_ext : WFFactoryExtension P extendFactory)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) T params₁ params₂)
    (ss : List (Stmt P CmdT))
    (ss' : List (Stmt P CmdT))
    (hmap : ss.mapM T = some ss')
    (ρ₀ : Env P)
    (hwf : WellFormedSemanticEval (P := P) ρ₀.factory)
    (hcf : ∃ cfg : Config P CmdT, cfg.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) cfg) :
    ∃ cfg' : Config P CmdT, cfg'.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) cfg' := by
  induction ss generalizing ss' ρ₀ with
  | nil =>
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    exact ⟨cfg, hfcfg, hstar⟩
  | cons s rest ih =>
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    cases hstar with
    | refl =>
      -- cfg = .stmts (s :: rest) ρ₀, so cfg.getEnv = ρ₀, hasFailure = true
      exact ⟨.stmts (s' :: rest') ρ₀, hfcfg, .refl _⟩
    | step _ _ _ hstep hrest_exec => cases hstep with
      | step_stmts_cons =>
        match seq_canfail_prop hrest_exec hfcfg with
        | .inl ⟨cfg', hf', hstar'⟩ =>
          -- Failure happens in the first statement `s`.
          -- Use hsem's CanFail clause for statement `s`.
          have hsem_canfail := (hsem s s' hs trivial ρ₀ ρ₀ rfl hwf).2.1
          have ⟨cfg_t, hf_t, hstar_t⟩ := hsem_canfail ⟨cfg', hf', hstar'⟩
          exact ⟨.seq cfg_t rest', hf_t,
            .step _ _ _ .step_stmts_cons
              (seq_inner_star P evalCmd extendFactory _ cfg_t rest' hstar_t)⟩
        | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
          -- First statement terminates at ρ₁, failure is in the rest.
          have hwf₁ : WellFormedSemanticEval (P := P) ρ₁.factory :=
            star_preserves_wfEval P evalCmd extendFactory hwf_ext hterm_s hwf
          -- Get terminal simulation for s → s'
          have hsem_s := (hsem s s' hs trivial ρ₀ ρ₀ rfl hwf).1 ρ₁
          have ⟨ρ₁', heq₁, hterm_s'⟩ := hsem_s.1 hterm_s
          subst heq₁
          -- Recurse on the rest
          have ⟨cfg_rest, hf_rest, hstar_rest'⟩ :=
            ih rest' hrm ρ₁ hwf₁ ⟨cfg', hf', hstar_rest⟩
          exact ⟨cfg_rest, hf_rest,
            ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ hterm_s')
              hstar_rest'⟩

/-! ### Compositionality of `Overapproximates` over statement lists

`overapproximates_stmts` lifts a per-statement overapproximation to whole
statement lists (block bodies).  If `T` overapproximates every individual
statement, then `fun ss => ss.mapM T` overapproximates the block obtained by
mapping `T` over the list.
-/

theorem overapproximates_stmts
    (hwf_ext : WFFactoryExtension P extendFactory)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) T params₁ params₂) :
    Overapproximates
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn)
      (fun ss => ss.mapM T) () () := by
  intro ss ss' hmap _ ρ₀ ρ₀' heq hwf
  subst heq
  have aux := overapproximates_stmts_aux evalCmd extendFactory isAtAssertFn hwf_ext T
    params₁ params₂ hsem ss ss' hmap ρ₀
  refine ⟨fun ρ' => ⟨fun h => ⟨ρ', rfl, (aux ρ' hwf).1 h⟩,
                      fun lbl h => ⟨ρ', rfl, (aux ρ' hwf).2 lbl h⟩⟩, ?_, hwf⟩
  -- CanFail preservation via the dedicated helper.
  intro ⟨cfg, hfcfg, hstar⟩
  exact overapproximates_stmts_canfail evalCmd extendFactory isAtAssertFn hwf_ext T params₁ params₂
    hsem ss ss' hmap ρ₀ hwf ⟨cfg, hfcfg, hstar⟩


/-! ## Aggressive statement-list overapproximation

The lemmas below are the aggressive analogues of `overapproximates_stmts_*`.
They use `OverapproximatesAggressively`, under which the target program is
allowed to assert-fail spuriously. -/

omit [HasOps P] in
/-- Lifting `CanFail` from a head statement to the enclosing block (cons of a
    statement list): if the head `s` can fail from `ρ₀`, so can `s :: ss`. -/
theorem canFail_head_to_block
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT)) (ρ₀ : Env P)
    (h : CanFail (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) s ρ₀) :
    CanFailBlock evalCmd extendFactory (s :: ss) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  refine ⟨.seq cfg ss, ?_, ?_⟩
  · simp [Config.getEnv]; exact hfail
  · exact ReflTrans_Transitive _ _ _ _
      (.step _ _ _ .step_stmts_cons (.refl _))
      (seq_inner_star P evalCmd extendFactory _ _ ss hreach)

private theorem overapproximatesAggressively_stmts_canfail
    (hwf_ext : WFFactoryExtension P extendFactory)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) T params₁ params₂)
    (ss : List (Stmt P CmdT))
    (ss' : List (Stmt P CmdT))
    (hmap : ss.mapM T = some ss')
    (ρ₀ : Env P)
    (hwf : WellFormedSemanticEval (P := P) ρ₀.factory)
    (hcf : ∃ cfg : Config P CmdT, cfg.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) cfg) :
    ∃ cfg' : Config P CmdT, cfg'.getEnv.hasFailure = true ∧
      StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) cfg' := by
  induction ss generalizing ss' ρ₀ with
  | nil =>
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    exact ⟨cfg, hfcfg, hstar⟩
  | cons s rest ih =>
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    obtain ⟨cfg, hfcfg, hstar⟩ := hcf
    cases hstar with
    | refl =>
      exact ⟨.stmts (s' :: rest') ρ₀, hfcfg, .refl _⟩
    | step _ _ _ hstep hrest_exec => cases hstep with
      | step_stmts_cons =>
        match seq_canfail_prop hrest_exec hfcfg with
        | .inl ⟨cfg', hf', hstar'⟩ =>
          -- Failure in the head `s`: use aggressive fail preservation (`.2.2.1`).
          have hsem_canfail := (hsem s s' hs trivial ρ₀ hwf).2.2.1
          have ⟨cfg_t, hf_t, hstar_t⟩ := hsem_canfail ⟨cfg', hf', hstar'⟩
          exact ⟨.seq cfg_t rest', hf_t,
            .step _ _ _ .step_stmts_cons
              (seq_inner_star P evalCmd extendFactory _ cfg_t rest' hstar_t)⟩
        | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
          have hwf₁ : WellFormedSemanticEval (P := P) ρ₁.factory :=
            star_preserves_wfEval P evalCmd extendFactory hwf_ext hterm_s hwf
          -- The head's terminal guarantee is a disjunction under `hsem` (`.1`).
          match (hsem s s' hs trivial ρ₀ hwf).1 ρ₁ hterm_s with
          | .inl canfail_s' =>
            obtain ⟨cfg'', hf'', hreach''⟩ := canfail_s'
            exact ⟨.seq cfg'' rest', by simp [Config.getEnv]; exact hf'',
              .step _ _ _ .step_stmts_cons
                (seq_inner_star P evalCmd extendFactory _ cfg'' rest' hreach'')⟩
          | .inr hterm_s' =>
            by_cases hf₁ : ρ₁.hasFailure = false
            · -- Head terminates without failure at ρ₁; recurse on the tail.
              have ⟨cfg_rest, hf_rest, hstar_rest'⟩ :=
                ih rest' hrm ρ₁ hwf₁ ⟨cfg', hf', hstar_rest⟩
              exact ⟨cfg_rest, hf_rest,
                ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                  hstar_rest'⟩
            · -- ρ₁ already has a failure ⇒ the head can fail ⇒ so can `s'`.
              have hf₁' : ρ₁.hasFailure = true := by
                cases h : ρ₁.hasFailure <;> simp_all
              have hcanfail_s :
                  CanFail (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) s ρ₀ :=
                ⟨.terminal ρ₁, by simp [Config.getEnv]; exact hf₁', hterm_s⟩
              have ⟨cfg'', hf'', hreach''⟩ := (hsem s s' hs trivial ρ₀ hwf).2.2.1 hcanfail_s
              exact ⟨.seq cfg'' rest', by simp [Config.getEnv]; exact hf'',
                .step _ _ _ .step_stmts_cons
                  (seq_inner_star P evalCmd extendFactory _ cfg'' rest' hreach'')⟩

private theorem overapproximatesAggressively_stmts_aux
    (hwf_ext : WFFactoryExtension P extendFactory)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) T params₁ params₂)
    (ss : List (Stmt P CmdT)) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEval (P := P) ρ₀.factory →
        (StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.terminal ρ') →
          CanFailBlock evalCmd extendFactory ss' ρ₀ ∨
          (ρ'.hasFailure = false →
            StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) (.terminal ρ')))
        ∧
        (∀ lbl, StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.exiting lbl ρ') →
          CanFailBlock evalCmd extendFactory ss' ρ₀ ∨
          (ρ'.hasFailure = false →
            StepStmtStar P evalCmd extendFactory (.stmts ss' ρ₀) (.exiting lbl ρ'))) := by
  induction ss with
  | nil =>
    intro ss' hmap ρ₀ ρ' _
    have : ss' = [] := by simp [List.mapM_nil] at hmap; exact hmap
    subst this; exact ⟨fun h => .inr (fun _ => h), fun lbl h => .inr (fun _ => h)⟩
  | cons s rest ih =>
    intro ss' hmap ρ₀ ρ' hwf
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have wf_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
        WellFormedSemanticEval (P := P) ρ₁.factory := by
      intro ρ₁ hterm_s
      exact star_preserves_wfEval P evalCmd extendFactory hwf_ext hterm_s hwf
    have ⟨hsem_term, hsem_exit, hsem_fail, _hsem_swf⟩ :=
      hsem s s' hs trivial ρ₀ hwf
    -- Common pattern: a failing intermediate env makes the head, hence the whole
    -- transformed block, able to fail.
    have canfail_from_failure : ∀ (ρ₁ : Env P),
        StepStmtStar P evalCmd extendFactory (.stmt s ρ₀) (.terminal ρ₁) →
        ρ₁.hasFailure = true →
        CanFailBlock evalCmd extendFactory (s' :: rest') ρ₀ := by
      intro ρ₁ hterm_s hf₁
      have hcanfail_s :
          CanFail (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) s ρ₀ :=
        ⟨.terminal ρ₁, by simp [Config.getEnv]; exact hf₁, hterm_s⟩
      exact canFail_head_to_block evalCmd extendFactory isAtAssertFn s' rest' ρ₀
        (hsem_fail hcanfail_s)
    constructor
    · -- Terminal case
      intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendFactory hrest_exec
          have hwf₁ := wf_preserved ρ₁ hterm_s
          match hsem_term ρ₁ hterm_s with
          | .inl canfail_s' =>
            exact .inl (canFail_head_to_block evalCmd extendFactory isAtAssertFn s' rest' ρ₀ canfail_s')
          | .inr hterm_s' =>
            by_cases hf₁ : ρ₁.hasFailure = false
            · match (ih rest' hrm ρ₁ ρ' hwf₁).1 hterm_rest with
              | .inl canfail_rest' =>
                obtain ⟨cfg', hf', hreach'⟩ := canfail_rest'
                exact .inl ⟨cfg', hf',
                  ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                    hreach'⟩
              | .inr hterm_rest' =>
                exact .inr fun hf =>
                  ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                    (hterm_rest' hf)
            · have hf₁' : ρ₁.hasFailure = true := by
                cases h : ρ₁.hasFailure <;> simp_all
              exact .inl (canfail_from_failure ρ₁ hterm_s hf₁')
    · -- Exiting case
      intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendFactory hrest_exec with
          | .inl hexit_s =>
            match hsem_exit lbl ρ' hexit_s with
            | .inl canfail_s' =>
              exact .inl (canFail_head_to_block evalCmd extendFactory isAtAssertFn s' rest' ρ₀ canfail_s')
            | .inr hexit_s' =>
              exact .inr fun hf =>
                .step _ _ _ .step_stmts_cons
                  (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendFactory _ _ rest'
                    (hexit_s' hf))
                    (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have hwf₁ := wf_preserved ρ₁ hterm_s
            match hsem_term ρ₁ hterm_s with
            | .inl canfail_s' =>
              exact .inl (canFail_head_to_block evalCmd extendFactory isAtAssertFn s' rest' ρ₀ canfail_s')
            | .inr hterm_s' =>
              match (ih rest' hrm ρ₁ ρ' hwf₁).2 lbl hexit_rest with
              | .inl canfail_rest' =>
                by_cases hf₁ : ρ₁.hasFailure = false
                · obtain ⟨cfg', hf', hreach'⟩ := canfail_rest'
                  exact .inl ⟨cfg', hf',
                    ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                      hreach'⟩
                · have hf₁' : ρ₁.hasFailure = true := by
                    cases h : ρ₁.hasFailure <;> simp_all
                  exact .inl (canfail_from_failure ρ₁ hterm_s hf₁')
              | .inr hexit_rest' =>
                exact .inr fun hf => by
                  by_cases hf₁ : ρ₁.hasFailure = false
                  · exact ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step P evalCmd extendFactory s' rest' ρ₀ ρ₁ (hterm_s' hf₁))
                      (hexit_rest' hf)
                  · exfalso
                    have hf₁' : ρ₁.hasFailure = true := by
                      cases h : ρ₁.hasFailure <;> simp_all
                    have hf_ρ' : ρ'.hasFailure = true :=
                      StepStmtStar_hasFailure_monotone hexit_rest hf₁'
                    exact absurd hf (by simp [hf_ρ'])

/-- Compositionality of `OverapproximatesAggressively` over statement lists.

The aggressive analogue of `overapproximates_stmts`: if `T` aggressively
overapproximates every individual statement, then `fun ss => ss.mapM T`
aggressively overapproximates the whole block.
-/
theorem overapproximatesAggressively_stmts
    (hwf_ext : WFFactoryExtension P extendFactory)
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (params₁ params₂ : (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn).InitEnvWFParamsTy)
    (hsem : OverapproximatesAggressively (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn)
      (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn) T params₁ params₂) :
    OverapproximatesAggressively
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn)
      (fun ss => ss.mapM T) () () := by
  intro ss ss' hmap _ ρ₀ hwf
  refine ⟨fun ρ' hstar => ?_, fun lbl ρ' hstar => ?_, ?_, hwf⟩
  · exact (overapproximatesAggressively_stmts_aux evalCmd extendFactory isAtAssertFn hwf_ext T
      params₁ params₂ hsem ss ss' hmap ρ₀ ρ' hwf).1 hstar
  · exact (overapproximatesAggressively_stmts_aux evalCmd extendFactory isAtAssertFn hwf_ext T
      params₁ params₂ hsem ss ss' hmap ρ₀ ρ' hwf).2 lbl hstar
  · intro ⟨cfg, hfcfg, hstar⟩
    exact overapproximatesAggressively_stmts_canfail evalCmd extendFactory isAtAssertFn hwf_ext T
      params₁ params₂ hsem ss ss' hmap ρ₀ hwf
      ⟨cfg, hfcfg, hstar⟩

end StructuredStmts

end Transform
end Specification
end Imperative

end -- public section
