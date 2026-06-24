/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Specification
import all Strata.Transform.Specification
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Util.ListUtils

/-! # Theorems for the Soundness Specification

Theorems and proofs that complement the definitions in
`Strata.Transform.Specification`. -/

public section

namespace Imperative

namespace Specification

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasVarsPure P P.Expr]
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
  intro ρ₀ ρ' hpre' hwfb hwfcongr hf₀ hstar
  have ⟨hp, hf⟩ := h ρ₀ ρ' (hpre ρ₀ hpre') hwfb hwfcongr hf₀ hstar
  exact ⟨hpost ρ' hp, hf⟩


/-! ## Structural Hoare rules (Imperative-specific) -/

section StmtRules

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

 omit [HasFvar P] [HasVal P] in
/-- Empty statement list is skip. -/
theorem skip_block (Pre : Env P → Prop) :
    TripleBlock evalCmd extendEval Pre [] Pre := by
  intro ρ₀ ρ' hpre _ _ hf₀ hstar
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
  intro ρ₀ ρ' hpre hwfb _hwfcongr hf₀ hstar
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
  intro ρ₀ ρ' hpre hwfb hwfcongr hf₀ hdone
  have hwfb_preserved : ∀ ρ₁, StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
      WellFormedSemanticEvalBool ρ₁.eval := by
    intro ρ₁ hterm
    have this := smallStep_noFuncDecl_preserves_eval P evalCmd extendEval s ρ₀ ρ₁ hnofd hterm
    rw [this]; exact hwfb
  have hwfcongr_preserved : ∀ ρ₁, StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
      WellFormedSemanticEvalExprCongr ρ₁.eval := by
    intro ρ₁ hterm
    have this := smallStep_noFuncDecl_preserves_eval P evalCmd extendEval s ρ₀ ρ₁ hnofd hterm
    rw [this]; exact hwfcongr
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_ss⟩ := seq_reaches_terminal P evalCmd extendEval hrest
        have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hwfb hwfcongr hf₀ hterm_s
        exact h₂ ρ₁ ρ' hmid (hwfb_preserved ρ₁ hterm_s) (hwfcongr_preserved ρ₁ hterm_s) hf₁ (.inl hrest_ss)
  | .inr ⟨lbl, hexit⟩ =>
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P evalCmd extendEval hrest with
        | .inl hexit_inner =>
          exact absurd hexit_inner
            (exitsCoveredByBlocks_noEscape P evalCmd extendEval s hnoesc ρ₀ lbl ρ')
        | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
          have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre hwfb hwfcongr hf₀ hterm_s
          exact h₂ ρ₁ ρ' hmid (hwfb_preserved ρ₁ hterm_s) (hwfcongr_preserved ρ₁ hterm_s) hf₁ (.inr ⟨lbl, hexit_ss⟩)

omit [HasVal P] in
/-- Lift a `TripleBlock` to a `Triple` by wrapping in a block.
    The postcondition `Post` is required to be stable under `projectStore`
    (it only references variables defined before the block). -/
theorem TripleBlock.toTriple {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h : TripleBlock evalCmd extendEval Pre ss Post)
    (hpost_proj : PostWF Post) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.block l ss md) Post := by
  intro ρ₀ ρ' hpre hwfb hwfcongr hf₀ hstar
  cases hstar with
  | step _ _ _ hstep hrest => cases hstep with
    | step_block =>
      match block_reaches_terminal P evalCmd extendEval hrest with
      | .inl ⟨ρ_inner, hterm, heq⟩ =>
        have ⟨hpost, hf⟩ := h ρ₀ ρ_inner hpre hwfb hwfcongr hf₀ (.inl hterm)
        subst heq; exact hpost_proj ρ_inner _ hpost hf
      | .inr ⟨lbl, ρ_inner, hexit, heq⟩ =>
        have ⟨hpost, hf⟩ := h ρ₀ ρ_inner hpre hwfb hwfcongr hf₀ (.inr ⟨lbl, hexit⟩)
        subst heq; exact hpost_proj ρ_inner _ hpost hf

omit [HasVal P] in
/-- Lift a `Triple` to a `TripleBlock` for a singleton list. -/
theorem Triple.toTripleBlock {s : Stmt P CmdT}
    {Pre Post : Env P → Prop}
    (h : Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre s Post)
    (hnoesc : Stmt.exitsCoveredByBlocks [] s) :
    TripleBlock evalCmd extendEval Pre [s] Post := by
  intro ρ₀ ρ' hpre hwfb hwfcongr hf₀ hdone
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_nil⟩ := seq_reaches_terminal P evalCmd extendEval hrest
        have ⟨hp, hf⟩ := h ρ₀ ρ₁ hpre hwfb hwfcongr hf₀ hterm_s
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
    (he : TripleBlock evalCmd extendEval (fun ρ => Pre ρ ∧ ρ.eval ρ.store c = some HasBool.ff) ess Post) :
    Triple (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) Pre (.ite (.det c) tss ess md) Post := by
  intro ρ₀ ρ' hpre hwfb hwfcongr hf₀ hstar
  cases hstar with
  | step _ _ _ h1 r1 => cases h1 with
    | step_ite_true hc _ => exact ht ρ₀ ρ' ⟨hpre, hc⟩ hwfb hwfcongr hf₀ (.inl r1)
    | step_ite_false hc _ => exact he ρ₀ ρ' ⟨hpre, hc⟩ hwfb hwfcongr hf₀ (.inl r1)

/- TODO: the WHILE rule -/

end StmtRules


/-! ## Connection between HoareTriple and AssertValid (standard Lang) -/

section StandardConnection

variable (P' : PureExpr) [HasFvar P'] [HasBool P'] [HasNot P'] [HasVarsPure P' P'.Expr]
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
                      | eval_assume hpre hwfb hwfcongr =>
                        cases h_assume_rest with
                        | refl =>
                          have ⟨ρ'_clean, hterm_clean, hs_eq, he_eq⟩ :=
                            smallStep_hasFailure_irrel P' (EvalCmd P') extendEval
                              st _ ρ' hterm_st { ρ₀ with hasFailure := false } rfl rfl
                          have ⟨hpost, _⟩ := hoare { ρ₀ with hasFailure := false } ρ'_clean
                            hpre hwfb hwfcongr rfl hterm_clean
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
  intro ρ₀ ρ' hpre hwfb hwfcongr hf₀ hstar
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
      .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb hwfcongr)) (.refl _)
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
    .step _ _ _ (StepStmt.step_cmd (EvalCmd.eval_assume hpre hwfb hwfcongr)) (.refl _)
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

/-! ## Overapproximate predicate -/

/-- If `T` overapproximates and a Hoare triple holds on `T(st)` in L₂,
    then the triple holds on `st` in L₁. -/
theorem overapproximates_triple (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : Overapproximates L₁ L₂ T)
    {Pre Post : Env P → Prop}
    (htriple : Hoare.Triple L₂ Pre s' Post)
    (hwfv : ∀ ρ₀ : Env P, Pre ρ₀ → WellFormedSemanticEvalVal ρ₀.eval) :
    Hoare.Triple L₁ Pre st Post := by
  intro ρ₀ ρ' hpre hwfb hwfcongr hf₀ hstar
  exact htriple ρ₀ ρ' hpre hwfb hwfcongr hf₀
    ((hsem st s' ht ρ₀ ρ' hwfb (hwfv ρ₀ hpre) hwfcongr).1 hstar)

theorem overapproximates_id (L₁ : Lang P) :
    Overapproximates L₁ L₁ some := by
  intro st s' ht ρ₀ ρ' _ _ _
  simp at ht; subst ht
  exact ⟨id, fun _ => id⟩

theorem overapproximates_comp (L₁ L₂ L₃ : Lang P)
    (T₁ : L₁.StmtT → Option L₂.StmtT) (T₂ : L₂.StmtT → Option L₃.StmtT)
    (h₁ : Overapproximates L₁ L₂ T₁)
    (h₂ : Overapproximates L₂ L₃ T₂) :
    Overapproximates L₁ L₃ (fun s => T₁ s >>= T₂) := by
  intro st s'' ht ρ₀ ρ' hwfb hwfv hwfcongr
  simp [bind, Option.bind] at ht
  match h : T₁ st with
  | some s' =>
    rw [h] at ht
    have hr₁ := h₁ st s' h ρ₀ ρ' hwfb hwfv hwfcongr
    have hr₂ := h₂ s' s'' ht ρ₀ ρ' hwfb hwfv hwfcongr
    refine ⟨?_, ?_⟩
    · intro hstar; exact hr₂.1 (hr₁.1 hstar)
    · intro lbl hstar; exact hr₂.2 lbl (hr₁.2 lbl hstar)
  | none => rw [h] at ht; exact absurd ht (by nofun)

/-! ## Overapproximation up to an environment relation (`OverapproximatesUpto*`)

Consumer lemmas for the additive Upto family.  The Upto predicates relate whole
environments by a relation `R : Relation (Env P)` and route initial-environment
well-formedness through each `Lang`'s `initEnvWF` field.  These lemmas establish
monotonicity in `R`, precondition strengthening, identity, and compositionality
(via relation composition `RComp`, collapsed back to a single relation when `R`
is a preorder). -/

section Upto

open scoped Relations  -- `R₁ ∘ R₂` for relation composition (`RComp`)

omit [HasVal P] [HasVarsPure P P.Expr] in
/-- `OverapproximatesWhen` is `OverapproximatesUptoWhen` at the equality
    relation (definitional). -/
theorem overapproximatesWhen_iff_uptoWhen_eq (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) :
    OverapproximatesWhen L₁ L₂ T pre params₁ params₂ ↔
      OverapproximatesUptoWhen (· = ·) L₁ L₂ T pre params₁ params₂ :=
  Iff.rfl

omit [HasVal P] [HasVarsPure P P.Expr] in
/-- Unconditional version: `OverapproximatesWhen` at the trivial precondition is
    `OverapproximatesUpto` at equality (definitional). -/
theorem overapproximatesWhen_true_iff_upto_eq (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy) :
    OverapproximatesWhen L₁ L₂ T (fun _ => True) params₁ params₂ ↔
      OverapproximatesUpto (· = ·) L₁ L₂ T params₁ params₂ :=
  Iff.rfl

omit [HasVal P] [HasVarsPure P P.Expr] in
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

omit [HasVal P] [HasVarsPure P P.Expr] in
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

omit [HasVal P] [HasVarsPure P P.Expr] in
/-- The identity transform is an overapproximation up to `Eq` (reflexivity).
    This is the unit for `comp`. -/
theorem OverapproximatesUpto.id (L : Lang P) (params : L.InitEnvWFParamsTy) :
    OverapproximatesUpto (· = ·) L L some params params := by
  intro st st' ht _ ρ₀ ρ₀' heq hwf
  simp only [Option.some.injEq] at ht; subst ht; subst heq
  exact ⟨fun ρ' => ⟨fun hstar => ⟨ρ', rfl, hstar⟩, fun lbl hstar => ⟨ρ', rfl, hstar⟩⟩,
         (fun h => h), hwf⟩

omit [HasVal P] [HasVarsPure P P.Expr] in
/-- **Compositionality** (general form): composing transforms composes the
    relations via `RComp`.  No conditions on the relations are needed at this
    level of generality — they only appear when collapsing the composite
    `RComp R₁ R₂` back into a single relation (see `comp_preorder`). -/
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

omit [HasVal P] [HasVarsPure P P.Expr] in
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

omit [HasVal P] [HasVarsPure P P.Expr] in
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

omit [HasVal P] [HasVarsPure P P.Expr] in
/-- Precondition strengthening for `OverapproximatesAggressivelyWhen`. -/
theorem OverapproximatesAggressivelyWhen.strengthen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) {pre pre' : L₁.StmtT → Prop}
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (himp : ∀ st, pre' st → pre st)
    (h : OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre' params₁ params₂ := by
  intro st st' ht hpre' ρ₀ hswf
  exact h st st' ht (himp st hpre') ρ₀ hswf

omit [HasVal P] [HasVarsPure P P.Expr] in
/-- `OverapproximatesUptoWhen` at equality implies `OverapproximatesAggressivelyWhen`
    (same precondition).  An exact transform that handles all preconditioned
    inputs is also an aggressive transform that handles them. -/
theorem OverapproximatesWhen.toAggressivelyWhen (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (h : OverapproximatesWhen L₁ L₂ T pre params₁ params₂) :
    OverapproximatesAggressivelyWhen L₁ L₂ T pre params₁ params₂ := by
  intro st st' ht hpre ρ₀ hswf
  have hr := h st st' ht hpre ρ₀ ρ₀ rfl hswf
  refine ⟨?_, ?_, hr.2.1, hr.2.2⟩
  · intro ρ' hstar
    obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').1 hstar
    exact .inr (fun _ => heq ▸ hstar')
  · intro lbl ρ' hstar
    obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').2 lbl hstar
    exact .inr (fun _ => heq ▸ hstar')

end Upto

/-! ## Statement-list overapproximation (Imperative-specific)

Uses `Overapproximates L L T` (single-language): the proof decomposes
seq execution into terminal/exiting outcomes of individual statements,
which is exactly what `Overapproximates` provides. -/

section ImperativeStmts

variable {CmdT : Type} (evalCmd : EvalCmdParam P CmdT) (extendEval : ExtendEval P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)

omit [HasFvar P] [HasBool P] [HasNot P] [HasVal P] in
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

private theorem overapproximates_stmts_aux
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T)
    (ss : List (Stmt P CmdT))
    (hnofd : Block.noFuncDecl ss = true) :
    ∀ (ss' : List (Stmt P CmdT)),
      ss.mapM T = some ss' →
      ∀ (ρ₀ ρ' : Env P),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalExprCongr ρ₀.eval →
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
    intro ss' hmap ρ₀ ρ' hwfb hwfv hwfcongr
    simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd
    have ⟨hnofd_s, hnofd_rest⟩ := hnofd
    have ⟨s', rest', hs, hrm, hss'⟩ := List.mapM_cons_some hmap
    subst hss'
    have eval_preserved : ∀ ρ₁ : Env P,
        StepStmtStar P evalCmd extendEval (.stmt s ρ₀) (.terminal ρ₁) →
        WellFormedSemanticEvalBool ρ₁.eval ∧ WellFormedSemanticEvalVal ρ₁.eval ∧
          WellFormedSemanticEvalExprCongr ρ₁.eval := by
      intro ρ₁ hterm_s
      have heq := smallStep_noFuncDecl_preserves_eval P evalCmd extendEval s ρ₀ ρ₁ hnofd_s hterm_s
      exact ⟨heq ▸ hwfb, heq ▸ hwfv, heq ▸ hwfcongr⟩
    constructor
    · intro hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          have ⟨ρ₁, hterm_s, hterm_rest⟩ := seq_reaches_terminal P evalCmd extendEval hrest_exec
          have ⟨hwfb₁, hwfv₁, hwfcongr₁⟩ := eval_preserved ρ₁ hterm_s
          exact ReflTrans_Transitive _ _ _ _
            (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁
              ((hsem s s' hs ρ₀ ρ₁ hwfb hwfv hwfcongr).1 hterm_s))
            ((ih hnofd_rest rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfcongr₁).1 hterm_rest)
    · intro lbl hstar
      cases hstar with
      | step _ _ _ hstep hrest_exec => cases hstep with
        | step_stmts_cons =>
          match seq_reaches_exiting P evalCmd extendEval hrest_exec with
          | .inl hexit_s =>
            exact .step _ _ _ .step_stmts_cons
              (ReflTrans_Transitive _ _ _ _ (seq_inner_star P evalCmd extendEval _ _ rest'
                ((hsem s s' hs ρ₀ ρ' hwfb hwfv hwfcongr).2 lbl hexit_s))
                (.step _ _ _ .step_seq_exit (.refl _)))
          | .inr ⟨ρ₁, hterm_s, hexit_rest⟩ =>
            have ⟨hwfb₁, hwfv₁, hwfcongr₁⟩ := eval_preserved ρ₁ hterm_s
            exact ReflTrans_Transitive _ _ _ _
              (stmts_cons_step P evalCmd extendEval s' rest' ρ₀ ρ₁
                ((hsem s s' hs ρ₀ ρ₁ hwfb hwfv hwfcongr).1 hterm_s))
              ((ih hnofd_rest rest' hrm ρ₁ ρ' hwfb₁ hwfv₁ hwfcongr₁).2 lbl hexit_rest)

theorem overapproximates_stmts
    (T : Stmt P CmdT → Option (Stmt P CmdT))
    (hsem : Overapproximates (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) (Lang.imperative P CmdT evalCmd extendEval isAtAssertFn) T)
    (hnofd_T : ∀ s s', T s = some s' → Stmt.noFuncDecl s = true) :
    Overapproximates
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (Lang.imperativeBlock evalCmd extendEval isAtAssertFn)
      (fun ss => ss.mapM T) := by
  intro ss ss' hmap ρ₀ ρ' hwfb hwfv hwfcongr
  exact overapproximates_stmts_aux evalCmd extendEval isAtAssertFn T hsem ss
    (mapM_noFuncDecl T hnofd_T ss ss' hmap) ss' hmap ρ₀ ρ' hwfb hwfv hwfcongr

end ImperativeStmts

end Transform
end Specification
end Imperative

end -- public section
