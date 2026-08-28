/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.Transform.Specification
public import Strata.DL.Imperative.Logic.HoareTemplate
import all Strata.Transform.Specification
import all Strata.DL.Imperative.Logic.HoareTemplate
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.StmtSemanticsProps
import Strata.Util.ListUtilsProps

/-! # Bridges between the Hoare logic and the soundness specification

`Strata.DL.Imperative.Logic.HoareTemplate` is deliberately self-contained: it never mentions
the reachability-based half of the framework (`AssertValidWhen`, `Sound`, the
`Overapproximates` family).  This module holds the bridges in both directions, so that
neither side has to depend on the other's internals.

## Key results

Between `Hoare.Triple` and assertion validity, for a `PredicatedStmt`
(`assume pre; s; assert post` wrapped in a block, defined here):

- `hoareTriple_implies_assertValid` — a triple makes the *postcondition* assert valid.
- `allAssertsValid_implies_hoareTriple` — and conversely, for an `st` whose exits
  are locally covered (an escaping `exit` would skip the trailing `assert`).

Both are stated at an arbitrary initial-environment well-formedness condition rather
than at `Lang.imperative`'s default, and each carries the one side condition its proof
consumes.

Between `Hoare.Triple` and the `Overapproximates` family — `Triple` is `Lang`-generic,
so a triple proved about the *target* of a translation (possibly the unstructured
`Lang.cfg`) transports back to the source:

- `overapproximates_triple` — an overapproximation preserves `Hoare.Triple`.
- `overapproximatesWhen_triple` — the same for `OverapproximatesWhen`, i.e. under a
  precondition on the source statement.
-/

public section

namespace Imperative

namespace Specification

open Strata.Logic Imperative.Logic

namespace Hoare

/-! ## The predicated statement the bridges are stated over -/

/-- The composite statement `assume pre; st; assert post` wrapped in a block.

    This is the shape that makes a Hoare triple and assertion validity comparable at
    all: the triple's pre/postcondition become the `assume` and the trailing `assert`,
    so "the triple holds" and "that `assert` is valid" are statements about the same
    program. -/
@[expose] def PredicatedStmt (P' : PureExpr)
    [HasFvar P'] [HasBool P'] [HasBoolOps P'] [HasFvars P']
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P') : Stmt P' (Cmd P') :=
  .block block_label
    [.cmd (.assume pre_label pre_expr pre_md), st, .cmd (.assert post_label post_expr post_md)]
    block_md

/-! ## Connection between HoareTriple and AssertValid -/

section StandardConnection

variable (P' : PureExpr) [HasFvar P'] [HasFvars P'] [HasBool P'] [HasBoolOps P'] [HasSubstFvar P']
    [HasInt P'] [HasIntOps P']
variable (extendFactory : ExtendFactory P')
variable {ParamsTy : Type} (initEnvWF : ParamsTy → Stmt P' (Cmd P') → Env P' → Prop)

/-- **Direction 1**: a Hoare triple makes the postcondition assertion valid.  For the
    composite statement `assume pre; st; assert post` wrapped in a block, if
    `{pre} st {post}` holds then that trailing `assert post` holds on every execution
    path that reaches it.

    `hno` restricts this to the *trailing* assertion: it says `st` contains no assertion
    carrying `post_label`, so the only site with that label is the one the triple's
    postcondition speaks about.  `hPreWF` bridges the `AssertValidWhen` precondition
    `Pre` to the triple's own initial-environment condition, at the failure-cleared
    initial environment the triple is applied to. -/
theorem hoareTriple_implies_assertValid (params : ParamsTy) (Pre : Env P' → Prop)
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hPreWF : ∀ ρ, Pre ρ → initEnvWF params st { ρ with hasFailure := false })
    (hoare : Strata.Logic.Hoare.Triple (Lang.imperative P' (Cmd P') (EvalCmd P') extendFactory
        (Imperative.isAtAssert P') ParamsTy initEnvWF) params
      (fun ρ => P'.eval ρ.factory ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => P'.eval ρ.factory ρ.store post_expr = some HasBool.tt))
    (hno : st.noMatchingAssert post_label) :
    AssertValidWhen (Lang.imperative P' (Cmd P') (EvalCmd P') extendFactory
        (Imperative.isAtAssert P') ParamsTy initEnvWF)
      Pre
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)
      ⟨post_label, post_expr⟩ := by
  intro ρ₀ cfg hwhen hreach hat
  replace hwhen := hPreWF ρ₀ hwhen
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
              have h_not_at : ¬ isAtAssert P'
                  (.stmts (st :: [.cmd (.assert post_label post_expr post_md)]) ρ₁)
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
              exact absurd hat_stmts h_not_at
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
                            hpre hwhen rfl (.inl hterm_clean)
                          simp only [hs_eq, he_eq] at hpost
                          have ⟨hs, he⟩ := assert_tail_getStore P' extendFactory
                            ρ' post_label post_expr post_md inner ⟨post_label, post_expr⟩
                            hrest_assert hat_inner
                          dsimp [Config.getStore, Config.getEnv] at he hs ⊢
                          rw [he, hs]; exact hpost
                        | step _ _ _ h _ => exact absurd h (by intro h; cases h)


/-- **Direction 2**: assertion validity gives back the Hoare triple.  For the composite
    statement `assume pre; st; assert post` wrapped in a block, if every assertion in it
    is valid then `{pre} st {post}` holds.

    `hbool` is the only well-formedness the proof consumes: the `assume` command
    prefixed by `PredicatedStmt` steps only under `WellFormedSemanticEvalBool`.
    At the default condition it is the `.bool` field of `WellFormedSemanticEval`.

    `hnoesc` is what the other direction does not need.  `Triple` also constrains
    runs that end *exiting*, and an `exit` escaping `st` skips the trailing
    `assert post` of the `PredicatedStmt` — so assertion validity says nothing
    about such a run.  Requiring `st`'s exits to be locally covered rules the case
    out; it holds of any `st` that does not `exit` out of itself.
-/
theorem allAssertsValid_implies_hoareTriple
    (params : ParamsTy)
    (pre_label : String) (pre_expr : P'.Expr) (pre_md : MetaData P')
    (st : Stmt P' (Cmd P'))
    (post_label : String) (post_expr : P'.Expr) (post_md : MetaData P')
    (block_label : String) (block_md : MetaData P')
    (hbool : ∀ ρ, initEnvWF params st ρ → WellFormedSemanticEvalBool (P := P') ρ.factory)
    (hnoesc : st.exitsCoveredByBlocks [])
    (hvalid : AllAssertsValid (Lang.imperative P' (Cmd P') (EvalCmd P') extendFactory
        (Imperative.isAtAssert P') ParamsTy initEnvWF)
      (PredicatedStmt P' pre_label pre_expr pre_md st post_label post_expr post_md block_label block_md)) :
    Strata.Logic.Hoare.Triple (Lang.imperative P' (Cmd P') (EvalCmd P') extendFactory
        (Imperative.isAtAssert P') ParamsTy initEnvWF) params
      (fun ρ => P'.eval ρ.factory ρ.store pre_expr = some HasBool.tt)
      st
      (fun ρ => P'.eval ρ.factory ρ.store post_expr = some HasBool.tt) := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  have hstar : StepStmtStar P' (EvalCmd P') extendFactory (.stmt st ρ₀) (.terminal ρ') := by
    rcases hdone with hterm | ⟨lbl, hexit⟩
    · exact hterm
    · exact absurd hexit
        (exitsCoveredByBlocks_noEscape P' (EvalCmd P') extendFactory st hnoesc ρ₀ lbl ρ')
  have hwfb := hbool ρ₀ hinit
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

variable {P : PureExpr}

/-- If `T` overapproximates and a Hoare triple holds on `T(st)` in L₂,
    then the triple holds on `st` in L₁. -/
theorem overapproximates_triple (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : Overapproximates L₁ L₂ T params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.Triple L₂ params₂ Pre s' Post) :
    Strata.Logic.Hoare.Triple L₁ params₁ Pre st Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  have hr := hsem st s' ht trivial ρ₀ ρ₀ rfl hinit
  refine htriple ρ₀ ρ' hpre hr.2.2 hf₀ ?_
  rcases hstar with hterm | ⟨lbl, hexit⟩
  · obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').1 hterm; subst heq; exact .inl hstar'
  · obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').2 lbl hexit; subst heq; exact .inr ⟨lbl, hstar'⟩

/-- Hoare-triple corollary for `OverapproximatesWhen`: if `T` overapproximates
    when `pre` holds and `pre st` is satisfied, then a Hoare triple on `T(st)`
    in `L₂` lifts to a Hoare triple on `st` in `L₁`.

    This generalizes `overapproximates_triple` to a nontrivial precondition
    (recover the latter with `pre := fun _ => True` and `hsource_pre := trivial`).
    Well-formedness of the source initial env is supplied by `L₁`'s own triple
    condition (`hinit`), so no separate WF-bridging hypothesis is needed. -/
theorem overapproximatesWhen_triple (L₁ L₂ : Lang P)
    (T : L₁.StmtT → Option L₂.StmtT) (pre : L₁.StmtT → Prop)
    (params₁ : L₁.InitEnvWFParamsTy) (params₂ : L₂.InitEnvWFParamsTy)
    (st : L₁.StmtT) (s' : L₂.StmtT) (ht : T st = some s')
    (hsem : OverapproximatesWhen L₁ L₂ T pre params₁ params₂)
    {Pre Post : Env P → Prop}
    (htriple : Strata.Logic.Hoare.Triple L₂ params₂ Pre s' Post)
    (hsource_pre : pre st) :
    Strata.Logic.Hoare.Triple L₁ params₁ Pre st Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hstar
  have hr := hsem st s' ht hsource_pre ρ₀ ρ₀ rfl hinit
  refine htriple ρ₀ ρ' hpre hr.2.2 hf₀ ?_
  rcases hstar with hterm | ⟨lbl, hexit⟩
  · obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').1 hterm; subst heq; exact .inl hstar'
  · obtain ⟨ρ'', heq, hstar'⟩ := (hr.1 ρ').2 lbl hexit; subst heq; exact .inr ⟨lbl, hstar'⟩

end Transform

end Specification

end Imperative

end -- public section
