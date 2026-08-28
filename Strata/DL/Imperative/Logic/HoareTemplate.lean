/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.Logic.LangDef
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.StmtSemanticsProps

/-! # A Hoare-logic template for the Imperative dialect

Note: This module is a *template*, not a Hoare logic for a language: `Imperative` fixes no
command type and no evaluator, so nothing here can be applied to a program.  A language
instantiates it — see `Strata.Languages.Core.Logic.Hoare` — to obtain usable rules.

A self-contained partial-correctness Hoare logic, depending only on the Imperative dialect
itself (`Stmt`, `Cmd`, their small-step semantics, and the `Strata.Logic.Lang` bundle).  It
does not mention the reachability-based half of the soundness-specification framework
(`AssertValidWhen`, `Sound`, the `Overapproximates` family); the bridges to that live on
its side, in `Strata.Transform.SpecHoareConnection`.

`Strata.Logic.Hoare.Triple` is language-agnostic — stated over an arbitrary
`Strata.Logic.Lang P`, which is what lets a triple be transported from a target language
back to the source.  Everything else lives in `Imperative.Logic.Hoare`.

## Contents

`Strata.Logic.Hoare.Triple` and `PostWF`, with the rules `false_pre`, `consequence`,
`skip_block`, `cmd`, `seq_append`, `exit_cons`, `block`, `singleton`, `skip`, `ite` and
`while_rule`.

There is a *single* triple judgement.  Statements and statement lists are covered by
instantiating it at two `Lang` packs — `Lang.imperative` and `Lang.imperativeBlock` —
rather than by two definitions (see `Triple` for why the exiting final configuration it
admits lets one judgement cover both).  `block` and `singleton` move between the two.

## Why the rules read as verbosely as they do

The rules take their well-formedness conditions as parameters because the dialect is
abstract over the command type and evaluator, so it has no notion of a well-formed state
to appeal to.  Each rule therefore carries a *lowering* condition, taking the enclosing
condition to the sub-derivation it hands off to, and — where a sub-derivation runs — a
*preservation* condition re-establishing it afterwards.  A concrete language pays this
price once, discharging both from its own lemmas.

The rules live alongside the judgement they introduce rather than in a `HoareProps`
module: they *are* the logic, not properties of it.
-/

public section

/-! ## The `Lang`-generic triple -/

namespace Strata.Logic.Hoare

open Imperative

section

variable {P : PureExpr}
variable (L : Lang P)

/-- Partial-correctness Hoare triple: for every initial environment satisfying
    `Pre` that the language's own `initEnvWF` admits and that carries no prior
    failure, if `s` runs to completion at `ρ'` then `Post ρ'` holds and no
    assertion failed along the way (`ρ'.hasFailure = false`).

    `L.initEnvWF params` is the initial-environment well-formedness condition: the
    triple only constrains runs started from an environment the condition admits, and it
    is *antimonotone* in that condition — a triple proved under a weaker one holds under
    any stronger one.

    A run may end **terminal or exiting**: `s` may be a statement list whose
    `exit` escapes, or a statement that is itself an `exit`, and in either case an
    enclosing block would catch it and continue — so the postcondition has to hold
    there too.  Constraining only terminal runs would make `{Pre} exit l {Post}`
    vacuous for every `Post`.

    "All asserts in `s` are valid" is strictly stronger than this triple:
    `{True} (assert false; loop_forever) {anything}` holds vacuously because the
    program never terminates, even though the `assert` fails.

    TODO: We will want to define Triple for total correctness. It will be useful
    when proving preservation of termination after program transformation. -/
@[expose] def Triple
    (params : L.InitEnvWFParamsTy)
    (Pre : Env P → Prop) (s : L.StmtT) (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P),
    Pre ρ₀ → L.initEnvWF params s ρ₀ → ρ₀.hasFailure = false →
    (L.star (L.stmtCfg s ρ₀) (L.terminalCfg ρ') ∨
     ∃ lbl, L.star (L.stmtCfg s ρ₀) (L.exitingCfg lbl ρ')) →
    Post ρ' ∧ ρ'.hasFailure = false


/-! ## Rules that do not inspect the statement -/

/-- False precondition proves anything. -/
theorem false_pre (params : L.InitEnvWFParamsTy) (s : L.StmtT) (Post : Env P → Prop) :
    Triple L params (fun _ => False) s Post := by
  intro _ _ hpre; exact absurd hpre id

/-- Consequence (weakening): strengthen precondition, weaken postconditions. -/
theorem consequence (params : L.InitEnvWFParamsTy)
    {Pre Pre' Post Post' : Env P → Prop} {s : L.StmtT}
    (h : Triple L params Pre s Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple L params Pre' s Post' := by
  intro ρ₀ ρ' hpre' hinit hf₀ hstar
  have ⟨hp, hf⟩ := h ρ₀ ρ' (hpre ρ₀ hpre') hinit hf₀ hstar
  exact ⟨hpost ρ' hp, hf⟩

end

end Strata.Logic.Hoare


namespace Imperative.Logic.Hoare

open Strata.Logic Strata.Logic.Hoare

/-! ## Definitions -/

/-- A postcondition stable under dropping the names the body defines.  Required by every
    rule that wraps a body in a block, since leaving the block removes those names from
    the store. -/
def PostWF {P : PureExpr} {CmdT : Type} [HasVarsImp P CmdT] [DecidableEq P.Ident]
    (ss : List (Stmt P CmdT)) (Post : Env P → Prop) : Prop :=
  ∀ ρ, Post ρ →
    Post { ρ with
      store := dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ.store }

/-- A body that declares nothing satisfies `PostWF` for every postcondition: leaving the
    block has nothing to drop. -/
theorem postWF_of_definedVars_nil {P : PureExpr} {CmdT : Type} [HasVarsImp P CmdT]
    [DecidableEq P.Ident] {ss : List (Stmt P CmdT)} (Post : Env P → Prop)
    (h : Block.definedVars (P := P) (C := CmdT) ss true = []) :
    PostWF ss Post := by
  intro ρ hpost
  have hdrop : dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ.store = ρ.store := by
    funext n; simp [dropVars, h]
  rw [hdrop]
  exact hpost


/-! ## Structural rules (Structured Imperative-specific) -/

section StmtRules

variable {P : PureExpr} [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P]
    [HasSubstFvar P] [HasInt P] [HasIntOps P] [HasIdent P] [DecidableEq P.Ident]
variable {CmdT : Type} [HasVarsImp P CmdT]
variable (evalCmd : EvalCmdParam P CmdT) (extendFactory : ExtendFactory P)
variable (isAtAssertFn : Config P CmdT → AssertId P → Prop)
variable {ParamsTy : Type} (initEnvWF : ParamsTy → Stmt P CmdT → Env P → Prop)
variable {BParamsTy : Type}
    (blockInitEnvWF : BParamsTy → List (Stmt P CmdT) → Env P → Prop) (bparams : BParamsTy)

omit [DecidableEq P.Ident] in
/-- Empty statement list is skip.  Holds at every block condition: the empty list
    cannot step anywhere but its own terminal. -/
theorem skip_block (Pre : Env P → Prop) :
    Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre [] Pre := by
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

/-- Helper for `while_rule`: the invariant survives arbitrarily many iterations.  By
    strong induction on derivation length. -/
private theorem while_gen
    {guard : P.Expr} {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop} (params : ParamsTy)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hnofd : Block.noFuncDecl (P := P) (C := CmdT) body = true)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      StepStmtStar P evalCmd extendFactory (.stmts body ρ) (.terminal ρ_inner) →
      initEnvWF params (.loop (.det guard) measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store, factory := ρ.factory })
    (hbody : Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some HasBool.tt) body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv)
    (ρ₀ ρ' : Env P) (n : Nat)
    (hInv : Inv ρ₀)
    (hwf : initEnvWF params (.loop (.det guard) measure inv body md) ρ₀)
    (hf₀ : ρ₀.hasFailure = false)
    (hstarT : ReflTransT (StepStmt P evalCmd extendFactory)
      (.stmt (.loop (.det guard) measure inv body md) ρ₀) (.terminal ρ'))
    (hlen : hstarT.len ≤ n) :
    (Inv ρ' ∧ P.eval ρ'.factory ρ'.store guard = some HasBool.ff) ∧ ρ'.hasFailure = false := by
  induction n generalizing ρ₀ ρ' with
  | zero =>
    -- A run from a loop statement to a terminal must take at least one step.
    match hstarT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    match hstarT, hlen with
    | .step _ _ _ (StepStmt.step_loop_exit hg _) hrest, hlen =>
      match hrest with
      | .refl _ => exact ⟨⟨hInv, hg⟩, hf₀⟩
      | .step _ _ _ h _ => exact nomatch h
    | .step _ _ _ (StepStmt.step_loop_enter hg _) hrest, hlen =>
      have ⟨ρ_mid, h_block_term, h_loop_rest, hlen_seq⟩ := seqT_reaches_terminal hrest
      have h_noescape := block_exitsCoveredByBlocks_noEscape P evalCmd extendFactory body hcov ρ₀
      have ⟨ρ_inner, h_inner_term, heq_ρ_mid, hlen_inner⟩ :=
        blockT_reaches_terminal_noExit h_block_term h_noescape
      have ⟨hInv_inner, hf_inner⟩ :=
        hbody ρ₀ ρ_inner ⟨hInv, hg⟩ (hloopBodyWF ρ₀ hwf) hf₀
          (.inl (reflTransT_to_prop h_inner_term))
      have hfac : ρ_inner.factory = ρ₀.factory :=
        noFuncDecl_preserves_factory P evalCmd extendFactory _ _
          (show Config.noFuncDecl (.stmts body ρ₀) from hnofd)
          (reflTransT_to_prop h_inner_term)
      have hproj : projectStore ρ₀.store ρ_inner.store
          = dropVars (Block.definedVars (P := P) (C := CmdT) body true) ρ_inner.store :=
        projectStore_eq_dropVars (evalCmd := evalCmd) (extendFactory := extendFactory)
          h_cmd (hbodyDefs ρ₀ hwf) (.inl (reflTransT_to_prop h_inner_term))
      have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store, factory := ρ₀.factory } : Env P) = { ρ_inner with store := dropVars (Block.definedVars (P := P) (C := CmdT) body true) ρ_inner.store } := by
        rw [hproj, ← hfac]
      have hInv_mid : Inv ρ_mid := by
        rw [heq_ρ_mid, hrec]; exact hInv_proj ρ_inner hInv_inner
      have hf_mid : ρ_mid.hasFailure = false := by rw [heq_ρ_mid]; exact hf_inner
      have ⟨ρ_x, h_loop_T, h_nil, hlen_cons⟩ := stmtsT_cons_terminal h_loop_rest
      have hρx : ρ_x = ρ' := by
        match h_nil with
        | .step _ _ _ StepStmt.step_stmts_nil hr =>
          match hr with
          | .refl _ => rfl
          | .step _ _ _ h _ => exact nomatch h
      subst hρx
      have hwf_mid : initEnvWF params (.loop (.det guard) measure inv body md) ρ_mid := by
        rw [heq_ρ_mid]
        exact hloopWF ρ₀ ρ_inner hwf (reflTransT_to_prop h_inner_term)
      -- Recurse: the loop-tail derivation is strictly shorter.
      exact ih ρ_mid ρ_x hInv_mid hwf_mid hf_mid h_loop_T
        (by simp [ReflTransT.len] at hlen; omega)


omit [HasIdent P] [HasVarsImp P CmdT] [DecidableEq P.Ident] in
/-- **A single command.**  Whatever the command's own semantics establishes about the
    resulting store is the postcondition, provided it raises no failure.

    `h` is that obligation: for every way the command can step from a `Pre`-environment
    the language admits, the postcondition holds of the resulting store and the failure
    flag comes back false.  It receives the language's well-formedness condition
    unchanged, which is where an evaluator-based semantics finds what it needs to step
    at all. -/
theorem cmd (params : ParamsTy) (c : CmdT) (Pre Post : Env P → Prop)
    (h : ∀ ρ₀ σ' f, Pre ρ₀ → initEnvWF params (.cmd c) ρ₀ →
      evalCmd ρ₀.factory ρ₀.store c σ' f →
      Post { ρ₀ with store := σ', hasFailure := f } ∧ f = false) :
    Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn ParamsTy initEnvWF)
      params Pre (.cmd c) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  match hdone with
  | .inl hstar =>
    cases hstar with
    | step _ _ _ h1 r1 => cases h1 with
      | step_cmd hcmd =>
        cases r1 with
        | refl =>
          have ⟨hp, hfeq⟩ := h ρ₀ _ _ hpre hinit hcmd
          simp [hf₀] at hp ⊢; exact ⟨hp, hfeq⟩
        | step _ _ _ h _ => exact nomatch h
  | .inr ⟨_, hexit⟩ =>
    -- A command steps straight to `.terminal`, so it can never reach `.exiting`.
    cases hexit with
    | step _ _ _ h1 r1 => cases h1 with
      | step_cmd _ => cases r1 with | step _ _ _ h _ => exact nomatch h

omit [DecidableEq P.Ident] in
/-- Sequencing: two triples over statement lists compose into one about their
    concatenation, provided the prefix does not escape.  This is the only rule that
    chains derivations.

    `hSs1NoExit` states that the prefix ss₁ doesn't escape (through the .exit statement). -/
theorem seq_append
    {ss₁ ss₂ : List (Stmt P CmdT)}
    {Pre Mid Post : Env P → Prop}
    (hheadWF : ∀ ρ, blockInitEnvWF bparams (ss₁ ++ ss₂) ρ → blockInitEnvWF bparams ss₁ ρ)
    (htailWF : ∀ ρ ρ', blockInitEnvWF bparams (ss₁ ++ ss₂) ρ →
      StepStmtStar P evalCmd extendFactory (.stmts ss₁ ρ) (.terminal ρ') →
      blockInitEnvWF bparams ss₂ ρ')
    (h₁ : Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre ss₁ Mid)
    (h₂ : Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams Mid ss₂ Post)
    (hSs1NoExit : Block.exitsCoveredByBlocks [] ss₁) :
    Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre (ss₁ ++ ss₂) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  match stmts_append_done P evalCmd extendFactory ss₁ ss₂ ρ₀ ρ' hdone with
  | .inl ⟨lbl, hexit₁⟩ =>
    exact absurd hexit₁
      (block_exitsCoveredByBlocks_noEscape P evalCmd extendFactory ss₁ hSs1NoExit ρ₀ lbl ρ')
  | .inr ⟨ρ₁, hterm₁, hfin₂⟩ =>
    have ⟨hmid, hf₁⟩ := h₁ ρ₀ ρ₁ hpre (hheadWF ρ₀ hinit) hf₀ (.inl hterm₁)
    exact h₂ ρ₁ ρ' hmid (htailWF ρ₀ ρ₁ hinit hterm₁) hf₁ hfin₂

omit [DecidableEq P.Ident] in
/-- **Exit.**  An `exit` ends the statement list where it stands: the statements after
    it never run, and the environment is unchanged, so whatever held before the `exit`
    still holds at the exiting configuration.

    This is the rule `seq_append` cannot supply, since it requires its prefix not to
    escape, and it is what the exiting half of `Triple` exists for.  An enclosing `block`
    catches the exit and continues from the projected environment. -/
theorem exit_cons {lbl : String} {md : MetaData P} {ss : List (Stmt P CmdT)}
    {Pre : Env P → Prop} :
    Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre (.exit lbl md :: ss) Pre := by
  intro ρ₀ ρ' hpre _hinit hf₀ hdone
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        -- The head can only reach `.exiting`, so the list cannot terminate.
        have ⟨_, hinner, _⟩ := seq_reaches_terminal P evalCmd extendFactory hrest
        cases hinner with
        | step _ _ _ h r => cases h with
          | step_exit => cases r with | step _ _ _ h' _ => exact nomatch h'
  | .inr ⟨_, hexit⟩ =>
    cases hexit with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        match seq_reaches_exiting P evalCmd extendFactory hrest with
        | .inl hinner =>
          cases hinner with
          | step _ _ _ h r => cases h with
            | step_exit =>
              cases r with
              | refl => exact ⟨hpre, hf₀⟩
              | step _ _ _ h' _ => exact nomatch h'
        | .inr ⟨_, hterm_inner, _⟩ =>
          cases hterm_inner with
          | step _ _ _ h r => cases h with
            | step_exit => cases r with | step _ _ _ h' _ => exact nomatch h'

/-- **Block introduction.**  Wrap a statement list in a block: a triple at
    `Lang.imperativeBlock` about `ss` becomes one at `Lang.imperative` about
    `.block l ss md`.
    `Post` must not mention the names the body scopes (`PostWF`).

    `hbodyWF` lowers the statement condition on `.block l ss md` to the block condition
    on the body `ss`, and `hbodyDefs` extracts from it that those names start undefined —
    which is what makes leaving the block a *drop*.  `hnofd` keeps the factory constant
    across the body, so the exit restores nothing. -/
theorem block (params : ParamsTy)
    {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hnofd : Block.noFuncDecl (P := P) (C := CmdT) ss = true)
    (hbodyWF : ∀ ρ, initEnvWF params (.block l ss md) ρ → blockInitEnvWF bparams ss ρ)
    (hbodyDefs : ∀ ρ, initEnvWF params (.block l ss md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ss true, ρ.store x = none)
    (h : Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre ss Post)
    (hpost_proj : PostWF ss Post) :
    Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn ParamsTy initEnvWF)
      params Pre (.block l ss md) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  -- Step into the block, then invert: however the block finished, its body ran to a
  -- terminal-or-exiting config and the block projected that env.
  have hinner : ∃ ρ_inner,
      (StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.terminal ρ_inner) ∨
       ∃ lbl, StepStmtStar P evalCmd extendFactory (.stmts ss ρ₀) (.exiting lbl ρ_inner)) ∧
      ρ' = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store, factory := ρ₀.factory } := by
    match hdone with
    | .inl hterm =>
      cases hterm with
      | step _ _ _ hstep hrest => cases hstep with
        | step_block => exact block_reaches_done P evalCmd extendFactory (.inl hrest)
    | .inr ⟨lbl, hexit⟩ =>
      cases hexit with
      | step _ _ _ hstep hrest => cases hstep with
        | step_block => exact block_reaches_done P evalCmd extendFactory (.inr ⟨lbl, hrest⟩)
  obtain ⟨ρ_inner, hrun, heq⟩ := hinner
  have ⟨hpost, hf⟩ := h ρ₀ ρ_inner hpre (hbodyWF ρ₀ hinit) hf₀ hrun
  have hfac : ρ_inner.factory = ρ₀.factory := by
    match hrun with
    | .inl hterm =>
      exact noFuncDecl_preserves_factory P evalCmd extendFactory _ _
        (show Config.noFuncDecl (.stmts ss ρ₀) from hnofd) hterm
    | .inr ⟨_, hexit⟩ =>
      exact noFuncDecl_preserves_factory P evalCmd extendFactory _ _
        (show Config.noFuncDecl (.stmts ss ρ₀) from hnofd) hexit
  have hproj : projectStore ρ₀.store ρ_inner.store
      = dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ_inner.store :=
    projectStore_eq_dropVars (evalCmd := evalCmd) (extendFactory := extendFactory)
      h_cmd (hbodyDefs ρ₀ hinit) hrun
  subst heq
  refine ⟨?_, hf⟩
  have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store, factory := ρ₀.factory } : Env P) = { ρ_inner with store := dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ_inner.store } := by
    rw [hproj, ← hfac]
  rw [hrec]
  exact hpost_proj ρ_inner hpost

omit [DecidableEq P.Ident] in
/-- **Singleton list.**  The converse of `block` for a one-element list: a triple at
    `Lang.imperative` about `s` becomes one at `Lang.imperativeBlock` about `[s]`.
    Every statement-shaped rule reaches the list judgement through this.

    `hstmtWF` lowers the block condition on `[s]` to the statement condition on `s`. -/
theorem singleton (params : ParamsTy)
    {s : Stmt P CmdT}
    {Pre Post : Env P → Prop}
    (hstmtWF : ∀ ρ, blockInitEnvWF bparams [s] ρ → initEnvWF params s ρ)
    (h : Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn ParamsTy initEnvWF)
      params Pre s Post) :
    Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre [s] Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ hstep hrest => cases hstep with
      | step_stmts_cons =>
        have ⟨ρ₁, hterm_s, hrest_nil⟩ := seq_reaches_terminal P evalCmd extendFactory hrest
        have ⟨hp, hf⟩ := h ρ₀ ρ₁ hpre (hstmtWF ρ₀ hinit) hf₀ (.inl hterm_s)
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
          -- `s` itself escaped.  The merged triple constrains that run too, so no
          -- escape-coverage side condition is needed here.
          exact h ρ₀ ρ' hpre (hstmtWF ρ₀ hinit) hf₀ (.inr ⟨lbl, hexit_s⟩)
        | .inr ⟨ρ₁, hterm_s, hexit_nil⟩ =>
          cases hexit_nil with
          | step _ _ _ h _ => cases h with
            | step_stmts_nil => rename_i r; cases r with | step _ _ _ h _ => cases h

/-- Empty block is skip.  No well-formedness side condition: `skip_block` holds
    at *every* block condition, so this instantiates it at the trivial one. -/
theorem skip (params : ParamsTy)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (l : String) (md : MetaData P) (Pre : Env P → Prop) :
    Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn ParamsTy initEnvWF)
      params Pre (.block l [] md) Pre :=
  block evalCmd extendFactory isAtAssertFn initEnvWF
    (fun (_ : Unit) _ _ => True) () params h_cmd (by simp [Block.noFuncDecl]) (fun _ _ => trivial)
    (fun _ _ x hx => absurd hx (by simp))
    (skip_block evalCmd extendFactory isAtAssertFn (fun (_ : Unit) _ _ => True) () Pre)
    (postWF_of_definedVars_nil Pre (by simp))

/-- If-then-else rule.  `hthenWF`/`helseWF` lower the statement condition on the
    `ite` to the block condition on each branch. -/
theorem ite (params : ParamsTy)
    {cond : P.Expr} {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hnofd : Stmt.noFuncDecl (P := P) (C := CmdT) (.ite (.det cond) tss ess md) = true)
    (hthenWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ → blockInitEnvWF bparams tss ρ)
    (helseWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ → blockInitEnvWF bparams ess ρ)
    (hthenDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) tss true, ρ.store x = none)
    (helseDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ess true, ρ.store x = none)
    (ht : Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some HasBool.tt) tss Post)
    (he : Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some HasBool.ff) ess Post)
    (hthen_proj : PostWF tss Post) (helse_proj : PostWF ess Post) :
    Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn ParamsTy initEnvWF)
      params Pre (.ite (.det cond) tss ess md) Post := by
  intro ρ₀ ρ' hpre hinit hf₀ hdone
  have hnofd' : Block.noFuncDecl (P := P) (C := CmdT) tss = true ∧
      Block.noFuncDecl (P := P) (C := CmdT) ess = true := by
    simpa only [Stmt.noFuncDecl, Bool.and_eq_true] using hnofd
  -- Both branches, and both ways the `ite`'s block can finish, reduce to the same
  -- shape: the taken branch ran to terminal-or-exiting and the block projected its
  -- env.  `hbranch` does that once, given the branch's own triple.
  have hbranch : ∀ (bss : List (Stmt P CmdT)) (Pre' : Env P → Prop),
      Pre' ρ₀ → blockInitEnvWF bparams bss ρ₀ →
      Block.noFuncDecl (P := P) (C := CmdT) bss = true →
      (∀ x ∈ Block.definedVars (P := P) (C := CmdT) bss true, ρ₀.store x = none) →
      PostWF bss Post →
      Strata.Logic.Hoare.Triple
        (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩)
        bparams Pre' bss Post →
      (StepStmtStar P evalCmd extendFactory
          (.block .none ρ₀.store ρ₀.factory (.stmts bss ρ₀)) (.terminal ρ') ∨
       ∃ lbl, StepStmtStar P evalCmd extendFactory
          (.block .none ρ₀.store ρ₀.factory (.stmts bss ρ₀)) (.exiting lbl ρ')) →
      Post ρ' ∧ ρ'.hasFailure = false := by
    intro bss Pre' hpre' hbwf hbnofd hbdefs hbproj hb hdone_b
    obtain ⟨ρ_inner, hrun, heq⟩ := block_reaches_done P evalCmd extendFactory hdone_b
    have ⟨hpost, hf⟩ := hb ρ₀ ρ_inner hpre' hbwf hf₀ hrun
    have hfac : ρ_inner.factory = ρ₀.factory := by
      match hrun with
      | .inl ht' =>
        exact noFuncDecl_preserves_factory P evalCmd extendFactory _ _
          (show Config.noFuncDecl (.stmts bss ρ₀) from hbnofd) ht'
      | .inr ⟨_, he'⟩ =>
        exact noFuncDecl_preserves_factory P evalCmd extendFactory _ _
          (show Config.noFuncDecl (.stmts bss ρ₀) from hbnofd) he'
    have hproj : projectStore ρ₀.store ρ_inner.store
        = dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store :=
      projectStore_eq_dropVars (evalCmd := evalCmd) (extendFactory := extendFactory)
        h_cmd hbdefs hrun
    subst heq
    refine ⟨?_, hf⟩
    have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store, factory := ρ₀.factory } : Env P) = { ρ_inner with store := dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store } := by
      rw [hproj, ← hfac]
    rw [hrec]
    exact hbproj ρ_inner hpost
  match hdone with
  | .inl hterm =>
    cases hterm with
    | step _ _ _ h1 r1 => cases h1 with
      | step_ite_true hc _ =>
        exact hbranch tss _ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit) hnofd'.1 (hthenDefs ρ₀ hinit) hthen_proj ht (.inl r1)
      | step_ite_false hc _ =>
        exact hbranch ess _ ⟨hpre, hc⟩ (helseWF ρ₀ hinit) hnofd'.2 (helseDefs ρ₀ hinit) helse_proj he (.inl r1)
  | .inr ⟨lbl, hexit⟩ =>
    cases hexit with
    | step _ _ _ h1 r1 => cases h1 with
      | step_ite_true hc _ =>
        exact hbranch tss _ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit) hnofd'.1 (hthenDefs ρ₀ hinit) hthen_proj ht (.inr ⟨lbl, r1⟩)
      | step_ite_false hc _ =>
        exact hbranch ess _ ⟨hpre, hc⟩ (helseWF ρ₀ hinit) hnofd'.2 (helseDefs ρ₀ hinit) helse_proj he (.inr ⟨lbl, r1⟩)

/-- **While rule.**  An invariant that the body re-establishes on every iteration
    holds when the loop finishes, however many iterations it took.

    `hbody` is that obligation: from the invariant *and* a true guard, one run of `body`
    ends in the invariant again.  `hcov` says every `exit` in the body is caught inside
    it, so an iteration cannot jump out of the loop; and `hInv_proj` says the invariant
    survives leaving the body's block, whose store projection would otherwise be free to
    drop it.  The two `…WF` conditions lower the loop's own well-formedness condition to
    the body and re-establish it after an iteration.

    The conclusion is the invariant *together with a false guard* — the loop only
    finishes by failing its guard.  Partial correctness, so a loop that never terminates
    satisfies any conclusion. -/
theorem while_rule (params : ParamsTy)
    {guard : P.Expr} {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {hf : Bool} {y : P.Ident},
      evalCmd f σ c σ' hf → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hnofd : Block.noFuncDecl (P := P) (C := CmdT) body = true)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      StepStmtStar P evalCmd extendFactory (.stmts body ρ) (.terminal ρ_inner) →
      initEnvWF params (.loop (.det guard) measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store, factory := ρ.factory })
    (hbody : Strata.Logic.Hoare.Triple (Lang.imperativeBlock evalCmd extendFactory isAtAssertFn ⟨BParamsTy, blockInitEnvWF⟩) bparams
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some HasBool.tt) body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv) :
    Triple (Lang.imperative P CmdT evalCmd extendFactory isAtAssertFn ParamsTy initEnvWF)
      params Inv (.loop (.det guard) measure inv body md)
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some HasBool.ff) := by
  intro ρ₀ ρ' hInv hinit hf₀ hdone
  match hdone with
  | .inl hstar =>
    exact while_gen evalCmd extendFactory isAtAssertFn initEnvWF blockInitEnvWF bparams params
      h_cmd hnofd hbodyDefs hloopBodyWF hloopWF hbody hcov hInv_proj
      ρ₀ ρ' _ hInv hinit hf₀ (reflTrans_to_T hstar) (Nat.le_refl _)
  | .inr ⟨lbl, hexit⟩ =>
    -- `hcov` says the body catches its own exits, and a loop's only exits are its
    -- body's, so the loop itself can never reach an exiting configuration.
    exact absurd hexit
      (exitsCoveredByBlocks_noEscape P evalCmd extendFactory
        (.loop (.det guard) measure inv body md) hcov ρ₀ lbl ρ')

end StmtRules

end Imperative.Logic.Hoare

end -- public section
