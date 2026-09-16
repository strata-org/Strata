/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.Termination
public import Strata.DL.Imperative.Logic.TraceInterpProps
public import Strata.DL.Imperative.StmtSemanticsProps

/-! # A Hoare-logic template for the Imperative dialect

Note: This module is a *template*, not a Hoare logic for a language: `Imperative` fixes no
command type and no evaluator, so nothing here can be applied to a program.  A language
instantiates it — see `Strata.Languages.Core.Logic.Hoare` — to obtain usable rules.

A self-contained partial-correctness Hoare logic, depending only on the Imperative dialect
itself (`Stmt`, `Cmd`, their event-trace small-step semantics, and the
`Strata.Logic.EventLang` bundle). It does not mention the transformation-soundness
framework (`AssertValidOnTracesWhen`, `Sound`, or the `Overapproximates` family); the event-trace transport bridge lives on its side, in
`Strata.Transform.SpecHoareConnection`.

`Strata.Logic.Hoare.Triple` is language-agnostic — stated over an arbitrary
`Strata.Logic.EventLang P (Event P)`, which is what lets a triple be transported from a
target language back to the source.  Conditions use `EvaluatorBasedInterp P` throughout.
Everything else lives in `Imperative.Logic.Hoare`.

## Contents

`Strata.Logic.Hoare.Triple` and `PostWF`, with the rules `false_pre`,
`consequence`, `skip_block`, `cmd`, `seq_append`, `exit_cons`, `block`,
`singleton`, `skip`, `ite`, and `while_rule`.

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

/-! ## The `EventLang`-generic triple -/

namespace Strata.Logic.Hoare

open Imperative

section

variable {P : PureExpr} [HasBool P]
variable (L : EventLang P (Event P))

local notation "I" => EvaluatorBasedInterp P

/-- Partial-correctness Hoare triple: for every initial environment satisfying
    `Pre` that the language's own `initEnvWF` admits, if `s` runs to completion
    at `ρ'` along `trace`, then every assertion in `trace` is valid.

    `L.initEnvWF params` is the initial-environment well-formedness condition: the
    triple only constrains runs started from an environment the condition admits, and it
    is *antimonotone* in that condition — a triple proved under a weaker one holds under
    any stronger one.

    A run may end terminal or exiting (`L.TerminatesAt`): `s` may be a statement list whose
    `exit` escapes, or a statement that is itself an `exit`, and in either case an
    enclosing block would catch it and continue — so the postcondition has to hold
    there too.  Constraining only terminal runs would make `{Pre} exit l {Post}`
    vacuous for every `Post`.

    "All asserts in `s` are valid" is strictly stronger than this triple:
    `{True} (assert false; loop_forever) {anything}` holds vacuously because the
    program never completes, even though the `assert` fails.

    TODO: We will want to define Triple for total correctness. It will be useful
    when proving preservation of termination after program transformation. -/
@[expose] def TripleWith (conditionInterp : ConditionInterp P)
    (params : L.InitEnvWFParamsTy)
    (Pre : Env P → Prop) (s : L.StmtT) (Post : Env P → Prop) : Prop :=
  ∀ (ρ₀ ρ' : Env P) (trace : Trace P),
    Pre ρ₀ → L.initEnvWF params s ρ₀ →
    L.TerminatesAt s ρ₀ trace ρ' →
    Trace.AssertionsValid P conditionInterp trace ∧
      (Trace.Reachable P conditionInterp trace → Post ρ')

/-- `TripleWith` specialized to the interpreter which uses the evaluator
registered at PureExpr.

TODO: rewrite the Hoare rules in this file to use `TripleWith`, and remove
`Triple` below.
This will help users of HoareTemplate not accidentally use the evaluator-based
interpreter. It will have to be included in a patch that fully switches Core's
Hoare.Triple to use the LExpr.denote function.
-/
@[expose] def Triple
    (params : L.InitEnvWFParamsTy)
    (Pre : Env P → Prop) (s : L.StmtT) (Post : Env P → Prop) : Prop :=
  TripleWith L I params Pre s Post

/-! ## Rules that do not inspect the statement -/

/-- False precondition proves anything. -/
theorem false_pre (params : L.InitEnvWFParamsTy) (s : L.StmtT) (Post : Env P → Prop) :
    Triple L params (fun _ => False) s Post := by
  intro _ _ _ hpre
  exact absurd hpre id

/-- Consequence (weakening): strengthen precondition, weaken postconditions. -/
theorem consequence (params : L.InitEnvWFParamsTy)
    {Pre Pre' Post Post' : Env P → Prop} {s : L.StmtT}
    (h : Triple L params Pre s Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple L params Pre' s Post' := by
  intro ρ₀ ρ' trace hpre' hinit hrun
  have ⟨hvalid, hp⟩ := h ρ₀ ρ' trace (hpre ρ₀ hpre') hinit hrun
  exact ⟨hvalid, fun hsatisfiable => hpost ρ' (hp hsatisfiable)⟩

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
    [HasSubstFvar P] [HasInt P] [HasIntOps P]
variable {CmdT : Type}
local notation "I" => EvaluatorBasedInterp P
variable (evalCmd : EvalCmdParamE P CmdT (Event P))
variable (extendFactory : ExtendFactory P)
variable {ParamsTy : Type}
variable (initEnvWF : ParamsTy → Stmt P CmdT → Env P → Prop)
variable {BParamsTy : Type}
variable (blockInitEnvWF : BParamsTy → List (Stmt P CmdT) → Env P → Prop)
variable (bparams : BParamsTy)

/-- Empty statement list is skip.  Holds at every block condition: the empty list
    cannot step anywhere but its own terminal. -/
theorem skip_block (Pre : Env P → Prop) :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre [] Pre := by
  intro ρ₀ ρ' trace hpre _ hrun
  rcases hrun with hterm | ⟨label, hexit⟩
  · obtain ⟨htrace, hcfg⟩ := stmts_nil_runE evalCmd extendFactory hterm
    subst htrace
    refine ⟨True.intro, fun _ => ?_⟩
    rcases hcfg with hcfg | hcfg
    · simp at hcfg
    · injection hcfg with hρ
      subst hρ
      exact hpre
  · obtain ⟨_, hcfg⟩ := stmts_nil_runE evalCmd extendFactory hexit
    rcases hcfg with hcfg | hcfg <;> simp at hcfg

section
variable [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]

/-- Helper for `while_rule`: the invariant survives arbitrarily many iterations, and
    the completed trace is assertion-valid.  By strong induction on derivation length. -/
private theorem while_genE
    {guard : P.Expr} {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop} (params : ParamsTy)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hnofd : Block.noFuncDecl (P := P) (C := CmdT) body = true)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner tr, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      StepStmtStarE P evalCmd extendFactory (.stmts body ρ) tr (.terminal ρ_inner) →
      initEnvWF params (.loop (.det guard) measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store, factory := ρ.factory })
    (hbody : Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some HasBool.tt) body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv)
    (ρ₀ ρ' : Env P) (trace : Trace P) (n : Nat)
    (hInv : Inv ρ₀)
    (hwf : initEnvWF params (.loop (.det guard) measure inv body md) ρ₀)
    (hrunT : ReflTransTraceT (StepStmtE P evalCmd extendFactory)
      (.stmt (.loop (.det guard) measure inv body md) ρ₀) trace (.terminal ρ'))
    (hlen : hrunT.len ≤ n) :
    Trace.AssertionsValid P I trace ∧
      (Trace.Reachable P I trace →
        Inv ρ' ∧ P.eval ρ'.factory ρ'.store guard = some HasBool.ff) := by
  induction n generalizing ρ₀ ρ' trace with
  | zero =>
    -- A run from a loop statement to a terminal takes at least one step.
    match hrunT, hlen with
    | .step _ _ _ _ _ _ _, hlen => simp only [ReflTransTraceT.len] at hlen; omega
  | succ n ih =>
    match hrunT, hlen with
    | .step _ _ _ restTr _ (.step_admin (.step_loop_exit hg _)) hrest, hlen =>
      -- guard false: the loop terminates immediately, emitting nothing.
      obtain ⟨hc, hnil⟩ := Imperative.stepStmtStarE_from_terminal (reflTransTraceT_to_prop hrest)
      subst hnil
      injection hc with hρ
      subst hρ
      exact ⟨True.intro, fun _ => ⟨hInv, hg⟩⟩
    | .step _ _ _ restTr _ (.step_admin (.step_loop_enter hg _)) hrest, hlen =>
      -- one iteration: the body's block, then the loop again.
      simp only [List.nil_append]
      obtain ⟨ρ_mid, tr₁, tr₂, htr, h_block_term, h_loop_rest, hlen_seq⟩ :=
        seqT_reaches_terminalE hrest
      -- the body block reaches terminal; `hcov` rules out an escaping body.
      obtain ⟨ρ_inner, hbody_disj, heq_ρ_mid⟩ :=
        block_reaches_doneE (.inl (reflTransTraceT_to_prop h_block_term))
      have hbody_run : StepStmtStarE P evalCmd extendFactory (.stmts body ρ₀) tr₁ (.terminal ρ_inner) := by
        rcases hbody_disj with hterm | ⟨lbl, hexit⟩
        · exact hterm
        · exact absurd hexit (stmts_exitsCoveredByBlocks_noEscapeE evalCmd extendFactory
            body hcov ρ₀ lbl ρ_inner)
      -- the loop tail `[loop]` reaches terminal; its `[]` continuation pins ρ' and tr.
      obtain ⟨ρ_x, tr_l, tr_nil, htr2, h_loop_head, h_nil, hlen_cons⟩ :=
        stmtsT_cons_terminalE h_loop_rest
      obtain ⟨htail_nil, htail_cfg⟩ := stmts_nil_runE evalCmd extendFactory
        (reflTransTraceT_to_prop h_nil)
      subst htail_nil
      have hρx : ρ_x = ρ' := by
        rcases htail_cfg with hcfg | hcfg
        · exact absurd hcfg (by simp)
        · injection hcfg with hρ; exact hρ.symm
      subst ρ_x
      simp only [List.append_nil] at htr2
      rw [htr2] at htr
      rw [htr]
      -- reusable facts for lifting `Inv` across the body block's projection.
      have hbodyTriple := hbody ρ₀ ρ_inner tr₁ ⟨hInv, hg⟩ (hloopBodyWF ρ₀ hwf) (.inl hbody_run)
      have hfac : ρ_inner.factory = ρ₀.factory :=
        block_noFuncDecl_preserves_factoryE body ρ₀ ρ_inner hnofd (.inl hbody_run)
      have hproj : projectStore ρ₀.store ρ_inner.store
          = dropVars (Block.definedVars (P := P) (C := CmdT) body true) ρ_inner.store :=
        projectStore_eq_dropVarsE h_cmd (hbodyDefs ρ₀ hwf) (.inl hbody_run)
      have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store, factory := ρ₀.factory } : Env P)
          = { ρ_inner with store := dropVars (Block.definedVars (P := P) (C := CmdT) body true) ρ_inner.store } := by
        rw [hproj, ← hfac]
      have hwf_mid : initEnvWF params (.loop (.det guard) measure inv body md) ρ_mid := by
        rw [heq_ρ_mid]; exact hloopWF ρ₀ ρ_inner tr₁ hwf hbody_run
      -- the tail is proved only when the body prefix is reachable
      -- (so `Inv ρ_mid` holds).
      have hIH : Trace.Reachable P I tr₁ →
          Trace.AssertionsValid P I tr_l ∧
            (Trace.Reachable P I tr_l →
              Inv ρ' ∧ P.eval ρ'.factory ρ'.store guard = some HasBool.ff) := by
        intro hs
        have hInv_mid : Inv ρ_mid := by
          rw [heq_ρ_mid, hrec]; exact hInv_proj ρ_inner (hbodyTriple.2 hs)
        exact ih ρ_mid ρ' tr_l hInv_mid hwf_mid h_loop_head
          (by simp only [ReflTransTraceT.len] at hlen; omega)
      refine ⟨Trace.AssertionsValid.append_of_reachable_left I hbodyTriple.1
        (fun hs => (hIH hs).1), fun hfull => ?_⟩
      exact (hIH (Trace.Reachable.left_of_append I hfull)).2
        (Trace.Reachable.right_of_append I hfull)

end

/-- **A single command.**  Whatever the command's own semantics establishes about the
    resulting store is the postcondition, provided its emitted assertions are valid and
    its emitted trace is reachable.

    `h` is that obligation: for every way the command can step from a `Pre`-environment
    the language admits, its trace is assertion-valid and, when reachable, the
    postcondition holds of the resulting store.  It receives the
    language's well-formedness condition unchanged, which is where an evaluator-based
    semantics finds what it needs to step at all. -/
theorem cmd (params : ParamsTy) (c : CmdT)
    (Pre Post : Env P → Prop)
    (h : ∀ ρ₀ σ' emitted,
      Pre ρ₀ → initEnvWF params (.cmd c) ρ₀ →
      evalCmd ρ₀.factory ρ₀.store c σ' emitted →
      Trace.AssertionsValid P I emitted ∧
        (Trace.Reachable P I emitted → Post { ρ₀ with store := σ' })) :
    Triple (EventLang.imperativeE P CmdT evalCmd extendFactory
      ParamsTy initEnvWF) params Pre (.cmd c) Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  rcases hrun with hterm | ⟨label, hexit⟩
  · cases hterm with
    | step _ emitted _ rest _ hstep htail =>
      cases hstep with
      | step_cmd hcmd =>
        obtain ⟨hcfg, hrest⟩ := Imperative.stepStmtStarE_from_terminal htail
        injection hcfg with hρ
        subst hρ
        subst hrest
        simpa using h ρ₀ _ emitted hpre hinit hcmd
      | step_admin hadmin =>
        cases hadmin with
        | step_cmd hfalse => exact hfalse.elim
  · cases hexit with
    | step _ emitted _ rest _ hstep htail =>
      cases hstep with
      | step_cmd _ =>
        obtain ⟨hcfg, _⟩ := Imperative.stepStmtStarE_from_terminal htail
        cases hcfg
      | step_admin hadmin =>
        cases hadmin with
        | step_cmd hfalse => exact hfalse.elim

/-- Sequencing: two triples over statement lists compose into one about their
    concatenation, provided the prefix does not escape.  This is the only rule that
    chains derivations.

    `hSs1NoExit` states that the prefix ss₁ doesn't escape (through the .exit statement). -/
theorem seq_append
    {ss₁ ss₂ : List (Stmt P CmdT)}
    {Pre Mid Post : Env P → Prop}
    (hheadWF : ∀ ρ, blockInitEnvWF bparams (ss₁ ++ ss₂) ρ →
      blockInitEnvWF bparams ss₁ ρ)
    (htailWF : ∀ ρ ρ' tr, blockInitEnvWF bparams (ss₁ ++ ss₂) ρ →
      StepStmtStarE P evalCmd extendFactory (.stmts ss₁ ρ) tr (.terminal ρ') →
      blockInitEnvWF bparams ss₂ ρ')
    (h₁ : Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre ss₁ Mid)
    (h₂ : Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams Mid ss₂ Post)
    (hSs1NoExit : Block.exitsCoveredByBlocks [] ss₁) :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre (ss₁ ++ ss₂) Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  rcases stmts_append_doneE evalCmd extendFactory ss₁ ss₂ ρ₀ ρ' hrun with
    ⟨lbl, hexit₁⟩ | ⟨ρ₁, tr₁, tr₂, htr, hterm₁, htail⟩
  · -- the prefix cannot escape, so this case is impossible
    exact (stmts_exitsCoveredByBlocks_noEscapeE evalCmd extendFactory ss₁ hSs1NoExit
      ρ₀ lbl ρ' hexit₁).elim
  · subst htr
    obtain ⟨hvalid₁, hmid⟩ := h₁ ρ₀ ρ₁ tr₁ hpre (hheadWF ρ₀ hinit) (.inl hterm₁)
    have htail2WF := htailWF ρ₀ ρ₁ tr₁ hinit hterm₁
    refine ⟨?_, ?_⟩
    · -- assertion validity of the whole trace
      refine Trace.AssertionsValid.append_of_reachable_left I hvalid₁ (fun hs => ?_)
      exact (h₂ ρ₁ ρ' tr₂ (hmid hs) htail2WF htail).1
    · -- postcondition when the whole trace is reachable
      intro hfull
      have hpost := (h₂ ρ₁ ρ' tr₂
        (hmid (Trace.Reachable.left_of_append I hfull)) htail2WF htail).2
      exact hpost (Trace.Reachable.right_of_append I hfull)

/-- **Exit.**  An `exit` ends the statement list where it stands: the statements after
    it never run, and the environment is unchanged, so whatever held before the `exit`
    still holds at the exiting configuration.

    This is the rule `seq_append` cannot supply, since it requires its prefix not to
    escape, and it is what the exiting half of `Triple` exists for.  An enclosing `block`
    catches the exit and continues from the projected environment. -/
theorem exit_cons {lbl : String} {md : MetaData P} {ss : List (Stmt P CmdT)}
    {Pre : Env P → Prop} :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre (.exit lbl md :: ss) Pre := by
  intro ρ₀ ρ' trace hpre _hinit hrun
  rcases hrun with hterm | ⟨elbl, hexit⟩
  · rcases stmts_cons_headE evalCmd extendFactory hterm with hinitial | hseq
    · simp at hinitial
    · obtain ⟨ρ₁, tr₁, tr₂, _, hhead, _⟩ :=
        seq_reaches_terminalE evalCmd extendFactory hseq
      -- the head is an `exit`, so it reaches `.exiting`, never `.terminal`
      cases hhead with
      | step _ _ _ _ _ hstep hrest =>
        cases hstep with
        | step_admin hadmin => cases hadmin with
          | step_exit =>
            obtain ⟨hc, _⟩ := stepStmtStarE_from_exiting hrest
            simp at hc
  · rcases stmts_cons_headE evalCmd extendFactory hexit with hinitial | hseq
    · simp at hinitial
    · rcases seq_reaches_exitingE evalCmd extendFactory hseq with
        hhead | ⟨ρ₁, tr₁, tr₂, _, hterm_head, _⟩
      · -- the head exited: the label and environment are those of the `exit`
        cases hhead with
        | step _ _ _ _ _ hstep hrest =>
          cases hstep with
          | step_admin hadmin => cases hadmin with
            | step_exit =>
              obtain ⟨hc, htr0⟩ := stepStmtStarE_from_exiting hrest
              subst htr0
              injection hc with _ hρ
              subst hρ
              exact ⟨True.intro, fun _ => hpre⟩
      · -- the head cannot terminate before exiting
        cases hterm_head with
        | step _ _ _ _ _ hstep hrest =>
          cases hstep with
          | step_admin hadmin => cases hadmin with
            | step_exit =>
              obtain ⟨hc, _⟩ := stepStmtStarE_from_exiting hrest
              simp at hc

section StructuredRules

variable [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]

/-- **Block introduction.**  Wrap a statement list in a block: a triple at
    `EventLang.imperativeBlockE` about `ss` becomes one at `EventLang.imperativeE` about
    `.block l ss md`.
    `Post` must not mention the names the body scopes (`PostWF`).

    `hbodyWF` lowers the statement condition on `.block l ss md` to the block condition
    on the body `ss`, and `hbodyDefs` extracts from it that those names start undefined —
    which is what makes leaving the block a *drop*.  `hnofd` keeps the factory constant
    across the body, so the exit restores nothing. -/
theorem block (params : ParamsTy)
    {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hnofd : Block.noFuncDecl (P := P) (C := CmdT) ss = true)
    (hbodyWF : ∀ ρ, initEnvWF params (.block l ss md) ρ → blockInitEnvWF bparams ss ρ)
    (hbodyDefs : ∀ ρ, initEnvWF params (.block l ss md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ss true, ρ.store x = none)
    (h : Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre ss Post)
    (hpost_proj : PostWF ss Post) :
    Triple (EventLang.imperativeE P CmdT evalCmd extendFactory
      ParamsTy initEnvWF) params Pre (.block l ss md) Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  obtain ⟨ρ_inner, hrun_inner, heq⟩ := stmt_block_reaches_doneE hrun
  have ⟨hvalid, hpost⟩ := h ρ₀ ρ_inner trace hpre (hbodyWF ρ₀ hinit) hrun_inner
  have hfac : ρ_inner.factory = ρ₀.factory :=
    block_noFuncDecl_preserves_factoryE ss ρ₀ ρ_inner hnofd hrun_inner
  have hproj : projectStore ρ₀.store ρ_inner.store
      = dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ_inner.store :=
    projectStore_eq_dropVarsE h_cmd (hbodyDefs ρ₀ hinit) hrun_inner
  subst heq
  refine ⟨hvalid, fun hf => ?_⟩
  have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store, factory := ρ₀.factory } : Env P) = { ρ_inner with store := dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ_inner.store } := by
    rw [hproj, ← hfac]
  rw [hrec]
  exact hpost_proj ρ_inner (hpost hf)

omit [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT] in
/-- **Singleton list.**  The converse of `block` for a one-element list: a triple at
    `EventLang.imperativeE` about `s` becomes one at `EventLang.imperativeBlockE` about
    `[s]`.  Every statement-shaped rule reaches the list judgement through this.

    `hstmtWF` lowers the block condition on `[s]` to the statement condition on `s`. -/
theorem singleton (params : ParamsTy)
    {s : Stmt P CmdT}
    {Pre Post : Env P → Prop}
    (hstmtWF : ∀ ρ, blockInitEnvWF bparams [s] ρ → initEnvWF params s ρ)
    (h : Triple (EventLang.imperativeE P CmdT evalCmd extendFactory
      ParamsTy initEnvWF) params Pre s Post) :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre [s] Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  rcases hrun with hterm | ⟨label, hexit⟩
  · rcases stmts_cons_headE evalCmd extendFactory hterm with hinitial | hseq
    · simp at hinitial
    · obtain ⟨ρ₁, headTrace, tailTrace, htrace, hhead, htail⟩ :=
        seq_reaches_terminalE evalCmd extendFactory hseq
      obtain ⟨htailTrace, htailCfg⟩ := stmts_nil_runE evalCmd extendFactory htail
      subst htailTrace
      rcases htailCfg with hcfg | hcfg
      · simp at hcfg
      · cases hcfg
        rw [htrace, List.append_nil]
        exact h ρ₀ ρ' headTrace hpre (hstmtWF ρ₀ hinit) (.inl hhead)
  · rcases stmts_cons_headE evalCmd extendFactory hexit with hinitial | hseq
    · simp at hinitial
    · rcases seq_reaches_exitingE evalCmd extendFactory hseq with hhead | htail
      · exact h ρ₀ ρ' trace hpre (hstmtWF ρ₀ hinit) (.inr ⟨label, hhead⟩)
      · obtain ⟨ρ₁, headTrace, tailTrace, htrace, hhead, htailRun⟩ := htail
        obtain ⟨_, htailCfg⟩ := stmts_nil_runE evalCmd extendFactory htailRun
        rcases htailCfg with hcfg | hcfg <;> simp at hcfg

/-- Empty block is skip.  No well-formedness side condition: `skip_block` holds
    at *every* block condition, so this instantiates it at the trivial one. -/
theorem skip (params : ParamsTy)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (l : String) (md : MetaData P) (Pre : Env P → Prop) :
    Triple (EventLang.imperativeE P CmdT evalCmd extendFactory
      ParamsTy initEnvWF) params Pre (.block l [] md) Pre :=
  block evalCmd extendFactory initEnvWF (fun (_ : Unit) _ _ => True) () params
    h_cmd (by simp [Block.noFuncDecl]) (fun _ _ => trivial)
    (fun _ _ x hx => absurd hx (by simp))
    (skip_block evalCmd extendFactory (fun (_ : Unit) _ _ => True) () Pre)
    (postWF_of_definedVars_nil Pre (by simp))

/-- If-then-else rule.  `hthenWF`/`helseWF` lower the statement condition on the
    `ite` to the block condition on each branch. -/
theorem ite (params : ParamsTy)
    {cond : P.Expr} {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hnofd : Stmt.noFuncDecl (P := P) (C := CmdT) (.ite (.det cond) tss ess md) = true)
    (hthenWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      blockInitEnvWF bparams tss ρ)
    (helseWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      blockInitEnvWF bparams ess ρ)
    (hthenDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) tss true, ρ.store x = none)
    (helseDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ess true, ρ.store x = none)
    (ht : Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some HasBool.tt) tss Post)
    (he : Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some HasBool.ff) ess Post)
    (hthen_proj : PostWF tss Post) (helse_proj : PostWF ess Post) :
    Triple (EventLang.imperativeE P CmdT evalCmd extendFactory
      ParamsTy initEnvWF) params Pre (.ite (.det cond) tss ess md) Post := by
  intro ρ₀ ρ' trace hpre hinit hrun
  have hnofd' : Block.noFuncDecl (P := P) (C := CmdT) tss = true ∧
      Block.noFuncDecl (P := P) (C := CmdT) ess = true := by
    simpa only [Stmt.noFuncDecl, Bool.and_eq_true] using hnofd
  -- Both branches, and both ways the `ite`'s block finishes, reduce to the same
  -- shape: the taken branch ran to terminal-or-exiting and the block projected.
  have hbranch : ∀ (bss : List (Stmt P CmdT)) (Pre' : Env P → Prop) (tr : Trace P),
      Pre' ρ₀ → blockInitEnvWF bparams bss ρ₀ →
      Block.noFuncDecl (P := P) (C := CmdT) bss = true →
      (∀ x ∈ Block.definedVars (P := P) (C := CmdT) bss true, ρ₀.store x = none) →
      PostWF bss Post →
      Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
        ⟨BParamsTy, blockInitEnvWF⟩) bparams Pre' bss Post →
      (StepStmtStarE P evalCmd extendFactory
          (.block .none ρ₀.store ρ₀.factory (.stmts bss ρ₀)) tr (.terminal ρ') ∨
       ∃ lbl, StepStmtStarE P evalCmd extendFactory
          (.block .none ρ₀.store ρ₀.factory (.stmts bss ρ₀)) tr (.exiting lbl ρ')) →
      Trace.AssertionsValid P I tr ∧ (Trace.Reachable P I tr → Post ρ') := by
    intro bss Pre' tr hpre' hbwf hbnofd hbdefs hbproj hb hdone_b
    obtain ⟨ρ_inner, hrun_inner, heq⟩ := block_reaches_doneE hdone_b
    have ⟨hvalid, hpost⟩ := hb ρ₀ ρ_inner tr hpre' hbwf hrun_inner
    have hfac : ρ_inner.factory = ρ₀.factory :=
      block_noFuncDecl_preserves_factoryE bss ρ₀ ρ_inner hbnofd hrun_inner
    have hproj : projectStore ρ₀.store ρ_inner.store
        = dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store :=
      projectStore_eq_dropVarsE h_cmd hbdefs hrun_inner
    subst heq
    refine ⟨hvalid, fun hf => ?_⟩
    have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store, factory := ρ₀.factory } : Env P) = { ρ_inner with store := dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store } := by
      rw [hproj, ← hfac]
    rw [hrec]
    exact hbproj ρ_inner (hpost hf)
  rcases hrun with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_ite_true hc _ =>
          exact hbranch tss _ _ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit) hnofd'.1
            (hthenDefs ρ₀ hinit) hthen_proj ht (.inl (by simpa using hrest))
        | step_ite_false hc _ =>
          exact hbranch ess _ _ ⟨hpre, hc⟩ (helseWF ρ₀ hinit) hnofd'.2
            (helseDefs ρ₀ hinit) helse_proj he (.inl (by simpa using hrest))
  · cases hexit with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_ite_true hc _ =>
          exact hbranch tss _ _ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit) hnofd'.1
            (hthenDefs ρ₀ hinit) hthen_proj ht (.inr ⟨lbl, by simpa using hrest⟩)
        | step_ite_false hc _ =>
          exact hbranch ess _ _ ⟨hpre, hc⟩ (helseWF ρ₀ hinit) hnofd'.2
            (helseDefs ρ₀ hinit) helse_proj he (.inr ⟨lbl, by simpa using hrest⟩)

/-- **While rule.**  An invariant that the body re-establishes on every iteration
    holds when the loop finishes, however many iterations it took.

    `hbody` is that obligation: from the invariant *and* a true guard, one run of `body`
    ends in the invariant again.  `hcov` says every `exit` in the body is caught inside
    it, so an iteration cannot jump out of the loop; and `hInv_proj` says the invariant
    survives leaving the body's block, whose store projection would otherwise be free to
    drop it.  The two `…WF` conditions lower the loop's own well-formedness condition to
    the body and re-establish it after an iteration.

    The conclusion is the invariant *together with a false guard* — the loop only
    finishes by failing its guard.  Every completed trace also has valid assertions.
    Partial correctness, so a loop that never terminates satisfies any conclusion. -/
theorem while_rule (params : ParamsTy)
    {guard : P.Expr} {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hnofd : Block.noFuncDecl (P := P) (C := CmdT) body = true)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner tr, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      StepStmtStarE P evalCmd extendFactory (.stmts body ρ) tr (.terminal ρ_inner) →
      initEnvWF params (.loop (.det guard) measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store, factory := ρ.factory })
    (hbody : Triple (EventLang.imperativeBlockE P CmdT evalCmd extendFactory
      ⟨BParamsTy, blockInitEnvWF⟩) bparams
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some HasBool.tt) body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv) :
    Triple (EventLang.imperativeE P CmdT evalCmd extendFactory
      ParamsTy initEnvWF) params Inv (.loop (.det guard) measure inv body md)
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some HasBool.ff) := by
  intro ρ₀ ρ' trace hInv hinit hrun
  rcases hrun with hterm | ⟨lbl, hexit⟩
  · exact while_genE evalCmd extendFactory initEnvWF blockInitEnvWF bparams params
      h_cmd hnofd hbodyDefs hloopBodyWF hloopWF hbody hcov hInv_proj
      ρ₀ ρ' trace _ hInv hinit (reflTransTrace_to_T hterm) (Nat.le_refl _)
  · -- a loop's only exits are its body's, which `hcov` catches, so it never exits.
    exact absurd hexit (exitsCoveredByBlocks_noEscapeE evalCmd extendFactory
      (.loop (.det guard) measure inv body md) hcov ρ₀ lbl ρ')

end StructuredRules

end StmtRules

end Imperative.Logic.Hoare

end -- public section
