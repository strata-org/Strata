/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.Termination
public import Strata.DL.Imperative.Logic.TraceInterpProps
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.Analysis.Assertions

/-! # A Hoare-logic template for the Imperative dialect

Note: This module is a *template*, not a Hoare logic for a language: `Imperative` fixes no
command type and no evaluator, so nothing here can be applied to a program.  A language
instantiates it — see `Strata.Languages.Core.Logic.Hoare` — to obtain usable rules.

A self-contained partial-correctness Hoare logic, depending only on the Imperative dialect
itself (`Stmt`, `Cmd`, their event-trace small-step semantics, and the
`Strata.Logic.EventLang` bundle). It does not mention the transformation-soundness
framework (`AssertValidityPreservedWhen`, or the `OverapproximatesTraces` family); the
event-trace transport bridge lives on its side, in `Strata.Transform.SpecHoareConnection`.

`Strata.Logic.Hoare.TripleWith` is language-agnostic — stated over an arbitrary
`Strata.Logic.EventLang P (Event P)` and condition interpreter, which is what lets a
triple be transported from a target language back to the source. Everything else lives
in `Imperative.Logic.Hoare`.

## Assertions on runs that do not finish

The triple checks the assertions of every finite execution, finished or not, as
`Imperative.Specification.AllAssertsValidOnTracesWhen` does: with the trivial postcondition it
is that property (`TripleWith.true_iff_allAssertsValidOnTracesWhen`).  So
`{True} assert false; while (true) {} {Q}` holds for no `Q`, although the program never
finishes.  The postcondition is still owed only by finished runs, so a loop that never
terminates meets every postcondition once its assertions hold.

## Contents

`Strata.Logic.Hoare.TripleWith`, `TripleWith.run`,
`TripleWith.true_iff_allAssertsValidOnTracesWhen`, and `PostWF`, with the rules `false_pre`,
`consequence`, `skip_block`, `cmd`, `seq_append`, `exit_cons`, `block`, `singleton`, `skip`,
`ite`, and `while_rule`.

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

section HoareRules

variable {P : Imperative.PureExpr}
variable {conditionInterp : Imperative.ConditionInterp P}

namespace Strata.Logic.Hoare

open Imperative

section

variable (L : EventLang P (Event P))

/-- Partial-correctness Hoare triple: for every initial environment satisfying `Pre` that the
    language's own `initEnvWF` admits, every assertion of every finite execution of `s` is
    valid, and every execution that finishes at `ρ'` along a reachable trace ends in an
    environment satisfying `Post`.

    The first part reads every finite execution, finished or not, so it also covers
    executions that diverge or get stuck: `{True} (assert false; loop_forever) {anything}`
    does not hold.  With the trivial postcondition, the triple is
    `Imperative.Specification.AllAssertsValidOnTracesWhen` over the admitted entries
    (`TripleWith.true_iff_allAssertsValidOnTracesWhen`).

    `L.initEnvWF params` is the initial-environment well-formedness condition: the
    triple only constrains runs started from an environment the condition admits, and it
    is *antimonotone* in that condition — a triple proved under a weaker one holds under
    any stronger one.

    A run may finish terminal or exiting (`L.TerminatesAt`): `s` may be a statement list whose
    `exit` escapes, or a statement that is itself an `exit`, and in either case an
    enclosing block would catch it and continue — so the postcondition has to hold
    there too.  Constraining only terminal runs would make `{Pre} exit l {Post}`
    vacuous for every `Post`.

    The total-correctness counterpart is `Strata.Logic.HoareTotal.TripleWith`, in
    `Strata.DL.Imperative.Logic.HoareTotalTemplate`. -/
@[expose] def TripleWith (conditionInterp : ConditionInterp P)
    (params : L.InitEnvWFParamsTy)
    (Pre : Env P → Prop) (s : L.StmtT) (Post : Env P → Prop) : Prop :=
  ∀ ρ₀, Pre ρ₀ → L.initEnvWF params s ρ₀ →
    (∀ (cfg : L.CfgT) (trace : Trace P), L.traceStar (L.stmtCfg s ρ₀) trace cfg →
      Trace.AssertionsValid P conditionInterp trace) ∧
    (∀ (ρ' : Env P) (trace : Trace P), L.TerminatesAt s ρ₀ trace ρ' →
      Trace.Reachable P conditionInterp trace → Post ρ')

end

variable {L : EventLang P (Event P)}

/-- A finished run of a triple's statement from an admitted entry satisfying the
    precondition has valid assertions, and ends in the postcondition when its trace is
    reachable. -/
theorem TripleWith.run {params : L.InitEnvWFParamsTy} {Pre Post : Env P → Prop}
    {s : L.StmtT} (h : TripleWith L conditionInterp params Pre s Post)
    (ρ₀ ρ' : Env P) (trace : Trace P) (hpre : Pre ρ₀) (hinit : L.initEnvWF params s ρ₀)
    (hrun : L.TerminatesAt s ρ₀ trace ρ') :
    Trace.AssertionsValid P conditionInterp trace ∧
      (Trace.Reachable P conditionInterp trace → Post ρ') := by
  obtain ⟨hvalid, hpost⟩ := h ρ₀ hpre hinit
  refine ⟨?_, hpost ρ' trace hrun⟩
  rcases hrun with hrun | ⟨_, hrun⟩ <;> exact hvalid _ _ hrun

/-- **A triple with the trivial postcondition is validity of every assertion on every finite
    execution** from the admitted entries satisfying the precondition. -/
theorem TripleWith.true_iff_allAssertsValidOnTracesWhen {params : L.InitEnvWFParamsTy}
    {Pre : Env P → Prop} {s : L.StmtT} :
    TripleWith L conditionInterp params Pre s (fun _ => True) ↔
      Imperative.Specification.AllAssertsValidOnTracesWhen L conditionInterp
        (fun ρ => Pre ρ ∧ L.initEnvWF params s ρ) s :=
  ⟨fun h ρ₀ cfg trace ⟨hpre, hinit⟩ hrun => (h ρ₀ hpre hinit).1 cfg trace hrun,
    fun h ρ₀ hpre hinit =>
      ⟨fun cfg trace hrun => h ρ₀ cfg trace ⟨hpre, hinit⟩ hrun, fun _ _ _ _ => trivial⟩⟩

end Strata.Logic.Hoare

local notation "I" => conditionInterp
local notation "Triple" => fun L => Strata.Logic.Hoare.TripleWith L conditionInterp

namespace Strata.Logic.Hoare

open Imperative

variable (L : EventLang P (Event P))

/-! ## Rules that do not inspect the statement -/

/-- False precondition proves anything. -/
theorem false_pre (params : L.InitEnvWFParamsTy) (s : L.StmtT) (Post : Env P → Prop) :
    Triple L params (fun _ => False) s Post :=
  fun _ hpre => absurd hpre id

/-- Consequence (weakening): strengthen precondition, weaken postconditions. -/
theorem consequence (params : L.InitEnvWFParamsTy)
    {Pre Pre' Post Post' : Env P → Prop} {s : L.StmtT}
    (h : Triple L params Pre s Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple L params Pre' s Post' := by
  intro ρ₀ hpre' hinit
  obtain ⟨hvalid, hruns⟩ := h ρ₀ (hpre ρ₀ hpre') hinit
  exact ⟨hvalid, fun ρ' trace hrun hreach => hpost ρ' (hruns ρ' trace hrun hreach)⟩

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

variable [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P]
    [HasSubstFvar P] [HasInt P] [HasIntOps P]
variable {CmdT : Type}
variable (evalCmd : EvalCmdParamE P CmdT (Event P))
variable (initEnvWF : InitEnvWFParams P → Stmt P CmdT → Env P → Prop)
variable (blockInitEnvWF : InitEnvWFParams P → List (Stmt P CmdT) → Env P → Prop)
variable (bparams : InitEnvWFParams P)

omit [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [HasSubstFvar P] [HasInt P]
  [HasIntOps P] in
/-- The empty trace has valid assertions. -/
private theorem assertionsValid_nil : Trace.AssertionsValid P I [] := True.intro

/-- Empty statement list is skip.  Holds at every block condition: the empty list
    cannot step anywhere but its own terminal. -/
theorem skip_block (Pre : Env P → Prop) :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre [] Pre := by
  intro ρ₀ hpre _
  refine ⟨fun cfg trace hrun => ?_, fun ρ' trace hrun _ => ?_⟩
  · obtain ⟨rfl, _⟩ := stmts_nil_runE evalCmd hrun
    exact assertionsValid_nil
  rcases hrun with hterm | ⟨label, hexit⟩
  · obtain ⟨_, hcfg⟩ := stmts_nil_runE evalCmd hterm
    rcases hcfg with hcfg | hcfg
    · simp at hcfg
    · injection hcfg with hρ
      subst hρ
      exact hpre
  · obtain ⟨_, hcfg⟩ := stmts_nil_runE evalCmd hexit
    rcases hcfg with hcfg | hcfg <;> simp at hcfg

section
variable [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]

/-- Helper for `while_rule`: an iteration that terminates along a reachable trace, from an
    entry satisfying the invariant with a true guard that the loop's gate admits, ends at an
    entry satisfying the invariant that the loop's gate admits. -/
private theorem while_iterE
    {guard : P.Expr} {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop} (params : InitEnvWFParams P)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P}
      {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner tr, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      StepStmtStarE P evalCmd (.stmts body ρ) tr (.terminal ρ_inner) →
      initEnvWF params (.loop (.det guard) measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store })
    (hbody : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory)) body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv)
    {ρ ρ₁ : Env P} {tr : Trace P} (hInv : Inv ρ)
    (hwf : initEnvWF params (.loop (.det guard) measure inv body md) ρ)
    (hg : P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory))
    (hrun : StepStmtStarE P evalCmd (.block .none ρ.store (.stmts body ρ)) tr (.terminal ρ₁))
    (hreach : Trace.Reachable P I tr) :
    Inv ρ₁ ∧ initEnvWF params (.loop (.det guard) measure inv body md) ρ₁ := by
  obtain ⟨ρ_inner, hdisj, hρ₁⟩ := block_reaches_doneE (.inl hrun)
  have hbrun : StepStmtStarE P evalCmd (.stmts body ρ) tr (.terminal ρ_inner) := by
    rcases hdisj with hterm | ⟨lbl, hexit⟩
    · exact hterm
    · exact absurd hexit (stmts_exitsCoveredByBlocks_noEscapeE evalCmd body hcov ρ lbl ρ_inner)
  have hproj : projectStore ρ.store ρ_inner.store
      = dropVars (Block.definedVars (P := P) (C := CmdT) body true) ρ_inner.store :=
    projectStore_eq_dropVarsE h_cmd (hbodyDefs ρ hwf) (.inl hbrun)
  refine ⟨?_, ?_⟩
  · rw [hρ₁, hproj]
    exact hInv_proj ρ_inner ((hbody ρ ⟨hInv, hg⟩ (hloopBodyWF ρ hwf)).2 ρ_inner tr
      (.inl hbrun) hreach)
  · rw [hρ₁]
    exact hloopWF ρ ρ_inner tr hwf hbrun

/-- Helper for `while_rule`: the invariant survives arbitrarily many iterations of a run that
    finishes.  By strong induction on derivation length. -/
private theorem while_genE
    {guard : P.Expr} {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop} (params : InitEnvWFParams P)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner tr, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      StepStmtStarE P evalCmd (.stmts body ρ) tr (.terminal ρ_inner) →
      initEnvWF params (.loop (.det guard) measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store })
    (hbody : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory)) body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv)
    (ρ₀ ρ' : Env P) (trace : Trace P) (n : Nat)
    (hInv : Inv ρ₀)
    (hwf : initEnvWF params (.loop (.det guard) measure inv body md) ρ₀)
    (hrunT : ReflTransTraceT (StepStmtE P evalCmd)
      (.stmt (.loop (.det guard) measure inv body md) ρ₀) trace (.terminal ρ'))
    (hlen : hrunT.len ≤ n) :
    Trace.Reachable P I trace →
      Inv ρ' ∧ P.eval ρ'.factory ρ'.store guard = some (HasBool.ffVal ρ'.factory) := by
  induction n generalizing ρ₀ ρ' trace with
  | zero =>
    -- A run from a loop statement to a terminal takes at least one step.
    match hrunT, hlen with
    | .step _ _ _ _ _ _ _, hlen => simp only [ReflTransTraceT.len] at hlen; omega
  | succ n ih =>
    match hrunT, hlen with
    | .step _ _ _ restTr _ (.step_loop_exit hg) hrest, hlen =>
      -- guard false: the loop terminates immediately, emitting nothing.
      obtain ⟨hc, _⟩ := Imperative.stepStmtStarE_from_terminal (reflTransTraceT_to_prop hrest)
      injection hc with hρ
      subst hρ
      exact fun _ => ⟨hInv, hg⟩
    | .step _ _ _ restTr _ (.step_loop_enter hg) hrest, hlen =>
      -- one iteration: the body's block, then the loop again.
      simp only [List.nil_append]
      obtain ⟨ρ_mid, tr₁, tr₂, htr, h_block_term, h_loop_rest, hlen_seq⟩ :=
        seqT_reaches_terminalE hrest
      -- the loop tail `[loop]` reaches terminal; its `[]` continuation pins ρ' and tr.
      obtain ⟨ρ_x, tr_l, tr_nil, htr2, h_loop_head, h_nil, hlen_cons⟩ :=
        stmtsT_cons_terminalE h_loop_rest
      obtain ⟨htail_nil, htail_cfg⟩ := stmts_nil_runE evalCmd
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
      intro hfull
      obtain ⟨hInv_mid, hwf_mid⟩ := while_iterE evalCmd initEnvWF blockInitEnvWF bparams params
        h_cmd hbodyDefs hloopBodyWF hloopWF hbody hcov hInv_proj hInv hwf hg
        (reflTransTraceT_to_prop h_block_term) (Trace.Reachable.left_of_append I hfull)
      exact ih ρ_mid ρ' tr_l hInv_mid hwf_mid h_loop_head
        (by simp only [ReflTransTraceT.len] at hlen; omega)
        (Trace.Reachable.right_of_append I hfull)

/-- Helper for `while_rule`: every finite execution of the loop from an entry satisfying the
    invariant that the loop's gate admits has valid assertions.  By strong induction on
    derivation length: an execution is either still in an iteration's body, whose triple
    validates it, or past a finished iteration, whose trace is valid and, when reachable,
    leaves the invariant for the rest. -/
private theorem while_prefixE
    {guard : P.Expr} {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop} (params : InitEnvWFParams P)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P}
      {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner tr, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      StepStmtStarE P evalCmd (.stmts body ρ) tr (.terminal ρ_inner) →
      initEnvWF params (.loop (.det guard) measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store })
    (hbody : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory)) body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv) (n : Nat) :
    ∀ (ρ₀ : Env P) (cfg : Config P CmdT) (trace : Trace P)
      (hrunT : ReflTransTraceT (StepStmtE P evalCmd)
        (.stmt (.loop (.det guard) measure inv body md) ρ₀) trace cfg),
      hrunT.len ≤ n → Inv ρ₀ → initEnvWF params (.loop (.det guard) measure inv body md) ρ₀ →
      Trace.AssertionsValid P I trace := by
  induction n with
  | zero =>
    intro ρ₀ cfg trace hrunT hlen _ _
    match hrunT, hlen with
    | .refl _, _ => exact assertionsValid_nil
    | .step _ _ _ _ _ _ _, hlen => simp only [ReflTransTraceT.len] at hlen; omega
  | succ n ih =>
    intro ρ₀ cfg trace hrunT hlen hInv hwf
    match hrunT, hlen with
    | .refl _, _ => exact assertionsValid_nil
    | .step _ _ _ restTr _ (.step_loop_exit _) hrest, _ =>
      obtain ⟨_, hnil⟩ := Imperative.stepStmtStarE_from_terminal (reflTransTraceT_to_prop hrest)
      subst hnil
      exact assertionsValid_nil
    | .step _ _ _ restTr _ (.step_loop_enter hg) hrest, hlen =>
      simp only [List.nil_append]
      simp only [ReflTransTraceT.len] at hlen
      -- a finite execution of the iteration's block runs its body
      have hblock : ∀ tr c, StepStmtStarE P evalCmd
          (.block .none ρ₀.store (.stmts body ρ₀)) tr c → Trace.AssertionsValid P I tr := by
        intro tr c h
        obtain ⟨inner', h'⟩ := block_run_inner_prefixE h
        exact (hbody ρ₀ ⟨hInv, hg⟩ (hloopBodyWF ρ₀ hwf)).1 inner' tr h'
      rcases seqT_run_decomposeE hrest with
        ⟨_, _, h1, _⟩ | ⟨ρ₁, tr₁, tr₂, rfl, h1, h2, hlen2⟩ | ⟨_, _, _, h1, _⟩
      · exact hblock _ _ (reflTransTraceT_to_prop h1)
      · refine Trace.AssertionsValid.append_of_reachable_left I
          (hblock _ _ (reflTransTraceT_to_prop h1)) fun hreach => ?_
        obtain ⟨hInv₁, hwf₁⟩ := while_iterE evalCmd initEnvWF blockInitEnvWF bparams params
          h_cmd hbodyDefs hloopBodyWF hloopWF hbody hcov hInv_proj hInv hwf hg
          (reflTransTraceT_to_prop h1) hreach
        match h2, hlen2 with
        | .refl _, _ => exact assertionsValid_nil
        | .step _ _ _ _ _ .step_stmts_cons hrest2, hlen2 =>
          simp only [List.nil_append]
          simp only [ReflTransTraceT.len] at hlen2
          rcases seqT_run_decomposeE hrest2 with
            ⟨_, _, h1', hl'⟩ | ⟨ρ₂, tr₂₁, tr₂₂, rfl, h1', h2', hl'⟩ | ⟨_, _, _, h1', hl'⟩
          · exact ih ρ₁ _ _ h1' (by omega) hInv₁ hwf₁
          · obtain ⟨rfl, _⟩ := stmts_nil_runE evalCmd (reflTransTraceT_to_prop h2')
            simpa using ih ρ₁ _ _ h1' (by omega) hInv₁ hwf₁
          · exact ih ρ₁ _ _ h1' (by omega) hInv₁ hwf₁
      · exact hblock _ _ (reflTransTraceT_to_prop h1)

end

/-- **A single command.**  Whatever the command's own semantics establishes about the
    resulting store is the postcondition, provided its emitted assertions are valid and
    its emitted trace is reachable.

    `h` is that obligation: for every way the command can step from a `Pre`-environment
    the language admits, its trace is assertion-valid and, when reachable, the
    postcondition holds of the resulting store.  It receives the
    language's well-formedness condition unchanged, which is where an evaluator-based
    semantics finds what it needs to step at all. -/
theorem cmd (params : InitEnvWFParams P) (c : CmdT)
    (Pre Post : Env P → Prop)
    (h : ∀ ρ₀ σ' emitted,
      Pre ρ₀ → initEnvWF params (.cmd c) ρ₀ →
      evalCmd ρ₀.factory ρ₀.store c σ' emitted →
      Trace.AssertionsValid P I emitted ∧
        (Trace.Reachable P I emitted → Post { ρ₀ with store := σ' })) :
    Triple (EventLang.imperativeE P CmdT evalCmd
      initEnvWF) params Pre (.cmd c) Post := by
  intro ρ₀ hpre hinit
  refine ⟨fun cfg trace hrun => ?_, fun ρ' trace hrun hreach => ?_⟩
  · cases hrun with
    | refl => exact assertionsValid_nil
    | step _ emitted _ rest _ hstep htail =>
      cases hstep with
      | step_cmd hcmd =>
        obtain ⟨_, hrest⟩ := Imperative.stepStmtStarE_from_terminal htail
        subst hrest
        simpa using (h ρ₀ _ emitted hpre hinit hcmd).1
  rcases hrun with hterm | ⟨label, hexit⟩
  · cases hterm with
    | step _ emitted _ rest _ hstep htail =>
      cases hstep with
      | step_cmd hcmd =>
        obtain ⟨hcfg, hrest⟩ := Imperative.stepStmtStarE_from_terminal htail
        injection hcfg with hρ
        subst hρ
        subst hrest
        exact (h ρ₀ _ emitted hpre hinit hcmd).2 (by simpa using hreach)
  · cases hexit with
    | step _ emitted _ rest _ hstep htail =>
      cases hstep with
      | step_cmd _ =>
        obtain ⟨hcfg, _⟩ := Imperative.stepStmtStarE_from_terminal htail
        cases hcfg

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
      StepStmtStarE P evalCmd (.stmts ss₁ ρ) tr (.terminal ρ') →
      blockInitEnvWF bparams ss₂ ρ')
    (h₁ : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre ss₁ Mid)
    (h₂ : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Mid ss₂ Post)
    (hSs1NoExit : Block.exitsCoveredByBlocks [] ss₁) :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre (ss₁ ++ ss₂) Post := by
  intro ρ₀ hpre hinit
  obtain ⟨hvalid₁, hruns₁⟩ := h₁ ρ₀ hpre (hheadWF ρ₀ hinit)
  refine ⟨fun cfg trace hrun => ?_, fun ρ' trace hrun hreach => ?_⟩
  · -- a finite execution is one of the prefix, or a finished one of the prefix followed by
    -- one of the suffix
    rcases stmts_append_prefixE (EvalCmd := evalCmd) ss₁ ss₂ ρ₀ hrun with
      ⟨cfg', h'⟩ | ⟨ρ₁, tr₁, tr₂, rfl, hterm₁, cfg', htail⟩
    · exact hvalid₁ cfg' trace h'
    · refine Trace.AssertionsValid.append_of_reachable_left I (hvalid₁ _ _ hterm₁)
        fun hs => ?_
      exact (h₂ ρ₁ (hruns₁ ρ₁ tr₁ (.inl hterm₁) hs) (htailWF ρ₀ ρ₁ tr₁ hinit hterm₁)).1
        cfg' tr₂ htail
  · rcases stmts_append_doneE evalCmd ss₁ ss₂ ρ₀ ρ' hrun with
      ⟨lbl, hexit₁⟩ | ⟨ρ₁, tr₁, tr₂, rfl, hterm₁, htail⟩
    · -- the prefix cannot escape, so this case is impossible
      exact (stmts_exitsCoveredByBlocks_noEscapeE evalCmd ss₁ hSs1NoExit
        ρ₀ lbl ρ' hexit₁).elim
    · exact (h₂ ρ₁ (hruns₁ ρ₁ tr₁ (.inl hterm₁) (Trace.Reachable.left_of_append I hreach))
        (htailWF ρ₀ ρ₁ tr₁ hinit hterm₁)).2 ρ' tr₂ htail
        (Trace.Reachable.right_of_append I hreach)

omit [HasFvar P] [HasFvars P] [HasBoolOps P] [HasSubstFvar P] [HasInt P] [HasIntOps P] in
/-- A finite execution of an `exit` emits nothing and does not terminate normally. -/
private theorem exit_runE {lbl : String} {md : MetaData P} {ρ : Env P}
    {cfg : Config P CmdT} {tr : Trace P}
    (h : StepStmtStarE P evalCmd (.stmt (.exit lbl md) ρ) tr cfg) :
    tr = [] ∧ ∀ ρ', cfg ≠ .terminal ρ' := by
  cases h with
  | refl => exact ⟨rfl, fun _ hc => by cases hc⟩
  | step _ _ _ _ _ hstep hrest =>
    cases hstep with
    | step_exit =>
      obtain ⟨hc, rfl⟩ := stepStmtStarE_from_exiting hrest
      exact ⟨rfl, fun _ hc' => by rw [hc] at hc'; cases hc'⟩

/-- **Exit.**  An `exit` ends the statement list where it stands: the statements after
    it never run, and the environment is unchanged, so whatever held before the `exit`
    still holds at the exiting configuration.

    This is the rule `seq_append` cannot supply, since it requires its prefix not to
    escape, and it is what the exiting half of `Triple` exists for.  An enclosing `block`
    catches the exit and continues from the projected environment. -/
theorem exit_cons {lbl : String} {md : MetaData P} {ss : List (Stmt P CmdT)}
    {Pre : Env P → Prop} :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre (.exit lbl md :: ss) Pre := by
  intro ρ₀ hpre _hinit
  refine ⟨fun cfg trace hrun => ?_, fun ρ' trace hrun _ => ?_⟩
  · rcases stmts_cons_headE evalCmd hrun with ⟨_, rfl⟩ | hseq
    · exact assertionsValid_nil
    rcases seq_run_decomposeE evalCmd hseq with
      ⟨_, _, hs⟩ | ⟨ρ₁, _, _, _, hs, _⟩ | ⟨_, _, _, hs⟩
    · rw [(exit_runE evalCmd hs).1]; exact assertionsValid_nil
    · exact absurd rfl ((exit_runE evalCmd hs).2 ρ₁)
    · rw [(exit_runE evalCmd hs).1]; exact assertionsValid_nil
  rcases hrun with hterm | ⟨elbl, hexit⟩
  · rcases stmts_cons_headE evalCmd hterm with hinitial | hseq
    · simp at hinitial
    · obtain ⟨ρ₁, tr₁, tr₂, _, hhead, _⟩ :=
        seq_reaches_terminalE evalCmd hseq
      -- the head is an `exit`, so it reaches `.exiting`, never `.terminal`
      exact absurd rfl ((exit_runE evalCmd hhead).2 ρ₁)
  · rcases stmts_cons_headE evalCmd hexit with hinitial | hseq
    · simp at hinitial
    · rcases seq_reaches_exitingE evalCmd hseq with
        hhead | ⟨ρ₁, tr₁, tr₂, _, hterm_head, _⟩
      · -- the head exited: the label and environment are those of the `exit`
        cases hhead with
        | step _ _ _ _ _ hstep hrest =>
          cases hstep with
          | step_exit =>
            obtain ⟨hc, _⟩ := stepStmtStarE_from_exiting hrest
            injection hc with _ hρ
            subst hρ
            exact hpre
      · -- the head cannot terminate before exiting
        exact absurd rfl ((exit_runE evalCmd hterm_head).2 ρ₁)

section StructuredRules

variable [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT]

/-- **Block introduction.**  Wrap a statement list in a block: a triple at
    `EventLang.imperativeBlockE` about `ss` becomes one at `EventLang.imperativeE` about
    `.block l ss md`.
    `Post` must not mention the names the body scopes (`PostWF`).

    `hbodyWF` lowers the statement condition on `.block l ss md` to the block condition
    on the body `ss`, and `hbodyDefs` extracts from it that those names start undefined —
    which is what makes leaving the block a *drop*.  No statement step mutates the
    factory, so the exit restores nothing. -/
theorem block (params : InitEnvWFParams P)
    {ss : List (Stmt P CmdT)} {l : String} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyWF : ∀ ρ, initEnvWF params (.block l ss md) ρ → blockInitEnvWF bparams ss ρ)
    (hbodyDefs : ∀ ρ, initEnvWF params (.block l ss md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ss true, ρ.store x = none)
    (h : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre ss Post)
    (hpost_proj : PostWF ss Post) :
    Triple (EventLang.imperativeE P CmdT evalCmd
      initEnvWF) params Pre (.block l ss md) Post := by
  intro ρ₀ hpre hinit
  obtain ⟨hvalid, hruns⟩ := h ρ₀ hpre (hbodyWF ρ₀ hinit)
  refine ⟨fun cfg trace hrun => ?_, fun ρ' trace hrun hf => ?_⟩
  · obtain ⟨inner', h'⟩ := stmt_block_prefixE (EvalCmd := evalCmd) hrun
    exact hvalid inner' trace h'
  obtain ⟨ρ_inner, hrun_inner, heq⟩ := stmt_block_reaches_doneE hrun
  have hproj : projectStore ρ₀.store ρ_inner.store
      = dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ_inner.store :=
    projectStore_eq_dropVarsE h_cmd (hbodyDefs ρ₀ hinit) hrun_inner
  subst heq
  have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store } : Env P) = { ρ_inner with store := dropVars (Block.definedVars (P := P) (C := CmdT) ss true) ρ_inner.store } := by
    rw [hproj]
  rw [hrec]
  exact hpost_proj ρ_inner (hruns ρ_inner trace hrun_inner hf)

omit [HasIdent P] [DecidableEq P.Ident] [HasVarsImp P CmdT] in
/-- **Singleton list.**  The converse of `block` for a one-element list: a triple at
    `EventLang.imperativeE` about `s` becomes one at `EventLang.imperativeBlockE` about
    `[s]`.  Every statement-shaped rule reaches the list judgement through this.

    `hstmtWF` lowers the block condition on `[s]` to the statement condition on `s`. -/
theorem singleton (params : InitEnvWFParams P)
    {s : Stmt P CmdT}
    {Pre Post : Env P → Prop}
    (hstmtWF : ∀ ρ, blockInitEnvWF bparams [s] ρ → initEnvWF params s ρ)
    (h : Triple (EventLang.imperativeE P CmdT evalCmd
      initEnvWF) params Pre s Post) :
    Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams Pre [s] Post := by
  intro ρ₀ hpre hinit
  obtain ⟨hvalid, hruns⟩ := h ρ₀ hpre (hstmtWF ρ₀ hinit)
  refine ⟨fun cfg trace hrun => ?_, fun ρ' trace hrun hreach => ?_⟩
  · obtain ⟨cfg', h'⟩ := singleton_prefixE hrun
    exact hvalid cfg' trace h'
  · exact hruns ρ' trace (singletonRun_to_stmtRunE evalCmd hrun) hreach

/-- Empty block is skip.  No well-formedness side condition: `skip_block` holds
    at *every* block condition, so this instantiates it at the trivial one. -/
theorem skip (params : InitEnvWFParams P)
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (l : String) (md : MetaData P) (Pre : Env P → Prop) :
    Triple (EventLang.imperativeE P CmdT evalCmd
      initEnvWF) params Pre (.block l [] md) Pre :=
  block evalCmd initEnvWF (fun _ _ _ => True) params params
    h_cmd (fun _ _ => trivial)
    (fun _ _ x hx => absurd hx (by simp))
    (skip_block evalCmd (fun _ _ _ => True) params Pre)
    (postWF_of_definedVars_nil Pre (by simp))

/-- If-then-else rule.  `hthenWF`/`helseWF` lower the statement condition on the
    `ite` to the block condition on each branch. -/
theorem ite (params : InitEnvWFParams P)
    {cond : P.Expr} {tss ess : List (Stmt P CmdT)} {md : MetaData P}
    {Pre Post : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hthenWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      blockInitEnvWF bparams tss ρ)
    (helseWF : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      blockInitEnvWF bparams ess ρ)
    (hthenDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) tss true, ρ.store x = none)
    (helseDefs : ∀ ρ, initEnvWF params (.ite (.det cond) tss ess md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) ess true, ρ.store x = none)
    (ht : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some (HasBool.ttVal ρ.factory)) tss Post)
    (he : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams
      (fun ρ => Pre ρ ∧ P.eval ρ.factory ρ.store cond = some (HasBool.ffVal ρ.factory)) ess Post)
    (hthen_proj : PostWF tss Post) (helse_proj : PostWF ess Post) :
    Triple (EventLang.imperativeE P CmdT evalCmd
      initEnvWF) params Pre (.ite (.det cond) tss ess md) Post := by
  intro ρ₀ hpre hinit
  refine ⟨fun cfg trace hrun => ?_, fun ρ' trace hrun hf => ?_⟩
  · -- a finite execution runs the taken branch inside its block
    cases hrun with
    | refl => exact assertionsValid_nil
    | step _ _ _ rest _ hstep hrest =>
      cases hstep with
      | step_ite_true hc =>
        obtain ⟨inner', h'⟩ := block_run_inner_prefixE hrest
        simpa using (ht ρ₀ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit)).1 inner' rest h'
      | step_ite_false hc =>
        obtain ⟨inner', h'⟩ := block_run_inner_prefixE hrest
        simpa using (he ρ₀ ⟨hpre, hc⟩ (helseWF ρ₀ hinit)).1 inner' rest h'
  -- Both branches, and both ways the `ite`'s block finishes, reduce to the same
  -- shape: the taken branch ran to terminal-or-exiting and the block projected.
  have hbranch : ∀ (bss : List (Stmt P CmdT)) (Pre' : Env P → Prop) (tr : Trace P),
      Pre' ρ₀ → blockInitEnvWF bparams bss ρ₀ →
      (∀ x ∈ Block.definedVars (P := P) (C := CmdT) bss true, ρ₀.store x = none) →
      PostWF bss Post →
      Triple (EventLang.imperativeBlockE P CmdT evalCmd
        blockInitEnvWF) bparams Pre' bss Post →
      (StepStmtStarE P evalCmd
          (.block .none ρ₀.store (.stmts bss ρ₀)) tr (.terminal ρ') ∨
       ∃ lbl, StepStmtStarE P evalCmd
          (.block .none ρ₀.store (.stmts bss ρ₀)) tr (.exiting lbl ρ')) →
      Trace.Reachable P I tr → Post ρ' := by
    intro bss Pre' tr hpre' hbwf hbdefs hbproj hb hdone_b hf
    obtain ⟨ρ_inner, hrun_inner, heq⟩ := block_reaches_doneE hdone_b
    have hpost := (hb ρ₀ hpre' hbwf).2 ρ_inner tr hrun_inner hf
    have hproj : projectStore ρ₀.store ρ_inner.store
        = dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store :=
      projectStore_eq_dropVarsE h_cmd hbdefs hrun_inner
    subst heq
    have hrec : ({ ρ_inner with store := projectStore ρ₀.store ρ_inner.store } : Env P) = { ρ_inner with store := dropVars (Block.definedVars (P := P) (C := CmdT) bss true) ρ_inner.store } := by
      rw [hproj]
    rw [hrec]
    exact hbproj ρ_inner hpost
  rcases hrun with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_ite_true hc =>
        exact hbranch tss _ _ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit)
          (hthenDefs ρ₀ hinit) hthen_proj ht (.inl (by simpa using hrest)) (by simpa using hf)
      | step_ite_false hc =>
        exact hbranch ess _ _ ⟨hpre, hc⟩ (helseWF ρ₀ hinit)
          (helseDefs ρ₀ hinit) helse_proj he (.inl (by simpa using hrest)) (by simpa using hf)
  · cases hexit with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_ite_true hc =>
        exact hbranch tss _ _ ⟨hpre, hc⟩ (hthenWF ρ₀ hinit)
          (hthenDefs ρ₀ hinit) hthen_proj ht (.inr ⟨lbl, by simpa using hrest⟩)
          (by simpa using hf)
      | step_ite_false hc =>
        exact hbranch ess _ _ ⟨hpre, hc⟩ (helseWF ρ₀ hinit)
          (helseDefs ρ₀ hinit) helse_proj he (.inr ⟨lbl, by simpa using hrest⟩)
          (by simpa using hf)

/-- **While rule.**  An invariant that the body re-establishes on every iteration
    holds when the loop finishes, however many iterations it took.

    `hbody` is that obligation: from the invariant *and* a true guard, every finite execution
    of `body` has valid assertions, and one run of `body` ends in the invariant again.  `hcov`
    says every `exit` in the body is caught inside it, so an iteration cannot jump out of the
    loop; and `hInv_proj` says the invariant survives leaving the body's block, whose store
    projection would otherwise be free to drop it.  The two `…WF` conditions lower the loop's
    own well-formedness condition to the body and re-establish it after an iteration.

    The conclusion is the invariant *together with a false guard* — the loop only
    finishes by failing its guard.  Every finite execution of the loop, finished or not, has
    valid assertions.  Partial correctness, so a loop that never terminates owes no
    postcondition. -/
theorem while_rule (params : InitEnvWFParams P)
    {guard : P.Expr} {measure : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P CmdT)} {md : MetaData P}
    {Inv : Env P → Prop}
    (h_cmd : ∀ {f : P.Factory} {σ σ' : SemanticStore P} {c : CmdT} {emitted : Trace P} {y : P.Ident},
      evalCmd f σ c σ' emitted → σ y = none →
      y ∉ HasVarsImp.definedVars (P := P) c true → σ' y = none)
    (hbodyDefs : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      ∀ x ∈ Block.definedVars (P := P) (C := CmdT) body true, ρ.store x = none)
    (hloopBodyWF : ∀ ρ, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      blockInitEnvWF bparams body ρ)
    (hloopWF : ∀ ρ ρ_inner tr, initEnvWF params (.loop (.det guard) measure inv body md) ρ →
      StepStmtStarE P evalCmd (.stmts body ρ) tr (.terminal ρ_inner) →
      initEnvWF params (.loop (.det guard) measure inv body md)
        { ρ_inner with store := projectStore ρ.store ρ_inner.store })
    (hbody : Triple (EventLang.imperativeBlockE P CmdT evalCmd
      blockInitEnvWF) bparams
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory)) body Inv)
    (hcov : Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] body)
    (hInv_proj : PostWF body Inv) :
    Triple (EventLang.imperativeE P CmdT evalCmd
      initEnvWF) params Inv (.loop (.det guard) measure inv body md)
      (fun ρ => Inv ρ ∧ P.eval ρ.factory ρ.store guard = some (HasBool.ffVal ρ.factory)) := by
  intro ρ₀ hInv hinit
  refine ⟨fun cfg trace hrun => ?_, fun ρ' trace hrun hreach => ?_⟩
  · exact while_prefixE evalCmd initEnvWF blockInitEnvWF bparams params
      h_cmd hbodyDefs hloopBodyWF hloopWF hbody hcov hInv_proj _ ρ₀ cfg trace
      (reflTransTrace_to_T hrun) (Nat.le_refl _) hInv hinit
  rcases hrun with hterm | ⟨lbl, hexit⟩
  · exact while_genE evalCmd initEnvWF blockInitEnvWF bparams params
      h_cmd hbodyDefs hloopBodyWF hloopWF hbody hcov hInv_proj
      ρ₀ ρ' trace _ hInv hinit (reflTransTrace_to_T hterm) (Nat.le_refl _) hreach
  · -- a loop's only exits are its body's, which `hcov` catches, so it never exits.
    exact absurd hexit (exitsCoveredByBlocks_noEscapeE evalCmd
      (.loop (.det guard) measure inv body md) hcov ρ₀ lbl ρ')

end StructuredRules

end StmtRules

end Imperative.Logic.Hoare

end HoareRules

end -- public section
