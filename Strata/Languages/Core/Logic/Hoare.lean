/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.LangDefProps
public import Strata.DL.Imperative.Logic.HoareTemplate
import all Strata.Languages.Core.Logic.LangDefProps
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Imperative.Logic.HoareTemplate
import all Strata.DL.Imperative.StmtSemanticsProps

/-! # Hoare Logic for Core

The structural Hoare rules of `Imperative.Logic.Hoare`, instantiated for Core directly
over its own language of statement lists, `Lang.coreBlock`: there is a single
judgement, `Triple`, conditioned on `Core.Logic.BlockInitEnvWF`.

## Contents

`Triple`, and the rules `false_pre`, `consequence`, `cmd`, `set`, `init`, `seq`,
`exit_cons`, `block`, `skip`, `ite` and `while_rule`.

## Why the rules are here and not in a `HoareProps` module

As in `Strata.DL.Imperative.Logic.HoareTemplate`: the rules below *are* the logic rather than
properties of it, so they stay with the judgements they introduce.  What does live
separately is the *contract reading* — `Strata.Languages.Core.Logic.ContractToHoareTriple`
for its definitions, and `…ContractToHoareTripleProps` for the ways to discharge them.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare

variable (π : String → Option Procedure)
variable (φ : Expression.Factory → PureFunc Expression → Expression.Factory)

/-! ## The Core triple -/

/-- **Core Hoare triple** over statement lists. -/
@[expose] def Triple (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (ss : Statements)
    (Post : Imperative.Env Expression → Prop) : Prop :=
  Strata.Logic.Hoare.Triple (Lang.coreBlock π φ) params Pre ss Post

/-! ## Parametric rules -/

/-- False precondition proves anything. -/
theorem false_pre (params : InitEnvWFParams) (ss : Statements)
    (Post : Imperative.Env Expression → Prop) :
    Triple π φ params (fun _ => False) ss Post :=
  Strata.Logic.Hoare.false_pre (Lang.coreBlock π φ) params ss Post

/-- Consequence (weakening): strengthen the precondition, weaken the
    postcondition. -/
theorem consequence (params : InitEnvWFParams)
    {Pre Pre' Post Post' : Imperative.Env Expression → Prop} {ss : Statements}
    (h : Triple π φ params Pre ss Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple π φ params Pre' ss Post' :=
  Strata.Logic.Hoare.consequence (Lang.coreBlock π φ) params h hpre hpost

/-! ## Rules for a single command -/

/-- A generic single Core command.  `h` receives the full `InitEnvWF params (.cmd c) ρ₀`,
    including the `WellFormedSemanticEval` bundle that `EvalCommand` needs. -/
theorem cmd (params : InitEnvWFParams) (c : Command)
    (Pre Post : Imperative.Env Expression → Prop)
    (h : ∀ ρ₀ σ' f, Pre ρ₀ → InitEnvWF params (.cmd c) ρ₀ →
      EvalCommand π φ ρ₀.factory ρ₀.store c σ' f →
      Post { ρ₀ with store := σ', hasFailure := f } ∧ f = Bool.false) :
    Triple π φ params Pre [.cmd c] Post :=
  Imperative.Logic.Hoare.singleton (EvalCommand π φ) (EvalPureFunc φ)
    coreIsAtAssert InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.cmd (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
      InitEnvWF params c Pre Post h)

/-- Assignment.  The value written is quantified inside `hpost`, next to the evaluation
    that produced it: which value `e` takes depends on the environment, so fixing one
    outside would demand that `Pre` determine it. -/
theorem set (params : InitEnvWFParams)
    (x : Expression.Ident) (e : Expression.Expr)
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Expr),
      Pre ρ₀ → Expression.eval ρ₀.factory ρ₀.store e = some v →
      Imperative.UpdateState Expression ρ₀.store x v σ' →
      Post { ρ₀ with store := σ', hasFailure := Bool.false }) :
    Triple π φ params Pre [Statement.set x e md] Post := by
  refine cmd π φ params _ Pre Post (fun ρ₀ σ' f hpre _hwf hstep => ?_)
  cases hstep with
  | cmd_sem hcmd =>
    cases hcmd with
    | eval_set hev hup _hvar => exact ⟨hpost ρ₀ σ' _ hpre hev hup, rfl⟩

/-- Declaration.  `InitState` differs from `UpdateState` only in requiring the slot to
    have been undefined beforehand, which the postcondition never inspects. -/
theorem init (params : InitEnvWFParams)
    (x : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr)
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Expr),
      Pre ρ₀ → Expression.eval ρ₀.factory ρ₀.store e = some v →
      Imperative.InitState Expression ρ₀.store x v σ' →
      Post { ρ₀ with store := σ', hasFailure := Bool.false }) :
    Triple π φ params Pre [Statement.init x ty (.det e) md] Post := by
  refine cmd π φ params _ Pre Post (fun ρ₀ σ' f hpre _hwf hstep => ?_)
  cases hstep with
  | cmd_sem hcmd =>
    cases hcmd with
    | eval_init hev hinit _hvar => exact ⟨hpost ρ₀ σ' _ hpre hev hinit, rfl⟩


/-! ## Structural rules -/

/-- Sequencing: glue two triples along the concatenation of their statement lists.
    `hnofd` keeps the factory constant across the prefix's run, which is what lets the
    well-formedness condition be re-established on the suffix; see
    `Imperative.Logic.Hoare.seq_append` for why `hnoesc` is needed. -/
theorem seq (params : InitEnvWFParams)
    {ss₁ ss₂ : Statements}
    {Pre Mid Post : Imperative.Env Expression → Prop}
    (hnofd : Block.noFuncDecl (P := Expression) (C := Command) ss₁ = Bool.true)
    (h₁ : Triple π φ params Pre ss₁ Mid)
    (h₂ : Triple π φ params Mid ss₂ Post)
    (hnoesc : Imperative.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] ss₁) :
    Triple π φ params Pre (ss₁ ++ ss₂) Post :=
  Imperative.Logic.Hoare.seq_append (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
    BlockInitEnvWF params
    (fun _ hb => blockInitEnvWF_append_head hb)
    (fun _ _ hb hr => blockInitEnvWF_append_tail π φ hnofd hb
      (Core.StepStmtStar_to_CoreStepStar hr))
    h₁ h₂ hnoesc

/-- An `exit` ends the statement list where it stands, leaving the
    environment untouched, so the precondition survives to the exiting configuration.
    The statements after it never run.  An enclosing `block` catches the exit. -/
theorem exit_cons (params : InitEnvWFParams) {lbl : String}
    {md : Imperative.MetaData Expression} {ss : Statements}
    (Pre : Imperative.Env Expression → Prop) :
    Triple π φ params Pre (.exit lbl md :: ss) Pre :=
  Imperative.Logic.Hoare.exit_cons (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
    BlockInitEnvWF params

/-- Wrap a statement list in a labelled block.  `Post` must not mention the names the
    body scopes (`PostWF`), and `hnofd` keeps the factory constant across the body, so
    leaving the block restores nothing. -/
theorem block (params : InitEnvWFParams)
    {ss : Statements} {l : String} {md : Imperative.MetaData Expression}
    {Pre Post : Imperative.Env Expression → Prop}
    (hnofd : Block.noFuncDecl (P := Expression) (C := Command) ss = Bool.true)
    (h : Triple π φ params Pre ss Post)
    (hpost_proj : Imperative.Logic.Hoare.PostWF ss Post) :
    Triple π φ params Pre [.block l ss md] Post :=
  Imperative.Logic.Hoare.singleton (EvalCommand π φ) (EvalPureFunc φ)
    coreIsAtAssert InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.block (EvalCommand π φ) (EvalPureFunc φ)
      coreIsAtAssert InitEnvWF BlockInitEnvWF params params (fun he hn hnd => evalCommand_preserves_none_of_not_def π φ he hn hnd) hnofd
      (fun _ hb => blockInitEnvWF_of_block hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_block hb))
      h hpost_proj)

/-- Empty block is skip.  No lowering condition: the generic rule instantiates
    `skip_block` at the trivial block condition. -/
theorem skip (params : InitEnvWFParams) (l : String) (md : Imperative.MetaData Expression)
    (Pre : Imperative.Env Expression → Prop) :
    Triple π φ params Pre [.block l [] md] Pre :=
  Imperative.Logic.Hoare.singleton (EvalCommand π φ) (EvalPureFunc φ)
    coreIsAtAssert InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.skip (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
      InitEnvWF params (fun he hn hnd => evalCommand_preserves_none_of_not_def π φ he hn hnd) l md Pre)

/-- If-then-else rule. -/
theorem ite (params : InitEnvWFParams)
    {cond : Expression.Expr} {tss ess : Statements} {md : Imperative.MetaData Expression}
    {Pre Post : Imperative.Env Expression → Prop}
    (hnofd : Imperative.Stmt.noFuncDecl (P := Expression) (C := Command)
      (.ite (.det cond) tss ess md) = Bool.true)
    (ht : Triple π φ params
      (fun ρ => Pre ρ ∧ Expression.eval ρ.factory ρ.store cond = some HasBool.tt) tss Post)
    (he : Triple π φ params
      (fun ρ => Pre ρ ∧ Expression.eval ρ.factory ρ.store cond = some HasBool.ff) ess Post)
    (hthen_proj : Imperative.Logic.Hoare.PostWF tss Post)
    (helse_proj : Imperative.Logic.Hoare.PostWF ess Post) :
    Triple π φ params Pre [.ite (.det cond) tss ess md] Post :=
  Imperative.Logic.Hoare.singleton (EvalCommand π φ) (EvalPureFunc φ)
    coreIsAtAssert InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.ite (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
      InitEnvWF BlockInitEnvWF params params (fun he hn hnd => evalCommand_preserves_none_of_not_def π φ he hn hnd) hnofd
      (fun _ hb => blockInitEnvWF_of_ite_then hb)
      (fun _ hb => blockInitEnvWF_of_ite_else hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_then hb))
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_else hb))
      ht he hthen_proj helse_proj)

/-- While rule.  `hcov` says the body's `exit`s are all caught inside the body,
    and `hInv_proj` that the invariant survives the body block's store
    projection. -/
theorem while_rule (params : InitEnvWFParams)
    {guard : Expression.Expr} {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : Imperative.MetaData Expression}
    {Inv : Imperative.Env Expression → Prop}
    (hnofd : Block.noFuncDecl (P := Expression) (C := Command) body = Bool.true)
    (hbody : Triple π φ params
      (fun ρ => Inv ρ ∧ Expression.eval ρ.factory ρ.store guard = some HasBool.tt) body Inv)
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] body)
    (hInv_proj : Imperative.Logic.Hoare.PostWF body Inv) :
    Triple π φ params Inv [.loop (.det guard) measure inv body md]
      (fun ρ => Inv ρ ∧ Expression.eval ρ.factory ρ.store guard = some HasBool.ff) :=
  Imperative.Logic.Hoare.singleton (EvalCommand π φ) (EvalPureFunc φ)
    coreIsAtAssert InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.while_rule (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
      InitEnvWF BlockInitEnvWF params params (fun he hn hnd => evalCommand_preserves_none_of_not_def π φ he hn hnd) hnofd
      (fun _ hl => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_loop_body hl))
      (fun _ hl => blockInitEnvWF_of_loop_body hl)
      (fun _ _ hl hr => initEnvWF_loop_iterate π φ hnofd hl
        (Core.StepStmtStar_to_CoreStepStar hr))
      hbody hcov hInv_proj)

end Hoare

end Core.Logic

end -- public section

