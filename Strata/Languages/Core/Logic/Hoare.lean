/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.LangDefProps
public import Strata.DL.Imperative.Logic.HoareTemplate
public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
import all Strata.Languages.Core.Logic.LangDefProps
import all Strata.DL.Imperative.Logic.HoareTemplate

/-! # Hoare Logic for Core

The structural Hoare rules of `Imperative.Logic.Hoare`, instantiated for Core directly
over its own language of statement lists, `EventLang.coreBlock`: there is a single
judgement, `Triple`, conditioned on `Core.Logic.BlockInitEnvWF`.

## Contents

`Triple`, and the rules `false_pre`, `consequence`, `of_storeWF_pre`,
`of_forall_entryFactory`, `cmd`, `set`, `init`, `init_nondet`, `havoc`, `assume`,
`assume_eval`, `assert`, `assert_eval`, `seq`, `exit_cons`, `block`, `skip`, `ite`
and `while_rule`.

## Why the rules are here and not in a `HoareProps` module

As in `Strata.DL.Imperative.Logic.HoareTemplate`: the rules below *are* the logic rather than
properties of it, so they stay with the judgements they introduce.  What does live
separately is the contract integration: `ContractToHoareTriple` defines the
contract reading, `ContractToHoareTripleProps` discharges it, and `HoareCall`
provides the rule for procedure calls.

The denotational domain of Core `real` is `Strata.Util.Real`, inherited from
`Lambda.SortDenote`, so these Hoare judgements state correctness over the real
numbers.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare

variable (π : String → Option Procedure)
variable {factory : Lambda.Factory CoreLParams}

/-! ## The Core triple -/

/-- Core Hoare triple with an explicit event-condition interpretation. -/
@[expose] def TripleWith (conditionInterp : ConditionInterp Expression)
    (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (ss : Statements)
    (Post : Imperative.Env Expression → Prop) : Prop :=
  Strata.Logic.Hoare.TripleWith (EventLang.coreBlock π)
    conditionInterp params Pre ss Post

/-- **Core Hoare triple** over statement lists, with conditions read by evaluation in
    runtime factories over `factory` (`DenoteBasedInterp factory`). A runtime factory
    carries a model of `factory`, so the triple covers every model through the entry
    environments it quantifies over. The default is `Core.Factory`; program-level
    clients can supply the factory visible at a particular declaration. -/
@[expose] def Triple (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (ss : Statements)
    (Post : Imperative.Env Expression → Prop)
    (factory : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  TripleWith π (DenoteBasedInterp factory) params Pre ss Post

/-! ## Parametric rules -/

/-- False precondition proves anything. -/
theorem false_pre (params : InitEnvWFParams) (ss : Statements)
    (Post : Imperative.Env Expression → Prop) :
    Triple π params (fun _ => False) ss Post (factory := factory) := by
  exact Strata.Logic.Hoare.false_pre (EventLang.coreBlock π) params ss Post

/-- Consequence (weakening): strengthen the precondition, weaken the
    postcondition. -/
theorem consequence (params : InitEnvWFParams)
    {Pre Pre' Post Post' : Imperative.Env Expression → Prop} {ss : Statements}
    (h : Triple π params Pre ss Post (factory := factory))
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple π params Pre' ss Post' (factory := factory) := by
  exact Strata.Logic.Hoare.consequence (EventLang.coreBlock π) params h hpre hpost

/-- A triple whose precondition also requires a well-formed entry store holds without that
    requirement: the gate of every admitted entry gives it. -/
theorem of_storeWF_pre (params : InitEnvWFParams)
    {Pre Post : Imperative.Env Expression → Prop} {ss : Statements}
    (h : Triple π params (fun ρ => Pre ρ ∧ Imperative.WellFormedStore ρ.store ρ.factory) ss
      Post (factory := factory)) :
    Triple π params Pre ss Post (factory := factory) :=
  fun ρ₀ ρ' tr hpre hinit hrun => h ρ₀ ρ' tr ⟨hpre, hinit.storeWellDefined⟩ hinit hrun

/-- A triple holds when it holds, for every runtime factory `E`, from the entries whose
    runtime factory is `E`. -/
theorem of_forall_entryFactory (params : InitEnvWFParams)
    {Pre Post : Imperative.Env Expression → Prop} {ss : Statements}
    (h : ∀ E, Triple π params (fun ρ => Pre ρ ∧ ρ.factory = E) ss Post (factory := factory)) :
    Triple π params Pre ss Post (factory := factory) :=
  fun ρ₀ ρ' tr hpre hinit hrun => h ρ₀.factory ρ₀ ρ' tr ⟨hpre, rfl⟩ hinit hrun

/-! ## Rules for a single command -/

/-- A generic single Core command.  `h` receives the full `InitEnvWF params (.cmd c) ρ₀`,
    including the `WellFormedSemanticEval` bundle that `EvalCommandE` needs. -/
theorem cmd (params : InitEnvWFParams) (c : Command)
    (Pre Post : Imperative.Env Expression → Prop)
    (h : ∀ ρ₀ σ' emitted,
      Pre ρ₀ → InitEnvWF params (.cmd c) ρ₀ →
      EvalCommandE π ρ₀.factory ρ₀.store c σ' emitted →
      Trace.AssertionsValid Expression (DenoteBasedInterp factory) emitted ∧
        (Trace.Reachable Expression (DenoteBasedInterp factory) emitted →
          Post { ρ₀ with store := σ' })) :
    Triple π params Pre [.cmd c] Post (factory := factory) := by
  exact Imperative.Logic.Hoare.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.cmd (EvalCommandE π)
      InitEnvWF params c Pre Post h)

/-- Assignment.  The value written is quantified inside `hpost`, next to the evaluation
    that produced it: which value `e` takes depends on the environment, so fixing one
    outside would demand that `Pre` determine it. -/
theorem set (params : InitEnvWFParams)
    (x : Expression.Ident) (e : Expression.Expr)
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Val),
      Pre ρ₀ → Expression.eval ρ₀.factory ρ₀.store e = some v →
      Imperative.UpdateState Expression ρ₀.store x v σ' →
      Post { ρ₀ with store := σ' }) :
    Triple π params Pre [Statement.set x e md] Post (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Post (fun ρ₀ σ' emitted hpre _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_set heval hupdate _ _ =>
        exact ⟨True.intro, fun _ => hpost ρ₀ σ' _ hpre heval hupdate⟩

/-- Declaration.  `InitState` differs from `UpdateState` only in requiring the slot to
    have been undefined beforehand, which the postcondition never inspects. -/
theorem init (params : InitEnvWFParams)
    (x : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr)
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Val),
      Pre ρ₀ → Expression.eval ρ₀.factory ρ₀.store e = some v →
      Imperative.InitState Expression ρ₀.store x v σ' →
      Post { ρ₀ with store := σ' }) :
    Triple π params Pre [Statement.init x ty (.det e) md] Post (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Post (fun ρ₀ σ' emitted hpre _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_init heval hinit _ _ =>
        exact ⟨True.intro, fun _ => hpost ρ₀ σ' _ hpre heval hinit⟩

/-- Declaration without an initial value.  The variable is bound to an arbitrary value of
    its declared type, which is all the postcondition may rely on. -/
theorem init_nondet (params : InitEnvWFParams)
    (x : Expression.Ident) (ty : Expression.Ty)
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Val),
      Pre ρ₀ → Imperative.InitState Expression ρ₀.store x v σ' →
      HasVal.valueOfTy (P := Expression) ρ₀.factory v ty →
      Post { ρ₀ with store := σ' }) :
    Triple π params Pre [Statement.init x ty .nondet md] Post (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Post (fun ρ₀ σ' emitted hpre _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_init_unconstrained hinit hty _ =>
        exact ⟨True.intro, fun _ => hpost ρ₀ σ' _ hpre hinit hty⟩

/-- Havoc.  The variable takes an arbitrary value of the type of the value it held, which
    is all the postcondition may rely on. -/
theorem havoc (params : InitEnvWFParams)
    (x : Expression.Ident) (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Val),
      Pre ρ₀ → Imperative.UpdateState Expression ρ₀.store x v σ' →
      HasVal.valueOfStoredTy (P := Expression) ρ₀.factory ρ₀.store x v →
      Post { ρ₀ with store := σ' }) :
    Triple π params Pre [Statement.havoc x md] Post (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Post (fun ρ₀ σ' emitted hpre _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_set_nondet hupdate hty _ =>
        exact ⟨True.intro, fun _ => hpost ρ₀ σ' _ hpre hupdate hty⟩

/-- Assumption.  The store is unchanged, and the postcondition is owed only where the
    assumed condition holds in some world: an assumption that cannot hold makes the
    rest of the run unreachable. -/
theorem assume (params : InitEnvWFParams)
    (label : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ →
      (∃ world, (DenoteBasedInterp factory).holds world
        { factory := ρ₀.factory, store := ρ₀.store, label := label, expr := e,
          metadata := md }) →
      Post ρ₀) :
    Triple π params Pre [Statement.assume label e md] Post (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Post (fun ρ₀ σ' emitted hpre _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_assume =>
        exact ⟨True.intro, fun ⟨world, hassum⟩ =>
          hpost ρ₀ hpre ⟨world, hassum _ List.mem_cons_self⟩⟩

/-- Assumption, where the precondition fixes the runtime factory to be over `factory`:
    the assumed condition then holds exactly when it evaluates to `true`. -/
theorem assume_eval (params : InitEnvWFParams)
    (label : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hfac : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ → ρ₀.factory.factory = factory)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ →
      Expression.eval ρ₀.factory ρ₀.store e = some (HasBool.ttVal ρ₀.factory) →
      Post ρ₀) :
    Triple π params Pre [Statement.assume label e md] Post (factory := factory) := by
  refine assume (factory := factory) π params label e md Pre Post
    (fun ρ₀ hpre ⟨_, hholds⟩ => ?_)
  rcases hholds with ⟨_, heval⟩ | ⟨hne, _⟩
  · exact hpost ρ₀ hpre heval
  · exact absurd (hfac ρ₀ hpre) hne

/-- Assertion.  The store is unchanged, and the asserted condition must hold in every
    world at every environment the precondition admits. -/
theorem assert (params : InitEnvWFParams)
    (label : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (Pre : Imperative.Env Expression → Prop)
    (hvalid : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ →
      ∀ world, (DenoteBasedInterp factory).holds world
        { factory := ρ₀.factory, store := ρ₀.store, label := label, expr := e,
          metadata := md }) :
    Triple π params Pre [Statement.assert label e md] Pre (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Pre (fun ρ₀ σ' emitted hpre _ hstep => ?_)
  cases hstep with
  | cmd_sem hbase =>
    cases hbase with
    | eval_assert =>
        exact ⟨⟨fun _ world _ => hvalid ρ₀ hpre world, True.intro⟩, fun _ => hpre⟩

/-- Assertion, where the precondition fixes the runtime factory to be over `factory`:
    the asserted condition then holds exactly when it evaluates to `true`. -/
theorem assert_eval (params : InitEnvWFParams)
    (label : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (Pre : Imperative.Env Expression → Prop)
    (hfac : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ → ρ₀.factory.factory = factory)
    (hvalid : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ →
      Expression.eval ρ₀.factory ρ₀.store e = some (HasBool.ttVal ρ₀.factory)) :
    Triple π params Pre [Statement.assert label e md] Pre (factory := factory) :=
  assert (factory := factory) π params label e md Pre
    (fun ρ₀ hpre _ => Or.inl ⟨hfac ρ₀ hpre, hvalid ρ₀ hpre⟩)

/-! ## Structural rules -/

/-- Sequencing: glue two triples along the concatenation of their statement lists.
    No statement step mutates the factory across the prefix's run, which is what lets
    the well-formedness condition be re-established on the suffix; see
    `Imperative.Logic.Hoare.seq_append` for why `hnoesc` is needed. -/
theorem seq (params : InitEnvWFParams)
    {ss₁ ss₂ : Statements}
    {Pre Mid Post : Imperative.Env Expression → Prop}
    (h₁ : Triple π params Pre ss₁ Mid (factory := factory))
    (h₂ : Triple π params Mid ss₂ Post (factory := factory))
    (hnoesc : Imperative.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] ss₁) :
    Triple π params Pre (ss₁ ++ ss₂) Post (factory := factory) := by
  exact Imperative.Logic.Hoare.seq_append (EvalCommandE π)
    BlockInitEnvWF params
    (fun _ hb => blockInitEnvWF_append_head hb)
    (fun _ _ _ hb hr => blockInitEnvWF_append_tailE π hb hr)
    h₁ h₂ hnoesc

/-- An `exit` ends the statement list where it stands, leaving the
    environment untouched, so the precondition survives to the exiting configuration.
    The statements after it never run.  An enclosing `block` catches the exit. -/
theorem exit_cons (params : InitEnvWFParams) {lbl : String}
    {md : Imperative.MetaData Expression} {ss : Statements}
    (Pre : Imperative.Env Expression → Prop) :
    Triple π params Pre (.exit lbl md :: ss) Pre (factory := factory) := by
  exact Imperative.Logic.Hoare.exit_cons (EvalCommandE π)
    BlockInitEnvWF params

/-- Wrap a statement list in a labelled block.  `Post` must not mention the names the
    body scopes (`PostWF`); no statement step mutates the factory across the body, so
    leaving the block restores nothing. -/
theorem block (params : InitEnvWFParams)
    {ss : Statements} {l : String} {md : Imperative.MetaData Expression}
    {Pre Post : Imperative.Env Expression → Prop}
    (h : Triple π params Pre ss Post (factory := factory))
    (hpost_proj : Imperative.Logic.Hoare.PostWF ss Post) :
    Triple π params Pre [.block l ss md] Post (factory := factory) := by
  exact Imperative.Logic.Hoare.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.block (EvalCommandE π)
      InitEnvWF BlockInitEnvWF params params
      (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hb => blockInitEnvWF_of_block hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_block hb))
      h hpost_proj)

/-- Empty block is skip.  No lowering condition: the generic rule instantiates
    `skip_block` at the trivial block condition. -/
theorem skip (params : InitEnvWFParams) (l : String) (md : Imperative.MetaData Expression)
    (Pre : Imperative.Env Expression → Prop) :
    Triple π params Pre [.block l [] md] Pre (factory := factory) := by
  exact Imperative.Logic.Hoare.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.skip (EvalCommandE π)
      InitEnvWF params
      (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd) l md Pre)

/-- If-then-else rule. -/
theorem ite (params : InitEnvWFParams)
    {cond : Expression.Expr} {tss ess : Statements} {md : Imperative.MetaData Expression}
    {Pre Post : Imperative.Env Expression → Prop}
    (ht : Triple π params
      (fun ρ => Pre ρ ∧ Expression.eval ρ.factory ρ.store cond = some (HasBool.ttVal ρ.factory))
        tss Post
      (factory := factory))
    (he : Triple π params
      (fun ρ => Pre ρ ∧ Expression.eval ρ.factory ρ.store cond = some (HasBool.ffVal ρ.factory))
        ess Post
      (factory := factory))
    (hthen_proj : Imperative.Logic.Hoare.PostWF tss Post)
    (helse_proj : Imperative.Logic.Hoare.PostWF ess Post) :
    Triple π params Pre [.ite (.det cond) tss ess md] Post (factory := factory) := by
  exact Imperative.Logic.Hoare.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.ite (EvalCommandE π)
      InitEnvWF BlockInitEnvWF params params
      (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd)
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
    (hbody : Triple π params
      (fun ρ => Inv ρ ∧ Expression.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory))
        body Inv
      (factory := factory))
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] body)
    (hInv_proj : Imperative.Logic.Hoare.PostWF body Inv) :
    Triple π params Inv [.loop (.det guard) measure inv body md]
      (fun ρ => Inv ρ ∧ Expression.eval ρ.factory ρ.store guard = some (HasBool.ffVal ρ.factory))
      (factory := factory) := by
  exact Imperative.Logic.Hoare.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.while_rule (EvalCommandE π)
      InitEnvWF BlockInitEnvWF params params
      (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hl => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_loop_body hl))
      (fun _ hl => blockInitEnvWF_of_loop_body hl)
      (fun _ _ _ hl hr => initEnvWF_loop_iterateE π hl hr)
      hbody hcov hInv_proj)

end Hoare

end Core.Logic

end -- public section

