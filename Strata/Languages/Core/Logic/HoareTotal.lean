/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.Hoare
public import Strata.DL.Imperative.Logic.HoareTotalTemplate
public import Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.Languages.Core.Logic.LangDefProps
import Strata.DL.Imperative.CmdSemanticsProps

/-! # Total-correctness Hoare logic for Core

The total-correctness rules of `Imperative.Logic.HoareTotal`, instantiated for Core over its
language of statement lists, `EventLang.coreBlock`, as `Strata.Languages.Core.Logic.Hoare`
instantiates the partial-correctness ones.

A total triple `Triple π params Pre ss Post` says that from every admitted entry satisfying
`Pre`, `ss` terminates with valid assertions (in every world, every execution whose assumptions
hold there terminates and has its assertions hold there), and every completed run has valid
assertions and, when reachable, ends in
`Post` (see `Strata.DL.Imperative.Logic.HoareTotalTemplate`).  A call is one step of Core's
semantics, which runs the callee's body to completion inside the step, so the termination of
a triple about a call says that the call can execute, not that every run of the callee
terminates (see `HoareTotal.Procedure.call_of_contract`).

## Contents

`TripleWith`, `Triple`, `Triple.to_partial`, and the rules `false_pre`, `consequence`,
`of_storeWF_pre`, `of_forall_entryFactory`, `cmd`, `set`, `init`, `init_nondet`, `havoc`,
`assume`, `assume_eval`, `assert`, `assert_eval`, `seq`, `exit_cons`, `block`, `skip`, `ite`
and `while_rule`.

A command rule takes the obligation of the partial rule and asks that the command can execute:
for `set` and `init`, that the expression evaluates to a value of the right type; for
`havoc` and `init_nondet`, that the type has a value. `ite` asks that its condition
evaluates to a Boolean, and `while_rule` that its guard does and that a natural-number
measure decreases on every iteration. The procedure-call rule is in `HoareCall`.

The CFG triple `HoareTotal.TripleUnstructured` (in `HoareUnstructured`) has no proof rules yet:
a procedure with a CFG body proves its `Procedure.contractTripleTotal` from its
`Procedure.contractTriple` and a direct proof that the body terminates with valid assertions
(`Procedure.contractTripleTotal_iff`).
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace HoareTotal

variable (π : String → Option Procedure)
variable {factory : Lambda.Factory CoreLParams}

/-! ## The Core total triple -/

/-- Core total-correctness Hoare triple with an explicit event-condition interpretation. -/
@[expose] def TripleWith (conditionInterp : ConditionInterp Expression)
    (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (ss : Statements)
    (Post : Imperative.Env Expression → Prop) : Prop :=
  Strata.Logic.HoareTotal.TripleWith (EventLang.coreBlock π)
    conditionInterp params Pre ss Post

/-- **Core total-correctness Hoare triple** over statement lists, with conditions read by
    evaluation in runtime factories over `factory` (`DenoteBasedInterp factory`), as in
    `Core.Logic.Hoare.Triple`.

    The termination it guarantees counts a procedure call as one step: Core's `call_sem`
    runs the callee's body to completion inside a single command step, so a call can step
    as soon as some run of the callee finishes, even if other runs of the callee diverge.
    A triple about a call therefore says only that the call can execute, for which
    `HoareTotal.Procedure.call_of_contract` asks for one finished run of the callee's body;
    it does not say that every run of the callee terminates. -/
@[expose] def Triple (params : InitEnvWFParams)
    (Pre : Imperative.Env Expression → Prop) (ss : Statements)
    (Post : Imperative.Env Expression → Prop)
    (factory : Lambda.Factory CoreLParams := Core.Factory) : Prop :=
  TripleWith π (DenoteBasedInterp factory) params Pre ss Post

/-- A total triple gives the partial triple with the same pre- and postcondition. -/
theorem Triple.to_partial {params : InitEnvWFParams}
    {Pre Post : Imperative.Env Expression → Prop} {ss : Statements}
    (h : Triple π params Pre ss Post (factory := factory)) :
    Hoare.Triple π params Pre ss Post (factory := factory) :=
  Strata.Logic.HoareTotal.TripleWith.to_partial h

/-! ## Parametric rules -/

/-- False precondition proves anything. -/
theorem false_pre (params : InitEnvWFParams) (ss : Statements)
    (Post : Imperative.Env Expression → Prop) :
    Triple π params (fun _ => False) ss Post (factory := factory) :=
  Strata.Logic.HoareTotal.false_pre (EventLang.coreBlock π) params ss Post

/-- Consequence (weakening): strengthen the precondition, weaken the postcondition. -/
theorem consequence (params : InitEnvWFParams)
    {Pre Pre' Post Post' : Imperative.Env Expression → Prop} {ss : Statements}
    (h : Triple π params Pre ss Post (factory := factory))
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Triple π params Pre' ss Post' (factory := factory) :=
  Strata.Logic.HoareTotal.consequence (EventLang.coreBlock π) params h hpre hpost

/-- A total triple whose precondition also requires a well-formed entry store holds without
    that requirement: the gate of every admitted entry gives it. -/
theorem of_storeWF_pre (params : InitEnvWFParams)
    {Pre Post : Imperative.Env Expression → Prop} {ss : Statements}
    (h : Triple π params (fun ρ => Pre ρ ∧ Imperative.WellFormedStore ρ.store ρ.factory) ss
      Post (factory := factory)) :
    Triple π params Pre ss Post (factory := factory) :=
  fun ρ₀ hpre hinit => h ρ₀ ⟨hpre, hinit.storeWellDefined⟩ hinit

/-- A total triple holds when it holds, for every runtime factory `E`, from the entries
    whose runtime factory is `E`. -/
theorem of_forall_entryFactory (params : InitEnvWFParams)
    {Pre Post : Imperative.Env Expression → Prop} {ss : Statements}
    (h : ∀ E, Triple π params (fun ρ => Pre ρ ∧ ρ.factory = E) ss Post
      (factory := factory)) :
    Triple π params Pre ss Post (factory := factory) :=
  fun ρ₀ hpre hinit => h ρ₀.factory ρ₀ ⟨hpre, rfl⟩ hinit

/-! ## Rules for a single command -/

/-- A declaration of `x` that the gate admits starts from a store where `x` is unbound. -/
private theorem init_target_undefined {params : InitEnvWFParams} {x : Expression.Ident}
    {ty : Expression.Ty} {e : ExprOrNondet Expression} {md : Imperative.MetaData Expression}
    {ρ₀ : Imperative.Env Expression} (hinit : InitEnvWF params (Statement.init x ty e md) ρ₀) :
    ρ₀.store x = none :=
  Option.isNone_iff_eq_none.mp (hinit.defsUndefined x (by
    simp [Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars]))

/-- **A single command.**  A partial triple about `[.cmd c]` is a total one when the command
    can execute at every admitted `Pre`-environment (`hprog`): a command is one step, and the
    partial triple gives the validity of the assertions it emits. -/
theorem cmd (params : InitEnvWFParams) (c : Command)
    (Pre Post : Imperative.Env Expression → Prop)
    (hprog : ∀ ρ₀, Pre ρ₀ → InitEnvWF params (.cmd c) ρ₀ →
      ∃ σ' emitted, EvalCommandE π ρ₀.factory ρ₀.store c σ' emitted)
    (h : Hoare.Triple π params Pre [.cmd c] Post (factory := factory)) :
    Triple π params Pre [.cmd c] Post (factory := factory) := by
  intro ρ₀ hpre hinit
  refine ⟨fun w => ?_, (h ρ₀ hpre hinit).2⟩
  obtain ⟨σ', emitted, hstep⟩ := hprog ρ₀ hpre (blockInitEnvWF_singleton hinit)
  refine mustTerminateAndAssertsValid_imperativeBlockE_of_imperativeE
    (initEnvWF := fun _ _ _ => True)
    (mustTerminateAndAssertsValid_stmts_consE (mustTerminateAndAssertsValid_seqE
      (.step ⟨emitted, _, (.step_cmd hstep : StepStmtE Expression (EvalCommandE π) _ _ _)⟩
        (fun e _ hs => ?_) fun _ _ hs _ => ?_)
      fun _ _ _ _ => mustTerminateAndAssertsValid_stmts_nilE))
  · -- The command's assertions hold: its one-step run is a finished run of `[.cmd c]`.
    cases (hs : StepStmtE Expression (EvalCommandE π) _ _ _) with
    | step_cmd hs' =>
      have hrun := ReflTransTrace.step _ _ _ _ _
        (.step_cmd hs' : StepStmtE Expression (EvalCommandE π) _ _ _) (.refl _)
      rw [List.append_nil] at hrun
      exact (Trace.AssertionsValid_iff_assertionsHoldIn _ _).1
        ((h ρ₀ hpre hinit).1 _ _ (stmtRun_to_singletonE (EvalCommandE π) hrun)) w
  cases (hs : StepStmtE Expression (EvalCommandE π) _ _ _)
  exact .terminal _

/-- Assignment.  `hprog` says `e` evaluates, at every admitted `Pre`-environment, to a value
    of the type of the value `x` holds, so the assignment can execute; `hpost` is the
    obligation of `Core.Logic.Hoare.set`. -/
theorem set (params : InitEnvWFParams)
    (x : Expression.Ident) (e : Expression.Expr)
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hprog : ∀ ρ₀, Pre ρ₀ → InitEnvWF params (Statement.set x e md) ρ₀ →
      ∃ v, Expression.eval ρ₀.factory ρ₀.store e = some v ∧
        HasVal.valueOfStoredTy (P := Expression) ρ₀.factory ρ₀.store x v)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Val),
      Pre ρ₀ → Expression.eval ρ₀.factory ρ₀.store e = some v →
      Imperative.UpdateState Expression ρ₀.store x v σ' →
      Post { ρ₀ with store := σ' }) :
    Triple π params Pre [Statement.set x e md] Post (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Post (fun ρ₀ hpre hinit => ?_)
    (Hoare.set π params x e md Pre Post hpost)
  obtain ⟨v, hev, hty⟩ := hprog ρ₀ hpre hinit
  obtain ⟨_, _, hprev, _⟩ := id hty
  exact ⟨SemanticStore.update ρ₀.store x v, [],
    .cmd_sem (.eval_set hev (UpdateState.of_update hprev) hty
      (coreEvaluator_WellFormedSemanticEvalVar _))⟩

/-- Declaration.  `hprog` says `e` evaluates, at every admitted `Pre`-environment, to a value
    of type `ty`; the gate keeps `x` undefined beforehand.  `hpost` is the obligation of
    `Core.Logic.Hoare.init`. -/
theorem init (params : InitEnvWFParams)
    (x : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr)
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hprog : ∀ ρ₀, Pre ρ₀ → InitEnvWF params (Statement.init x ty (.det e) md) ρ₀ →
      ∃ v, Expression.eval ρ₀.factory ρ₀.store e = some v ∧
        HasVal.valueOfTy (P := Expression) ρ₀.factory v ty)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Val),
      Pre ρ₀ → Expression.eval ρ₀.factory ρ₀.store e = some v →
      Imperative.InitState Expression ρ₀.store x v σ' →
      Post { ρ₀ with store := σ' }) :
    Triple π params Pre [Statement.init x ty (.det e) md] Post (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Post (fun ρ₀ hpre hinit => ?_)
    (Hoare.init π params x ty e md Pre Post hpost)
  obtain ⟨v, hev, hty⟩ := hprog ρ₀ hpre hinit
  exact ⟨SemanticStore.update ρ₀.store x v, [],
    .cmd_sem (.eval_init hev (InitState.of_update (init_target_undefined hinit)) hty
      (coreEvaluator_WellFormedSemanticEvalVar _))⟩

/-- Declaration without an initial value.  `hprog` says the declared type has a value at
    every admitted `Pre`-environment; `hpost` is the obligation of
    `Core.Logic.Hoare.init_nondet`. -/
theorem init_nondet (params : InitEnvWFParams)
    (x : Expression.Ident) (ty : Expression.Ty)
    (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hprog : ∀ ρ₀, Pre ρ₀ → InitEnvWF params (Statement.init x ty .nondet md) ρ₀ →
      ∃ v, HasVal.valueOfTy (P := Expression) ρ₀.factory v ty)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Val),
      Pre ρ₀ → Imperative.InitState Expression ρ₀.store x v σ' →
      HasVal.valueOfTy (P := Expression) ρ₀.factory v ty →
      Post { ρ₀ with store := σ' }) :
    Triple π params Pre [Statement.init x ty .nondet md] Post (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Post (fun ρ₀ hpre hinit => ?_)
    (Hoare.init_nondet π params x ty md Pre Post hpost)
  obtain ⟨v, hty⟩ := hprog ρ₀ hpre hinit
  exact ⟨SemanticStore.update ρ₀.store x v, [],
    .cmd_sem (.eval_init_unconstrained (InitState.of_update (init_target_undefined hinit)) hty
      (coreEvaluator_WellFormedSemanticEvalVar _))⟩

/-- Havoc.  `hprog` says the type of the value `x` holds has a value at every admitted
    `Pre`-environment; `hpost` is the obligation of `Core.Logic.Hoare.havoc`. -/
theorem havoc (params : InitEnvWFParams)
    (x : Expression.Ident) (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hprog : ∀ ρ₀, Pre ρ₀ → InitEnvWF params (Statement.havoc x md) ρ₀ →
      ∃ v, HasVal.valueOfStoredTy (P := Expression) ρ₀.factory ρ₀.store x v)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (v : Expression.Val),
      Pre ρ₀ → Imperative.UpdateState Expression ρ₀.store x v σ' →
      HasVal.valueOfStoredTy (P := Expression) ρ₀.factory ρ₀.store x v →
      Post { ρ₀ with store := σ' }) :
    Triple π params Pre [Statement.havoc x md] Post (factory := factory) := by
  refine cmd (factory := factory) π params _ Pre Post (fun ρ₀ hpre hinit => ?_)
    (Hoare.havoc π params x md Pre Post hpost)
  obtain ⟨v, hty⟩ := hprog ρ₀ hpre hinit
  obtain ⟨_, _, hprev, _⟩ := id hty
  exact ⟨SemanticStore.update ρ₀.store x v, [],
    .cmd_sem (.eval_set_nondet (UpdateState.of_update hprev) hty
      (coreEvaluator_WellFormedSemanticEvalVar _))⟩

/-- Assumption.  The store is unchanged, and the postcondition is owed only where the
    assumed condition holds in some world, as in `Core.Logic.Hoare.assume`: a run the
    assumption makes unreachable need not terminate. -/
theorem assume (params : InitEnvWFParams)
    (label : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ →
      (∃ world, (DenoteBasedInterp factory).holds world
        { factory := ρ₀.factory, store := ρ₀.store, label := label, expr := e,
          metadata := md }) →
      Post ρ₀) :
    Triple π params Pre [Statement.assume label e md] Post (factory := factory) :=
  cmd (factory := factory) π params _ Pre Post (fun _ _ _ => ⟨_, _, .cmd_sem .eval_assume⟩)
    (Hoare.assume π params label e md Pre Post hpost)

/-- Assumption, where the precondition fixes the runtime factory to be over `factory`:
    the postcondition may then use that the assumed condition evaluates to `true`. -/
theorem assume_eval (params : InitEnvWFParams)
    (label : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (Pre Post : Imperative.Env Expression → Prop)
    (hfac : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ → ρ₀.factory.factory = factory)
    (hpost : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ →
      Expression.eval ρ₀.factory ρ₀.store e = some (HasBool.ttVal ρ₀.factory) →
      Post ρ₀) :
    Triple π params Pre [Statement.assume label e md] Post (factory := factory) :=
  cmd (factory := factory) π params _ Pre Post (fun _ _ _ => ⟨_, _, .cmd_sem .eval_assume⟩)
    (Hoare.assume_eval π params label e md Pre Post hfac hpost)

/-- Assertion.  The store is unchanged, and the asserted condition must hold in every
    world at every environment the precondition admits. -/
theorem assert (params : InitEnvWFParams)
    (label : String) (e : Expression.Expr) (md : Imperative.MetaData Expression)
    (Pre : Imperative.Env Expression → Prop)
    (hvalid : ∀ (ρ₀ : Imperative.Env Expression), Pre ρ₀ →
      ∀ world, (DenoteBasedInterp factory).holds world
        { factory := ρ₀.factory, store := ρ₀.store, label := label, expr := e,
          metadata := md }) :
    Triple π params Pre [Statement.assert label e md] Pre (factory := factory) :=
  cmd (factory := factory) π params _ Pre Pre (fun _ _ _ => ⟨_, _, .cmd_sem .eval_assert⟩)
    (Hoare.assert π params label e md Pre hvalid)

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

/-- Sequencing: glue two total triples along the concatenation of their statement lists;
    see `Core.Logic.Hoare.seq`. -/
theorem seq (params : InitEnvWFParams)
    {ss₁ ss₂ : Statements}
    {Pre Mid Post : Imperative.Env Expression → Prop}
    (h₁ : Triple π params Pre ss₁ Mid (factory := factory))
    (h₂ : Triple π params Mid ss₂ Post (factory := factory))
    (hnoesc : Imperative.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] ss₁) :
    Triple π params Pre (ss₁ ++ ss₂) Post (factory := factory) :=
  Imperative.Logic.HoareTotal.seq_append (EvalCommandE π)
    BlockInitEnvWF params
    (fun _ hb => blockInitEnvWF_append_head hb)
    (fun _ _ _ hb hr => blockInitEnvWF_append_tailE π hb hr)
    h₁ h₂ hnoesc

/-- An `exit` ends the statement list where it stands, leaving the environment untouched. -/
theorem exit_cons (params : InitEnvWFParams) {lbl : String}
    {md : Imperative.MetaData Expression} {ss : Statements}
    (Pre : Imperative.Env Expression → Prop) :
    Triple π params Pre (.exit lbl md :: ss) Pre (factory := factory) :=
  Imperative.Logic.HoareTotal.exit_cons (EvalCommandE π) BlockInitEnvWF params

/-- Wrap a statement list in a labelled block.  `Post` must not mention the names the body
    scopes (`PostWF`). -/
theorem block (params : InitEnvWFParams)
    {ss : Statements} {l : String} {md : Imperative.MetaData Expression}
    {Pre Post : Imperative.Env Expression → Prop}
    (h : Triple π params Pre ss Post (factory := factory))
    (hpost_proj : Imperative.Logic.Hoare.PostWF ss Post) :
    Triple π params Pre [.block l ss md] Post (factory := factory) :=
  Imperative.Logic.HoareTotal.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.HoareTotal.block (EvalCommandE π)
      InitEnvWF BlockInitEnvWF params params
      (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hb => blockInitEnvWF_of_block hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_block hb))
      h hpost_proj)

/-- Empty block is skip. -/
theorem skip (params : InitEnvWFParams) (l : String) (md : Imperative.MetaData Expression)
    (Pre : Imperative.Env Expression → Prop) :
    Triple π params Pre [.block l [] md] Pre (factory := factory) :=
  Imperative.Logic.HoareTotal.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.HoareTotal.skip (EvalCommandE π)
      InitEnvWF params
      (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd) l md Pre)

/-- If-then-else rule.  `hcond` says the condition evaluates to a Boolean at every admitted
    `Pre`-environment. -/
theorem ite (params : InitEnvWFParams)
    {cond : Expression.Expr} {tss ess : Statements} {md : Imperative.MetaData Expression}
    {Pre Post : Imperative.Env Expression → Prop}
    (hcond : ∀ ρ, Pre ρ → InitEnvWF params (.ite (.det cond) tss ess md) ρ →
      Expression.eval ρ.factory ρ.store cond = some (HasBool.ttVal ρ.factory) ∨
        Expression.eval ρ.factory ρ.store cond = some (HasBool.ffVal ρ.factory))
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
    Triple π params Pre [.ite (.det cond) tss ess md] Post (factory := factory) :=
  Imperative.Logic.HoareTotal.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.HoareTotal.ite (EvalCommandE π)
      InitEnvWF BlockInitEnvWF params params
      (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hb => blockInitEnvWF_of_ite_then hb)
      (fun _ hb => blockInitEnvWF_of_ite_else hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_then hb))
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_ite_else hb))
      hcond ht he hthen_proj helse_proj)

/-- While rule.  The invariant `Inv` and the bound `M ρ < n` must survive the body block's
    store projection (`hInv_proj`); every iteration decreases the measure `M` (`hbody`); and
    the guard evaluates to a Boolean wherever `Inv` holds (`hguard`). -/
theorem while_rule (params : InitEnvWFParams)
    {guard : Expression.Expr} {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : Imperative.MetaData Expression}
    {Inv : Imperative.Env Expression → Prop} (M : Imperative.Env Expression → Nat)
    (hguard : ∀ ρ, Inv ρ → InitEnvWF params (.loop (.det guard) measure inv body md) ρ →
      Expression.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory) ∨
        Expression.eval ρ.factory ρ.store guard = some (HasBool.ffVal ρ.factory))
    (hbody : ∀ n, Triple π params
      (fun ρ => (Inv ρ ∧
        Expression.eval ρ.factory ρ.store guard = some (HasBool.ttVal ρ.factory)) ∧ M ρ = n)
        body (fun ρ => Inv ρ ∧ M ρ < n)
      (factory := factory))
    (hcov : Imperative.Block.exitsCoveredByBlocks
      (P := Expression) (CmdT := Command) [] body)
    (hInv_proj : ∀ n, Imperative.Logic.Hoare.PostWF body (fun ρ => Inv ρ ∧ M ρ < n)) :
    Triple π params Inv [.loop (.det guard) measure inv body md]
      (fun ρ => Inv ρ ∧ Expression.eval ρ.factory ρ.store guard = some (HasBool.ffVal ρ.factory))
      (factory := factory) :=
  Imperative.Logic.HoareTotal.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.HoareTotal.while_rule (EvalCommandE π)
      InitEnvWF BlockInitEnvWF params params M
      (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hl => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_loop_body hl))
      (fun _ hl => blockInitEnvWF_of_loop_body hl)
      (fun _ _ _ hl hr => initEnvWF_loop_iterateE π hl hr)
      hguard hbody hcov hInv_proj)

end HoareTotal

end Core.Logic

end -- public section
