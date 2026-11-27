/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.ValuationToRunSupport
public import Strata.Languages.Core.InterpreterReplayProps
public import Strata.Languages.Core.Counterexample.ValuationToRunProducer
public import Strata.DL.Lambda.LStateProps
public import Strata.Languages.Core.Counterexample.BackLinkSim
import all Strata.Languages.Core.InterpreterReplay
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Imperative.Counterexample.Valuation
import all Strata.Languages.Core.Counterexample.ValuationToRunProducer
import all Strata.Languages.Core.Counterexample.ValuationToRunSupport
import Strata.DL.Imperative.Counterexample.Tactics
import all Strata.DL.Lambda.LExprEvalFuelProps
import all Strata.Languages.Core.Counterexample.BackLinkSim
import all Strata.Languages.Core.Counterexample.BackLinkSimProps
import Strata.Languages.Core.InterpreterDomainProps

/-! # `(b)→(a)` drive: composite `ReplayM` stepping lemmas

Composite stepping lemmas over the engine (`runInterp`/`runCoreInterp` over `ReplayM`),
proved from the toolkit primitives (`Strata/Languages/Core/InterpreterReplayProps.lean`,
`Strata/DL/Imperative/InterpreterProps.lean`): the per-command single-step reductions
and whole-run lift lemmas of the drive induction.

Key theorems: `run_stmts_passive_head`, `bounded_cex_goal_false_on_agreeing_store`,
`bounded_cov_goal_true_on_agreeing_store`, `drive_base_store_agreement`.
Key definitions: `StoreAgreesThreaded`, `AssumesHoldThreaded`. -/

namespace Core

open Imperative

public section

variable {d : Nat}

/-! ## `runInterp` one-step unfolds for the non-`.stmt` configs

The toolkit gives `runInterp_succ_stmt` for `.stmt` configs; the drive also steps
`.seq`/`.stmts`/`.block` configs, which fall into `runInterp`'s general `_` arm.
These local unfolds cover them. -/

/-- `runInterp` on a `.stmts` config at successor fuel: step once, then recurse. -/
theorem runInterp_succ_stmts {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (stepCmd : StepCmdM Expression Command m) (fuel : Nat)
    (stmts : List (Stmt Expression Command)) (env : IEnv Expression) :
    runInterp stepCmd (fuel + 1) (.stmts stmts env)
      = stepInterp stepCmd (fuel + 1) (.stmts stmts env) >>= runInterp stepCmd fuel := (rfl)

/-- `runInterp` on a `.seq` config at successor fuel: step once, then recurse. -/
theorem runInterp_succ_seq {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (stepCmd : StepCmdM Expression Command m) (fuel : Nat)
    (inner : IConfig Expression Command) (rest : List (Stmt Expression Command)) :
    runInterp stepCmd (fuel + 1) (.seq inner rest)
      = stepInterp stepCmd (fuel + 1) (.seq inner rest) >>= runInterp stepCmd fuel := (rfl)

/-- `runInterp` on a `.block` config at successor fuel: step once, then recurse. -/
theorem runInterp_succ_block {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (stepCmd : StepCmdM Expression Command m) (fuel : Nat)
    (label : Option String) (frame : ScopeFrame Expression)
    (inner : IConfig Expression Command) :
    runInterp stepCmd (fuel + 1) (.block label frame inner)
      = stepInterp stepCmd (fuel + 1) (.block label frame inner) >>= runInterp stepCmd fuel :=
  (rfl)

/-! ## Single-step run-projections for each passive/atomic head

Each reduces `stepInterp (replayStepCmd π d) fuel (.stmt (.cmd (.cmd HEAD)) env)` under
the run-projection to its `(outcome, state)` pair.  `assert`/`assume`/`cover` emit
their snapshot event (store unchanged); `init`/`set` update the store. -/

/-- The trace `forM` over a one-event list reduces to that single `emit` then
    `pure ⟨⟩` (the shape `Cmd.emittedEvents` returns for assert/assume/cover). -/
private theorem replayM_emit_forM_single (ev : IEvent Expression) :
    (([ev] : List (IEvent Expression)).forM (InterpEffects.emit (m := ReplayM Expression)))
      = (InterpEffects.emit (m := ReplayM Expression) ev >>= fun _ => (pure ⟨⟩ : ReplayM Expression
          PUnit)) := rfl

/-- **assert single-step.**  Emits the assert snapshot event, store unchanged. -/
theorem step_assert_run (π : String → Option Procedure) (fuel : Nat)
    (cfg : ReplayCfg Expression) (st : ReplayState Expression)
    (env : IEnv Expression) (label : String) (e : Expression.Expr)
    (md : Imperative.MetaData Expression) (hcfg : cfg.interruptOn = fun _ => none) :
    rrun (stepInterp (replayStepCmd π d) fuel
        (.stmt (.cmd (.cmd (.assert label e md))) env)) cfg st
      = (.ok (.terminal env),
         { st with
           traceRev :=
             (REvent.assert ⟨env.factory, env.store.get, label, e, md⟩) :: st.traceRev }) := by
  simp only [stepInterp_stmt_cmd, replayStepCmd_cmd, stepBaseCmdStore_assert, Cmd.rEmittedEvents,
    replayM_emit_forM_single, replayM_run_bind, replayM_run_emit_none _ _ _ hcfg]
  rfl

/-- **assume single-step.**  Emits the assume snapshot event, store unchanged
    (`assume` is an unconditional skip on the store; the guard is recorded, not
    branched on). -/
theorem step_assume_run (π : String → Option Procedure) (fuel : Nat)
    (cfg : ReplayCfg Expression) (st : ReplayState Expression)
    (env : IEnv Expression) (label : String) (e : Expression.Expr)
    (md : Imperative.MetaData Expression) (hcfg : cfg.interruptOn = fun _ => none) :
    rrun (stepInterp (replayStepCmd π d) fuel
        (.stmt (.cmd (.cmd (.assume label e md))) env)) cfg st
      = (.ok (.terminal env),
         { st with
           traceRev :=
             (REvent.assume ⟨env.factory, env.store.get, label, e, md⟩) :: st.traceRev }) := by
  simp only [stepInterp_stmt_cmd, replayStepCmd_cmd, stepBaseCmdStore_assume, Cmd.rEmittedEvents,
    replayM_emit_forM_single, replayM_run_bind, replayM_run_emit_none _ _ _ hcfg]
  rfl

/-- **cover single-step.**  Emits the cover snapshot event, store unchanged. -/
theorem step_cover_run (π : String → Option Procedure) (fuel : Nat)
    (cfg : ReplayCfg Expression) (st : ReplayState Expression)
    (env : IEnv Expression) (label : String) (e : Expression.Expr)
    (md : Imperative.MetaData Expression) (hcfg : cfg.interruptOn = fun _ => none) :
    rrun (stepInterp (replayStepCmd π d) fuel
        (.stmt (.cmd (.cmd (.cover label e md))) env)) cfg st
      = (.ok (.terminal env),
         { st with
           traceRev :=
             (REvent.cover ⟨env.factory, env.store.get, label, e, md⟩) :: st.traceRev }) := by
  simp only [stepInterp_stmt_cmd, replayStepCmd_cmd, stepBaseCmdStore_cover, Cmd.rEmittedEvents,
    replayM_emit_forM_single, replayM_run_bind, replayM_run_emit_none _ _ _ hcfg]
  rfl

/-- **det-init single-step.**  Undefined target, RHS evaluates to a well-typed
    value: updates the store at that variable; no event, no oracle consumed. -/
theorem step_init_det_run (π : String → Option Procedure) (fuel : Nat)
    (cfg : ReplayCfg Expression) (st : ReplayState Expression)
    (env : IEnv Expression) (name : Expression.Ident) (ty : Expression.Ty)
    (e : Expression.Expr) (md : Imperative.MetaData Expression) (v : Expression.Expr)
    (hu : env.store.get name = none)
    (he : InterpLang.boundedEval (P := Expression) fuel env.factory env.store.get e = some v)
    (ht : ((InterpLang.ops (P := Expression)).isValue env.factory v
            && (InterpLang.ops (P := Expression)).hasType env.factory v ty) = true) :
    rrun (stepInterp (replayStepCmd π d) fuel
        (.stmt (.cmd (.cmd (.init name ty (.det e) md))) env)) cfg st
      = (.ok (.terminal { env with store := env.store.update name v }), st) := by
  simp_all [stepBaseCmdStore_init_det, replayM_run_pure]

/-- **nondet-`init` single-step.**  Undefined target and an oracle head `v` that is
    a well-typed value: `choose` pops `v` (validating it against `ty`), the store is
    updated at `name`, and the `ReplayState` advances (`remaining` loses its head,
    `usedRev` gains it).  The nondet-write counterpart of `step_init_det_run`. -/
theorem step_init_nondet_run (π : String → Option Procedure) (fuel : Nat)
    (cfg : ReplayCfg Expression) (st : ReplayState Expression)
    (env : IEnv Expression) (name : Expression.Ident) (ty : Expression.Ty)
    (md : Imperative.MetaData Expression) (v : Expression.Expr) (rest : List Expression.Expr)
    (hu : env.store.get name = none)
    (hrem : st.remaining = v :: rest)
    (hval : ((InterpLang.ops (P := Expression)).isValue env.factory v
            && (InterpLang.ops (P := Expression)).hasType env.factory v ty) = true) :
    rrun (stepInterp (replayStepCmd π d) fuel
        (.stmt (.cmd (.cmd (.init name ty .nondet md))) env)) cfg st
      = (.ok (.terminal { env with store := env.store.update name v }),
         { st with remaining := rest, usedRev := v :: st.usedRev }) := by
  simp only [stepInterp_stmt_cmd, replayStepCmd_cmd, stepBaseCmdStore, hu, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte, replayM_run_bind,
    replayM_choose_cons _ _ _ _ _ _ _ hrem hval]
  rfl

/-- **nondet-`ite` then-branch descent.**  The oracle head is the boolean `tt`;
    `choose` pops it (validating against `boolTy`) and the engine descends into the
    then-branch as a label-less block. -/
theorem step_ite_nondet_true_run (π : String → Option Procedure) (fuel : Nat)
    (cfg : ReplayCfg Expression) (st : ReplayState Expression)
    (env : IEnv Expression)
    (thenSs elseSs : List (Stmt Expression Command)) (md : Imperative.MetaData Expression)
    (rest : List Expression.Expr)
    (hrem : st.remaining = (HasBool.tt (P := Expression)) :: rest)
    (hval : ((InterpLang.ops (P := Expression)).isValue env.factory (HasBool.tt (P := Expression))
              && (InterpLang.ops (P := Expression)).hasType env.factory (HasBool.tt (P :=
                  Expression))
                  (HasBool.boolTy (P := Expression))) = true) :
    rrun (stepInterp (replayStepCmd π d) fuel (.stmt (.ite .nondet thenSs elseSs md) env)) cfg st
      = (.ok (.block .none (.opened env.store) (.stmts thenSs env)),
         { st with
           remaining := rest
           usedRev := (HasBool.tt (P := Expression)) :: st.usedRev }) := by
  simp only [stepInterp, resolveGuard, replayM_run_bind,
    replayM_choose_cons _ _ _ _ _ _ _ hrem hval]
  rfl

/-- **nondet-`ite` else-branch descent.**  The oracle head is the boolean `ff`;
    `choose` pops it and the engine descends into the else-branch. -/
theorem step_ite_nondet_false_run (π : String → Option Procedure) (fuel : Nat)
    (cfg : ReplayCfg Expression) (st : ReplayState Expression)
    (env : IEnv Expression)
    (thenSs elseSs : List (Stmt Expression Command)) (md : Imperative.MetaData Expression)
    (rest : List Expression.Expr)
    (hrem : st.remaining = (HasBool.ff (P := Expression)) :: rest)
    (hval : ((InterpLang.ops (P := Expression)).isValue env.factory (HasBool.ff (P := Expression))
              && (InterpLang.ops (P := Expression)).hasType env.factory (HasBool.ff (P :=
                  Expression))
                  (HasBool.boolTy (P := Expression))) = true) :
    rrun (stepInterp (replayStepCmd π d) fuel (.stmt (.ite .nondet thenSs elseSs md) env)) cfg st
      = (.ok (.block .none (.opened env.store) (.stmts elseSs env)),
         { st with
           remaining := rest
           usedRev := (HasBool.ff (P := Expression)) :: st.usedRev }) := by
  simp only [stepInterp, resolveGuard, replayM_run_bind,
    replayM_choose_cons _ _ _ _ _ _ _ hrem hval]
  rfl

/-! ## Whole-run lifts

Peeling one statement off a `.stmts` run and threading the `ReplayState`.  All
built on the master bind ladder `replayM_run_bind` specialized to the success
branch (`rrun_bind_ok`), which the passive path always takes. -/

/-- **`rrun` bind-on-success.**  If `x`'s run succeeds with `a` and state `st'`,
    then `x >>= g`'s run continues with `g a` from `st'` — the success branch of the
    master ladder `replayM_run_bind`. -/
theorem rrun_bind_ok {α β : Type} (x : ReplayM Expression α) (g : α → ReplayM Expression β)
    (cfg : ReplayCfg Expression) (st st' : ReplayState Expression) (a : α)
    (h : rrun x cfg st = (.ok a, st')) :
    rrun (x >>= g) cfg st = rrun (g a) cfg st' := by simp_all [replayM_run_bind]

/-- **passive-head peel.**  A head statement `s` whose single step runs to a
    non-failing `.terminal env'` (threading `st → st'`) is consumed by the `.stmts`
    run in three engine steps (`.stmts → .seq`, step head, `.seq .terminal → .stmts`),
    reducing the run of `s :: rest` at fuel `n+3` to the run of `rest` at fuel `n`. -/
theorem run_stmts_passive_head (π : String → Option Procedure) (n : Nat)
    (cfg : ReplayCfg Expression) (st st' : ReplayState Expression)
    (s : Stmt Expression Command) (rest : List (Stmt Expression Command))
    (env env' : IEnv Expression)
    (hstep : rrun (stepInterp (replayStepCmd π d) (n + 2) (.stmt s env)) cfg st
              = (.ok (.terminal env'), st')) :
    rrun (runInterp (replayStepCmd π d) (n + 3) (.stmts (s :: rest) env)) cfg st
      = rrun (runInterp (replayStepCmd π d) n (.stmts rest env')) cfg st' := by
  rcases rest with _ | ⟨s', rest⟩
  · rw [runInterp_succ_stmts, stepInterp_stmts_single (P := Expression), pure_bind]
    change rrun (stepInterp (replayStepCmd π d) (n + 2) ((IConfig.stmt s env).seqs 0) >>=
      runInterp (replayStepCmd π d) (n + 1)) cfg st = _
    rw [stepInterp.eq_def (P := Expression)]
    dsimp only
    rw [bind_assoc, rrun_bind_ok _ _ _ _ _ _ hstep]
    rfl
  · simp_all [runInterp_succ_stmts, runInterp_succ_seq, replayM_run_bind]

/-! ## `traceRev`-monotonicity — the run only ever prepends events

`ReplayState.traceRev` is touched by exactly one engine op — `emit` (a prepend);
`choose` writes only `remaining`/`usedRev`.  So every `stepInterp`/`runInterp` run
leaves the initial `traceRev` as a **suffix** of the final one.  This transports a
firing event forward through the remainder of a run — blocks, scope projections,
passive tails alike — so genuineness, once reached, is never lost, with no
fuel-alignment argument. -/

/-- Membership survives passing to a supersequence that has the list as a suffix. -/
theorem mem_of_mem_suffix {α} {a : α} {l l' : List α} (hm : a ∈ l) (hs : l <:+ l') :
    a ∈ l' := hs.subset hm

/-- **`runInterp` only ever prepends events** (whole run): the initial `traceRev` is
    a suffix of the final one, at any fuel. -/
theorem runInterp_traceRev_suffix :
    ∀ (n : Nat) (c : IConfig Expression Command) (cfg : ReplayCfg Expression)
      (st : ReplayState Expression),
      st.traceRev <:+
        (rrun (runInterp (replayStepCmd (fun _ => none) d) n c) cfg st).2.traceRev := by
  intros
  solve_by_elim [runInterp_grows, replayStepCmd_grows]

/-! ## The goal on agreeing stores -/

/-- **Bounded-eval store-congruence.**  Two stores agreeing on the read expression's free variables
    give the same `evalBounded fb` result, provided the `declStore` values are well-formed
    (canonical ⇒ closed). -/
private theorem evalBounded_store_congr
    (factory : @Lambda.Factory CoreLParams)
    (hWF : Lambda.FactoryWF factory)
    (fb : Nat) (opStore declStore : RStore Expression) (e : Expression.Expr)
    (hdeclWF : RWellFormedStore declStore factory)
    (hptwise : ∀ x ∈ HasFvars.getFvars e, opStore x = declStore x) :
    evalBounded fb factory opStore e = evalBounded fb factory declStore e := by
  unfold evalBounded
  rw [evalTypedDomain_congr hptwise, evalOpsChecked_congr hptwise,
    Lambda.eval_env_congr (fun ⟨_, _⟩ ⟨_, _⟩ h => by cases h; rfl)
    _ factory _ _ hWF (fun x v h => Lambda.isValue_getVars_nil _ _ (hdeclWF x v h)) e hptwise]

/-- **Store-extension frame for `evalBounded`.**  A decided bounded evaluation is
    preserved when the store is extended pointwise (`EnvExtends σ σ'`: every binding of
    `σ` is present, identically, in `σ'`). -/
private theorem evalBounded_frame
    (factory : @Lambda.Factory CoreLParams) (fb : Nat)
    (σ σ' : RStore Expression) (e v : Expression.Expr)
    (hext : Lambda.EnvExtends (T := CoreLParams) σ σ')
    (h : evalBounded fb factory σ e = some v) :
    evalBounded fb factory σ' e = some v := by
  obtain ⟨hd, he, ht⟩ := evalBounded_eq_some_iff.1 h
  exact evalBounded_eq_some_iff.2
    ⟨evalTypedDomain_frame hext hd, Lambda.eval_frame _ _ _ hext _ _ _ he, ht.1,
      evalOpsChecked_frame hext hd ht.2⟩

/-- **Restricted declarative→operational transfer for `evalBounded`.**  A bounded evaluation
    on `declStore` gives the same value on `opStore` when every binding `declStore` holds at a
    free variable of `e` is closed and reproduced by `opStore`; `opStore` may hold other
    bindings, and lack those `declStore` holds elsewhere. -/
private theorem evalBounded_transfer_mono
    (factory : @Lambda.Factory CoreLParams)
    (hWF : Lambda.FactoryWF factory)
    (fb : Nat) (declStore opStore : RStore Expression) (e v : Expression.Expr)
    (hclosed : ∀ x ∈ HasFvars.getFvars (P := Expression) e, ∀ w,
        declStore x = some w → Lambda.LExpr.LExpr.getVars w = [])
    (hmatch : ∀ x ∈ HasFvars.getFvars (P := Expression) e, ∀ w,
        declStore x = some w → opStore x = some w)
    (hdecl : evalBounded fb factory declStore e = some v) :
    evalBounded fb factory opStore e = some v := by
  let σ0 := fun x => if x ∈ HasFvars.getFvars e then declStore x else none
  have hcongr := Lambda.eval_env_congr (fun ⟨_, _⟩ ⟨_, _⟩ h => by cases h; rfl) fb factory
    declStore σ0 hWF (fun x v h => by grind) e (fun x hx => (ite_eq_left hx).symm)
  exact evalBounded_frame _ _ σ0 _ e v (fun x w h => by grind) (by
    rwa [evalBounded, ← hcongr, evalTypedDomain_congr (σr := σ0) (σr' := declStore)
      fun x hx => ite_eq_left hx, evalOpsChecked_congr (σr := σ0) (σr' := declStore)
      fun x hx => ite_eq_left hx])

/-- A `.isFalse` reduction under ANY evaluator `ev` forces the goal to evaluate under `ev` to a
    value the check reads as false (`isFf`). -/
private theorem reduceBool_isFalse_eval_gen
    {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    {Fa V : Type _} [DecidableEq V] (L : Imperative.ObligationEvaluator P Fa V) (factory : Fa)
    (σ : P.Ident → Option V) (Q : P.Expr)
    (h : Imperative.reduceBool' (P := P) L factory σ Q = .isFalse) :
    ∃ v, L.ev factory σ Q = some v ∧ L.isFf factory v = true := by
  grind [reduceBool']

/-- From `valuationObligationCheck' ops ev … = .genuine` under any evaluator `ev`, the
    assumptions thread to some `threaded` store, the goal reduces `.isFalse` there,
    and the assumptions reduce `.isTrue` there. -/
theorem genuine_decompose_gen
    {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    {Fa V : Type _} [DecidableEq V] (L : Imperative.ObligationEvaluator P Fa V)
    (factory : Fa) (store : P.Ident → Option V) (obligation : ProofObligation P)
    (hcex : Imperative.valuationObligationCheck' (P := P) L factory store obligation
        (isValidityCheck := true) = .genuine) :
    ∃ threaded,
      obligation.assumptions.foldlM
        (Imperative.extendWithVarDecls' (P := P) L factory · ·) store = some threaded
      ∧ Imperative.reduceBool' (P := P) L factory threaded obligation.obligation = .isFalse
      ∧ Imperative.assumptionsHold' (P := P) L factory threaded obligation.assumptions
        = .isTrue := by grind [valuationObligationCheck']

/-- A bounded evaluation transfers to a larger fuel and to a well-formed store extending the
    first on the expression's free variables. -/
theorem cel_agreeEval {factory : @Lambda.Factory CoreLParams} (hWF : Lambda.FactoryWF factory)
    {fb f : Nat} (hle : fb ≤ f)
      {σ σ' : RStore Expression}
    (hwf : RWellFormedStore σ' factory) {e v : Expression.Expr}
    (hm : ∀ x ∈ HasFvars.getFvars (P := Expression) e, ∀ w, σ x = some w → σ' x = some w)
    (h : evalBounded fb factory σ e = some v) : evalBounded f factory σ' e = some v :=
  evalBounded_mono hle _ _ _ _ (evalBounded_transfer_mono _ hWF _ _ _ _ _
    (fun x hx w h => Lambda.isValue_getVars_nil _ _ (hwf x w (hm x hx w h))) hm h)

/-- **The eval-bridge, packaged.**  A fuel-bounded level-`(b)` counterexample
    (`IsValuationObligationCexBounded … fb`) makes the goal evaluate under `evalBounded f`, on ANY
    run store `σRun` that agrees with the check's threaded declarative store on the goal's free
    variables (`fb ≤ f`), to a value equal to the false literal up to metadata
    (`InterpLang.eqModuloMeta`). -/
theorem bounded_cex_goal_false_on_agreeing_store
    (factory : @Lambda.Factory CoreLParams)
    (hWF : Lambda.FactoryWF factory)
    (store : RStore Expression) (obligation : ProofObligation Expression)
    (fb f : Nat) (hle : fb ≤ f)
    (hcexb : IsValuationObligationCexBounded factory store obligation fb)
    (σRun threaded : RStore Expression)
    (hthread : obligation.assumptions.foldlM
        (Imperative.extendWithVarDecls' (P := Expression)
            (.runtime (evalBounded fb)) factory · ·)
            store = some threaded)
    (hwfRun : RWellFormedStore σRun factory)
    (hagree : ∀ x ∈ HasFvars.getFvars obligation.obligation, σRun x = threaded x) :
    ∃ v, evalBounded f factory σRun obligation.obligation = some v ∧
      InterpLang.eqModuloMeta v (HasBool.ff (P := Expression)) = true := by
  obtain ⟨t, hfold, hgoal, -⟩ := genuine_decompose_gen _ _ _ _ hcexb
  cases hfold.symm.trans hthread
  obtain ⟨v, hv, hff⟩ := reduceBool_isFalse_eval_gen _ _ _ _ hgoal
  exact ⟨v, cel_agreeEval hWF hle hwfRun (fun x hx w h => (hagree x hx).trans h) hv, hff⟩

/-- **Cover dual of `reduceBool_isFalse_eval_gen`.**  A `.isTrue` reduction under ANY
    evaluator `ev` forces the goal to evaluate under `ev` to a value the check reads as true
    (`isTt`). -/
private theorem reduceBool_isTrue_eval_gen
    {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    {Fa V : Type _} [DecidableEq V] (L : Imperative.ObligationEvaluator P Fa V) (factory : Fa)
    (σ : P.Ident → Option V) (Q : P.Expr)
    (h : Imperative.reduceBool' (P := P) L factory σ Q = .isTrue) :
    ∃ v, L.ev factory σ Q = some v ∧ L.isTt factory v = true := by
  grind [reduceBool']

/-- **Cover dual of `genuine_decompose_gen`.**  From `valuationObligationCheck' … (isValidityCheck
    := false) = .genuine` the assumptions thread to some `threaded` store, and the goal
    (dual of the validity check's `.isFalse`) and the assumptions reduce `.isTrue` there. -/
theorem genuine_decompose_gen_cover
    {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    {Fa V : Type _} [DecidableEq V] (L : Imperative.ObligationEvaluator P Fa V)
    (factory : Fa) (store : P.Ident → Option V) (obligation : ProofObligation P)
    (hcex : Imperative.valuationObligationCheck' (P := P) L factory store obligation
        (isValidityCheck := false) = .genuine) :
    ∃ threaded,
      obligation.assumptions.foldlM
        (Imperative.extendWithVarDecls' (P := P) L factory · ·) store = some threaded
      ∧ Imperative.reduceBool' (P := P) L factory threaded obligation.obligation = .isTrue
      ∧ Imperative.assumptionsHold' (P := P) L factory threaded obligation.assumptions
        = .isTrue := by grind [valuationObligationCheck']

/-- **Cover dual of `bounded_cex_goal_false_on_agreeing_store`.**  A fuel-bounded
    level-`(b)` cover witness (`IsValuationObligationCovBounded … fb`) makes the goal evaluate under
    `evalBounded f`, on any run store agreeing with the check's threaded declarative store on
    the goal's free vars (`fb ≤ f`), to a value equal to the *true* literal up to metadata
    (`InterpLang.eqModuloMeta`). -/
theorem bounded_cov_goal_true_on_agreeing_store
    (factory : @Lambda.Factory CoreLParams)
    (hWF : Lambda.FactoryWF factory)
    (store : RStore Expression) (obligation : ProofObligation Expression)
    (fb f : Nat) (hle : fb ≤ f)
    (hcovb : IsValuationObligationCovBounded factory store obligation fb)
    (σRun threaded : RStore Expression)
    (hthread : obligation.assumptions.foldlM
        (Imperative.extendWithVarDecls' (P := Expression)
            (.runtime (evalBounded fb)) factory · ·)
            store = some threaded)
    (hwfRun : RWellFormedStore σRun factory)
    (hagree : ∀ x ∈ HasFvars.getFvars obligation.obligation, σRun x = threaded x) :
    ∃ v, evalBounded f factory σRun obligation.obligation = some v ∧
      InterpLang.eqModuloMeta v (HasBool.tt (P := Expression)) = true := by
  obtain ⟨t, hfold, hgoal, -⟩ := genuine_decompose_gen_cover _ _ _ _ hcovb
  cases hfold.symm.trans hthread
  obtain ⟨v, hv, htt⟩ := reduceBool_isTrue_eval_gen _ _ _ _ hgoal
  exact ⟨v, cel_agreeEval hWF hle hwfRun (fun x hx w h => (hagree x hx).trans h) hv, htt⟩

/-! ## The store-agreement invariant

`StoreAgreesThreaded σRun threaded`, the invariant of the reachability induction: the run store
agrees with the declarative `threaded` store wherever both are defined. -/

/-- The run/declarative store-agreement invariant: every variable that has a value `w` in
    the declarative store `threaded` and is defined in the run store `σRun` has value `w`
    in `σRun`. -/
def StoreAgreesThreaded (σRun threaded : RStore Expression) : Prop :=
  ∀ x w, threaded x = some w → (σRun x).isSome → σRun x = some w

/-- Every `.assumption` entry of the obligation's (flattened) path condition evaluates under
    `evalBounded fb` on the threaded declarative store to a value equal to the `tt` literal up
    to metadata (`InterpLang.eqModuloMeta`).  This is what a level-`(b)` check's
    `assumptionsHold' … = .isTrue` provides. -/
def AssumesHoldThreaded (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression) (threaded : RStore Expression) (fb : Nat) :
    Prop :=
  ∀ l e, Imperative.PathConditionEntry.assumption l e ∈ obligation.assumptions.flatten →
    ∃ v, evalBounded fb factory threaded e = some v ∧
      InterpLang.eqModuloMeta v (HasBool.tt (P := Expression)) = true

/-- A level-`(b)` assumption reduction to `.isTrue` on the threaded store makes every
    `.assumption` entry evaluate to `tt` up to metadata there (`AssumesHoldThreaded`). -/
theorem assumesHold_of_assumptionsHold (factory : @Lambda.Factory CoreLParams)
    (threaded : RStore Expression) (obligation : ProofObligation Expression) (fb : Nat)
    (hred : Imperative.assumptionsHold' (P := Expression)
        (.runtime (evalBounded fb)) factory threaded
        obligation.assumptions = .isTrue) :
    AssumesHoldThreaded factory obligation threaded fb := by
  exact fun _ _ he =>
    reduceBool_isTrue_eval_gen _ _ _ _ ((and_foldl_isTrue_forall _ _ _ hred).2 _ he)

/-- A det `init`/`set` write preserves `StoreAgreesThreaded` when the written value
    matches `threaded` wherever `threaded` is defined at that variable. -/
theorem storeAgreesThreaded_update (σRun threaded : RStore Expression)
    (name : Expression.Ident) (v : Expression.Expr)
    (h : StoreAgreesThreaded σRun threaded)
    (hmatch : ∀ w, threaded name = some w → w = v) :
    StoreAgreesThreaded (RStore.update σRun name v) threaded := by
  grind [RStore.update, StoreAgreesThreaded]

/-- With both stores defined at the goal's free variables, the invariant yields the
    pointwise agreement the eval-bridge needs. -/
theorem storeAgreesThreaded_pointwise (σRun threaded : RStore Expression)
    (e : Expression.Expr)
    (h : StoreAgreesThreaded σRun threaded)
    (hth : ∀ x ∈ HasFvars.getFvars e, (threaded x).isSome)
    (hσ : ∀ x ∈ HasFvars.getFvars e, (σRun x).isSome) :
    ∀ x ∈ HasFvars.getFvars e, σRun x = threaded x := fun x hx => by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hth x hx)
  rw [hw, h x w hw (hσ x hx)]

/-! ## Base store-agreement

The starting `StoreAgreesThreaded env.store.get threaded` of the drive, on the `env`
`valuationToEnv` reconstructs.  It needs the extraction provenance for the SSA disjointness of
the assumptions' variable definitions from the inputs (`extractLinked_all_ssa`), so `threaded`
agrees with the valuation on the inputs.  The frame lemmas are generic in the evaluator. -/

/-- Evaluator-generic single-scope frame: a scope with no `.det` varDecl of `x` leaves
    `x`'s binding unchanged. -/
theorem extendWithVarDecls'_frame_gen
    (L : ObligationEvaluator Expression (@Lambda.Factory CoreLParams) Expression.Expr)
    (F : @Lambda.Factory CoreLParams) :
    ∀ (sc : Imperative.PathCondition Expression) (s d : RStore Expression) (x : CoreIdent),
      Imperative.extendWithVarDecls' (P := Expression) L F s sc = some d →
      (∀ ty e, (Imperative.PathConditionEntry.varDecl x ty (.det e)) ∉ sc) →
      d x = s x := by
  intro sc s d x h hn
  fun_induction extendWithVarDecls' <;> grind [RStore.update]

/-- Evaluator-generic whole-`PathConditions` frame: scopes with no `.det` varDecl of `x`
    leave `x`'s binding unchanged. -/
private theorem extendWithVarDecls'_foldlM_frame_gen
    (L : ObligationEvaluator Expression (@Lambda.Factory CoreLParams) Expression.Expr)
    (F : @Lambda.Factory CoreLParams) (x : CoreIdent) :
    ∀ (pcs : Imperative.PathConditions Expression) (s d : RStore Expression),
      pcs.foldlM (Imperative.extendWithVarDecls' (P := Expression) L F · ·) s = some d →
      (∀ sc ∈ pcs, ∀ ty e, (Imperative.PathConditionEntry.varDecl x ty (.det e)) ∉ sc) →
      d x = s x := fun pcs => by
  induction pcs <;> grind [Option.bind_eq_some_iff, extendWithVarDecls'_frame_gen L F _ _ _ x]

/-- The single-scope `extendWithVarDecls'` fold is **monotone on definedness**: it
    only ever `update`s the store (adds/overwrites bindings), never clears one, so a
    name defined in the input store stays defined in the output. -/
private theorem extendWithVarDecls'_domain_mono
    (L : ObligationEvaluator Expression (@Lambda.Factory CoreLParams) Expression.Expr)
    (F : @Lambda.Factory CoreLParams) :
    ∀ (sc : Imperative.PathCondition Expression) (s d : RStore Expression) (x : CoreIdent),
      Imperative.extendWithVarDecls' (P := Expression) L F s sc = some d →
      (s x).isSome → (d x).isSome := by
  intro sc s d x h hx
  fun_induction extendWithVarDecls' <;> grind [RStore.update]

/-- Whole-`PathConditions` monotonicity on definedness: a name defined in the input
    store is defined in the fully threaded store. -/
theorem extendWithVarDecls'_foldlM_domain_mono
    (L : ObligationEvaluator Expression (@Lambda.Factory CoreLParams) Expression.Expr)
    (F : @Lambda.Factory CoreLParams) (x : CoreIdent) :
    ∀ (pcs : Imperative.PathConditions Expression) (s d : RStore Expression),
      pcs.foldlM (Imperative.extendWithVarDecls' (P := Expression) L F · ·) s = some d →
      (s x).isSome → (d x).isSome := fun pcs => by
  induction pcs <;>
    grind [Option.bind_eq_some_iff, extendWithVarDecls'_domain_mono L F _ _ _ x]

/-- Evaluator-generic append inversion: folding a scope `pre ++ suf` factors through an
    intermediate store `m` reached by folding `pre`. -/
private theorem extendWithVarDecls'_append_inv_gen
    (L : ObligationEvaluator Expression (@Lambda.Factory CoreLParams) Expression.Expr)
    (F : @Lambda.Factory CoreLParams) :
    ∀ (pre suf : Imperative.PathCondition Expression) (s d : RStore Expression),
      Imperative.extendWithVarDecls' (P := Expression) L F s (pre ++ suf) = some d →
      ∃ m, Imperative.extendWithVarDecls' (P := Expression) L F s pre = some m
        ∧ Imperative.extendWithVarDecls' (P := Expression) L F m suf = some d := by
  intro pre suf s d h
  fun_induction extendWithVarDecls' <;> grind [extendWithVarDecls']

/-- Evaluator-generic `.det`-varDecl value: the fold binds `name` to the value `v` of `e'`
    evaluated after `pre`, given `name` is not re-declared later in the scope. -/
theorem scope_det_value_gen
    (L : ObligationEvaluator Expression (@Lambda.Factory CoreLParams) Expression.Expr)
    (F : @Lambda.Factory CoreLParams)
    (name : CoreIdent) (ty : Expression.Ty) (e' : Expression.Expr)
    (pre suf : Imperative.PathCondition Expression)
    (store threaded : RStore Expression)
    (hfold : Imperative.extendWithVarDecls' (P := Expression) L F store
        (pre ++ Imperative.PathConditionEntry.varDecl name ty (.det e') :: suf) = some threaded)
    (hnotsuf : ∀ ty'' e'', Imperative.PathConditionEntry.varDecl name ty'' (.det e'') ∉ suf) :
    ∃ dpre v, Imperative.extendWithVarDecls' (P := Expression) L F store pre = some dpre
      ∧ L.ev F dpre e' = some v
      ∧ L.valOk F v ty = true
      ∧ threaded name = some v
      ∧ Imperative.extendWithVarDecls' (P := Expression) L F
          (RStore.update dpre name v) suf = some threaded := by
  obtain ⟨m, hpre, hsuf⟩ := extendWithVarDecls'_append_inv_gen _ F _ _ _ _ hfold
  simp only [extendWithVarDecls'] at hsuf
  split at hsuf
  · rename_i v hv
    split at hsuf
    · refine ⟨m, v, hpre, hv, ‹_›, ?_, hsuf⟩
      rw [extendWithVarDecls'_frame_gen _ F _ _ _ name hsuf hnotsuf]
      simp
    · cases hsuf
  · cases hsuf

/-- **Base store-agreement invariant** — the drive's starting `StoreAgreesThreaded`.
    Given the extraction provenance (`hok`/`hmem`), the reconstructed `env`, the
    shape check, and the `evalBounded fb`-threaded declarative store `threaded`,
    the run store `env.store` agrees with `threaded` wherever both are defined. -/
theorem drive_base_store_agreement
    (factory : @Lambda.Factory CoreLParams) (unit : PassiveUnit)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (store : RStore Expression) (env : IEnv Expression)
    (oracle : OracleSeed) (fb f : Nat) (threaded : RStore Expression)
    (pc0 : Imperative.RevPathConditions Expression) (hpc0 : RootPc pc0)
    (arr : Array ObligationExtraction.LinkedObligation)
    (hok : ObligationExtraction.extractLinkedFromStatements pc0 link.entryStatements = .ok arr)
    (hmem : (obligation, link) ∈ arr.toList)
    (hv : valuationToEnv factory unit obligation link store = .ok (env, oracle))
    (hshape : checkObligationProgram (unit.inputs.map (·.1)) link.entryStatements = some f)
    (hthread : obligation.assumptions.foldlM
      (Imperative.extendWithVarDecls' (P := Expression)
          (.runtime (evalBounded fb)) factory · ·)
          store = some threaded) :
    StoreAgreesThreaded env.store.get threaded := by
  obtain ⟨hcheck, -, hinputs, -⟩ := checkObligationProgram_some hshape
  obtain ⟨-, hdisj⟩ := extractLinked_all_ssa _ _ _ _ _ hok hmem hpc0 hinputs hcheck
  intro x w h hx
  have hin := valuationToEnv_inputs_only _ _ _ _ _ _ _ hv x hx
  rw [extendWithVarDecls'_foldlM_frame_gen _ _ x _ _ _ hthread fun sc hsc ty e hd =>
    hdisj x (by
      simp only [allVarNames, List.mem_flatMap, List.mem_flatten]
      exact ⟨_, ⟨sc, hsc, hd⟩, by simp!⟩) hin] at h
  apply_rules [valuationToEnv_entry_agrees]

end
end Core
