/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReplayProps
public import Strata.Languages.Core.ConfigWF
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.StatementSemantics
import all Strata.Languages.Core.ConfigWF
import Strata.Languages.Core.InterpreterReplayTactics
import Strata.DL.Lambda.LExprEvalFuelProps
public import Strata.DL.Imperative.InterpreterReplayProps
public import Strata.Languages.Core.ConfigWFProps

/-! # Replay steps keep stores closed and configurations well-formed

Key definitions:
* `OkPost X Q`: every successful result of the `ReplayM` computation `X` satisfies `Q`.
* `CfgStoresClosed`: every store a configuration holds is closed.
* `StepStoresClosed`, `StepWF`: a command stepper keeps stores closed, resp. configurations
  well-formed.

Key theorems:
* `stepInterp_storesClosed`, `runInterp_storesClosed`: under `StepStoresClosed`, every step and
  every run keeps every store closed.
* `replayStepCmd_stepWF`: Core's command stepper satisfies `StepWF`.
* `stepInterp_cfgWF`: under `StepWF`, a step keeps the configuration well-formed. -/

namespace Core

open Imperative

public section

/-! ## Successful outcomes of a `ReplayM` computation -/

/-- The full `ReplayM` run projection. -/
abbrev wrun {α : Type} (X : ReplayM Expression α) (cfg : ReplayCfg Expression)
    (s : ReplayState Expression) : Except StopReason α × ReplayState Expression :=
  ((X.run cfg).run).run s

/-- Every successful result of `X` (any run configuration, any state) satisfies `Q`. -/
@[expose] def OkPost {α : Type} (X : ReplayM Expression α) (Q : α → Prop) : Prop :=
  ∀ cfg s a s', wrun X cfg s = (.ok a, s') → Q a

namespace OkPost

/-- Every successful result of `pure a` satisfies `Q` when `Q a` holds. -/
theorem pure {α : Type} {Q : α → Prop} {a : α} (h : Q a) :
    OkPost (Pure.pure a : ReplayM Expression α) Q := by
  rintro _ _ _ _ ⟨⟩
  exact h

/-- `throw e` has no successful result, so `OkPost (throw e) Q` holds for every `Q`. -/
theorem throw {α : Type} {Q : α → Prop} (e : StopReason) :
    OkPost (MonadExcept.throw e : ReplayM Expression α) Q := nofun

/-- `throw e` through `MonadExceptOf` has no successful result, so `OkPost` holds for every
    postcondition. -/
theorem throw' {α : Type} {Q : α → Prop} (e : StopReason) :
    OkPost (MonadExceptOf.throw e : ReplayM Expression α) Q := nofun

/-- Every successful result of `x >>= g` satisfies `Q` when every successful result `a` of `x`
    satisfies `R` and, for every such `a`, every successful result of `g a` satisfies `Q`. -/
private theorem bind {α β : Type} {x : ReplayM Expression α} {g : α → ReplayM Expression β}
    {R : α → Prop} {Q : β → Prop} (hx : OkPost x R) (hg : ∀ a, R a → OkPost (g a) Q) :
    OkPost (x >>= g) Q := by grind [OkPost, replayM_run_bind]

/-- A postcondition every successful result of `X` satisfies can be weakened: if `Q` implies
    `R`, every successful result of `X` satisfies `R`. -/
private theorem mono {α : Type} {X : ReplayM Expression α} {Q R : α → Prop} (h : OkPost X Q)
    (hQR : ∀ a, Q a → R a) : OkPost X R := fun c s a s' e => hQR a (h c s a s' e)

/-- Every successful result of every computation satisfies the trivial postcondition `True`. -/
private theorem true {α : Type} (X : ReplayM Expression α) : OkPost X (fun _ => True) := by
  simp [OkPost]

end OkPost

/-! ## Closed values -/

/-- A value `evalBounded` returns is canonical, hence closed. -/
private theorem evalBounded_closed {fuel : Nat} {F : Lambda.Factory CoreLParams}
    {σ : RStore Expression} {e v : Expression.Expr}
    (h : evalBounded fuel F σ e = some v) : Lambda.LExpr.LExpr.getVars v = [] := by
  revert h
  unfold evalBounded
  split <;> grind [Lambda.isValue_getVars_nil, Lambda.eval_value_isValue]

/-- Every value `evalBoundedList` returns is closed. -/
private theorem evalBoundedList_closed {fuel : Nat} {F : Lambda.Factory CoreLParams}
    {σ : RStore Expression} :
    ∀ {es vs : List Expression.Expr}, Calls.evalBoundedList fuel F σ es = some vs →
      ∀ v ∈ vs, Lambda.LExpr.LExpr.getVars v = [] := by
  intro es
  fun_induction Calls.evalBoundedList <;>
    simp_all only [InterpLang.boundedEval, Option.some.injEq, Option.map_eq_some_iff,
      List.nil_eq, List.not_mem_nil, List.mem_cons, forall_exists_index, forall_eq_or_imp,
      forall_apply_eq_imp_iff₂, and_imp, and_true, false_implies, implies_true, reduceCtorEq] <;>
    grind [evalBounded_closed]

/-- Every value `readVarList` reads from a closed store is closed. -/
private theorem readVarList_closed {σ : RStore Expression} (hσ : StoreClosed σ) :
    ∀ {names : List Expression.Ident} {vs : List Expression.Expr},
      Calls.readVarList σ names = some vs → ∀ v ∈ vs, Lambda.LExpr.LExpr.getVars v = [] := by
  intro ns
  fun_induction Calls.readVarList <;>
    simp_all only [Option.some.injEq, Option.map_eq_some_iff,
      List.nil_eq, List.not_mem_nil, List.mem_cons, forall_exists_index, forall_eq_or_imp,
      forall_apply_eq_imp_iff₂, and_imp, and_true, false_implies, implies_true, reduceCtorEq] <;>
    grind [StoreClosed]

/-- Binding closed values positionally into a closed store yields a closed store. -/
theorem bindPositional_closed :
    ∀ {σ : RStore Expression} (_ : StoreClosed σ) (names : List Expression.Ident)
      (vs : List Expression.Expr), (∀ v ∈ vs, Lambda.LExpr.LExpr.getVars v = []) →
      StoreClosed (bindPositional σ names vs) := fun _ _ _ _ => by
  unfold bindPositional
  fun_induction Calls.bindPositional <;> grind [StoreClosed, Calls.storeUpdate]

/-- `withOldSnapshots` keeps a store closed. -/
private theorem withOldSnapshots_closed {σ : RStore Expression} (hσ : StoreClosed σ)
    (names : List Expression.Ident) : StoreClosed (Calls.withOldSnapshotsV names σ) := by
  grind [StoreClosed, Calls.withOldSnapshotsV]

/-- Projecting a closed store through any parent store yields a closed store. -/
private theorem projectStore_closed {σp σ : RStore Expression} (hσ : StoreClosed σ) :
    StoreClosed (RStore.project σp σ) := by grind [StoreClosed, RStore.project]

/-- Exiting a block through any scope frame from a closed store yields a closed store. -/
private theorem ScopeFrame.exit_closed (fr : ScopeFrame Expression) {σ : IStore Expression}
    (hσ : StoreClosed σ.get) : StoreClosed (fr.exit σ).get := by
  unfold ScopeFrame.exit
  split
  · rw [IStore.get_drop (P := Expression)]
    grind [StoreClosed, RStore.dropVars]
  · simpa using projectStore_closed hσ

/-- The callee entry frame built from closed input and output values is closed. -/
private theorem callEntryStore_closed (p : Procedure)
    {inputVals outOnlyVals : List Expression.Expr}
    (hi : ∀ v ∈ inputVals, Lambda.LExpr.LExpr.getVars v = [])
    (ho : ∀ v ∈ outOnlyVals, Lambda.LExpr.LExpr.getVars v = []) :
    StoreClosed (Calls.callEntryStore p inputVals outOnlyVals) :=
  withOldSnapshots_closed
    (bindPositional_closed (bindPositional_closed .empty _ _ hi) _ _ ho) _

/-- Every value of the list is closed (executable). -/
@[expose] def allClosed (vs : List Expression.Expr) : Bool :=
  vs.all fun v => (Lambda.LExpr.LExpr.getVars v).isEmpty

/-- `allClosed vs = true` means every value of `vs` has no free variables. -/
theorem allClosed_spec {vs : List Expression.Expr} (h : allClosed vs = true) :
    ∀ v ∈ vs, Lambda.LExpr.LExpr.getVars v = [] := by simp_all [allClosed]

/-! ## Effects -/

/-- A value `choose` resolves in `ReplayM` is closed. -/
theorem OkPost.choose (factory : Lambda.Factory CoreLParams) (store : RStore Expression)
    (ty : Expression.Ty) :
    OkPost (InterpEffects.choose (m := ReplayM Expression) factory store ty)
      (fun v => Lambda.LExpr.LExpr.getVars v = []) := by
  intro _ _ _ _ h
  obtain ⟨⟨hv, -⟩, -⟩ := replayRun_choose _ _ _ _ _ _ _ h
  exact Lambda.isValue_getVars_nil _ _ hv

/-! ## Base commands keep stores closed -/

/-- A successful base command step from a closed store yields a closed store. -/
private theorem stepBaseCmdStore_closed (k : Nat) (factory : Lambda.Factory CoreLParams)
    {store : IStore Expression} (hσ : StoreClosed store.get) (c : Cmd Expression) :
    OkPost (stepBaseCmdStore (m := ReplayM Expression) k factory store c) (StoreClosed ·.get) := by
  simp only [stepBaseCmdStore]
  repeat' first
    | with_reducible exact .pure hσ
    | with_reducible refine .bind (.choose _ _ _) fun _ h => ?_
    | with_reducible refine .bind (.true _) fun _ _ => ?_
    | split
    | exact .pure (IStore.get_update (P := Expression) .. ▸
        hσ.update _ (by first | exact h | exact evalBounded_closed ‹_›))
    | nofun

/-! ## Every step keeps every store closed -/

/-- Every store a configuration holds (active and enclosing blocks' parents) is closed. -/
@[expose] def CfgStoresClosed {CmdT : Type} : IConfig Expression CmdT → Prop
  | .stmt _ ρ => StoreClosed ρ.store.get
  | .stmts _ ρ => StoreClosed ρ.store.get
  | .terminal ρ => StoreClosed ρ.store.get
  | .exiting _ ρ => StoreClosed ρ.store.get
  | .block _ fr inner => StoreClosed fr.parent.get ∧ CfgStoresClosed inner
  | .seq inner _ => CfgStoresClosed inner
  | .seqs inner _ => CfgStoresClosed inner

/-- The active environment's store of a `CfgStoresClosed` configuration is closed. -/
private theorem CfgStoresClosed.getEnv {CmdT : Type} :
    ∀ {c : IConfig Expression CmdT}, CfgStoresClosed c → StoreClosed c.getEnv.store.get := by
  intro c
  induction c <;> simp_all!

/-- A property of configurations that ignores one sequence context with no remaining statements
    ignores every sequence tower: it holds of `c` under `k` such contexts exactly when it holds of
    `c`. -/
private theorem wrapSeqs_iff {CmdT : Type} {Q : IConfig Expression CmdT → Prop}
    (hQ : ∀ c, Q (.seq c []) ↔ Q c) (c : IConfig Expression CmdT) (k : Nat) :
    Q (c.wrapSeqs k) ↔ Q c := by
  induction k <;> simp_all [IConfig.wrapSeqs]

/-- The command stepper keeps stores closed: every successful step from an environment whose
    store is closed (no stored value has a free variable) yields a configuration whose stores are
    all closed (`CfgStoresClosed` of the semantic configuration `IConfig.abs` it stands for). -/
@[expose] def StepStoresClosed (sc : StepCmdM Expression Command (ReplayM Expression)) : Prop :=
  ∀ k env cmd, StoreClosed env.store.get → OkPost (sc k env cmd) (CfgStoresClosed ·)

/-- **Every step keeps every store closed**: if every successful command step of `sc` from a closed
    store (no stored value has a free variable) yields a configuration whose stores are all closed
    (`StepStoresClosed`), then a successful `stepInterp` step from a configuration whose stores are
    all closed (`CfgStoresClosed` of the semantic configuration `IConfig.abs` it stands for)
    yields such a configuration. -/
theorem stepInterp_storesClosed {sc : StepCmdM Expression Command (ReplayM Expression)}
    (hsc : StepStoresClosed sc) :
    ∀ (c : IConfig Expression Command) (k : Nat), CfgStoresClosed c →
      OkPost (stepInterp sc k c) (CfgStoresClosed ·) := fun _ _ _ => by
  fun_induction stepInterp <;>
    (first
      | apply hsc
      | with_reducible refine .bind (‹_ → _› ?_) fun _ _ => .pure ?_
      | (refine .bind (‹_ → _› ?_) fun _ _ => ?_
         rotate_left
         split <;> refine .pure ?_)
      | with_reducible refine .pure ?_
      | (refine .bind (.true _) fun _ _ => ?_
         (repeat' split) <;> first | exact .throw _ | refine .pure ?_)
      | nofun) <;>
    grind [CfgStoresClosed, IConfig.abs, IEnv.abs, ScopeFrame.opened, ScopeFrame.record_parent,
      ScopeFrame.exit_closed, wrapSeqs_iff (Q := CfgStoresClosed) fun _ => .rfl]

/-- **Every run keeps every store closed**: if every successful command step of `sc` from a
    closed store (no stored value has a free variable) yields a configuration whose stores are all
    closed (`StepStoresClosed`), then a successful `runInterp` run from a configuration whose
    stores are all closed (`CfgStoresClosed` of the semantic configuration `IConfig.abs` it stands
    for) ends in such a configuration. -/
theorem runInterp_storesClosed {sc : StepCmdM Expression Command (ReplayM Expression)}
    (hsc : StepStoresClosed sc) :
    ∀ (n : Nat) (c : IConfig Expression Command), CfgStoresClosed c →
      OkPost (runInterp sc n c) (CfgStoresClosed ·) := fun _ _ hc => by
  fun_induction runInterp <;> first
    | exact .pure hc
    | exact .bind (stepInterp_storesClosed hsc _ _ hc) ‹_›
    | nofun

/-- A successful callee body run (`Calls.runCallee`) from a closed entry store, over a command
    stepper that keeps stores closed, returns a closed store. -/
private theorem runCallee_closed {sc : StepCmdM Expression Command (ReplayM Expression)}
    (hsc : StepStoresClosed sc) (procName : String) (body : Body Expression Command)
    (fac : InterpLang.RFactory Expression) (n : Nat) {σ : RStore Expression} (h : StoreClosed σ) :
    OkPost (Calls.runCallee sc procName body fac n σ) StoreClosed := by
  cases body <;> simp only [Calls.runCallee]
  · refine .bind (runInterp_storesClosed hsc _ _
      (by simpa [IConfig.abs, IEnv.abs, CfgStoresClosed] using h)) fun c hc => ?_
    split
    · exact .pure hc
    · exact .throw _
  · exact .throw _

/-- From a closed store, every successful step of Core's command stepper yields a terminal
    configuration with the caller's factory and a closed store. -/
private theorem replayStepCmd_closed (π : String → Option Procedure) :
    ∀ (d k : Nat) (env : IEnv Expression) (cmd : Command), StoreClosed env.store.get →
      OkPost (replayStepCmd (m := ReplayM Expression) π d k env cmd)
        (fun c => ∃ ρ, c = .terminal ρ ∧ ρ.factory = env.factory ∧ StoreClosed ρ.store.get) :=
    fun _ _ _ _ h => by
  have hbp (s : IStore Expression) (ns : List Expression.Ident) (vs : List Expression.Expr)
      (hs : StoreClosed s.get) (hvs : ∀ v ∈ vs, Lambda.LExpr.LExpr.getVars v = []) :
      StoreClosed (s.bindPositional ns vs).get := by
    fun_induction IStore.bindPositional
    · rename_i ih
      exact ih (by simpa using hs.update _ (hvs _ (.head _))) fun v hv => hvs v (.tail _ hv)
    · exact hs
  unfold replayStepCmd
  fun_induction Calls.stepCmd <;> rename_i ih <;> (try dsimp +zetaDelta only) <;> repeat' first
    | with_reducible exact .bind (stepBaseCmdStore_closed _ _ h _) fun _ h => .pure ⟨_, rfl, rfl, h⟩
    | split
    | refine .bind (runCallee_closed (fun _ => (ih · · · |>.mono fun _ ⟨_, e, _, h⟩ => e ▸ h)) _ _ _ _
        (callEntryStore_closed _ (evalBoundedList_closed ‹_›) (readVarList_closed h ‹_›)))
          fun _ _ => ?_
    | with_reducible refine .bind (.true _) fun _ _ => ?_
    | exact .pure ⟨_, rfl, rfl, hbp _ _ _ h (readVarList_closed ‹_› ‹_›)⟩
    | nofun

/-! ## Steps keep configurations well-formed -/

/-- The command stepper keeps configurations well-formed: every successful step from a
    well-formed environment (`EnvWF`: well-formed factory, closed store) yields a configuration
    whose factories and stores are all well-formed (`CfgWF` of the semantic configuration
    `IConfig.abs` it stands for). -/
@[expose] def StepWF (sc : StepCmdM Expression Command (ReplayM Expression)) : Prop :=
  ∀ k env cmd, EnvWF env → OkPost (sc k env cmd) (CfgWF ·)

/-- For every callee table `π` and call-depth budget `d`, every successful step of
    `replayStepCmd π d` from a well-formed environment (well-formed factory, closed store) yields
    a configuration whose factories and stores are all well-formed (`StepWF`). -/
theorem replayStepCmd_stepWF (π : String → Option Procedure) (d : Nat) :
    StepWF (fun k env cmd => replayStepCmd (m := ReplayM Expression) π d k env cmd) :=
  fun k e c h => (replayStepCmd_closed π d k e c h.2).mono
    fun _ ⟨ρ, e, f, s⟩ => e ▸ ⟨(f ▸ h.1 : FactoryOK ρ.factory), s⟩

/-- **Steps keep configurations well-formed**: if every successful command step of `sc` from a
    well-formed environment yields a well-formed configuration (`StepWF`), then a successful
    `stepInterp` step from a configuration whose factory and stores are all well-formed
    (`CfgWF` of the semantic configuration `IConfig.abs` it stands for) yields such a
    configuration. -/
theorem stepInterp_cfgWF {sc : StepCmdM Expression Command (ReplayM Expression)}
    (hsc : StepWF sc) :
    ∀ (c : IConfig Expression Command) (k : Nat), CfgWF c →
      OkPost (stepInterp sc k c) (CfgWF ·) := fun _ _ _ => by
  fun_induction stepInterp <;>
    (first
      | apply hsc
      | refine .bind (‹_ → _› ?_) fun _ _ => .pure ?_
      | (refine .bind (‹_ → _› ?_) fun _ _ => ?_
         rotate_left
         split <;> refine .pure ?_)
      | with_reducible refine .pure ?_
      | (refine .bind (.true _) fun _ _ => ?_
         (repeat' split) <;> first | exact .throw _ | refine .pure ?_)
      | nofun) <;>
    grind [CfgWF, EnvWF, IConfig.abs, IEnv.abs, ScopeFrame.opened, ScopeFrame.record_parent,
      ScopeFrame.exit_closed, wrapSeqs_iff (Q := CfgWF) fun _ => .rfl]

end -- public section

end Core
