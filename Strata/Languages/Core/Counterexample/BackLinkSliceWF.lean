/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkChainReplay
public import Strata.Languages.Core.Counterexample.BackLinkCallElim
public import Strata.Languages.Core.Counterexample.BackLinkLoopElim
public import Strata.Languages.Core.ReplayWF
public import Strata.DL.Imperative.InterpreterCallEmbed
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterObs
import all Strata.Languages.Core.ConfigWF
import all Strata.Languages.Core.ReplayWF
import all Strata.Languages.Core.Counterexample.BackLinkChainReplay
import all Strata.Languages.Core.Counterexample.BackLinkCallElim
import all Strata.Languages.Core.Counterexample.BackLinkLoopElim
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Replay-based back-links keep chains well-formed

A configuration is well-formed (`CfgWF`) when every factory and store it holds, active or
enclosing, is well-formed (`EnvWF`: a well-formed factory and a closed store); a
counterexample is well-formed (`CexWF`) when its start configuration is.  The chain
elements a replay-based back-link emits start at configurations it built from
well-formed ones:

* the chain walk (`chainWalk`) proposes a claim whose start is the start of an incoming
  slice or of the incoming claim (`chainWalk_claim_wf`);
* the slicing replay (`sliceRun`) opens slices at its start, at a handler's cut
  configuration, or at a configuration a replay step reached
  (`sliceRun_wf`, from the handler obligation `HandlerWF`); the `callElim` and `loopElim`
  slicers meet it (`callElimSlice_wf`, `loopElimSlice_wf`);
* the downstream-to-upstream configuration maps of `callElim` and `loopElim` keep
  well-formedness (`uncallElimConfig_wf`, `unloopElimConfig_wf`), and so does dropping
  the fresh variables of `callElim` (`dropFreshEnv_wf`);
* embedding a base-command configuration preserves and reflects well-formedness
  (`cfgWF_embedConfig`, `embedOutcome_chain`).

Key definitions: `CutWF`, `HandlerWF`. -/

namespace Core

open Imperative

public section

/-! ## The next-statement frame -/

/-- The environment of the next statement of a well-formed configuration (`CfgWF`: its
    factory and every store it holds are well-formed) is well-formed (`EnvWF`). -/
private theorem focus_envWF :
    ∀ {c : IConfig Expression Command} {s : Statement} {env : IEnv Expression} {d : Nat},
      IConfig.focus c = some (s, env, d) → CfgWF c → EnvWF env := by
  intro c
  induction c <;> simp only [IConfig.focus, CfgWF, Option.map_eq_some_iff] <;> grind

/-- The environment of the next command of a well-formed configuration (`CfgWF`) is
    well-formed (`EnvWF`: a well-formed factory and a closed store). -/
private theorem nextCmd?_envWF {c : IConfig Expression Command} {cmd : Command}
    {env : IEnv Expression} (h : IConfig.nextCmd? c = some (cmd, env))
    (hw : CfgWF c) :
    EnvWF env := by grind [IConfig.nextCmd?, focus_envWF]

/-- Replacing the next-statement frame of a well-formed configuration (`CfgWF`: every
    factory and store it holds is well-formed) by a well-formed one keeps it well-formed. -/
private theorem replaceNextStmt_wf {r : IConfig Expression Command} (hr : CfgWF r) :
    ∀ {c : IConfig Expression Command}, CfgWF c → CfgWF (IConfig.replaceNextStmt r c) := by
  intro c
  induction c <;> simp_all [CfgWF, IConfig.replaceNextStmt]

/-- Binding closed values positionally keeps the store an interpreter store stands for closed
    (`StoreClosed`: every value has no free variables). -/
private theorem iBindPositional_closed {σ : IStore Expression} (h : StoreClosed σ.get)
    (names : List Expression.Ident) (vs : List Expression.Expr)
    (hv : ∀ v ∈ vs, Lambda.LExpr.LExpr.getVars v = []) :
    StoreClosed (σ.bindPositional names vs).get :=
  Imperative.IStore.get_bindPositional σ names vs ▸ bindPositional_closed h names vs hv

/-! ## The slicing replay -/

/-- A cut step continues only from well-formed configurations. -/
@[expose] def CutWF {H : Type} : CutStep H → Prop
  | .moved next _ _ => CfgWF next
  | .cut next _ _ _ => CfgWF next
  | _ => True

/-- The obligation of a cut handler: every configuration it continues from (a move or
    a cut) is well-formed when the configuration it was consulted at is. -/
@[expose] def HandlerWF {H : Type} (handler : CutHandler H) : Prop :=
  ∀ h fuel c st, CfgWF c → CutWF (handler h fuel c st)

/-- Every slice and the claim of a slicing replay from a well-formed start (`CexWF`: every
    factory and store of the start configuration is well-formed) are well-formed, when the
    cut handler only continues from well-formed configurations (`HandlerWF`). -/
theorem sliceRun_wf {H : Type} (π : String → Option Procedure) (target : AssertId Expression)
    (fuel : Nat) (handler : CutHandler H) (hH : HandlerWF handler) (h₀ : H)
    (start : CexA Expression Command) (hs : CexWF start) :
    (∀ x ∈ (sliceRun π target fuel handler h₀ start).slices, CexWF x) ∧
    (∀ c f, (sliceRun π target fuel handler h₀ start).claim = some (c, f) → CexWF c) := by
  suffices hgo : ∀ n h c st ss so acc, CfgWF c → CfgWF ss → (∀ x ∈ acc, CexWF x) →
      (∀ x ∈ (sliceRun.go π _ _ _ n h c st ss so acc).slices, CexWF x) ∧
      ∀ c' f, (sliceRun.go π _ _ _ n h c st ss so acc).claim = some (c', f) → CexWF c' from
    hgo _ _ _ _ _ _ _ hs hs nofun
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro h c st ss so acc hc hss hacc
    have hcut := hH h fuel c st hc
    unfold sliceRun.go
    simp only
  all_goals
    (repeat' split) <;> (try rw [‹handler _ _ _ _ = _›] at hcut) <;> first
      | exact ih _ _ _ _ _ _ hcut hss hacc
      | exact ih _ _ _ _ _ _ hcut hcut (List.forall_mem_cons.2 ⟨hss, hacc⟩)
      | exact ih _ _ _ _ _ _ (stepInterp_cfgWF (replayStepCmd_stepWF π _) c _ hc _ _ _ _ ‹_›) hss
          hacc
      | grind [CexWF]

/-- The configuration the real call of `callTowardOutputs` continues from, a replay step of a
    well-formed configuration (`CfgWF`), is well-formed. -/
private theorem callTowardOutputs_wf {π : String → Option Procedure} {target : AssertId Expression}
    {fuel : Nat} {c c' : IConfig Expression Command} {st st' : ReplayState Expression}
    {lhs : List Expression.Ident} {values remaining : List Expression.Expr} (hc : CfgWF c)
    (h : callTowardOutputs π target fuel c st lhs values remaining = some (c', st')) :
    CfgWF c' := by
  unfold callTowardOutputs at h
  split at h
  · rename_i heq
    split at h
    · cases h
      exact stepInterp_cfgWF (replayStepCmd_stepWF π _) c fuel hc _ _ _ _ heq
    · cases h
  · cases h

/-- The `callElim` cut handler satisfies `HandlerWF` (every configuration it continues
    from is well-formed when the one it was consulted at is): its real call is a replay step,
    and its cut binds closed values (it stops on any other) in the call's frame. -/
private theorem callElimCutHandler_wf (π : String → Option Procedure) (target : AssertId Expression)
    (origins : List CallElim.CallOrigin) : HandlerWF (callElimCutHandler π target
        origins) := fun _ _ _ _ hc => by
  unfold callElimCutHandler
  simp only
  (repeat' split) <;> try trivial
  all_goals first
    | exact callTowardOutputs_wf hc ‹_›
    | (have henv := nextCmd?_envWF (by assumption) hc
       refine replaceNextStmt_wf ?_ hc
       exact ⟨henv.1, iBindPositional_closed henv.2 _ _
         (allClosed_spec (by simpa using ‹¬(!_) = true›))⟩)

/-- At a well-formed configuration (`CfgWF`) whose next statement is a loop, the
    `loopElim` loop-entry step satisfies `CutWF` (a move or a cut continues from a
    well-formed configuration). -/
private theorem loopEntry_wf (π : String → Option Procedure) (target : AssertId Expression)
    (fuel : Nat) (c : IConfig Expression Command) (st : ReplayState Expression)
    (active : ActiveLoops) (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (invariants : List (String × Expression.Expr)) (body : List Statement)
    (md : Imperative.MetaData Expression) (env : IEnv Expression)
    (loop : Statement) (body' : List Statement) (carried : List Expression.Ident)
    {d : Nat} (hnext : IConfig.focus c = some (.loop guard measure invariants body md, env, d))
    (hc : CfgWF c) :
    CutWF (loopElimLoopEntry π target fuel c st active loop body' env carried) := by
  have henv := focus_envWF hnext hc
  unfold loopElimLoopEntry
  (repeat' split) <;> first
    | trivial
    | exact replaceNextStmt_wf (by
        have hσ := iBindPositional_closed henv.2 carried _
          (allClosed_spec (by simpa using ‹¬(!_) = true›))
        exact ⟨hσ, henv.1, hσ⟩) hc
    | exact stepInterp_cfgWF (replayStepCmd_stepWF π _) c fuel hc _ _ _ _ ‹_›

/-- The `loopElim` cut handler satisfies `HandlerWF`: every configuration it continues
    from is well-formed when the one it was consulted at is. -/
private theorem loopElimCutHandler_wf (π : String → Option Procedure)
    (target : AssertId Expression) :
    HandlerWF (loopElimCutHandler π target) := by
  intro _ fuel c _ hc
  unfold loopElimCutHandler
  simp only
  split
  · rename_i hnext
    have henv := focus_envWF hnext hc
    (repeat' split) <;> first
      | trivial
      | solve_by_elim [loopEntry_wf]
      | (refine replaceNextStmt_wf ?_ hc
         exact ⟨henv.1, iBindPositional_closed henv.2 _ _
           (allClosed_spec (by simpa using ‹¬(!_) = true›))⟩)
  · (repeat' split) <;> first
      | trivial
      | exact stepInterp_cfgWF (replayStepCmd_stepWF π _) c fuel hc _ _ _ _ ‹_›

/-! ## The chain walk -/

/-- The claim the chain walk proposes starts at the start of an incoming slice or of the
    incoming claim, so it is well-formed (`CexWF`) when they all are. -/
theorem chainWalk_claim_wf (π : String → Option Procedure) (target : AssertId Expression)
    (defaults : @Lambda.Factory CoreLParams → RStore Expression → Expression.Ty →
      Option Expression.Expr) (fuel : Nat)
    (slices : List (CexA Expression Command)) (claim : Option (CexA Expression Command × Nat))
    (hs : ∀ x ∈ slices, CexWF x) (hc : ∀ c f, claim = some (c, f) → CexWF c) :
    ∀ cand f, (chainWalk π target defaults fuel slices claim).2 = some (cand, f) →
      CexWF cand := by
  fun_induction chainWalk π target defaults fuel slices claim <;> simp_all only [CexWF] <;> grind

/-! ## The configuration maps of `callElim` and `loopElim` -/

/-- Dropping variables keeps a store closed (`StoreClosed`: every value has no free
    variables). -/
private theorem dropVars_closed (fresh : List Expression.Ident) {σ : RStore Expression}
    (h : StoreClosed σ) : StoreClosed (RStore.dropVars fresh σ) := by
  grind [StoreClosed, RStore.dropVars]

/-- Dropping variables keeps an environment well-formed (`EnvWF`: a well-formed factory
    and a closed store). -/
theorem dropFreshEnv_wf (fresh : List Expression.Ident) {env : IEnv Expression}
    (h : EnvWF env) : EnvWF (dropFreshEnv fresh env) :=
  ⟨h.1, by simpa [dropFreshEnv, IStore.get_ofStore] using dropVars_closed fresh h.2⟩

/-- `uncallElimConfig` maps a well-formed configuration (`CfgWF`: every factory and store
    it holds is well-formed) to a well-formed one. -/
theorem uncallElimConfig_wf (origins : List CallElim.CallOrigin) :
    ∀ (c : IConfig Expression Command) {c' : IConfig Expression Command},
      uncallElimConfig origins c = some c' → CfgWF c → CfgWF c' := by
  intro c
  fun_induction uncallElimConfig origins c <;> intro c' h hw <;>
    grind [CfgWF, dropFreshEnv_wf, dropVars_closed, Option.map_eq_some_iff,
      IStore.get_ofStore]

/-- `unloopElimConfig` maps a well-formed configuration (`CfgWF`: every factory and store
    it holds is well-formed) to a well-formed one. -/
theorem unloopElimConfig_wf (origins : LoopOrigins) :
    ∀ (c : IConfig Expression Command) {c' : IConfig Expression Command},
      unloopElimConfig origins c = some c' → CfgWF c → CfgWF c' := by
  intro c
  fun_induction unloopElimConfig origins c <;> intro c' h hw <;>
    grind [CfgWF, Option.map_eq_some_iff]

/-- The `callElim` slicer from a well-formed start (`CexWF`) has well-formed slices and
    claim. -/
theorem callElimSlice_wf (π : String → Option Procedure) (target : AssertId Expression)
    (origins : List CallElim.CallOrigin) (start : CexA Expression Command) (hs : CexWF start) :
    (∀ x ∈ (callElimSlice π target origins start).slices, CexWF x) ∧
    (∀ c f, (callElimSlice π target origins start).claim = some (c, f) → CexWF c) :=
  sliceRun_wf _ _ _ _ (callElimCutHandler_wf _ _ _) _ _ hs

/-- The `loopElim` slicer from a well-formed start (`CexWF`) has well-formed slices and
    claim. -/
theorem loopElimSlice_wf (π : String → Option Procedure) (target : AssertId Expression)
    (start : CexA Expression Command) (hs : CexWF start) :
    (∀ x ∈ (loopElimSlice π target start).slices, CexWF x) ∧
    (∀ c f, (loopElimSlice π target start).claim = some (c, f) → CexWF c) :=
  sliceRun_wf _ _ _ _ (loopElimCutHandler_wf _ _) _ _ hs

/-! ## Embedding base configurations -/

/-- Embedding a base-command configuration into `Command` preserves and reflects
    well-formedness (`CfgWF`: every factory and store it holds is well-formed). -/
theorem cfgWF_embedConfig :
    ∀ c : IConfig Expression (Imperative.Cmd Expression),
      CfgWF (Calls.embedIConfig c) ↔ CfgWF c := by
  intro c
  induction c <;> simp_all [CfgWF, Calls.embedIConfig]

/-- Embedding an outcome embeds each element of its chain. -/
theorem embedOutcome_chain (o : BackLinkOutcome Expression (Imperative.Cmd Expression)) :
    (Calls.embedOutcome o).chain = o.chain.map Calls.embedCexA := by
  obtain ⟨_, outcome⟩ := o
  cases outcome <;> simp [Calls.embedOutcome, BackLinkOutcome.chain]

end -- public section

end Core
