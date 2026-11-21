/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkRelSimProps
public import Strata.Transform.NondetElim
public import Strata.Languages.Core.Counterexample.BackLinkExactProps
public import Strata.Util.DecidableEqProps
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterProps
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.InterpreterReplayProps
import all Strata.Languages.Core.Counterexample.BackLinkSim
import all Strata.Languages.Core.Counterexample.BackLinkSimProps
import all Strata.Languages.Core.Counterexample.BackLinkRelSim
import all Strata.Languages.Core.Counterexample.BackLinkRelSimProps
import all Strata.Languages.Core.ConfigWF
import Strata.Languages.Core.ConfigWFProps
import all Strata.Languages.Core.ReplayWF
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.Languages.Core.Counterexample.ValuationToRun
import all Strata.DL.Lambda.LExprEval
import Strata.DL.Imperative.Counterexample.Tactics
import Strata.Languages.Core.InterpreterSound
import Strata.Languages.Core.InterpreterDomainProps
import Strata.DL.Lambda.LExprEvalFuelProps

/-! # The `nondetElim` certificate

`nondetElim` rewrites a nondeterministic `ite * {t} {f}` into
`init $g := *; ite ($g) {t} {f}` for a fresh Boolean `$g` (a name with prefix
`$__ndelim_ite$`).  The upstream guard draws `choose bool` exactly where the downstream
`init $g := *` does, so the oracle is unchanged; the stores agree outside the fresh
names; the downstream run takes three extra, silent steps per rewritten `ite` (the
upstream run stutters).

* `NdS`/`NdL` — the statement relation: identical statements (mentioning no fresh name,
  no call or loop), except that a downstream `init $g := *; ite ($g)` pair
  stands for an upstream `ite *`;
* `NdFrame` — related scope frames: parent stores agreeing outside the fresh names, and
  defined-name lists with the same names outside the fresh names;
* `NdC` — the relation on interpreter configurations (`IConfig`), with related frames at
  related blocks and the four intermediate shapes between the downstream `init $g := *` and
  its `ite ($g)` step;
* `nd_step` — one downstream step stutters or is dominated by one upstream step;
* `nondetElimCert` — the certificate: a downstream slice start `.stmts ss env` maps to
  `.stmts us env` (fresh names dropped from the store) when the checker `ndListB`
  confirms `NdL ss us`, `us` being the phase's input unit when `ss` is its output unit
  and the syntactic inverse `undoNdL ss` otherwise; the oracle, target and fuel are
  unchanged.

Key definition: `nondetElimCert`, built on the per-step obligation `nd_relStepSim`. -/

namespace Core

open Imperative

public section

/-! ## Fresh names and the relations -/

/-- The names `nondetElim` introduces for nondeterministic `ite` guards. -/
@[expose] def ndFresh (x : Expression.Ident) : Prop := NondetElim.prefixIte.isPrefixOf x.name = true

instance : DecidablePred ndFresh := fun _ => inferInstanceAs (Decidable (_ = true))

/-- Related environments: the same factory, stores agreeing outside the fresh names. -/
@[expose] def NdEnv (env' env : IEnv Expression) : Prop :=
  env'.factory = env.factory ∧ StoreAgreeOutside ndFresh env'.store.get env.store.get

mutual
/-- Downstream statement related to an upstream one: identical, mentioning no fresh
    name, with related sub-lists. -/
inductive NdS : Statement → Statement → Prop where
  | cmd (c : Cmd Expression) : CmdAvoids ndFresh c → NdS (.cmd (.cmd c)) (.cmd (.cmd c))
  | block (l : String) (md' md : MetaData Expression) {b' b : List Statement} :
      NdL b' b → NdS (.block l b' md') (.block l b md)
  | ite (e : Expression.Expr) (md' md : MetaData Expression) {t' t f' f : List Statement} :
      ExprAvoids ndFresh e → NdL t' t → NdL f' f → NdS (.ite (.det e) t' f' md')
        (.ite (.det e) t f md)
  | exit (l : String) (md' md : MetaData Expression) : NdS (.exit l md') (.exit l md)
  | typeDecl (d' d : TypeConstructor) (md' md : MetaData Expression) :
      NdS (.typeDecl d' md') (.typeDecl d md)

/-- Downstream statement list related to an upstream one. -/
inductive NdL : List Statement → List Statement → Prop where
  | nil : NdL [] []
  | cons {s' s : Statement} {ds us : List Statement} : NdS s' s → NdL ds us → NdL (s' :: ds)
      (s :: us)
  | nd {g : Expression.Ident} {md0 md' md : MetaData Expression} {mv : ExpressionMetadata}
      {tv : Option Lambda.LMonoTy} {t' t f' f ds us : List Statement} :
      ndFresh g → NdL t' t → NdL f' f → NdL ds us →
      NdL (.cmd (.cmd (.init g HasBool.boolTy .nondet md0)) ::
            .ite (.det (.fvar mv g tv)) t' f' md' :: ds)
        (.ite .nondet t f md :: us)
end

/-- Related scope frames: parent stores agreeing outside the fresh names, and either both
    frames embedded (`defined = none`) or both opened by the monadic interpreter with name lists
    that contain the same names outside the fresh names. -/
private def NdFrame (fr' fr : ScopeFrame Expression) : Prop :=
  StoreAgreeOutside ndFresh fr'.parent.get fr.parent.get ∧
    ((fr'.defined = none ∧ fr.defined = none) ∨
      ∃ D' D, fr'.defined = some D' ∧ fr.defined = some D ∧
        ∀ x, ¬ ndFresh x → (x ∈ D' ↔ x ∈ D))

/-- The configuration relation, on interpreter configurations: related blocks carry related
    scope frames (`NdFrame`). -/
private inductive NdC : IConfig Expression Command → IConfig Expression Command → Prop where
  | stmt {s' s : Statement} {env' env : IEnv Expression} :
      NdS s' s → NdEnv env' env → NdC (.stmt s' env') (.stmt s env)
  | stmts {ds us : List Statement} {env' env : IEnv Expression} :
      NdL ds us → NdEnv env' env → NdC (.stmts ds env') (.stmts us env)
  | terminal {env' env : IEnv Expression} :
      NdEnv env' env → NdC (.terminal env') (.terminal env)
  | exiting {l : String} {env' env : IEnv Expression} :
      NdEnv env' env → NdC (.exiting l env') (.exiting l env)
  | seq {i' i : IConfig Expression Command} {ds us : List Statement} :
      NdC i' i → NdL ds us → NdC (.seq i' ds) (.seq i us)
  | block {l : Option String} {fr' fr : ScopeFrame Expression}
      {i' i : IConfig Expression Command} :
      NdFrame fr' fr → NdC i' i → NdC (.block l fr' i') (.block l fr i)
  /-- About to run the downstream `init $g := *`, upstream about to run `ite *`. -/
  | a1 {g : Expression.Ident} {md0 md' md : MetaData Expression} {mv : ExpressionMetadata}
      {tv : Option Lambda.LMonoTy} {t' t f' f ds us : List Statement}
      {env' env : IEnv Expression} :
      ndFresh g → NdL t' t → NdL f' f → NdL ds us → NdEnv env' env →
      NdC (.seq (.stmt (.cmd (.cmd (.init g HasBool.boolTy .nondet md0))) env')
            (.ite (.det (.fvar mv g tv)) t' f' md' :: ds))
        (.seq (.stmt (.ite .nondet t f md) env) us)
  /-- `$g` drawn downstream (the Boolean literal of `b`, with metadata `mb`); upstream already
      in the branch `b` chooses. -/
  | a2 {g : Expression.Ident} {mb : ExpressionMetadata} {b : Bool}
      {md' : MetaData Expression} {mv : ExpressionMetadata} {tv : Option Lambda.LMonoTy}
      {t' t f' f ds us : List Statement} {env' env : IEnv Expression} :
      ndFresh g → env'.store.get g = some (Lambda.LExpr.boolConst mb b) →
      NdL t' t → NdL f' f → NdL ds us → NdEnv env' env →
      NdC (.seq (.terminal env') (.ite (.det (.fvar mv g tv)) t' f' md' :: ds))
        (.seq (.block .none (.opened env.store)
          (.stmts (if b then t else f) env)) us)
  | a3 {g : Expression.Ident} {mb : ExpressionMetadata} {b : Bool}
      {md' : MetaData Expression} {mv : ExpressionMetadata} {tv : Option Lambda.LMonoTy}
      {t' t f' f ds us : List Statement} {env' env : IEnv Expression} :
      ndFresh g → env'.store.get g = some (Lambda.LExpr.boolConst mb b) →
      NdL t' t → NdL f' f → NdL ds us → NdEnv env' env →
      NdC (.stmts (.ite (.det (.fvar mv g tv)) t' f' md' :: ds) env')
        (.seq (.block .none (.opened env.store)
          (.stmts (if b then t else f) env)) us)
  | a4 {g : Expression.Ident} {mb : ExpressionMetadata} {b : Bool}
      {md' : MetaData Expression} {mv : ExpressionMetadata} {tv : Option Lambda.LMonoTy}
      {t' t f' f ds us : List Statement} {env' env : IEnv Expression} :
      ndFresh g → env'.store.get g = some (Lambda.LExpr.boolConst mb b) →
      NdL t' t → NdL f' f → NdL ds us → NdEnv env' env →
      NdC (.seq (.stmt (.ite (.det (.fvar mv g tv)) t' f' md') env') ds)
        (.seq (.block .none (.opened env.store)
          (.stmts (if b then t else f) env)) us)

/-! ## Small facts -/

/-- A variable bound to a Boolean literal evaluates to it, at the variable's metadata, at any
    positive fuel. -/
private theorem evalBounded_fvar {k : Nat} (hk : 1 ≤ k) {F : Lambda.Factory CoreLParams}
    {σ : RStore Expression} {mv : ExpressionMetadata} {g : Expression.Ident}
    {tv : Option Lambda.LMonoTy} {mb : ExpressionMetadata} {b : Bool}
    (hg : σ g = some (Lambda.LExpr.boolConst mb b)) :
    evalBounded k F σ (.fvar mv g tv) = some (Lambda.LExpr.boolConst mv b) := by
  have hc : Lambda.LExpr.isValue F (Lambda.LExpr.boolConst mv b) = true :=
    Lambda.isValue_const_true ..
  refine evalBounded_eq_some_iff.2 ⟨evalTypedDomain_fvar hg ?_, ?_, ?_⟩
  · exact isGroundTy_iff.2 rfl
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have hn (c : Bool) : F.callOfLFunc (.fvar mv g tv) c = none := by
      simp [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall, Lambda.getLFuncCall.go]
    simp only [Lambda.LExpr.eval, Lambda.LExpr.isValue, hn, Lambda.LExpr.evalCore, hg,
      Lambda.LExpr.replaceMetadata1]
    split <;> simp_all [Lambda.LExpr.boolConst]
  · exact ⟨typeCheckWith_const (hc := rfl) .., evalOpsChecked_fvar hg rfl⟩

/-! ## Related frames -/

/-- Frames opened by the monadic interpreter at stores agreeing outside the fresh names are
    related. -/
private theorem NdFrame.opened {σ' σ : IStore Expression}
    (h : StoreAgreeOutside ndFresh σ'.get σ.get) : NdFrame (.opened σ') (.opened σ) :=
  ⟨h, .inr ⟨[], [], rfl, rfl, fun _ _ => .rfl⟩⟩

/-- The frames after steps whose level commands define the same names outside the fresh names
    (`ScopeFrame.record`) are related when the frames before are. -/
private theorem NdFrame.record {fr' fr : ScopeFrame Expression} (hf : NdFrame fr' fr)
    {c'? c? : Option Command}
    (hc : ∀ x, ¬ ndFresh x → (x ∈ c'?.elim [] (CmdDefs.defs (P := Expression)) ↔
      x ∈ c?.elim [] (CmdDefs.defs (P := Expression)))) :
    NdFrame (fr'.record c'?) (fr.record c?) := by
  obtain ⟨hp, ⟨h1, h2⟩ | ⟨D', D, h1, h2, hD⟩⟩ := hf
  all_goals refine ⟨by simpa only [ScopeFrame.record_parent] using hp, ?_⟩
  all_goals cases c'? <;> cases c? <;> simp only [ScopeFrame.record, h1, h2]
  all_goals first
    | (simp; done)
    | refine .inr ⟨_, _, rfl, rfl, fun x hx => ?_⟩
      have hcx := hc x hx
      simp only [Option.elim, List.mem_append, List.mem_filter, hD x hx, hp x hx] at hcx ⊢ <;>
        grind

/-! ## Unfolding a step inside a frame -/

/-- Lifting a step through frames: `c'` (downstream) and `c` (upstream) are framed
    configurations around `i'` and `i`, `w'` and `w` wrap the results of their inner steps, and
    `R` is preserved by wrapping.  If the inner downstream step stutters against `i`
    (`Stutters`: it succeeds or fails without moving the state, the result staying
    `R`-related to `i`) under a side
    condition `Q` that makes wrapped results `R`-related to `c` and gives `Q'`, or is dominated
    by the inner upstream step (`RelDom`: every downstream outcome is matched by an upstream
    one with `R`-related results), the same holds for `c'` and `c`. -/
private theorem cel_frameStepS {K : RelCtx}
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    {sc' sc : StepCmdM Expression Command (ReplayM Expression)} {k m : Nat}
    {i' i c' c : IConfig Expression Command} {Q Q' : Prop}
    {w' w : IConfig Expression Command → IConfig Expression Command}
    (e' : stepInterp sc' k c' = stepInterp sc' k i' >>= fun x => pure (w' x))
    (e : ¬ i.Done → stepInterp sc m c = stepInterp sc m i >>= fun x => pure (w x))
    (hd : ¬ c.Done) (hR : ∀ a' a, R a' a → R (w' a') (w a))
    (hQ : Q → Q' ∧ ∀ a', R a' i → R (w' a') c)
    (h : (Stutters K R (stepInterp sc' k i') i ∧ Q) ∨
      (¬ i.Done ∧ RelDom K (stepInterp sc' k i') (stepInterp sc m i) R)) :
    (Stutters K R (stepInterp sc' k c') c ∧ Q') ∨
      (¬ c.Done ∧ RelDom K (stepInterp sc' k c') (stepInterp sc m c) R) := by
  rw [e']
  rcases h with ⟨hstut, hq⟩ | ⟨hdone, hdom⟩
  · obtain ⟨hq', hRc⟩ := hQ hq
    exact .inl ⟨fun st => (hstut st).imp (fun ⟨_, hrun, hr⟩ => ⟨_, by rw [rrun_bind, hrun]; rfl,
      hRc _ hr⟩) fun ⟨_, hrun⟩ => ⟨_, by rw [rrun_bind, hrun]⟩, hq'⟩
  · exact .inr ⟨hd, e hdone ▸ .bind hdom (fun _ _ hr => .pure (hR _ _ hr)) fun _ => Grows.pure _ _⟩

/-- `NdC` read through the expansion of sequence towers (`IConfig.unseqs`): the relation the
    monadic interpreter's steps preserve. -/
private abbrev NdU (c' c : IConfig Expression Command) : Prop := NdC c'.unseqs c.unseqs

/-- Related configurations contain no sequence tower, so they stay related after the expansion. -/
private theorem NdC.toU {c' c : IConfig Expression Command} (h : NdC c' c) : NdU c' c := by
  induction h with
  | seq _ hL ih => exact .seq ih hL
  | block hfr _ ih => exact .block hfr ih
  | stmt h1 h2 => exact .stmt h1 h2
  | stmts h1 h2 => exact .stmts h1 h2
  | terminal h => exact .terminal h
  | exiting h => exact .exiting h
  | a1 h1 h2 h3 h4 h5 => exact .a1 h1 h2 h3 h4 h5
  | a2 h1 h2 h3 h4 h5 h6 => exact .a2 h1 h2 h3 h4 h5 h6
  | a3 h1 h2 h3 h4 h5 h6 => exact .a3 h1 h2 h3 h4 h5 h6
  | a4 h1 h2 h3 h4 h5 h6 => exact .a4 h1 h2 h3 h4 h5 h6

/-! ## The per-step obligation -/

/-- One downstream step from well-formed interpreter configurations (`CfgWF` of their
    abstractions) related by `NdC`, whose abstraction is not done, at fuel `1 ≤ k ≤ m`, either
    stutters against the upstream configuration (`Stutters`, related by `NdC` after the expansion
    of sequence towers) and runs no level command (`IConfig.levelCmd? = none`), so that an
    enclosing frame records nothing, or is dominated by one upstream step at fuel `m` (`RelDom`).
    Assumed: the oracle cursors agree (`K.freeOracle = false`) and events agree outside the fresh
    names (`AgreeCtx K ndFresh`). -/
private theorem nd_step_gen {K : RelCtx} (hK : K.Compat) (hO : K.freeOracle = false)
    (hER : AgreeCtx K ndFresh) (π' π : String → Option Procedure) (d : Nat) :
    ∀ {c' c : IConfig Expression Command}, NdC c' c → CfgWF c' → CfgWF c →
      ¬ c'.Done → ∀ k m, 1 ≤ k → k ≤ m →
      (Stutters K NdU (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c') c ∧
        c'.levelCmd? = none) ∨
      (¬ c.Done ∧ RelDom K (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c')
        (stepInterp (replayStepCmd (m := ReplayM Expression) π d) m c) NdU) := by
  intro _ c hrel
  induction hrel <;> intro hw' hw hnd k m hk hkm
  case stmt hS hE =>
    refine .inr ⟨nofun, ?_⟩
    simp only [CfgWF] at hw' hw
    cases hS <;> simp only [stepInterp, replayStepCmd_cmd, resolveGuard, hE.1]
    all_goals first
      | exact .bind (stepBaseCmdStore_rel hK hO hER hkm hw.1 hw.2 hE.2 _ ‹_›)
          (fun _ _ h => .pure (.terminal ⟨rfl, h⟩)) fun _ => Grows.pure _ _
      | cel_cmdArm ((evalBounded_agree hw.1 hw.2 hE.2 ‹_› k).symm.trans ‹_›)
          (grind [NdC, NdEnv, NdFrame.opened, IConfig.unseqs])
  case stmts hL hE =>
    refine .inr ⟨nofun, ?_⟩
    rcases hL with _ | ⟨hS, hL'⟩ | ⟨hg, ht, hf, hds⟩
    · exact .pure (.terminal hE)
    · have hL0 := hL'
      cases hL' <;> exact .pure (.seq (.stmt hS hE) hL0)
    · have hds0 := hds
      cases hds <;> exact .pure (.a1 hg ht hf hds0 hE)
  case seq i' i ds us hi hL ih =>
    by_cases hd : i'.Done
    · cases hi <;> simp only [IConfig.Done] at hd
      all_goals exact .inr ⟨nofun, .pure (by simp only [NdU, IConfig.unseqs]; grind [NdC])⟩
    exact cel_frameStepS (stepInterp_seq_notDone _ _ hd ds) (stepInterp_seq_notDone _ _ · us)
      (by nofun) (fun _ _ h => .seq h hL) (fun hq => ⟨hq, fun _ h => .seq h hL⟩)
      (ih hw' hw hd k m hk hkm)
  case block l fr' fr i' i hfr hi ih =>
    by_cases hd : i'.Done
    · have hex {σ' σ : IStore Expression} (h : StoreAgreeOutside ndFresh σ'.get σ.get) :
          StoreAgreeOutside ndFresh (fr'.exit σ').get (fr.exit σ).get := by
        obtain ⟨hp, ⟨h1, h2⟩ | ⟨D', D, h1, h2, hD⟩⟩ := hfr
        · simpa [ScopeFrame.exit, h1, h2] using hp.project h
        · intro x hx
          simp [ScopeFrame.exit, h1, h2, RStore.dropVars, hD x hx, h x hx]
      cases hi <;> simp only [IConfig.Done] at hd
      all_goals exact .inr ⟨nofun, by
        simp only [stepInterp]
        (try split) <;> exact .pure (by simp only [NdU, IConfig.unseqs]; grind [NdC, NdEnv])⟩
    obtain ⟨-, hwi'⟩ := hw'
    obtain ⟨-, hwi⟩ := hw
    have hrec {a' a} (h : NdC a' a) :
        NdFrame (fr'.record a'.levelCmd?) (fr.record a.levelCmd?) := by
      induction h with
      | seq _ _ ih => exact ih
      | stmt hS _ => cases hS <;> exact hfr.record (by simp [IConfig.levelCmd?])
      | a1 hg =>
        refine hfr.record fun x hx => ?_
        simp only [IConfig.levelCmd?, Option.elim, CmdDefs.defs, Cmd.definedVars]
        exact ⟨fun h => absurd (List.mem_singleton.1 h ▸ hg) hx, nofun⟩
      | _ => exact hfr.record (by simp [IConfig.levelCmd?])
    exact cel_frameStepS (stepInterp_block_notDone _ _ hd l fr')
      (stepInterp_block_notDone _ _ · l fr) (by nofun) (fun _ _ h => .block (hrec hi) h)
      (fun hq => ⟨rfl, fun _ h => .block (by rw [hq]; rcases fr' with ⟨_, _ | _⟩ <;> exact hfr) h⟩)
      (ih hwi' hwi hd k m hk hkm)
  case a2 _ _ _ _ _ _ _ _ _ _ ds us env' env hfresh hg ht hf hds hE =>
    exact .inl ⟨fun _ => .inl ⟨_, rrun_pure _ _ _, .a3 hfresh hg ht hf hds hE⟩, rfl⟩
  case a3 _ _ _ _ _ _ _ _ _ _ ds us env' env hfresh hg ht hf hds hE =>
    have hds0 := hds
    cases hds <;>
      exact .inl ⟨fun _ => .inl ⟨_, rrun_pure _ _ _, .a4 hfresh hg ht hf hds0 hE⟩, rfl⟩
  case a4 _ _ b _ _ _ _ _ _ _ ds us env' env hfresh hg ht hf hds hE =>
    refine .inl ⟨fun _ => ?_, rfl⟩
    simp only [stepInterp, resolveGuard, InterpLang.boundedEval, evalBounded_fvar hk hg,
      boolLit?_boolConst, hE.1]
    have hB {a b} (hL : NdL a b) :=
      NdC.seq (.block (l := none) (NdFrame.opened hE.2) (.stmts hL hE)) hds
    cases b <;> simp_all [rrun_pure, -bind_pure_comp, NdU, IConfig.unseqs]
  case a1 g _ md' _ mv tv _ _ _ _ _ _ env' env hfresh ht hf hds hE =>
    refine .inr ⟨nofun, ?_⟩
    simp only [stepInterp, replayStepCmd_cmd, stepBaseCmdStore, resolveGuard, hE.1]
    split
    · exact RelDom.throw_bind_left hK _ _ (by grows_tac)
    simp only [pure_bind, bind_assoc]
    refine .bind (.choose hK hO _ _ _ _) (fun v _ h => ?_) fun _ => by grows_tac
    obtain ⟨rfl, hv⟩ := h
    simp only [CfgWF] at hw'
    obtain ⟨⟨-, hCB⟩, -⟩ := hw'
    rw [hE.1] at hCB
    obtain ⟨mb, b, rfl⟩ : ∃ mb b, v = Lambda.LExpr.boolConst mb b := by
      rcases replayValueOps_bool hCB hv with h | h <;> simp only [InterpLang.boolLit?] at h <;>
        split at h <;> (try split at h) <;> cases h <;>
        exact (eq_boolConst_of_eqModuloMeta ‹_›).elim fun m h => ⟨m, _, h⟩
    have ha := NdC.a2 (mb := mb) (b := b) (md' := md') (mv := mv) (tv := tv)
      (env' := ⟨env'.store.update g (Lambda.LExpr.boolConst mb b), env.factory⟩) (env := env)
      hfresh (by simp [IStore.get_update, RStore.update]) ht hf hds
      ⟨rfl, by simpa using hE.2.update_fresh hfresh _⟩
    cases b <;> simpa using RelDom.pure ha.toU
  all_goals cases hnd ⟨⟩

/-- One downstream step from well-formed interpreter configurations (`CfgWF` of their
    abstractions) related by `NdC` (identical up to the fresh guard names in the stores and
    frames and the intermediate shapes of a rewritten `ite *`), whose abstraction is not done,
    at fuel `1 ≤ k ≤ m`, either stutters against the upstream configuration (`Stutters`: it
    moves no state and stays related by `NdC` after the expansion of sequence towers) or is
    dominated by one upstream step at fuel `m` (`RelDom`: every downstream outcome is matched by
    an upstream one whose result is related by `NdC` after the expansion).  Assumed: the oracle
    cursors agree (`K.freeOracle = false`) and events agree outside the fresh names
    (`AgreeCtx K ndFresh`). -/
private theorem nd_step {K : RelCtx} (hK : K.Compat) (hO : K.freeOracle = false)
    (hER : AgreeCtx K ndFresh)
    (π' π : String → Option Procedure) (d : Nat) :
    ∀ {c' c : IConfig Expression Command}, NdC c' c → CfgWF c' → CfgWF c →
      ¬ c'.Done → ∀ k m, 1 ≤ k → k ≤ m →
      Stutters K NdU (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c') c ∨
      (¬ c.Done ∧ RelDom K (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c')
        (stepInterp (replayStepCmd (m := ReplayM Expression) π d) m c) NdU) :=
  fun hrel hw' hw hnd k m hk hkm =>
    (nd_step_gen hK hO hER π' π d hrel hw' hw hnd k m hk hkm).imp_left And.left

/-! ## Relating whole steps, with well-formedness -/

/-- The simulation relation of `nondetElim` before the expansion of sequence towers: related
    interpreter configurations, both with well-formed abstractions. -/
private def NdR (c' c : IConfig Expression Command) : Prop :=
  NdC c' c ∧ CfgWF c' ∧ CfgWF c

/-- **The per-step obligation of `nondetElim`.**  For any procedure tables `π'`, `π`, the
    relation `NdR` read through the expansion of sequence towers (`IConfig.unseqs`) satisfies
    `RelStepSim`: from related configurations, a downstream step at fuel `k ≥ 1` either
    stutters or is matched in lockstep by one upstream step at any fuel `m ≥ k`.  The
    tables do not matter because related configurations contain no call.  Assumed: the
    oracle cursors agree and events agree outside the fresh guard names. -/
private theorem nd_relStepSim {K : RelCtx} (hK : K.Compat) (hO : K.freeOracle = false)
    (hER : AgreeCtx K ndFresh)
    (π' π : String → Option Procedure) (d : Nat) :
    RelStepSim K (replayStepCmd (m := ReplayM Expression) π' d)
      (replayStepCmd (m := ReplayM Expression) π d) fun c' c => NdR c'.unseqs c.unseqs := by
  refine relStepSim_unseqs fun c' c ⟨hrel, hwf', hwf⟩ hnd k m hk hkm => ?_
  have hpost := stepInterp_cfgWF (replayStepCmd_stepWF π' d) c' k hwf'
  have hpost' : OkPost (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c')
      (fun a => CfgWF a.unseqs) := fun cfg s a s1 h => (cfgWF_unseqs a).2 (hpost cfg s a s1 h)
  have hpostU : OkPost (stepInterp (replayStepCmd (m := ReplayM Expression) π d) m c)
      (fun a => CfgWF a.unseqs) := fun cfg s a s1 h =>
    (cfgWF_unseqs a).2 (stepInterp_cfgWF (replayStepCmd_stepWF π d) c m hwf cfg s a s1 h)
  have hc : CfgWF c.unseqs := (cfgWF_unseqs c).2 hwf
  exact (nd_step hK hO hER π' π d hrel hwf' hwf hnd k m hk hkm).imp
    (fun hs => Stutters.toRel hK fun st => (hs st).imp
      (fun ⟨c1, hrun, hR⟩ => ⟨c1, hrun, hR, hpost' _ _ _ _ hrun, hc⟩) id)
    fun ⟨hdone, hdom⟩ => ⟨hdone, hdom.withPost hpost' hpostU⟩

/-! ## The executable checker -/

/-- An expression mentions no fresh name (executable). -/
@[expose] def exprAvoidsB (e : Expression.Expr) : Bool :=
  (Lambda.LExpr.LExpr.getVars e).all fun x => !decide (ndFresh x)

/-- An expression `exprAvoidsB` accepts mentions no fresh guard name
    (`ExprAvoids ndFresh`). -/
private theorem exprAvoidsB_spec {e : Expression.Expr} (h : exprAvoidsB e = true) :
    ExprAvoids ndFresh e := fun _ hx => by grind [exprAvoidsB]

/-- A base command mentions no fresh name (executable). -/
@[expose] def cmdAvoidsB : Cmd Expression → Bool
  | .init x _ (.det e) _ => !decide (ndFresh x) && exprAvoidsB e
  | .init x _ .nondet _ => !decide (ndFresh x)
  | .set x (.det e) _ => !decide (ndFresh x) && exprAvoidsB e
  | .set x .nondet _ => !decide (ndFresh x)
  | .assert _ e _ => exprAvoidsB e
  | .assume _ e _ => exprAvoidsB e
  | .cover _ e _ => exprAvoidsB e

/-- A base command `cmdAvoidsB` accepts mentions no fresh guard name, in the names it
    writes or the expressions it reads (`CmdAvoids ndFresh`). -/
private theorem cmdAvoidsB_spec {c : Cmd Expression} (h : cmdAvoidsB c = true) :
    CmdAvoids ndFresh c := by
  unfold cmdAvoidsB at h; split at h <;> simp_all [CmdAvoids, exprAvoidsB_spec]

mutual
/-- Executable check of `NdS`. -/
@[expose] def ndStmtB : Statement → Statement → Bool
  | .cmd (.cmd c'), .cmd (.cmd c) => decide (c' = c) && cmdAvoidsB c
  | .block l' b' _, .block l b _ => decide (l' = l) && ndListB b' b
  | .ite (.det e') t' f' _, .ite (.det e) t f _ =>
    decide (e' = e) && exprAvoidsB e && ndListB t' t && ndListB f' f
  | .exit l' _, .exit l _ => decide (l' = l)
  | .typeDecl _ _, .typeDecl _ _ => true
  | _, _ => false
  termination_by s' => sizeOf s'

/-- Executable check of the `NdL.nd` pattern at the head of the lists. -/
@[expose] def ndPairB : Statement → List Statement → Statement → List Statement → Bool
  | .cmd (.cmd (.init g ty .nondet _)), .ite (.det (.fvar _ g' _)) t' f' _ :: ds,
    .ite .nondet t f _, us =>
    decide (g' = g) && decide (ty = HasBool.boolTy) && decide (ndFresh g) &&
      ndListB t' t && ndListB f' f && ndListB ds us
  | _, _, _, _ => false
  termination_by s' ds' => sizeOf s' + sizeOf ds'

/-- Executable check of `NdL`. -/
@[expose] def ndListB : List Statement → List Statement → Bool
  | [], [] => true
  | s' :: ds, s :: us => (ndStmtB s' s && ndListB ds us) || ndPairB s' ds s us
  | _, _ => false
  termination_by ds' => sizeOf ds'
end

/-- The executable checkers are sound: statements `ndStmtB` accepts are related by `NdS`,
    lists `ndListB` accepts are related by `NdL`, and a head pair `ndPairB` accepts (a
    downstream `init $g := *; ite ($g)` standing for an upstream `ite *`) makes the whole
    lists related by `NdL`. -/
private theorem nd_checker_spec :
    (∀ s' s, ndStmtB s' s = true → NdS s' s) ∧
    (∀ ds us, ndListB ds us = true → NdL ds us) ∧
    (∀ s' ds s us, ndPairB s' ds s us = true → NdL (s' :: ds) (s :: us)) := by
  apply ndStmtB.mutual_induct <;> grind [ndStmtB, ndListB, ndPairB, NdS, NdL, cmdAvoidsB_spec,
    exprAvoidsB_spec]

/-! ## The syntactic inverse and the certificate -/

mutual
/-- Best-effort syntactic inverse of `nondetElim` on a statement (validated afterwards by
    `ndListB`, so it needs no correctness proof). -/
@[expose] def undoNdS : Statement → Statement
  | .block l b md => .block l (undoNdL b) md
  | .ite (.det e) t f md => .ite (.det e) (undoNdL t) (undoNdL f) md
  | s => s
  termination_by s => sizeOf s

/-- Best-effort syntactic inverse of `nondetElim` on a statement list: a nondeterministic
    `init` of a fresh guard name (`ndFresh`) followed by an `if` on that name is read back as
    `if *`. -/
@[expose] def undoNdL : List Statement → List Statement
  | [] => []
  | s@(.cmd (.cmd (.init g _ .nondet _))) :: s'@(.ite (.det (.fvar _ g' _)) t f md) :: ds =>
    if decide (ndFresh g) && decide (g' = g) then
      .ite .nondet (undoNdL t) (undoNdL f) md :: undoNdL ds
    else undoNdS s :: undoNdL (s' :: ds)
  | s :: ds => undoNdS s :: undoNdL ds
  termination_by ss => sizeOf ss
end

/-- The phase's per-unit forward map. -/
@[expose] def nondetElimUnit (st : List Statement) : Option (List Statement) :=
  some (Block.nondetElim st)

/-- The fresh names removed from an environment's store. -/
@[expose] def ndDropEnv (env : IEnv Expression) : IEnv Expression :=
  { env with store := .ofStore fun x => if ndFresh x then none else env.store.get x }

/-- An environment is related by `NdEnv` (same factory, stores agreeing outside the fresh
    guard names) to itself with the fresh names removed from its store (`ndDropEnv`). -/
private theorem ndDropEnv_rel (env : IEnv Expression) :
    NdEnv env (ndDropEnv env) :=
  ⟨rfl, fun _ hx => by simp [ndDropEnv, IStore.get_ofStore, hx]⟩

/-- Removing the fresh guard names from the store (`ndDropEnv`) keeps an environment
    well-formed (`EnvWF`: a well-formed factory and a store of closed values). -/
private theorem ndDropEnv_wf {env : IEnv Expression} (h : EnvWF env) :
    EnvWF (ndDropEnv env) := by
  grind [ndDropEnv, StoreClosed, EnvWF, IStore.get_ofStore]

/-- The upstream statement list a downstream one stands for, at the upstream unit `st`:
    `st` itself for the phase's output unit, the syntactic inverse otherwise. -/
@[expose] def ndUpList (st ss : List Statement) : List Statement :=
  if ss = Block.nondetElim st then st else undoNdL ss

/-- The certificate's configuration map: a `.stmts` slice start whose statement list is
    confirmed related (`ndListB`), and which is top-level upstream only if it is
    top-level downstream. -/
@[expose] def ndBackCfg (st : List Statement) : IConfig Expression Command →
    Option (IConfig Expression Command)
  | .stmts ss env =>
    if ndListB ss (ndUpList st ss) &&
        (decide (ss = Block.nondetElim st) || !decide (ndUpList st ss = st)) then
      some (.stmts (ndUpList st ss) (ndDropEnv env))
    else none
  | _ => none

/-- When the certificate's configuration map `ndBackCfg st` maps `c'` to `c`, `c'` is a
    start `.stmts ss env`, `c` is `.stmts (ndUpList st ss)` with the fresh guard names
    removed from the store, the two lists are related by `NdL`, and either `ss` is the
    phase's output unit or its upstream list is not the input unit `st`. -/
private theorem ndBackCfg_eq_some {st : List Statement} {c' c : IConfig Expression Command}
    (h : ndBackCfg st c' = some c) :
    ∃ ss env, c' = .stmts ss env ∧ c = .stmts (ndUpList st ss) (ndDropEnv env) ∧
      NdL ss (ndUpList st ss) ∧ (ss = Block.nondetElim st ∨ ndUpList st ss ≠ st) := by
  cases c' <;> grind [ndBackCfg, nd_checker_spec.2.1]

/-- **The `nondetElim` certificate** (between tables `π'` downstream and `π` upstream;
    related configurations contain no call, so the tables are not consulted). -/
@[expose] def nondetElimCert (π' π : String → Option Procedure) :
    ExactCert nondetElimUnit (genuineFeasible π') (genuineFeasible π) where
  backCfg := fun st _ c => ndBackCfg st c
  backOracle := fun _ _ o => o
  backTarget := id
  backFuel := fun _ => id
  top_back := by
    intro st st' hT c' c htop hc oracle
    simp only [nondetElimUnit, Option.some.injEq] at hT
    subst hT
    obtain ⟨ss, env, hc', rfl, _, _⟩ := ndBackCfg_eq_some hc
    simp only [isTopLevelAt, hc'] at htop
    subst htop
    simp [isTopLevelAt, ndUpList]
  nontop_back := by
    intro st st' hT c' c hnt hc oracle
    simp only [nondetElimUnit, Option.some.injEq] at hT
    subst hT
    obtain ⟨ss, env, hc', rfl, _, hor⟩ := ndBackCfg_eq_some hc
    simp only [isTopLevelAt, hc'] at hnt
    simp only [isTopLevelAt]
    rcases hor with h | h
    · exact absurd h hnt
    · exact h
  wf_back := by
    intro st st' _ _ c' c hw hc
    obtain ⟨ss, env, rfl, rfl, _, _⟩ := ndBackCfg_eq_some hc
    exact ndDropEnv_wf hw
  claim_back := by
    intro st st' _ t f _ c' c hw hg hc
    obtain ⟨ss, env, hc', rfl, hL, _⟩ := ndBackCfg_eq_some hc
    have hwc : CfgWF (IConfig.stmts (ndUpList st ss) (ndDropEnv env)) := by
      have hw' : EnvWF env := by simpa [CexWF, hc'] using hw
      exact ndDropEnv_wf hw'
    have hR : NdR c'.cfg.unseqs (IConfig.stmts (ndUpList st ss) (ndDropEnv env)).unseqs := by
      rw [hc']
      exact ⟨NdC.stmts hL (ndDropEnv_rel env),
        by simpa [CexWF, hc', IConfig.unseqs, CfgWF] using hw, hwc⟩
    have hK := relProdCtx_compat (evAgree_transfer ndFresh t (Nat.le_refl f)) (fun _ => False)
      (fun _ h => absurd h id)
    exact claim_back_of_relSimulation (Nat.le_refl f) (evAgree_transfer ndFresh t (Nat.le_refl f))
      (fun _ h => absurd h id) (nd_relStepSim hK rfl (fun _ _ h => h) π' π _) c' _ hR hg

end -- public section

end Core
