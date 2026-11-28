/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkRelSimProps
public import Strata.Transform.InsertLoopInvariantAsserts
public import Strata.Languages.Core.Counterexample.BackLinkExactProps
public import Strata.Util.DecidableEqProps
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterConfig
import Strata.DL.Imperative.InterpreterConfigProps
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterProps
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.CmdSemantics
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
import all Strata.Languages.Core.Counterexample.BackLinkPhases
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Certificates for phases that only insert asserts and assumes

`precondElim` (on existing procedures) and `insertLoopInvariantAsserts` add
`assert`/`assume` commands with labels the phase reserves, and otherwise keep a unit's
statements (up to loop invariants, which a replay step ignores).  The downstream run
executes the inserted commands, which emit events the upstream run does not
(`RelCtx.Extra`); every other step is the same on both sides.

* `InsS`/`InsL`/`InsC` — the relations, parameterized by the reserved-label test `ext`
  (`InsC` relates interpreter configurations, `IConfig`, with equal scope frames);
* `ins_step` — the per-step obligation (`RelStepSim`), with no well-formedness needed
  (the two environments are equal);
* `insCert ext` — the certificate (start map `insBackCfg`), for targets whose label is not
  reserved (`V' := insValid`): an inserted assert is not an upstream obligation.

**Measured loops.**  For a loop with a measure `insertLoopInvariantAsserts` also inserts a
snapshot `init m_old := D` under a reserved name (the relation also admits `init m_old := *`,
which draws).  A start containing a snapshot is related through `MeasC` and accepted only
when nothing else in it draws, so the claim transports for any upstream oracle.  An
iteration start of a measured loop maps to the related upstream one, its first oracle value
dropped for a nondeterministic snapshot (`insBackOracle`).

Key definition: `insCert`, built on the per-step obligations `ins_step` and `m_relStepSim`
(with measure snapshots). -/

namespace Core

open Imperative

public section

variable {d : Nat}

/-- An inserted command: an `assert` or `assume` whose label is reserved. -/
@[expose] def isExtraCmd (ext : String → Bool) : Cmd Expression → Bool
  | .assert l _ _ => ext l
  | .assume l _ _ => ext l
  | _ => false

/-- An event an inserted command emits. -/
@[expose] def InsExtra (ext : String → Bool) : IEvent Expression → Prop
  | .assert a => ext a.label = true
  | .assume a => ext a.label = true
  | .cover _ => False

/-- For a target whose label is not reserved, no event an inserted command emits
    (`InsExtra`) fires the target predicate `assertFailureHalt`. -/
private theorem insExtra_halt (ext : String → Bool) {t : AssertId Expression}
    (ht : ext t.label = false) (f : Nat) :
    ∀ ev, InsExtra ext ev → assertFailureHalt t f ev = false := by
  simp only [InsExtra, assertFailureHalt, Calls.assertFailureHalt]
  grind

mutual
/-- Downstream statement related to an upstream one: the same statement, with related
    sub-lists (a loop's invariants and measure may differ; a replay step ignores them). -/
inductive InsS (ext : String → Bool) : Statement → Statement → Prop where
  | cmd (c : Cmd Expression) : InsS ext (.cmd (.cmd c)) (.cmd (.cmd c))
  | block (l : String) (md' md : MetaData Expression) {b' b : List Statement} :
      InsL ext b' b → InsS ext (.block l b' md') (.block l b md)
  | ite (g : ExprOrNondet Expression) (md' md : MetaData Expression) {t' t f' f : List Statement} :
      InsL ext t' t → InsL ext f' f → InsS ext (.ite g t' f' md') (.ite g t f md)
  | loop (g : ExprOrNondet Expression) (m' m : Option Expression.Expr)
      (inv' inv : List (String × Expression.Expr)) (md' md : MetaData Expression)
      {b' b : List Statement} :
      InsL ext b' b → InsS ext (.loop g m' inv' b' md') (.loop g m inv b md)
  | exit (l : String) (md' md : MetaData Expression) : InsS ext (.exit l md') (.exit l md)
  | typeDecl (d' d : TypeConstructor) (md' md : MetaData Expression) :
      InsS ext (.typeDecl d' md') (.typeDecl d md)

/-- Downstream statement list related to an upstream one: related statements, with
    inserted commands only downstream. -/
inductive InsL (ext : String → Bool) : List Statement → List Statement → Prop where
  | nil : InsL ext [] []
  | cons {s' s : Statement} {ds us : List Statement} :
      InsS ext s' s → InsL ext ds us → InsL ext (s' :: ds) (s :: us)
  | extra {c : Cmd Expression} {ds us : List Statement} :
      isExtraCmd ext c = true → InsL ext ds us → InsL ext (.cmd (.cmd c) :: ds) us
end

/-- The interpreter configuration relation: equal environments and equal scope frames; the
    downstream run may be inside an inserted command while the upstream one waits at the list
    after it. -/
private inductive InsC (ext : String → Bool) :
    IConfig Expression Command → IConfig Expression Command → Prop where
  | stmt {s' s : Statement} {env : IEnv Expression} :
      InsS ext s' s → InsC ext (.stmt s' env) (.stmt s env)
  | stmts {ds us : List Statement} {env : IEnv Expression} :
      InsL ext ds us → InsC ext (.stmts ds env) (.stmts us env)
  | terminal {env : IEnv Expression} : InsC ext (.terminal env) (.terminal env)
  | exiting {l : String} {env : IEnv Expression} :
      InsC ext (.exiting l env) (.exiting l env)
  | seq {i' i : IConfig Expression Command} {ds us : List Statement} :
      InsC ext i' i → InsL ext ds us → InsC ext (.seq i' ds) (.seq i us)
  | block {l : Option String} {fr : ScopeFrame Expression}
      {i' i : IConfig Expression Command} :
      InsC ext i' i → InsC ext (.block l fr i') (.block l fr i)
  /-- The downstream run is about to execute an inserted command. -/
  | xrun {c : Cmd Expression} {ds us : List Statement} {env : IEnv Expression} :
      isExtraCmd ext c = true → InsL ext ds us →
      InsC ext (.seq (.stmt (.cmd (.cmd c)) env) ds) (.stmts us env)
  /-- The downstream run has executed an inserted command. -/
  | xdone {ds us : List Statement} {env : IEnv Expression} :
      InsL ext ds us → InsC ext (.seq (.terminal env) ds) (.stmts us env)

/-- `InsC` read through the expansion of sequence towers (`IConfig.unseqs`): the relation the
    monadic interpreter's steps preserve. -/
private abbrev InsU (ext : String → Bool) (c' c : IConfig Expression Command) : Prop :=
  InsC ext c'.unseqs c.unseqs

/-! ## Relational steps on equal environments -/

/-- `emit ev >>= g` records `ev`, then stops if `ev` interrupts, else runs `g`. -/
private theorem rrun_emit_bind {α : Type} (cfg : ReplayCfg Expression) (ev : IEvent Expression)
    (g : PUnit → ReplayM Expression α) (s : ReplayState Expression) :
    rrun (InterpEffects.emit (P := Expression) (m := ReplayM Expression) ev >>= g) cfg s
      = (match cfg.interruptOn ev with
         | none => rrun (g ⟨⟩) cfg { s with traceRev := ev :: s.traceRev }
         | some r => (.error r, { s with traceRev := ev :: s.traceRev })) := by
  cel_rr [rrun_bind]
  cases cfg.interruptOn ev <;> cel_rr

/-- A base command run on the same factory and store downstream at fuel `k` is dominated
    (`RelDom`: every downstream outcome is matched by an upstream one with equal results)
    by the same command upstream at fuel `m ≥ k`, when every event is related to itself
    and the oracle cursors agree. -/
private theorem stepBaseCmdStore_relEq {K : RelCtx} (hK : K.Compat) (hO : K.freeOracle = false)
    (hER : ∀ ev, K.ER ev ev)
    {k m : Nat} (hkm : k ≤ m) (F : Lambda.Factory CoreLParams) (σ : IStore Expression)
    (c : Cmd Expression) :
    RelDom K (stepBaseCmdStore (m := ReplayM Expression) k F σ c)
      (stepBaseCmdStore (m := ReplayM Expression) m F σ c) Eq := by
  cases c <;> simp only [stepBaseCmdStore]
  case init | set => with_reducible cel_relLoop (by with_unfolding_all exact ‹_›) rfl
  all_goals exact .bind (.forM_emit hK (.imp (fun _ _ h => h ▸ hER _)
    (.refl (fun _ => rfl) _))) (fun _ _ _ => .pure rfl) fun _ => by grows_tac

/-- If `X'` stutters relationally against `c` (`StuttersRel`: from related states, a
    success keeps the states related and its result `R`-related to `c`, and a failure that
    fired downstream means the upstream state fired), then wrapping its result by `w`
    stutters relationally against `cU` for `R'`, provided `w` maps every result
    `R`-related to `c` to one `R'`-related to `cU`. -/
private theorem StuttersRel.bind_pure {K : RelCtx}
    {R R' : IConfig Expression Command → IConfig Expression Command → Prop}
    {X' : ReplayM Expression (IConfig Expression Command)} {c cU : IConfig Expression Command}
    {w : IConfig Expression Command → IConfig Expression Command}
    (h : StuttersRel K R X' c) (hw : ∀ c'1, R c'1 c → R' (w c'1) cU) :
    StuttersRel K R' (X' >>= fun i => pure (w i)) cU := fun s' s hs => by
  have hX := h s' s hs
  rcases hr : rrun X' K.cfgD s' with ⟨_ | a, _⟩ <;> simp_all [rrun_bind, rrun_pure, -bind_pure_comp]

/-- Lifting a step through frames: the downstream configuration `D` steps its inner
    configuration `i'` and wraps the result by `w'`; the upstream configuration `U` steps its
    inner configuration `i` and wraps the result by `w`, unless `i` is done.  If the inner
    downstream step stutters relationally against `i` (`StuttersRel`) with a side condition `Q`
    under which `w'` relates every result `R`-related to `i` to `U`, or is dominated by the
    inner upstream step (`RelDom`: every downstream outcome is matched by an upstream one with
    `R`-related results), and `w'`, `w` preserve `R`, the same holds for `D` and `U`, with the
    side condition `Q'` that `Q` implies. -/
private theorem cel_frameStep {K : RelCtx}
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    {sc' sc : StepCmdM Expression Command (ReplayM Expression)} {k m : Nat}
    {i' i D U : IConfig Expression Command}
    {w' w : IConfig Expression Command → IConfig Expression Command} {Q Q' : Prop}
    (e' : stepInterp sc' k D = stepInterp sc' k i' >>= fun x => pure (w' x))
    (e : ¬ i.Done → stepInterp sc m U = stepInterp sc m i >>= fun x => pure (w x))
    (hd : ¬ U.Done) (hRs : Q → ∀ a', R a' i → R (w' a') U)
    (hR : ∀ a' a, R a' a → R (w' a') (w a)) (hQ : Q → Q')
    (h : (StuttersRel K R (stepInterp sc' k i') i ∧ Q) ∨
      (¬ i.Done ∧ RelDom K (stepInterp sc' k i') (stepInterp sc m i) R)) :
    (StuttersRel K R (stepInterp sc' k D) U ∧ Q') ∨
      (¬ U.Done ∧ RelDom K (stepInterp sc' k D) (stepInterp sc m U) R) := by
  rw [e']
  rcases h with ⟨h, hq⟩ | ⟨hnd, h⟩
  · exact .inl ⟨h.bind_pure (hRs hq), hQ hq⟩
  · exact .inr ⟨hd, e hnd ▸ .bind h (fun _ _ hr => .pure (hR _ _ hr)) fun _ => Grows.pure _ _⟩

/-- A pure downstream computation whose result is `R`-related to `c` stutters
    relationally against `c` (`StuttersRel`). -/
private theorem StuttersRel.pure {K : RelCtx}
    {R : IConfig Expression Command → IConfig Expression Command → Prop}
    {c'1 c : IConfig Expression Command} (h : R c'1 c) :
    StuttersRel K R (Pure.pure c'1) c := by grind [rrun_pure, StuttersRel]

/-- Recording a step whose level command, if any, defines no name leaves a scope frame
    unchanged. -/
private theorem record_of_defs_nil {fr : ScopeFrame Expression} {c? : Option Command}
    (h : ∀ c, c? = some c → CmdDefs.defs (P := Expression) c = []) : fr.record c? = fr := by
  obtain ⟨σ, _ | D⟩ := fr <;> cases c? <;> simp_all [ScopeFrame.record]

/-- An inserted command (an `assert` or `assume` with a reserved label) defines no name. -/
private theorem isExtraCmd_defs {ext : String → Bool} {c : Cmd Expression}
    (h : isExtraCmd ext c = true) :
    CmdDefs.defs (P := Expression) (CmdExt.cmd c : Command) = [] := by
  cases c <;> first | rfl | simp [isExtraCmd] at h

/-- The downstream step of an inserted command (an `assert` or `assume` with a reserved
    label) emits one event only the downstream run emits (`K.Extra`) and changes nothing
    else, so it stutters relationally against the upstream list waiting after it, the
    configurations staying related by `InsC`. -/
private theorem stuttersRel_extra {K : RelCtx} (hK : K.Compat) {ext : String → Bool}
    (hX : ∀ ev, InsExtra ext ev → K.Extra ev) (π' : String → Option Procedure) (k : Nat)
    {c : Cmd Expression} (hc : isExtraCmd ext c = true) {ds us : List Statement}
    {env : IEnv Expression} (hds : InsL ext ds us) :
    StuttersRel K (InsU ext)
      (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k
        (.seq (.stmt (.cmd (.cmd c)) env) ds)) (.stmts us env) := by
  cases c <;> simp only [isExtraCmd, Bool.false_eq_true] at hc
  all_goals
    simp! only [replayStepCmd_cmd, stepBaseCmdStore_assert, stepBaseCmdStore_assume, bind_assoc,
      pure_bind]
    intro s' s hs
    simp only [rrun_emit_bind]
    split
    · exact ⟨fun _ _ h => by cases h; exact ⟨⟨hs.1, hs.2.1, .extra (hX _ hc) hs.2.2⟩, .xdone hds⟩,
        nofun⟩
    · exact ⟨nofun, fun _ _ h => by
        cases h; exact StRel.fired hK ⟨hs.1, hs.2.1, .extra (hX _ hc) hs.2.2⟩⟩

/-- **The per-step obligation of an insertion phase.**  One downstream step from
    interpreter configurations related by `InsC` (equal environments and scope frames; the
    downstream statements are the upstream ones with inserted commands), whose downstream
    abstraction (`IConfig.abs`) is not done, at fuel `1 ≤ k ≤ m`, either stutters
    relationally against the upstream configuration (`StuttersRel`) or is dominated by one
    upstream step at fuel `m` (`RelDom`), the results staying related.  Assumed: the oracle
    cursors agree, every event is related to itself, and every event an inserted command
    emits is downstream-only (`K.Extra`).  The procedure tables do not matter because related
    configurations contain no call. -/
private theorem ins_step {K : RelCtx} (hK : K.Compat) (hO : K.freeOracle = false)
    (hER : ∀ ev, K.ER ev ev) {ext : String → Bool}
    (hX : ∀ ev, InsExtra ext ev → K.Extra ev) (π' π : String → Option Procedure) :
    ∀ {c' c : IConfig Expression Command}, InsC ext c' c → ¬ c'.Done →
      ∀ k m, 1 ≤ k → k ≤ m →
      StuttersRel K (InsU ext) (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c') c ∨
      (¬ c.Done ∧ RelDom K (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c')
        (stepInterp (replayStepCmd (m := ReplayM Expression) π d) m c) (InsU ext)) := by
  have H : ∀ {c' c : IConfig Expression Command}, InsC ext c' c → ¬ c'.Done →
      ∀ k m, 1 ≤ k → k ≤ m →
      (StuttersRel K (InsU ext) (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c') c ∧
        ∀ fr : ScopeFrame Expression, fr.record c'.levelCmd? = fr) ∨
      (¬ c.Done ∧ RelDom K (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c')
        (stepInterp (replayStepCmd (m := ReplayM Expression) π d) m c) (InsU ext)) := by
    intro c' c h
    induction h <;> intro hnd k m hk hkm
    case stmt h =>
      refine .inr ⟨nofun, ?_⟩
      cases h <;> (try cases ‹ExprOrNondet _›) <;>
        simp only [stepInterp, replayStepCmd_cmd, resolveGuard, bind_assoc] <;> first
          | exact .bind (stepBaseCmdStore_relEq hK hO hER hkm _ _ _)
              (fun _ _ h => h ▸ .pure .terminal) fun _ => by grows_tac
          | exact .bind (.choose hK hO _ _ _ _) (fun _ _ h => by
              cases h.1
              (repeat' split) <;> first
                | exact .pure (by (repeat' constructor) <;> assumption)
                | exact .throw hK _ _)
              fun _ => by grows_tac
          | cel_cmdArm ‹_› ((repeat' constructor) <;> assumption)
    case seq i' i ds us hi hds ih =>
      by_cases hd : i'.Done
      · cases hi <;> simp only [IConfig.Done] at hd <;> refine .inr ⟨nofun, ?_⟩ <;>
          simp! only [stepInterp] <;> (try split) <;>
          exact .pure (by simp only [InsU, IConfig.unseqs]; grind [InsC])
      · exact cel_frameStep (stepInterp_seq_notDone _ _ hd ds) (stepInterp_seq_notDone _ _ · us)
          (by nofun) (fun _ _ h => .seq h hds) (fun _ _ h => .seq h hds) id (ih hd k m hk hkm)
    case block l fr i' i hi ih =>
      by_cases hd : i'.Done
      · cases hi <;> simp only [IConfig.Done] at hd <;> refine .inr ⟨nofun, ?_⟩ <;>
          simp! only [stepInterp] <;> (try split) <;>
          exact .pure (by simp only [InsU, IConfig.unseqs]; grind [InsC])
      · have hrec : fr.record i'.levelCmd? = fr.record i.levelCmd? := by
          clear ih hd hnd
          induction hi with
          | stmt hs => cases hs <;> rfl
          | seq _ _ ih => exact ih
          | xrun hc _ =>
            exact (record_of_defs_nil fun _ h => by cases h; exact isExtraCmd_defs hc).trans
              (record_of_defs_nil (c? := none) nofun).symm
          | _ => rfl
        exact cel_frameStep (stepInterp_block_notDone _ _ hd l fr)
          (stepInterp_block_notDone _ _ · l fr) (by nofun)
          (fun hq _ h => by rw [hq fr]; exact .block h)
          (fun _ _ h => by rw [hrec]; exact .block h)
          (fun _ _ => record_of_defs_nil nofun) (ih hd k m hk hkm)
    case stmts hl =>
      cases hl with
      | nil =>
        refine .inr ⟨nofun, ?_⟩
        simp only [stepInterp]
        refine RelDom.pure ?_
        exact .terminal
      | cons hS hL' =>
        rename_i ds1 us1
        have hL0 := hL'
        refine .inr ⟨nofun, ?_⟩
        cases us1 <;> cases hL' <;> simp only [stepInterp] <;> refine RelDom.pure ?_ <;>
          exact .seq (.stmt hS) hL0
      | extra hc hL' =>
        have hL0 := hL'
        refine .inl ⟨?_, fun _ => record_of_defs_nil nofun⟩
        cases hL' <;> simp only [stepInterp] <;> refine StuttersRel.pure ?_ <;> exact .xrun hc hL0
    case xrun hc hds =>
      exact .inl ⟨stuttersRel_extra hK hX π' k hc hds,
        fun _ => record_of_defs_nil fun _ h => by cases h; exact isExtraCmd_defs hc⟩
    case xdone hds => exact .inl ⟨.pure (.stmts hds), fun _ => record_of_defs_nil nofun⟩
    all_goals cases hnd ⟨⟩
  exact @fun _ _ h hnd k m hk hkm => (H h hnd k m hk hkm).imp_left And.left

/-! ## Loops with a measure

`MeasS`/`MeasL`/`MeasC` treat a measure snapshot (reserved prefix
`insertLoopInvAssertReservedPrefix`) as a downstream-only step and relate stores agreeing
outside the reserved names; every other statement draws nothing, so the simulation runs
with `RelCtx.freeOracle`. -/

/-- The names `insertLoopInvariantAsserts` introduces (measure snapshots). -/
@[expose] def measFresh (x : Expression.Ident) : Prop :=
  insertLoopInvAssertReservedPrefix.isPrefixOf x.name = true

instance : DecidablePred measFresh := fun _ => inferInstanceAs (Decidable (_ = true))

/-- Related environments: the same factory, stores agreeing outside the reserved names. -/
@[expose] def MeasEnv (env' env : IEnv Expression) : Prop :=
  env'.factory = env.factory ∧ StoreAgreeOutside measFresh env'.store.get env.store.get

/-- A base command that draws from the oracle: a nondeterministic `init` or `set`. -/
@[expose] def drawsFromOracle : Cmd Expression → Bool
  | .init _ _ .nondet _ => true
  | .set _ .nondet _ => true
  | _ => false

mutual
/-- Downstream statement related to an upstream one: identical, mentioning no reserved
    name and drawing nothing, with related sub-lists (a loop's invariants and measure
    may differ; a replay step ignores them). -/
inductive MeasS (ext : String → Bool) : Statement → Statement → Prop where
  | cmd (c : Cmd Expression) : CmdAvoids measFresh c → drawsFromOracle c = false →
      MeasS ext (.cmd (.cmd c)) (.cmd (.cmd c))
  | block (l : String) (md' md : MetaData Expression) {b' b : List Statement} :
      MeasL ext b' b → MeasS ext (.block l b' md') (.block l b md)
  | ite (e : Expression.Expr) (md' md : MetaData Expression) {t' t f' f : List Statement} :
      ExprAvoids measFresh e → MeasL ext t' t → MeasL ext f' f →
      MeasS ext (.ite (.det e) t' f' md') (.ite (.det e) t f md)
  | loop (e : Expression.Expr) (m' m : Option Expression.Expr)
      (inv' inv : List (String × Expression.Expr)) (md' md : MetaData Expression)
      {b' b : List Statement} :
      ExprAvoids measFresh e → MeasL ext b' b →
      MeasS ext (.loop (.det e) m' inv' b' md') (.loop (.det e) m inv b md)
  | exit (l : String) (md' md : MetaData Expression) : MeasS ext (.exit l md') (.exit l md)
  | typeDecl (d' d : TypeConstructor) (md' md : MetaData Expression) :
      MeasS ext (.typeDecl d' md') (.typeDecl d md)

/-- Downstream statement list related to an upstream one: related statements, with
    inserted commands and measure draws only downstream. -/
inductive MeasL (ext : String → Bool) : List Statement → List Statement → Prop where
  | nil : MeasL ext [] []
  | cons {s' s : Statement} {ds us : List Statement} :
      MeasS ext s' s → MeasL ext ds us → MeasL ext (s' :: ds) (s :: us)
  | extra {c : Cmd Expression} {ds us : List Statement} :
      isExtraCmd ext c = true → MeasL ext ds us → MeasL ext (.cmd (.cmd c) :: ds) us
  | draw {x : Expression.Ident} {ty : Expression.Ty} {md : MetaData Expression}
      {ds us : List Statement} :
      measFresh x → MeasL ext ds us → MeasL ext (.cmd (.cmd (.init x ty .nondet md)) :: ds) us
  | snap {x : Expression.Ident} {ty : Expression.Ty} {e : Expression.Expr}
      {md : MetaData Expression} {ds us : List Statement} :
      measFresh x → MeasL ext ds us → MeasL ext (.cmd (.cmd (.init x ty (.det e) md)) :: ds) us
end

/-- Related scope frames of measured loops: parent stores agreeing outside the reserved names,
    and both frames embedded (`defined = none`) or both opened with lists naming the same
    unreserved names. -/
private def MeasFrame (fr' fr : ScopeFrame Expression) : Prop :=
  StoreAgreeOutside measFresh fr'.parent.get fr.parent.get ∧
    (fr'.defined = none ↔ fr.defined = none) ∧
    ∀ D' D, fr'.defined = some D' → fr.defined = some D → ∀ x, ¬ measFresh x → (x ∈ D' ↔ x ∈ D)

/-- The interpreter configuration relation of measured loops. -/
private inductive MeasC (ext : String → Bool) :
    IConfig Expression Command → IConfig Expression Command → Prop where
  | stmt {s' s : Statement} {env' env : IEnv Expression} :
      MeasS ext s' s → MeasEnv env' env → MeasC ext (.stmt s' env') (.stmt s env)
  | stmts {ds us : List Statement} {env' env : IEnv Expression} :
      MeasL ext ds us → MeasEnv env' env → MeasC ext (.stmts ds env') (.stmts us env)
  | terminal {env' env : IEnv Expression} :
      MeasEnv env' env → MeasC ext (.terminal env') (.terminal env)
  | exiting {l : String} {env' env : IEnv Expression} :
      MeasEnv env' env → MeasC ext (.exiting l env') (.exiting l env)
  | seq {i' i : IConfig Expression Command} {ds us : List Statement} :
      MeasC ext i' i → MeasL ext ds us → MeasC ext (.seq i' ds) (.seq i us)
  | block {l : Option String} {fr' fr : ScopeFrame Expression}
      {i' i : IConfig Expression Command} :
      MeasFrame fr' fr → MeasC ext i' i → MeasC ext (.block l fr' i') (.block l fr i)
  /-- The downstream run is about to execute an inserted command. -/
  | xrun {c : Cmd Expression} {ds us : List Statement} {env' env : IEnv Expression} :
      isExtraCmd ext c = true → MeasL ext ds us → MeasEnv env' env →
      MeasC ext (.seq (.stmt (.cmd (.cmd c)) env') ds) (.stmts us env)
  /-- The downstream run is about to draw a measure snapshot. -/
  | drun {x : Expression.Ident} {ty : Expression.Ty} {md : MetaData Expression}
      {ds us : List Statement} {env' env : IEnv Expression} :
      measFresh x → MeasL ext ds us → MeasEnv env' env →
      MeasC ext (.seq (.stmt (.cmd (.cmd (.init x ty .nondet md))) env') ds) (.stmts us env)
  /-- The downstream run is about to take a deterministic measure snapshot. -/
  | srun {x : Expression.Ident} {ty : Expression.Ty} {e : Expression.Expr}
      {md : MetaData Expression} {ds us : List Statement} {env' env : IEnv Expression} :
      measFresh x → MeasL ext ds us → MeasEnv env' env →
      MeasC ext (.seq (.stmt (.cmd (.cmd (.init x ty (.det e) md))) env') ds) (.stmts us env)
  /-- The downstream run has executed an inserted command or draw. -/
  | xdone {ds us : List Statement} {env' env : IEnv Expression} :
      MeasL ext ds us → MeasEnv env' env → MeasC ext (.seq (.terminal env') ds) (.stmts us env)

/-- `MeasC` read through the expansion of sequence towers (`IConfig.unseqs`): the relation the
    monadic interpreter's steps preserve. -/
private abbrev MeasU (ext : String → Bool) (c' c : IConfig Expression Command) : Prop :=
  MeasC ext c'.unseqs c.unseqs

/-- Recording a step whose level command, if any, defines only reserved names keeps the
    downstream frame related (`MeasFrame`) to an unchanged upstream frame. -/
private theorem measFrame_record_fresh {fr' fr : ScopeFrame Expression} (h : MeasFrame fr' fr)
    {c? : Option Command}
    (hc : ∀ c, c? = some c → ∀ x ∈ CmdDefs.defs (P := Expression) c, measFresh x) :
    MeasFrame (fr'.record c?) fr := by
  obtain ⟨σp', _ | D'⟩ := fr' <;> cases c? <;> simp only [ScopeFrame.record] <;> try exact h
  refine ⟨h.1, by simpa using h.2.1, fun _ D e hD x hx => ?_⟩
  cases e
  rw [← h.2.2 D' D rfl hD x hx]
  simp only [List.mem_append, List.mem_filter]
  exact ⟨fun h1 => h1.elim (fun h2 => absurd (hc _ rfl x h2.1) hx) id, .inr⟩

/-- Recording the same level command keeps related frames (`MeasFrame`) related. -/
private theorem measFrame_record_same {fr' fr : ScopeFrame Expression} (h : MeasFrame fr' fr)
    (c? : Option Command) : MeasFrame (fr'.record c?) (fr.record c?) := by
  obtain ⟨σp', _ | D'⟩ := fr' <;> obtain ⟨σp, _ | D⟩ := fr <;> cases c? <;>
    simp_all [ScopeFrame.record, MeasFrame, StoreAgreeOutside]

/-- A measure snapshot `init x` of a reserved name `x` defines only reserved names. -/
private theorem measFresh_defs_init {x : Expression.Ident} (hx : measFresh x)
    {ty : Expression.Ty} {e : ExprOrNondet Expression} {md : MetaData Expression} :
    ∀ y ∈ CmdDefs.defs (P := Expression) (CmdExt.cmd (.init x ty e md) : Command), measFresh y :=
  fun _ hy => (List.mem_singleton.1 hy) ▸ hx

/-- A downstream computation that leaves the upstream one where it is: from related
    states, a success keeps the states related (its result satisfying `P`); a failure
    whose state has fired downstream means the upstream state has fired. -/
@[expose] def StutRel {α : Type} (K : RelCtx) (X' : ReplayM Expression α) (P : α → Prop) : Prop :=
  ∀ s' s, StRel K s' s →
    (∀ a s'1, rrun X' K.cfgD s' = (.ok a, s'1) → StRel K s'1 s ∧ P a) ∧
    (∀ e s'1, rrun X' K.cfgD s' = (.error e, s'1) → FiredD K s'1 → FiredU K s)

namespace StutRel

variable {K : RelCtx}

/-- A pure computation whose result satisfies `P` stutters (`StutRel`). -/
private theorem pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    StutRel K (Pure.pure a : ReplayM Expression α) P := by grind [rrun_pure, StutRel]

/-- A throw stutters (`StutRel`). -/
private theorem throw (hK : K.Compat) {α : Type} {P : α → Prop} (e : StopReason) :
    StutRel K (MonadExcept.throw e : ReplayM Expression α) P := by
  grind [StutRel, rrun_throw, StRel.fired]

/-- Stuttering computations (`StutRel`) compose under `bind`: if `X'` stutters with
    results satisfying `P`, and `g a` stutters with results satisfying `Q` for every `a`
    satisfying `P`, then `X' >>= g` stutters with results satisfying `Q`. -/
private theorem bind {α β : Type} {P : α → Prop} {Q : β → Prop} {X' : ReplayM Expression α}
    {g : α → ReplayM Expression β} (hx : StutRel K X' P) (hg : ∀ a, P a → StutRel K (g a) Q) :
    StutRel K (X' >>= g) Q := fun s' s hs => by
  have hX := hx s' s hs
  rcases hr : rrun X' K.cfgD s' with ⟨_ | a, s1⟩ <;> simp only [rrun_bind, hr]
  · exact ⟨nofun, fun _ _ h hf => by cases h; exact hX.2 _ _ hr hf⟩
  · exact hg a (hX.1 _ _ hr).2 _ _ (hX.1 _ _ hr).1

/-- Emitting an event only the downstream run emits (`K.Extra`) stutters (`StutRel`). -/
private theorem emit_extra (hK : K.Compat) {ev : IEvent Expression} (hx : K.Extra ev) :
    StutRel K (InterpEffects.emit (P := Expression) (m := ReplayM Expression) ev)
      (fun _ => True) := fun s' s hs => by
  have hst : StRel K {s' with traceRev := ev :: s'.traceRev} s := ⟨hs.1, hs.2.1, .extra hx hs.2.2⟩
  cel_rr
  cases K.cfgD.interruptOn ev <;> cel_rr <;> grind [StRel.fired]

/-- A draw from the oracle stutters (`StutRel`) when the oracle cursors need not agree
    (`K.freeOracle`). -/
private theorem choose (hK : K.Compat) (hFree : K.freeOracle = true)
    (F : Lambda.Factory CoreLParams) (σ : RStore Expression) (ty : Expression.Ty) :
    StutRel K (InterpEffects.choose (m := ReplayM Expression) F σ ty) (fun _ => True) :=
    fun s' s hs => by
  have htr := choose_traceRev K.cfgD F σ ty s'
  refine ⟨fun _ _ h => ⟨?_, trivial⟩, fun _ _ h hf => StRel.fired hK ?_ hf⟩ <;>
    exact ⟨.inl hFree, .inl hFree, by grind [hs.2.2]⟩

end StutRel

/-- A base command that mentions no name of `fresh` and draws nothing from the oracle,
    run downstream at fuel `k` on a store agreeing with the upstream one outside `fresh`,
    is dominated (`RelDom`) by the same command upstream at fuel `m ≥ k`, the result
    stores still agreeing outside `fresh`.  Assumed: a well-formed factory, a closed
    upstream store, and events agreeing outside `fresh`; no oracle agreement is needed. -/
private theorem stepBaseCmdStore_relDet {K : RelCtx} (hK : K.Compat)
    {fresh : Expression.Ident → Prop} (hER : AgreeCtx K fresh) {k m : Nat} (hkm : k ≤ m)
    {F : Lambda.Factory CoreLParams}
    (hF : FactoryOK F) {σ' σ : IStore Expression} (hσ : StoreClosed σ.get)
    (hag : StoreAgreeOutside fresh σ'.get σ.get) (c : Cmd Expression) (hc : CmdAvoids fresh c)
    (hnd : drawsFromOracle c = false) :
    RelDom K (stepBaseCmdStore (m := ReplayM Expression) k F σ' c)
      (stepBaseCmdStore (m := ReplayM Expression) m F σ c)
        (fun a b => StoreAgreeOutside fresh a.get b.get) :=
  cel_stepBaseCmdStore_rel hK hER hkm hF hσ hag c (.inl hnd) hc

/-- The downstream step of an inserted command (an `assert` or `assume` with a reserved
    label) stutters (`StutRel`) and ends terminal in the same environment: its results
    satisfy every `P` that holds of `.terminal env'`. -/
private theorem stutRel_extraCmd {K : RelCtx} (hK : K.Compat) {ext : String → Bool}
    (hX : ∀ ev, InsExtra ext ev → K.Extra ev) (π' : String → Option Procedure) (k : Nat)
    {c : Cmd Expression} (hc : isExtraCmd ext c = true) (env' : IEnv Expression)
    {P : IConfig Expression Command → Prop} (hP : P (.terminal env')) :
    StutRel K (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k
      (.stmt (.cmd (.cmd c)) env')) P := by
  cases c <;> simp_all! only [Bool.false_eq_true, replayStepCmd_cmd, stepBaseCmdStore_assert,
    stepBaseCmdStore_assume, bind_pure_comp, Functor.map_map] <;>
    exact .bind (.emit_extra hK (hX _ hc)) fun _ _ => .pure hP

/-- The downstream step of a measure draw `init x := *` (`x` a reserved name) stutters
    (`StutRel`) when the oracle cursors need not agree, ending terminal in an environment
    still related to the upstream one by `MeasEnv` (same factory, stores agreeing outside
    the reserved names). -/
private theorem stutRel_draw {K : RelCtx} (hK : K.Compat) (hFree : K.freeOracle = true)
    (π' : String → Option Procedure) (k : Nat) {x : Expression.Ident} (hx : measFresh x)
    (ty : Expression.Ty) (md : MetaData Expression) {env' env : IEnv Expression}
    (he : MeasEnv env' env) :
    StutRel K (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k
      (.stmt (.cmd (.cmd (.init x ty .nondet md))) env'))
      (fun c1 => ∃ env1, c1 = .terminal env1 ∧ MeasEnv env1 env) := by
  simp only [stepInterp_stmt_cmd, replayStepCmd_cmd, stepBaseCmdStore]
  split <;> simp only [pure_bind, bind_assoc] <;> first
    | exact .bind (.throw hK _) fun _ h => absurd h id
    | exact .bind (.choose hK hFree _ _ _) fun v _ =>
        .pure ⟨_, rfl, he.1, by simpa using he.2.update_fresh hx v⟩

/-- The downstream step of a deterministic measure snapshot `init x := e` (`x` a reserved
    name) stutters (`StutRel`), ending terminal in an environment still related to the
    upstream one by `MeasEnv` (same factory, stores agreeing outside the reserved names);
    it draws nothing, so no oracle condition is needed. -/
private theorem stutRel_snap {K : RelCtx} (hK : K.Compat)
    (π' : String → Option Procedure) (k : Nat) {x : Expression.Ident} (hx : measFresh x)
    (ty : Expression.Ty) (e : Expression.Expr) (md : MetaData Expression)
    {env' env : IEnv Expression} (he : MeasEnv env' env) :
    StutRel K (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k
      (.stmt (.cmd (.cmd (.init x ty (.det e) md))) env'))
      (fun c1 => ∃ env1, c1 = .terminal env1 ∧ MeasEnv env1 env) := by
  simp only [stepInterp_stmt_cmd, replayStepCmd_cmd, stepBaseCmdStore]
  split <;> first
    | exact .bind (.throw _ _) fun _ h => absurd h id
    | split <;> (try split) <;> first
        | exact .bind (.throw hK _) fun _ h => absurd h id
        | exact .pure ⟨_, rfl, he.1, by simpa using he.2.update_fresh hx _⟩

/-- One downstream step from interpreter configurations related by `MeasC` (the
    downstream statements are the upstream ones with inserted commands and measure
    snapshots, the stores agreeing outside the reserved names, the scope frames related by
    `MeasFrame`) whose abstractions (`IConfig.abs`) are well-formed, the downstream one not
    done, at fuel `1 ≤ k ≤ m`, either stutters relationally (`StuttersRel`: an inserted
    command, a measure snapshot, or a pure step towards one), recording in a frame related to
    an upstream frame one still related to it, or is dominated by one upstream step at fuel
    `m` (`RelDom`), the results staying related.  Assumed: the oracle cursors need not agree,
    events agree outside the reserved names, and every event an inserted command emits is
    downstream-only (`K.Extra`). -/
private theorem m_step {K : RelCtx} (hK : K.Compat) (hFree : K.freeOracle = true)
    (hER : AgreeCtx K measFresh) {ext : String → Bool}
    (hX : ∀ ev, InsExtra ext ev → K.Extra ev) (π' π : String → Option Procedure) :
    ∀ {c' c : IConfig Expression Command}, MeasC ext c' c → CfgWF c' → CfgWF c →
      ¬ c'.Done → ∀ k m, 1 ≤ k → k ≤ m →
      (StuttersRel K (MeasU ext)
          (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c') c ∧
        ∀ fr' fr, MeasFrame fr' fr → MeasFrame (fr'.record c'.levelCmd?) fr) ∨
      (¬ c.Done ∧ RelDom K (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c')
        (stepInterp (replayStepCmd (m := ReplayM Expression) π d) m c) (MeasU ext)) := by
  intro c' c h
  induction h <;> intro hwf' hwf hnd k m hk hkm
  case stmt hs he =>
    refine .inr ⟨nofun, ?_⟩
    simp only [CfgWF] at hwf' hwf
    cases hs <;> simp only [stepInterp, replayStepCmd_cmd, resolveGuard, he.1] <;> first
      | exact .bind (stepBaseCmdStore_relDet hK hER hkm hwf.1 hwf.2 he.2 _ ‹_› ‹_›)
          (fun _ _ h => .pure (.terminal ⟨rfl, h⟩)) fun _ => by grows_tac
      | cel_cmdArm ((evalBounded_agree hwf.1 hwf.2 he.2 ‹_› k).symm.trans ‹_›)
          (grind [MeasC, MeasEnv, MeasL, MeasS, MeasFrame, ScopeFrame.opened, IConfig.unseqs])
  case stmts hl he =>
    cases hl with
    | nil =>
      refine .inr ⟨nofun, ?_⟩
      simp only [stepInterp]
      refine RelDom.pure ?_
      exact .terminal he
    | cons hS hL' =>
      rename_i ds1 us1
      have hL0 := hL'
      refine .inr ⟨nofun, ?_⟩
      cases us1 <;> cases hL' <;> simp only [stepInterp] <;> refine RelDom.pure ?_ <;>
        exact .seq (.stmt hS he) hL0
    | extra hc hL' =>
      have hL0 := hL'
      refine .inl ⟨?_, fun _ _ hf => measFrame_record_fresh hf nofun⟩
      cases hL' <;> simp only [stepInterp] <;> refine StuttersRel.pure ?_ <;> exact .xrun hc hL0 he
    | draw hx hL' =>
      have hL0 := hL'
      refine .inl ⟨?_, fun _ _ hf => measFrame_record_fresh hf nofun⟩
      cases hL' <;> simp only [stepInterp] <;> refine StuttersRel.pure ?_ <;> exact .drun hx hL0 he
    | snap hx hL' =>
      have hL0 := hL'
      refine .inl ⟨?_, fun _ _ hf => measFrame_record_fresh hf nofun⟩
      cases hL' <;> simp only [stepInterp] <;> refine StuttersRel.pure ?_ <;> exact .srun hx hL0 he
  case seq i' i ds us hi hds ih =>
    by_cases hd : i'.Done
    · cases hi <;> simp only [IConfig.Done] at hd <;> refine .inr ⟨nofun, ?_⟩ <;>
        simp! only [stepInterp] <;> (try split) <;>
        exact .pure (by simp only [MeasU, IConfig.unseqs]; grind [MeasC, MeasEnv])
    · exact cel_frameStep (stepInterp_seq_notDone _ _ hd ds) (stepInterp_seq_notDone _ _ · us)
        (by nofun) (fun _ _ h => .seq h hds) (fun _ _ h => .seq h hds) id
        (ih hwf' hwf hd k m hk hkm)
  case block l fr' fr i' i hfr hi ih =>
    by_cases hd : i'.Done
    · have hex : ∀ {σ' σ : IStore Expression}, StoreAgreeOutside measFresh σ'.get σ.get →
          StoreAgreeOutside measFresh (fr'.exit σ').get (fr.exit σ).get := by
        intro σ' σ he
        obtain ⟨hp, hn, hD⟩ := hfr
        obtain ⟨σp', _ | D'⟩ := fr' <;> obtain ⟨σp, _ | D⟩ := fr <;>
          simp only [ScopeFrame.exit, reduceCtorEq, iff_false, iff_true, not_true_eq_false] at hn ⊢
        · simpa using hp.project he
        · intro x hx
          have hm := hD _ _ rfl rfl x hx
          simp_all [RStore.dropVars, StoreAgreeOutside]
      cases hi <;> simp only [IConfig.Done] at hd <;> refine .inr ⟨nofun, ?_⟩ <;>
        simp! only [stepInterp] <;> (try split) <;>
        exact .pure (by simp only [MeasU, IConfig.unseqs]; grind [MeasC, MeasEnv])
    · have hrec : MeasFrame (fr'.record i'.levelCmd?) (fr.record i.levelCmd?) := by
        clear ih hd hnd hwf' hwf
        induction hi with
        | stmt hs _ => cases hs <;> exact measFrame_record_same hfr _
        | seq _ _ ih => exact ih
        | xrun hc _ _ =>
          simp only [IConfig.levelCmd?, record_of_defs_nil (fr := fr) (c? := none) nofun]
          exact measFrame_record_fresh hfr fun _ e => by cases e; simp [isExtraCmd_defs hc]
        | drun hx _ _ | srun hx _ _ =>
          simp only [IConfig.levelCmd?, record_of_defs_nil (fr := fr) (c? := none) nofun]
          exact measFrame_record_fresh hfr fun _ e => by cases e; exact measFresh_defs_init hx
        | _ => exact measFrame_record_same hfr _
      exact cel_frameStep (stepInterp_block_notDone _ _ hd l fr')
        (stepInterp_block_notDone _ _ · l fr) (by nofun) (fun hq _ h => .block (hq _ _ hfr) h)
        (fun _ _ h => .block hrec h)
        (fun _ _ _ hf => measFrame_record_fresh hf nofun) (ih hwf'.2 hwf.2 hd k m hk hkm)
  case xrun hc hds he | drun hc hds he | srun hc hds he =>
    refine .inl ⟨StutRel.bind (P := fun c => ∃ ρ, c = .terminal ρ ∧ MeasEnv ρ _) ?_
      (fun _ ⟨_, h, he1⟩ => h ▸ .pure (.xdone hds he1)),
      fun _ _ hf => measFrame_record_fresh hf fun _ e => by
        cases e
        first
          | simp [isExtraCmd_defs hc]
          | exact measFresh_defs_init hc⟩
    first
      | exact stutRel_extraCmd hK hX π' k hc _ ⟨_, rfl, he⟩
      | exact stutRel_draw hK hFree π' k hc _ _ he
      | exact stutRel_snap hK π' k hc _ _ _ he
  case xdone hds he =>
    exact .inl ⟨.pure (.stmts hds he), fun _ _ hf => measFrame_record_fresh hf nofun⟩
  all_goals cases hnd ⟨⟩

/-- The simulation relation of measured-loop insertion: interpreter configurations related by
    `MeasC` whose abstractions (`IConfig.abs`) are both well-formed. -/
private def MeasR (ext : String → Bool) (c' c : IConfig Expression Command) : Prop :=
  MeasC ext c' c ∧ CfgWF c' ∧ CfgWF c

/-- **The per-step obligation of measured-loop insertion.**  For any procedure tables
    `π'`, `π`, the relation `MeasR ext` (interpreter configurations related by `MeasC`, both
    abstractions well-formed) satisfies `RelStepSim`: from related configurations, a
    downstream step at fuel `k ≥ 1` either stutters or is matched in lockstep by one upstream
    step at any fuel `m ≥ k`.  Assumed: the oracle cursors need not agree, events agree outside the
    reserved names, and every event an inserted command emits is downstream-only.  The
    tables do not matter because related configurations contain no call. -/
private theorem m_relStepSim {K : RelCtx} (hK : K.Compat) (hFree : K.freeOracle = true)
    (hER : AgreeCtx K measFresh) {ext : String → Bool}
    (hX : ∀ ev, InsExtra ext ev → K.Extra ev) (π' π : String → Option Procedure) :
    RelStepSim K (replayStepCmd (m := ReplayM Expression) π' d)
      (replayStepCmd (m := ReplayM Expression) π d) fun c' c => MeasR ext c'.unseqs c.unseqs := by
  refine relStepSim_unseqs fun c' c ⟨h, hwf', hwf⟩ hnd k m hk hkm => ?_
  have hpost := stepInterp_cfgWF (replayStepCmd_stepWF π' d) c' k hwf'
  have hpost' : OkPost (stepInterp (replayStepCmd (m := ReplayM Expression) π' d) k c')
      (fun a => CfgWF a.unseqs) := fun cfg s a s1 h => (cfgWF_unseqs a).2 (hpost cfg s a s1 h)
  have hpostU : OkPost (stepInterp (replayStepCmd (m := ReplayM Expression) π d) m c)
      (fun a => CfgWF a.unseqs) := fun cfg s a s1 h =>
    (cfgWF_unseqs a).2 (stepInterp_cfgWF (replayStepCmd_stepWF π d) c m hwf cfg s a s1 h)
  have hc : CfgWF c.unseqs := (cfgWF_unseqs c).2 hwf
  exact (m_step hK hFree hER hX π' π h hwf' hwf hnd k m hk hkm).imp
    (fun ⟨hst, _⟩ _ _ hs => (hst _ _ hs).imp_left fun hok _ _ hr =>
      (hok _ _ hr).imp id fun hR => ⟨hR, hpost' _ _ _ _ hr, hc⟩)
    fun ⟨hd, hdom⟩ => ⟨hd, hdom.withPost hpost' hpostU⟩

/-! ## The executable checker -/

mutual
/-- Executable check of `InsS`. -/
@[expose] def insStmtB (ext : String → Bool) : Statement → Statement → Bool
  | .cmd (.cmd c'), .cmd (.cmd c) => decide (c' = c)
  | .block l' b' _, .block l b _ => decide (l' = l) && insListB ext b' b
  | .ite g' t' f' _, .ite g t f _ => decide (g' = g) && insListB ext t' t && insListB ext f' f
  | .loop g' _ _ b' _, .loop g _ _ b _ => decide (g' = g) && insListB ext b' b
  | .exit l' _, .exit l _ => decide (l' = l)
  | .typeDecl _ _, .typeDecl _ _ => true
  | _, _ => false
  termination_by s' => sizeOf s'

/-- Executable check of `InsL.extra` at the head of the downstream list. -/
@[expose] def insExtraB (ext : String → Bool) : Statement → List Statement → List Statement → Bool
  | .cmd (.cmd c), ds, us => isExtraCmd ext c && insListB ext ds us
  | _, _, _ => false
  termination_by s' ds' => sizeOf s' + sizeOf ds'

/-- Executable check of `InsL`. -/
@[expose] def insListB (ext : String → Bool) : List Statement → List Statement → Bool
  | [], [] => true
  | s' :: ds, s :: us => (insStmtB ext s' s && insListB ext ds us) || insExtraB ext s' ds (s :: us)
  | s' :: ds, [] => insExtraB ext s' ds []
  | [], _ :: _ => false
  termination_by ds' => sizeOf ds'
end

/-- The executable checkers are sound: statements `insStmtB` accepts are related by
    `InsS`, lists `insListB` accepts are related by `InsL`, and a downstream head
    `insExtraB` accepts (an inserted command) followed by a related rest makes the whole
    lists related by `InsL`. -/
private theorem ins_checker_spec (ext : String → Bool) :
    (∀ s' s, insStmtB ext s' s = true → InsS ext s' s) ∧
    (∀ ds us, insListB ext ds us = true → InsL ext ds us) ∧
    (∀ s' ds us, insExtraB ext s' ds us = true → InsL ext (s' :: ds) us) := by
  apply insStmtB.mutual_induct <;> grind [insStmtB, insListB, insExtraB, InsS, InsL]

/-! ## The executable checker of measured-loop insertion -/

/-- An expression mentions no reserved name (executable). -/
@[expose] def measAvoidsB (e : Expression.Expr) : Bool :=
  (Lambda.LExpr.LExpr.getVars e).all fun x => !decide (measFresh x)

/-- An expression `measAvoidsB` accepts mentions no reserved name
    (`ExprAvoids measFresh`). -/
private theorem measAvoidsB_spec {e : Expression.Expr} (h : measAvoidsB e = true) :
    ExprAvoids measFresh e := fun _ hx => by grind [measAvoidsB]

/-- A base command mentions no reserved name and draws nothing (executable). -/
@[expose] def measCmdB : Cmd Expression → Bool
  | .init x _ (.det e) _ => !decide (measFresh x) && measAvoidsB e
  | .init _ _ .nondet _ => false
  | .set x (.det e) _ => !decide (measFresh x) && measAvoidsB e
  | .set _ .nondet _ => false
  | .assert _ e _ => measAvoidsB e
  | .assume _ e _ => measAvoidsB e
  | .cover _ e _ => measAvoidsB e

/-- A base command `measCmdB` accepts mentions no reserved name (`CmdAvoids measFresh`)
    and draws nothing from the oracle. -/
private theorem measCmdB_spec {c : Cmd Expression} (h : measCmdB c = true) :
    CmdAvoids measFresh c ∧ drawsFromOracle c = false := by
  cases c <;> (try cases ‹ExprOrNondet _›) <;>
    grind [measCmdB, CmdAvoids, measAvoidsB_spec, drawsFromOracle]

/-- A measure-snapshot draw: `init` of a reserved name from the oracle. -/
@[expose] def isMeasDraw : Cmd Expression → Bool
  | .init x _ .nondet _ => decide (measFresh x)
  | _ => false

/-- A deterministic measure snapshot: `init` of a reserved name from an expression
    (`insertLoopInvariantAsserts` emits `init m_old := D`). It draws nothing. -/
@[expose] def isMeasSnap : Cmd Expression → Bool
  | .init x _ (.det _) _ => decide (measFresh x)
  | _ => false

mutual
/-- Executable check of `MeasS`. -/
@[expose] def measStmtB (ext : String → Bool) : Statement → Statement → Bool
  | .cmd (.cmd c'), .cmd (.cmd c) => decide (c' = c) && measCmdB c
  | .block l' b' _, .block l b _ => decide (l' = l) && measListB ext b' b
  | .ite (.det e') t' f' _, .ite (.det e) t f _ =>
    decide (e' = e) && measAvoidsB e && measListB ext t' t && measListB ext f' f
  | .loop (.det e') _ _ b' _, .loop (.det e) _ _ b _ =>
    decide (e' = e) && measAvoidsB e && measListB ext b' b
  | .exit l' _, .exit l _ => decide (l' = l)
  | .typeDecl _ _, .typeDecl _ _ => true
  | _, _ => false
  termination_by s' => sizeOf s'

/-- Executable check of `MeasL.extra`/`MeasL.draw` at the head of the downstream list. -/
@[expose] def measExtraB (ext : String → Bool) : Statement → List Statement → List Statement → Bool
  | .cmd (.cmd c), ds, us =>
    (isExtraCmd ext c || isMeasDraw c || isMeasSnap c) && measListB ext ds us
  | _, _, _ => false
  termination_by s' ds' => sizeOf s' + sizeOf ds'

/-- Executable check of `MeasL`. -/
@[expose] def measListB (ext : String → Bool) : List Statement → List Statement → Bool
  | [], [] => true
  | s' :: ds, s :: us =>
    (measStmtB ext s' s && measListB ext ds us) || measExtraB ext s' ds (s :: us)
  | s' :: ds, [] => measExtraB ext s' ds []
  | [], _ :: _ => false
  termination_by ds' => sizeOf ds'
end

/-- The executable checkers are sound: statements `measStmtB` accepts are related by
    `MeasS`, lists `measListB` accepts are related by `MeasL`, and a downstream head
    `measExtraB` accepts (an inserted command or measure snapshot) followed by a related
    rest makes the whole lists related by `MeasL`. -/
private theorem meas_checker_spec (ext : String → Bool) :
    (∀ s' s, measStmtB ext s' s = true → MeasS ext s' s) ∧
    (∀ ds us, measListB ext ds us = true → MeasL ext ds us) ∧
    (∀ s' ds us, measExtraB ext s' ds us = true → MeasL ext (s' :: ds) us) := by
  apply measStmtB.mutual_induct <;> intros <;> (try cases ‹Cmd _›) <;>
    (try cases ‹ExprOrNondet _›) <;> grind [measStmtB, measListB, measExtraB, MeasS, MeasL,
      measCmdB_spec, measAvoidsB_spec, isMeasDraw, isMeasSnap]

/-! ## The certificate -/

mutual
/-- Syntactic inverse of an insertion phase on a statement: the inserted commands dropped
    (validated afterwards by `insListB`, so it needs no correctness proof). -/
@[expose] def undoInsS (ext : String → Bool) : Statement → Statement
  | .block l b md => .block l (undoInsL ext b) md
  | .ite g t f md => .ite g (undoInsL ext t) (undoInsL ext f) md
  | .loop g m inv b md => .loop g m inv (undoInsL ext b) md
  | s => s
  termination_by s => sizeOf s

/-- Syntactic inverse of an insertion phase on a statement list. -/
@[expose] def undoInsL (ext : String → Bool) : List Statement → List Statement
  | [] => []
  | .cmd (.cmd c) :: ds =>
    if isExtraCmd ext c then undoInsL ext ds else .cmd (.cmd c) :: undoInsL ext ds
  | s :: ds => undoInsS ext s :: undoInsL ext ds
  termination_by ss => sizeOf ss
end

mutual
/-- Syntactic inverse of measured-loop insertion on a statement: the inserted commands
    and measure draws dropped (validated afterwards by `measListB`). -/
@[expose] def undoMeasS (ext : String → Bool) : Statement → Statement
  | .block l b md => .block l (undoMeasL ext b) md
  | .ite g t f md => .ite g (undoMeasL ext t) (undoMeasL ext f) md
  | .loop g m inv b md => .loop g m inv (undoMeasL ext b) md
  | s => s
  termination_by s => sizeOf s

/-- Syntactic inverse of measured-loop insertion on a statement list. -/
@[expose] def undoMeasL (ext : String → Bool) : List Statement → List Statement
  | [] => []
  | .cmd (.cmd c) :: ds =>
    if isExtraCmd ext c || isMeasDraw c || isMeasSnap c then undoMeasL ext ds
    else .cmd (.cmd c) :: undoMeasL ext ds
  | s :: ds => undoMeasS ext s :: undoMeasL ext ds
  termination_by ss => sizeOf ss
end

mutual
/-- The first loop inside a statement related (`measStmtB`) to the downstream loop `lp'`. -/
@[expose] def measFindLoopS (ext : String → Bool) (lp' : Statement) : Statement → Option Statement
  | .loop g m inv b md =>
    if measStmtB ext lp' (.loop g m inv b md) then some (.loop g m inv b md)
    else measFindLoopL ext lp' b
  | .block _ b _ => measFindLoopL ext lp' b
  | .ite _ t f _ => (measFindLoopL ext lp' t).or (measFindLoopL ext lp' f)
  | _ => none
  termination_by s => sizeOf s

/-- The first loop inside a statement list related to the downstream loop `lp'`. -/
@[expose] def measFindLoopL (ext : String → Bool)
    (lp' : Statement) : List Statement → Option Statement
  | [] => none
  | s :: ss => (measFindLoopS ext lp' s).or (measFindLoopL ext lp' ss)
  termination_by ss => sizeOf ss
end

/-- The reserved names removed from a store. -/
@[expose] def measDropStore (σ : RStore Expression) : RStore Expression :=
  fun x => if measFresh x then none else σ x

/-- The reserved names removed from an environment's store. -/
@[expose] def measDropEnv (env : IEnv Expression) : IEnv Expression :=
  { env with store := .ofStore (measDropStore env.store.get) }

/-- A store agrees outside the reserved names with itself with the reserved names removed
    (`measDropStore`). -/
private theorem measDropStore_agree (σ : RStore Expression) :
    StoreAgreeOutside measFresh σ (measDropStore σ) := fun _ hx => by simp [measDropStore, hx]

/-- Removing the reserved names (`measDropStore`) keeps a store closed (every value a
    closed expression). -/
private theorem measDropStore_closed {σ : RStore Expression} (h : StoreClosed σ) :
    StoreClosed (measDropStore σ) := fun x v hx => h x v (by grind [measDropStore])

/-- An environment is related by `MeasEnv` (same factory, stores agreeing outside the
    reserved names) to itself with the reserved names removed from its store
    (`measDropEnv`). -/
private theorem measDropEnv_rel (env : IEnv Expression) :
    MeasEnv env (measDropEnv env) :=
  ⟨rfl, by simpa [measDropEnv, IStore.get_ofStore] using measDropStore_agree _⟩

/-- Removing the reserved names from the store (`measDropEnv`) keeps an environment
    well-formed (`EnvWF`: a well-formed factory and a store of closed values). -/
private theorem measDropEnv_wf {env : IEnv Expression} (h : EnvWF env) :
    EnvWF (measDropEnv env) :=
  ⟨h.1, by simpa [measDropEnv, IStore.get_ofStore] using measDropStore_closed h.2⟩

/-- A frame is related (`MeasFrame`) to itself with the reserved names removed from its
    parent store, keeping its defined-name list. -/
private theorem measFrame_drop (fr : ScopeFrame Expression) :
    MeasFrame fr { fr with parent := .ofStore (measDropStore fr.parent.get) } :=
  ⟨by simpa [IStore.get_ofStore] using measDropStore_agree _, Iff.rfl,
    fun _ _ h1 h2 _ _ => by simp_all⟩

/-- The upstream iteration start of a downstream one: the body `ss` of loop `lp'` about
    to start (parent store `σ`, environment `env`) maps to the body start of
    the related loop in the upstream unit `st`, reserved names dropped from the stores. -/
@[expose] def measIterBack (ext : String → Bool) (st : List Statement)
    (fr : ScopeFrame Expression) (ss : List Statement) (env : IEnv Expression)
    (lp' : Statement) : Option (IConfig Expression Command) :=
  match lp' with
  | .loop _ _ _ b' _ =>
    if ss = b' then
      match measFindLoopL ext lp' st with
      | some (.loop g m inv b md) =>
        if measStmtB ext lp' (.loop g m inv b md) && measListB ext ss b then
          some (.seq (.block .none { fr with parent := .ofStore (measDropStore fr.parent.get) }
            (.stmts b (measDropEnv env))) [.loop g m inv b md])
        else none
      | _ => none
    else none
  | _ => none

/-- An upstream iteration start `measIterBack` produces is related by `MeasC` to the
    downstream iteration start (through the expansion of sequence towers), is well-formed
    when that start is (`CfgWF`), and is not a `.stmts` configuration. -/
private theorem measIterBack_eq_some {ext : String → Bool} {st : List Statement}
    {fr : ScopeFrame Expression} {ss : List Statement}
    {env : IEnv Expression} {lp' : Statement} {c : IConfig Expression Command}
    (h : measIterBack ext st fr ss env lp' = some c) :
    MeasC ext (IConfig.seq (.block .none fr (.stmts ss env)) [lp']).unseqs
      c.unseqs ∧
    (CfgWF (IConfig.seq (.block .none fr (.stmts ss env)) [lp'] : IConfig Expression Command) →
      CfgWF c) ∧
    ∀ us env0, c ≠ .stmts us env0 := by
  unfold measIterBack at h
  (repeat' split at h) <;> simp_all only [Bool.and_eq_true, Option.some.injEq, reduceCtorEq]
  subst h
  have hb := ‹_ ∧ _›
  exact ⟨.seq (.block (measFrame_drop fr)
      (.stmts ((meas_checker_spec _).2.1 _ _ hb.2) (measDropEnv_rel _)))
      (.cons ((meas_checker_spec _).1 _ _ hb.1) .nil),
    fun hw => ⟨by simpa [IStore.get_ofStore] using measDropStore_closed hw.1, measDropEnv_wf hw.2⟩,
    nofun⟩

/-- An iteration start `.seq (.block none σ (.stmts body env)) [loop]`, mapped by
    `measIterBack`; `none` for any other shape. -/
@[expose] def measIterStart (ext : String → Bool) (st : List Statement) :
    IConfig Expression Command → List Statement → Option (IConfig Expression Command)
  | .block .none fr (.stmts ss env), [lp'] => measIterBack ext st fr ss env lp'
  | _, _ => none

/-- A configuration inside which a loop's iteration starts (the shape `loopElim`'s
    back-link cut produces), mapped frame by frame: the iteration start by `measIterBack`,
    a `.seq` continuation by its syntactic inverse (checked by `measListB`), a block with
    reserved names dropped from its parent store. -/
@[expose] def measCtxBack (ext : String → Bool) (st : List Statement) :
    IConfig Expression Command → Option (IConfig Expression Command)
  | .seq i rest =>
    (measIterStart ext st i rest).or
      ((measCtxBack ext st i).bind fun u =>
        if measListB ext rest (undoMeasL ext rest) then some (.seq u (undoMeasL ext rest))
        else none)
  | .block l fr i => (measCtxBack ext st i).map fun u =>
      .block l { fr with parent := .ofStore (measDropStore fr.parent.get) } u
  | _ => none

/-- An upstream configuration `measCtxBack` produces is related by `MeasC` to the
    downstream one (through the expansion of sequence towers), is well-formed when that
    one is (`CfgWF`), and is not a `.stmts` configuration. -/
private theorem measCtxBack_eq_some {ext : String → Bool} {st : List Statement} :
    ∀ {c' c : IConfig Expression Command}, measCtxBack ext st c' = some c →
      MeasC ext c'.unseqs c.unseqs ∧ (CfgWF c' → CfgWF c) ∧
        ∀ us env0, c ≠ .stmts us env0 := by
  intro c'
  induction c' <;> intro c h <;> simp only [measCtxBack, reduceCtorEq, Option.map_eq_some_iff,
    Option.or_eq_some_iff, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq] at h
  case seq ih =>
    rcases h with h | ⟨_, h⟩
    · unfold measIterStart at h
      split at h <;> first | exact measIterBack_eq_some h | simp at h
    · obtain ⟨u, hu, hl, rfl⟩ := h
      have hS (x : IConfig Expression Command) (ss : List Statement) :
          (IConfig.seq x ss).unseqs = .seq x.unseqs ss := by
        simp [IConfig.unseqs]
      rw [hS, hS]
      exact ⟨.seq (ih hu).1 ((meas_checker_spec _).2.1 _ _ hl), (ih hu).2.1, nofun⟩
  case block ih =>
    obtain ⟨u, hu, rfl⟩ := h
    exact ⟨.block (measFrame_drop _) (ih hu).1,
      fun hw => ⟨by simpa [IStore.get_ofStore] using measDropStore_closed hw.1, (ih hu).2.1 hw.2⟩,
      nofun⟩

/-- The certificate's configuration map.

    * A `.stmts` start: the chain's head maps to the input unit, a later start to its
      syntactic inverse (not the input unit), when related through `InsL` (equal
      environments) or else `MeasL` (reserved names dropped from the store).
    * A start inside which a loop's iteration starts maps by `measCtxBack`.
    * Any other start is declined. -/
@[expose] def insBackCfg (ext : String → Bool) (st : List Statement) (head : Bool) :
    IConfig Expression Command → Option (IConfig Expression Command)
  | .stmts ss env =>
    if head then
      if insListB ext ss st then some (.stmts st env)
      else if measListB ext ss st then some (.stmts st (measDropEnv env))
      else none
    else
      if insListB ext ss (undoInsL ext ss) && !decide (undoInsL ext ss = st) then
        some (.stmts (undoInsL ext ss) env)
      else if measListB ext ss (undoMeasL ext ss) && !decide (undoMeasL ext ss = st) then
        some (.stmts (undoMeasL ext ss) (measDropEnv env))
      else none
  | c => measCtxBack ext st c

/-- A statement list whose first non-inserted command is a measure draw. -/
@[expose] def measDrawsFirst (ext : String → Bool) : List Statement → Bool
  | .cmd (.cmd c) :: ds =>
    if isMeasDraw c then true else if isExtraCmd ext c then measDrawsFirst ext ds else false
  | _ => false

/-- A configuration inside which a measured loop's iteration starts: its first draw is
    the snapshot the inserted `init m_old := *` takes. -/
@[expose] def measIterDraws (ext : String → Bool) : IConfig Expression Command → Bool
  | .seq (.block .none _ (.stmts ss _)) [.loop _ _ _ _ _] => measDrawsFirst ext ss
  | .seq i _ => measIterDraws ext i
  | .block _ _ i => measIterDraws ext i
  | _ => false

/-- The certificate's oracle map: a start inside which a measured loop's iteration starts
    drops its first value (the snapshot the inserted `init m_old := *` draws); any other
    start keeps the oracle. -/
@[expose] def insBackOracle (ext : String → Bool) (c : IConfig Expression Command)
    (o : List Expression.Expr) : List Expression.Expr :=
  if measIterDraws ext c then o.drop 1 else o

/-- The certificate's oracle map `insBackOracle` keeps the oracle of a `.stmts` start. -/
private theorem insBackOracle_stmts (ext : String → Bool) (ss : List Statement)
    (env : IEnv Expression) (o : List Expression.Expr) :
    insBackOracle ext (.stmts ss env) o = o := rfl

/-- When the certificate's configuration map `insBackCfg` maps `c'` to `c`, either both
    are `.stmts` starts on equal environments whose lists are related by `InsL`, or the
    expansions of the sequence towers of `c'` and `c` are related by `MeasC` and `c` is
    well-formed when `c'` is.  In both cases a
    `.stmts` start has a `.stmts` image whose list is the input unit `st` exactly when
    `head` holds, and a start that is not `.stmts` has an image that is not `.stmts`. -/
private theorem insBackCfg_spec {ext : String → Bool} {st : List Statement} {head : Bool}
    {c' c : IConfig Expression Command} (h : insBackCfg ext st head c' = some c) :
    (∃ ss us env, c' = .stmts ss env ∧ c = .stmts us env ∧ InsL ext ss us ∧
      (head = true → us = st) ∧ (head = false → us ≠ st)) ∨
    (MeasC ext c'.unseqs c.unseqs ∧ (CfgWF c' → CfgWF c) ∧
      (∀ ss env, c' = .stmts ss env → ∃ us env0, c = .stmts us env0 ∧
        (head = true → us = st) ∧ (head = false → us ≠ st)) ∧
      ((∀ ss env, c' ≠ .stmts ss env) → ∀ us env0, c ≠ .stmts us env0)) := by
  cases c' with
  | stmts ss env =>
    cases head <;> simp only [insBackCfg, Bool.false_eq_true, ↓reduceIte] at h <;> split at h <;>
      (try split at h) <;> (try cases h)
    all_goals first
      | exact .inl ⟨_, _, _, rfl, rfl, (ins_checker_spec _).2.1 _ _ (by grind), by grind, by grind⟩
      | exact .inr ⟨.stmts ((meas_checker_spec _).2.1 _ _ (by grind)) (measDropEnv_rel env),
          measDropEnv_wf, fun _ _ _ => ⟨_, _, rfl, by grind, by grind⟩,
          fun hn => absurd rfl (hn ss env)⟩
  | _ =>
    have ⟨hM, hW, hn⟩ := measCtxBack_eq_some h
    exact .inr ⟨hM, hW, nofun, fun _ => hn⟩

/-- The downstream claim validity of an insertion certificate: genuine and feasible, for a
    target whose label the phase does not reserve (an inserted assert is not an upstream
    obligation). -/
@[expose] def insValid (π : String → Option Procedure) (ext : String → Bool) :
    CexValidity (AssertId Expression) :=
  fun t f c => genuineFeasible π t f c ∧ ext t.label = false

/-- **The certificate of an insertion phase** with reserved-label test `ext`, between
    tables `π'` and `π`, for any per-unit forward map `T` (the proof does not inspect it:
    related configurations contain no call).  A start related through `InsL` is
    transported on equal environments and oracles, one related through `MeasC` with the
    upstream run drawing nothing. -/
@[expose] def insCert (ext : String → Bool) (π' π : String → Option Procedure)
    (T : List Statement → Option (List Statement)) :
    ExactCert T (insValid π' ext) (genuineFeasible π) where
  backCfg := insBackCfg ext
  backOracle := fun _ c o => insBackOracle ext c o
  backTarget := id
  backFuel := fun _ => id
  top_back := by
    intro st st' _ c' c htop hc oracle
    obtain ⟨cfg, o'⟩ := c'
    rcases insBackCfg_spec hc with ⟨ss, us, env, _, rfl, _, htop', _⟩ | ⟨_, _, hs, _⟩
    · simp [isTopLevelAt, htop' rfl]
    · cases cfg with
      | stmts ss env =>
        obtain ⟨us, env0, rfl, hu, _⟩ := hs ss env rfl
        simp [isTopLevelAt, hu rfl]
      | _ => simp [isTopLevelAt] at htop
  nontop_back := by
    intro st st' _ c' c _ hc oracle
    obtain ⟨cfg, o'⟩ := c'
    rcases insBackCfg_spec hc with ⟨ss, us, env, _, rfl, _, _, hnt⟩ | ⟨_, _, hs, hn⟩
    · simp only [isTopLevelAt]
      exact hnt rfl
    · cases cfg with
      | stmts ss env =>
        obtain ⟨us, env0, rfl, _, hu⟩ := hs ss env rfl
        simp only [isTopLevelAt]
        exact hu rfl
      | _ =>
        have hn' := hn (fun _ _ h0 => by cases h0)
        cases c with
        | stmts us env0 => exact absurd rfl (hn' us env0)
        | _ => simp [isTopLevelAt]
  wf_back := by
    intro st st' _ head c' c hw hc
    rcases insBackCfg_spec hc with ⟨ss, us, env, rfl, rfl, _, _, _⟩ | ⟨_, hW, _, _⟩
    · exact hw
    · exact hW hw
  claim_back := by
    intro st st' _ t f head c' c hw hg hc
    obtain ⟨hgf, ht⟩ := hg
    rcases insBackCfg_spec hc with ⟨ss, us, env, hc', rfl, hL, _, _⟩ | ⟨hM, hW, _, _⟩
    · have ho : insBackOracle ext c'.cfg c'.oracle = c'.oracle := by
        rw [hc']; exact insBackOracle_stmts ext ss env _
      show genuineFeasible π t f ⟨_, insBackOracle ext c'.cfg c'.oracle⟩
      rw [ho]
      have hK := relProdCtx_compat (eventTransfer_eq t (Nat.le_refl f)) (InsExtra ext)
        (insExtra_halt ext ht f)
      exact claim_back_of_relSimulation (Nat.le_refl f) (eventTransfer_eq t (Nat.le_refl f))
        (insExtra_halt ext ht f)
        (relStepSim_unseqs (R := InsC ext) fun c' c hR hd k m hk hkm =>
          ins_step hK rfl (fun _ => rfl) (fun _ h => h) π' π hR hd k m hk hkm)
        c' _ (by rw [hc']; exact .stmts hL) hgf
    · have hK := relProdCtx_compat (evAgree_transfer measFresh t (Nat.le_refl f)) (InsExtra ext)
        (insExtra_halt ext ht f) true
      exact claim_back_of_relSimulation_free (Nat.le_refl f)
        (evAgree_transfer measFresh t (Nat.le_refl f)) (insExtra_halt ext ht f)
        (m_relStepSim hK rfl (fun _ _ h => h) (fun _ h => h) π' π) c' c
        ⟨hM,
          by
            exact (cfgWF_unseqs _).2 hw,
          (cfgWF_unseqs _).2 (hW hw)⟩
        _ hgf

/-! ## The two insertion phases -/

/-- The labels `precondElim` reserves: every assert it inserts is labelled
    `<prefix>_calls_<function>_<index>` (`PrecondElim.collectPrecondAsserts`), so a label is
    one when, after its last `_calls_`, it ends in `_` and the digits of an index. A label of
    a user assertion with that shape is taken for one too. -/
@[expose] def precondElimExt (l : String) : Bool :=
  match (l.splitOn "_calls_").reverse with
  | last :: _ :: _ =>
    match (last.splitOn "_").reverse with
    | idx :: _ :: _ => !idx.isEmpty && idx.all Char.isDigit
    | _ => false
  | _ => false

/-- The labels `insertLoopInvariantAsserts` reserves (`insertLoopInvAssertPrefix`,
    `insertLoopInvAssumePrefix`). -/
@[expose] def loopInvExt (l : String) : Bool :=
  l.startsWith insertLoopInvAssertPrefix || l.startsWith insertLoopInvAssumePrefix

end -- public section

end Core
