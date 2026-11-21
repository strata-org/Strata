/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterCallSound
public import Strata.Languages.Core.Counterexample.BackLinkTarget
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterCall
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.InterpreterCallSound
import all Strata.Languages.Core.Counterexample.BackLinkTarget
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Soundness of the loop-VC decision procedure

A successful target walk (`targetWalk`, the replay behind `loopVCRun` and `pointRun`)
is a reference execution (`CoreStepStarE`) reaching, on a feasible path, a configuration
where the walk's watch fires.  Every step of the walk is a step of the reference
semantics, by the call-aware per-step soundness `Calls.callStepInterpSound`.

Key definitions: `WalkReached`, `LoopVCReached`, `PointReached` (what a successful walk,
loop-VC claim and point-check claim certify), `MeasureProv` (where a recorded measure
value comes from).

Key theorems: `targetWalk_sound`, `loopVCRun_sound`, `pointRun_sound`. -/

namespace Core

open Imperative

public section

/-! ## Soundness of the loop-VC decision procedure -/

/-- An iteration of a loop with metadata `md` is in progress in the configuration `c` (its
    body block, followed by the loop, sits on the active path) and the loop's measure
    evaluates to `v` in the body block's parent store, the store at the iteration's
    start. -/
@[expose] def StartProv (f : Nat) (c : IConfig Expression Command) (md : MetaData Expression)
    (v : Expression.Expr) : Prop :=
  ∃ p fr inner g D invs body, IConfig.subAt c p = some (.seq (.block .none fr inner)
      [.loop g (some D) invs body md]) ∧ evalBounded f inner.getEnv.factory fr.parent.get D = some v

/-- Where a measure value an open iteration recorded comes from: a reference run from the
    semantic image under `F` of `start` reaches the semantic image of an interpreter configuration
    `c` that denotes at `F` and is at a head of a loop with metadata `md` whose measure evaluates
    to `v`, or the iteration was in progress at `start` with that measure value at its start. -/
@[expose] def MeasureProv (π : String → Option Procedure) (F : Expression.Factory)
    (f : Nat)
    (start : IConfig Expression Command) (md : MetaData Expression) (v : Expression.Expr) :
    Prop :=
  (∃ (revs : List (IEvent Expression)) (c : IConfig Expression Command), ∃ g D invs body env e,
    CoreStepStarE π (start.abs F) (revs.map (REvent.abs F)) (c.abs F) ∧ c.Denoting F ∧
    IConfig.focus c = some (.loop g (some D) invs body md, env, e) ∧
    evalBounded f env.factory env.store.get D = some v) ∨
  StartProv f start md v

/-- Every iteration `initialOpens f c d` finds in `c` with a recorded measure value `v` is
    in progress in `c` with measure value `v` at its start (`StartProv`: its body block,
    followed by the loop, is on the active path of `c`, and the loop's measure evaluates
    to `v` in the block's parent store). -/
private theorem initialOpens_prov (f : Nat) :
    ∀ (c : IConfig Expression Command) (d : Nat) (o : OpenIter), o ∈ initialOpens f c d →
      ∀ v, o.start = some v → StartProv f c o.md v := by
  intro c
  induction c with
  | seq inner rest ih =>
    intro d o ho v hv
    simp only [initialOpens, List.mem_append] at ho
    rcases ho with ho | ho
    · split at ho <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      subst ho
      simp only [Option.bind_eq_some_iff] at hv
      obtain ⟨D, rfl, hD⟩ := hv
      exact ⟨0, _, _, _, D, _, _, rfl, hD⟩
    · obtain ⟨p, hp⟩ := ih _ _ ho v hv
      exact ⟨p + 1, hp⟩
  | block _ _ _ ih => exact fun d o ho v hv => (ih _ _ ho v hv).elim fun p hp => ⟨p + 1, hp⟩
  | seqs inner k ih =>
    intro d o ho v hv
    obtain ⟨p, hp⟩ := ih _ _ ho v hv
    refine ⟨p + k + 1, ?_⟩
    simpa [IConfig.subAt, show ¬ p + k < k by omega] using hp
  | _ => simp [initialOpens]

/-- **What a loop-VC claim certifies in the reference semantics.**  A reference run from the
    image under `F` of `start` reaches, on a feasible path (every assumption holds at fuel `f`),
    the image of a configuration denoting at `F` about to execute a loop with the target's
    metadata, where the VC's expression evaluates at fuel `f` to the false literal up to metadata
    (`InterpLang.eqModuloMeta`); a measure value the decrease VC compares with has a provenance
    (`MeasureProv`). -/
@[expose] def LoopVCReached (π : String → Option Procedure) (F : Expression.Factory)
    (id : LoopVCId) (f : Nat) (start : IConfig Expression Command) : Prop :=
  ∃ (revs : List (IEvent Expression)) (c : IConfig Expression Command),
    ∃ g m invs body env e start? x,
    CoreStepStarE π (start.abs F) (revs.map (REvent.abs F)) (c.abs F) ∧ c.Denoting F ∧
    PathFeasible f revs ∧
    IConfig.focus c = some (.loop g m invs body id.loopMd, env, e) ∧
    loopVCExpr id.kind m invs start? = some x ∧
    (∃ v, evalBounded f env.factory env.store.get x = some v ∧
      InterpLang.eqModuloMeta v (HasBool.ff (P := Expression)) = true) ∧
    (∀ v, start? = some v → MeasureProv π F f start id.loopMd v)

/-- `evalsFalse f env x` holds exactly when `x` evaluates under the bounded evaluator at fuel
    `f` in `env` to a value equal to the false literal up to metadata
    (`InterpLang.eqModuloMeta`). -/
private theorem evalsFalse_iff {f : Nat} {env : IEnv Expression} {x : Expression.Expr} :
    evalsFalse f env x = true ↔
      ∃ v, evalBounded f env.factory env.store.get x = some v ∧
        InterpLang.eqModuloMeta v (HasBool.ff (P := Expression)) = true := by
  simp only [evalsFalse, Calls.evalsFalse, InterpLang.boundedEval]
  split <;> simp_all

/-- A trace whose reversal `PathFeasibleB` accepts is a feasible path (`PathFeasible`:
    every assumption on it evaluates to true at fuel `f`). -/
private theorem pathFeasibleB_reverse {f : Nat} {evs : List (IEvent Expression)}
    (h : PathFeasibleB f evs.reverse = true) : PathFeasible f evs := fun b hb =>
  Calls.pathFeasibleB_iff.1 h b (List.mem_reverse.2 hb)

/-- The iteration `findReentry opens md e` returns is one of `opens` and has metadata
    `md`. -/
private theorem findReentry_spec {opens : List OpenIter} {md : MetaData Expression} {e : Nat}
    {o : OpenIter} (h : findReentry opens md e = some o) : o ∈ opens ∧ o.md = md :=
  ⟨List.mem_of_find?_eq_some h, of_decide_eq_true (Bool.and_eq_true .. ▸ List.find?_some h).1⟩

/-- When the loop-head watch of the loop VC `id` fires on `c` with the open iterations
    `opens` (`loopHeadFires`), `c` is about to execute a loop with the target's metadata,
    the VC's expression evaluates to false there at fuel `f`, and any measure value the
    VC compares with is the recorded start value of an iteration of `opens` with that
    metadata. -/
private theorem loopHeadFires_spec {id : LoopVCId} {f : Nat} {opens : List OpenIter}
    {c : IConfig Expression Command} (h : loopHeadFires id f opens c = true) :
    ∃ g m invs body env e start? x,
      IConfig.focus c = some (.loop g m invs body id.loopMd, env, e) ∧
      loopVCExpr id.kind m invs start? = some x ∧
      (∃ v, evalBounded f env.factory env.store.get x = some v ∧
      InterpLang.eqModuloMeta v (HasBool.ff (P := Expression)) = true) ∧
      (∀ v, start? = some v → ∃ o ∈ opens, o.md = id.loopMd ∧ o.start = some v) := by
  simp only [loopHeadFires] at h
  split at h <;> grind [evalsFalse_iff, findReentry_spec]

/-- When the iteration-start watch of the loop VC `id` fires on `c` (`iterationFires`),
    `c` is about to execute a loop with the target's metadata, and the VC's expression,
    built without a measure start value, evaluates to false there at fuel `f`. -/
private theorem iterationFires_spec {id : LoopVCId} {f : Nat} {c : IConfig Expression Command}
    (h : iterationFires id f c = true) :
    ∃ g m invs body env e x,
      IConfig.focus c = some (.loop g m invs body id.loopMd, env, e) ∧
      loopVCExpr id.kind m invs none = some x ∧
      (∃ v, evalBounded f env.factory env.store.get x = some v ∧
      InterpLang.eqModuloMeta v (HasBool.ff (P := Expression)) = true) := by
  fun_cases iterationFires <;> grind [iterationFires, evalsFalse_iff]

/-- Every iteration of `eraseOpen l o` is an iteration of `l`. -/
private theorem mem_eraseOpen {o x : OpenIter} : ∀ {l : List OpenIter}, x ∈ eraseOpen l o → x ∈ l
  | [], h => by simp [eraseOpen] at h
  | y :: ys, h => by
    unfold eraseOpen at h
    split at h
    exact .tail _ h
    exact (List.mem_cons.1 h).elim (· ▸ .head _) (.tail _ ∘ mem_eraseOpen)

/-- Every open iteration after the step from `c` to `c'` (`updateOpens`) is one from
    before, or the iteration the step started: the loop in `c`'s focus has its metadata,
    and its recorded start value is that loop's measure evaluated in the focus store. -/
private theorem mem_updateOpens {f : Nat} {opens : List OpenIter}
    {c c' : IConfig Expression Command} {o : OpenIter} (h : o ∈ updateOpens f opens c c') :
    o ∈ opens ∨ ∃ g m invs body env e, IConfig.focus c = some (.loop g m invs body o.md, env, e) ∧
      o.start = m.bind fun d => evalBounded f env.factory env.store.get d := by
  simp only [updateOpens] at h
  split at h
  (repeat' split at h) <;> grind [→ mem_eraseOpen]
  exact .inl (List.mem_filter.1 h).1

/-- What a successful target walk certifies in the reference semantics: a reference run from
    the semantic image under `F` of `start` reaches, on a feasible path (every assumption holds at
    fuel `f`), the semantic image of an interpreter configuration `c` that denotes at `F` where the
    walk's watch fires — before the step from `c`, with open iterations whose recorded measure
    values have a provenance (`MeasureProv`), or at a step from `c`. -/
@[expose] def WalkReached (π : String → Option Procedure) (F : Expression.Factory)
    (W : WalkFire)
    (f : Nat) (start : IConfig Expression Command) : Prop :=
  ∃ (revs : List (IEvent Expression)) (c : IConfig Expression Command),
    CoreStepStarE π (start.abs F) (revs.map (REvent.abs F)) (c.abs F) ∧ c.Denoting F ∧
    PathFeasible f revs ∧
    ((∃ opens, W.pre opens c = true ∧
        ∀ o ∈ opens, ∀ v, o.start = some v → MeasureProv π F f start o.md v) ∨
     (∃ c', W.post c c' = true))

/-- If `targetWalk.go` succeeds from a tracked configuration `c` (`IConfig.Tracked`) denoting at
    `F`, whose image `c.abs F` a reference run from the image of `start` reaches emitting the
    images of `revs` (`CoreStepStarE`), with the replay trace equal to `revs`, `c.abs F`
    satisfying the call-site invariant (`CoreCfgInv`) and every recorded measure value of the
    open iterations `opens` having a provenance (`MeasureProv`), then the walk's watch `W` is
    reached (`WalkReached`); for well-formed procedures (`ProcsOk`) and factory (`FactoryWF`)
    and a bounded evaluator sound at `F` (`BoundedEvalSoundAt`). -/
private theorem targetWalk_go_sound (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (W : WalkFire) (f : Nat)
    (start : IConfig Expression Command) (F : Expression.Factory)
    (hEval : BoundedEvalSoundAt Expression F)
    (hfac : FactoryWF (P := Expression) F) :
    ∀ (budget : Nat) (c : IConfig Expression Command) (st : ReplayState Expression)
      (opens : List OpenIter) (revs : List (IEvent Expression)),
      CoreStepStarE π (start.abs F) (revs.map (REvent.abs F)) (c.abs F) → c.Denoting F →
      st.traceRev = revs.reverse → CoreCfgInv π (c.abs F) → c.Tracked →
      (∀ o ∈ opens, ∀ v, o.start = some v → MeasureProv π F f start o.md v) →
      targetWalk.go π W f budget c st opens = true → WalkReached π F W f start := by
  intro budget
  induction budget <;> intro c st opens revs hrun hd htr hinv ht hopens h <;>
    unfold targetWalk.go at h <;> split at h
  any_goals
    rename_i hpre
    simp only [Bool.and_eq_true] at hpre
    exact ⟨revs, c, hrun, hd, pathFeasibleB_reverse (htr ▸ hpre.2),
      .inl ⟨_, hpre.1, fun o ho v hv => hopens o (List.mem_filter.1 ho).1 v hv⟩⟩
  split at h <;> cases h
  rename_i ih _
  split at h; cases h
  rename_i hfin
  simp only [] at h
  split at h; cases h
  rename_i c' st' hc'
  have ⟨⟨revs', hstep, htr'⟩, hd', hinv', ht'⟩ := Calls.callStepInterpSound
    (obsReplay (P := Expression)) _ ((procsOk_iff π).mp hprocs) _ F _ _ _ _ _ _ hc'
    (by rintro _ rfl; simp [IConfig.Done] at hfin) (by rintro _ _ rfl; simp [IConfig.Done] at hfin)
    hfac hEval hd ((coreCfgInv_iff π _).mp hinv) ht
  split at h
  rename_i hpost
  simp only [Bool.and_eq_true] at hpost
  exact ⟨revs, c, hrun, hd, pathFeasibleB_reverse (htr ▸ hpost.2), .inr ⟨c', hpost.1⟩⟩
  refine ih c' st' _ (revs ++ revs')
    (by simpa using hrun.trans _ (.step _ _ _ _ _ (Calls.stepET_toE π hstep) (.refl _))) hd'
    (by rw [List.reverse_append, ← htr]; exact htr') ((coreCfgInv_iff π _).mpr hinv') ht'
    (fun o ho v hv => ?_) h
  rcases mem_updateOpens ho with ho | ⟨g, _ | D, invs, body, env, e, hfoc, hst⟩
  exact hopens o ho v hv
  simp [hst] at hv
  exact .inl ⟨revs, c, g, D, invs, body, env, e, hrun, hd, hfoc, (hst ▸ hv :)⟩

/-- **Soundness of the target walk against the reference semantics.** For a procedure table whose
    procedures are well-formed (`ProcsOk`), if `targetWalk` with the watch `W` succeeds at fuel
    `f` on a counterexample whose tracked start denotes at a well-formed factory `F` (`FactoryWF`),
    at which the bounded evaluator is sound (`BoundedEvalSoundAt`), and has a
    semantic image satisfying the call-site invariant (`CoreCfgInv`), a reference run from that
    image reaches, on a feasible path, the image of a configuration where the watch fires, and
    every measure value recorded there has a provenance (`WalkReached`). -/
theorem targetWalk_sound (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (W : WalkFire) (f : Nat)
    (cex : CexA Expression Command) (F : Expression.Factory)
    (hEval : BoundedEvalSoundAt Expression F)
    (hfac : FactoryWF (P := Expression) F) (hd : cex.cfg.Denoting F) (ht : cex.cfg.Tracked)
    (hinv : CoreCfgInv π (cex.cfg.abs F)) (h : targetWalk π W f cex = true) :
    WalkReached π F W f cex.cfg := by
  exact targetWalk_go_sound π hprocs W f cex.cfg F hEval hfac f cex.cfg _ _ [] (.refl _) hd rfl
    hinv ht (fun o ho v hv => .inr (initialOpens_prov f cex.cfg 0 o ho v hv)) h

/-- **Soundness of the target walk against the reference semantics.** For a procedure table whose
    procedures are well-formed (`ProcsOk`), if `targetWalk` with the watch `W` succeeds at fuel `f`
    on a counterexample whose tracked start denotes at a well-formed factory `F` (`FactoryWF`),
    whose functions meet the conditions under which the bounded evaluator is sound (`EvalFactoryWF`,
    which `evalFactoryWF_of_userFuncs` gives program factories), and has a semantic image satisfying
    the call-site invariant (`CoreCfgInv`), a reference run from that image reaches, on a feasible
    path, the image of a configuration where the watch fires, and every measure value recorded there
    has a provenance (`WalkReached`). -/
theorem targetWalk_sound_of_evalFactoryWF
    (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (W : WalkFire)
    (f : Nat)
    (cex : CexA Expression Command)
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (hfac : FactoryWF (P := Expression) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked)
    (hinv : CoreCfgInv π (cex.cfg.abs F))
    (h : targetWalk π W f cex = true) :
    WalkReached π F W f cex.cfg :=
  targetWalk_sound π hprocs W f cex F (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) hfac hd
    ht hinv h

/-- **Soundness of the loop-VC decision procedure against the reference semantics.**
    For a procedure table whose procedures are well-formed (`ProcsOk`), if `loopVCRun` succeeds
    on a counterexample whose tracked start denotes at a well-formed factory `F` (`FactoryWF`), at
    which the bounded evaluator is sound (`BoundedEvalSoundAt`), and has a semantic image
    satisfying the call-site invariant (`CoreCfgInv`), a reference run from that image reaches the
    loop VC failing on a feasible path (`LoopVCReached`). -/
theorem loopVCRun_sound (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (id : LoopVCId) (f : Nat) (cex : CexA Expression Command) (F : Expression.Factory)
    (hEval : BoundedEvalSoundAt Expression F)
    (hfac : FactoryWF (P := Expression) F) (hd : cex.cfg.Denoting F) (ht : cex.cfg.Tracked)
    (hinv : CoreCfgInv π (cex.cfg.abs F))
    (h : loopVCRun π id f cex = true) :
    LoopVCReached π F id f cex.cfg := by
  obtain ⟨_, _, hrun, hden, hfeas, ⟨_, hpre, hopens⟩ | ⟨_, hpost⟩⟩ :=
    targetWalk_sound π hprocs (loopVCFire id f) f _ F hEval hfac hd ht hinv h
  · have ⟨_, _, _, _, _, _, _, _, hfoc, hx, hff, hst⟩ := loopHeadFires_spec hpre
    exact ⟨_, _, _, _, _, _, _, _, _, _, hrun, hden, hfeas, hfoc, hx, hff, fun v hv =>
      let ⟨o, hmem, hmd, hov⟩ := hst v hv
      hmd ▸ hopens o hmem v hov⟩
  · simp only [loopVCFire, Bool.and_eq_true] at hpost
    have ⟨_, _, _, _, _, _, _, hfoc, hx, hff⟩ := iterationFires_spec hpost.2
    exact ⟨_, _, _, _, _, _, _, _, none, _, hrun, hden, hfeas, hfoc, hx, hff, nofun⟩

/-- **Soundness of the loop-VC decision procedure against the reference semantics.** For a procedure
    table whose procedures are well-formed (`ProcsOk`), if `loopVCRun` succeeds on a counterexample
    whose tracked start denotes at a well-formed factory `F` (`FactoryWF`), whose functions meet the
    conditions under which the bounded evaluator is sound (`EvalFactoryWF`, which
    `evalFactoryWF_of_userFuncs` gives program factories), and has a semantic image satisfying the
    call-site invariant (`CoreCfgInv`), a reference run from that image reaches the loop VC failing
    on a feasible path (`LoopVCReached`). -/
theorem loopVCRun_sound_of_evalFactoryWF
    (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (id : LoopVCId)
    (f : Nat)
    (cex : CexA Expression Command)
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (hfac : FactoryWF (P := Expression) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked)
    (hinv : CoreCfgInv π (cex.cfg.abs F))
    (h : loopVCRun π id f cex = true) :
    LoopVCReached π F id f cex.cfg :=
  loopVCRun_sound π hprocs id f cex F (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) hfac hd
    ht hinv h

/-- **What a point-check claim certifies in the reference semantics**: a reference run from the
    semantic image under `F` of `start` reaches, on a feasible path, the semantic image of an
    interpreter configuration that denotes at `F` and is about to execute a statement with the
    check's metadata, where the check's expression evaluates at fuel `f` to a value equal to the
    false literal up to metadata (`InterpLang.eqModuloMeta`). -/
@[expose] def PointReached (π : String → Option Procedure) (F : Expression.Factory)
    (id : PointCheckId) (f : Nat) (start : IConfig Expression Command) : Prop :=
  ∃ (revs : List (IEvent Expression)) (c : IConfig Expression Command), ∃ s env e,
    CoreStepStarE π (start.abs F) (revs.map (REvent.abs F)) (c.abs F) ∧ c.Denoting F ∧
    PathFeasible f revs ∧
    IConfig.focus c = some (s, env, e) ∧ s.getMetaData = id.stmtMd ∧
    ∃ v, evalBounded f env.factory env.store.get id.expr = some v ∧
      InterpLang.eqModuloMeta v (HasBool.ff (P := Expression)) = true

/-- **Soundness of the point-check decision procedure against the reference semantics.** For a
    procedure table whose procedures are well-formed (`ProcsOk`), if `pointRun` succeeds on a
    counterexample whose tracked start denotes at a well-formed factory `F` (`FactoryWF`), at which
    the bounded evaluator is sound (`BoundedEvalSoundAt`), and has a semantic image satisfying the
    call-site invariant (`CoreCfgInv`), a reference run from that image reaches, on a feasible
    path, a statement with the check's metadata where the check's expression evaluates to false
    (`PointReached`). -/
theorem pointRun_sound (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (id : PointCheckId) (f : Nat) (cex : CexA Expression Command) (F : Expression.Factory)
    (hEval : BoundedEvalSoundAt Expression F)
    (hfac : FactoryWF (P := Expression) F) (hd : cex.cfg.Denoting F) (ht : cex.cfg.Tracked)
    (hinv : CoreCfgInv π (cex.cfg.abs F))
    (h : pointRun π id f cex = true) :
    PointReached π F id f cex.cfg := by
  obtain ⟨revs, c, hrun, hden, hfeas, ⟨_, hpre, _⟩ | ⟨_, hpost⟩⟩ :=
    targetWalk_sound π hprocs
      { pre := fun _ c => pointFires id f c, post := fun _ _ => false }
      f _ F hEval hfac hd ht hinv h
  · simp only [pointFires] at hpre
    split at hpre <;> simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at hpre
    exact ⟨revs, c, _, _, _, hrun, hden, hfeas, ‹_›, hpre.1, evalsFalse_iff.1 hpre.2⟩
  · cases hpost

/-- **Soundness of the point-check decision procedure against the reference semantics.** For a
    procedure table whose procedures are well-formed (`ProcsOk`), if `pointRun` succeeds on a
    counterexample whose tracked start denotes at a well-formed factory `F` (`FactoryWF`), whose
    functions meet the conditions under which the bounded evaluator is sound (`EvalFactoryWF`, which
    `evalFactoryWF_of_userFuncs` gives program factories), and has a semantic image satisfying the
    call-site invariant (`CoreCfgInv`), a reference run from that image reaches, on a feasible path,
    a statement with the check's metadata where the check's expression evaluates to false
    (`PointReached`). -/
theorem pointRun_sound_of_evalFactoryWF
    (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (id : PointCheckId)
    (f : Nat)
    (cex : CexA Expression Command)
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (hfac : FactoryWF (P := Expression) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked)
    (hinv : CoreCfgInv π (cex.cfg.abs F))
    (h : pointRun π id f cex = true) :
    PointReached π F id f cex.cfg :=
  pointRun_sound π hprocs id f cex F (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) hfac hd
    ht hinv h

end -- public section

end Core
