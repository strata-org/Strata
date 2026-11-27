/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Interpreter
public import Strata.DL.Imperative.InterpreterViewSound
public import Strata.Languages.Core.InterpreterCallSound
import all Strata.Languages.Cortex.Interpreter
import all Strata.Languages.Cortex.Module
import Std.Data.String.ToNat
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterCFG
import all Strata.Languages.Core.Interpreter
import Strata.Languages.Core.InterpreterProps
import Strata.Languages.Core.InterpreterDomainProps
import Strata.DL.Imperative.InterpreterConfigProps
import Strata.DL.Imperative.CmdSemanticsProps


/-! # Soundness of the Cortex interpreter

The Cortex interpreter steps Cortex commands with the call-aware stepper `Calls.stepCmdWith` at
the view `view prog`, in the host monad `HostM`. This module gives Cortex commands a command
semantics, `sem prog`: a base command and a call are what the view takes them for, and every
other command is an extension command, related by `ExtE`. It proves the view sound against it,
observed through `obsHost` (`viewSound`), and obtains the soundness of the interpreter's runs
against `EvalCmdViewE (sem prog) (calleeTable prog)`:

* `runCFG_sound`: the CFG driver `runCFG`, from a configuration that meets its invariant;
* `startProc_sound`: starting an entry procedure, from the configuration `startProc` builds;
* `runPrepared_sound`: the entry point `runPrepared`, on a program after `prepare`. The lowering
  passes of `prepare` are not covered. -/

namespace Cortex.Interp

open Imperative
open Imperative.Calls (CmdSem CmdKind ExtOutcome ExtStep)

public section

/-- The engine stop reason of a stop of `HostM`: an engine stop is itself, and every
    Cortex-specific stop is `.interrupted "Cortex"`. So `obsHost` observes only engine stop
    reasons, which is all a soundness statement about successful runs needs. -/
@[expose] def toEngine : StopReason → Imperative.StopReason
  | .engine r => r
  | _ => .interrupted "Cortex"

/-- Run a `HostM` computation with the oracle `o` from the state `st`, to its outcome, a stop
    mapped by `toEngine`, and its final state. -/
@[expose] def hostRun {α : Type} (x : HostM α) (o : Oracle) (st : HostState) :
    Except Imperative.StopReason α × HostState :=
  match ((x.run o).run).run st with
  | (.ok a, st') => (.ok a, st')
  | (.error e, st') => (.error (toEngine e), st')

/-- `hostRun` of a bind runs the first computation, then the continuation from its state; an error
    stops the run. -/
theorem hostRun_bind {α β : Type} (ma : HostM α) (f : α → HostM β) (o : Oracle)
    (st : HostState) :
    hostRun (ma >>= f) o st = (match hostRun ma o st with
      | (.ok a, st') => hostRun (f a) o st'
      | (.error e, st') => (.error e, st')) := by
  unfold hostRun
  simp only [ReaderT.run_bind, ExceptT.run_bind, StateT.run_bind]
  rcases ((ma.run o).run).run st with ⟨r, s⟩
  cases r <;> rfl

/-- `hostRun` of `f <$> x` is `hostRun x` with `f` applied to a successful result. -/
private theorem hostRun_map {α β : Type} (f : α → β) (x : HostM α) (o : Oracle) (st : HostState) :
    hostRun (f <$> x) o st = (match hostRun x o st with
      | (.ok a, st') => (.ok (f a), st')
      | (.error e, st') => (.error e, st')) := by
  unfold hostRun
  simp only [ReaderT.run_map, ExceptT.run_map, StateT.run_map]
  rcases ((x.run o).run).run st with ⟨r, s⟩
  cases r <;> rfl

/-- `read` gives the oracle and leaves the state. -/
private theorem hostRun_read (o : Oracle) (st : HostState) :
    hostRun (read : HostM Oracle) o st = (.ok o, st) := rfl

/-- `modifyGetThe HostState g` gives the first component of `g st` and moves to its second. -/
private theorem hostRun_modifyGet {α : Type} (g : HostState → α × HostState) (o : Oracle)
    (st : HostState) :
    hostRun (modifyGetThe HostState g : HostM α) o st = (.ok (g st).1, (g st).2) := rfl

/-- `pure a` gives `a` and leaves the state. -/
private theorem hostRun_pure {α : Type} (a : α) (o : Oracle) (st : HostState) :
    hostRun (pure a : HostM α) o st = (.ok a, st) := rfl

/-- An engine stop thrown as an engine stop stops the run with that reason, state unchanged. -/
private theorem hostRun_throw {α : Type} (e : Imperative.StopReason) (o : Oracle) (st : HostState) :
    hostRun (throwThe Imperative.StopReason e : HostM α) o st = (.error e, st) := rfl

/-- An engine stop thrown through `MonadExcept` stops the run with that reason, state unchanged. -/
private theorem hostRun_throwE {α : Type} (e : Imperative.StopReason) (o : Oracle)
    (st : HostState) :
    hostRun (throw e : HostM α) o st = (.error e, st) := rfl

/-- A Cortex stop stops the run with its engine reason (`toEngine`), state unchanged. -/
private theorem hostRun_throwCortex {α : Type} (e : StopReason) (o : Oracle) (st : HostState) :
    hostRun (throwThe StopReason e : HostM α) o st = (.error (toEngine e), st) := rfl

/-- A successful choice of `HostM` passes the value checks for its type and emits no event. -/
theorem hostRun_choose (rf : InterpLang.RFactory CortexExpression)
    (store : RStore CortexExpression) (ty : CortexExpression.Ty) (o : Oracle) (st : HostState)
    (v : CortexExpression.Expr) (st' : HostState)
    (h : hostRun (InterpEffects.choose (P := CortexExpression) rf store ty) o st = (.ok v, st')) :
    ((InterpLang.ops (P := CortexExpression)).isValue rf v = true
      ∧ (InterpLang.ops (P := CortexExpression)).hasType rf v ty = true)
    ∧ st'.trace.toList.reverse = st.trace.toList.reverse := by
  simp only [InterpEffects.choose, hostRun_bind, hostRun_read, hostRun_modifyGet] at h
  revert h
  cases o rf ty st.choices with
  | none => simp [hostRun_throw]
  | some w =>
    simp only
    split <;> rename_i hc
    · simp only [hostRun_pure, Prod.mk.injEq, Except.ok.injEq]
      rintro ⟨rfl, rfl⟩
      simpa using hc
    · simp [hostRun_throw]

/-- `HostM` as an `InterpObs`: its configuration is the oracle, its state `HostState`, its run
    `hostRun`, and its trace the recorded events, most recent first. -/
@[expose] def obsHost : InterpObs CortexExpression HostM where
  Cfg := Oracle
  St := HostState
  run := hostRun
  trace st := st.trace.toList.reverse
  run_pure _ _ _ := rfl
  run_throw _ _ _ := rfl
  run_bind ma f o st := by
    rw [hostRun_bind]
    rcases hostRun ma o st with ⟨r, s⟩
    cases r <;> rfl
  emit_trace ev o st st' u h := by
    have h' : st' = { st with trace := st.trace.push ev } := (Prod.mk.inj h).2.symm
    subst h'
    simp
  choose_sound := hostRun_choose
  branch_stuck _ _ _ _ _ := rfl

/-- The extension relation of Cortex. A `cast x ty e mode md` assigns the value of `e` to the
    already defined `x`, emitting no event; it ignores `ty` and `mode`. These semantics do not
    take constrained types into account: a cast to a constrained type gets its unchecked meaning
    here, as `extCmd` gives it. Its checked meaning is the one `LowerCTE` gives it (a `set` and
    the constraint's check), which `prepare` runs; that lowering is tested, not proved. Every
    other extension command has no rule and is stuck: `new`, the field, array and `instanceOf`
    commands, `virtualCall`, `throw`, an assertion that stops the run (`stopSummary?`), and a call
    whose arguments do not match the callee's formals. No extension command resolves to a call. -/
inductive ExtE : CortexExpression.Factory → SemanticStore CortexExpression → IRCmd →
    ExtOutcome CortexExpression IRCmd Hdr → Imperative.Trace CortexExpression → Prop where
  /-- A cast assigns the value of its expression to its already defined target. -/
  | cast {f σ x ty e mode md v} :
      CortexExpression.eval f σ e = some v →
      (σ x).isSome →
      ExtE f σ (.cast x ty e mode md) (.done (SemanticStore.update σ x v)) []

/-- What each Cortex command is, with the case split of `view prog`: a `.cmd` is a base command,
    except an assertion that stops the run (`stopSummary?`), a call whose arguments match the
    callee's formals (`callArgs`), or of an unknown callee, is a call with the identity
    instantiation, and every other command is an extension command. -/
@[expose] def kind (prog : UnorderedProgram) : IRCmd → CmdKind CortexExpression IRCmd Hdr
  | .cmd c =>
    match c with
    | .assert _ e md => match stopSummary? e md with
      | some _ => .ext
      | none => .base c
    | _ => .base c
  | .call lhs n args md =>
    match prog.findProcedure? n with
    | none => .call n (args.map (CallArg.inArg (P := CortexExpression)) ++
        lhs.map (CallArg.outArg (P := CortexExpression))) md some
    | some p =>
      if callsWithoutBody p then .ext else
      match callArgs p lhs args with
      | some cas => .call n cas md some
      | none => .ext
  | _ => .ext

/-- The command semantics of Cortex for the program `prog`: `kind prog` and `ExtE`. -/
@[expose] def sem (prog : UnorderedProgram) : CmdSem CortexExpression IRCmd Hdr where
  kind := kind prog
  ExtE := ExtE


/-- `view prog` and `kind prog` classify every command alike: base command, call (with the same
    arguments and instantiation), or extension command. -/
private theorem kind_of_view {prog : UnorderedProgram} (c : IRCmd) :
    (∀ b, view (m := HostM) prog c = .base b → kind prog c = .base b) ∧
    (∀ n args md inst, view (m := HostM) prog c = .call n args md inst →
      kind prog c = .call n args md inst) ∧
    (∀ run, view (m := HostM) prog c = .ext run → kind prog c = .ext) := by
  cases c
  case cmd c =>
    cases c
    case assert l e md => cases hs : stopSummary? e md <;> simp [view, kind, hs]
    all_goals simp [view, kind]
  case call lhs n args md =>
    simp only [view, kind]
    cases hp : prog.findProcedure? n with
    | none => simp
    | some p =>
      cases hb : callsWithoutBody p
      · cases hc : callArgs p lhs args <;> simp [hb, hc]
      · simp [hb]
  all_goals simp [view, kind]

/-- A Core value a runtime value denotes is a value of some type (its own sort). -/
private theorem typed_of_denotes {F : CortexExpression.Factory} {r : CortexExpression.Expr}
    {v : CortexExpression.Val} (h : InterpLang.Denotes F r v) :
    ∃ ty, HasVal.valueOfTy F v ty :=
  ⟨.forAll [] v.sort.toMonoTy, Lambda.LExpr.denoteEval_tc (Core.denotes_iff.1 h).2.2, rfl⟩

/-- A successful run of `extCmd` on a `cast` leaves the host state alone and meets `ExtStepOk`:
    `ExtE.cast` relates it to the updated store, which is value-only, typed and denoting, and
    updates an already defined name. -/
private theorem cast_ok {F : CortexExpression.Factory}
    (hEval : BoundedEvalSoundAt CortexExpression F)
    {env : Env} (hden : RStore.Denoting F env.store.get)
    (hrf : env.factory = InterpLang.rfactory F)
    (henv : Calls.CallEnvOk F (InterpLang.absStore F env.store.get))
    {fuel : Nat} {x : Core.Expression.Ident} {ty : TypeName} {e : Expr} {mode : CastMode} {md : MD}
    {σ' : Store} {o : Oracle} {st st' : HostState}
    (h : hostRun (extCmd (m := HostM) fuel env.factory env.store (.cast x ty e mode md)) o st =
      (.ok σ', st')) :
    st' = st ∧ Calls.ExtStepOk (sem prog) F env (.cast x ty e mode md) (.done σ') [] := by
  simp only [extCmd, evalExpr, setVar, stop, hostRun_bind] at h
  revert h
  cases hb : InterpLang.boundedEval (P := CortexExpression) fuel env.factory env.store.get e with
  | none => simp [hostRun_throwE]
  | some r =>
    simp only [hostRun_pure]
    split <;> rename_i hx
    · simp only [hostRun_pure, Prod.mk.injEq, Except.ok.injEq]
      rintro ⟨rfl, rfl⟩
      rw [hrf] at hb
      obtain ⟨w, hw, hdw⟩ := hEval.atAbs hden hb
      have habs : InterpLang.absStore F (env.store.update x r).get =
          SemanticStore.update (InterpLang.absStore F env.store.get) x w := by
        rw [IStore.get_update, InterpLang.absStore_update _ _ hdw]
      have hxa : (InterpLang.absStore F env.store.get x).isSome :=
        (InterpLang.absStore_isSome hden x).trans hx
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · rw [habs]
        exact .cast hw hxa
      · rw [habs]
        obtain ⟨tyw, htyw⟩ := typed_of_denotes hdw
        exact ⟨wfStore_update henv.1 x (Calls.CallLangWF.isValue_sound F r w
            (show (InterpLang.ops (P := CortexExpression)).isValue (InterpLang.rfactory F) r = true
              from (Core.denotes_iff.1 hdw).1) hdw),
          henv.2.update x htyw⟩
      · rw [IStore.get_update]
        exact hden.update x hdw
      · rw [habs]
        intro y hy
        by_cases hyx : y = x
        · subst hyx
          exact .inl hxa
        · exact .inl (by simpa [SemanticStore.update, hyx] using hy)
    · simp [hostRun_throwE]

/-- The Cortex view `view prog` agrees with `sem prog`, observed through `obsHost`. -/
theorem viewSound (prog : UnorderedProgram) :
    Calls.ViewSound obsHost (view (m := HostM) prog) (sem prog) where
  base c b h := by
    refine ⟨(kind_of_view c).1 b h, ?_⟩
    cases c
    case cmd b' =>
      simp only [view] at h
      cases b'
      case assert l e md' =>
        cases hs : stopSummary? e md' <;> simp only [hs, Calls.CmdView.base.injEq,
          reduceCtorEq] at h
        rw [← h]
        rfl
      all_goals
        simp only [Calls.CmdView.base.injEq] at h
        rw [← h]
        rfl
    all_goals (simp only [view] at h <;> (repeat' split at h) <;> simp at h)
  call c n args md inst h := (kind_of_view c).2.1 n args md inst h
  ext_kind c run h := (kind_of_view c).2.2 run h
  ext F fuel c run env r o st st' hvc hr hfac hEval hden hrf henv := by
    change Oracle at o
    change HostState at st st'
    change hostRun (run fuel env) o st = (.ok r, st') at hr
    have hthrow : ∀ {α : Type} (e : StopReason) (a : α),
        hostRun (throwThe StopReason e : HostM α) o st ≠ (.ok a, st') := fun e a h =>
      by rw [hostRun_throwCortex] at h; cases h
    cases c
    case cmd c =>
      simp only [view] at hvc
      cases c
      case assert l e md' =>
        cases hs : stopSummary? e md' <;> simp only [hs, Calls.CmdView.ext.injEq,
          reduceCtorEq] at hvc
        subst hvc
        exact absurd hr (hthrow _ _)
      all_goals simp at hvc
    case call lhs n args md =>
      simp only [view] at hvc
      revert hvc
      cases hp : prog.findProcedure? n with
      | none => simp
      | some p =>
        cases hb : callsWithoutBody p
        · cases hc : callArgs p lhs args with
          | some => simp [hb, hc]
          | none =>
            simp only [hb, hc, Bool.false_eq_true, ite_false, Calls.CmdView.ext.injEq]
            rintro rfl
            exact absurd hr (hthrow _ _)
        · simp only [hb, ite_true, Calls.CmdView.ext.injEq]
          rintro rfl
          exact absurd hr (hthrow _ _)
    case cast x ty e mode md =>
      simp only [view, Calls.CmdView.ext.injEq] at hvc
      subst hvc
      dsimp only at hr
      rw [hostRun_bind] at hr
      revert hr
      cases hc :
          hostRun (extCmd (m := HostM) fuel env.factory env.store (.cast x ty e mode md)) o st with
      | mk res s =>
        cases res with
        | error => simp
        | ok σ' =>
          simp only [hostRun_pure, Prod.mk.injEq, Except.ok.injEq]
          rintro ⟨rfl, rfl⟩
          obtain ⟨rfl, hok⟩ := cast_ok (prog := prog) hEval hden hrf henv hc
          exact ⟨[], by simp, hok⟩
    all_goals
      simp only [view, Calls.CmdView.ext.injEq] at hvc
      subst hvc
      first
        | exact absurd hr (hthrow _ _)
        | (dsimp only at hr; rw [hostRun_bind] at hr; simp [extCmd, hostRun_throwCortex] at hr)

/-- A successful run of `locatedAt md x` is a successful run of `x`, with the same result and
    final state. -/
private theorem hostRun_locatedAt {α : Type} (md : MD) (x : HostM α) (o : Oracle)
    (st st' : HostState)
    (r : α) (h : hostRun (locatedAt md x) o st = (.ok r, st')) : hostRun x o st = (.ok r, st') := by
  revert h
  unfold hostRun locatedAt
  have hrun : ((tryCatchThe StopReason x fun e => throwThe StopReason (e.locate md) :
      HostM α).run o).run.run st =
      match (x.run o).run.run st with
      | (.ok a, s) => (.ok a, s)
      | (.error e, s) => (.error (e.locate md), s) := by
    simp only [tryCatchThe, MonadExceptOf.tryCatch, ReaderT.run, ExceptT.run, ExceptT.tryCatch,
      ExceptT.mk, StateT.run]
    show StateT.bind (x o) _ st = _
    simp only [StateT.bind]
    cases h : x o st with
    | mk res s => cases res <;> rfl
  rw [hrun]
  rcases (x.run o).run.run st with ⟨res, s⟩
  cases res <;> simp

/-- `locatedAt` keeps successful runs. -/
private theorem aroundOk_locatedAt {α : Type} :
    Calls.AroundOk (CmdT := IRCmd) obsHost (α := α) fun c x => locatedAt (IRCmd.md c) x :=
  fun _ x o st st' r h => hostRun_locatedAt _ x o st st' r h

/-- A procedure a Cortex call can run is a procedure of the callee table: a Cortex call runs its
    callee uninstantiated, and no extension command resolves to a call. -/
private theorem callRuns_calleeTable {prog : UnorderedProgram} {p : IProcedure}
    (h : Calls.CallRuns (sem prog) (calleeTable prog) p) : ∃ n, calleeTable prog n = some p := by
  obtain ⟨n, p₀, inst, hπ, hinst, ⟨c, args, md, hk⟩ | ⟨_, _, _, _, _, _, _, hx⟩⟩ := h
  · have hi : inst = some := by
      cases c <;> simp only [sem, kind] at hk
      all_goals first
        | (split at hk <;> (try split at hk) <;> (try split at hk) <;> simp_all)
        | simp_all
    subst hi
    cases hinst
    exact ⟨n, hπ⟩
  · cases hx

/-- For Cortex, `ProcsOkV` follows from the check of every procedure of the callee table. -/
theorem procsOkV_of (prog : UnorderedProgram)
    (h : ∀ n p, calleeTable prog n = some p → Calls.ProcOkV (sem prog) p) :
    Calls.ProcsOkV (sem prog) (calleeTable prog) := fun p hr =>
  let ⟨n, hn⟩ := callRuns_calleeTable hr
  h n p hn

/-- The Cortex stepper's call mode `CallMode.execute` runs as its contract exactly the opaque
    callees (`ModeOk`): the callee table builds every body as a CFG that is not opaque. -/
theorem modeOk_of (prog : UnorderedProgram) :
    Calls.ModeOk (sem prog) (calleeTable prog) .execute := fun p hr => by
  obtain ⟨n, hn⟩ := callRuns_calleeTable hr
  simp only [calleeTable, Option.map_eq_some_iff] at hn
  obtain ⟨q, -, rfl⟩ := hn
  rfl

/-- A successful run of `x >>= f` is a successful run of `y >>= g`, when every successful run of
    `x` is one of `y` and every successful run of `f a` is one of `g a`. -/
private theorem hostRun_bind_mono {α β : Type} {x y : HostM α} {f g : α → HostM β} {o : Oracle}
    {st st' : HostState} {r : β}
    (hxy : ∀ a s, hostRun x o st = (.ok a, s) → hostRun y o st = (.ok a, s))
    (hfg : ∀ a s, hostRun (f a) o s = (.ok r, st') → hostRun (g a) o s = (.ok r, st'))
    (h : hostRun (x >>= f) o st = (.ok r, st')) : hostRun (y >>= g) o st = (.ok r, st') := by
  rw [hostRun_bind] at h ⊢
  revert h
  cases hx : hostRun x o st with
  | mk res s =>
    cases res with
    | error => simp
    | ok a =>
      intro h
      rw [hxy a s hx]
      exact hfg a s h

/-- A successful `runCFG` run is a successful `runInterpCFG` run of the same stepper: `runCFG`
    only wraps some steps in `locatedAt`, which keeps successful steps. -/
private theorem hostRun_runCFG (step : Imperative.StepCmdStoreM CortexExpression IRCmd HostM) :
    ∀ (n : Nat) (c c' : Config) (o : Oracle) (st st' : HostState),
      hostRun (runCFG step n c) o st = (.ok c', st') →
      hostRun (Imperative.runInterpCFG step n c) o st = (.ok c', st') := by
  intro n
  induction n with
  | zero =>
    intro c c' o st st' h
    unfold runCFG at h
    unfold Imperative.runInterpCFG
    cases c
    case terminal => exact h
    all_goals
      dsimp only at h ⊢
      exact hostRun_locatedAt _ _ _ _ _ _ h
  | succ n ih =>
    intro c c' o st st' h
    unfold runCFG at h
    unfold Imperative.runInterpCFG
    cases c
    case terminal => exact h
    all_goals
      dsimp only at h ⊢
      first
        | exact hostRun_bind_mono (fun a s hx => hx) (fun a s hf => ih _ _ _ _ _ hf) h
        | split at h
          · exact hostRun_bind_mono (fun a s hx => hostRun_locatedAt _ _ _ _ _ _ hx)
              (fun a s hf => ih _ _ _ _ _ hf) h
          · exact hostRun_bind_mono (fun a s hx => hx) (fun a s hf => ih _ _ _ _ _ hf) h

/-- The Cortex stepper `stepper prog` meets `ArmSound` at every factory at which the bounded
    evaluator is sound. -/
theorem stepper_armSound (prog : UnorderedProgram) {F : CortexExpression.Factory}
    (hEval : BoundedEvalSoundAt CortexExpression F)
    (hprocs : Calls.ProcsOkV (sem prog) (calleeTable prog)) :
    Calls.ArmSound obsHost (stepper (m := HostM) prog) (sem prog) (calleeTable prog) F :=
  Calls.armSound_wrap obsHost aroundOk_locatedAt
    (Calls.stepCmdWith_armSound obsHost (viewSound prog) aroundOk_locatedAt _ .execute hprocs
      (modeOk_of prog) hEval _)

/-- **Soundness of the Cortex CFG driver.** A successful `runCFG` run of the Cortex stepper, from a
    configuration that denotes at a well-formed factory `F` at which the bounded evaluator is sound
    and meets `CFGCfgInvV (sem prog) F`, is a reference CFG run over
    `EvalCmdViewE (sem prog) (calleeTable prog)` that emits exactly the recorded events, to a
    configuration that denotes at `F`. It assumes `ProcsOkV (sem prog) (calleeTable prog)`. Casts
    have their unchecked meaning (`ExtE`): constrained types are not taken into account. -/
theorem runCFG_sound (prog : UnorderedProgram) {F : CortexExpression.Factory}
    (hEval : BoundedEvalSoundAt CortexExpression F) (hfac : FactoryWF (P := CortexExpression) F)
    (hprocs : Calls.ProcsOkV (sem prog) (calleeTable prog)) (fuel : Nat) {c c' : Config}
    {o : Oracle} {st st' : HostState} (hd : c.Denoting F)
    (hinv : Calls.CFGCfgInvV (sem prog) F (c.abs F))
    (h : hostRun (runCFG (stepper (m := HostM) prog).toStore fuel c) o st = (.ok c', st')) :
    ∃ revs : List Event, st'.trace.toList.reverse = revs.reverse ++ st.trace.toList.reverse ∧
      StepCFGStarE CortexExpression (EvalCmdViewE (sem prog) (calleeTable prog)) (c.abs F)
        (revs.map (REvent.abs F)) (c'.abs F) ∧ c'.Denoting F :=
  Calls.runInterpCFG_sound_of_arm obsHost (calleeTable prog) (stepper_armSound prog hEval hprocs)
    hEval hfac fuel hd hinv (hostRun_runCFG _ _ _ _ _ _ _ h)

/-- Choosing a list of values, one per type, emits no event, and each chosen value passes the
    value checks for its type. -/
private theorem hostRun_mapM_choose (f : LFactory) (σ : Store) (o : Oracle) :
    ∀ (tys : List Core.Expression.Ty) (st st' : HostState) (outs : List Expr),
      hostRun (tys.mapM (chooseTyped (m := HostM) f σ)) o st = (.ok outs, st') →
      st'.trace.toList.reverse = st.trace.toList.reverse ∧
      List.Rel₂ (fun r ty => (InterpLang.ops (P := CortexExpression)).isValue f r = true ∧
        (InterpLang.ops (P := CortexExpression)).hasType f r ty = true) outs tys
  | [], st, st', outs, h => by
    simp only [List.mapM_nil, hostRun_pure, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, .nil⟩
  | ty :: tys, st, st', outs, h => by
    simp only [List.mapM_cons, hostRun_bind] at h
    revert h
    cases hc : hostRun (chooseTyped (m := HostM) f σ ty) o st with
    | mk r s =>
      cases r with
      | error => simp
      | ok v =>
        cases hr : hostRun (tys.mapM (chooseTyped (m := HostM) f σ)) o s with
        | mk r2 s2 =>
          cases r2 with
          | error => intro h; simp only [hr] at h; cases h
          | ok vs =>
            intro h
            simp only [hr, hostRun_pure, Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨⟨hv, ht⟩, htr⟩ := hostRun_choose _ _ _ _ _ _ _ hc
            obtain ⟨htr2, hrel⟩ := hostRun_mapM_choose f σ o tys s s2 vs hr
            exact ⟨htr2.trans htr, .cons ⟨hv, ht⟩ hrel⟩

/-- Runtime values that pass the value checks for their types denote values of those types. -/
private theorem typed_values_of_ops {F : CortexExpression.Factory} :
    ∀ {outs : List Expr} {tys : List Core.Expression.Ty},
      List.Rel₂ (fun r ty =>
        (InterpLang.ops (P := CortexExpression)).isValue (InterpLang.rfactory F) r = true ∧
        (InterpLang.ops (P := CortexExpression)).hasType (InterpLang.rfactory F) r ty = true)
        outs tys →
      ∃ vs, List.Rel₂ (InterpLang.Denotes F) outs vs ∧
        List.Rel₂ (fun v ty => HasVal.valueOfTy F v ty) vs tys ∧
        ∀ v ∈ vs, HasVal.value F v
  | [], [], .nil => ⟨[], .nil, .nil, nofun⟩
  | r :: _, ty :: _, .cons ⟨hv, ht⟩ hrest => by
    obtain ⟨v, hd, hty⟩ := Calls.CallLangWF.ops_typed.hasType F r ty hv ht
    obtain ⟨vs, hrel, hrelt, hval⟩ := typed_values_of_ops hrest
    refine ⟨v :: vs, .cons hd hrel, .cons hty hrelt, ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨Calls.CallLangWF.isValue_sound F r v hv hd, hval⟩

/-- The store that binds names to runtime values denoting values of some types, from the empty
    store, denotes, and its image is value-only and typed. -/
private theorem startStore_ok {F : CortexExpression.Factory} (names : List Core.Expression.Ident)
    {outs : List Expr} {vs : List CortexExpression.Val} {tys : List Core.Expression.Ty}
    (hrel : List.Rel₂ (InterpLang.Denotes F) outs vs)
    (hrelt : List.Rel₂ (fun v ty => HasVal.valueOfTy F v ty) vs tys)
    (hval : ∀ v ∈ vs, HasVal.value F v) :
    RStore.Denoting F (Store.empty.bindPositional names outs).get ∧
    Calls.CallEnvOk F (InterpLang.absStore F (Store.empty.bindPositional names outs).get) := by
  rw [IStore.get_bindPositional]
  have hempty : Store.empty.get = fun _ => none := by
    funext x
    simp [Store.empty]
  refine ⟨Calls.denoting_bindPositional names (by rw [hempty]; intro _ _ h; cases h) hrel, ?_⟩
  rw [Calls.absStore_bindPositional _ _ hrel, hempty]
  have habs : InterpLang.absStore F (fun _ => none : RStore CortexExpression) = fun _ => none := by
    funext x
    simp [InterpLang.absStore]
  rw [habs]
  have htyped : ∀ v ∈ vs, ∃ ty, HasVal.valueOfTy F v ty := by
    clear hrel hval
    induction hrelt with
    | nil => nofun
    | cons h _ ih =>
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact ⟨_, h⟩
      · exact ih v hv
  exact ⟨Calls.wellFormedStore_bindPositional _ _ _ (fun _ _ h => by cases h) hval,
    Calls.storeTyped_bindPositional _ _ _ (fun _ _ h => by cases h) htyped⟩

/-- The search of `freshLabel base used` from the index `i`, with `fuel` tries, ends in a label not
    in `used`, or every one of the `fuel` labels it tries is in `used`. -/
private theorem freshLabel_go_spec (base : String) (used : List String) :
    ∀ fuel i, used.contains (freshLabel.go base used i fuel) = false ∨
      ∀ j ∈ List.range' i fuel, used.contains s!"{base}{j}" = true
  | 0, _ => .inr (by simp)
  | fuel + 1, i => by
    simp only [freshLabel.go]
    split
    · rename_i h
      rcases freshLabel_go_spec base used fuel (i + 1) with h' | h'
      · exact .inl h'
      · refine .inr fun j hj => ?_
        rw [List.range'_succ, List.mem_cons] at hj
        rcases hj with rfl | hj
        · exact h
        · exact h' j hj
    · exact .inl (Bool.of_not_eq_true ‹_›)

/-- `freshLabel base used` is not in `used`: of the `used.length + 1` distinct labels it tries,
    one is not in `used`. -/
private theorem freshLabel_fresh (base : String) (used : List String) :
    used.contains (freshLabel base used) = false := by
  unfold freshLabel
  split
  · cases hc : used.contains base <;> simp_all
  · rcases freshLabel_go_spec base used (used.length + 1) 1 with h | h
    · exact h
    · exfalso
      have hinj : ∀ a b : Nat, s!"{base}{a}" = s!"{base}{b}" → a = b := by
        intro a b hab
        simp only [String.append_right_inj] at hab
        exact Nat.repr_injective hab
      have hnd : ((List.range' 1 (used.length + 1)).map (fun j => s!"{base}{j}")).Nodup :=
        List.pairwise_map.2 ((List.nodup_range' (s := 1) (n := used.length + 1)).imp
          fun hne e => hne (hinj _ _ e))
      have hsub : (List.range' 1 (used.length + 1)).map (fun j => s!"{base}{j}") ⊆ used := by
        intro s hs
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
        simpa using h j hj
      have := hnd.length_le_of_subset hsub
      simp at this
      omega

/-- A CFG passes the check `q` when the CFG with one more block in front, under a label that is
    not one of its own, does. -/
private theorem allCmds_of_cons {q : IRCmd → Bool} {g : Cortex.LCFG} {e fr : Label}
    {mk : Cortex.LBlock} (hfr : (g.blocks.map (·.1)).contains fr = false)
    (h : CFG.allCmds q ({ entry := e, blocks := (fr, mk) :: g.blocks } : Cortex.LCFG)) :
    g.allCmds q := by
  intro t b hb
  apply h t b
  simp only [List.lookup]
  split
  · rename_i heq
    have ht : t = fr := by simpa using heq
    subst ht
    have hs : (g.blocks.lookup t).isSome := by simp [hb]
    obtain ⟨p, hp, hpt⟩ := List.lookup_isSome_iff.1 hs
    have : t ∈ g.blocks.map (·.1) := List.mem_map.2 ⟨p, hp, (by simpa using hpt : t = p.1).symm⟩
    simp_all
  · exact hb

/-- The entry CFG passes the call-site check when the body does: the block of `globalInit`
    commands in front of it holds only base commands. -/
private theorem entryCfg_allCmds (prog : UnorderedProgram) (body : Body)
    (h : body.cfg.allCmds (Calls.CmdOk (sem prog))) :
    (entryCfg prog body).allCmds (Calls.CmdOk (sem prog)) := by
  unfold entryCfg
  split
  · exact h
  · intro t b hb
    simp only [List.lookup] at hb
    split at hb
    · cases hb
      simp only [List.all_map, List.all_eq_true]
      intro x _
      cases x
      case assert _ e md _ => cases hs : stopSummary? e md <;> simp [Calls.CmdOk, sem, kind, hs]
      all_goals rfl
    · exact h t b hb

/-- **Soundness of starting an entry procedure.** A successful `startProc` run of the entry
    procedure `p` of `prog` starts from the entry CFG `entryCfg prog body` with a store that binds
    the outputs of `p` to values of their declared types, and is, from there, a reference CFG run
    as in `runCFG_sound`. It assumes that every procedure of the callee table passes `ProcOkV`,
    which requires every argument of a call to a known callee to be a variable or a literal, in
    every procedure of the program. -/
theorem startProc_sound (prog : UnorderedProgram) {F : CortexExpression.Factory}
    (hEval : BoundedEvalSoundAt CortexExpression F) (hfac : FactoryWF (P := CortexExpression) F)
    (hck : ∀ n q, calleeTable prog n = some q → Calls.ProcOkV (sem prog) q)
    {n : ProcName} {p : Procedure} (hp : prog.findProcedure? n = some p) (fuel : Nat)
    {c' : Config} {o : Oracle} {st st' : HostState}
    (h : hostRun (startProc prog (InterpLang.rfactory F) fuel p) o st = (.ok c', st')) :
    ∃ (body : Body) (outs : List Expr) (vs : List CortexExpression.Val) (revs : List Event),
      p.body = some body ∧ List.Rel₂ (InterpLang.Denotes F) outs vs ∧
      List.Rel₂ (fun v ty => HasVal.valueOfTy F v ty) vs (p.outputs.map Prod.snd) ∧
      st'.trace.toList.reverse = revs.reverse ++ st.trace.toList.reverse ∧
      StepCFGStarE CortexExpression (EvalCmdViewE (sem prog) (calleeTable prog))
        (ICFGConfig.abs F (.atBlock (entryCfg prog body) (entryCfg prog body).entry
          { store := Store.empty.bindPositional (p.outputs.map Prod.fst) outs,
            factory := InterpLang.rfactory F }))
        (revs.map (REvent.abs F)) (c'.abs F) ∧ c'.Denoting F := by
  unfold startProc at h
  cases hb : p.body with
  | none =>
    simp only [hb, hostRun_throwCortex] at h
    cases h
  | some body =>
    simp only [hb, hostRun_bind] at h
    revert h
    cases hm : hostRun ((p.outputs.map Prod.snd).mapM
        (chooseTyped (m := HostM) (InterpLang.rfactory F) Store.empty)) o st with
    | mk r s =>
      cases r with
      | error => simp
      | ok outs =>
        intro h
        obtain ⟨htr1, hops⟩ := hostRun_mapM_choose _ _ _ _ _ _ _ hm
        obtain ⟨vs, hrel, hrelt, hval⟩ := typed_values_of_ops hops
        obtain ⟨hden, henv⟩ := startStore_ok (p.outputs.map Prod.fst) hrel hrelt hval
        have hbody : body.cfg.allCmds (Calls.CmdOk (sem prog)) := by
          have hq := hck n _ (by simp [calleeTable, hp]; rfl)
          have hc := hq.2.2 _ false rfl
          simp only [hb, Option.getD_some] at hc
          split at hc
          · exact hc
          · exact allCmds_of_cons (freshLabel_fresh _ _) hc
        obtain ⟨revs, htr2, R, hd'⟩ := runCFG_sound prog hEval hfac (procsOkV_of prog hck) fuel
          (c := .atBlock (entryCfg prog body) (entryCfg prog body).entry
            { store := Store.empty.bindPositional (p.outputs.map Prod.fst) outs,
              factory := InterpLang.rfactory F }) ⟨hden, rfl⟩
          ⟨henv, entryCfg_allCmds prog body hbody, rfl⟩ h
        exact ⟨body, outs, vs, revs, rfl, hrel, hrelt, by rw [htr2, htr1], R, hd'⟩

/-- **Soundness of the Cortex interpreter's entry point** on a prepared program. A successful
    `runPrepared prog fuel name` runs the procedure `name` from a start configuration as in
    `startProc_sound`, and its result's trace and final configuration are those of a reference CFG
    run from there. It assumes that the factory `programFactory prog` builds is well formed and
    that the bounded evaluator is sound at it, and, as `startProc_sound` does, that every
    procedure of the callee table passes `ProcOkV`, so that every argument of a call to a known
    callee is a variable or a literal. The passes `prepare` runs are not covered. -/
theorem runPrepared_sound (prog : UnorderedProgram) {F : CortexExpression.Factory}
    (hEval : BoundedEvalSoundAt CortexExpression F) (hfac : FactoryWF (P := CortexExpression) F)
    (hck : ∀ n q, calleeTable prog n = some q → Calls.ProcOkV (sem prog) q)
    (hF : programFactory prog = .ok (InterpLang.rfactory F)) {fuel : Nat} {name : ProcName}
    {r : RunResult} (h : runPrepared prog fuel name = .ok r) :
    ∃ (p : Procedure) (body : Body) (outs : List Expr) (vs : List CortexExpression.Val),
      prog.findProcedure? name = some p ∧ p.body = some body ∧
      List.Rel₂ (InterpLang.Denotes F) outs vs ∧
      List.Rel₂ (fun v ty => HasVal.valueOfTy F v ty) vs (p.outputs.map Prod.snd) ∧
      StepCFGStarE CortexExpression (EvalCmdViewE (sem prog) (calleeTable prog))
        (ICFGConfig.abs F (.atBlock (entryCfg prog body) (entryCfg prog body).entry
          { store := Store.empty.bindPositional (p.outputs.map Prod.fst) outs,
            factory := InterpLang.rfactory F }))
        (r.trace.map (REvent.abs F)) (r.final.abs F) ∧ r.final.Denoting F := by
  unfold runPrepared runPreparedTraced at h
  cases hp : prog.findProcedure? name with
  | none => simp [hp] at h
  | some p =>
    simp only [hp] at h
    by_cases hbn : p.body.isNone = true
    · simp [hbn] at h
    · simp only [hbn, hF, Bool.false_eq_true, ite_false] at h
      split at h
      · rename_i c tr hres
        cases h
        revert hres
        generalize hx : StateT.run (ExceptT.run (ReaderT.run
          (startProc prog (InterpLang.rfactory F) fuel p) _)) {} = x
        obtain ⟨res, st⟩ := x
        intro hres
        simp only [Prod.mk.injEq] at hres
        obtain ⟨rfl, rfl⟩ := hres
        obtain ⟨o, hh⟩ : ∃ o, hostRun (startProc prog (InterpLang.rfactory F) fuel p) o {} =
            (.ok c, st) := ⟨_, by unfold hostRun; rw [hx]⟩
        obtain ⟨body, outs, vs, revs, hb, hrel, hrelt, htr, R, hd⟩ :=
          startProc_sound prog hEval hfac hck hp fuel hh
        have hrevs : revs = st.trace.toList := by simpa using htr.symm
        subst hrevs
        exact ⟨p, body, outs, vs, rfl, hb, hrel, hrelt, R, hd⟩
      · cases h

end -- public section

end Cortex.Interp
