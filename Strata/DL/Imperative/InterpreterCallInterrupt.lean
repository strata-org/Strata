/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCall
public import Strata.DL.Imperative.InterpreterObs
public import Strata.DL.Imperative.InterpreterProps
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterProps
import all Strata.DL.Imperative.InterpreterCall
import Strata.DL.Imperative.InterpreterReplayTactics
public import Strata.DL.Imperative.InterpreterObsProps
public import Strata.DL.Imperative.InterpreterReplayProps
public import Strata.DL.Imperative.InterpreterCallProps

/-! # Interruption bridges between the production and spec runs of `Calls.runCallInterp π`

The production replay run stops at the first event its stop hook `interruptOn` fires on; the spec
run records every event and never stops early.  Each bridge below is a relation between the two
runs of a `ReplayM` computation, proved for `pure`, `throw`, `emit`, `choose` and `>>=`, then
lifted to `stepInterp`, `runInterp`, the callee body run `runCallee`, the call-aware stepper
`stepCmd π` and `runCallInterp π`:

* `DBridge` (`dBridge_runCallInterp`): the interrupt-on trace is a suffix of the interrupt-off
  trace, and a non-throwing interrupt-on run coincides with the off-run; hence an interrupt-on
  `.genuine` verdict is also an interrupt-off one (`runReplay_genuine_of_interruptOn`).
* `FeasBridge` (`feasBridge_runCallInterp`): under the enforcing stop hook
  `enforceInterrupt`, a run that ends `.ok` or interrupted at the target keeps a path-feasible
  trace path-feasible.
* `StopBridge` (`stopBridge_runCallInterp`): under `enforceInterrupt`, a run that records a new
  failing target event ends `.interrupted`.
* `CoBridge` (`coBridge_runCallInterp`): the interrupt-on run equals the interrupt-off run, or
  throws from the stop hook at its last recorded event.

Key theorems: `genuineFeasible_iff_genuineEnforced` (the record-only verdict with a feasible
path and the enforcing verdict agree) and `genuineEnforced_of_spec_suffix` (completeness of the
enforcing verdict from a spec trace with a feasible prefix ending at a failing target event). -/

namespace Imperative

public section

namespace Calls

variable {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- The `ReplayM` run-projection to an `(outcome, final-state)` pair. -/
private abbrev runProj {α : Type} (X : ReplayM P α) (cfg : ReplayCfg P)
    (st : ReplayState P) : Except StopReason α × ReplayState P :=
  ((X.run cfg).run).run st

omit [DecidableEq P.Ident] in
/-- `choose` leaves `traceRev` unchanged. -/
private theorem choose_traceRev_eq (factory : InterpLang.RFactory P) (store : RStore P)
    (ty : P.Ty) (cfg : ReplayCfg P) (st : ReplayState P) :
    (runProj (InterpEffects.choose (m := ReplayM P) factory store ty) cfg st).2.traceRev
      = st.traceRev := by
  simp only [InterpEffects.choose, replayM_run_read_bind, replayM_run_get_bind]
  (repeat' split) <;> rfl

/-! ## `DBridge`: the interrupt-on trace is a suffix of the interrupt-off trace -/

/-- The interrupt-on run of `x` against its run with the stop hook off: the on-run trace is a
    suffix of the off-run trace, a non-throwing on-run coincides with the off-run (`RunBridge`),
    and the off-run only prepends events to the initial trace. -/
@[reducible] def DBridge {α : Type} (x : ReplayM P α)
    (cfg : ReplayCfg P) (st : ReplayState P) : Prop :=
  RunBridge x cfg st ∧ st.traceRev <:+ (replayRun x (interruptOff cfg) st).2.traceRev

omit [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- `DBridge` holds for `pure`. -/
private theorem dBridge_pure {α} (a : α) (cfg : ReplayCfg P) (st : ReplayState P) :
    DBridge (pure a : ReplayM P α) cfg st := ⟨⟨List.suffix_rfl, fun _ _ => rfl⟩, List.suffix_rfl⟩

omit [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- `DBridge` holds for `throw`. -/
private theorem dBridge_throw {α} (r : StopReason) (cfg : ReplayCfg P)
    (st : ReplayState P) : DBridge (throw r : ReplayM P α) cfg st := by grind [replayRun_throw]

omit [DecidableEq P.Ident] in
/-- `DBridge` holds for `branch`, which throws in `ReplayM`. -/
private theorem dBridge_branch (factory : InterpLang.RFactory P) (store : RStore P) (v : P.Expr)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    DBridge (InterpEffects.branch (P := P) (m := ReplayM P) factory store v) cfg st :=
  dBridge_throw .expressionWasNotBoolean cfg st

omit [DecidableEq P.Ident] in
/-- `DBridge` holds for `emit`. -/
private theorem dBridge_emit (ev : IEvent P) (cfg : ReplayCfg P)
    (st : ReplayState P) :
    DBridge (InterpEffects.emit (P := P) (m := ReplayM P) ev) cfg st :=
  ⟨runBridge_emit .., by simp [replayRun_emit_state]⟩

omit [DecidableEq P.Ident] in
/-- `DBridge` holds for `choose`. -/
private theorem dBridge_choose (factory : InterpLang.RFactory P) (store : RStore P)
    (ty : P.Ty) (cfg : ReplayCfg P) (st : ReplayState P) :
    DBridge (InterpEffects.choose (P := P) factory store ty) cfg st :=
  ⟨runBridge_choose .., by simp only [replayRun, choose_traceRev_eq, List.suffix_rfl]⟩

omit [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- `DBridge` is closed under `>>=`, given the tail's `DBridge` after each `.ok` prefix. -/
private theorem dBridge_bind {α β : Type} (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : DBridge x cfg st)
    (hgon : ∀ a s, replayRun x cfg st = (.ok a, s) → DBridge (g a) cfg s)
    (hgoff : ∀ aO sO, replayRun x (interruptOff cfg) st = (.ok aO, sO) → DBridge (g aO) cfg sO) :
    DBridge (x >>= g) cfg st := by grind [runBridge_bind, replayRun_bind]

omit [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- `x >>= g` satisfies `DBridge` when `x` does and every `g a` does from every state. -/
private theorem dBridge_bind' {α β : Type} (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : DBridge x cfg st) (hg : ∀ a s, DBridge (g a) cfg s) :
    DBridge (x >>= g) cfg st := by apply dBridge_bind <;> intros <;> apply_assumption

omit [DecidableEq P.Ident] in
/-- `DBridge` holds for a `forM` of `emit`s. -/
private theorem dBridge_forM_emit (evs : List (IEvent P))
    (cfg : ReplayCfg P) (st : ReplayState P) :
    DBridge (evs.forM (InterpEffects.emit (P := P))) cfg st := by bridge_ind dBridge

/-- `DBridge` holds for `stepBaseCmdStore`. -/
private theorem dBridge_stepBaseCmdStore (fuel : Nat) (factory : InterpLang.RFactory P)
    (store : IStore P) (base : Cmd P)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    DBridge (stepBaseCmdStore (m := ReplayM P) fuel factory store base) cfg st := by
  bridge_ind dBridge

/-- `DBridge` (the stop hook only truncates the run) holds for `stepInterp` over a command stepper
    satisfying it. -/
theorem dBridge_stepInterp {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P),
        DBridge (stepCmd f e cmd) cfg st) :
    ∀ (n : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), DBridge (stepInterp stepCmd n c) cfg st := by bridge_ind dBridge

/-- `DBridge` (the stop hook only truncates the run) holds for `runInterp` over a command stepper
    satisfying it. -/
theorem dBridge_runInterp {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P),
        DBridge (stepCmd f e cmd) cfg st) :
    ∀ (fuel : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), DBridge (runInterp stepCmd fuel c) cfg st := by bridge_ind dBridge

/-- `DBridge` (the stop hook only truncates the run) holds for the callee body run `runCallee` over
    a command stepper satisfying it. -/
private theorem dBridge_runCallee (step : StepCmdM P (CmdExt P) (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdExt P) (cfg : ReplayCfg P) (st : ReplayState P),
        DBridge (step f e cmd) cfg st)
    (procName : String) (body : Body P (CmdExt P)) (fac : InterpLang.RFactory P) (n : Nat)
    (σ : RStore P) (cfg : ReplayCfg P) (st : ReplayState P) :
    DBridge (runCallee step procName body fac n σ) cfg st := by
  cases body
  · have hR := dBridge_runInterp step hstep
    unfold runCallee
    bridge_close dBridge
  · unfold runCallee
    bridge_close dBridge

/-- `DBridge` (the stop hook only truncates the run) holds for `stepCmd π`, for every callee table
    `π`. -/
theorem dBridge_stepCmd [HasFvar P] [HasOldIdent P]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    ∀ (k d : Nat) (env : IEnv P) (cmd : CmdExt P)
      (cfg : ReplayCfg P) (st : ReplayState P),
      DBridge (stepCmd π d k env cmd) cfg st := by bridge_ind dBridge

/-- The interrupt-on run of `runCallInterp π` matches its interrupt-off run (`DBridge`): the
    interrupt-on trace is a suffix of the interrupt-off trace, a non-throwing interrupt-on run
    coincides with the off-run, and the off-run only prepends to the initial trace. -/
theorem dBridge_runCallInterp [HasFvar P] [HasOldIdent P]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (fuel : Nat)
    (start : IConfig P (CmdExt P)) (d : Nat) (cfg : ReplayCfg P) (st : ReplayState P) :
    DBridge (runCallInterp (m := ReplayM P) π fuel start d) cfg st :=
  dBridge_runInterp _ (fun k => dBridge_stepCmd π k d) ..

/-- **Interrupt-on genuine ⟹ interrupt-off genuine**: if the interrupt-on run of
    `runCallInterp π` is `.genuine`, so is the run at `interruptOff cfg`, with the same `haltOn`
    and oracle. -/
theorem runReplay_genuine_of_interruptOn [HasFvar P] [HasOldIdent P]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (fuel : Nat)
    (start : IConfig P (CmdExt P)) (d : Nat) (cfg : ReplayCfg P)
    (haltOn : IEvent P → Bool)
    (oracle : List P.Expr)
    (h : (runReplay (runCallInterp (m := ReplayM P) π fuel start d) cfg haltOn oracle).1
        = .genuine) :
    (runReplay (runCallInterp (m := ReplayM P) π fuel start d)
        (interruptOff cfg) haltOn oracle).1 = .genuine := by
  rw [runReplay_genuine_iff] at *
  obtain ⟨⟨hsuf, -⟩, -⟩ := dBridge_runCallInterp π fuel start d cfg { remaining := oracle }
  exact h.imp fun _ ⟨hmem, hhalt⟩ => ⟨hsuf.subset hmem, hhalt⟩

/-! ### `FeasBridge`: a target-reaching production run has a path-feasible trace -/

/-- The outcome is `.ok`, or an `.interrupted` throw of the stop hook. -/
def OkOrInterrupt {α} (r : Except StopReason α) : Prop :=
  (∃ a, r = .ok a) ∨ (∃ s, r = .error (.interrupted s))

/-- Under `enforceInterrupt target fuel`, an `OkOrInterrupt` outcome keeps the trace `PathFeasible`.
    -/
def FeasBridge {α} (target : AssertId P) (fuel : Nat) (x : ReplayM P α)
    (cfg : ReplayCfg P) (st : ReplayState P) : Prop :=
  cfg.interruptOn = enforceInterrupt target fuel →
    ∀ r s', replayRun x cfg st = (r, s') →
      OkOrInterrupt r → PathFeasible fuel st.traceRev → PathFeasible fuel s'.traceRev

/-- `FeasBridge` holds for `pure`. -/
private theorem feasBridge_pure {α} (target : AssertId P) (fuel : Nat) (a : α)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    FeasBridge target fuel (pure a : ReplayM P α) cfg st := by
  rintro _ _ _ ⟨⟩ _
  exact id

/-- `FeasBridge` holds for `throw`. -/
private theorem feasBridge_throw {α} (target : AssertId P) (fuel : Nat) (rr : StopReason)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    FeasBridge target fuel (throw rr : ReplayM P α) cfg st := by
  rintro _ _ _ ⟨⟩ _
  exact id

/-- `FeasBridge` holds for `branch`, which throws in `ReplayM`. -/
private theorem feasBridge_branch (target : AssertId P) (fuel : Nat)
    (factory : InterpLang.RFactory P) (store : RStore P) (v : P.Expr)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    FeasBridge target fuel (InterpEffects.branch (P := P) (m := ReplayM P) factory store v)
      cfg st :=
  feasBridge_throw target fuel .expressionWasNotBoolean cfg st

/-- `FeasBridge` holds for `choose`, which leaves the trace unchanged. -/
private theorem feasBridge_choose (target : AssertId P) (fuel : Nat)
    (factory : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    FeasBridge target fuel (InterpEffects.choose (P := P) factory store ty) cfg st :=
  fun _ _ _ h _ hp => by rwa [← congrArg (·.2.traceRev) h, replayRun, choose_traceRev_eq]

/-- `FeasBridge` holds for `emit`. -/
private theorem feasBridge_emit (target : AssertId P) (fuel : Nat) (ev : IEvent P)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    FeasBridge target fuel (InterpEffects.emit (P := P) (m := ReplayM P) ev)
      cfg st := by
  intro hc r s h
  eff_inv [hc] <;> grind [enforceInterrupt, PathFeasible, OkOrInterrupt]

/-- `FeasBridge` is closed under `>>=`, given the tail's `FeasBridge` after each `.ok` prefix. -/
private theorem feasBridge_bind {α β} (target : AssertId P) (fuel : Nat)
    (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : FeasBridge target fuel x cfg st)
    (hg : ∀ a s, replayRun x cfg st = (.ok a, s) → FeasBridge target fuel (g a) cfg s) :
    FeasBridge target fuel (x >>= g) cfg st := by
  grind [FeasBridge, replayRun_bind, OkOrInterrupt]

/-- `x >>= g` satisfies `FeasBridge` when `x` does and every `g a` does from every state. -/
private theorem feasBridge_bind' {α β} (target : AssertId P) (fuel : Nat)
    (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : FeasBridge target fuel x cfg st)
    (hg : ∀ a s, FeasBridge target fuel (g a) cfg s) :
    FeasBridge target fuel (x >>= g) cfg st := feasBridge_bind _ _ _ _ _ _ hx fun a s _ => hg a s

/-- `FeasBridge` holds for a `forM` of `emit`s. -/
private theorem feasBridge_forM_emit (target : AssertId P) (fuel : Nat)
    (evs : List (IEvent P)) (cfg : ReplayCfg P) (st : ReplayState P) :
    FeasBridge target fuel (evs.forM (InterpEffects.emit (P := P))) cfg st := by
  bridge_ind feasBridge

/-- `FeasBridge` holds for `stepBaseCmdStore`. -/
private theorem feasBridge_stepBaseCmdStore (target : AssertId P) (fuel : Nat)
    (f : Nat)
    (factory : InterpLang.RFactory P) (store : IStore P) (base : Cmd P)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    FeasBridge target fuel (stepBaseCmdStore (m := ReplayM P) f factory store base) cfg st := by
  bridge_ind feasBridge

/-- `FeasBridge` (an `.ok` or interrupted run keeps the trace path-feasible) holds for `stepInterp`
    over a command stepper satisfying it. -/
theorem feasBridge_stepInterp {CmdT : Type} [CmdDefs P CmdT]
    (target : AssertId P) (fuel : Nat)
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P),
        FeasBridge target fuel (stepCmd f e cmd) cfg st) :
    ∀ (n : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), FeasBridge target fuel (stepInterp stepCmd n c) cfg st := by
  bridge_ind feasBridge

/-- `FeasBridge` (an `.ok` or interrupted run keeps the trace path-feasible) holds for `runInterp`
    over a command stepper satisfying it. -/
theorem feasBridge_runInterp {CmdT : Type} [CmdDefs P CmdT]
    (target : AssertId P) (fuel : Nat)
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P),
        FeasBridge target fuel (stepCmd f e cmd) cfg st) :
    ∀ (dfuel : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), FeasBridge target fuel (runInterp stepCmd dfuel c) cfg st := by
  bridge_ind feasBridge

/-- `FeasBridge` (an `.ok` or interrupted run keeps the trace path-feasible) holds for the callee
    body run `runCallee` over a command stepper satisfying it. -/
private theorem feasBridge_runCallee (target : AssertId P) (fuel : Nat)
    (step : StepCmdM P (CmdExt P) (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdExt P) (cfg : ReplayCfg P) (st : ReplayState P),
        FeasBridge target fuel (step f e cmd) cfg st)
    (procName : String) (body : Body P (CmdExt P)) (fac : InterpLang.RFactory P) (n : Nat)
    (σ : RStore P) (cfg : ReplayCfg P) (st : ReplayState P) :
    FeasBridge target fuel (runCallee step procName body fac n σ) cfg st := by
  cases body
  · have hR := feasBridge_runInterp target fuel step hstep
    unfold runCallee
    bridge_close feasBridge
  · unfold runCallee
    bridge_close feasBridge

/-- `FeasBridge` (an `.ok` or interrupted run keeps the trace path-feasible) holds for `stepCmd π`,
    for every callee table `π`. -/
theorem feasBridge_stepCmd [HasFvar P] [HasOldIdent P] (target : AssertId P)
    (fuel : Nat)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    ∀ (k d : Nat) (env : IEnv P) (cmd : CmdExt P)
      (cfg : ReplayCfg P) (st : ReplayState P),
      FeasBridge target fuel (stepCmd π d k env cmd) cfg st := by bridge_ind feasBridge

/-- `FeasBridge` (an `.ok` or interrupted run keeps the trace path-feasible) holds for
    `runCallInterp π`, for every callee table `π`. -/
theorem feasBridge_runCallInterp [HasFvar P] [HasOldIdent P]
    (target : AssertId P) (fuel : Nat)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (dfuel : Nat)
    (start : IConfig P (CmdExt P)) (d : Nat) (cfg : ReplayCfg P) (st : ReplayState P) :
    FeasBridge target fuel (runCallInterp (m := ReplayM P) π dfuel start d) cfg st := by
  apply feasBridge_runInterp
  exact fun k => feasBridge_stepCmd target fuel π k d

/-- A strict run of `runCallInterp π` under the enforcing stop hook `enforceInterrupt target fuel`
    that ends `.ok` or interrupted by the stop hook (`OkOrInterrupt`) has a path-feasible trace:
    every recorded `.assume` evaluates to `tt` (`PathFeasible`). -/
theorem pathFeasible_of_runReplayRun_enforce [HasFvar P] [HasOldIdent P]
    (target : AssertId P) (fuel : Nat)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (start : IConfig P (CmdExt P)) (d : Nat)
    (oracle : List P.Expr)
    (hok : OkOrInterrupt (runReplayRun (runCallInterp (m := ReplayM P) π fuel start d)
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel } oracle).1) :
    PathFeasible fuel (runReplayRun (runCallInterp (m := ReplayM P) π fuel start d)
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        oracle).2.traceRev :=
  feasBridge_runCallInterp _ _ _ _ _ _ _ _ rfl _ _ rfl hok nofun

/-! ### `StopBridge`: a target-reaching production run stops by `.interrupted` -/

/-- Under `enforceInterrupt target fuel`, a failing target occurrence in the final trace is
    already in the initial trace, or the outcome is `.interrupted`. -/
def StopBridge {α} (target : AssertId P) (fuel : Nat) (x : ReplayM P α)
    (cfg : ReplayCfg P) (st : ReplayState P) : Prop :=
  cfg.interruptOn = enforceInterrupt target fuel →
    ∀ r s', replayRun x cfg st = (r, s') →
      s'.traceRev.any (assertFailureHalt target fuel) = true →
        st.traceRev.any (assertFailureHalt target fuel) = true ∨ ∃ m, r = .error (.interrupted m)

/-- `enforceInterrupt` fires `.interrupted` on every `assertFailureHalt` event. -/
private theorem enforceInterrupt_of_assertFailureHalt (target : AssertId P) (fuel : Nat)
    (ev : IEvent P) (h : assertFailureHalt target fuel ev = true) :
    enforceInterrupt target fuel ev = some (.interrupted "target failure reached") := by
  cases ev <;> simp_all!

/-- `StopBridge` holds for `pure`. -/
private theorem stopBridge_pure {α} (target : AssertId P) (fuel : Nat) (a : α)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    StopBridge target fuel (pure a : ReplayM P α) cfg st := by
  rintro _ _ _ ⟨⟩ h
  exact .inl h

/-- `StopBridge` holds for `throw`. -/
private theorem stopBridge_throw {α} (target : AssertId P) (fuel : Nat) (rr : StopReason)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    StopBridge target fuel (throw rr : ReplayM P α) cfg st := by
  rintro _ _ _ ⟨⟩ h
  exact .inl h

/-- `StopBridge` holds for `branch`, which throws in `ReplayM`. -/
private theorem stopBridge_branch (target : AssertId P) (fuel : Nat)
    (factory : InterpLang.RFactory P) (store : RStore P) (v : P.Expr)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    StopBridge target fuel (InterpEffects.branch (P := P) (m := ReplayM P) factory store v)
      cfg st :=
  stopBridge_throw target fuel .expressionWasNotBoolean cfg st

/-- `StopBridge` holds for `choose`, which leaves the trace unchanged. -/
private theorem stopBridge_choose (target : AssertId P) (fuel : Nat)
    (factory : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    StopBridge target fuel (InterpEffects.choose (P := P) factory store ty) cfg st := by
  grind [StopBridge, choose_traceRev_eq, replayRun]

/-- `StopBridge` holds for `emit`. -/
private theorem stopBridge_emit (target : AssertId P) (fuel : Nat) (ev : IEvent P)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    StopBridge target fuel (InterpEffects.emit (P := P) (m := ReplayM P) ev)
      cfg st := by
  intro hc r s h
  eff_inv [hc] <;> grind [enforceInterrupt_of_assertFailureHalt]

/-- `StopBridge` is closed under `>>=`, given the tail's `StopBridge` after each `.ok` prefix. -/
private theorem stopBridge_bind {α β} (target : AssertId P) (fuel : Nat)
    (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : StopBridge target fuel x cfg st)
    (hg : ∀ a s, replayRun x cfg st = (.ok a, s) → StopBridge target fuel (g a) cfg s) :
    StopBridge target fuel (x >>= g) cfg st := by grind [StopBridge, replayRun_bind]

/-- `x >>= g` satisfies `StopBridge` when `x` does and every `g a` does from every state. -/
private theorem stopBridge_bind' {α β} (target : AssertId P) (fuel : Nat)
    (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : StopBridge target fuel x cfg st)
    (hg : ∀ a s, StopBridge target fuel (g a) cfg s) :
    StopBridge target fuel (x >>= g) cfg st := stopBridge_bind _ _ _ _ _ _ hx fun a s _ => hg a s

/-- `StopBridge` holds for a `forM` of `emit`s. -/
private theorem stopBridge_forM_emit (target : AssertId P) (fuel : Nat)
    (evs : List (IEvent P)) (cfg : ReplayCfg P) (st : ReplayState P) :
    StopBridge target fuel (evs.forM (InterpEffects.emit (P := P))) cfg st := by
  bridge_ind stopBridge

/-- `StopBridge` holds for `stepBaseCmdStore`. -/
private theorem stopBridge_stepBaseCmdStore (target : AssertId P) (fuel : Nat)
    (f : Nat)
    (factory : InterpLang.RFactory P) (store : IStore P) (base : Cmd P)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    StopBridge target fuel (stepBaseCmdStore (m := ReplayM P) f factory store base) cfg st := by
  bridge_ind stopBridge

/-- `StopBridge` (a newly recorded failing target event interrupts the run) holds for `stepInterp`
    over a command stepper satisfying it. -/
theorem stopBridge_stepInterp {CmdT : Type} [CmdDefs P CmdT]
    (target : AssertId P) (fuel : Nat)
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P),
        StopBridge target fuel (stepCmd f e cmd) cfg st) :
    ∀ (n : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), StopBridge target fuel (stepInterp stepCmd n c) cfg st := by
  bridge_ind stopBridge

/-- `StopBridge` (a newly recorded failing target event interrupts the run) holds for `runInterp`
    over a command stepper satisfying it. -/
theorem stopBridge_runInterp {CmdT : Type} [CmdDefs P CmdT]
    (target : AssertId P) (fuel : Nat)
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P),
        StopBridge target fuel (stepCmd f e cmd) cfg st) :
    ∀ (dfuel : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), StopBridge target fuel (runInterp stepCmd dfuel c) cfg st := by
  bridge_ind stopBridge

/-- `StopBridge` (a newly recorded failing target event interrupts the run) holds for the callee
    body run `runCallee` over a command stepper satisfying it. -/
private theorem stopBridge_runCallee (target : AssertId P) (fuel : Nat)
    (step : StepCmdM P (CmdExt P) (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdExt P) (cfg : ReplayCfg P) (st : ReplayState P),
        StopBridge target fuel (step f e cmd) cfg st)
    (procName : String) (body : Body P (CmdExt P)) (fac : InterpLang.RFactory P) (n : Nat)
    (σ : RStore P) (cfg : ReplayCfg P) (st : ReplayState P) :
    StopBridge target fuel (runCallee step procName body fac n σ) cfg st := by
  cases body
  · have hR := stopBridge_runInterp target fuel step hstep
    unfold runCallee
    bridge_close stopBridge
  · unfold runCallee
    bridge_close stopBridge

/-- `StopBridge` (a newly recorded failing target event interrupts the run) holds for `stepCmd π`,
    for every callee table `π`. -/
theorem stopBridge_stepCmd [HasFvar P] [HasOldIdent P] (target : AssertId P)
    (fuel : Nat)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    ∀ (k d : Nat) (env : IEnv P) (cmd : CmdExt P)
      (cfg : ReplayCfg P) (st : ReplayState P),
      StopBridge target fuel (stepCmd π d k env cmd) cfg st := by bridge_ind stopBridge

/-- `StopBridge` (a newly recorded failing target event interrupts the run) holds for
    `runCallInterp π`, for every callee table `π`. -/
theorem stopBridge_runCallInterp [HasFvar P] [HasOldIdent P]
    (target : AssertId P) (fuel : Nat)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (dfuel : Nat)
    (start : IConfig P (CmdExt P)) (d : Nat) (cfg : ReplayCfg P) (st : ReplayState P) :
    StopBridge target fuel (runCallInterp (m := ReplayM P) π dfuel start d) cfg st := by
  apply stopBridge_runInterp
  exact fun k => stopBridge_stepCmd target fuel π k d

/-! ### `CoBridge`: the production run coincides with the spec run until its stop hook fires -/

/-- The interrupt-on run of `x` equals its run with the stop hook off, or it throws the stop
    hook's reason at its last recorded event. -/
def CoBridge {α} (x : ReplayM P α) (cfg : ReplayCfg P)
    (st : ReplayState P) : Prop :=
  replayRun x cfg st = replayRun x (interruptOff cfg) st ∨
    ∃ r s' ev rest, replayRun x cfg st = (.error r, s') ∧ s'.traceRev = ev :: rest ∧
      cfg.interruptOn ev = some r

omit [DecidableEq P.Ident] in
/-- `CoBridge` holds for `pure`. -/
private theorem coBridge_pure {α} (a : α) (cfg : ReplayCfg P) (st : ReplayState P) :
    CoBridge (pure a : ReplayM P α) cfg st := .inl (obsReplay.run_pure ..)

omit [DecidableEq P.Ident] in
/-- `CoBridge` holds for `throw`. -/
private theorem coBridge_throw {α} (rr : StopReason) (cfg : ReplayCfg P)
    (st : ReplayState P) : CoBridge (throw rr : ReplayM P α) cfg st := .inl (obsReplay.run_throw ..)

omit [DecidableEq P.Ident] in
/-- `CoBridge` holds for `branch`, which throws in `ReplayM`. -/
private theorem coBridge_branch (factory : InterpLang.RFactory P) (store : RStore P) (v : P.Expr)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    CoBridge (InterpEffects.branch (P := P) (m := ReplayM P) factory store v) cfg st :=
  coBridge_throw .expressionWasNotBoolean cfg st

omit [DecidableEq P.Ident] in
/-- `CoBridge` holds for `choose`, which does not read `interruptOn`. -/
private theorem coBridge_choose (factory : InterpLang.RFactory P) (store : RStore P)
    (ty : P.Ty) (cfg : ReplayCfg P) (st : ReplayState P) :
    CoBridge (InterpEffects.choose (P := P) factory store ty) cfg st :=
  .inl (replayRun_choose_cfg_congr _ _ _ _ _ _ rfl)

omit [DecidableEq P.Ident] in
/-- `CoBridge` holds for `emit`. -/
private theorem coBridge_emit (ev : IEvent P) (cfg : ReplayCfg P)
    (st : ReplayState P) :
    CoBridge (InterpEffects.emit (P := P) (m := ReplayM P) ev) cfg st := by
  cases h : cfg.interruptOn ev <;>
    simp only [CoBridge, InterpEffects.emit, replayRun_modify_bind, replayRun_read_bind, h,
      replayRun_pure, replayRun_throw, interruptOff, Prod.mk.injEq, reduceCtorEq, false_and,
      exists_const, exists_false, or_false, and_true, Except.error.injEq, exists_and_left,
      exists_and_right, false_or] <;>
    grind

omit [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- `CoBridge` is closed under `>>=`, given the tail's `CoBridge` after each `.ok` prefix. -/
private theorem coBridge_bind {α β} (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : CoBridge x cfg st)
    (hg : ∀ a s, replayRun x cfg st = (.ok a, s) → CoBridge (g a) cfg s) :
    CoBridge (x >>= g) cfg st := by grind [CoBridge, replayRun_bind]

omit [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] in
/-- `x >>= g` satisfies `CoBridge` when `x` does and every `g a` does from every state. -/
private theorem coBridge_bind' {α β} (x : ReplayM P α) (g : α → ReplayM P β)
    (cfg : ReplayCfg P) (st : ReplayState P)
    (hx : CoBridge x cfg st) (hg : ∀ a s, CoBridge (g a) cfg s) :
    CoBridge (x >>= g) cfg st := coBridge_bind _ _ _ _ hx fun a s _ => hg a s

omit [DecidableEq P.Ident] in
/-- `CoBridge` holds for a `forM` of `emit`s. -/
private theorem coBridge_forM_emit
    (evs : List (IEvent P)) (cfg : ReplayCfg P) (st : ReplayState P) :
    CoBridge (evs.forM (InterpEffects.emit (P := P))) cfg st := by bridge_ind coBridge

/-- `CoBridge` holds for `stepBaseCmdStore`. -/
private theorem coBridge_stepBaseCmdStore (f : Nat)
    (factory : InterpLang.RFactory P) (store : IStore P) (base : Cmd P)
    (cfg : ReplayCfg P) (st : ReplayState P) :
    CoBridge (stepBaseCmdStore (m := ReplayM P) f factory store base) cfg st := by
  bridge_ind coBridge

/-- `CoBridge` (the stop hook can only stop the run at its last event) holds for `stepInterp` over a
    command stepper satisfying it. -/
theorem coBridge_stepInterp {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P),
        CoBridge (stepCmd f e cmd) cfg st) :
    ∀ (n : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), CoBridge (stepInterp stepCmd n c) cfg st := by bridge_ind coBridge

/-- `CoBridge` (the stop hook can only stop the run at its last event) holds for `runInterp` over a
    command stepper satisfying it. -/
theorem coBridge_runInterp {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdT)
        (cfg : ReplayCfg P) (st : ReplayState P),
        CoBridge (stepCmd f e cmd) cfg st) :
    ∀ (dfuel : Nat) (c : IConfig P CmdT) (cfg : ReplayCfg P)
      (st : ReplayState P), CoBridge (runInterp stepCmd dfuel c) cfg st := by bridge_ind coBridge

/-- `CoBridge` (the stop hook can only stop the run at its last event) holds for the callee body run
    `runCallee` over a command stepper satisfying it. -/
private theorem coBridge_runCallee (step : StepCmdM P (CmdExt P) (ReplayM P))
    (hstep : ∀ (f : Nat) (e : IEnv P) (cmd : CmdExt P) (cfg : ReplayCfg P) (st : ReplayState P),
        CoBridge (step f e cmd) cfg st)
    (procName : String) (body : Body P (CmdExt P)) (fac : InterpLang.RFactory P) (n : Nat)
    (σ : RStore P) (cfg : ReplayCfg P) (st : ReplayState P) :
    CoBridge (runCallee step procName body fac n σ) cfg st := by
  cases body
  · have hR := coBridge_runInterp step hstep
    unfold runCallee
    bridge_close coBridge
  · unfold runCallee
    bridge_close coBridge

/-- `CoBridge` (the stop hook can only stop the run at its last event) holds for `stepCmd π`, for
    every callee table `π`. -/
theorem coBridge_stepCmd [HasFvar P] [HasOldIdent P]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    ∀ (k d : Nat) (env : IEnv P) (cmd : CmdExt P)
      (cfg : ReplayCfg P) (st : ReplayState P),
      CoBridge (stepCmd π d k env cmd) cfg st := by bridge_ind coBridge

/-- `CoBridge` (the stop hook can only stop the run at its last event) holds for `runCallInterp π`,
    for every callee table `π`. -/
theorem coBridge_runCallInterp [HasFvar P] [HasOldIdent P]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (dfuel : Nat)
    (start : IConfig P (CmdExt P)) (d : Nat) (cfg : ReplayCfg P) (st : ReplayState P) :
    CoBridge (runCallInterp (m := ReplayM P) π dfuel start d) cfg st :=
  coBridge_runInterp _ (fun k => coBridge_stepCmd π k d) ..

/-- A `.genuine` strict verdict under the enforcing stop hook implies a path-feasible trace (every
    recorded `.assume` evaluates to `tt`), for any run satisfying `FeasBridge` and `StopBridge`. -/
private theorem pathFeasible_of_runReplay_genuine_enforce {CmdT : Type} (target : AssertId P)
    (fuel : Nat) (driver : ReplayM P (IConfig P CmdT))
    (oracle : List P.Expr)
    (hfb : FeasBridge target fuel driver
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        { remaining := oracle })
    (hsb : StopBridge target fuel driver
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        { remaining := oracle })
    (h : (runReplay driver { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        (assertFailureHalt target fuel) oracle).1 = .genuine) :
    PathFeasible fuel (runReplayRun driver
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        oracle).2.traceRev :=
  hfb rfl _ _ rfl
    (.inr ((hsb rfl _ _ rfl (List.any_eq_true.2 ((runReplay_genuine_iff ..).1 h))).resolve_left
      nofun)) nofun

/-- If the strict replay of `runCallInterp π` under the enforcing stop hook
    `enforceInterrupt target fuel` is `.genuine`, its trace is path-feasible: every recorded
    `.assume` evaluates to `tt` (`PathFeasible`). -/
theorem pathFeasible_of_runReplay_genuine_call [HasFvar P] [HasOldIdent P]
    (target : AssertId P) (fuel : Nat)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (start : IConfig P (CmdExt P)) (d : Nat)
    (oracle : List P.Expr)
    (h : (runReplay (runCallInterp (m := ReplayM P) π fuel start d)
        { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        (assertFailureHalt target fuel) oracle).1 = .genuine) :
    PathFeasible fuel (runReplayRun (runCallInterp (m := ReplayM P) π fuel start d)
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        oracle).2.traceRev :=
  pathFeasible_of_runReplay_genuine_enforce _ _ _ _ (feasBridge_runCallInterp _ _ _ _ _ _ _ _)
    (stopBridge_runCallInterp _ _ _ _ _ _ _ _) h

/-- If the record-only spec trace of `runCallInterp π` has the suffix `tgt :: pre`, with `pre`
    feasible and `tgt` an event failing the target (`assertFailureHalt target fuel`), the trace
    of the run under the enforcing stop hook is path-feasible: every recorded `.assume`
    evaluates to `tt` (`PathFeasible`). -/
theorem pathFeasible_enforce_of_spec_suffix [HasFvar P] [HasOldIdent P]
    (target : AssertId P) (fuel : Nat)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (start : IConfig P (CmdExt P)) (d : Nat)
    (oracle : List P.Expr) (tgt : IEvent P) (pre : List (IEvent P))
    (htgt : assertFailureHalt target fuel tgt = true) (hpre : PathFeasible fuel pre)
    (hsuf : (tgt :: pre) <:+ (runReplayRun (runCallInterp (m := ReplayM P) π fuel start d)
        { oracleConfig := .strict } oracle).2.traceRev) :
    PathFeasible fuel (runReplayRun (runCallInterp (m := ReplayM P) π fuel start d)
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        oracle).2.traceRev := by
  obtain ⟨⟨hon, -⟩, -⟩ := dBridge_runCallInterp π fuel start d
    { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel } { remaining := oracle }
  rcases List.suffix_or_suffix_of_suffix hon hsuf with hsub | hsub
  · exact pathFeasible_of_subset hsub.subset (pathFeasible_cons.2 ⟨fun _ hev => by simp_all!, hpre⟩)
  · exact pathFeasible_of_runReplay_genuine_call _ _ _ _ _ _
      ((runReplay_genuine_iff ..).2 ⟨tgt, hsub.mem (.head _), htgt⟩)

/-- A counterexample genuine under the enforcing production replay (`genuineEnforced`) is
    genuine under the record-only replay with a path-feasible production trace
    (`genuineFeasible`). -/
private theorem genuineFeasible_of_genuineEnforced [HasFvar P] [HasOldIdent P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P)) (d : Nat)
    (hg : genuineEnforced π target fuel cex d) : genuineFeasible π target fuel cex d :=
  ⟨runReplay_genuine_of_interruptOn _ _ _ _ _ _ _ hg,
    pathFeasible_of_runReplay_genuine_call _ _ _ _ _ _ hg⟩

/-- A firing `enforceInterrupt` is an `assertFailureHalt` event or an `.assume` not evaluating
    to `tt` up to metadata. -/
private theorem enforceInterrupt_some_cases (target : AssertId P) (fuel : Nat)
    (ev : IEvent P) (r : StopReason) (h : enforceInterrupt target fuel ev = some r) :
    assertFailureHalt target fuel ev = true ∨
      ∃ arg, ev = .assume arg ∧
        (InterpLang.boundedEval (P := P) fuel arg.factory arg.store arg.expr).bind
          InterpLang.boolLit? ≠ some true := by
  cases ev with
  | assume arg =>
    refine .inr ⟨arg, rfl, fun hb => ?_⟩
    simp only [enforceInterrupt] at h
    split at h <;> simp_all only [Option.bind_some, Option.bind_none, reduceCtorEq]
  | _ =>
    refine .inl ?_
    simp only [enforceInterrupt] at h
    split at h <;> simp_all only [reduceCtorEq]

/-- If the record-only replay of a run is `.genuine` and its trace under the enforcing stop hook is
    path-feasible (every recorded `.assume` evaluates to `tt`), the enforcing replay is `.genuine`
    too, for any run satisfying `CoBridge`. -/
private theorem runReplay_genuine_enforce_of_feasible {CmdT : Type} (target : AssertId P)
    (fuel : Nat) (driver : ReplayM P (IConfig P CmdT))
    (oracle : List P.Expr)
    (hC : CoBridge driver
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        { remaining := oracle })
    (hg : (runReplay driver { oracleConfig := .strict } (assertFailureHalt target fuel) oracle).1
        = .genuine)
    (hfeas : PathFeasible fuel (runReplayRun driver
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel } oracle).2.traceRev) :
    (runReplay driver { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        (assertFailureHalt target fuel) oracle).1 = .genuine := by
  rw [runReplay_genuine_iff] at *
  rcases hC with hrun | ⟨_, _, _, _, hrun, htrace, hfire⟩ <;>
    simp only [runReplayRun, replayRun, interruptOff] at *
  · rwa [hrun]
  grind [PathFeasible, enforceInterrupt_some_cases _ _ _ _ hfire]

/-- **`genuineFeasible ⟹ genuineEnforced`**: a counterexample genuine under the record-only replay
    with a path-feasible trace under the enforcing stop hook is genuine under the enforcing
    replay, with no uniqueness assumption on the target id. -/
private theorem genuineEnforced_of_genuineFeasible [HasFvar P] [HasOldIdent P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P)) (d : Nat)
    (h : genuineFeasible π target fuel cex d) : genuineEnforced π target fuel cex d :=
  runReplay_genuine_enforce_of_feasible _ _ _ _ (coBridge_runCallInterp ..) h.1 h.2

/-- The two feasibility-aware verdicts coincide on every counterexample: `genuineFeasible`
    (genuine under the record-only replay, with a path-feasible trace under the enforcing stop
    hook) holds exactly when `genuineEnforced` (genuine under the enforcing replay, which stops
    at the first failing target event or unsatisfied assumption) does. -/
theorem genuineFeasible_iff_genuineEnforced [HasFvar P] [HasOldIdent P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P)) (d : Nat) :
    genuineFeasible π target fuel cex d ↔ genuineEnforced π target fuel cex d :=
  ⟨genuineEnforced_of_genuineFeasible _ _ _ _ _, genuineFeasible_of_genuineEnforced _ _ _ _ _⟩

/-- If the record-only spec trace has the suffix `tgt :: pre`, with `pre` feasible and `tgt` a
    failing target occurrence, the production verdict is `.genuine`, for any run satisfying
    `DBridge` and `CoBridge`. -/
private theorem runReplay_genuine_enforce_of_spec_suffix {CmdT : Type} (target : AssertId P)
    (fuel : Nat) (driver : ReplayM P (IConfig P CmdT))
    (oracle : List P.Expr)
    (hDB : DBridge driver
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        { remaining := oracle })
    (hC : CoBridge driver
      { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        { remaining := oracle })
    (tgt : IEvent P) (pre : List (IEvent P))
    (htgt : assertFailureHalt target fuel tgt = true) (hpre : PathFeasible fuel pre)
    (hsuf : (tgt :: pre) <:+ (runReplayRun driver { oracleConfig := .strict } oracle).2.traceRev) :
    (runReplay driver { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        (assertFailureHalt target fuel) oracle).1 = .genuine := by
  rw [runReplay_genuine_iff]
  obtain ⟨⟨hon, -⟩, -⟩ := hDB
  have hsufs := List.suffix_or_suffix_of_suffix hon hsuf
  rcases hC with hrun | ⟨_, _, _, _, hrun, htrace, hfire⟩ <;>
    simp only [runReplayRun, replayRun, interruptOff] at *
  · exact hrun ▸ ⟨tgt, hsuf.mem (.head _), htgt⟩
  grind [PathFeasible, enforceInterrupt_some_cases _ _ _ _ hfire]

/-- **Completeness of the production verdict.**  If the record-only spec trace of
    `runCallInterp π` has the suffix `tgt :: pre` — a feasible prefix `pre` (every assume `tt`
    under `InterpLang.boundedEval (P := P) fuel`) followed by a failing target occurrence `tgt` —
    then `genuineEnforced` holds: the enforcing replay, which stops at the first failing target
    event or unsatisfied assumption, classifies the counterexample genuine.  `tgt` need not be
    the first occurrence of the target id. -/
theorem genuineEnforced_of_spec_suffix [HasFvar P] [HasOldIdent P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (cex : CexA P (CmdExt P)) (fuel : Nat) (d : Nat)
    (tgt : IEvent P) (pre : List (IEvent P))
    (htgt : assertFailureHalt target fuel tgt = true) (hpre : PathFeasible fuel pre)
    (hsuf : (tgt :: pre) <:+ (runReplayRun (runCallInterp (m := ReplayM P) π fuel
        cex.cfg d) { oracleConfig := .strict } cex.oracle).2.traceRev) :
    genuineEnforced π target fuel cex d :=
  runReplay_genuine_enforce_of_spec_suffix _ _ _ _ (dBridge_runCallInterp ..)
    (coBridge_runCallInterp ..) _ _ htgt hpre hsuf

end Calls

end -- public section

end Imperative
