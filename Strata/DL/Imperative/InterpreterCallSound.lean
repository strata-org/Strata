/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCallInterrupt
public import Strata.DL.Imperative.InterpreterViewSound
public import Strata.DL.Imperative.InterpreterSoundGeneric
public import Strata.DL.Imperative.InterpreterSound
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.StmtCFGCallSemantics
import Strata.DL.Imperative.InterpreterReplayTactics
public import Strata.DL.Imperative.InterpreterReplayProps
public import Strata.DL.Imperative.InterpreterCallProps
public import Strata.DL.Imperative.InterpreterSemanticsSpecProps
public import Strata.DL.Imperative.InterpreterCFGSound
public import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.DL.Imperative.CFGSemanticsProps
import all Strata.DL.Imperative.InterpreterCFG

/-! # Call-aware replay soundness against the reference event semantics

The engine's `.call` arm (`Calls.stepCmd`) computes its callee frame, its argument
values and its write-back with *executable* functions; the reference rule
`Calls.EvalCmdExtE.call_sem` states the same things *relationally*
(`EvalExpressions`, `ReadValues`, `InitCallFrame` / `CallEntry`, `UpdateStates` /
`CallExit`).  The bridges from each executable function to its relation are in
`InterpreterCallProps.lean`.  This module proves the per-step and whole-run soundness of the
call-aware driver `runCallInterp`, certifies the events of interrupted runs, and proves replay
soundness against `StepStmtExtStarE`, generically in the expression language `P`.  A callee
with a structured body runs as a statement run, a callee with a CFG body as a CFG run from its
entry block (`runCallee`), each sound against the corresponding `BigStepE` rule; the
evaluator facts the CFG run needs at the caller's factory come from `FactoryWF`.  The contract
run of an opaque callee (`runAbstractCallee`) is sound against the `HavocVars` and
`assumeEvents` premises of `EvalCmdExtE.call_abstract_sem` (`runAbstractCallee_sound`).

The success-path lemmas are instances, at `CmdExt.sem`, of the soundness of the call-aware
stepper over any command type (`InterpreterViewSound.lean`), which also holds `CallLangWF`,
`StrictActual`, `TypedActual` and `CallEnvOk`.

Key definitions:
* `ProcsOk π` (every procedure is well-formed) and `CfgInv π` (the configuration invariant):
  the side conditions of the soundness theorems;
* `EvalCommandET`: the reference call-aware command relation restricted to steps that keep a
  typed store typed;
* `CFGCfgInv`: the invariant of a CFG callee run;
* `InterruptedSound`: a certificate for the events of a run that may stop inside a call;
* `TargetNotInProcs π target`: the target assertion occurs in no procedure of `π`;
* `ReplaySound`, `ReplaySoundFeasible`: the replay-soundness statements.

Key theorems:
* `callStepInterpSound`, `call_cmd_arm`: per-step soundness of the call-aware stepper;
* `cfg_stepCmd_store_sound`: per-command soundness of `stepCmd π` with its result projected
  to the store;
* `call_runInterp_sound`, `call_replayRun_sound`: whole-run soundness of successful runs;
* `call_replayRun_interruptedSound`: the events of every replay run, throwing ones included,
  are certified by `InterruptedSound`;
* `interruptedSound_flatPrefix_of_targetReached`: under `TargetNotInProcs`, a certified event
  that reaches the target lies in a flat reference run;
* replay soundness: `call_replaySound_of_ok`, `call_replaySound_general`, `call_replaySound`,
  `call_replaySound_feasible`, `call_replaySound_interruptOn`.

Each bridge needs a side condition, because on that axis the relation demands
strictly more than the function checks:

* `EvalExpressions` carries `SemanticStore.varsDefined (· ∈ getFvars e) σ` per argument expression;
  `evalBoundedList` only requires the expression to reduce to a value.
* `ReadValues` requires each value read to be a value in the factory
  (`HasVal.value`); `readVarList` returns whatever the store holds.
* `InitCallFrame` is a fold of `InitState`, each step of which requires its target
  slot *unbound*; `bindPositional` overwrites blindly, so the callee's formal names
  must be pairwise distinct.
* `CallExit`'s `UpdateStates` is a fold of `UpdateState`, each step of which
  requires its target slot *already bound*; `bindPositional` does not check. -/

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp

public section

namespace Calls

variable {P : PureExpr} [HasBoolOps P] [HasFvar P] [HasFvars P]
  [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CallLangWF P]
  [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [ProcedureTypeInstantiation P Hdr]

/-- **Soundness of call-aware replay**: if the replay at call-depth limit `maxCallDepth` classifies
    the counterexample `genuine`, some run of the reference relation `StepStmtExtStarE π` from its
    configuration records an event failing the target assertion (`assertFailureHalt`). -/
@[expose] def ReplaySound (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (F : P.Factory) (cex : CexA P (CmdExt P))
    (maxCallDepth : Nat := defaultMaxCallDepth) : Prop :=
  genuine π target fuel cex maxCallDepth →
    ∃ (revs : List (IEvent P)) (final : Config P (CmdExt P)),
      StepStmtExtStarE π (cex.cfg.abs F) (revs.map (REvent.abs F)) final ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true

/-- **Feasibility-aware soundness**: if the replay classifies the counterexample
    `genuineEnforced` (genuine, with every assumption on the path enforced), some reference run
    from its configuration records an event failing the target assertion, and every `.assume`
    event it records evaluates to `tt` (`PathFeasible`). -/
@[expose] def ReplaySoundFeasible (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (F : P.Factory) (cex : CexA P (CmdExt P))
    (maxCallDepth : Nat := defaultMaxCallDepth) : Prop :=
  genuineEnforced π target fuel cex maxCallDepth →
    ∃ (revs : List (IEvent P)) (final : Config P (CmdExt P)),
      StepStmtExtStarE π (cex.cfg.abs F) (revs.map (REvent.abs F)) final ∧
      (∃ ev ∈ revs, assertFailureHalt target fuel ev = true) ∧
      PathFeasible fuel revs

/-! ## The flat side conditions: per command, per procedure, per program

`CmdCallOk` (one command), `ProcOk` (one procedure), `ProcsOk` (every procedure of `π`), and the
configuration invariant `CfgInv` the `.call` step obligation runs under. -/

/-- Per-command check on a call site: its input actuals are all `StrictActual` and all
    `TypedActual` (the latter keeps the callee frame typed, see `CallLangWF`), and its result
    variables are distinct (as the call rule's write-back `CallExit` requires).  Base commands
    carry no condition.  The output arity (`|getLhs args| = |outputs.keys|`) is not part of the
    check: the engine checks it itself and throws `programCallOutputArityMismatch`, a throw
    certified sound. -/
@[expose] def CmdCallOk (_π : String → Option (Procedure P (CmdExt P) Hdr)) : CmdExt P → Bool
  | .cmd _ => true
  | .call _ _ args _ =>
    (getInputExprs args).all StrictActual && (getInputExprs args).all TypedActual &&
      decide (CallArg.getLhs args).Nodup

/-- Shallow check on one procedure, mentioning no calls: its frame-binding formals
    are pairwise distinct (what `InitCallFrame` needs), a structured body is
    exit-covered and has well-formed call sites everywhere, and every command of every
    block of a CFG body is a well-formed call site. -/
@[expose] def ProcOk (π : String → Option (Procedure P (CmdExt P) Hdr))
    (p : Procedure P (CmdExt P) Hdr) : Prop :=
  (ProcedureHeader.inputParams (P := P) p.header ++ outputOnlyParams (P := P) p.header).Nodup ∧
  (∀ ss opq, p.body = .structured ss opq →
    Block.exitsCoveredByBlocks (P := P) (CmdT := CmdExt P) [] ss ∧
    Block.allCmds (P := P) (CmdCallOk π) ss = true) ∧
  ∀ g opq, p.body = .cfg g opq → g.allCmds (CmdCallOk π)

/-- Flat program-level check: every procedure a call can run, `π`'s procedure instantiated at
    the call's type arguments (`typeInstantiatedCallee`), satisfies `ProcOk`.
    No recursion: `ProcOk` says nothing about the *callees* of the calls inside a
    body, only that each such call site is locally well-formed. -/
@[expose] def ProcsOk (π : String → Option (Procedure P (CmdExt P) Hdr)) : Prop :=
  ∀ n tyArgs p, typeInstantiatedCallee π n tyArgs = some p → ProcOk π p

/-- The configuration invariant call-aware replay soundness runs under: a value-only store
    (`Config.storeWellDefined`), well-formed call sites everywhere (`CmdCallOk π`), and typed
    stores (`Config.storeTyped`).

    Exit coverage is deliberately *not* a conjunct.  It is the one condition whose
    label list grows when execution descends into a labeled block, so it does not
    project from a `.block` configuration into its inner one and cannot be part of a
    fixed configuration invariant.  A `.call` step needs it only to know the callee
    body's run did not end `.exiting`, and there it is transported along that run's
    own reference derivation. -/
@[expose] def CfgInv (π : String → Option (Procedure P (CmdExt P) Hdr))
    (c : Config P (CmdExt P)) : Prop :=
  Config.storeWellDefined (P := P) c ∧
  Config.allCmds (P := P) (CmdCallOk π) c ∧
  Config.storeTyped (P := P) c

/-- The call-aware reference command relation restricted to steps that keep a typed
    store typed.  The engine's soundness argument runs against this relation, so
    that `Config.storeTyped` transports along the reference steps it builds: the
    reference `call_sem` writes back values `ReadValues` only knows to be values,
    while the engine's own callee run shows they are typed.  Every derivation of it
    is a derivation of `EvalCmdExtE`. -/
@[expose] def EvalCommandET (π : String → Option (Procedure P (CmdExt P) Hdr))
    : EvalCmdParamE P (CmdExt P) (Event P) :=
  fun f σ c σ' evs => EvalCmdExtE π f σ c σ' evs ∧ (StoreTyped f σ → StoreTyped f σ')

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- A run of the typed-step relation is a run of `EvalCmdExtE`. -/
private theorem stepStarET_toE (π : String → Option (Procedure P (CmdExt P) Hdr))
    {c c' : Config P (CmdExt P)} {evs : Trace P}
    (h : StepStmtStarE P (EvalCommandET π) c evs c') :
    StepStmtStarE P (EvalCmdExtE π) c evs c' := h.imp fun _ _ _ _ _ => And.left

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- A step of the typed-step relation is a step of `EvalCmdExtE`. -/
theorem stepET_toE (π : String → Option (Procedure P (CmdExt P) Hdr))
    {c c' : Config P (CmdExt P)} {evs : Trace P}
    (h : StepStmtE P (EvalCommandET π) c evs c') :
    StepStmtE P (EvalCmdExtE π) c evs c' := h.imp fun _ _ _ _ _ => And.left

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- A reference call-aware command evaluation (`EvalCmdExtE`) defines only the binder of an
    `init`: a call's write-back (`CallExit`) updates already defined slots only. -/
theorem evalCmdExtE_cmdDefsSound (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    CmdDefsSound (EvalCmdExtE π) := by
  intro _ _ _ _ _ h x hx
  cases h with
  | cmd_sem h => exact evalCmdE_cmdDefsSound _ _ _ _ _ h x hx
  | call_sem _ _ _ _ hexit =>
    obtain ⟨_, _, _, hup, -⟩ := hexit
    exact .inl (UpdateStatesDefMonotone' (vs := [x]) (fun _ hv => List.mem_singleton.1 hv ▸ hx)
      hup x (List.mem_singleton_self x))
  | call_abstract_sem _ _ _ _ hexit =>
    obtain ⟨_, _, _, hup, -⟩ := hexit
    exact .inl (UpdateStatesDefMonotone' (vs := [x]) (fun _ hv => List.mem_singleton.1 hv ▸ hx)
      hup x (List.mem_singleton_self x))

/-! ## The `CmdExt` instance of the generic soundness chain

`CmdCallOk`, `ProcOk`, `CfgInv`, `CFGCfgInv` and `EvalCommandET` are the generic `CmdOk`,
`ProcOkV`, `CfgInvV`, `CFGCfgInvV` and `EvalCommandVT` (`InterpreterViewSound.lean`) at
`CmdExt.sem` (`cmdCallOk_eq`, `procOk_iff`, `cfgInv_eq`, `cfgCfgInv_eq`, `evalCommandVT_of_ET`,
`evalCommandET_of_VT`), and `CmdExt.view` agrees with `CmdExt.sem` (`cmdExt_viewSound`). The
soundness lemmas of this section are instances of the generic ones. -/

omit [DecidableEq P.Expr] in
/-- A reference command step leaves a value-only store (a call's write-back writes exactly
    the values `ReadValues` read out of the callee's final store). -/
private theorem evalCommandE_wellFormedStore
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : CmdExt P} {emitted : Trace P}
    (h : EvalCmdExtE π fac σ c σ' emitted) (hsv : WellFormedStore σ fac) :
    WellFormedStore σ' fac := by
  cases h <;> grind [CallExit, wellFormedStore_updateStates, readValues_values,
      evalCmdE_storeWellDefined (P := P), CallLangWF.evalVal]

/-! ## The CFG body invariant

A CFG callee body runs from its entry block at the caller's factory; the run carries a
well-formed, typed store (`CallEnvOk`) and the well-formed call sites of its blocks. -/

/-- Static well-formedness of a residual command list: every command is `CmdCallOk`. -/
@[expose] def resOk (π : String → Option (Procedure P (CmdExt P) Hdr))
    (cs : List (CmdExt P)) : Prop :=
  ∀ c ∈ cs, CmdCallOk π c = true

/-- The CFG configuration invariant the call-aware CFG soundness runs under, at the factory
    `fac`: the store facts (`CallEnvOk`) hold at the running store, every command of every block
    of the configuration's CFG is `CmdCallOk` (`CFG.allCmds`), (mid-block) the residual commands
    are all `CmdCallOk`, and the environment's factory is `fac`. -/
@[expose] def CFGCfgInv {l : Type} [BEq l] (π : String → Option (Procedure P (CmdExt P) Hdr))
    (fac : P.Factory) : CFGConfig l (CmdExt P) P → Prop
  | .atBlock g _ ρ => CallEnvOk fac ρ.store ∧ g.allCmds (CmdCallOk π) ∧ ρ.factory = fac
  | .inBlock g _ cs _ ρ =>
    CallEnvOk fac ρ.store ∧ resOk π cs ∧ g.allCmds (CmdCallOk π) ∧ ρ.factory = fac
  | .terminal ρ => CallEnvOk fac ρ.store ∧ ρ.factory = fac

omit [DecidableEq P.Expr] [HasOldIdent P] [ProcedureHeader P Hdr] in
/-- `CmdCallOk` is `CmdOk` at `CmdExt.sem`. -/
theorem cmdCallOk_eq (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    CmdCallOk π = CmdOk (Calls.CmdExt.sem (Hdr := Hdr)) := by
  funext c
  cases c <;> rfl

omit [DecidableEq P.Expr] [HasOldIdent P] [ProcedureHeader P Hdr] in
/-- `CfgInv` is `CfgInvV` at `CmdExt.sem`. -/
theorem cfgInv_eq (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    CfgInv π = CfgInvV (Calls.CmdExt.sem (Hdr := Hdr)) := by
  funext c
  simp only [CfgInv, CfgInvV, cmdCallOk_eq]

omit [DecidableEq P.Expr] [HasOldIdent P] [ProcedureHeader P Hdr] in
/-- `CFGCfgInv` is `CFGCfgInvV` at `CmdExt.sem`. -/
theorem cfgCfgInv_eq {l : Type} [BEq l] (π : String → Option (Procedure P (CmdExt P) Hdr))
    (fac : P.Factory) :
    CFGCfgInv (l := l) π fac = CFGCfgInvV (Calls.CmdExt.sem (Hdr := Hdr)) fac := by
  funext c
  cases c <;> simp only [CFGCfgInv, CFGCfgInvV, resOk, cmdCallOk_eq]

omit [DecidableEq P.Expr] [HasOldIdent P] in
/-- `ProcOk` is `ProcOkV` at `CmdExt.sem`. -/
theorem procOk_iff (π : String → Option (Procedure P (CmdExt P) Hdr))
    (p : Procedure P (CmdExt P) Hdr) : ProcOk π p ↔ ProcOkV (Calls.CmdExt.sem (Hdr := Hdr)) p := by
  simp only [ProcOk, ProcOkV, cmdCallOk_eq]

omit [DecidableEq P.Expr] [HasOldIdent P] in
/-- `ProcsOk` gives `ProcsOkV` at `CmdExt.sem`: a procedure a `CmdExt` call can run is its
    callee instantiated at its type arguments, and no `CmdExt` command is an extension command. -/
theorem procsOkV_of_procsOk (π : String → Option (Procedure P (CmdExt P) Hdr)) (h : ProcsOk π) :
    ProcsOkV (Calls.CmdExt.sem (Hdr := Hdr)) π := by
  rintro p ⟨n, p₀, inst, hπ, hinst, ⟨c, args, md, hk⟩ | ⟨_, _, _, _, _, _, _, hx⟩⟩
  · obtain ⟨tyArgs, -, hcallee⟩ := Calls.CmdExt.sem_kind_call_callee hk hπ hinst
    exact (procOk_iff π p).1 (h n tyArgs p hcallee)
  · exact hx.elim

omit [DecidableEq P.Expr] in
/-- A step of `EvalCommandET` is a step of `EvalCommandVT` at `CmdExt.sem`. -/
theorem evalCommandVT_of_ET {π : String → Option (Procedure P (CmdExt P) Hdr)} {f : P.Factory}
    {σ σ' : SemanticStore P} {c : CmdExt P} {evs : Trace P}
    (h : EvalCommandET π f σ c σ' evs) :
    EvalCommandVT (Calls.CmdExt.sem (Hdr := Hdr)) π f σ c σ' evs :=
  ⟨h.1, evalCommandE_wellFormedStore π h.1, h.2,
    evalCmdExtE_cmdDefsSound π _ _ _ _ _ h.1⟩

omit [DecidableEq P.Expr] [InterpLang P] [CallLangWF P] in
/-- A step of `EvalCommandVT` at `CmdExt.sem` is a step of `EvalCommandET`. -/
theorem evalCommandET_of_VT {π : String → Option (Procedure P (CmdExt P) Hdr)} {f : P.Factory}
    {σ σ' : SemanticStore P} {c : CmdExt P} {evs : Trace P}
    (h : EvalCommandVT (Calls.CmdExt.sem (Hdr := Hdr)) π f σ c σ' evs) :
    EvalCommandET π f σ c σ' evs :=
  ⟨h.1, h.2.2.1⟩

omit [DecidableEq P.Expr] in
/-- The CFG invariant `CFGCfgInv` (well-formed, typed running store; well-formed call sites in
    every block command and every residual command) is preserved by one event-trace CFG
    reference step whose commands follow the typed call-aware command relation
    `EvalCommandET π`. -/
theorem cfgCfgInv_stepE {l : Type} [BEq l]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (fac : P.Factory)
    {a : CFGConfig l (CmdExt P) P} {emitted : Trace P} {b : CFGConfig l (CmdExt P) P}
    (h : StepCFGE P (EvalCommandET π) a emitted b)
    (hinv : CFGCfgInv π fac a) : CFGCfgInv π fac b := by
  rw [cfgCfgInv_eq] at hinv ⊢
  exact cfgCfgInvV_stepE _ π fac (StepCFGE.imp (fun _ _ _ _ _ => evalCommandVT_of_ET) h) hinv

/-! ## The call-aware per-step obligation -/

section CallArm

variable {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m]
  [MonadExcept StopReason m]

omit [LawfulMonad m] in
omit [DecidableEq P.Expr] [HasOldIdent P] [ProcedureHeader P Hdr] in
/-- `CfgInv` projects into the inner configuration of a `.seq`. -/
private theorem cfgInv_seq (π : String → Option (Procedure P (CmdExt P) Hdr))
    (inner : Config P (CmdExt P)) (ss : List (Stmt P (CmdExt P)))
    (h : CfgInv π (.seq inner ss)) : CfgInv π inner := by
  rw [cfgInv_eq] at h ⊢
  exact cfgInvV_seq _ inner ss h

omit [LawfulMonad m] in
omit [DecidableEq P.Expr] [HasOldIdent P] [ProcedureHeader P Hdr] in
/-- `CfgInv` projects into the inner configuration of a `.block`. -/
private theorem cfgInv_block (π : String → Option (Procedure P (CmdExt P) Hdr))
    (l : Option String) (σ : SemanticStore P) (inner : Config P (CmdExt P))
    (h : CfgInv π (.block l σ inner)) : CfgInv π inner := by
  rw [cfgInv_eq] at h ⊢
  exact cfgInvV_block _ l σ inner h

omit [LawfulMonad m] in
omit [DecidableEq P.Expr] in
/-- A `.call` whose marshalling succeeded, from a configuration with a well-formed factory
    (`FactoryWF`) satisfying `CfgInv π`, satisfies `CallEntry`, and its entry frame is a
    well-formed, typed store (`CallEnvOk`). -/
private theorem callEntry_ok (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    {n : String} {args : List (CallArg P)} {md : MetaData P} {F : P.Factory} {env : IEnv P}
    {tyArgs : Option (List P.Ty)}
    {p : Procedure P (CmdExt P) Hdr} {k : Nat} {i o : List P.Expr}
    (hEval : BoundedEvalSoundAt P F)
    (hfac : FactoryWF (P := P) F) (hden : RStore.Denoting F env.store.get)
    (hrf : env.factory = InterpLang.rfactory F)
    (hinv : CfgInv π (.stmt (.cmd (CmdExt.call n tyArgs args md)) (env.abs F)))
    (hπ : typeInstantiatedCallee π n tyArgs = some p)
    (hi : evalBoundedList k env.factory env.store.get (getInputExprs args) = some i)
    (hil : ¬i.length ≠ (ProcedureHeader.inputParams (P := P) p.header).length)
    (ho : readVarList env.store.get (CallArg.getOutArgs args) = some o)
    (hol : ¬o.length ≠ (outputOnlyParams (P := P) p.header).length) :
    ∃ vi vo, List.Rel₂ (InterpLang.Denotes F) i vi ∧ List.Rel₂ (InterpLang.Denotes F) o vo ∧
    CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo) ∧
    CallEnvOk F (callEntryStore p vi vo) ∧ RStore.Denoting F (callEntryStore p i o) ∧
    InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo := by
  obtain ⟨hstore, hall, htyped⟩ := hinv
  have hargs : ArgsOk args = true := by
    simpa [Config.allCmds, Stmt.allCmds, CmdCallOk, ArgsOk] using hall
  exact callEntry_okV hEval hfac hden hrf ⟨hstore, htyped⟩ hargs (hprocs n _ p hπ).1 hi hil ho hol

omit [LawfulMonad m] in
omit [HasOldIdent P] [ProcedureHeader P Hdr] in
/-- `CmdExt.view` agrees with `CmdExt.sem`; it has no extension command. -/
theorem cmdExt_viewSound (obs : InterpObs P m) :
    ViewSound obs (CmdExt.view (Hdr := Hdr) (m := m)) (Calls.CmdExt.sem (Hdr := Hdr)) where
  base c b h := by
    cases c <;> simp only [CmdExt.view, CmdView.base.injEq, reduceCtorEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  call c n args md inst h := by
    cases c <;> simp only [CmdExt.view, CmdView.call.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  ext_kind c run h := absurd h (CmdExt.view_ne_ext c run)
  ext _ _ c run _ _ _ _ _ h := absurd h (CmdExt.view_ne_ext c run)

omit [LawfulMonad m] in
/-- A `CmdExt` command arm in the form of this file is `ArmSound` at `CmdExt.sem`. -/
private theorem armSound_of_cmdExt {obs : InterpObs P m} {step : StepCmdM P (CmdExt P) m}
    {π : String → Option (Procedure P (CmdExt P) Hdr)} {F : P.Factory}
    (IH : ∀ (fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (step fuel env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F) :
    ArmSound obs step (Calls.CmdExt.sem (Hdr := Hdr)) π F := by
  intro fuel cmd env cfg' cfgr st st' h hf hd hr hi
  rw [← cfgInv_eq] at hi
  obtain ⟨revs, hs, ht, hd'⟩ := IH fuel cmd env cfg' cfgr st st' h hf hd hr hi
  exact ⟨revs, StepStmtE.imp (fun _ _ _ _ _ => evalCommandVT_of_ET) hs, ht, hd'⟩

omit [LawfulMonad m] in
omit [CallLangWF P] in
/-- `StepInterpSoundGeneric` over `EvalCommandVT` at `CmdExt.sem` gives it over
    `EvalCommandET`. -/
private theorem stepInterpSound_toET {obs : InterpObs P m} {step : StepCmdM P (CmdExt P) m}
    {π : String → Option (Procedure P (CmdExt P) Hdr)} {Inv : Config P (CmdExt P) → Prop}
    (h : StepInterpSoundGeneric obs step (EvalCommandVT (Calls.CmdExt.sem (Hdr := Hdr)) π) Inv) :
    StepInterpSoundGeneric obs step (EvalCommandET π) Inv :=
  fun F fuel cfg cfg' cfgr st st' hr ht he hf hE hd hi htr =>
    let ⟨⟨revs, hs, htr'⟩, hd', hi', htr''⟩ :=
      h F fuel cfg cfg' cfgr st st' hr ht he hf hE hd hi htr
    ⟨⟨revs, StepStmtE.imp (fun _ _ _ _ _ => evalCommandET_of_VT) hs, htr'⟩, hd', hi', htr''⟩

omit [LawfulMonad m] in
/-- **Per-step soundness of the call-aware engine at one factory.** As `callStepSound_of_arm`, for
    a command arm `harm` known at the single factory `F₀` only: the carried invariant adds that the
    configuration's factory is `F₀` (which every reference step keeps). It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem callStepSound_at [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (d : Nat) (kf : Nat → Nat) {F₀ : P.Factory}
    (harm : ∀ (fuel : Nat) (cmd : CmdExt P) (env : IEnv P)
        (cfg' : IConfig P (CmdExt P)) (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π .contract d (kf fuel) env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F₀ → RStore.Denoting F₀ env.store.get →
        env.factory = InterpLang.rfactory F₀ → CfgInv π (.stmt (.cmd cmd) (env.abs F₀)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F₀)) (revs.map (REvent.abs F₀)) (cfg'.abs F₀)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F₀) :
    StepInterpSoundGeneric obs (fun fuel e c => stepCmd π .contract d (kf fuel) e c)
      (EvalCommandET π) (fun c => CfgInv π c ∧ c.getEnv.factory = F₀) := by
  rw [cfgInv_eq]
  exact stepInterpSound_toET
    (stepSoundV_at obs (Calls.CmdExt.sem (Hdr := Hdr)) π _ (armSound_of_cmdExt harm))

omit [LawfulMonad m] in
/-- Assume every procedure of `π` is well-formed (`ProcsOk π`), and every successful command step
    `stepCmd π .contract d k` from a configuration with a well-formed factory (`FactoryWF`)
    satisfying the invariant `CfgInv π` (the replay invariant on the stores and the call sites) is
    one reference
    `EvalCommandET π` step recording its events. Then a successful callee-body run of `runInterp` at
    call-depth budget `d` and stepper fuel `k` from a configuration `.stmt (.block "" ss #[]) E`
    satisfying `CfgInv π`, with `E.factory` well-formed, for the structured body `ss` of a procedure
    `π` resolves, ends in a `.terminal` configuration carrying the caller's factory `E.factory`
    whose abstraction (`IConfig.abs`) satisfies `CfgInv π` and is reached by a reference
    `StepStmtStarE` run over `EvalCmdExtE π` that records exactly the run's events. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem callee_run_ok [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    {n : String} {p : Procedure P (CmdExt P) Hdr} {ss : List (Stmt P (CmdExt P))} {k d : Nat}
    {E : IEnv P} {fc : IConfig P (CmdExt P)} {cfgr : obs.Cfg} {st st' : obs.St}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π .contract d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    {tyArgs : Option (List P.Ty)} (hπ : typeInstantiatedCallee π n tyArgs = some p)
    (hb : p.body = .structured ss opq)
    (hI : CfgInv π (.stmt (.block "" ss #[]) (E.abs F))) (hfE : FactoryWF (P := P) F)
    (hdE : RStore.Denoting F E.store.get) (hrE : E.factory = InterpLang.rfactory F)
    (h : obs.run (runInterp (fun _ e c => stepCmd π .contract d k e c) k (.stmt (.block "" ss #[])
        E)) cfgr st
        = (.ok fc, st')) :
    ∃ σ', fc = .terminal ⟨σ', E.factory⟩ ∧ fc.Denoting F ∧ CfgInv π (fc.abs F) ∧
      ∃ revs : List (IEvent P), StepStmtStarE P (EvalCmdExtE π)
        (.stmt (.block "" ss #[]) (E.abs F)) (revs.map (REvent.abs F)) (fc.abs F) ∧
          obs.trace st' = revs.reverse ++ obs.trace st := by
  rw [cfgInv_eq] at hI ⊢
  obtain ⟨σ', h1, h2, h3, revs, R, htr⟩ :=
    callee_run_okV obs (Calls.CmdExt.sem (Hdr := Hdr)) π hEval _ (k := k)
    (armSound_of_cmdExt IH) ((procOk_iff π p).1 (hprocs n tyArgs p hπ)) hb hI hfE hdE hrE h
  exact ⟨σ', h1, h2, h3, revs, ReflTransTrace.imp (fun _ _ _ hs =>
    StepStmtE.imp (fun _ _ _ _ _ hv => hv.1) hs) R, htr⟩

omit [LawfulMonad m] in
/-- A successful step `stepCmd π .contract d k` of a command with well-formed call sites
    (`CmdCallOk`), projected to its store, from a well-formed, typed store (`CallEnvOk`) at a
    well-formed factory (`FactoryWF`), is a step of `EvalCommandET π` recording exactly its events,
    and the resulting store is again well-formed and typed, given that every successful step
    `stepCmd π .contract d k` from a configuration with a well-formed factory satisfying `CfgInv π`
    is one reference step over `EvalCommandET π` recording its events (`IH`). -/
private theorem store_sound_of_arm (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) {k d : Nat}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π .contract d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    {σ σ' : IStore P} {cmd : CmdExt P}
    {cfgr : obs.Cfg} {st st' : obs.St}
    (hfac : FactoryWF (P := P) F) (hok : CmdCallOk π cmd = true) (hd : RStore.Denoting F σ.get)
    (henv : CallEnvOk F (InterpLang.absStore F σ.get))
    (h : obs.run (StepCmdM.toStore (stepCmd π .contract d) k (InterpLang.rfactory F) σ cmd) cfgr st
        =
        (.ok σ', st')) :
    ∃ revs : List (IEvent P), EvalCommandET π F (InterpLang.absStore F σ.get) cmd
        (InterpLang.absStore F σ'.get) (revs.map (REvent.abs F)) ∧
      CallEnvOk F (InterpLang.absStore F σ'.get) ∧ RStore.Denoting F σ'.get
      ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨revs, hev, henv', hd', ht⟩ := store_sound_of_armV obs (Calls.CmdExt.sem (Hdr := Hdr)) π
    (fun _ e c => stepCmd π .contract d k e c) (k := k) (armSound_of_cmdExt IH) hfac
    (by rw [← cmdCallOk_eq]; exact hok) hd henv h
  exact ⟨revs, evalCommandET_of_VT hev, henv', hd', ht⟩

omit [LawfulMonad m] in
/-- The command obligation of the CFG soundness theorems (`stepInterpCFG_soundE`,
    `runInterpCFG_soundE`) for the store-stepper of `stepCmd π .contract d` at fuel `k`, under the
    CFG invariant `CFGCfgInv π F` at a well-formed factory `F`: a successful step on the next
    command of a block, from a store that denotes at `F`, is a step of `EvalCommandET π` recording
    exactly its events, to a store that denotes at `F`, given that every successful step
    `stepCmd π .contract d k` from a configuration with a well-formed factory satisfying `CfgInv π`
    is one reference step over `EvalCommandET π` recording its events (`IH`). -/
private theorem cfgCmd_sound_of_arm (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) {k d : Nat}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π .contract d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    (hfac : FactoryWF (P := P) F) :
    ∀ (_ : Nat) (g : DetCFG P (CmdExt P)) t c cs tr (ρ : IEnv P) σ' cfgr st st',
      RStore.Denoting F ρ.store.get → ρ.factory = InterpLang.rfactory F →
      CFGCfgInv π F (.inBlock g t (c :: cs) tr (ρ.abs F)) →
      obs.run (StepCmdM.toStore (stepCmd π .contract d) k ρ.factory ρ.store c) cfgr st = (.ok σ',
          st') →
      ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
        ∧ EvalCommandET π F (InterpLang.absStore F ρ.store.get) c (InterpLang.absStore F σ'.get)
          (revs.map (REvent.abs F))
        ∧ RStore.Denoting F σ'.get :=
  fun _ _ _ _ _ _ _ _ _ _ _ hdρ hrf ⟨he, hr, _, _⟩ hc =>
    (store_sound_of_arm obs π IH hfac (hr _ (.head _)) hdρ he (hrf ▸ hc)).imp
      fun _ ⟨hev, _, hd', ht⟩ => ⟨ht, hev, hd'⟩


omit [LawfulMonad m] in
/-- A successful `runInterpCFG` run over the store-stepper of `stepCmd π .contract d` at fuel `k`,
    from a configuration that denotes at a well-formed factory `F` and whose image satisfies the CFG
    invariant `CFGCfgInv π F`, is a CFG reference run over `EvalCommandET π` between the images,
    recording exactly the run's events, to a configuration that denotes at `F`.  It assumes `IH`
    (as `cfgCmd_sound_of_arm`), that at `F` every value the bounded evaluator commits to denotes
    the reference evaluator's value, and that the Boolean literals denote the Boolean values. -/
private theorem cfg_run_sound [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (hEval : BoundedEvalSoundAt P F)
    {k d : Nat}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π .contract d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    (hfac : FactoryWF (P := P) F) {n : Nat} {c c' : ICFGConfig String (CmdExt P) P}
    {cfgr : obs.Cfg} {st st' : obs.St} (hd : c.Denoting F) (hinv : CFGCfgInv π F (c.abs F))
    (h : obs.run (runInterpCFG (fun _ => StepCmdM.toStore (stepCmd π .contract d) k) n c) cfgr st
      = (.ok c', st')) :
    ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
      ∧ StepCFGStarE P (EvalCommandET π) (c.abs F) (revs.map (REvent.abs F)) (c'.abs F)
      ∧ c'.Denoting F := by
  rw [cfgCfgInv_eq] at hinv
  obtain ⟨revs, ht, R, hd'⟩ :=
    cfg_run_soundV obs (Calls.CmdExt.sem (Hdr := Hdr)) π hEval
      (fun _ e c => stepCmd π .contract d k e c) (armSound_of_cmdExt IH) hfac hd hinv h
  exact ⟨revs, ht, ReflTransTrace.imp (fun _ _ _ hs =>
    StepCFGE.imp (fun _ _ _ _ _ => evalCommandET_of_VT) hs) R, hd'⟩

omit [LawfulMonad m] in
/-- Assume every procedure of `π` is well-formed (`ProcsOk π`), and every successful command
    step `stepCmd π .contract d k` from a configuration with a well-formed factory (`FactoryWF`)
    satisfying
    `CfgInv π` is one reference step over `EvalCommandET π` recording its events (`IH`).  Then a
    successful callee body run `runCallee` of a procedure `π` resolves, over
    `stepCmd π .contract d k` at driver fuel `k`, from a well-formed, typed entry frame `σ`
    (`CallEnvOk`) at a well-formed factory `fac`, is a reference body execution `BigStepE` from
    `⟨σ, fac⟩` to the returned store recording exactly the run's events, and the returned store is
    well-formed and typed. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem runCallee_ok [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    {n : String} {p : Procedure P (CmdExt P) Hdr} {k d : Nat}
    {σ σf : RStore P} {cfgr : obs.Cfg} {st st' : obs.St}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π .contract d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    {tyArgs : Option (List P.Ty)} (hπ : typeInstantiatedCallee π n tyArgs = some p)
    (hfac : FactoryWF (P := P) F) (hd : RStore.Denoting F σ)
    (henv : CallEnvOk F (InterpLang.absStore F σ))
    (h : obs.run (runCallee (fun _ e c => stepCmd π .contract d k e c) n p.body (InterpLang.rfactory
        F) k σ)
        cfgr st = (.ok σf, st')) :
    ∃ revs : List (IEvent P), BigStepE π p.body ⟨InterpLang.absStore F σ, F⟩
        (InterpLang.absStore F σf) (revs.map (REvent.abs F)) ∧
      CallEnvOk F (InterpLang.absStore F σf) ∧ RStore.Denoting F σf
      ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨revs, B, henv', hd', ht⟩ := runCallee_okV obs (Calls.CmdExt.sem (Hdr := Hdr)) π hEval
    (fun _ e c => stepCmd π .contract d k e c) (armSound_of_cmdExt IH)
    ((procOk_iff π p).1 (hprocs n tyArgs p hπ)) hfac hd henv h
  exact ⟨revs, B, henv', hd', ht⟩

omit [LawfulMonad m] in
/-- At every stepper fuel `k` and call-depth budget `d`, if every procedure of `π` is well-formed
    (`ProcsOk π`: distinct frame formals, and a structured body that is exit-covered and has only
    well-formed call sites), a successful step `stepCmd π .contract d k` of a command (base command
    or
    `.call`) from a configuration with a well-formed factory (`FactoryWF`) satisfying the invariant
    `CfgInv π` (the replay invariant on the stores and the call sites) is one reference `StepStmtE`
    step over `EvalCommandET π`, to the configuration the result stands for (`IConfig.abs`),
    recording exactly the step's events. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
theorem call_cmd_arm [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F) :
    ∀ (k d : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
      (cfgr : obs.Cfg) (st st' : obs.St),
      obs.run (stepCmd π .contract d k env cmd) cfgr st = (.ok cfg', st') →
      FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
      ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F :=
  fun k d cmd env cfg' cfgr st st' h hf hd hr hi => by
    rw [cfgInv_eq] at hi
    obtain ⟨revs, hs, ht, hd'⟩ := stepCmdWith_arm obs (cmdExt_viewSound obs)
      (fun _ _ _ _ _ _ h => h) π .contract (procsOkV_of_procsOk π hprocs) (modeOk_contract _ π)
      hEval k d 0 cmd env cfg' cfgr st
      st' h hf hd hr hi
    exact ⟨revs, StepStmtE.imp (fun _ _ _ _ _ => evalCommandET_of_VT) hs, ht, hd'⟩

omit [LawfulMonad m] in
/-- **Per-step soundness of the call-aware engine.** If every procedure of `π` is well-formed
    (`ProcsOk π`), every successful `stepInterp (stepCmd π .contract d)` step, at every call-depth
    budget
    `d`, from a non-terminal, non-exiting
    configuration with a well-formed factory (`FactoryWF`) satisfying the invariant `CfgInv π`
    (the replay invariant on the stores and the call sites) is one reference `StepStmtE` step over
    `EvalCommandET π` that records exactly the step's events and reaches a configuration
    satisfying `CfgInv π` (`StepInterpSoundGeneric`). It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
theorem callStepInterpSound [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π) (d : Nat) :
    StepInterpSoundGeneric obs (stepCmd π .contract d) (EvalCommandET π) (CfgInv π) := by
  rw [cfgInv_eq]
  exact stepInterpSound_toET (stepCmdWith_stepSound obs (cmdExt_viewSound obs)
    (fun _ _ _ _ _ _ h => h) π .contract (procsOkV_of_procsOk π hprocs) (modeOk_contract _ π) d)

omit [LawfulMonad m] in
/-- **Whole-run soundness, monad-generically.**  If every procedure of `π` is well-formed
    (`ProcsOk π`) and the start configuration has a well-formed factory (`FactoryWF`) and satisfies
    the invariant `CfgInv π`, a successful `runCallInterp` run, at every call-depth limit `d`, is a
    reference `StepStmtExtStarE` execution emitting exactly the same events. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
theorem call_runInterp_sound [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π) (d : Nat) :
    RunInterpSound P m obs (stepCmd π .contract d) (EvalCmdExtE π) (CfgInv π) :=
  fun _ _ _ _ _ _ _ _ hD hrun hf hE hi =>
    (runInterp_sound_generic obs _ _ _ (callStepInterpSound obs π hprocs d) _ _ _ _ _ _ _
      _ hD hrun hf hE hi).imp fun _ => .imp fun _ => .imp fun _ => .imp_left (stepStarET_toE π)


omit [LawfulMonad m] in
/-- A successful run of `stepCmd π` whose result is projected to its store, on a command
    with well-formed call sites (`CmdCallOk`) from a well-formed, typed store (`CallEnvOk`) at a
    well-formed factory (`FactoryWF`), is a step of the typed call-aware command relation
    `EvalCommandET π` emitting exactly the recorded events, and the resulting store is again
    well formed and typed.  It assumes that every procedure of `π` passes `ProcsOk` and that
    at `F` every value the bounded evaluator commits to denotes the reference evaluator's value.
    It assumes that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
theorem cfg_stepCmd_store_sound [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (hprocs : ProcsOk π)
    {fuel d : Nat} {F : P.Factory} {σ σ' : IStore P} {cmd : CmdExt P}
    {cfgr : obs.Cfg} {st st' : obs.St} (hEval : BoundedEvalSoundAt P F)
    (hfac : FactoryWF (P := P) F) (hok : CmdCallOk π cmd = true) (hd : RStore.Denoting F σ.get)
    (henv : CallEnvOk F (InterpLang.absStore F σ.get))
    (h : obs.run (StepCmdM.toStore (stepCmd π .contract d) fuel (InterpLang.rfactory F) σ cmd) cfgr
        st
        = (.ok σ', st')) :
    ∃ revs : List (IEvent P), EvalCommandET π F (InterpLang.absStore F σ.get) cmd
        (InterpLang.absStore F σ'.get) (revs.map (REvent.abs F)) ∧
      CallEnvOk F (InterpLang.absStore F σ'.get) ∧ RStore.Denoting F σ'.get
      ∧ obs.trace st' = revs.reverse ++ obs.trace st :=
  store_sound_of_arm obs π (fun _ => call_cmd_arm obs π hprocs hEval fuel d) hfac hok hd henv h


end CallArm

/-! ## The interrupted-run certificate (`InterruptedSound`)

The reference relation takes a whole call as one `call_sem` step, so a trace that ends inside a call
has no flat `StepStmtStarE` derivation. `InterruptedSound` certifies such a trace recursively:
`clean` covers a completed run of steps, and the other constructors cover a run that stops inside
the call at its tail (in the precondition events, in the callee body, in the postcondition events,
or at the write-back; for an opaque callee, after havocking its outputs). -/

/-- **The call is the active redex of a config**, stable under the `.seq _ rest` and
    `.block l σ _` evaluation contexts.  A callee body is `.block "" ss` → `.stmts ss`
    → `.seq (.stmt call env) rest`, so a call is almost never at a *bare* config when it
    is stepped; `CallActive C pn tyArgs args md env` says peeling seq/block wrappers from `C`
    reaches the bare call `.stmt (.cmd (.call pn tyArgs args md)) env`.
    This is what makes `InterruptedSound` closed under those wrappers. -/
inductive CallActive :
    Config P (CmdExt P) → String → Option (List P.Ty) → List (CallArg P) →
      MetaData P → Env P → Prop where
  | here {pn tyArgs args md env} :
      CallActive (.stmt (.cmd (.call pn tyArgs args md)) env) pn tyArgs args md env
  | seq {inner rest pn tyArgs args md env} :
      CallActive inner pn tyArgs args md env →
        CallActive (.seq inner rest) pn tyArgs args md env
  | block {inner label σ pn tyArgs args md env} :
      CallActive inner pn tyArgs args md env →
        CallActive (.block label σ inner) pn tyArgs args md env

/-- Certificate that `evs` is the event trace of a reference run from a configuration, possibly
    stopped inside a call: a flat reference run (`clean`), or a flat run to an active call
    followed by a prefix of that call's events.  The call may stop inside a structured callee
    body (`inCall`), inside a CFG callee body between commands (`inCallCfg`) or inside one of
    its commands (`inCallCfgCmd`), at the write-back after a completed body (`inCallExit`),
    while emitting the precondition (`preThrow`) or postcondition (`postThrow`) events, or, for an
    abstract callee, after havocking the outputs (`inAbstractCall`). -/
inductive InterruptedSound (π : String → Option (Procedure P (CmdExt P) Hdr))
    :
    Config P (CmdExt P) → Trace P → Prop where
  | clean {start : Config P (CmdExt P)} {evs : Trace P} {mid : Config P (CmdExt P)} :
      StepStmtStarE P (EvalCmdExtE π) start evs mid →
      InterruptedSound π start evs
  | inCall {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String} {tyArgs : Option (List P.Ty)}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO : SemanticStore P}
        {bodyStmts : List (Stmt P (CmdExt P))}
      {calleeEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn tyArgs args md env →
      typeInstantiatedCallee π pn tyArgs = some p →
      p.body = .structured bodyStmts false →
      CallEntry env.factory env.store p args σAO →
      InterruptedSound π
        (.stmt (.block "" bodyStmts #[]) (⟨σAO, env.factory⟩ : Env P))
        calleeEvs →
      InterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (checksAtCall md p.spec.preconditions) ++ calleeEvs)
  /-- A CFG callee body that stops between two of its steps: the trace carries the events of a
      CFG run from the entry block. -/
  | inCallCfg {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String} {tyArgs : Option (List P.Ty)}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO : SemanticStore P} {g : DetCFG P (CmdExt P)}
      {cfgEvs : Trace P} {mid : CFGConfig String (CmdExt P) P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn tyArgs args md env →
      typeInstantiatedCallee π pn tyArgs = some p →
      p.body = .cfg g false →
      CallEntry env.factory env.store p args σAO →
      StepCFGStarE P (EvalCmdExtE π) (.atBlock g g.entry ⟨σAO, env.factory⟩) cfgEvs mid →
      InterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (checksAtCall md p.spec.preconditions) ++ cfgEvs)
  /-- A CFG callee body that stops inside its command `c`: the trace carries the events of a
      CFG run from the entry block to `c`, then events certified from `c`'s configuration. -/
  | inCallCfgCmd {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String} {tyArgs : Option (List P.Ty)}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO : SemanticStore P} {g g' : DetCFG P (CmdExt P)}
      {cfgEvs : Trace P} {t : String} {c : CmdExt P} {cs : List (CmdExt P)}
      {tr : DetTransferCmd String P} {ρ : Env P} {cmdEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn tyArgs args md env →
      typeInstantiatedCallee π pn tyArgs = some p →
      p.body = .cfg g false →
      CallEntry env.factory env.store p args σAO →
      StepCFGStarE P (EvalCmdExtE π) (.atBlock g g.entry ⟨σAO, env.factory⟩) cfgEvs
        (.inBlock g' t (c :: cs) tr ρ) →
      InterruptedSound π (.stmt (.cmd c) (⟨ρ.store, env.factory⟩ : Env P)) cmdEvs →
      InterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (checksAtCall md p.spec.preconditions) ++ cfgEvs
          ++ cmdEvs)
  /-- A **completed** callee body whose write-back throws
      (`programCallOutputUndefinedOnReturn`): the body ran to its final store and both the
      pre- and post-condition events emitted in full, but `CallExit` never fired, so this
      is neither `clean` (no `call_sem` step) nor `inCall` (the body is not still running). -/
  | inCallExit {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String} {tyArgs : Option (List P.Ty)}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO σf : SemanticStore P} {bodyEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn tyArgs args md env →
      typeInstantiatedCallee π pn tyArgs = some p →
      p.body.isOpaque = false →
      CallEntry env.factory env.store p args σAO →
      BigStepE π p.body ⟨σAO, env.factory⟩ σf bodyEvs →
      InterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO (checksAtCall md p.spec.preconditions)
          ++ bodyEvs ++ defaultAssertEvents env.factory σf p.spec.postconditions)
  /-- The interrupt fires **mid-precondition** emit (the target id matches a callee
      precondition clause): the trace carries a *prefix* of the precondition events.
      Reachable only when `emit` throws on the target. -/
  | preThrow {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String} {tyArgs : Option (List P.Ty)}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO : SemanticStore P}
      {preEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn tyArgs args md env →
      typeInstantiatedCallee π pn tyArgs = some p →
      CallEntry env.factory env.store p args σAO →
      preEvs <+: defaultAssertEvents env.factory σAO (checksAtCall md p.spec.preconditions) →
      InterruptedSound π start (outerEvs ++ preEvs)
  /-- The interrupt fires **mid-postcondition** emit, after the body completed: the trace
      carries the full pre-events, the full body events, and a *prefix* of the post-events.
      Reachable only when `emit` throws on the target. -/
  | postThrow {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String} {tyArgs : Option (List P.Ty)}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO σf : SemanticStore P} {bodyEvs : Trace P}
      {postEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn tyArgs args md env →
      typeInstantiatedCallee π pn tyArgs = some p →
      p.body.isOpaque = false →
      CallEntry env.factory env.store p args σAO →
      BigStepE π p.body ⟨σAO, env.factory⟩ σf bodyEvs →
      postEvs <+: defaultAssertEvents env.factory σf p.spec.postconditions →
      InterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO (checksAtCall md p.spec.preconditions)
          ++ bodyEvs ++ postEvs)
  /-- A call to an opaque callee that stops after havocking its output formals: the trace
      carries the full pre-events and a *prefix* of the postcondition assumption events at the
      post-havoc frame (all of them when the write-back throws). -/
  | inAbstractCall {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String} {tyArgs : Option (List P.Ty)}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO σO : SemanticStore P} {postEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn tyArgs args md env →
      typeInstantiatedCallee π pn tyArgs = some p →
      p.body.isOpaque = true →
      CallEntry env.factory env.store p args σAO →
      HavocVars env.factory σAO (ProcedureHeader.outputParams (P := P) p.header) σO →
      postEvs <+: assumeEvents env.factory σO p.spec.postconditions →
      InterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO (checksAtCall md p.spec.preconditions)
          ++ postEvs)

/-- Certificate that `evs` is the event trace of a CFG reference run over `EvalCmdExtE π` from
    `c`, possibly stopped inside one of its commands: the events of a run (`between`), or the
    events of a run to a block whose next command is `cmd`, followed by events certified by
    `InterruptedSound` from `cmd`'s configuration at the factory of `c` (`inCmd`). -/
inductive CFGInterrupted (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    CFGConfig String (CmdExt P) P → Trace P → Prop where
  /-- A run that stops between two of its steps. -/
  | between {c mid : CFGConfig String (CmdExt P) P} {evs : Trace P} :
      StepCFGStarE P (EvalCmdExtE π) c evs mid → CFGInterrupted π c evs
  /-- A run that stops inside its command `cmd`. -/
  | inCmd {c : CFGConfig String (CmdExt P) P} {cfgEvs cmdEvs : Trace P} {g : DetCFG P (CmdExt P)}
      {t : String} {cmd : CmdExt P} {cs : List (CmdExt P)} {tr : DetTransferCmd String P}
      {ρ : Env P} :
      StepCFGStarE P (EvalCmdExtE π) c cfgEvs (.inBlock g t (cmd :: cs) tr ρ) →
      InterruptedSound π (.stmt (.cmd cmd) ⟨ρ.store, c.getEnv.factory⟩) cmdEvs →
      CFGInterrupted π c (cfgEvs ++ cmdEvs)

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- **Closure of `InterruptedSound` under prepending one clean step**: a reference step from
    `cfg` to `cfg'` followed by a certified trace from `cfg'` is a certified trace from `cfg`. -/
private theorem interruptedSound_stepThen
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (cfg : Config P (CmdExt P)) (evs : Trace P) (cfg' : Config P (CmdExt P)) (rest : Trace P)
    (hstep : StepStmtE P (EvalCmdExtE π) cfg evs cfg')
    (hrest : InterruptedSound π cfg' rest) :
    InterruptedSound π cfg (evs ++ rest) := by
  cases hrest <;> (try simp only [← List.append_assoc]) <;>
    open InterruptedSound in
    solve_by_elim (maxDepth := 12) [inCall, inCallCfg, inCallCfgCmd, inCallExit, postThrow,
      preThrow, inAbstractCall]

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- **`InterruptedSound` is closed under the `.seq _ rest` evaluation context**: a certified trace
    from `inner` is a certified trace from `.seq inner rest`. -/
private theorem interruptedSound_seq
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (inner : Config P (CmdExt P)) (rest : List (Stmt P (CmdExt P))) (evs : Trace P)
    (h : InterruptedSound π inner evs) :
    InterruptedSound π (.seq inner rest) evs := by
  cases h <;> open InterruptedSound in
    solve_by_elim (maxDepth := 12) [inCall, inCallCfg, inCallCfgCmd, inCallExit, postThrow,
      preThrow, inAbstractCall, clean, seq_inner_starE]

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- **`InterruptedSound` is closed under the `.block l σ _` evaluation context**: a certified
    trace from `inner` is a certified trace from `.block l σ inner`. -/
private theorem interruptedSound_block
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (label : Option String) (σp : SemanticStore P)
    (inner : Config P (CmdExt P)) (evs : Trace P)
    (h : InterruptedSound π inner evs) :
    InterruptedSound π (.block label σp inner) evs := by
  cases h <;> open InterruptedSound in
    solve_by_elim (maxDepth := 12) [inCall, inCallCfg, inCallCfgCmd, inCallExit, postThrow,
      preThrow, inAbstractCall, clean, block_inner_starE]

/-- If every procedure of `π` is well-formed (`ProcsOk π`), the Boolean literals denote the Boolean
    values (`InterpLangBool`), the bounded evaluator is sound up to denotation at `F`
    (`BoundedEvalSoundAt`), and `start` satisfies the invariant `CfgInv π` at a well-formed factory
    `F` (`FactoryWF`), a successful replay run of `runCallInterp π` from a runtime configuration
    `istart` that denotes `start` under `F` (`IConfig.Denotes`) records runtime events whose images
    (`REvent.abs F`) are exactly the events of a reference run from `start` to the image
    (`IConfig.abs F`) of the returned configuration, and the returned configuration denotes. -/
theorem call_replayRun_sound [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (fuel : Nat) (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (start : Config P (CmdExt P))
    (istart : IConfig P (CmdExt P))
    (hstart : istart.Denotes F start) (final : IConfig P (CmdExt P))
    (cfg : ReplayCfg P) (oracle : List P.Expr)
    (st' : ReplayState P) (d : Nat)
    (hrun : runReplayRun (runCallInterp (m := ReplayM P) π .contract fuel istart d) cfg oracle
        = (.ok final, st'))
    (hfac : FactoryWF (P := P) F) (hinv : CfgInv π start) :
    ∃ revs : List (IEvent P), StepStmtStarE (P := P) (EvalCmdExtE π)
             start (revs.map (REvent.abs F)) (final.abs F) ∧ final.Denoting F ∧
             st'.traceRev = revs.reverse := by
  obtain ⟨_, revs, _, hs, ⟨hd, -, rfl⟩, htr, rfl⟩ := call_runInterp_sound obsReplay π hprocs
    d _ _ _ _ _ _ _ _ hstart hrun hfac hEval hinv
  exact ⟨revs, hs, hd, by simpa [obsReplay] using htr⟩

/-! ## The error discharge: `StepInterpErrSoundInto` into `InterruptedSound` -/

section CallErrDischarge

variable {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m]
  [MonadExcept StopReason m]

omit [CallLangWF P] [HasOldIdent P] [LawfulMonad m] [HasFvar P] [HasFvars P] in
/-- A run of `resolveGuard`, whatever its outcome, leaves the trace unchanged when a throwing
    `choose` does. -/
private theorem obs_resolveGuard_trace (obs : InterpObs P m)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    {fuel : Nat} {env : IEnv P} {g : ExprOrNondet P} {cfgr : obs.Cfg} {st st' : obs.St}
    {q : Except StopReason Bool} (h : obs.run (resolveGuard fuel env g) cfgr st = (q, st')) :
    obs.trace st' = obs.trace st := by
  cases g with
  | det c =>
    simp only [resolveGuard] at h
    split at h
    · split at h <;> simp only [InterpObs.run_pure, InterpObs.branch_stuck, Prod.mk.injEq] at h <;>
        rw [← h.2]
    · simp only [InterpObs.run_throw, Prod.mk.injEq] at h
      rw [← h.2]
  | nondet =>
    simp only [resolveGuard, InterpObs.run_bind] at h
    split at h
    · rename_i hc
      have ht := (obs.choose_sound _ _ _ _ _ _ _ hc).2
      split at h <;> simp only [InterpObs.run_pure, InterpObs.run_throw, Prod.mk.injEq] at h <;>
        rw [← h.2, ht]
    · rename_i hc
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact hchooseErr _ _ _ _ _ _ _ hc

omit [CallLangWF P] [HasOldIdent P] [LawfulMonad m] in
/-- **Error soundness of one step, into a certificate.** Fix an invariant `Inv` on
    configurations and a trace certificate `TraceSound`.  Assume a throwing command step from an
    `Inv` configuration recorded events certified by `TraceSound`; `TraceSound` holds of every
    `StepStmtStarE` trace and is closed under the `.seq`/`.block` evaluation contexts; `Inv`
    projects into the inner configuration of a `.seq`/`.block`; and a throwing `choose` leaves
    the trace unchanged.  Then every throwing `stepInterp stepCmd` step from a non-terminal,
    non-exiting tracked configuration whose abstraction satisfies `Inv` recorded events certified
    by `TraceSound` from that abstraction (`StepInterpErrSoundInto`). -/
private theorem stepInterpErrInto_of_arms (obs : InterpObs P m)
    (stepCmd : StepCmdM P (CmdExt P) m)
    (EvalCmd : EvalCmdParamE P (CmdExt P) (Event P))
    (Inv : Config P (CmdExt P) → Prop)
    (TraceSound : Config P (CmdExt P) → List (Event P) → Prop)
    (hclean : ∀ (start : Config P (CmdExt P)) (evs : List (Event P)) (mid : Config P (CmdExt P)),
        StepStmtStarE P EvalCmd start evs mid → TraceSound start evs)
    (hseqInv : ∀ (inner : Config P (CmdExt P)) (ss : List (Stmt P (CmdExt P))),
        Inv (.seq inner ss) → Inv inner)
    (hblkInv : ∀ (l : Option String) (σ : SemanticStore P)
        (inner : Config P (CmdExt P)),
        Inv (.block l σ inner) → Inv inner)
    (hseqClose : ∀ (inner : Config P (CmdExt P)) (rest : List (Stmt P (CmdExt P)))
        (evs : List (Event P)),
        TraceSound inner evs → TraceSound (.seq inner rest) evs)
    (hblkClose : ∀ (l : Option String) (σ : SemanticStore P)
        (inner : Config P (CmdExt P)) (evs : List (Event P)),
        TraceSound inner evs → TraceSound (.block l σ inner) evs)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    (hcmdErr : ∀ (F : P.Factory) (fuel : Nat) (cmd : CmdExt P) (env : IEnv P)
        (cfgr : obs.Cfg) (st st' : obs.St) (r : StopReason),
        obs.run (stepInterp stepCmd fuel (.stmt (.cmd cmd) env)) cfgr st = (.error r, st') →
        FactoryWF (P := P) F → BoundedEvalSoundAt P F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → Inv (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), TraceSound (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F))
          ∧ obs.trace st' = revs.reverse ++ obs.trace st) :
    StepInterpErrSoundInto obs stepCmd Inv (fun _ => TraceSound) := by
  intro F fuel c cfgr
  have hW : ∀ k c evs, TraceSound c evs → TraceSound (Config.wrapSeqs c k) evs := by
    intro k c evs h
    induction k with | zero => exact h | succ _ ih => exact hseqClose _ _ _ ih
  have hV : ∀ k c, Inv (Config.wrapSeqs c k) → Inv c := by
    intro k c h
    induction k with | zero => exact h | succ _ ih => exact ih (hseqInv _ _ h)
  have hnil : ∀ (c : Config P (CmdExt P)) (st st' : obs.St), obs.trace st' = obs.trace st →
      ∃ revs : List (IEvent P), TraceSound c (revs.map (REvent.abs F)) ∧
        obs.trace st' = revs.reverse ++ obs.trace st :=
    fun c _ _ h => ⟨[], hclean _ _ _ (.refl _), by simpa using h⟩
  induction c with
  | stmt s env =>
    intro st st' r h _ _ hf hE hd hi _
    cases s with
    | cmd cmd => exact hcmdErr F _ _ _ _ _ _ _ h hf hE hd.1 hd.2 hi
    | ite | loop =>
      simp only [stepInterp, InterpObs.run_bind] at h
      split at h
      · simp only [InterpObs.run_pure, Prod.mk.injEq, reduceCtorEq, false_and] at h
      · rename_i hrg
        obtain ⟨-, rfl⟩ := Prod.mk.inj h
        exact hnil _ _ _ (obs_resolveGuard_trace obs hchooseErr hrg)
    | _ =>
      simp only [stepInterp, InterpObs.run_pure, Prod.mk.injEq, reduceCtorEq, false_and] at h
  | stmts | terminal | exiting =>
    intro st st' r h hnt hne
    first
      | exact absurd rfl (hnt _)
      | exact absurd rfl (hne _ _)
      | (rename_i ss _
         rcases ss with _ | ⟨_, _ | _⟩ <;> simp [stepInterp] at h)
  | seq inner ss ih =>
    intro st st' r h _ _ hf hE hd hi ht
    by_cases hdone : (∃ e, inner = .terminal e) ∨ ∃ l e, inner = .exiting l e
    · rcases hdone with ⟨e, rfl⟩ | ⟨l, e, rfl⟩ <;> simp [stepInterp] at h
    simp only [not_or, not_exists] at hdone
    simp only [stepInterp_seq_unfold_gen _ _ _ _ hdone.1 hdone.2, InterpObs.run_bind,
      InterpObs.run_pure] at h
    split at h
    · cases h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    obtain ⟨revs, hs, htr⟩ := ih _ _ _ ‹_› hdone.1 hdone.2 hf hE hd (hseqInv _ _ hi) ht
    exact ⟨revs, hseqClose _ _ _ hs, htr⟩
  | seqs inner k ih =>
    intro st st' r h _ _ hf hE hd hi ht
    by_cases hdone : (∃ e, inner = .terminal e) ∨ ∃ l e, inner = .exiting l e
    · rcases hdone with ⟨e, rfl⟩ | ⟨l, e, rfl⟩ <;> cases k <;> simp [stepInterp] at h
    simp only [not_or, not_exists] at hdone
    simp only [stepInterp] at h
    split at h
    · exact absurd rfl (hdone.1 _)
    · exact absurd rfl (hdone.2 _ _)
    simp only [InterpObs.run_bind] at h
    split at h
    · split at h <;> simp at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    obtain ⟨revs, hs, htr⟩ := ih _ _ _ ‹_› hdone.1 hdone.2 hf hE hd (hV (k + 1) _ hi) ht
    exact ⟨revs, hW (k + 1) _ _ hs, htr⟩
  | block l fr inner ih =>
    intro st st' r h _ _ hf hE hd hi ht
    by_cases hdone : (∃ e, inner = .terminal e) ∨ ∃ l e, inner = .exiting l e
    · rcases hdone with ⟨e, rfl⟩ | ⟨l', e, rfl⟩ <;> simp only [stepInterp] at h
      all_goals (try split at h) <;> simp at h
    simp only [not_or, not_exists] at hdone
    simp only [stepInterp_block_unfold_gen _ _ _ _ _ hdone.1 hdone.2, InterpObs.run_bind,
      InterpObs.run_pure] at h
    split at h
    · cases h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    obtain ⟨revs, hs, htr⟩ := ih _ _ _ ‹_› hdone.1 hdone.2 hf hE hd.2 (hblkInv _ _ _ hi) ht.2
    exact ⟨revs, hblkClose _ _ _ _ hs, htr⟩

omit [LawfulMonad m] in
omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [CallLangWF P]
    [HasOldIdent P] in
/-- A throwing `forM` of `emit`s recorded a prefix of its events. -/
private theorem obs_forM_emit_err (obs : InterpObs P m)
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2
          = ev :: obs.trace st)
    (cfgr : obs.Cfg) :
    ∀ (evs : List (IEvent P)) (st st' : obs.St) (r : StopReason),
      obs.run (evs.forM (InterpEffects.emit (P := P))) cfgr st = (.error r, st') →
      ∃ pref, pref <+: evs ∧ obs.trace st' = pref.reverse ++ obs.trace st := fun evs => by
  induction evs <;> intro st st' r h <;>
    simp_all only [List.forM_eq_forM, List.forM_nil, InterpObs.run_pure, Prod.mk.injEq,
      reduceCtorEq, false_and, List.forM_cons, InterpObs.run_bind]
  rename_i a l ih
  split at h
  · obtain ⟨w, hw⟩ := ih _ _ _ h
    exact ⟨a :: w, by grind⟩
  exact ⟨[a], by grind⟩

omit [CallLangWF P] [LawfulMonad m] in
/-- A throwing base-command step is certified `clean` by a flat reference derivation. -/
private theorem obs_stepCmd_base_err (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2
          = ev :: obs.trace st)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    {k d : Nat} {env : IEnv P} {base : Cmd P} {cfgr : obs.Cfg} {st st' : obs.St} {r : StopReason}
    (h : obs.run (stepCmd π .contract d k env (.cmd base)) cfgr st = (.error r, st')) :
    ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd (CmdExt.cmd base)) (env.abs F)) (revs.map (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  rcases base with ⟨_, _, _ | _, _⟩ | ⟨_, _ | _, _⟩ | _ | _ | _
  rotate_left 4
  iterate 3
    simp only [stepCmd_cmd, stepBaseCmdStore, Cmd.rEmittedEvents, List.forM_eq_forM,
      List.forM_cons, List.forM_nil, obs.run_bind, obs.run_pure] at h
    generalize hE : obs.run (InterpEffects.emit (P := P) _) cfgr st = q at h
    rcases q with ⟨_ | _, s⟩ <;> simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
    obtain ⟨-, rfl⟩ := h
    have hs : (obs.run _ cfgr st).2 = s := congrArg Prod.snd hE
    subst hs
    refine ⟨[?_], ?_, ?_⟩
    all_goals try (rw [hemitStep]; rfl)
    exact .clean (StepStmtStarE.single (StepStmtE.step_cmd (EvalCmdExtE.cmd_sem (by constructor))))
  all_goals
    simp only [stepCmd_cmd, stepBaseCmdStore] at h
    (repeat' first | split at h | simp only [obs.run_bind, obs.run_pure, obs.run_throw] at h)
  all_goals cases h
  all_goals
    refine ⟨[], .clean (.refl _), ?_⟩
    grind [→ obs.choose_sound]

omit [HasFvar P] [HasFvars P] [HasOldIdent P] [CallLangWF P] [LawfulMonad m] in
/-- A run of `havocVarList`, successful or throwing, records no event, given that a throwing
    `choose` leaves the trace unchanged. -/
private theorem obs_havocVarList_trace (obs : InterpObs P m)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    (fuel : Nat) (fac : InterpLang.RFactory P) :
    ∀ (xs : List P.Ident) (store : IStore P) (cfgr : obs.Cfg) (st : obs.St)
      (res : Except StopReason (IStore P)) (st' : obs.St),
      obs.run (havocVarList fuel fac xs store) cfgr st = (res, st') → obs.trace st' = obs.trace st
  | [], _, _, _, _, _, h => by
    simp only [havocVarList, obs.run_pure, Prod.mk.injEq] at h
    rw [← h.2]
  | x :: xs, store, cfgr, st, res, st', h => by
    have hb : ∀ (res' : Except StopReason (IStore P)) (s : obs.St),
        obs.run (stepBaseCmdStore fuel fac store (.set x .nondet MetaData.empty)) cfgr st =
          (res', s) → obs.trace s = obs.trace st := by
      intro _ _ h
      simp only [stepBaseCmdStore] at h
      (repeat' first | split at h | simp only [obs.run_bind, obs.run_pure, obs.run_throw] at h)
      all_goals cases h
      all_goals grind [→ obs.choose_sound]
    simp only [havocVarList, obs.run_bind] at h
    split at h
    · rename_i hs
      exact (obs_havocVarList_trace obs hchooseErr fuel fac xs _ cfgr _ res st' h).trans (hb _ _ hs)
    · rename_i hs
      exact (Prod.mk.inj h).2 ▸ hb _ _ hs

omit [LawfulMonad m] in
/-- Assume every procedure of `π` is well-formed (`ProcsOk π`), and every throwing command step
    `stepCmd π .contract d k` from a configuration with a well-formed factory (`FactoryWF`)
    satisfying the invariant `CfgInv π` (the replay invariant on the stores and the call sites)
    recorded events certified by `InterruptedSound π` (the events of a reference run, possibly
    stopped inside a call), and a throwing `choose` leaves the trace unchanged. Then a throwing
    callee-body run of
    `runInterp` at call-depth budget `d` and stepper fuel `k` from a configuration
    `.stmt (.block "" ss #[]) E` satisfying `CfgInv π`, at a well-formed factory `E.factory`,
    recorded events certified by `InterruptedSound π` from that configuration. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem callee_run_err [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    {k d : Nat} {ss : List (Stmt P (CmdExt P))} {E : IEnv P} {cfgr : obs.Cfg} {st st' : obs.St}
    {r : StopReason}
    (ih : ∀ (cmd : CmdExt P) (env : IEnv P) (cfgr : obs.Cfg) (st st' : obs.St) (r : StopReason),
      obs.run (stepCmd π .contract d k env cmd) cfgr st = (.error r, st') →
      FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
      ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st)
    (hI : CfgInv π (.stmt (.block "" ss #[]) (E.abs F))) (hfE : FactoryWF (P := P) F)
    (hdE : RStore.Denoting F E.store.get) (hrE : E.factory = InterpLang.rfactory F)
    (h : obs.run (runInterp (fun _ e c => stepCmd π .contract d k e c) k (.stmt (.block "" ss #[])
        E)) cfgr st
        = (.error r, st')) :
    ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.block "" ss #[]) (E.abs F))
        (revs.map (REvent.abs F))
      ∧ obs.trace st' = revs.reverse ++ obs.trace st :=
  runInterp_traceSound_generic obs _ (EvalCommandET π) _ (fun _ => InterruptedSound π)
    (fun _ _ _ _ hstar => .clean (stepStarET_toE π hstar))
    (fun _ _ _ _ _ hs hr => interruptedSound_stepThen π _ _ _ _ (stepET_toE π hs) hr)
    (callStepSound_at obs π d (fun _ => k) fun _ => call_cmd_arm obs π hprocs hEval k d)
    (stepInterpErrInto_of_arms obs _ (EvalCommandET π) _ _
      (fun _ _ _ hstar => .clean (stepStarET_toE π hstar))
      (fun _ _ h => ⟨cfgInv_seq π _ _ h.1, h.2⟩) (fun _ _ _ h => ⟨cfgInv_block π _ _ _ h.1, h.2⟩)
      (interruptedSound_seq π) (interruptedSound_block π) hchooseErr
      fun _ _ cmd env cfgr st st' r h hf _ hd hrf ⟨hi, hF⟩ => by
        subst hF
        exact ih cmd env cfgr st st' r h hf hd hrf hi)
    F k _ cfgr st st' _ h hfE hEval ⟨hdE, hrE⟩ ⟨hI, rfl⟩ trivial

omit [HasFvar P] [HasFvars P] [CallLangWF P] [HasOldIdent P]
    [ProcedureHeader P Hdr] [ProcedureTypeInstantiation P Hdr] [LawfulMonad m] in
/-- A throwing CFG step either leaves the state alone, or is a throwing command step of the store
    stepper on the first residual command of the current block. -/
private theorem stepInterpCFG_err (obs : InterpObs P m) (S : StepCmdStoreM P (CmdExt P) m)
    (n : Nat) (c : ICFGConfig String (CmdExt P) P)
    {cfgr : obs.Cfg} {st st' : obs.St} {r : StopReason}
    (h : obs.run (stepInterpCFG S n c) cfgr st = (.error r, st')) :
    st' = st ∨ ∃ g t c' cs tr ρ, c = .inBlock g t (c' :: cs) tr ρ ∧
      ∃ r', obs.run (S n ρ.factory ρ.store c') cfgr st = (.error r', st') := by
  fun_cases stepInterpCFG <;> simp only [stepInterpCFG] at h <;>
    (repeat' first
      | split at h
      | simp only [obs.run_pure, obs.run_throw, obs.run_bind, Prod.mk.injEq, reduceCtorEq,
          false_and] at h) <;>
    grind

omit [LawfulMonad m] in
/-- Assume every successful step `stepCmd π .contract d k` from a configuration with a well-formed
    factory satisfying `CfgInv π` is one reference step over `EvalCommandET π` (`IH`), and every
    throwing one records events certified by `InterruptedSound π` (`IHerr`).  Then a throwing
    run of `runInterpCFG` over the store stepper of `stepCmd π .contract d k`, at a well-formed
    factory
    `fac`, from a configuration satisfying `CFGCfgInv`, recorded the events of a CFG reference
    run from that configuration, possibly followed by events certified from the configuration
    of the command the run stopped in. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem cfg_run_err [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hEval : BoundedEvalSoundAt P F)
    {k d : Nat}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π .contract d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    (IHerr : ∀ (cmd : CmdExt P) (env : IEnv P) (cfgr : obs.Cfg) (st st' : obs.St)
        (r : StopReason),
        obs.run (stepCmd π .contract d k env cmd) cfgr st = (.error r, st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd cmd) (env.abs F)) (revs.map
            (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st)
    (hfac : FactoryWF (P := P) F) :
    ∀ (n : Nat) (c : ICFGConfig String (CmdExt P) P) (cfgr : obs.Cfg) (st st' : obs.St)
      (r : StopReason), c.Denoting F → CFGCfgInv π F (c.abs F) →
      obs.run (runInterpCFG (fun _ => StepCmdM.toStore (stepCmd π .contract d) k) n c) cfgr st
        = (.error r, st') →
      ∃ revs : List (IEvent P), CFGInterrupted π (c.abs F) (revs.map (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  intro n c cfgr st st' r hd hinv h
  induction n generalizing c st with
  | zero =>
    unfold runInterpCFG at h
    split at h <;>
      simp only [obs.run_pure, obs.run_throw, Prod.mk.injEq, reduceCtorEq, false_and] at h
    exact ⟨[], .between (.refl _), by rw [h.2]; rfl⟩
  | succ n ih =>
    unfold runInterpCFG at h
    split at h
    any_goals simp only [obs.run_pure, Prod.mk.injEq, reduceCtorEq, false_and] at h
    rw [obs.run_bind] at h
    split at h
    · rename_i next s hs
      obtain ⟨⟨e₁, ht₁, hstep⟩, hd', hinv'⟩ :=
        stepInterpCFG_soundE obs (EvalCommandET π) _ (CFGCfgInv π F) F
          (cfgCmd_sound_of_arm obs π IH hfac) (fun _ _ _ => cfgCfgInv_stepE π F) hEval _
          (by grind) hd hinv hs
      have hstepE := hstep.imp fun _ _ _ _ _ => And.left
      obtain ⟨e₂, hc, ht₂⟩ := ih next s hd' hinv' h
      refine ⟨e₁ ++ e₂, ?_, by simp [ht₂, ht₁]⟩
      rw [List.map_append]
      generalize e₂.map (REvent.abs F) = e at hc
      have hF : (next.abs F).getEnv.factory = (c.abs F).getEnv.factory := by
        cases next <;> cases c <;> rfl
      cases hc with
      | between R => exact .between (.step _ _ _ _ _ hstepE R)
      | inCmd R hcmd => exact List.append_assoc .. ▸ .inCmd (.step _ _ _ _ _ hstepE R) (hF ▸ hcmd)
    · rename_i r' s hs
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      rcases stepInterpCFG_err obs _ _ _ hs with rfl | ⟨g, t, c', cs, tr, ρ, rfl, r'', he⟩
      · exact ⟨[], .between (.refl _), rfl⟩
      · rw [obs.run_bind] at he
        split at he
        · simp only [obs.run_pure, Prod.mk.injEq, reduceCtorEq, false_and] at he
        rename_i _ _ hcmd
        obtain ⟨he', hr, _, -⟩ := hinv
        obtain ⟨hdρ, hrf⟩ := hd
        obtain ⟨cmdEvs, hcert, ht⟩ := IHerr _ _ _ _ _ _ hcmd hfac hdρ hrf
          ⟨he'.1, by simpa [Config.allCmds, Stmt.allCmds] using hr _ (.head _), he'.2⟩
        exact ⟨cmdEvs, List.nil_append (cmdEvs.map _) ▸ .inCmd (.refl _) hcert,
          (Prod.mk.inj he).2 ▸ ht⟩

omit [LawfulMonad m] in
/-- Assume every procedure of `π` is well-formed (`ProcsOk π`), every successful step
    `stepCmd π .contract d k` from a configuration with a well-formed factory satisfying `CfgInv π`
    is one reference step over `EvalCommandET π` (`IH`), every throwing one records events certified
    by
    `InterruptedSound π` (`IHerr`), and a throwing `choose` leaves the trace unchanged.  Then a
    throwing callee body run `runCallee` of a procedure `π` resolves, over `stepCmd π .contract d k`
    at driver fuel `k`, from a well-formed, typed entry frame `σ` at a well-formed factory `fac`,
    recorded events certified from the body's start: for a structured body, by `InterruptedSound π`
    from its
    `.block ""` configuration; for a CFG body, as the events of a CFG reference run from its entry
    block, possibly followed by events certified from the configuration of the command the run
    stopped in. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem runCallee_err [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    {n : String} {p : Procedure P (CmdExt P) Hdr} {k d : Nat}
    {σ : RStore P} {cfgr : obs.Cfg} {st st' : obs.St} {r : StopReason}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π .contract d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    (IHerr : ∀ (cmd : CmdExt P) (env : IEnv P) (cfgr : obs.Cfg) (st st' : obs.St)
        (r : StopReason),
        obs.run (stepCmd π .contract d k env cmd) cfgr st = (.error r, st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd cmd) (env.abs F)) (revs.map
            (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st)
    {tyArgs : Option (List P.Ty)} (hπ : typeInstantiatedCallee π n tyArgs = some p)
    (hfac : FactoryWF (P := P) F) (hd : RStore.Denoting F σ)
    (henv : CallEnvOk F (InterpLang.absStore F σ))
    (hnabs : ¬p.body.isOpaque = true)
    (h : obs.run (runCallee (fun _ e c => stepCmd π .contract d k e c) n p.body (InterpLang.rfactory
        F) k σ)
        cfgr st = (.error r, st')) :
    ∃ revs : List (IEvent P), ((∃ ss, p.body = .structured ss false ∧
          InterruptedSound π (.stmt (.block "" ss #[]) ⟨InterpLang.absStore F σ, F⟩)
            (revs.map (REvent.abs F))) ∨
        ∃ g, p.body = .cfg g false ∧
          CFGInterrupted π (.atBlock g g.entry ⟨InterpLang.absStore F σ, F⟩)
          (revs.map (REvent.abs F)))
      ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨-, hS, hC⟩ := hprocs n _ p hπ
  have hE : IEnv.abs F (⟨.ofStore σ, InterpLang.rfactory F⟩ : IEnv P) =
      ⟨InterpLang.absStore F σ, F⟩ := by simp [IEnv.abs]
  have hdE : RStore.Denoting F (IStore.ofStore σ).get := by simpa using hd
  have hdA : ∀ g : DetCFG P (CmdExt P), ICFGConfig.Denoting F
      (.atBlock g g.entry ⟨.ofStore σ, InterpLang.rfactory F⟩ : ICFGConfig _ (CmdExt P) P) :=
    fun _ => ⟨hdE, rfl⟩
  revert h
  cases hb : p.body with
  | structured ss o =>
    obtain rfl : o = false := by simpa [hb] using hnabs
    intro h
    have hI : CfgInv π (.stmt (.block "" ss #[])
        (IEnv.abs F ⟨.ofStore σ, InterpLang.rfactory F⟩)) :=
      hE ▸ ⟨henv.1, by simpa [Config.allCmds, Stmt.allCmds] using (hS ss _ hb).2, henv.2⟩
    simp only [runCallee, obs.run_bind] at h
    split at h
    · rename_i fc s hrun
      obtain ⟨σ', rfl, -⟩ := callee_run_ok obs π hprocs hEval IH hπ hb hI hfac hdE rfl hrun
      simp only [obs.run_pure, Prod.mk.injEq, reduceCtorEq, false_and] at h
    · rename_i r' s hrun
      obtain ⟨revs, hc, ht⟩ :=
        callee_run_err obs π hprocs hEval hchooseErr IHerr hI hfac hdE rfl hrun
      exact ⟨revs, .inl ⟨ss, rfl, hE ▸ hc⟩, (Prod.mk.inj h).2 ▸ ht⟩
  | cfg g o =>
    obtain rfl : o = false := by simpa [hb] using hnabs
    intro h
    have hA : ICFGConfig.abs F (.atBlock g g.entry ⟨.ofStore σ, InterpLang.rfactory F⟩ :
        ICFGConfig _ (CmdExt P) P) = .atBlock g g.entry ⟨InterpLang.absStore F σ, F⟩ := by
      simp [ICFGConfig.abs, IEnv.abs]
    have hInv : CFGCfgInv π F
        (ICFGConfig.abs F (.atBlock g g.entry ⟨.ofStore σ, InterpLang.rfactory F⟩)) :=
      hA ▸ ⟨henv, hC g _ hb, rfl⟩
    simp only [runCallee, obs.run_bind] at h
    split at h
    · rename_i fc s hrun
      obtain ⟨revs, htr, R, -⟩ := cfg_run_sound obs π hEval IH hfac (hdA g) hInv hrun
      rw [hA] at R
      split at h <;> simp only [obs.run_pure, obs.run_throw, Prod.mk.injEq, reduceCtorEq,
        false_and] at h
      exact ⟨revs, .inr ⟨g, rfl, .between (R.imp fun _ _ _ => .imp fun _ _ _ _ _ => And.left)⟩,
        h.2 ▸ htr⟩
    · rename_i r' s hrun
      obtain ⟨revs, hc, ht⟩ :=
        cfg_run_err obs π hEval IH IHerr hfac _ _ _ _ _ _ (hdA g) hInv hrun
      exact ⟨revs, .inr ⟨g, rfl, hA ▸ hc⟩, (Prod.mk.inj h).2 ▸ ht⟩
  | abstract => simp [hb] at hnabs

/-! ### The interrupted `.call` step, by where it stops

Each lemma takes a `.call` step that built the callee frame `callEntryStore p i o` (its image the
reference frame `callEntryStore p vi vo`, `CallEntry` holding) and stopped at one point, and
certifies the recorded events by the matching `InterruptedSound` constructor. -/

omit [CallLangWF P] [LawfulMonad m] in
/-- A call stopped inside its precondition events: `InterruptedSound.preThrow`. -/
private theorem callErr_pre (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2 = ev :: obs.trace st)
    {n : String} {tyArgs : Option (List P.Ty)}
    {args : List (CallArg P)} {md : MetaData P} {env : IEnv P}
    {p : Procedure P (CmdExt P) Hdr} {i o : List P.Expr} {vi vo : List P.Val}
    {cfgr : obs.Cfg} {st st' : obs.St} {r : StopReason}
    (hπ : typeInstantiatedCallee π n tyArgs = some p)
    (hE : CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo))
    (habs : InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo)
    (hpre : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions)).forM (InterpEffects.emit (P := P))) cfgr st
        = (.error r, st')) :
    ∃ revs : List (IEvent P),
        InterruptedSound π (.stmt (.cmd (.call n tyArgs args md)) (env.abs F))
        (revs.map (REvent.abs F)) ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨pref, hq, u⟩ := obs_forM_emit_err obs hemitStep cfgr _ _ _ _ hpre
  have hq' := hq.map (REvent.abs F)
  rw [rDefaultAssertEvents_abs, habs] at hq'
  refine ⟨pref, ?_, u⟩
  simpa using
    InterruptedSound.preThrow (outerEvs := []) (env := env.abs F) (.refl _) .here hπ hE hq'

omit [CallLangWF P] [LawfulMonad m] in
/-- A call stopped inside its callee body, given the certificate of the body's events (the shape
    `runCallee_err` returns): `InterruptedSound.inCall`, `inCallCfg` or `inCallCfgCmd`. -/
private theorem callErr_body (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {n : String} {tyArgs : Option (List P.Ty)}
    {args : List (CallArg P)} {md : MetaData P} {env : IEnv P}
    {p : Procedure P (CmdExt P) Hdr} {i o : List P.Expr} {vi vo : List P.Val}
    {cfgr : obs.Cfg} {st s st' : obs.St} {u : Unit} {crevs : List (IEvent P)}
    (hπ : typeInstantiatedCallee π n tyArgs = some p)
    (hE : CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo))
    (habs : InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo)
    (hpre : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions)).forM (InterpEffects.emit (P := P))) cfgr st
        = (.ok u, s))
    (hc : (∃ ss, p.body = .structured ss false ∧
          InterruptedSound π
            (.stmt (.block "" ss #[]) ⟨InterpLang.absStore F (callEntryStore p i o), F⟩)
            (crevs.map (REvent.abs F))) ∨
        ∃ g, p.body = .cfg g false ∧ CFGInterrupted π
          (.atBlock g g.entry ⟨InterpLang.absStore F (callEntryStore p i o), F⟩)
          (crevs.map (REvent.abs F)))
    (u' : obs.trace st' = crevs.reverse ++ obs.trace s) :
    ∃ revs : List (IEvent P),
        InterruptedSound π (.stmt (.cmd (.call n tyArgs args md)) (env.abs F))
        (revs.map (REvent.abs F)) ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
    (checksAtCall md p.spec.preconditions) ++ crevs, ?_,
    by simp [u', obs_forM_emit obs _ _ _ _ _ hpre]⟩
  rw [habs] at hc
  rw [List.map_append, rDefaultAssertEvents_abs, habs, ← List.nil_append (defaultAssertEvents ..)]
  rcases hc with ⟨_, hb, hc⟩ | ⟨_, hb, hc⟩
  · exact .inCall (env := env.abs F) (.refl _) .here hπ hb hE hc
  generalize crevs.map (REvent.abs F) = e at hc ⊢
  cases hc with
  | between R => exact .inCallCfg (env := env.abs F) (.refl _) .here hπ hb hE R
  | inCmd R hc =>
    rw [← List.append_assoc]
    exact .inCallCfgCmd (env := env.abs F) (.refl _) .here hπ hb hE R hc

omit [CallLangWF P] [LawfulMonad m] in
/-- A call stopped after its completed body: inside its postcondition events
    (`InterruptedSound.postThrow`), or after them (`InterruptedSound.inCallExit`). -/
private theorem callErr_post (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2 = ev :: obs.trace st)
    {n : String} {tyArgs : Option (List P.Ty)}
    {args : List (CallArg P)} {md : MetaData P} {env : IEnv P}
    {p : Procedure P (CmdExt P) Hdr} {i o : List P.Expr} {vi vo : List P.Val} {σf : RStore P}
    {cfgr : obs.Cfg} {st s s2 st' : obs.St} {u : Unit} {bevs : List (IEvent P)}
    {res : Except StopReason Unit}
    (hπ : typeInstantiatedCallee π n tyArgs = some p) (hno : p.body.isOpaque = false)
    (hE : CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo))
    (habs : InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo)
    (hpre : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions)).forM (InterpEffects.emit (P := P))) cfgr st
        = (.ok u, s))
    (B : BigStepE π p.body ⟨callEntryStore p vi vo, F⟩ (InterpLang.absStore F σf)
        (bevs.map (REvent.abs F)))
    (t : obs.trace s2 = bevs.reverse ++ obs.trace s)
    (hpost : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) σf
        p.spec.postconditions).forM (InterpEffects.emit (P := P))) cfgr s2 = (res, st')) :
    ∃ revs : List (IEvent P),
        InterruptedSound π (.stmt (.cmd (.call n tyArgs args md)) (env.abs F))
        (revs.map (REvent.abs F)) ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  have hpa :=
    rDefaultAssertEvents_abs F (callEntryStore p i o) (checksAtCall md p.spec.preconditions)
  rw [habs] at hpa
  have hq := rDefaultAssertEvents_abs F σf p.spec.postconditions
  rcases res with r | u2
  · obtain ⟨pref, hpref, u3⟩ := obs_forM_emit_err obs hemitStep cfgr _ _ _ _ hpost
    have hpref' := hpref.map (REvent.abs F)
    rw [hq] at hpref'
    refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
      (checksAtCall md p.spec.preconditions) ++ bevs ++ pref, ?_,
      by simp [u3, t, obs_forM_emit obs _ _ _ _ _ hpre]⟩
    rw [List.map_append, List.map_append, hpa, ← List.nil_append (defaultAssertEvents ..)]
    exact .postThrow (env := env.abs F) (.refl _) .here hπ hno hE B hpref'
  · refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
      (checksAtCall md p.spec.preconditions) ++ bevs ++
      rDefaultAssertEvents (InterpLang.rfactory F) σf p.spec.postconditions, ?_,
      by simp [obs_forM_emit obs _ _ _ _ _ hpost, t, obs_forM_emit obs _ _ _ _ _ hpre]⟩
    rw [List.map_append, List.map_append, hpa, hq, ← List.nil_append (defaultAssertEvents ..)]
    exact .inCallExit (env := env.abs F) (.refl _) .here hπ hno hE B

omit [CallLangWF P] [LawfulMonad m] [HasOldIdent P] in
/-- A throwing contract run of an opaque callee (`runAbstractCallee`) over the output formals
    `xs`, at a well-formed factory (`FactoryWF`), from an entry frame that denotes a well-formed,
    typed store (`CallEnvOk`), for an observation whose `emit` always records its event and whose
    throwing `choose` leaves the trace unchanged, recorded no event (it stopped while havocking),
    or a prefix of the assumption events of `post` at a frame reached from the entry frame by a
    reference `HavocVars` of `xs`. -/
private theorem runAbstractCallee_err [CallLangWF P] (obs : InterpObs P m)
    (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2 = ev :: obs.trace st)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    {fuel : Nat} {xs : List P.Ident} {post : ListMap String (Check P)} {σ : RStore P}
    {cfgr : obs.Cfg} {st st' : obs.St} {r : StopReason}
    (hd : RStore.Denoting F σ) (henv : CallEnvOk F (InterpLang.absStore F σ))
    (h : obs.run (runAbstractCallee fuel (InterpLang.rfactory F) xs post σ) cfgr st =
      (.error r, st')) :
    obs.trace st' = obs.trace st ∨ ∃ (σO : RStore P) (pref : List (IEvent P)),
      HavocVars F (InterpLang.absStore F σ) xs (InterpLang.absStore F σO) ∧
      pref <+: rAssumeEvents (InterpLang.rfactory F) σO post ∧
      obs.trace st' = pref.reverse ++ obs.trace st := by
  simp only [runAbstractCallee, obs.run_bind] at h
  split at h
  · rename_i σO s1 h1
    obtain ⟨H, -, -, t⟩ := havocVarList_sound obs hEval hfac _ _ _ _ _ _ _ h1
      (by simpa using hd) (by simpa using henv)
    simp only [IStore.get_ofStore] at H
    split at h
    · simp [obs.run_pure] at h
    · rename_i s2 h2
      obtain ⟨pref, hpref, u⟩ := obs_forM_emit_err obs hemitStep cfgr _ _ _ _ h2
      exact .inr ⟨_, pref, H, hpref, (Prod.mk.inj h).2 ▸ u.trans (by rw [t])⟩
  · rename_i s1 h1
    exact .inl ((Prod.mk.inj h).2 ▸ obs_havocVarList_trace obs hchooseErr _ _ _ _ _ _ _ _ h1)

omit [CallLangWF P] [LawfulMonad m] in
/-- A call to an opaque callee stopped after havocking its outputs, inside its postcondition
    assumption events or after them: `InterruptedSound.inAbstractCall`. -/
private theorem callErr_abstract (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {n : String} {tyArgs : Option (List P.Ty)} {args : List (CallArg P)} {md : MetaData P}
    {env : IEnv P}
    {p : Procedure P (CmdExt P) Hdr} {i o : List P.Expr} {vi vo : List P.Val} {σf : RStore P}
    {cfgr : obs.Cfg} {st s st' : obs.St} {u : Unit} {pref : List (IEvent P)}
    (hπ : typeInstantiatedCallee π n tyArgs = some p) (hab : p.body.isOpaque = true)
    (hE : CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo))
    (habs : InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo)
    (hpre : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions)).forM (InterpEffects.emit (P := P))) cfgr st
        = (.ok u, s))
    (H : HavocVars F (callEntryStore p vi vo) (ProcedureHeader.outputParams (P := P) p.header)
        (InterpLang.absStore F σf))
    (hpref : pref <+: rAssumeEvents (InterpLang.rfactory F) σf p.spec.postconditions)
    (t : obs.trace st' = pref.reverse ++ obs.trace s) :
    ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd (.call n tyArgs args md)) (env.abs F))
        (revs.map (REvent.abs F)) ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  have hpa :=
    rDefaultAssertEvents_abs F (callEntryStore p i o) (checksAtCall md p.spec.preconditions)
  rw [habs] at hpa
  have hpref' := hpref.map (REvent.abs F)
  rw [rAssumeEvents_abs] at hpref'
  refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
    (checksAtCall md p.spec.preconditions) ++ pref, ?_,
    by simp [t, obs_forM_emit obs _ _ _ _ _ hpre]⟩
  rw [List.map_append, hpa, ← List.nil_append (defaultAssertEvents ..)]
  exact .inAbstractCall (env := env.abs F) (.refl _) .here hπ
    (by cases hb : p.body <;> simp_all) hE H hpref'

omit [CallLangWF P] [LawfulMonad m] in
/-- A call to an opaque callee stopped while havocking its outputs, after its precondition
    events: `InterruptedSound.preThrow` with every precondition event. -/
private theorem callErr_havoc (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {n : String} {tyArgs : Option (List P.Ty)} {args : List (CallArg P)} {md : MetaData P}
    {env : IEnv P}
    {p : Procedure P (CmdExt P) Hdr} {i o : List P.Expr} {vi vo : List P.Val}
    {cfgr : obs.Cfg} {st s st' : obs.St} {u : Unit}
    (hπ : typeInstantiatedCallee π n tyArgs = some p)
    (hE : CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo))
    (habs : InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo)
    (hpre : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions)).forM (InterpEffects.emit (P := P))) cfgr st
        = (.ok u, s))
    (t : obs.trace st' = obs.trace s) :
    ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd (.call n tyArgs args md)) (env.abs F))
        (revs.map (REvent.abs F)) ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
    (checksAtCall md p.spec.preconditions), ?_, by simp [t, obs_forM_emit obs _ _ _ _ _ hpre]⟩
  rw [rDefaultAssertEvents_abs, habs]
  simpa [IEnv.abs] using InterruptedSound.preThrow (outerEvs := []) (env := env.abs F) (.refl _)
    .here hπ hE List.prefix_rfl

omit [LawfulMonad m] in
/-- At every stepper fuel `k` and call-depth budget `d`, for an observation whose `emit` always
    records its event and whose throwing `choose` leaves the trace unchanged, and if every procedure
    of `π` is well-formed (`ProcsOk π`): a throwing step `stepCmd π .contract d k` of a command from
    a configuration with a well-formed factory (`FactoryWF`) satisfying the invariant `CfgInv π`
    (the replay invariant on the stores and the call sites) recorded events certified by
    `InterruptedSound π` (the events of a reference run, possibly stopped inside a call) from that
    command's configuration. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem call_cmd_errArm [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2
          = ev :: obs.trace st)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st) :
    ∀ (k d : Nat) (cmd : CmdExt P) (env : IEnv P)
      (cfgr : obs.Cfg) (st st' : obs.St) (r : StopReason),
      obs.run (stepCmd π .contract d k env cmd) cfgr st = (.error r, st') →
      FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
      ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  intro k
  induction k with
  | zero =>
    intro _ c _ cfgr _ _ _ h _ _ _ _
    cases c
    · exact obs_stepCmd_base_err (F := F) obs π hemitStep hchooseErr h
    · rw [stepCmd, stepCmdWith] at h
      simp only [CmdExt.view, dispatchCall, obs.run_throw, Prod.mk.injEq] at h
      exact ⟨[], .clean (.refl _), by rw [← h.2]; rfl⟩
  | succ k ih =>
  intro d c env cfgr st st' r h hf hd hrf hi
  cases c
  · exact obs_stepCmd_base_err (F := F) obs π hemitStep hchooseErr h
  cases d
  · rw [stepCmd, stepCmdWith] at h
    simp only [CmdExt.view, dispatchCall, obs.run_throw, Prod.mk.injEq] at h
    exact ⟨[], .clean (.refl _), by rw [← h.2]; rfl⟩
  rename_i n tyArgs args md d
  have ih := ih d
  have A := fun k => call_cmd_arm obs π hprocs hEval (F := F) k d
  rw [stepCmd, stepCmdWith] at h
  simp only [CmdExt.view, dispatchCall, callBody] at h
  repeat' first
    | rw [obs_run_throw_bind] at h
    | split at h
    | simp only [obs.run_bind, obs.run_pure, obs.run_throw] at h
  all_goals cases h
  all_goals try exact ⟨[], .clean (.refl _), rfl⟩
  all_goals
    have hπ := (congrArg (fun o => Option.bind o
        (ProcedureTypeInstantiation.instantiate · (tyArgs.getD []))) ‹π n = some _›).trans
      ‹ProcedureTypeInstantiation.instantiate _ (tyArgs.getD []) = some _›
    change typeInstantiatedCallee π n tyArgs = _ at hπ
    obtain ⟨vi, vo, hreli, hrelo, hE, hen, hdEntry, habsEntry⟩ :=
      callEntry_ok π hprocs hEval hf hd hrf hi ‹_› ‹_› ‹_› ‹_› ‹_›
    rw [hrf] at *
    first
      | (have hY := runAbstractCallee_sound obs hEval hf (σ := callEntryStore _ _ _) hdEntry
            (habsEntry ▸ hen) ‹obs.run (runAbstractCallee _ _ _ _ _) _ _ = (.ok _, _)›
         obtain ⟨H, -, -, t⟩ := hY
         rw [habsEntry] at H
         exact callErr_abstract obs π ‹_› ‹_› hE habsEntry ‹_› H List.prefix_rfl t)
      | (have hY := runAbstractCallee_err obs hEval hf hemitStep hchooseErr
            (σ := callEntryStore _ _ _) hdEntry (habsEntry ▸ hen)
            ‹obs.run (runAbstractCallee _ _ _ _ _) _ _ = (.error _, _)›
         rcases hY with t | ⟨_, _, H, hpref, t⟩
         · exact callErr_havoc obs π ‹_› hE habsEntry ‹_› t
         · rw [habsEntry] at H
           exact callErr_abstract obs π ‹_› ‹_› hE habsEntry ‹_› H hpref t)
      | (obtain ⟨bevs, B, -, -, t⟩ := runCallee_ok obs π hprocs hEval (fun _ => A k) ‹_› hf hdEntry
            (habsEntry ▸ hen) ‹obs.run (runCallee _ _ _ _ _ _) _ _ = (.ok _, _)›
         rw [habsEntry] at B
         exact callErr_post obs π hemitStep ‹_› (by simpa using ‹¬(Body.isOpaque _) = true›) hE
           habsEntry ‹_› B t ‹_›)
      | (obtain ⟨crevs, hc, u⟩ := runCallee_err obs π hprocs hEval hchooseErr (fun _ => A k) ih ‹_›
            hf hdEntry (habsEntry ▸ hen) ‹¬(Body.isOpaque _) = true›
            ‹obs.run (runCallee _ _ _ _ _ _) _ _ = (.error _, _)›
         exact callErr_body obs π ‹_› hE habsEntry ‹_› hc u)
      | exact callErr_pre obs π hemitStep ‹_› hE habsEntry ‹_›

end CallErrDischarge

/-! ## Replay soundness for `CmdExt P` -/

section CallReplay

/-- Replay soundness for a run that completes: if every procedure of `π` is well-formed
    (`ProcsOk π`: distinct frame formals, and a structured body that is exit-covered, declares no
    function and has only well-formed call sites), the Boolean literals denote the Boolean values
    (`InterpLangBool`), the bounded evaluator is sound up to denotation at `F`
    (`BoundedEvalSoundAt`), the counterexample's configuration denotes and is tracked under a
    well-formed factory `F` (`FactoryWF`) and its image satisfies the invariant `CfgInv π`, and the
    strict replay run of `runCallInterp π` at fuel `fuel` from the counterexample's configuration
    returns `.ok`, then a counterexample classified `genuine` has a reference run recording the
    images of runtime events one of which fails the target assertion (`ReplaySound`). -/
theorem call_replaySound_of_ok [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F))
    (d : Nat)
    (hok : ∃ final, (runReplayRun (runCallInterp (m := ReplayM P) π .contract fuel cex.cfg d)
          { oracleConfig := .strict }
          cex.oracle).1 = .ok final) :
    ReplaySound π target fuel F cex d := by
  intro hg
  obtain ⟨final, hf⟩ := hok
  obtain ⟨ev, hmem, hhalt⟩ := (genuine_iff ..).1 hg
  obtain ⟨revs, hs, -, htr⟩ := call_replayRun_sound π hprocs _ F hEval _ _ ⟨hd, ht, rfl⟩ final _ _ _
    d (Prod.ext hf rfl) hfac hinv
  exact ⟨revs, _, hs, ev, List.mem_reverse.1 (htr ▸ hmem), hhalt⟩

/-- An erroring `choose` in `ReplayM` leaves `traceRev` unchanged. -/
private theorem replayRun_choose_err {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (factory : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
    (cfg : ReplayCfg P) (st : ReplayState P) (e : StopReason)
    (st' : ReplayState P)
    (h : replayRun (InterpEffects.choose (P := P) factory store ty) cfg st
        = (.error e, st')) :
    st'.traceRev = st.traceRev := by eff_inv [] <;> rfl

/-- **Whole-run interrupted soundness.**  If every procedure of `π` is well-formed (`ProcsOk π`),
    the Boolean literals denote the Boolean values (`InterpLangBool`), the bounded evaluator is
    sound up to denotation at `F` (`BoundedEvalSoundAt`), and `start` satisfies the invariant
    `CfgInv π` at a well-formed factory `F` (`FactoryWF`), then for any outcome of a replay run from
    a runtime configuration `istart` that denotes `start` under `F` (`IConfig.Denotes`), including a
    throw inside a callee, the images (`REvent.abs F`) of the recorded events are certified by
    `InterruptedSound` (they are the events of a reference run, possibly stopped inside a call). -/
theorem call_replayRun_interruptedSound [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (fuel : Nat) (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (start : Config P (CmdExt P))
    (istart : IConfig P (CmdExt P))
    (hstart : istart.Denotes F start)
    (cfg : ReplayCfg P) (oracle : List P.Expr)
    (res : Except StopReason (IConfig P (CmdExt P))) (st' : ReplayState P) (d : Nat)
    (hrun : runReplayRun (runCallInterp (m := ReplayM P) π .contract fuel istart d) cfg oracle
        = (res, st'))
    (hfac : FactoryWF (P := P) F) (hinv : CfgInv π start) :
    ∃ revs : List (IEvent P), InterruptedSound π start (revs.map (REvent.abs F)) ∧
      st'.traceRev = revs.reverse := by
  have hclean : ∀ (F : P.Factory) (c : Config P (CmdExt P)) (evs : List (Event P))
      (mid : Config P (CmdExt P)), StepStmtStarE P (EvalCommandET π) c evs mid →
      InterruptedSound π c evs := fun _ _ _ _ hs => .clean (stepStarET_toE π hs)
  obtain ⟨revs, hcert, htr⟩ := runInterp_traceSound_generic obsReplay _ (EvalCommandET π) _
    (fun _ => InterruptedSound π) hclean
    (fun _ _ _ _ _ hs hr => interruptedSound_stepThen π _ _ _ _ (stepET_toE π hs) hr)
    (callStepInterpSound _ π hprocs d)
    (stepInterpErrInto_of_arms _ _ _ _ _ (hclean F) (cfgInv_seq _) (cfgInv_block _)
      (interruptedSound_seq _) (interruptedSound_block _) replayRun_choose_err
      (fun F k _ _ _ _ _ _ h hf hE => call_cmd_errArm _ π hprocs hE
        (fun _ _ _ => congrArg _ (replayRun_emit_state ..)) replayRun_choose_err (F := F) k d
          _ _ _ _ _ _ h hf))
    F _ _ _ _ _ _ hrun hfac hEval hstart.1 (hstart.2.2 ▸ hinv) hstart.2.1
  exact ⟨revs, hstart.2.2 ▸ hcert, by simpa [obsReplay] using htr⟩

/-- **Production replay soundness with prompt stopping.** If every procedure of `π` is well-formed
    (`ProcsOk π`), the Boolean literals denote the Boolean values (`InterpLangBool`), the bounded
    evaluator is sound up to denotation at `F` (`BoundedEvalSoundAt`), and the counterexample's
    configuration denotes and is tracked under a well-formed factory `F` (`FactoryWF`) and its image
    satisfies the invariant `CfgInv π`, then at `interruptOn := targetInterrupt target fuel` (stop
    at the target), the images of the recorded events of a `.genuine` verdict of the replay from the
    counterexample's configuration are certified by `InterruptedSound` (the events of a reference
    run, possibly stopped inside a call), and the recorded events contain one failing the target
    assertion (`assertFailureHalt`); no run-completion premise is needed. -/
theorem call_replaySound_interruptOn [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F))
    (fuel d : Nat)
    (hg : (runReplay (runCallInterp (m := ReplayM P) π .contract fuel cex.cfg d)
            { interruptOn := targetInterrupt target fuel,
              oracleConfig := .strict } (assertFailureHalt target fuel) cex.oracle).1 = .genuine) :
    ∃ (revs : List (IEvent P)),
      InterruptedSound π (cex.cfg.abs F) (revs.map (REvent.abs F)) ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true := by
  obtain ⟨_, hmem, hhalt⟩ := (runReplay_genuine_iff ..).1 hg
  obtain ⟨revs, hcert, htr⟩ := call_replayRun_interruptedSound π hprocs _ F hEval _ _ ⟨hd, ht, rfl⟩
    _ _ _ _ _ rfl hfac hinv
  exact ⟨revs, hcert, _, List.mem_reverse.1 (htr ▸ hmem), hhalt⟩

/-! ## Replay soundness without a run-completion premise -/

/-- If every procedure of `π` is well-formed (`ProcsOk π`), the Boolean literals denote the Boolean
    values (`InterpLangBool`), the bounded evaluator is sound up to denotation at `F`
    (`BoundedEvalSoundAt`), and the counterexample's configuration denotes and is tracked under a
    well-formed factory `F` (`FactoryWF`) and its image satisfies the invariant `CfgInv π`, a
    counterexample classified `genuine` has a list of runtime events whose images are certified by
    `InterruptedSound` (the events of a reference run, possibly stopped inside a call) and one of
    which fails the target assertion (`assertFailureHalt target fuel`). -/
theorem call_replaySound_general [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F)) (d : Nat)
    (hg : genuine π target fuel cex d) :
    ∃ (revs : List (IEvent P)),
      InterruptedSound π (cex.cfg.abs F) (revs.map (REvent.abs F)) ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true := by
  obtain ⟨_, hmem, hhalt⟩ := (genuine_iff ..).1 hg
  obtain ⟨revs, hcert, htr⟩ := call_replayRun_interruptedSound π hprocs _ F hEval _ _ ⟨hd, ht, rfl⟩
    _ _ _ _ _ rfl hfac hinv
  exact ⟨revs, hcert, _, List.mem_reverse.1 (htr ▸ hmem), hhalt⟩

/-! ### `TargetNotInProcs`: the target id occurs in no procedure of `π`

Under `TargetNotInProcs π target`, no event a callee contributes reaches the target, so a
target-reaching event of an `InterruptedSound` certificate lies in its flat outer prefix. -/

/-- A command that does not *reach* `target` in the sense of `targetReached`:
    it is not an `assert`/`cover` whose label and metadata both equal `target`'s. -/
@[expose] def cmdAvoidsTarget (target : AssertId P) : CmdExt P → Bool
  | .cmd (.assert l _ md) => !(target.label == l && decide (target.md = md))
  | .cmd (.cover l _ md) => !(target.label == l && decide (target.md = md))
  | _ => true

/-- No spec clause of `checks` has both `target`'s label and `target`'s metadata. -/
@[expose] def ChecksAvoidTarget (target : AssertId P)
    (checks : ListMap String (Check P)) : Prop :=
  ∀ lc ∈ checks.toList, ¬ (target.label = lc.1 ∧ target.md = lc.2.md)

/-- **The target id occurs in no procedure of `π`**: for every `p` a call can run (`π`'s procedure
    instantiated at the call's type arguments), no pre- or postcondition clause of `p` has
    `target`'s label and metadata, and no `assert`/`cover` command of `p`'s body does: anywhere in a
    structured body (nested `block`/`ite`/`loop` bodies included, via `Block.allCmds`), and in any
    block of a CFG body. -/
@[expose] def TargetNotInProcs (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) : Prop :=
  ∀ n tyArgs p, typeInstantiatedCallee π n tyArgs = some p →
    (∀ callMd, ChecksAvoidTarget target (checksAtCall callMd p.spec.preconditions)) ∧
    ChecksAvoidTarget target p.spec.postconditions ∧
    (∀ ss opq, p.body = .structured ss opq → Block.allCmds (cmdAvoidsTarget target) ss = true) ∧
    ∀ g opq, p.body = .cfg g opq → g.allCmds (cmdAvoidsTarget target)

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [CallLangWF P] [HasOldIdent P]
    [ProcedureHeader P Hdr] in
omit [InterpLang P] in
/-- The empty procedure table satisfies `TargetNotInProcs` for every target. -/
theorem targetNotInProcs_none (target : AssertId P) :
    TargetNotInProcs (Hdr := Hdr) (fun _ => none) target := nofun

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [CallLangWF P] [HasOldIdent P] [InterpLang P] in
/-- The assertion events of spec clauses that avoid `target` do not reach `target`. -/
private theorem defaultAssertEvents_avoid (target : AssertId P)
    (fac : P.Factory) (σ : SemanticStore P) (checks : ListMap String (Check P))
    (h : ChecksAvoidTarget target checks) :
    ∀ e ∈ defaultAssertEvents fac σ checks, targetReachedE target e = false := by
  grind [defaultAssertEvents, targetReachedE, ChecksAvoidTarget]

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [CallLangWF P] [HasOldIdent P] [InterpLang P] in
/-- Assumption events never reach a target. -/
private theorem assumeEvents_avoid (target : AssertId P)
    (fac : P.Factory) (σ : SemanticStore P) (checks : ListMap String (Check P)) :
    ∀ e ∈ assumeEvents fac σ checks, targetReachedE target e = false := by
  grind [assumeEvents, targetReachedE]

omit [HasFvars P] [CallLangWF P] [HasOldIdent P] [InterpLang P] in
/-- A base command that avoids `target` emits no event reaching `target`. -/
private theorem evalCmdE_avoid (target : AssertId P)
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P}
    {evs : Trace P}
    (h : EvalCmdE (P := P) fac σ c σ' evs)
    (hq : cmdAvoidsTarget target (.cmd c) = true) :
    ∀ e ∈ evs, targetReachedE target e = false := by
  cases h <;> unfold cmdAvoidsTarget at hq <;> grind [targetReachedE]

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, a reference evaluation of a command that avoids the target emits no
    target-reaching event. -/
private theorem evalCommandE_avoid
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : CmdExt P} {evs : Trace P}
    (h : EvalCmdExtE π fac σ c σ' evs)
    (hq : cmdAvoidsTarget target c = true) :
    ∀ e ∈ evs, targetReachedE target e = false := by
  revert hq
  refine EvalCmdViewE.rec
    (motive_1 := fun b _ _ l _ =>
      (∀ ss opq, b = .structured ss opq → Block.allCmds (cmdAvoidsTarget target) ss) →
      (∀ g opq, b = .cfg g opq → g.allCmds (cmdAvoidsTarget target)) →
        l.all (!targetReachedE target ·))
    (motive_3 := fun c l _ _ =>
      c.allCmds (cmdAvoidsTarget target) → l.all (!targetReachedE target ·))
    (motive_4 := fun c l _ _ =>
      c.allCmds (cmdAvoidsTarget target) → l.all (!targetReachedE target ·))
    (motive_5 := fun c l _ _ =>
      c.allCmds (cmdAvoidsTarget target) → l.all (!targetReachedE target ·))
    (motive_6 := fun c l c' _ =>
      c.allCmds (cmdAvoidsTarget target) → l.all (!targetReachedE target ·) ∧
        c'.allCmds (cmdAvoidsTarget target))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;> intros <;>
  (try (obtain ⟨_, rfl, _⟩ :=
            CmdExt.sem_kind_call_callee (π := π)
              ‹(Calls.CmdExt.sem (Hdr := Hdr)).kind _ = .call _ _ _ _› ‹π _ = some _› ‹_ = some _›))
    <;>
  (try (obtain rfl :=
            Calls.CmdExt.sem_kind_base ‹(Calls.CmdExt.sem (Hdr := Hdr)).kind _ = .base _›)) <;>
  grind [Config.allCmds, Stmt.allCmds, evalCmdE_avoid, defaultAssertEvents_avoid,
    assumeEvents_avoid, Calls.CmdExt.sem_kind_ne_ext,
    stepStmtE_preserves_allCmds, TargetNotInProcs, CFGConfig.allCmds, CFG.allCmds]

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, a reference run from a target-avoiding configuration emits no
    target-reaching event. -/
private theorem stepStarE_avoid
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {c c' : Config P (CmdExt P)} {evs : Trace P}
    (h : StepStmtStarE P (EvalCmdExtE π) c evs c')
    (hall : c.allCmds (cmdAvoidsTarget target)) :
    ∀ e ∈ evs, targetReachedE target e = false := by
  induction h
  nofun
  rename_i hs hr ih
  have hrest := ih (stepStmtE_preserves_allCmds _ hs hall)
  clear hr
  induction hs <;> grind [Config.allCmds, Stmt.allCmds, evalCommandE_avoid]

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, a CFG reference run over `EvalCmdExtE π` from a configuration whose
    remaining commands avoid the target emits no target-reaching event and ends in a configuration
    whose remaining commands avoid the target. -/
private theorem stepCFGStarE_avoid
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {c c' : CFGConfig String (CmdExt P) P} {evs : Trace P}
    (h : StepCFGStarE P (EvalCmdExtE π) c evs c') (hc : c.allCmds (cmdAvoidsTarget target)) :
    (∀ e ∈ evs, targetReachedE target e = false) ∧ c'.allCmds (cmdAvoidsTarget target) := by
  induction h with
  | refl => exact ⟨nofun, hc⟩
  | step _ _ _ _ _ hs _ ih =>
    cases hs with
    | step_cmd he =>
      simp only [CFGConfig.allCmds, List.all_cons, Bool.and_eq_true] at hc
      grind [evalCommandE_avoid, CFGConfig.allCmds]
    | _ => grind [CFGConfig.allCmds, CFG.allCmds]

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, a reference execution `BigStepE` of the body of a procedure of `π`
    emits no target-reaching event. -/
private theorem bigStepE_avoid
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {n : String} {tyArgs : Option (List P.Ty)} {p : Procedure P (CmdExt P) Hdr}
    (hp : typeInstantiatedCallee π n tyArgs = some p)
    {ρ : Env P} {σ' : SemanticStore P} {evs : Trace P}
    (h : BigStepE π p.body ρ σ' evs) :
    ∀ e ∈ evs, targetReachedE target e = false := by
  obtain ⟨-, -, hs, hc⟩ := hπ n tyArgs p hp
  revert h
  cases hb : p.body with
  | structured ss =>
    rintro ⟨R⟩
    exact stepStarE_avoid π target hπ R (by simpa [Config.allCmds, Stmt.allCmds] using hs ss _ hb)
  | cfg g =>
    intro h
    cases h with
    | cfg R => exact (stepCFGStarE_avoid π target hπ R (hc g _ hb)).1
  | abstract => intro h; cases h

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, an `InterruptedSound` certificate from a target-avoiding configuration
    has no target-reaching event. -/
private theorem interruptedSound_avoid
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {start : Config P (CmdExt P)} {evs : Trace P}
    (h : InterruptedSound π start evs)
    (hall : start.allCmds (cmdAvoidsTarget target)) :
    ∀ e ∈ evs, targetReachedE target e = false := by
  induction h with
  | inCallCfg R _ hp hb _ hc =>
    have hC := (stepCFGStarE_avoid π target hπ hc ((hπ _ _ _ hp).2.2.2 _ _ hb)).1
    grind [stepStarE_avoid, defaultAssertEvents_avoid, TargetNotInProcs]
  | inCallCfgCmd R _ hp hb _ hc _ ih =>
    obtain ⟨hC, hr⟩ := stepCFGStarE_avoid π target hπ hc ((hπ _ _ _ hp).2.2.2 _ _ hb)
    simp only [CFGConfig.allCmds, List.all_cons, Bool.and_eq_true] at hr
    have hI := ih (by simpa [Config.allCmds, Stmt.allCmds] using hr.2.1)
    grind [stepStarE_avoid, defaultAssertEvents_avoid, TargetNotInProcs]
  | inCallExit R _ hp _ _ hB =>
    have hC := bigStepE_avoid π target hπ hp hB
    grind [stepStarE_avoid, defaultAssertEvents_avoid, TargetNotInProcs]
  | postThrow R _ hp _ _ hB _ =>
    have hC := bigStepE_avoid π target hπ hp hB
    grind [stepStarE_avoid, defaultAssertEvents_avoid, TargetNotInProcs]
  | _ => grind [stepStarE_avoid, defaultAssertEvents_avoid, assumeEvents_avoid, TargetNotInProcs,
      Config.allCmds, Stmt.allCmds, List.IsPrefix.subset]

omit [CallLangWF P] [InterpLang P] in
/-- **Flattening a certificate at a target-reaching event, with the flat trace a prefix.** If the
    target assertion occurs in no procedure of `π` (`TargetNotInProcs π target`), an event of an
    `InterruptedSound` certificate that reaches the target lies in a flat reference run from `start`
    whose events are a prefix of the certificate's: every event a callee contributes is target-free,
    so the event is in the certificate's flat outer prefix. -/
theorem interruptedSound_flatPrefix_of_targetReached
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {start : Config P (CmdExt P)} {evs : Trace P}
    (h : InterruptedSound π start evs)
    {ev : Event P} (hmem : ev ∈ evs) (hreach : targetReachedE target ev = true) :
    ∃ evs' final, StepStmtStarE P (EvalCmdExtE π)
        start evs' final ∧ ev ∈ evs' ∧ evs' <+: evs := by
  have hI := fun s e (h : InterruptedSound π s e) => interruptedSound_avoid π target hπ h
  cases h with
  | inCallCfg R _ hp hb _ hc =>
    have hC := (stepCFGStarE_avoid π target hπ hc ((hπ _ _ _ hp).2.2.2 _ _ hb)).1
    grind [stepStarE_avoid, defaultAssertEvents_avoid, TargetNotInProcs]
  | inCallCfgCmd R _ hp hb _ hc hcert =>
    obtain ⟨hC, hr⟩ := stepCFGStarE_avoid π target hπ hc ((hπ _ _ _ hp).2.2.2 _ _ hb)
    simp only [CFGConfig.allCmds, List.all_cons, Bool.and_eq_true] at hr
    have hD := hI _ _ hcert (by simpa [Config.allCmds, Stmt.allCmds] using hr.2.1)
    grind [stepStarE_avoid, defaultAssertEvents_avoid, TargetNotInProcs]
  | inCallExit R _ hp _ _ hB =>
    have hC := bigStepE_avoid π target hπ hp hB
    grind [stepStarE_avoid, defaultAssertEvents_avoid, TargetNotInProcs]
  | postThrow R _ hp _ _ hB _ =>
    have hC := bigStepE_avoid π target hπ hp hB
    grind [stepStarE_avoid, defaultAssertEvents_avoid, TargetNotInProcs]
  | _ => grind [stepStarE_avoid, defaultAssertEvents_avoid, assumeEvents_avoid, TargetNotInProcs,
      Config.allCmds, Stmt.allCmds, List.IsPrefix.subset]

omit [CallLangWF P] [InterpLang P] in
/-- **Flattening a certificate at a target-reaching event.** If the target assertion occurs in
    no procedure of `π` (`TargetNotInProcs π target`), an
    event of an `InterruptedSound` certificate that reaches the target lies in a flat reference run
    from `start`: every event a callee contributes is target-free, so the event is in the
    certificate's flat outer prefix. -/
private theorem interruptedSound_flat_of_targetReached
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {start : Config P (CmdExt P)} {evs : Trace P}
    (h : InterruptedSound π start evs)
    {ev : Event P} (hmem : ev ∈ evs) (hreach : targetReachedE target ev = true) :
    ∃ evs' final, StepStmtStarE P (EvalCmdExtE π)
        start evs' final ∧ ev ∈ evs' := by
  grind [interruptedSound_flatPrefix_of_targetReached _ _ hπ]

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, the events of an `InterruptedSound` certificate are the events of a
    flat reference run from its start followed by events none of which reaches the target. -/
private theorem interruptedSound_split
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {start : Config P (CmdExt P)} {evs : Trace P}
    (h : InterruptedSound π start evs) :
    ∃ evs' rest final, StepStmtStarE P (EvalCmdExtE π) start evs' final ∧ evs = evs' ++ rest ∧
      ∀ e ∈ rest, targetReachedE target e = false := by
  have hI := fun s e (h : InterruptedSound π s e) => interruptedSound_avoid π target hπ h
  cases h with
  | clean R => exact ⟨_, [], _, R, (List.append_nil _).symm, nofun⟩
  | inCall R _ hp hb _ hc =>
    have hC := hI _ _ hc (by simpa [Config.allCmds, Stmt.allCmds] using (hπ _ _ _ hp).2.2.1 _ _ hb)
    refine ⟨_, _, _, R, List.append_assoc .., ?_⟩
    grind [defaultAssertEvents_avoid, TargetNotInProcs]
  | inCallCfg R _ hp hb _ hc =>
    have hC := (stepCFGStarE_avoid π target hπ hc ((hπ _ _ _ hp).2.2.2 _ _ hb)).1
    refine ⟨_, _, _, R, List.append_assoc .., ?_⟩
    grind [defaultAssertEvents_avoid, TargetNotInProcs]
  | inCallCfgCmd R _ hp hb _ hc hcert =>
    obtain ⟨hC, hr⟩ := stepCFGStarE_avoid π target hπ hc ((hπ _ _ _ hp).2.2.2 _ _ hb)
    simp only [CFGConfig.allCmds, List.all_cons, Bool.and_eq_true] at hr
    have hD := hI _ _ hcert (by simpa [Config.allCmds, Stmt.allCmds] using hr.2.1)
    refine ⟨_, _, _, R, by simp only [List.append_assoc]; rfl, ?_⟩
    grind [defaultAssertEvents_avoid, TargetNotInProcs]
  | inCallExit R _ hp _ _ hB =>
    have hC := bigStepE_avoid π target hπ hp hB
    refine ⟨_, _, _, R, by simp only [List.append_assoc]; rfl, ?_⟩
    grind [defaultAssertEvents_avoid, TargetNotInProcs]
  | preThrow R _ hp _ hpre =>
    refine ⟨_, _, _, R, rfl, fun e he => ?_⟩
    exact defaultAssertEvents_avoid _ _ _ _ ((hπ _ _ _ hp).1 _) e (hpre.subset he)
  | postThrow R _ hp _ _ hB hpost =>
    have hC := bigStepE_avoid π target hπ hp hB
    have hQ := fun e he => defaultAssertEvents_avoid _ _ _ _ (hπ _ _ _ hp).2.1 e (hpost.subset he)
    refine ⟨_, _, _, R, by simp only [List.append_assoc]; rfl, ?_⟩
    grind [defaultAssertEvents_avoid, TargetNotInProcs]
  | inAbstractCall R _ hp _ _ _ hpost =>
    have hQ := fun e he => assumeEvents_avoid target _ _ _ e (hpost.subset he)
    refine ⟨_, _, _, R, List.append_assoc .., ?_⟩
    grind [defaultAssertEvents_avoid, TargetNotInProcs]

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [CallLangWF P] [HasOldIdent P] in
/-- The semantic image of a runtime event reaches the target exactly when the event does. -/
private theorem targetReachedE_abs (target : AssertId P) (F : P.Factory) (e : IEvent P) :
    targetReachedE target (REvent.abs F e) = targetReached target e := by
  cases e <;> rfl

omit [CallLangWF P] in
/-- Under `TargetNotInProcs`, a certificate of the images of runtime events `revs` containing a
    target-reaching event `ev` has a prefix of `revs` that contains `ev` and whose images are the
    events of a flat reference run from its start. -/
private theorem interruptedSound_flatRuntime
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target) {F : P.Factory}
    {start : Config P (CmdExt P)} {revs : List (IEvent P)}
    (h : InterruptedSound π start (revs.map (REvent.abs F)))
    {ev : IEvent P} (hmem : ev ∈ revs) (hreach : targetReached target ev = true) :
    ∃ pre final, StepStmtStarE P (EvalCmdExtE π) start (pre.map (REvent.abs F)) final ∧
      ev ∈ pre ∧ pre <+: revs := by
  obtain ⟨evs', rest, final, R, heq, hrest⟩ := interruptedSound_split π target hπ h
  have hpre : evs' = (revs.take evs'.length).map (REvent.abs F) := by
    rw [List.map_take, heq, List.take_left]
  have hsuf : rest = (revs.drop evs'.length).map (REvent.abs F) := by
    rw [List.map_drop, heq, List.drop_left]
  refine ⟨_, final, hpre ▸ R, ?_, List.take_prefix _ _⟩
  rw [← List.take_append_drop evs'.length revs, List.mem_append] at hmem
  refine hmem.resolve_right fun hd => ?_
  have hr := hrest _ (hsuf ▸ List.mem_map_of_mem hd)
  rw [targetReachedE_abs, hreach] at hr
  cases hr

/-- **Replay soundness** (`ReplaySound`): if every procedure of `π` is well-formed (`ProcsOk π`:
    distinct frame formals, and a structured body that is exit-covered and has only well-formed call
    sites), the Boolean literals denote the Boolean values (`InterpLangBool`), the bounded evaluator
    is sound up to denotation at `F` (`BoundedEvalSoundAt`), the counterexample's configuration
    denotes and is tracked under a well-formed factory `F` (`FactoryWF`) and its image satisfies the
    invariant `CfgInv π` (the replay invariant on the stores and the call sites), and the target
    assertion occurs in no procedure of `π` (`TargetNotInProcs π target`), then a counterexample
    classified `genuine` has a reference run recording the images of runtime events one of which
    fails the target assertion. -/
theorem call_replaySound [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F))
    (htgt : TargetNotInProcs π target) (d : Nat) :
    ReplaySound π target fuel F cex d := by
  intro hg
  obtain ⟨revs, hcert, ev, hmem, hhalt⟩ :=
    call_replaySound_general π _ _ _ hprocs F hEval hfac hd ht hinv d hg
  obtain ⟨pre, final, R, hev, -⟩ := interruptedSound_flatRuntime π target htgt hcert hmem
    (targetReached_of_assertFailureHalt _ _ _ hhalt)
  exact ⟨pre, final, R, ev, hev, hhalt⟩

/-- **Feasibility-aware replay soundness** (`ReplaySoundFeasible`): under the hypotheses of replay
    soundness (every procedure of `π` well-formed, `ProcsOk π`; Boolean literals denoting the
    Boolean values, `InterpLangBool`; a bounded evaluator sound up to denotation at `F`,
    `BoundedEvalSoundAt`; the counterexample's configuration denoting and tracked under a
    well-formed factory `F`, `FactoryWF`, with its image satisfying the invariant `CfgInv π`; the
    target assertion in no procedure of `π`, `TargetNotInProcs π target`), a counterexample
    classified `genuineEnforced` has a reference run recording the images of runtime events one of
    which fails the target assertion and whose `.assume` events all evaluate to `tt`
    (`PathFeasible`). -/
theorem call_replaySound_feasible [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F))
    (htgt : TargetNotInProcs π target) (d : Nat) :
    ReplaySoundFeasible π target fuel F cex d := by
  intro hg
  obtain ⟨_, hmem, hhalt⟩ := (runReplay_genuine_iff ..).1 hg
  obtain ⟨revs, hcert, htr⟩ := call_replayRun_interruptedSound π hprocs _ F hEval _ _ ⟨hd, ht, rfl⟩
    _ _ _ _ _ rfl hfac hinv
  obtain ⟨pre, final, R, hev, hpre⟩ := interruptedSound_flatRuntime π target htgt hcert
    (List.mem_reverse.1 (htr ▸ hmem)) (targetReached_of_assertFailureHalt _ _ _ hhalt)
  exact ⟨pre, final, R, ⟨_, hev, hhalt⟩,
    pathFeasible_of_subset (fun _ hx => htr ▸ List.mem_reverse.2 (hpre.subset hx))
      (pathFeasible_of_runReplay_genuine_call _ _ _ _ _ _ hg)⟩

end CallReplay

end Calls

end -- public section

end Imperative
