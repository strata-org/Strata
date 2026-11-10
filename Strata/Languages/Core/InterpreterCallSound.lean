/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterBridgeStatements
public import Strata.DL.Imperative.InterpreterSoundGeneric
public import Strata.Languages.Core.InterpreterSound
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.Languages.Core.InterpreterObs
public import Strata.DL.Imperative.InterpreterCallSound
public import Strata.DL.Imperative.InterpreterCall
public import Strata.Languages.Core.StatementSemanticsProps
public import Strata.Languages.Core.InterpreterReplayProps
public import Strata.DL.Imperative.InterpreterCallProps
public import Strata.Languages.Core.InterpreterProps
import all Strata.Languages.Core.StatementSemanticsProps
import Strata.Languages.Core.InterpreterInterruptBridge
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.Languages.Core.InterpreterBridgeStatements
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.InterpreterReplay
import all Strata.DL.Imperative.CmdSemantics
import all Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterCallSound
import all Strata.DL.Imperative.InterpreterCall
import Strata.Languages.Core.InterpreterReplayTactics
import Strata.Languages.Core.ProcedureProps
public import Strata.Languages.Core.InterpreterProps
import Strata.Languages.Core.InterpreterDomainProps
public import Strata.Languages.Core.InterpreterEvalSound
import Strata.DL.Lambda.LExprEvalFuelProps

/-! # Core `.call` soundness against the reference event semantics

The Core instance of the generic call-aware replay soundness
(`Calls.call_runInterp_sound`, `Calls.call_replaySound`).  Core's stepper `replayStepCmd`
is an abbreviation of the generic `Calls.stepCmd` at `Expression`, and
Core's reference relation `EvalCommandE`/`CoreStepStarE` is the generic
`EvalCmdExtE`/`StepStmtExtStarE` (Core's relations are abbreviations of the generic
ones).  The per-actual, per-command and target checks (`StrictActual`, `TypedActual`,
`CmdCallOk`, `cmdAvoidsTarget`, `ChecksAvoidTarget`, `TargetNotInProcs`) and the active-call
predicate `CallActive` are abbreviations of the generic ones at `Expression`.  This module states
the procedure checks (`ProcOk`, `ProcsOk`, over Core's header fields), the configuration invariant
`CoreCfgInv` and the interrupted-run certificate (`CoreInterruptedSound`) over Core's own
definitions, proves them equivalent to the generic ones, and obtains every soundness theorem as
an instance of its generic counterpart; `core_runCoreInterp_sound_eval` is the `EvalM`
instance of `core_runInterp_sound`.

The side conditions exist because on each axis the reference relation demands more
than the engine's executable functions check:
strict input actuals (`StrictActual`), input actuals whose values are typed
(`TypedActual`: the reference call rule binds formals without a type premise, while
the typed `set` rules read the type of a slot's current value), pairwise-distinct
frame formals, and exit-covered structured callee bodies.

Key theorems: `core_runInterp_sound`, `core_runCoreInterp_sound_eval`, `core_replayRun_sound`,
`core_replayRun_interruptedSound`, `core_replaySound_interruptOn`, `core_replaySound_general`,
`coreInterruptedSound_flatPrefix_of_targetReached`, `core_replaySound` and
`core_replaySound_feasible`. -/

namespace Core

open Imperative

public section

/-- Core's closed typed actuals (`Calls.CallLangWF.closedTyped`): literal constants.
    A constant is a canonical value that evaluates to itself and whose `typeCheck []` is its
    literal type, so its value is a typed value. -/
@[expose] def closedTypedActual : Expression.Expr → Bool
  | .const _ _ => true
  | _ => false

/-- A closed typed actual (a literal constant) that the bounded evaluator reduces evaluates to a
    value of some type. -/
private theorem closedTypedActual_sound (n : Nat) (f : Expression.Factory) (σ : RStore Expression)
    (e r : Expression.Expr) (hc : closedTypedActual e = true)
    (he : InterpLang.boundedEval (P := Expression) n (InterpLang.rfactory f) σ e = some r) :
    ∃ v ty, InterpLang.Denotes f r v ∧ HasVal.valueOfTy f v ty := by
  obtain ⟨m, c, rfl⟩ : ∃ m c, e = .const m c := by
    cases e <;> simp_all [closedTypedActual]
  obtain rfl := Option.some.inj ((evalBounded_const n _ σ m c).symm.trans he)
  exact ⟨_, .forAll [] c.ty, denotes_literal Lambda.LExpr.denoteEval_const,
    rfl, by cases c <;> rfl⟩

/-- Core's expression language satisfies the facts the generic call-aware
    soundness proofs use. -/
instance : Calls.CallLangWF Expression where
  isValue_sound f r v _ hd := isValue_hasVal f r v hd
  evalVal := coreEvaluator_WellFormedSemanticEvalVal
  getFvars_of_getFvar := fun | .fvar .., _, rfl, _, .head _ => rfl
  mem_getFvars_mkFvar := fun _ => .head _
  lawfulHasVal := inferInstance
  ops_typed := replayValueOps_typedSound
  closedTyped := closedTypedActual
  closedTyped_sound := by exact closedTypedActual_sound

/-- The per-actual syntactic check: a bare free variable, or a closed expression
    (`Calls.StrictActual` at `Expression`).  Anything else is rejected, because
    `Expression.eval` is not strict in general (`(fun _ => 3) x` evaluates with `x` unbound), so
    a successful evaluation would not witness `EvalExpressions`' definedness premise. -/
abbrev StrictActual : Expression.Expr → Bool := Calls.StrictActual (P := Expression)

/-- The per-actual typing check: a bare free variable (its value is read from a
    typed store) or a literal constant (`closedTypedActual`, Core's `CallLangWF.closedTyped`), so
    the callee's entry frame is typed (`Calls.TypedActual` at `Expression`). -/
abbrev TypedActual : Expression.Expr → Bool := Calls.TypedActual (P := Expression)

/-- Per-command check on a call site: its input actuals are all strict and all
    `TypedActual`, and its result variables are distinct (`Calls.CmdCallOk` at `Expression`).
    Base commands carry no condition.  The output arity is not a fragment side condition: the
    engine enforces it itself (throwing `programCallOutputArityMismatch`). -/
abbrev CmdCallOk (π : String → Option Procedure) : Command → Bool := Calls.CmdCallOk π

/-- Shallow check on one procedure, mentioning no calls: its frame-binding formals
    are pairwise distinct (what `InitCallFrame` needs), a structured body is
    exit-covered and has well-formed call sites everywhere, and every command of every
    block of a CFG body is a well-formed call site. -/
@[expose] def ProcOk (π : String → Option Procedure) (p : Procedure) : Prop :=
  (ListMap.keys p.header.inputs ++ ListMap.keys p.header.getOutputOnlyParams).Nodup ∧
  (∀ ss, p.body = .structured ss →
    Block.exitsCoveredByBlocks (P := Expression) (CmdT := Command) [] ss ∧
    Block.allCmds (P := Expression) (CmdCallOk π) ss = true) ∧
  ∀ g, p.body = .cfg g → g.allCmds (CmdCallOk π)

/-- Flat program-level check: every procedure `π` resolves satisfies `ProcOk`. -/
@[expose] def ProcsOk (π : String → Option Procedure) : Prop :=
  ∀ n p, π n = some p → ProcOk π p

/-- The configuration invariant Core call-aware replay soundness runs under: a value-only store,
    well-formed call sites, and typed stores (`Config.storeTyped`, needed by the typed `set`
    rules).  Exit coverage is not a conjunct: it does not project from a `.block` configuration
    into its inner one. -/
@[expose] def CoreCfgInv (π : String → Option Procedure) (c : CoreConfig) : Prop :=
  Config.storeWellDefined (P := Expression) c ∧
  Config.allCmds (P := Expression) (CmdCallOk π) c ∧
  Config.storeTyped (P := Expression) c

/-- **The call is the active redex of a config**, stable under the `.seq _ rest` and
    `.block l σ _` evaluation contexts: peeling seq/block wrappers from `C` reaches
    the bare call `.stmt (.cmd (.call pn args md)) env` (`Calls.CallActive` at `Expression`). -/
abbrev CallActive :
    CoreConfig → String → List (Imperative.CallArg Expression) →
      Imperative.MetaData Expression → Imperative.Env Expression → Prop :=
  Calls.CallActive

/-- **The interrupted-run certificate.**  A run interrupted inside a callee records
    `outer-events ++ callee-precondition-events ++ callee-prefix`; the reference
    relation packages a whole call as one atomic `call_sem` step, so there is no flat
    `StepStmtStarE start evs mid` ending mid-callee.  `clean` covers any completed run
    of steps; the other constructors cover the one interrupted call at the tail
    (inside a structured body, recursing on the callee; inside a CFG body, between its
    commands or inside one of them, recursing on the command; at the write-back;
    mid-precondition; mid-postcondition). -/
inductive CoreInterruptedSound (π : String → Option Procedure)
    :
    CoreConfig → Trace Expression → Prop where
  | clean {start : CoreConfig} {evs : Trace Expression} {mid : CoreConfig} :
      StepStmtStarE Expression (EvalCommandE π) start evs mid →
      CoreInterruptedSound π start evs
  | inCall {start : CoreConfig} {outerEvs : Trace Expression} {C : CoreConfig}
      {env : Imperative.Env Expression} {pn : String}
      {args : List (Imperative.CallArg Expression)} {md : Imperative.MetaData Expression}
      {p : Procedure} {σAO : CoreStore} {bodyStmts : List Statement}
      {calleeEvs : Trace Expression} :
      StepStmtStarE Expression (EvalCommandE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      p.body = .structured bodyStmts →
      CallEntry env.factory env.store p args σAO →
      CoreInterruptedSound π
        (.stmt (.block "" bodyStmts #[]) (⟨σAO, env.factory⟩ : Imperative.Env Expression))
        calleeEvs →
      CoreInterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (Imperative.Calls.checksAtCall md p.spec.preconditions) ++ calleeEvs)
  | inCallCfg {start : CoreConfig} {outerEvs : Trace Expression} {C : CoreConfig}
      {env : Imperative.Env Expression} {pn : String}
      {args : List (Imperative.CallArg Expression)} {md : Imperative.MetaData Expression}
      {p : Procedure} {σAO : CoreStore} {g : Imperative.DetCFG Expression Command}
      {cfgEvs : Trace Expression} {mid : CFGConfig String Command Expression} :
      StepStmtStarE Expression (EvalCommandE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      p.body = .cfg g →
      CallEntry env.factory env.store p args σAO →
      StepCFGStarE Expression (EvalCommandE π)
        (.atBlock g g.entry (⟨σAO, env.factory⟩ : Imperative.Env Expression)) cfgEvs mid →
      CoreInterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (Imperative.Calls.checksAtCall md p.spec.preconditions) ++ cfgEvs)
  | inCallCfgCmd {start : CoreConfig} {outerEvs : Trace Expression} {C : CoreConfig}
      {env : Imperative.Env Expression} {pn : String}
      {args : List (Imperative.CallArg Expression)} {md : Imperative.MetaData Expression}
      {p : Procedure} {σAO : CoreStore} {g g' : Imperative.DetCFG Expression Command}
      {cfgEvs : Trace Expression} {t : String} {c : Command} {cs : List Command}
      {tr : DetTransferCmd String Expression} {ρ : Imperative.Env Expression}
      {cmdEvs : Trace Expression} :
      StepStmtStarE Expression (EvalCommandE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      p.body = .cfg g →
      CallEntry env.factory env.store p args σAO →
      StepCFGStarE Expression (EvalCommandE π)
        (.atBlock g g.entry (⟨σAO, env.factory⟩ : Imperative.Env Expression)) cfgEvs
        (.inBlock g' t (c :: cs) tr ρ) →
      CoreInterruptedSound π
        (.stmt (.cmd c) (⟨ρ.store, env.factory⟩ : Imperative.Env Expression)) cmdEvs →
      CoreInterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (Imperative.Calls.checksAtCall md p.spec.preconditions) ++ cfgEvs
          ++ cmdEvs)
  | inCallExit {start : CoreConfig} {outerEvs : Trace Expression} {C : CoreConfig}
      {env : Imperative.Env Expression} {pn : String}
      {args : List (Imperative.CallArg Expression)} {md : Imperative.MetaData Expression}
      {p : Procedure} {σAO σf : CoreStore} {bodyEvs : Trace Expression} :
      StepStmtStarE Expression (EvalCommandE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      CallEntry env.factory env.store p args σAO →
      BigStepE π p.body ⟨σAO, env.factory⟩ σf bodyEvs →
      CoreInterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (Imperative.Calls.checksAtCall md p.spec.preconditions)
          ++ bodyEvs ++ defaultAssertEvents env.factory σf p.spec.postconditions)
  | preThrow {start : CoreConfig} {outerEvs : Trace Expression} {C : CoreConfig}
      {env : Imperative.Env Expression} {pn : String}
      {args : List (Imperative.CallArg Expression)} {md : Imperative.MetaData Expression}
      {p : Procedure} {σAO : CoreStore}
      {preEvs : Trace Expression} :
      StepStmtStarE Expression (EvalCommandE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      CallEntry env.factory env.store p args σAO →
      preEvs <+: defaultAssertEvents env.factory σAO
          (Imperative.Calls.checksAtCall md p.spec.preconditions) →
      CoreInterruptedSound π start (outerEvs ++ preEvs)
  | postThrow {start : CoreConfig} {outerEvs : Trace Expression} {C : CoreConfig}
      {env : Imperative.Env Expression} {pn : String}
      {args : List (Imperative.CallArg Expression)} {md : Imperative.MetaData Expression}
      {p : Procedure} {σAO σf : CoreStore} {bodyEvs : Trace Expression}
      {postEvs : Trace Expression} :
      StepStmtStarE Expression (EvalCommandE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      CallEntry env.factory env.store p args σAO →
      BigStepE π p.body ⟨σAO, env.factory⟩ σf bodyEvs →
      postEvs <+: defaultAssertEvents env.factory σf p.spec.postconditions →
      CoreInterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (Imperative.Calls.checksAtCall md p.spec.preconditions)
          ++ bodyEvs ++ postEvs)

/-- A Core command that does not *reach* `target` in the sense of `targetReached`:
    it is not an `assert`/`cover` whose label and metadata both equal `target`'s
    (`Calls.cmdAvoidsTarget` at `Expression`). -/
abbrev cmdAvoidsTarget (target : AssertId Expression) : Command → Bool :=
  Calls.cmdAvoidsTarget target

/-- No spec clause of `checks` has both `target`'s label and `target`'s metadata
    (`Calls.ChecksAvoidTarget` at `Expression`). -/
abbrev ChecksAvoidTarget (target : AssertId Expression) :
    ListMap CoreLabel Procedure.Check → Prop :=
  Calls.ChecksAvoidTarget target

/-- **The target id occurs in no procedure of `π`**: for every `p` that `π`
    resolves, no pre- or postcondition clause of `p` has `target`'s label and
    metadata, and no `assert`/`cover` command of `p`'s body does: anywhere in a
    structured body, and in any block of a CFG body (`Calls.TargetNotInProcs` at `Expression`). -/
abbrev TargetNotInProcs (π : String → Option Procedure) (target : AssertId Expression) : Prop :=
  Calls.TargetNotInProcs π target

/-- The empty procedure table satisfies `TargetNotInProcs` for every target. -/
theorem targetNotInProcs_none (target : AssertId Expression) :
    TargetNotInProcs (fun _ => none) target := nofun

/-! ## Core's side conditions and certificate are the generic ones -/

section Bridge

variable (π : String → Option Procedure)

/-- Core's per-procedure check `ProcOk` is the generic `Calls.ProcOk`. -/
private theorem procOk_iff (p : Procedure) : ProcOk π p ↔ Calls.ProcOk π p := by
  rw [ProcOk, Procedure.Header.keys_getOutputOnlyParams]
  rfl

/-- Core's program-level check `ProcsOk` is the generic `Calls.ProcsOk`. -/
theorem procsOk_iff : ProcsOk π ↔ Calls.ProcsOk π := by
  simp only [ProcsOk, procOk_iff]
  rfl

/-- Core's configuration invariant `CoreCfgInv` is the generic `Calls.CfgInv`. -/
theorem coreCfgInv_iff (c : CoreConfig) : CoreCfgInv π c ↔ Calls.CfgInv π c := Iff.rfl

/-- A generic interrupted-run certificate at `Expression` is Core's. -/
private theorem coreInterruptedSound_of_generic {start : CoreConfig} {evs : Trace Expression}
    (h : Calls.InterruptedSound π start evs) :
    CoreInterruptedSound π start evs := by
  induction h with
  | clean h => exact .clean h
  | inCall a b c d e _ ih =>
    exact .inCall a b c d ((callEntry_iff ..).2 e) ih
  | inCallCfg a b c d e f =>
    exact .inCallCfg a b c d ((callEntry_iff ..).2 e) f
  | inCallCfgCmd a b c d e f _ ih =>
    exact .inCallCfgCmd a b c d ((callEntry_iff ..).2 e) f ih
  | inCallExit a b c e f => exact .inCallExit a b c ((callEntry_iff ..).2 e) f
  | preThrow a b c e f => exact .preThrow a b c ((callEntry_iff ..).2 e) f
  | postThrow a b c e f g =>
    exact .postThrow a b c ((callEntry_iff ..).2 e) f g

/-- Core's interrupted-run certificate is a generic one at `Expression`. -/
private theorem coreInterruptedSound_toGeneric {start : CoreConfig} {evs : Trace Expression}
    (h : CoreInterruptedSound π start evs) :
    Calls.InterruptedSound π start evs := by
  induction h with
  | clean h => exact .clean h
  | inCall a b c d e _ ih =>
    exact .inCall a b c d ((callEntry_iff ..).1 e) ih
  | inCallCfg a b c d e f =>
    exact .inCallCfg a b c d ((callEntry_iff ..).1 e) f
  | inCallCfgCmd a b c d e f _ ih =>
    exact .inCallCfgCmd a b c d ((callEntry_iff ..).1 e) f ih
  | inCallExit a b c e f => exact .inCallExit a b c ((callEntry_iff ..).1 e) f
  | preThrow a b c e f => exact .preThrow a b c ((callEntry_iff ..).1 e) f
  | postThrow a b c e f g =>
    exact .postThrow a b c ((callEntry_iff ..).1 e) f g

/-- Core's interrupted-run certificate `CoreInterruptedSound` is the generic
    `Calls.InterruptedSound`. -/
private theorem coreInterruptedSound_iff {start : CoreConfig} {evs : Trace Expression} :
    CoreInterruptedSound π start evs ↔ Calls.InterruptedSound π start evs :=
  ⟨coreInterruptedSound_toGeneric _, coreInterruptedSound_of_generic _⟩

/-- Core's `ReplaySound` is the generic `Calls.ReplaySound`. -/
private theorem replaySound_iff (target : AssertId Expression) (fuel : Nat)
    (F : Expression.Factory) (cex : CexA Expression Command) (d : Nat) :
    ReplaySound π target fuel F cex d ↔ Calls.ReplaySound π target fuel F cex d := by
  rw [ReplaySound]
  rfl

/-- Core's `ReplaySoundFeasible` is the generic `Calls.ReplaySoundFeasible`. -/
private theorem replaySoundFeasible_iff (target : AssertId Expression) (fuel : Nat)
    (F : Expression.Factory) (cex : CexA Expression Command) (d : Nat) :
    ReplaySoundFeasible π target fuel F cex d ↔
      Calls.ReplaySoundFeasible π target fuel F cex d := by
  rw [ReplaySoundFeasible]
  rfl

end Bridge

/-! ## Replay soundness for Core `Command`, as instances of the generic theorems -/

section CoreReplay

/-- **Core whole-run soundness, monad-generically.**  If every procedure of `π` passes Core's
    call checks (`ProcsOk`), then a successful `runCoreInterp π` run from a configuration with a
    well-formed factory (`FactoryWF`) at which the bounded evaluator is sound
    (`BoundedEvalSoundAt`), satisfying the replay invariant `CoreCfgInv π`, is a reference
    `CoreStepStarE` execution emitting exactly the same events. -/
theorem core_runInterp_sound {m : Type → Type} [Monad m] [LawfulMonad m]
    [InterpEffects Expression m] [MonadExcept StopReason m]
    (obs : InterpObs Expression m)
    (π : String → Option Procedure)
    (hprocs : ProcsOk π) (d : Nat) :
    RunInterpSound Expression m obs (replayStepCmd π d) (EvalCommandE π)
      (CoreCfgInv π) := by
  unfold CoreCfgInv
  apply Calls.call_runInterp_sound <;> grind [procsOk_iff]

/-- **Core whole-run soundness at `EvalM`, with calls.** A successful `EvalM` run of
    `runCoreInterp π` from an interpreter configuration `istart` denoting (`IConfig.Denotes`) a
    configuration `start` with a well-formed factory (`FactoryWF`) at which the bounded
    evaluator is sound (`BoundedEvalSoundAt`) satisfying the replay invariant `CoreCfgInv π` is
    a reference `CoreStepStarE` execution to the configuration the result stands for
    (`IConfig.abs`), emitting exactly the recorded events, provided every procedure of `π`
    passes Core's call checks (`ProcsOk`). -/
theorem core_runCoreInterp_sound_eval
    (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (fuel : Nat) (F : Expression.Factory) (hEval : BoundedEvalSoundAt Expression F)
    (start : Config Expression Command)
    (istart : IConfig Expression Command) (hstart : istart.Denotes F start)
    (final : IConfig Expression Command)
    (opts : EvalOpts) (st st' : EvalState) (d : Nat)
    (hrun : evalRun (runCoreInterp π fuel istart d) opts st = (.ok final, st'))
    (hfac : FactoryWF (P := Expression) F) (hinv : CoreCfgInv π start) :
    ∃ (revs : List (IEvent Expression)), CoreStepStarE π start (revs.map (REvent.abs F))
      (final.abs F) ∧ final.Denoting F ∧ st'.traceRev = revs.reverse ++ st.traceRev := by
  obtain ⟨_, revs, _, hstar, ⟨hd, -, rfl⟩, htr, rfl⟩ :=
    core_runInterp_sound obsEval π hprocs d fuel F start istart final opts st st' hstart hrun hfac
      hEval hinv
  exact ⟨revs, hstar, hd, htr⟩

/-- **Core whole-run soundness at `EvalM`, with calls.** A successful `EvalM` run of `runCoreInterp
    π` from an interpreter configuration `istart` denoting (`IConfig.Denotes`) a configuration
    `start` with a well-formed factory (`FactoryWF`) whose functions meet the conditions under which
    the bounded evaluator is sound (`EvalFactoryWF`, which `evalFactoryWF_of_userFuncs` gives
    program factories) satisfying the replay invariant `CoreCfgInv π` is a reference `CoreStepStarE`
    execution to the configuration the result stands for (`IConfig.abs`), emitting exactly the
    recorded events, provided every procedure of `π` passes Core's call checks (`ProcsOk`). -/
theorem core_runCoreInterp_sound_eval_of_evalFactoryWF
    (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (fuel : Nat)
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (start : Config Expression Command)
    (istart : IConfig Expression Command)
    (hstart : istart.Denotes F start)
    (final : IConfig Expression Command)
    (opts : EvalOpts)
    (st st' : EvalState)
    (d : Nat)
    (hrun : evalRun (runCoreInterp π fuel istart d) opts st = (.ok final, st'))
    (hfac : FactoryWF (P := Expression) F)
    (hinv : CoreCfgInv π start) :
    ∃ (revs : List (IEvent Expression)), CoreStepStarE π start (revs.map (REvent.abs F))
      (final.abs F) ∧ final.Denoting F ∧ st'.traceRev = revs.reverse ++ st.traceRev :=
  core_runCoreInterp_sound_eval π hprocs fuel F (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) start
    istart hstart final opts st st' d hrun hfac hinv

/-- A successful Core replay run from an interpreter configuration `istart` denoting
    (`IConfig.Denotes`) a configuration `start` with a well-formed factory (`FactoryWF`) at
    which the bounded evaluator is sound (`BoundedEvalSoundAt`) satisfying the replay invariant
    (`CoreCfgInv π`), with every procedure of `π` passing Core's call checks (`ProcsOk`),
    records exactly the events of a reference run to the configuration its result stands for
    (`IConfig.abs`). -/
theorem core_replayRun_sound
    (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (fuel : Nat) (F : Expression.Factory) (hEval : BoundedEvalSoundAt Expression F)
    (start : Config Expression Command)
    (istart : IConfig Expression Command) (hstart : istart.Denotes F start)
    (final : IConfig Expression Command)
    (cfg : ReplayCfg Expression) (oracle : List Expression.Expr)
    (st' : ReplayState Expression) (d : Nat)
    (hrun : runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel istart d)
        cfg oracle = (.ok final, st'))
    (hfac : FactoryWF (P := Expression) F) (hinv : CoreCfgInv π start) :
    ∃ (revs : List (IEvent Expression)), StepStmtStarE (P := Expression) (EvalCommandE π)
             start (revs.map (REvent.abs F)) (final.abs F) ∧ final.Denoting F ∧
             st'.traceRev = revs.reverse := by
  core_gen_by [procsOk_iff, coreCfgInv_iff]

/-- A successful Core replay run from an interpreter configuration `istart` denoting
    (`IConfig.Denotes`) a configuration `start` with a well-formed factory (`FactoryWF`) whose
    functions meet the conditions under which the bounded evaluator is sound (`EvalFactoryWF`, which
    `evalFactoryWF_of_userFuncs` gives program factories) satisfying the replay invariant
    (`CoreCfgInv π`), with every procedure of `π` passing Core's call checks (`ProcsOk`), records
    exactly the events of a reference run to the configuration its result stands for
    (`IConfig.abs`). -/
theorem core_replayRun_sound_of_evalFactoryWF
    (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (fuel : Nat)
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (start : Config Expression Command)
    (istart : IConfig Expression Command)
    (hstart : istart.Denotes F start)
    (final : IConfig Expression Command)
    (cfg : ReplayCfg Expression)
    (oracle : List Expression.Expr)
    (st' : ReplayState Expression)
    (d : Nat)
    (hrun : runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel istart d)
        cfg oracle = (.ok final, st'))
    (hfac : FactoryWF (P := Expression) F)
    (hinv : CoreCfgInv π start) :
    ∃ (revs : List (IEvent Expression)), StepStmtStarE (P := Expression) (EvalCommandE π)
             start (revs.map (REvent.abs F)) (final.abs F) ∧ final.Denoting F ∧
             st'.traceRev = revs.reverse :=
  core_replayRun_sound π hprocs fuel F (boundedEvalSoundAt_of_evalFactoryWF F hEvalF) start istart
    hstart final cfg oracle st' d hrun hfac hinv

/-- A genuine Core counterexample reaches the target failure under the reference relation
    (`ReplaySound`), provided every procedure of `π` passes Core's call checks (`ProcsOk`), the
    start configuration has a well-formed factory (`FactoryWF`) at which the bounded evaluator
    is sound (`BoundedEvalSoundAt`) and satisfies the replay invariant (`CoreCfgInv`: value-only
    and typed stores, well-formed call sites), and the strict replay run of `runCoreInterp π` at
    fuel `fuel` from `cex.cfg` (denoting at `F`, `IConfig.Denoting`) returns `.ok`. -/
theorem core_replaySound_of_ok
    (π : String → Option Procedure)
    (target : AssertId Expression) (fuel : Nat) (cex : CexA Expression Command)
    (hprocs : ProcsOk π)
    (F : Expression.Factory) (hEval : BoundedEvalSoundAt Expression F)
    (hfac : FactoryWF (P := Expression) F) (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CoreCfgInv π (cex.cfg.abs F))
    (d : Nat)
    (hok : ∃ final, (runReplayRun
          (runCoreInterp (m := ReplayM Expression) π fuel cex.cfg d)
          { oracleConfig := .strict }
          cex.oracle).1 = .ok final) :
    ReplaySound π target fuel F cex d := by
  core_gen_by [procsOk_iff, coreCfgInv_iff, replaySound_iff]

/-- A genuine Core counterexample reaches the target failure under the reference relation
    (`ReplaySound`), provided every procedure of `π` passes Core's call checks (`ProcsOk`), the
    start configuration has a well-formed factory (`FactoryWF`) whose functions meet the conditions
    under which the bounded evaluator is sound (`EvalFactoryWF`, which `evalFactoryWF_of_userFuncs`
    gives program factories) and satisfies the replay invariant (`CoreCfgInv`: value-only and typed
    stores, well-formed call sites), and the strict replay run of `runCoreInterp π` at fuel `fuel`
    from `cex.cfg` (denoting at `F`, `IConfig.Denoting`) returns `.ok`. -/
theorem core_replaySound_of_ok_of_evalFactoryWF
    (π : String → Option Procedure)
    (target : AssertId Expression)
    (fuel : Nat)
    (cex : CexA Expression Command)
    (hprocs : ProcsOk π)
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (hfac : FactoryWF (P := Expression) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked)
    (hinv : CoreCfgInv π (cex.cfg.abs F))
    (d : Nat)
    (hok : ∃ final, (runReplayRun
          (runCoreInterp (m := ReplayM Expression) π fuel cex.cfg d)
          { oracleConfig := .strict }
          cex.oracle).1 = .ok final) :
    ReplaySound π target fuel F cex d :=
  core_replaySound_of_ok π target fuel cex hprocs F (boundedEvalSoundAt_of_evalFactoryWF F hEvalF)
    hfac hd ht hinv d hok

/-- Whatever its outcome, a Core replay run from an interpreter configuration `istart` denoting
    (`IConfig.Denotes`) a configuration `start` with a well-formed factory (`FactoryWF`) at
    which the bounded evaluator is sound (`BoundedEvalSoundAt`) satisfying the replay invariant
    (`CoreCfgInv π`), with every procedure of `π` passing Core's call checks (`ProcsOk`),
    records events certified by the interrupted-run certificate `CoreInterruptedSound`: they are
    the events of a reference run, possibly cut off inside one call. -/
theorem core_replayRun_interruptedSound
    (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (fuel : Nat) (F : Expression.Factory) (hEval : BoundedEvalSoundAt Expression F)
    (start : Config Expression Command)
    (istart : IConfig Expression Command) (hstart : istart.Denotes F start)
    (cfg : ReplayCfg Expression) (oracle : List Expression.Expr)
    (res : Except StopReason (IConfig Expression Command)) (st' : ReplayState Expression)
    (d : Nat)
    (hrun : runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel istart d)
        cfg oracle = (res, st'))
    (hfac : FactoryWF (P := Expression) F) (hinv : CoreCfgInv π start) :
    ∃ (revs : List (IEvent Expression)), CoreInterruptedSound π start (revs.map (REvent.abs F)) ∧
      st'.traceRev = revs.reverse := by
  core_gen_by [procsOk_iff, coreCfgInv_iff, coreInterruptedSound_iff]

/-- Whatever its outcome, a Core replay run from an interpreter configuration `istart` denoting
    (`IConfig.Denotes`) a configuration `start` with a well-formed factory (`FactoryWF`) whose
    functions meet the conditions under which the bounded evaluator is sound (`EvalFactoryWF`, which
    `evalFactoryWF_of_userFuncs` gives program factories) satisfying the replay invariant
    (`CoreCfgInv π`), with every procedure of `π` passing Core's call checks (`ProcsOk`), records
    events certified by the interrupted-run certificate `CoreInterruptedSound`: they are the events
    of a reference run, possibly cut off inside one call. -/
theorem core_replayRun_interruptedSound_of_evalFactoryWF
    (π : String → Option Procedure)
    (hprocs : ProcsOk π)
    (fuel : Nat)
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (start : Config Expression Command)
    (istart : IConfig Expression Command)
    (hstart : istart.Denotes F start)
    (cfg : ReplayCfg Expression)
    (oracle : List Expression.Expr)
    (res : Except StopReason (IConfig Expression Command))
    (st' : ReplayState Expression)
    (d : Nat)
    (hrun : runReplayRun (runCoreInterp (m := ReplayM Expression) π fuel istart d)
        cfg oracle = (res, st'))
    (hfac : FactoryWF (P := Expression) F)
    (hinv : CoreCfgInv π start) :
    ∃ (revs : List (IEvent Expression)), CoreInterruptedSound π start (revs.map (REvent.abs F)) ∧
      st'.traceRev = revs.reverse :=
  core_replayRun_interruptedSound π hprocs fuel F (boundedEvalSoundAt_of_evalFactoryWF F hEvalF)
    start istart hstart cfg oracle res st' d hrun hfac hinv

/-- If the strict replay run of `runCoreInterp π` that stops at the target failure
    (`targetInterrupt target fuel`) returns `.genuine` from `cex.cfg`, which denotes at `F`
    (`IConfig.Denoting`), where `cex.cfg` has a well-formed factory (`FactoryWF`) at which the
    bounded evaluator is sound (`BoundedEvalSoundAt`) and satisfies the replay invariant
    `CoreCfgInv π`, and every procedure of `π` passes Core's call checks (`ProcsOk`), then some
    events certified from `cex.cfg` by the interrupted-run certificate `CoreInterruptedSound` (a
    reference run, possibly cut off inside one call) contain an event on which the target fails
    (`assertFailureHalt target fuel`). -/
theorem core_replaySound_interruptOn
    (π : String → Option Procedure)
    (target : AssertId Expression) (cex : CexA Expression Command)
    (hprocs : ProcsOk π)
    (F : Expression.Factory) (hEval : BoundedEvalSoundAt Expression F)
    (hfac : FactoryWF (P := Expression) F) (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CoreCfgInv π (cex.cfg.abs F))
    (fuel d : Nat)
    (hg : (runReplay (runCoreInterp (m := ReplayM Expression) π fuel cex.cfg d)
            { interruptOn := targetInterrupt target fuel,
              oracleConfig := .strict } (assertFailureHalt target fuel) cex.oracle).1 = .genuine) :
    ∃ (revs : List (IEvent Expression)),
      CoreInterruptedSound π (cex.cfg.abs F) (revs.map (REvent.abs F)) ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true := by
  core_gen_by [procsOk_iff, coreCfgInv_iff, coreInterruptedSound_iff]

/-- If the strict replay run of `runCoreInterp π` that stops at the target failure (`targetInterrupt
    target fuel`) returns `.genuine` from `cex.cfg`, which denotes at `F` (`IConfig.Denoting`),
    where `cex.cfg` has a well-formed factory (`FactoryWF`) whose functions meet the conditions
    under which the bounded evaluator is sound (`EvalFactoryWF`, which `evalFactoryWF_of_userFuncs`
    gives program factories) and satisfies the replay invariant `CoreCfgInv π`, and every procedure
    of `π` passes Core's call checks (`ProcsOk`), then some events certified from `cex.cfg` by the
    interrupted-run certificate `CoreInterruptedSound` (a reference run, possibly cut off inside one
    call) contain an event on which the target fails (`assertFailureHalt target fuel`). -/
theorem core_replaySound_interruptOn_of_evalFactoryWF
    (π : String → Option Procedure)
    (target : AssertId Expression)
    (cex : CexA Expression Command)
    (hprocs : ProcsOk π)
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (hfac : FactoryWF (P := Expression) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked)
    (hinv : CoreCfgInv π (cex.cfg.abs F))
    (fuel d : Nat)
    (hg : (runReplay (runCoreInterp (m := ReplayM Expression) π fuel cex.cfg d)
            { interruptOn := targetInterrupt target fuel,
              oracleConfig := .strict } (assertFailureHalt target fuel) cex.oracle).1 = .genuine) :
    ∃ (revs : List (IEvent Expression)),
      CoreInterruptedSound π (cex.cfg.abs F) (revs.map (REvent.abs F)) ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true :=
  core_replaySound_interruptOn π target cex hprocs F (boundedEvalSoundAt_of_evalFactoryWF F hEvalF)
    hfac hd ht hinv fuel d hg

/-- For a `genuine` Core counterexample whose start configuration has a well-formed factory
    (`FactoryWF`) at which the bounded evaluator is sound (`BoundedEvalSoundAt`) and satisfies
    the replay invariant `CoreCfgInv π`, with every procedure of `π` passing Core's call checks
    (`ProcsOk`), some events certified from `cex.cfg` by the interrupted-run certificate
    `CoreInterruptedSound` (a reference run, possibly cut off inside one call) contain an event
    on which the target fails (`assertFailureHalt target fuel`). -/
theorem core_replaySound_general
    (π : String → Option Procedure)
    (target : AssertId Expression) (fuel : Nat) (cex : CexA Expression Command)
    (hprocs : ProcsOk π)
    (F : Expression.Factory) (hEval : BoundedEvalSoundAt Expression F)
    (hfac : FactoryWF (P := Expression) F) (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CoreCfgInv π (cex.cfg.abs F))
    (d : Nat) (hg : genuine π target fuel cex d) :
    ∃ (revs : List (IEvent Expression)),
      CoreInterruptedSound π (cex.cfg.abs F) (revs.map (REvent.abs F)) ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true := by
  core_gen_by [procsOk_iff, coreCfgInv_iff, coreInterruptedSound_iff]

/-- For a `genuine` Core counterexample whose start configuration has a well-formed factory
    (`FactoryWF`) whose functions meet the conditions under which the bounded evaluator is sound
    (`EvalFactoryWF`, which `evalFactoryWF_of_userFuncs` gives program factories) and satisfies the
    replay invariant `CoreCfgInv π`, with every procedure of `π` passing Core's call checks
    (`ProcsOk`), some events certified from `cex.cfg` by the interrupted-run certificate
    `CoreInterruptedSound` (a reference run, possibly cut off inside one call) contain an event on
    which the target fails (`assertFailureHalt target fuel`). -/
theorem core_replaySound_general_of_evalFactoryWF
    (π : String → Option Procedure)
    (target : AssertId Expression)
    (fuel : Nat)
    (cex : CexA Expression Command)
    (hprocs : ProcsOk π)
    (F : Expression.Factory)
    (hEvalF : EvalFactoryWF F.factory)
    (hfac : FactoryWF (P := Expression) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked)
    (hinv : CoreCfgInv π (cex.cfg.abs F))
    (d : Nat)
    (hg : genuine π target fuel cex d) :
    ∃ (revs : List (IEvent Expression)),
      CoreInterruptedSound π (cex.cfg.abs F) (revs.map (REvent.abs F)) ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true :=
  core_replaySound_general π target fuel cex hprocs F (boundedEvalSoundAt_of_evalFactoryWF F hEvalF)
    hfac hd ht hinv d hg

/-- **Flattening a certificate at a target-reaching event, with the flat trace a
    prefix.**  If the target id occurs in no procedure of `π` (`TargetNotInProcs`), an event
    that reaches the target in an interrupted-run certificate (`CoreInterruptedSound`: a
    reference run possibly cut off inside one call) lies in a flat reference run from `start`
    whose events are a prefix of the certificate's. -/
theorem coreInterruptedSound_flatPrefix_of_targetReached
    (π : String → Option Procedure)
    (target : AssertId Expression) (hπ : TargetNotInProcs π target)
    {start : CoreConfig} {evs : Trace Expression}
    (h : CoreInterruptedSound π start evs)
    {ev : Event Expression} (hmem : ev ∈ evs) (hreach : Calls.targetReachedE target ev = true) :
    ∃ evs' final, StepStmtStarE Expression (EvalCommandE π)
        start evs' final ∧ ev ∈ evs' ∧ evs' <+: evs := by
  apply Calls.interruptedSound_flatPrefix_of_targetReached _ target <;>
      simp_all [coreInterruptedSound_iff]

/-- **Flattening a certificate at a target-reaching event.**  If the target id occurs in no
    procedure of `π` (`TargetNotInProcs`), an event that reaches the target in an interrupted-run
    certificate (`CoreInterruptedSound`) lies in a flat reference run from `start`. -/
theorem coreInterruptedSound_flat_of_targetReached
    (π : String → Option Procedure)
    (target : AssertId Expression) (hπ : TargetNotInProcs π target)
    {start : CoreConfig} {evs : Trace Expression}
    (h : CoreInterruptedSound π start evs)
    {ev : Event Expression} (hmem : ev ∈ evs) (hreach : Calls.targetReachedE target ev = true) :
    ∃ evs' final, StepStmtStarE Expression (EvalCommandE π)
        start evs' final ∧ ev ∈ evs' := by grind [coreInterruptedSound_flatPrefix_of_targetReached]

/-- **`ReplaySound` for Core**: a genuine counterexample reaches the target failure under the
    reference relation, provided every procedure of `π` passes Core's call checks (`ProcsOk`),
    the start configuration has a well-formed factory (`FactoryWF`) whose functions meet the
    conditions under which the bounded evaluator is sound (`EvalFactoryWF`; `Core.Factory` meets
    them) and satisfies the replay invariant (`CoreCfgInv`:
    value-only and typed stores, well-formed call sites), and the target id occurs in no
    procedure of `π` (`TargetNotInProcs`; always true for an empty procedure table). -/
theorem core_replaySound
    (π : String → Option Procedure)
    (target : AssertId Expression) (fuel : Nat) (cex : CexA Expression Command)
    (hprocs : ProcsOk π)
    (F : Expression.Factory) (hEvalF : EvalFactoryWF F.factory)
    (hfac : FactoryWF (P := Expression) F) (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CoreCfgInv π (cex.cfg.abs F))
    (htgt : TargetNotInProcs π target) (d : Nat) :
    ReplaySound π target fuel F cex d := by
  have hEval := boundedEvalSoundAt_of_evalFactoryWF F hEvalF
  core_gen_by [procsOk_iff, coreCfgInv_iff, replaySound_iff]

/-- **`ReplaySoundFeasible` for Core**: a Core counterexample classified `genuineEnforced`
    reaches the target failure on a reference path whose `.assume` events all evaluate to `tt`
    (`PathFeasible`), provided every procedure of `π` passes Core's call checks (`ProcsOk`), the
    start configuration has a well-formed factory (`FactoryWF`) whose functions meet the
    conditions under which the bounded evaluator is sound (`EvalFactoryWF`; `Core.Factory` meets
    them) and satisfies the replay invariant (`CoreCfgInv`: value-only
    and typed stores, well-formed call sites), and the target id occurs in no procedure of `π`
    (`TargetNotInProcs`). -/
theorem core_replaySound_feasible
    (π : String → Option Procedure)
    (target : AssertId Expression) (fuel : Nat) (cex : CexA Expression Command)
    (hprocs : ProcsOk π)
    (F : Expression.Factory) (hEvalF : EvalFactoryWF F.factory)
    (hfac : FactoryWF (P := Expression) F) (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CoreCfgInv π (cex.cfg.abs F))
    (htgt : TargetNotInProcs π target) (d : Nat) :
    ReplaySoundFeasible π target fuel F cex d := by
  have hEval := boundedEvalSoundAt_of_evalFactoryWF F hEvalF
  core_gen_by [procsOk_iff, coreCfgInv_iff, replaySoundFeasible_iff]

end CoreReplay

end -- public section

end Core
