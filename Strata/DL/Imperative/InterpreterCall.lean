/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtCFGCallSemantics
public import Strata.DL.Imperative.InterpreterReplay
public import Strata.DL.Imperative.InterpreterCFG
import Strata.DL.Imperative.InterpreterReplayTactics
public import Strata.DL.Imperative.InterpreterReplayProps

/-! # The call-aware monadic-interpreter stepper, over any `PureExpr`

`Calls.stepCmd π` steps a `CmdExt P` command: a base command through the generic
`stepBaseCmdStore`, and a `.call` as an **exact run-to-completion** of the callee
body in the same effect monad, at strictly smaller fuel: a structured body through the
Imperative driver `runInterp`, a CFG body through the CFG driver `runInterpCFG`.  It follows the
reference rule `Calls.EvalCmdExtE.call_sem`: `callEntryStore` is its `InitCallFrame`, the
argument evaluation and `out` read its other `CallEntry` premises, the trailing
`readVarList`/`bindPositional` pair its `CallExit`, and the callee's non-`free` pre- and
postconditions are **emitted** as assertion events (never adjudicated) around the body run.

An unresolved callee and a positional arity mismatch are refused.

It also defines, over this stepper, the target-event predicates `assertFailureHalt` and
`targetReached` and the replay verdicts `genuine`, `genuineFeasible`, `genuineEnforced`.

Lemmas about these definitions are in `InterpreterCallProps.lean`. -/

namespace Imperative

public section

namespace Calls

variable {P : PureExpr}

/-! ## Executable call helpers -/

/-- Evaluate a list of expressions with the language's fuel-bounded evaluator,
    short-circuiting to `none` if any does not reduce. -/
@[expose] def evalBoundedList [InterpLang P] (fuel : Nat) (factory : InterpLang.RFactory P)
    (store : RStore P) : List P.Expr → Option (List P.Expr)
  | [] => some []
  | expr :: rest =>
    match InterpLang.boundedEval (P := P) fuel factory store expr with
    | some value => (evalBoundedList fuel factory store rest).map (value :: ·)
    | none => none

/-- A point update of a store of any value type (runtime or semantic). -/
@[expose] def storeUpdate [DecidableEq P.Ident] {V : Type _} (σ : P.Ident → Option V) (x : P.Ident)
    (v : V) : P.Ident → Option V :=
  fun y => if y = x then some v else σ y

/-- On semantic stores, `storeUpdate` is `SemanticStore.update`. -/
theorem storeUpdate_eq_update [DecidableEq P.Ident] (σ : SemanticStore P) (x : P.Ident)
    (v : P.Val) : storeUpdate σ x v = SemanticStore.update σ x v := rfl

/-- Positionally bind names to values on top of a store (point updates, in order).
    Extra names or extra values are dropped. -/
@[expose] def bindPositional [DecidableEq P.Ident] {V : Type _} (store : P.Ident → Option V)
    (names : List P.Ident) (values : List V) : P.Ident → Option V :=
  match names, values with
  | name :: names, value :: values =>
    bindPositional (storeUpdate store name value) names values
  | _, _ => store

/-- Read a list of variables from a store, short-circuiting to `none` if any is
    undefined. -/
@[expose] def readVarList {V : Type _} (store : P.Ident → Option V) :
    List P.Ident → Option (List V)
  | [] => some []
  | name :: rest =>
    match store name with
    | some value => (readVarList store rest).map (value :: ·)
    | none => none

/-- The typed write-back check of a call: every written-back value passes the runtime value check
    `isValue` and has the type of the value its target held before the call (`sameType`), pairing
    the targets' previous values `olds` with the written values `vals` positionally. -/
@[expose] def writeBackTyped {RF : Type} (ops : ReplayValueOps P RF) (f : RF)
    (olds vals : List P.Expr) : Bool :=
  (olds.zip vals).all fun (o, v) => ops.isValue f v && ops.sameType f o v

section Stepper

variable [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- `withOldSnapshots` over stores of any value type (runtime or semantic): every name of
    `snapshot` is also readable under its `old` name. -/
@[expose] def withOldSnapshotsV {V : Type _} (snapshot : List P.Ident) (σ : P.Ident → Option V) :
    P.Ident → Option V :=
  fun id =>
    match snapshot.find? (fun g => HasOldIdent.mkOld g == id) with
    | some g => σ g
    | none   => σ id

/-- On semantic stores, `withOldSnapshotsV` is `withOldSnapshots`. -/
theorem withOldSnapshotsV_eq (snapshot : List P.Ident) (σ : SemanticStore P) :
    withOldSnapshotsV snapshot σ = withOldSnapshots snapshot σ := rfl

/-- The runtime counterpart of `defaultAssertEvents`: the non-free clauses of `checks` as
    runtime assert events at the runtime snapshot `(rf, σ)`. -/
@[expose] def rDefaultAssertEvents {RF : Type} (rf : RF) (σ : RStore P)
    (checks : ListMap String (Check P)) : List (REvent P RF) :=
  checks.toList.filterMap fun (label, check) =>
    if check.attr = .Default then
      some (.assert { factory := rf, store := σ, label := label, expr := check.expr,
                      metadata := check.md })
    else
      none

/-- The callee's entry frame `σAO`: a fresh, empty store in which the input formals
    hold the evaluated input values, the output-only formals hold the caller's
    `out`-actual values, and each inout formal is snapshotted under `old`.
    Executable counterpart of `InitCallFrame`. -/
@[expose] def callEntryStore (p : Procedure P (CmdExt P) Hdr)
    {V : Type _} (inputVals outOnlyVals : List V) : P.Ident → Option V :=
  let σA := bindPositional (fun _ => none) (ProcedureHeader.inputParams (P := P) p.header)
    inputVals
  let σIO := bindPositional σA (outputOnlyParams (P := P) p.header) outOnlyVals
  withOldSnapshotsV (inoutParams (P := P) p.header) σIO

/-! ## The stepper -/

variable [HasBool P] [DecidableEq P.Expr] [InterpLang P] [HasFvar P]

/-- The callee body run of a `.call`, from the entry frame `entryStore` at the caller's factory
    `fac` and driver fuel `fuel`, over the command stepper `step`; it returns the body's final
    store.  A structured body `ss` runs as `.block "" ss` through `runInterp`, and its final
    store is the store of the terminal configuration.  A CFG body `g` runs through
    `runInterpCFG` from its entry block, each command through `step` at the running store, and
    its final store is the halting store projected through the entry frame (`projectStore`), as
    in `BigStepE`.  A body that does not end in a terminal configuration stops with
    `programCallBodyExited`. -/
@[expose] def runCallee {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
    (step : StepCmdM P (CmdExt P) m) (procName : String) (body : Body P (CmdExt P))
    (fac : InterpLang.RFactory P) (fuel : Nat) (entryStore : RStore P) : m (RStore P) :=
  match body with
  | .structured ss => do
    let finalCfg ← runInterp step fuel
      (.stmt (.block "" ss #[])
        { store := .ofStore entryStore, factory := fac })
    let .terminal finalEnv := finalCfg
      | throw (.programCallBodyExited procName)
    pure finalEnv.store.get
  | .cfg g => do
    let finalCfg ← runInterpCFG step.toStore fuel (.atBlock g g.entry
        { store := .ofStore entryStore, factory := fac })
    let .terminal ρEnd := finalCfg
      | throw (.programCallBodyExited procName)
    pure (RStore.project entryStore ρEnd.store.get)

/-- The call-aware command stepper, generic over the effect monad `m`.  `depth` is the
    remaining call-depth budget: how many more calls may nest inside this one.  Base
    commands go through `stepBaseCmdStore` (presented as `.terminal`).  `.call` at
    fuel `fuel' + 1` stops with `callDepthExceeded` at budget `0`; at budget `depth' + 1` it
    evaluates its arguments, builds the callee frame, emits the non-free preconditions with
    their site metadata (`checksAtCall md`), runs the callee body (`runCallee`) at the caller's
    factory with this stepper baked at budget `depth'` and fuel `fuel'`, emits the non-free
    postconditions at the callee's final store, checks that each output has the type of the value
    its target held (`writeBackTyped`; `illTypedValue` otherwise), and writes the outputs back. -/
def stepCmd {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (depth : Nat)
    (fuel : Nat) (env : IEnv P) (cmd : CmdExt P) : m (IConfig P (CmdExt P)) :=
  match cmd with
  | .cmd base => do
    let store ← stepBaseCmdStore fuel env.factory env.store base
    return .terminal { env with store }
  | .call procName args md =>
    match fuel with
    | 0 => throw .replayFuelExhausted
    | fuel' + 1 =>
      match depth with
      | 0 => throw .callDepthExceeded
      | depth' + 1 =>
      match π procName with
      | none => throw (.unsupportedCalleeNotFound procName)
      | some p =>
        do
          let inArgs := getInputExprs args
          let outArgs := CallArg.getOutArgs args
          let lhs := CallArg.getLhs args
          let inputNames := ProcedureHeader.inputParams (P := P) p.header
          let outOnlyNames := outputOnlyParams (P := P) p.header
          let outputNames := ProcedureHeader.outputParams (P := P) p.header
          let some inputVals := evalBoundedList (fuel' + 1) env.factory env.store.get inArgs
            | throw .expressionDidNotEvaluate
          if inputVals.length ≠ inputNames.length then
            throw (.programCallInputArityMismatch procName)
          let some outOnlyVals := readVarList env.store.get outArgs
            | throw (.programCallLhsUndefined procName)
          if outOnlyVals.length ≠ outOnlyNames.length then
            throw (.programCallOutputArityMismatch procName)
          let entryStore := callEntryStore p inputVals outOnlyVals
          (rDefaultAssertEvents env.factory entryStore
              (checksAtCall md p.spec.preconditions)).forM (InterpEffects.emit (P := P))
          let finalStore ← runCallee (fun _ e c => stepCmd π depth' fuel' e c) procName p.body
            env.factory fuel' entryStore
          (rDefaultAssertEvents env.factory finalStore p.spec.postconditions).forM
            (InterpEffects.emit (P := P))
          let some modvals := readVarList finalStore outputNames
            | throw (.programCallOutputUndefinedOnReturn procName)
          if lhs.length ≠ outputNames.length then
            throw (.programCallOutputArityMismatch procName)
          let some oldVals := readVarList env.store.get lhs
            | throw (.programCallLhsUndefined procName)
          if !writeBackTyped (InterpLang.ops (P := P)) env.factory oldVals modvals then
            throw .illTypedValue
          let store' := env.store.bindPositional lhs modvals
          return .terminal { env with store := store' }
termination_by fuel
decreasing_by omega

/-- The call-aware driver: `runInterp` over `stepCmd π maxCallDepth`, nesting at most
    `maxCallDepth` calls. -/
@[expose] def runCallInterp {m : Type → Type} [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m] (π : String → Option (Procedure P (CmdExt P) Hdr))
    (fuel : Nat) (cfg : IConfig P (CmdExt P)) (maxCallDepth : Nat := defaultMaxCallDepth) :
    m (IConfig P (CmdExt P)) :=
  runInterp (stepCmd π maxCallDepth) fuel cfg

end Stepper

/-! ## Target-event predicates -/

variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]

/-- The halting predicate: fire on the event matching the target obligation id
    (`label` and `md`) whose recorded condition evaluates, under the bounded
    evaluator, to the literal that witnesses the obligation, up to metadata
    (`InterpLang.eqModuloMeta`): `ff` (a failing assertion) for an `.assert`, `tt` (a reached
    cover) for a `.cover`. -/
@[expose] def assertFailureHalt (target : AssertId P) (fuel : Nat) : IEvent P → Bool
  | .assert arg =>
      target.label == arg.label && decide (target.md = arg.metadata) &&
      (match InterpLang.boundedEval (P := P) fuel arg.factory arg.store arg.expr with
       | some v => InterpLang.eqModuloMeta v (HasBool.ff (P := P))
       | none => false)
  | .cover arg =>
      target.label == arg.label && decide (target.md = arg.metadata) &&
      (match InterpLang.boundedEval (P := P) fuel arg.factory arg.store arg.expr with
       | some v => InterpLang.eqModuloMeta v (HasBool.tt (P := P))
       | none => false)
  | _ => false

/-- Target-id match of an event (an `.assert`/`.cover` with the target's label and
    metadata), with no evaluation of the condition. -/
@[expose] def targetReached (target : AssertId P) : IEvent P → Bool
  | .assert arg | .cover arg =>
      target.label == arg.label && decide (target.md = arg.metadata)
  | _ => false

/-- Target-id match of a semantic event, with no evaluation of the condition: the semantic
    counterpart of `targetReached`. -/
@[expose] def targetReachedE (target : AssertId P) : Event P → Bool
  | .assert arg | .cover arg =>
      target.label == arg.label && decide (target.md = arg.metadata)
  | _ => false

/-! ## Replay verdicts over the call-aware stepper -/

/-- Production stop hook, interrupt only: throw `.interrupted` at a failing target
    occurrence. -/
@[expose] def targetInterrupt (target : AssertId P) (fuel : Nat) : IEvent P → Option StopReason :=
  fun ev => if assertFailureHalt target fuel ev then some (.interrupted "target failure reached")
    else none

/-- Production stop hook: `targetInterrupt`, plus a throw on an `.assume` not evaluating to `tt`
    up to metadata (`InterpLang.boolLit?`). -/
@[expose] def enforceInterrupt (target : AssertId P) (fuel : Nat) :
    IEvent P → Option StopReason :=
  fun ev => match ev with
    | .assume arg =>
      match InterpLang.boundedEval (P := P) fuel arg.factory arg.store arg.expr with
      | some v =>
        match InterpLang.boolLit? v with
        | some true => none
        | some false => some (.assumptionFalseUnderReplay arg.label)
        | none => some .expressionWasNotBoolean
      | none => some .expressionDidNotEvaluate
    | _ => if assertFailureHalt target fuel ev then some (.interrupted "target failure reached")
      else none

/-- Path-feasibility of a replay trace: every `.assume` event evaluates under the bounded
    evaluator to `tt` up to metadata (`InterpLang.boolLit?`). -/
@[expose] def PathFeasible (fuel : Nat) (evs : List (IEvent P)) : Prop :=
  ∀ arg, REvent.assume arg ∈ evs →
    (InterpLang.boundedEval (P := P) fuel arg.factory arg.store arg.expr).bind
      InterpLang.boolLit? = some true

variable [HasOldIdent P] [HasFvar P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- Strict record-only replay of `cex` through `runCallInterp π` at fuel `fuel` and call-depth
    limit `maxCallDepth`, halting on the target id. -/
@[expose] def replayWith (cex : CexA P (CmdExt P)) (target : AssertId P)
    (fuel : Nat)
    (π : String → Option (Procedure P (CmdExt P) Hdr) := fun _ => none)
    (maxCallDepth : Nat := defaultMaxCallDepth) :
    CEValidationVerdict StopReason :=
  let cfg : ReplayCfg P := { oracleConfig := .strict }
  (runReplay (runCallInterp (m := ReplayM P) π fuel cex.cfg maxCallDepth) cfg
    (assertFailureHalt target fuel) cex.oracle).1

/-- Genuineness: `cex` replays, at fuel `fuel` and call-depth limit `maxCallDepth`, to the
    target failure. -/
@[expose] def genuine (π : String → Option (Procedure P (CmdExt P) Hdr)) (target : AssertId P)
    (fuel : Nat) (cex : CexA P (CmdExt P)) (maxCallDepth : Nat := defaultMaxCallDepth) : Prop :=
  replayWith cex target fuel π maxCallDepth = .genuine

/-- Genuineness with path-feasibility of the enforcing production run's trace. -/
@[expose] def genuineFeasible (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (maxCallDepth : Nat := defaultMaxCallDepth) : Prop :=
  genuine π target fuel cex maxCallDepth ∧
    PathFeasible fuel
      (runReplayRun (runCallInterp (m := ReplayM P) π fuel cex.cfg maxCallDepth)
        { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
        cex.oracle).2.traceRev

/-- Genuineness of the enforcing production run. -/
@[expose] def genuineEnforced (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (maxCallDepth : Nat := defaultMaxCallDepth) : Prop :=
  (runReplay (runCallInterp (m := ReplayM P) π fuel cex.cfg maxCallDepth)
    { oracleConfig := .strict, interruptOn := enforceInterrupt target fuel }
    (assertFailureHalt target fuel) cex.oracle).1 = .genuine

end Calls

end -- public section

end Imperative
