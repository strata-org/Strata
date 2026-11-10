/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterTypes
public import Strata.DL.Imperative.InterpreterConfig
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.CmdTrace

/-! # The monadic interpreter — one small-step engine

A single small-step evaluation engine over the imperative semantics, written
tagless-final against `InterpEffects`, which bundles the two axes the engine
abstracts over as capabilities of the monad `m`:

* **nondeterminism** — `choose` produces a value of a requested type
  (`P.Ty`): the oracle instance pops it from the remaining oracle tail, the
  symbolic instance mints a fresh variable, a random instance samples;
* **observation** — `emit` observes an `Event`; the replay instance records it in
  its trace and stops only when its configured stop hook fires on the event, so
  the engine itself never polls a predicate.

Expression evaluation is not an axis (it does not vary per instance): the
fuel-bounded evaluator lives in the language typeclass `InterpLang.boundedEval`
(Core: `Core.evalBounded`, never the unbounded `P.eval`), which the engine
applies directly.

The engine mirrors the reference event-trace relation `EvalCmdE`/`StepStmtE`
faithfully: `.assert`/`.assume`/`.cover` emit their *unevaluated* condition and
runtime snapshot (`Cmd.rEmittedEvents`) and skip; target-detection sits on top of that
faithful image (in the instance's `emit`).

Lemmas about the engine are in `InterpreterProps.lean`.
-/

namespace Imperative

public section

variable {P : PureExpr} {CmdT : Type} {m : Type → Type}

/-- The two axes the monadic interpreter abstracts over, as capabilities of `m`.

    `choose` returns `m P.Expr` (not `Option`): "cannot choose" (oracle
    exhausted, ill-typed) is routed through the monad's error channel, and the
    requested `P.Ty` covers guards too (a Boolean guard is a value of
    `HasBool.boolTy`).  `emit` observes an event and may record instance-local
    state.  `branch` resolves a deterministic guard whose value is not a Boolean
    literal; its default throws, as the reference semantics prescribes. -/
class InterpEffects (P : PureExpr) [InterpLang P] (m : Type → Type) where
  /-- Resolve one nondeterministic choice: a runtime value of the requested type. -/
  choose   : InterpLang.RFactory P → RStore P → P.Ty → m P.Expr
  /-- Observe one runtime event. -/
  emit     : IEvent P → m Unit
  /-- Resolve a deterministic guard that evaluated to a value that is neither `HasBool.tt`
      nor `HasBool.ff`: `true` takes the then-branch (loop entry), `false` the else-branch
      (loop exit).  By default it throws `expressionWasNotBoolean`, since the reference
      semantics has no step there; a symbolic instance may fork instead. -/
  branch [MonadExcept StopReason m] (factory : InterpLang.RFactory P) (store : RStore P)
      (value : P.Expr) : m Bool := throw .expressionWasNotBoolean

/-- A monadic per-command stepper: given the current fuel and `Env`, it produces the
    configuration the command *becomes*, emitting events and signalling "cannot
    continue" through the monad's error channel (no result `Option`).  Returning an
    `IConfig` rather than a store leaves room for a stepper that splices a callee body
    into the configuration; the steppers in this development run a call to completion,
    as the reference semantics does, and return `.terminal`. -/
abbrev StepCmdM (P : PureExpr) [InterpLang P] (CmdT : Type) (m : Type → Type) :=
  Nat → IEnv P → CmdT → m (IConfig P CmdT)

/-- Generic base-command stepper for `Cmd P`.  Deterministic `.init`/`.set`
    reduce their RHS through `InterpLang.boundedEval`; nondeterministic `.init` draws a typed
    value through `choose`; `.assert`/`.assume`/`.cover` emit their captured
    condition (via `Cmd.rEmittedEvents`) and leave the store unchanged, exactly
    as `EvalCmdE`.

    Nondeterministic `.set x := *` (a `havoc x`) looks up `x`'s current value
    (`programSetTargetUndefined` if `x` is unbound), takes its type through
    `InterpLang.typeOf` (`unsupportedNondetSet` if the type is unknown), draws a
    value of that type through `choose`, and applies the same `isValue`/`sameType`
    checks as a deterministic `.set` (`illTypedValue` otherwise). -/
def stepBaseCmdStore [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
    (fuel : Nat) (factory : InterpLang.RFactory P)
    (store : IStore P) (cmd : Cmd P) : m (IStore P) := do
    let ops := InterpLang.ops (P := P)
    match cmd with
    | .init name ty (.det e) _ =>
      if (store.get name).isSome then
        throw .programInitTargetAlreadyDefined
      match InterpLang.boundedEval (P := P) fuel factory store.get e with
      | none => throw .expressionDidNotEvaluate
      | some v =>
        if ops.isValue factory v && ops.hasType factory v ty then
          return store.update name v
        else throw .illTypedValue
    | .init name ty .nondet _ =>
      if (store.get name).isSome then
        throw .programInitTargetAlreadyDefined
      let v ← InterpEffects.choose (P := P) factory store.get ty
      return store.update name v
    | .set name (.det e) _ =>
      match store.get name with
      | none => throw .programSetTargetUndefined
      | some old =>
        match InterpLang.boundedEval (P := P) fuel factory store.get e with
        | none => throw .expressionDidNotEvaluate
        | some v =>
          if ops.isValue factory v && ops.sameType factory old v then
            return store.update name v
          else throw .illTypedValue
    | .set name .nondet _ =>
      match store.get name with
      | none => throw .programSetTargetUndefined
      | some old =>
        match InterpLang.typeOf (P := P) factory old with
        | none => throw .unsupportedNondetSet
        | some ty =>
          let v ← InterpEffects.choose (P := P) factory store.get ty
          if ops.isValue factory v && ops.sameType factory old v then
            return store.update name v
          else throw .illTypedValue
    | .assert _ _ _ | .assume _ _ _ | .cover _ _ _ =>
      (Cmd.rEmittedEvents (P := P) cmd factory store.get).forM (InterpEffects.emit (P := P))
      return store

/-- The base config-level command stepper (for `CmdT = Cmd P`): run the atomic
    base command via `stepBaseCmdStore` and present the result as a `.terminal`
    configuration. -/
def baseStepCmd [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m] :
    StepCmdM P (Cmd P) m :=
  fun fuel env cmd => do
    let store ← stepBaseCmdStore fuel env.factory env.store cmd
    return .terminal { env with store }

/-- Resolve a guard to a branch: `true` takes the then-branch (loop entry), `false` the
    else-branch (loop exit).  A deterministic guard is evaluated with `InterpLang.boundedEval`, a
    nondeterministic one draws a value of the Boolean type through `choose`.  The value must be
    `HasBool.tt` or `HasBool.ff` up to metadata (`InterpLang.boolLit?`); any other evaluated value
    is handed to `InterpEffects.branch` (concrete instances throw `expressionWasNotBoolean` there),
    any other chosen value is an error (`expectedBooleanChoice`). -/
def resolveGuard [HasBool P] [DecidableEq P.Ident] [InterpLang P] [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m] (fuel : Nat) (env : IEnv P) : ExprOrNondet P → m Bool
  | .det condition =>
    match InterpLang.boundedEval (P := P) fuel env.factory env.store.get condition with
    | some value =>
      match InterpLang.boolLit? value with
      | some true => pure true
      | some false => pure false
      | none => InterpEffects.branch (P := P) env.factory env.store.get value
    | none => throw .expressionDidNotEvaluate
  | .nondet => do
    let value ←
      InterpEffects.choose (P := P) env.factory env.store.get (HasBool.boolTy (P := P))
    match InterpLang.boolLit? value with
    | some true => pure true
    | some false => pure false
    | none => throw .expectedBooleanChoice

/-- One small step over `IConfig`, monadic and event-emitting: it resolves
    nondeterminism and events through `InterpEffects`, evaluates expressions with
    `InterpLang.boundedEval`, and delegates commands to `stepCmd`.  Guards are resolved by
    `resolveGuard`.

    A block opens with the frame `ScopeFrame.opened` of the current store; a step of a block's
    inner configuration updates the frame with `ScopeFrame.record`, and the block's exit store is
    `ScopeFrame.exit`.

    Returns the next configuration.  A terminal/exiting configuration steps to
    itself (a no-op) — the driver `runInterp` detects those and stops, so there
    is no result `Option`; can't-continue is the monad's error channel. -/
def stepInterp [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
    [CmdDefs P CmdT] [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
    (stepCmd : StepCmdM P CmdT m) (fuel : Nat) :
    IConfig P CmdT → m (IConfig P CmdT)
  | .stmt stmt env => do
    match stmt with
    | .cmd cmd => stepCmd fuel env cmd
    | .block label body _ =>
      return .block (some label) (.opened env.store) (.stmts body env)
    | .ite guard thenStmts elseStmts _ =>
      let choice ← resolveGuard fuel env guard
      return .block .none (.opened env.store)
        (.stmts (if choice then thenStmts else elseStmts) env)
    | .loop guard measure invariants body metadata =>
      let enter ← resolveGuard fuel env guard
      return if enter then
          .seq (.block .none (.opened env.store) (.stmts body env))
            [.loop guard measure invariants body metadata]
        else .terminal env
    | .exit label _ => return .exiting label env
    | .typeDecl _ _ => return .terminal env
  | .stmts stmts env => do
    match stmts with
    | [] => return .terminal env
    | [stmt] => return .seqs (.stmt stmt env) 0
    | stmt :: rest => return .seq (.stmt stmt env) rest
  | .terminal env => pure (.terminal env)
  | .exiting label env => pure (.exiting label env)
  | .seq inner rest => do
    match inner with
    | .terminal env => return .stmts rest env
    | .exiting label env => return .exiting label env
    | _ =>
      let inner ← stepInterp stepCmd fuel inner
      return .seq inner rest
  | .seqs inner k => do
    match inner with
    | .terminal env =>
      match k with
      | 0 => return .stmts [] env
      | k + 1 => return .seqs (.stmts [] env) k
    | .exiting label env =>
      match k with
      | 0 => return .exiting label env
      | k + 1 => return .seqs (.exiting label env) k
    | _ =>
      let inner' ← stepInterp stepCmd fuel inner
      match inner' with
      | .seqs c j => return .seqs c (j + k + 1)
      | _ => return .seqs inner' k
  | .block label frame inner => do
    match inner with
    | .terminal env =>
      return .terminal { env with store := frame.exit env.store }
    | .exiting exitLabel env =>
      let env := { env with store := frame.exit env.store }
      if label = some exitLabel then return .terminal env
      else return .exiting exitLabel env
    | _ =>
      let inner' ← stepInterp stepCmd fuel inner
      return .block label (frame.record inner.levelCmd?) inner'

/-- Fuel-bounded driver: iterate `stepInterp` until a terminal/exiting
    configuration or out of fuel.  Out of fuel with a non-terminal configuration
    throws `replayFuelExhausted`.

    The single `fuel` argument is the decreasing measure *and* the bound each step
    hands to `InterpLang.boundedEval`. -/
def runInterp [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
    [CmdDefs P CmdT] [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
    (stepCmd : StepCmdM P CmdT m) :
    Nat → IConfig P CmdT → m (IConfig P CmdT)
  | fuel, cfg =>
    match cfg with
    | .terminal _ | .exiting _ _ => pure cfg
    | _ =>
      match fuel with
      | 0 => throw .replayFuelExhausted
      | fuel + 1 => do
        let next ← stepInterp stepCmd (fuel + 1) cfg
        runInterp stepCmd fuel next

end -- public section

end Imperative
