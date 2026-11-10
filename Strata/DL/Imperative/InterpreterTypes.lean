/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics

/-! # Monadic-interpreter vocabulary types

The types shared by the monadic interpreter and its effect-monad instances:
`StopReason` (why a run stopped short of a terminal configuration),
`CEValidationVerdict` (the verdict of a counterexample replay), runtime stores (`RStore`) and
events (`REvent`), and `ReplayValueOps` (the executable value checks a language supplies).
Nothing here executes anything.
-/

namespace Imperative

public section

variable {P : PureExpr}
/-- The default call-depth limit of the monadic interpreter: the most calls a run may nest,
    each callee body counting one level.  A call nested deeper stops the run with
    `StopReason.callDepthExceeded`.  Each nested call holds native stack until it returns,
    and a self-recursive procedure exhausts the native stack of the Lean interpreter at a
    depth of about 100,000; the limit keeps runs well below it.  It is the default of every
    run option that sets the limit. -/
def defaultMaxCallDepth : Nat := 1000

/-- Why an interpreter run stopped short of a terminal configuration; a replay
    verdict that is neither genuine nor spurious carries one
    (`CEValidationVerdict.cantValidate`).

    Every constructor is *monad-generic*: it is thrown by code that is generic in
    the monadic interpreter's monad `m`.  A failure only one monad instance can raise
    belongs in that instance's own error type (`Core.EvalHalt` for `EvalM`), so
    there is no string-carrying catch-all to parse.

    The inductive is flat, but its constructors fall into five situations a caller
    can tell apart *from the constructor alone*.  The comment blocks below mark
    them:

    * **cannot compute** — the engine is fine and the program is fine, but the
      witness does not let replay compute a value (no fuel, no oracle choice, an
      expression that does not reduce);
    * **program error** — the replayed program is itself wrong, in a way the `Core`
      statement evaluator also errors on (`EvalError.InitVarExists`,
      `EvalError.AssignVarNotExists`, and the call-marshalling mismatches);
    * **unsupported construct** — the program is fine but this engine cannot
      execute the construct (nondeterminism where the engine has no oracle, a CFG
      procedure body, an unresolved callee);
    * **replay verdict** — not an error at all: replay reached a contradiction
      with an `assume`, so the candidate counterexample does not describe a real
      execution;
    * **deliberate stop** — not a failure: an instance's `emit` interrupted the run
      on purpose. -/
inductive StopReason where
  -- cannot compute
  | replayFuelExhausted
  /-- A call nested deeper than the run's call-depth limit (`defaultMaxCallDepth` unless the
      run sets another). -/
  | callDepthExceeded
  | oracleExhausted
  | expectedBooleanChoice
  | illTypedValue
  | expressionDidNotEvaluate
  | expressionWasNotBoolean
  -- program error
  /-- An `init` whose target is already defined (statement evaluator:
      `EvalError.InitVarExists`). -/
  | programInitTargetAlreadyDefined
  /-- A `set` whose target is undefined (statement evaluator:
      `EvalError.AssignVarNotExists`). -/
  | programSetTargetUndefined
  /-- A call whose argument count differs from the callee's input-parameter count. -/
  | programCallInputArityMismatch (procName : String)
  /-- A call one of whose left-hand-side variables is undefined in the caller store. -/
  | programCallLhsUndefined (procName : String)
  /-- A call whose left-hand-side count differs from the callee's output-parameter
      count. -/
  | programCallOutputArityMismatch (procName : String)
  /-- A callee that returned without defining one of its output parameters. -/
  | programCallOutputUndefinedOnReturn (procName : String)
  /-- A callee whose body ended by exiting through a label that no block of the body
      matches; a call returns only when the callee body ends normally. -/
  | programCallBodyExited (procName : String)
  -- unsupported construct
  /-- A nondeterministic `set x := *` whose type source is unavailable: the
      language's `InterpLang.typeOf` returned no type for `x`'s current value. -/
  | unsupportedNondetSet
  /-- A call whose callee name the callee environment does not resolve. -/
  | unsupportedCalleeNotFound (procName : String)
  /-- A CFG transfer to a label that the CFG has no block for. -/
  | unsupportedMissingBlockLabel
  -- replay verdict
  /-- An `assume` condition is false under the replay environment (`label` is the
      `assume`'s label). -/
  | assumptionFalseUnderReplay (label : String)
  -- deliberate stop (not a failure)
  /-- The run was **deliberately interrupted** — an instance's `emit` reached a
      condition it was told to stop on (for replay: the target assert/cover id).
      This is not a failure: the run stopped short of a terminal configuration on
      purpose, so downstream reasoning treats the reached configuration as a prefix
      of what the small-step semantics would allow, not as an error. Generic across
      monads (any instance may interrupt); the `reason` records why. -/
  | interrupted (reason : String)
  deriving Repr, BEq, DecidableEq

/-- English rendering of a `StopReason`, for user-facing diagnostics. -/
def StopReason.describe : StopReason → String
  | .replayFuelExhausted => "replay fuel was exhausted"
  | .callDepthExceeded => "the call-depth limit was exceeded"
  | .oracleExhausted => "the nondeterministic-choice oracle was exhausted"
  | .expectedBooleanChoice => "expected a Boolean oracle choice"
  | .illTypedValue => "an ill-typed value was produced"
  | .expressionDidNotEvaluate => "an expression did not evaluate"
  | .expressionWasNotBoolean => "an expression did not reduce to a Boolean"
  | .programInitTargetAlreadyDefined => "init target is already defined"
  | .programSetTargetUndefined => "set target is undefined"
  | .programCallInputArityMismatch procName =>
      s!"callee {procName} input arity mismatch"
  | .programCallLhsUndefined procName =>
      s!"callee {procName} output variable undefined"
  | .programCallOutputArityMismatch procName =>
      s!"callee {procName} output arity mismatch"
  | .programCallOutputUndefinedOnReturn procName =>
      s!"callee {procName} output undefined on return"
  | .programCallBodyExited procName =>
      s!"callee {procName} body exited through an unmatched label"
  | .unsupportedNondetSet =>
    "set-nondet: the type of the assigned variable's current value is unknown"
  | .unsupportedCalleeNotFound procName => s!"callee {procName} not found"
  | .unsupportedMissingBlockLabel => "CFG: missing block label"
  | .assumptionFalseUnderReplay label =>
      s!"assumption ({label}) is false under replay environment"
  | .interrupted reason => s!"run interrupted: {reason}"

instance : ToString StopReason where
  toString := StopReason.describe

/-- The counterexample-validation verdict: the result of deciding whether one
    given counterexample is genuine.  It is payload-free (the counterexample
    being validated is the validator's argument, so the verdict need not echo it
    back) and parameterized by the type `ρ` of `cantValidate` reason, so a
    single type serves both program replay (`ρ := StopReason`) and model
    checking (`ρ := String`). -/
inductive CEValidationVerdict (ρ : Type) where
  | genuine
  | spurious
  | cantValidate (reason : ρ)
  deriving Repr, BEq, DecidableEq

/-- A *runtime store*: the monadic interpreter's store, mapping identifiers to *value
    expressions* (`P.Expr`), as opposed to a semantic store (`SemanticStore P`), which holds
    semantic values (`P.Val`). -/
abbrev RStore (P : PureExpr) := P.Ident → Option P.Expr

/-- Bind `x` to `r` in a runtime store. -/
@[expose] def RStore.update [DecidableEq P.Ident] (σ : RStore P) (x : P.Ident) (r : P.Expr) :
    RStore P :=
  fun y => if y = x then some r else σ y

/-- The runtime counterpart of `projectStore`: the inner store restricted to the names the parent
    store defines. -/
@[expose] def RStore.project (σ_parent σ_inner : RStore P) : RStore P :=
  fun x => if (σ_parent x).isSome then σ_inner x else none

/-- The runtime counterpart of `dropVars`: the store with every name of `D` undefined. -/
@[expose] def RStore.dropVars [DecidableEq P.Ident] (D : List P.Ident) (σ : RStore P) :
    RStore P :=
  fun x => if x ∈ D then none else σ x

/-- Executable value checks required by generic replay, over the runtime factory `RF`. -/
structure ReplayValueOps (P : PureExpr) (RF : Type) where
  isValue : RF → P.Expr → Bool
  hasType : RF → P.Expr → P.Ty → Bool := fun _ _ _ => true
  sameType : RF → P.Expr → P.Expr → Bool := fun _ _ _ => true

/-- Every value bound in `σ` is a value of some type under the factory `f`
    (`HasVal.valueOfTy`).  The reference `set` rules require the value already
    stored in the target slot to witness a type (`HasVal.valueOfStoredTy`), so a
    replayer that only compares the old and new values with `sameType` is sound
    only on stores satisfying this. -/
@[expose] def StoreTyped [HasVal P] (f : P.Factory) (σ : SemanticStore P) : Prop :=
  ∀ x v, σ x = some v → ∃ ty, HasVal.valueOfTy f v ty

/-- Soundness of the executable type checks of `ops` against the semantic typed-value
    predicate `HasVal.valueOfTy`, through the runtime factory `rf F` of a factory `F` and the
    denotation `den F` of runtime values:

    * `hasType`: a runtime value that passes `isValue` and `hasType (rf F) r ty` denotes a value
      of `ty`;
    * `sameType`: a runtime value that passes `isValue` and `sameType (rf F) old r`, against an
      `old` runtime value denoting a value of type `ty`, denotes a value of `ty`. -/
structure ReplayValueOps.TypedSound [HasVal P] {RF : Type} (ops : ReplayValueOps P RF)
    (rf : P.Factory → RF) (den : P.Factory → P.Expr → Option P.Val) : Prop where
  hasType : ∀ F r ty, ops.isValue (rf F) r = true → ops.hasType (rf F) r ty = true →
    ∃ v, den F r = some v ∧ HasVal.valueOfTy F v ty
  sameType : ∀ F old r vo ty, den F old = some vo → HasVal.valueOfTy F vo ty →
    ops.isValue (rf F) r = true → ops.sameType (rf F) old r = true →
    ∃ v, den F r = some v ∧ HasVal.valueOfTy F v ty

/-! ## Runtime events -/

/-- An event argument as the monadic interpreter captures it: the runtime factory `RF` and the
    runtime store in place of the semantic factory and store of `EventArg`. -/
structure REventArg (P : PureExpr) (RF : Type) where
  /-- Runtime factory active when the event was emitted. -/
  factory : RF
  /-- Runtime store observed when the event was emitted. -/
  store : RStore P
  /-- Source-level label identifying the observed command. -/
  label : String
  /-- Unevaluated condition captured by the event. -/
  expr : P.Expr
  /-- Source and analysis metadata attached to the command. -/
  metadata : MetaData P

/-- The events the monadic interpreter emits, over runtime factories and stores. -/
inductive REvent (P : PureExpr) (RF : Type) where
  | assert : REventArg P RF → REvent P RF
  | assume : REventArg P RF → REvent P RF
  | cover : REventArg P RF → REvent P RF

/-- The runtime event trace a base command emits at its input snapshot: the runtime counterpart
    of `Cmd.emittedEvents`. -/
@[expose] def Cmd.rEmittedEvents {RF : Type} :
    Cmd P → RF → RStore P → List (REvent P RF)
  | .assert label expr metadata, f, σ =>
      [.assert { factory := f, store := σ, label, expr, metadata }]
  | .assume label expr metadata, f, σ =>
      [.assume { factory := f, store := σ, label, expr, metadata }]
  | .cover label expr metadata, f, σ =>
      [.cover { factory := f, store := σ, label, expr, metadata }]
  | _, _, _ => []

end -- public section

end Imperative
