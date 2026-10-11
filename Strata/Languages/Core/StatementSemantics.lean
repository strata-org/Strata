/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.StmtCallSemantics
public import Strata.Languages.Core.CoreGen
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.Semantics
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Util.FuncAttr
public import Strata.Languages.Core.FactoryWF
import Std.Tactic.BVDecide.Normalize.Prop

---------------------------------------------------------------------

public section

namespace Core

open Imperative

-- ---------------------------------------------------------------------------
-- From this point on, we define the inductive relations that specify Core
-- statement/expression semantics: check evaluation, variable initialization
-- and havoc, and command/body execution.  Expression-list evaluation and
-- reading/updating/initializing stores are Imperative's `EvalExpressions`,
-- `ReadValues`, `UpdateStates` and `InitStates`.  Core's call semantics is the
-- generic one at `Expression`: `HavocVars`, `withOldSnapshots`, `InitCallFrame`,
-- `defaultAssertEvents`, `assumeEvents`, `CallEntry`, `CallExit` and the event
-- relations `EvalCommandE`, `CoreBodyExecE`, `EvalCommandContractE` are
-- abbreviations of their `Imperative` counterparts.
-- ---------------------------------------------------------------------------

/-- Evaluate assertion-style checks for failure-flag call semantics, reporting
whether any check evaluates to false. The explicit `isDefined` premises cover
all syntactic free variables, including variables in branches that evaluation
does not take. Event semantics records the checks with `defaultAssertEvents`
instead. -/
inductive EvalChecks (fac : Expression.Factory) (σ : CoreStore) :
    List Expression.Expr → Bool → Prop where
  | eval_none : EvalChecks fac σ [] false
  | eval_pass :
      isDefined σ (HasFvars.getFvars e) →
      Expression.eval fac σ e = some HasBool.tt →
      EvalChecks fac σ es failed →
      EvalChecks fac σ (e :: es) failed
  | eval_fail :
      isDefined σ (HasFvars.getFvars e) →
      Expression.eval fac σ e = some HasBool.ff →
      EvalChecks fac σ es failed →
      EvalChecks fac σ (e :: es) true

/-- Every assumption in a failure-flag contract call is syntactically defined
and evaluates to true. A false assumption admits no execution. Event semantics
records the assumptions with `assumeEvents` instead. -/
abbrev AssumeExprs (fac : Expression.Factory) (σ : CoreStore)
    (es : List Expression.Expr) : Prop :=
  Forall (fun e =>
    isDefined σ (HasFvars.getFvars e) ∧
    Expression.eval fac σ e = some HasBool.tt) es

inductive InitVars : SemanticStore P → List P.Ident → SemanticStore P → Prop where
  | init_none :
    InitVars σ [] σ
  | init_some :
    InitState P σ x v σ' →
    InitVars σ' xs σ'' →
    InitVars σ (x :: xs) σ''

/-- Nondeterministically updates existing slots while preserving each slot's
monomorphic runtime type: the generic `Calls.HavocVars`. -/
abbrev HavocVars {P : PureExpr} [HasVal P] :
    P.Factory → SemanticStore P → List P.Ident → SemanticStore P → Prop :=
  Calls.HavocVars

inductive TouchVars : SemanticStore P → List P.Ident → SemanticStore P → Prop where
  | none :
    TouchVars σ [] σ
  | init_some :
    InitState P σ x v σ' →
    TouchVars σ' xs σ'' →
    TouchVars σ (x :: xs) σ''
  | update_some :
    UpdateState P σ x v σ' →
    TouchVars σ' xs σ'' →
    TouchVars σ (x :: xs) σ''

inductive Inits : SemanticStore P → SemanticStore P → Prop where
  | init : InitVars σ xs σ' → Inits σ σ'

def updatedState
  (σ : SemanticStore P)
  (ident : P.Ident)
  (val : P.Expr)
  : SemanticStore P :=
  λ k ↦ if (@Decidable.decide (k = ident) (P.EqIdent k ident))
    then some val
    else (σ k)

def updatedStates'
  (σ : SemanticStore P)
  (idvals : List (P.Ident × P.Expr))
  : SemanticStore P :=
  match idvals with
  | [] => σ
  | (ident, val) :: rest  => updatedStates' (updatedState σ ident val) rest

def updatedStates
  (σ : SemanticStore P)
  (idents : List P.Ident)
  (vals : List P.Expr)
  : SemanticStore P :=
  updatedStates' σ $ idents.zip vals

/-- Core's `old` identifiers are the `"old "`-prefixed names (`CoreIdent.mkOld`). -/
instance : HasOldIdent Expression where
  mkOld g := CoreIdent.mkOld g.name

/-- Extend a store with `old` snapshots: every `g ∈ snapshot` gains a binding of
    `CoreIdent.mkOld g.name` to `g`'s current value. All other lookups, `g`
    itself included, are unchanged.  The generic `Calls.withOldSnapshots` at
    `Expression`. -/
abbrev withOldSnapshots (snapshot : List Expression.Ident) (σ : CoreStore) : CoreStore :=
  Calls.withOldSnapshots snapshot σ

/-- Initialize a callee-local frame without colliding with caller names.

Input and inout formals are initialized from evaluated `inputVals`, and
output-only formals from the current values of the corresponding caller `out`
actuals. The frame also snapshots each inout formal as `old`, so postconditions
mentioning `old g` are evaluable in the callee.  The generic
`Calls.InitCallFrame` at `Expression`. -/
abbrev InitCallFrame
    (p : Procedure) (inputVals outOnlyVals : List Expression.Expr)
    (σAO : CoreStore) : Prop :=
  Calls.InitCallFrame p inputVals outOnlyVals σAO

/-- Capture non-free specification clauses as assertion events at a semantic
snapshot. Free clauses are not call-site obligations.  The generic
`Calls.defaultAssertEvents` at `Expression`. -/
abbrev defaultAssertEvents
    (fac : Expression.Factory) (σ : CoreStore)
    (checks : ListMap CoreLabel Procedure.Check) : Trace Expression :=
  Calls.defaultAssertEvents fac σ checks

/-- Capture every specification clause as an assumption event at a semantic
snapshot. Contract postconditions, including free ones, constrain the abstract
callee result.  The generic `Calls.assumeEvents` at `Expression`. -/
abbrev assumeEvents
    (fac : Expression.Factory) (σ : CoreStore)
    (checks : ListMap CoreLabel Procedure.Check) : Trace Expression :=
  Calls.assumeEvents fac σ checks

/-- Core-level small-step configuration. -/
abbrev CoreConfig := Imperative.Config Expression Command

/-- Shared prologue of every call rule: evaluate the input and inout arguments,
    read the caller's `out` variables, and build the collision-free callee frame.
    The generic `Calls.CallEntry` at `Expression`. -/
abbrev CallEntry (fac : Expression.Factory) (σ : CoreStore) (p : Procedure)
    (callArgs : List (CallArg Expression)) (σAO : CoreStore) : Prop :=
  Calls.CallEntry fac σ p callArgs σAO

/-- Shared epilogue of every call rule: read the callee's output formals in its
    final store and write them back positionally to the caller's `out`/`inout`
    variables.  The generic `Calls.CallExit` at `Expression`. -/
abbrev CallExit (fac : Expression.Factory) (σ : CoreStore) (p : Procedure)
    (callArgs : List (CallArg Expression)) (σEnd σ' : CoreStore) : Prop :=
  Calls.CallExit fac σ p callArgs σEnd σ'

/-!
### Mutual inductive: `EvalCommand` and `CoreStepStar`

`CoreStepStar` is the reflexive-transitive closure of `StepStmt` specialized
to the Core language with `EvalCommand` as the command semantics.  It is
defined mutually with `EvalCommand` so that `call_sem` can reference it
without violating Lean's strict positivity requirement.

The generic `ReflTrans (StepStmt ...)` cannot be used here because it would
place `EvalCommand` in a non-strictly-positive position.
-/

mutual

/-- Reflexive-transitive closure of `StepStmt` for the Core language,
    defined mutually with `EvalCommand` to satisfy strict positivity. The
    immutable factory is carried by each configuration's environment and read
    there by every step. -/
inductive CoreStepStar
    (π : String → Option Procedure) :
    CoreConfig → CoreConfig → Prop where
  | refl : CoreStepStar π c c
  | step :
    Imperative.StepStmt Expression (EvalCommand π) c₁ c₂ →
    CoreStepStar π c₂ c₃ →
    ----
    CoreStepStar π c₁ c₃

/-- Execution of a procedure body. Only structured bodies have an executable
    semantics; the `.cfg` arm of `Procedure.Body` has no inhabitant of
    `CoreBodyExec`.

    The initial execution environment `ρ` is an explicit argument carrying the
    store, active factory, and entry failure flag. The factory is immutable
    during execution, so the body's output factory equals `ρ.factory`.

    For structured bodies, the body is wrapped in `Stmt.block "" ss #[]` so that
    variable scoping introduced by the body does not leak past the procedure
    boundary.  This wrapping mirrors
    `Specification.AssertValidInProcedure` and the `procToVerifyStmt` pipeline. -/
inductive CoreBodyExec
    (π : String → Option Procedure) :
    Procedure.Body → Env Expression → CoreStore → Bool → Prop where
  | structured {ss ρ ρ'} :
    CoreStepStar π
      (.stmt (Stmt.block "" ss #[]) ρ)
      (.terminal ρ') →
    CoreBodyExec π (.structured ss) ρ ρ'.store ρ'.hasFailure

/-- Core command semantics. The first relation index `g` is the active
    expression factory. -/
inductive EvalCommand (π : String → Option Procedure) :
  Expression.Factory → CoreStore → Command → CoreStore → Bool → Prop where
  | cmd_sem {g σ c σ' f} :
    Imperative.EvalCmd (P := Expression) g σ c σ' f →
    ----
    EvalCommand π g σ (CmdExt.cmd c) σ' f

  /-- Arguments are matched positionally in three alignments: `inArgs`
      (`getInputExprs`) ↔ `p.header.inputs`; `lhs` (`getLhs`) ↔
      `p.header.outputs`; and `getOutArgs callArgs` ↔
      `ListMap.keys p.header.getOutputOnlyParams`. The third alignment follows
      from the second because every inout formal is passed as `.inoutArg`. -/
  -- TODO: Instantiate procedure type variables for polymorphic calls.
  | call_sem {g σ n p callArgs σ' σ_final
      bodyFailed preFailed postFailed md σAO} :
    π n = .some p →
    CallEntry g σ p callArgs σAO →
    EvalChecks g σAO
      (Procedure.Spec.getDefaultCheckExprs p.spec.preconditions) preFailed →
    CoreBodyExec π p.body ⟨σAO, g, false⟩ σ_final bodyFailed →
    EvalChecks g σ_final
      (Procedure.Spec.getDefaultCheckExprs p.spec.postconditions) postFailed →
    CallExit g σ p callArgs σ_final σ' →
    ----
    EvalCommand π g σ (CmdExt.call n callArgs md) σ'
      ((preFailed || bodyFailed) || postFailed)

end

/-!
### Mutual event semantics: `EvalCommandE` and `CoreBodyExecE`
-/

/-- Event-producing execution of a structured Core procedure body: the generic
    `BigStepE` at `Expression`. -/
abbrev CoreBodyExecE
    (π : String → Option Procedure) :
    Procedure.Body → Env Expression → CoreStore → Trace Expression → Prop :=
  BigStepE π

/-- Event-producing Core command semantics: the generic `EvalCmdExtE` at
    `Expression`.  Base commands delegate to `EvalCmdE`; a procedure call emits
    its non-free preconditions as assertions, runs its body run-to-completion,
    and emits its non-free postconditions as assertions.  The expression factory
    is immutable, so a call runs its body from the entry environment and
    interprets every contract clause at the active factory. -/
abbrev EvalCommandE
    (π : String → Option Procedure) :
    Expression.Factory → CoreStore → Command → CoreStore → Trace Expression → Prop :=
  EvalCmdExtE π

/-- Reflexive-transitive Core statement execution with chronological events. -/
abbrev CoreStepStarE
    (π : String → Option Procedure) :=
  StepStmtExtStarE π

/-- Core-level event-producing single-step relation. -/
abbrev CoreStepE
    (π : String → Option Procedure) :=
  StepStmtExtE π

/-- Core-level single-step relation. -/
abbrev CoreStep
    (π : String → Option Procedure) :=
  Imperative.StepStmt Expression (EvalCommand π)

abbrev EvalStatement (π : String → Option Procedure) :
    Imperative.Env Expression → Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtSmall Expression (EvalCommand π)

abbrev EvalStatements (π : String → Option Procedure) :
    Imperative.Env Expression → List Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtsSmall Expression (EvalCommand π)

/-! ## Old-variable environment augmentation -/

/-- Augment an environment with old-variable bindings for a set of variables
    whose pre-state values are snapshotted (the inout parameters / referenced
    globals of a procedure). This is the environment-level counterpart of
    `withOldSnapshots`; `hasFailure` is preserved. -/
def withOldBindings
    (modifies : List Expression.Ident) (ρ : Env Expression) : Env Expression :=
  { ρ with store := withOldSnapshots modifies ρ.store }

/-! ## Assert detection -/

/-- Assert detection for Core configurations.

    Core commands have type `Command = CmdExt Expression`, so an assert
    command appears as `.cmd (CmdExt.cmd (Cmd.assert l e md))`.
    Call commands (`.cmd (CmdExt.call ...)`) never trigger assert detection. -/
@[expose] def coreIsAtAssert : CoreConfig → Imperative.AssertId Expression → Prop
  | .stmt (.cmd (.cmd (.assert label expr _))) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .stmts ((.cmd (.cmd (.assert label expr _))) :: _) _, aid =>
    aid.label = label ∧ aid.expr = expr
  | .block _ _ inner, aid => coreIsAtAssert inner aid
  | .seq inner _, aid => coreIsAtAssert inner aid
  | _, _ => False

---------------------------------------------------------------------

inductive EvalCommandContract : (String → Option Procedure)  →
  Expression.Factory → CoreStore → Command → CoreStore → Bool → Prop where
  | cmd_sem {π fac σ c σ' f} :
    Imperative.EvalCmd (P := Expression) fac σ c σ' f →
    ----
    EvalCommandContract π fac σ (CmdExt.cmd c) σ' f

  /-- Contract-based semantics: like `EvalCommand.call_sem` but replaces
      body execution with havoc + postcondition assumptions.
      Same positional matching as `EvalCommand.call_sem`. -/
  -- TODO: Instantiate procedure type variables for polymorphic calls.
  | call_sem {π σ σO n p callArgs σ' preFailed md fac σAO} :
    π n = .some p →
    CallEntry fac σ p callArgs σAO →
    EvalChecks fac σAO
      (Procedure.Spec.getDefaultCheckExprs p.spec.preconditions) preFailed →
    HavocVars fac σAO (ListMap.keys p.header.outputs) σO →
    AssumeExprs fac σO (Procedure.Spec.getCheckExprs p.spec.postconditions) →
    CallExit fac σ p callArgs σO σ' →
    ----
    EvalCommandContract π fac σ (.call n callArgs md) σ' preFailed

/-- Event-producing contract abstraction for Core commands: the generic
`EvalCmdExtContractE` at `Expression`.

Base commands retain `EvalCmdE` behavior. A procedure call emits non-free
preconditions as assertions at the initialized callee frame, havocs the output
formals, and then emits every postcondition as an assumption at the post-havoc
snapshot. No procedure body is executed. -/
abbrev EvalCommandContractE (π : String → Option Procedure) :
    Expression.Factory → CoreStore → Command → CoreStore → Trace Expression → Prop :=
  EvalCmdExtContractE π

abbrev EvalStatementContract (π : String → Option Procedure) :
    Imperative.Env Expression → Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtSmall Expression (EvalCommandContract π)

abbrev EvalStatementsContract (π : String → Option Procedure) :
    Imperative.Env Expression → List Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtsSmall Expression (EvalCommandContract π)

end Core

end -- public section
