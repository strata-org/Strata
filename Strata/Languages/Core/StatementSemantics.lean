/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.StmtCFGCallSemantics
public import Strata.Languages.Core.CoreGen
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.OperationalSemanticsProps
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
-- statement/expression semantics: variable initialization and havoc, and
-- command/body execution.  Expression-list evaluation and
-- reading/updating/initializing stores are Imperative's `EvalExpressions`,
-- `ReadValues`, `UpdateStates` and `InitStates`.  Core's call semantics is the
-- generic one at `Expression`: `HavocVars`, `withOldSnapshots`, `InitCallFrame`,
-- `defaultAssertEvents`, `assumeEvents`, `CallEntry`, `CallExit` and the event
-- relations `EvalCommandE`, `CoreBodyExecE`, `EvalCommandContractE` are
-- abbreviations of their `Imperative` counterparts.
-- ---------------------------------------------------------------------------

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
  (val : P.Val)
  : SemanticStore P :=
  λ k ↦ if (@Decidable.decide (k = ident) (P.EqIdent k ident))
    then some val
    else (σ k)

def updatedStates'
  (σ : SemanticStore P)
  (idvals : List (P.Ident × P.Val))
  : SemanticStore P :=
  match idvals with
  | [] => σ
  | (ident, val) :: rest  => updatedStates' (updatedState σ ident val) rest

def updatedStates
  (σ : SemanticStore P)
  (idents : List P.Ident)
  (vals : List P.Val)
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
    (p : Procedure) (inputVals outOnlyVals : List Expression.Val)
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
### Event semantics: `EvalCommandE` and `CoreBodyExecE`
-/

/-- Event-producing execution of a Core procedure body, structured or CFG: the
    generic `BigStepE` at `Expression`. -/
abbrev CoreBodyExecE
    (π : String → Option Procedure) :
    Procedure.Body → Env Expression → CoreStore → Trace Expression → Prop :=
  BigStepE π

/-- Event-producing Core command semantics: the generic `EvalCmdExtE` at
    `Expression`.  Base commands delegate to `EvalCmdE`; a procedure call emits
    its non-free preconditions as assertions, runs its body run-to-completion,
    and emits its non-free postconditions as assertions. -/
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

/-! ## Old-variable environment augmentation -/

/-- Augment an environment with old-variable bindings for a set of variables
    whose pre-state values are snapshotted (the inout parameters / referenced
    globals of a procedure). This is the environment-level counterpart of
    `withOldSnapshots`; the factory is preserved. -/
def withOldBindings
    (modifies : List Expression.Ident) (ρ : Env Expression) : Env Expression :=
  { ρ with store := withOldSnapshots modifies ρ.store }

/-- Event-producing contract abstraction for Core commands: the generic
`EvalCmdExtContractE` at `Expression`.

Base commands retain `EvalCmdE` behavior. A procedure call emits non-free
preconditions as assertions at the initialized callee frame, havocs the output
formals, and then emits every postcondition as an assumption at the post-havoc
snapshot. No procedure body is executed. -/
abbrev EvalCommandContractE (π : String → Option Procedure) :
    Expression.Factory → CoreStore → Command → CoreStore → Trace Expression → Prop :=
  EvalCmdExtContractE π

end Core

end -- public section
