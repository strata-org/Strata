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

/-- Case analysis on `EvalCommandE` by its three rules, as `EvalCmdExtE.casesOn'`. -/
@[elab_as_elim, cases_eliminator]
theorem EvalCommandE.casesOn' {π : String → Option Procedure}
    {motive : ∀ fac σ c σ' evs, EvalCommandE π fac σ c σ' evs → Prop}
    {fac : Expression.Factory} {σ : CoreStore} {c : Command} {σ' : CoreStore}
    {evs : Trace Expression} (h : EvalCommandE π fac σ c σ' evs)
    (cmd_sem : ∀ {fac σ c σ' emitted} (h : EvalCmdE (P := Expression) fac σ c σ' emitted),
      motive fac σ (.cmd c) σ' emitted (EvalCmdExtE.cmd_sem h))
    (call_sem : ∀ {σ n tyArgs p callArgs σ' σ_final bodyEvents md fac σAO}
      (hπ : Calls.typeInstantiatedCallee π n tyArgs = .some p)
      (hno : p.body.isOpaque = false)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hbody : CoreBodyExecE π p.body ⟨σAO, fac⟩ σ_final bodyEvents)
      (hexit : Calls.CallExit fac σ p callArgs σ_final σ'),
      motive fac σ (.call n tyArgs callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          bodyEvents ++
          Calls.defaultAssertEvents fac σ_final p.spec.postconditions)
        (EvalCmdExtE.call_sem hπ hno hentry hbody hexit))
    (call_abstract_sem : ∀ {σ σO n tyArgs p callArgs σ' md fac σAO}
      (hπ : Calls.typeInstantiatedCallee π n tyArgs = .some p)
      (ho : p.body.isOpaque = true)
      (hentry : Calls.CallEntry fac σ p callArgs σAO)
      (hhavoc : Calls.HavocVars fac σAO (ProcedureHeader.outputParams (P := Expression) p.header)
        σO)
      (hexit : Calls.CallExit fac σ p callArgs σO σ'),
      motive fac σ (.call n tyArgs callArgs md) σ'
        (Calls.defaultAssertEvents fac σAO (Calls.checksAtCall md p.spec.preconditions) ++
          Calls.assumeEvents fac σO p.spec.postconditions)
        (EvalCmdExtE.call_abstract_sem hπ ho hentry hhavoc hexit)) :
    motive fac σ c σ' evs h :=
  EvalCmdExtE.casesOn' (motive := motive) h cmd_sem call_sem call_abstract_sem

/-- Case analysis on `CoreBodyExecE` by its two rules, as `BigStepE.casesOn'`. -/
@[elab_as_elim, cases_eliminator]
theorem CoreBodyExecE.casesOn' {π : String → Option Procedure}
    {motive : ∀ b ρ σ' evs, CoreBodyExecE π b ρ σ' evs → Prop}
    {b : Procedure.Body} {ρ : Env Expression} {σ' : CoreStore} {evs : Trace Expression}
    (h : CoreBodyExecE π b ρ σ' evs)
    (structured : ∀ {ss opq ρ ρ' emitted}
      (h : ReflTransTrace (StepStmtE Expression (EvalCmdExtE π)) (.stmt (Stmt.block "" ss #[]) ρ)
        emitted (.terminal ρ')),
      motive (.structured ss opq) ρ ρ'.store emitted (BigStepE.structured h))
    (cfg : ∀ {g opq ρ ρ' emitted}
      (h : ReflTransTrace (StepCFGE Expression (EvalCmdExtE π)) (.atBlock g g.entry ρ) emitted
        (.terminal ρ')),
      motive (.cfg g opq) ρ (projectStore ρ.store ρ'.store) emitted (BigStepE.cfg h)) :
    motive b ρ σ' evs h :=
  BigStepE.casesOn' (motive := motive) h structured cfg

/-- Reflexive-transitive Core statement execution with chronological events. -/
abbrev CoreStepStarE
    (π : String → Option Procedure) :=
  StepStmtExtStarE π

/-- Core-level event-producing single-step relation. -/
abbrev CoreStepE
    (π : String → Option Procedure) :=
  StepStmtExtE π

/-- The configuration runs next a call that does not finish: the call, possibly inside
    sequences and blocks, is the next command to run. Its callee, the procedure of the table
    instantiated at the call's type arguments, is found and is not opaque, the entry into the
    callee succeeds in some callee store `σAO`, and no complete run of the callee body from `σAO`
    exists. The call has no step. -/
inductive CallDoesNotFinish (π : String → Option Procedure) : CoreConfig → Prop where
  /-- The call is the next statement to run. -/
  | call {n : String} {tyArgs : Option (List Expression.Ty)} {args : List (CallArg Expression)}
      {md : MetaData Expression} {ρ : Env Expression} {p : Procedure} {σAO : CoreStore} :
      Calls.typeInstantiatedCallee π n tyArgs = some p →
      p.body.isOpaque = false →
      CallEntry ρ.factory ρ.store p args σAO →
      (¬ ∃ σEnd evs, CoreBodyExecE π p.body ⟨σAO, ρ.factory⟩ σEnd evs) →
      CallDoesNotFinish π (.stmt (.cmd (.call n tyArgs args md)) ρ)
  /-- The call is the next command of the first part of a sequence. -/
  | seq {inner : CoreConfig} {ss : List Statement} :
      CallDoesNotFinish π inner → CallDoesNotFinish π (.seq inner ss)
  /-- The call is the next command inside a block. -/
  | block {label : Option String} {σp : CoreStore} {inner : CoreConfig} :
      CallDoesNotFinish π inner → CallDoesNotFinish π (.block label σp inner)

/-- The configuration runs next a call whose callee runs on without finishing: the call, possibly
    inside sequences and blocks, is the next command to run, its callee is found, the entry into
    the callee succeeds in some callee store `σAO`, the callee body is structured and not opaque,
    and every configuration reachable from the start of the callee body either steps or is again
    such a configuration. The callee is never finished, since a finished configuration neither steps nor
    runs such a call. -/
coinductive CallRunsForever (π : String → Option Procedure) : CoreConfig → Prop where
  /-- The call is the next statement to run. -/
  | call {n : String} {tyArgs : Option (List Expression.Ty)} {args : List (CallArg Expression)}
      {md : MetaData Expression} {ρ : Env Expression} {p : Procedure} {σAO : CoreStore}
      {ss : List Statement} :
      Calls.typeInstantiatedCallee π n tyArgs = some p →
      CallEntry ρ.factory ρ.store p args σAO →
      p.body = .structured ss false →
      (∀ evs cfg, CoreStepStarE π (.stmt (Stmt.block "" ss #[]) ⟨σAO, ρ.factory⟩) evs cfg →
        (∃ evs' cfg', CoreStepE π cfg evs' cfg') ∨ CallRunsForever π cfg) →
      CallRunsForever π (.stmt (.cmd (.call n tyArgs args md)) ρ)
  /-- The call is the next command of the first part of a sequence. -/
  | seq {inner : CoreConfig} {ss : List Statement} :
      CallRunsForever π inner → CallRunsForever π (.seq inner ss)
  /-- The call is the next command inside a block. -/
  | block {label : Option String} {σp : CoreStore} {inner : CoreConfig} :
      CallRunsForever π inner → CallRunsForever π (.block label σp inner)

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
