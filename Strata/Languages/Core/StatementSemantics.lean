/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
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
-- statement/expression semantics: expression-list evaluation, reading/updating
-- stores, and command/body execution.
-- ---------------------------------------------------------------------------

inductive EvalExpressions : Expression.Factory → SemanticStore Expression → List Expression.Expr → List Expression.Expr → Prop where
  | eval_none :
    EvalExpressions f σ [] []
  | eval_some :
    isDefined σ (HasFvars.getFvars e) →
    Expression.eval f σ e = .some v →
    EvalExpressions f σ es vs →
    EvalExpressions f σ (e :: es) (v :: vs)

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
@[expose] abbrev AssumeExprs (fac : Expression.Factory) (σ : CoreStore)
    (es : List Expression.Expr) : Prop :=
  Forall (fun e =>
    isDefined σ (HasFvars.getFvars e) ∧
    Expression.eval fac σ e = some HasBool.tt) es



/-- Read values from store slots. Every returned expression is a value in `f`. -/
inductive ReadValues {P : PureExpr} [HasVal P] (f : P.Factory) :
    SemanticStore P → List P.Ident → List P.Expr → Prop where
  | read_none : ReadValues f σ [] []
  | read_some :
      σ x = .some v →
      HasVal.value f v →
      ReadValues f σ xs vs →
      ReadValues f σ (x :: xs) (v :: vs)

inductive UpdateStates : SemanticStore P → List P.Ident → List P.Expr → SemanticStore P → Prop where
  | update_none :
    UpdateStates σ [] [] σ
  | update_some :
    UpdateState P σ x v σ' →
    UpdateStates σ' xs vs σ'' →
    UpdateStates σ (x :: xs) (v :: vs) σ''

inductive InitStates : SemanticStore P → List P.Ident → List P.Expr → SemanticStore P → Prop where
  | init_none :
    InitStates σ [] [] σ
  | init_some :
    InitState P σ x v σ' →
    InitStates σ' xs vs σ'' →
    InitStates σ (x :: xs) (v :: vs) σ''

inductive InitVars : SemanticStore P → List P.Ident → SemanticStore P → Prop where
  | init_none :
    InitVars σ [] σ
  | init_some :
    InitState P σ x v σ' →
    InitVars σ' xs σ'' →
    InitVars σ (x :: xs) σ''

inductive HavocVars {P : PureExpr} [HasVal P] : P.Factory → SemanticStore P → List P.Ident → SemanticStore P → Prop where
  | update_none :
    HavocVars f σ [] σ
  | update_some :
    UpdateState P σ x v σ' →
    HasVal.value f v →
    HavocVars f σ' xs σ'' →
    HavocVars f σ (x :: xs) σ''

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

/-- Extend a store with `old` snapshots: every `g ∈ snapshot` gains a binding of
    `CoreIdent.mkOld g.name` to `g`'s current value. All other lookups, `g`
    itself included, are unchanged. -/
def withOldSnapshots (snapshot : List Expression.Ident) (σ : CoreStore) : CoreStore :=
  fun id =>
    match snapshot.find? (fun g => CoreIdent.mkOld g.name == id) with
    | some g => σ g
    | none   => σ id

/-- Initialize a callee-local frame without colliding with caller names.

Input and inout formals are initialized from evaluated `inputVals`, and
output-only formals from the current values of the corresponding caller `out`
actuals. The frame also snapshots each inout formal as `old`, so postconditions
mentioning `old g` are evaluable in the callee. -/
def InitCallFrame
    (p : Procedure) (inputVals outOnlyVals : List Expression.Expr)
    (σAO : CoreStore) : Prop :=
  ∃ σA σIO,
    InitStates emptyStore (ListMap.keys p.header.inputs) inputVals σA ∧
    InitStates σA (ListMap.keys p.header.getOutputOnlyParams) outOnlyVals σIO ∧
    σAO = withOldSnapshots (ListMap.keys p.header.getInoutParams) σIO

/-- Capture non-free specification clauses as assertion events at a semantic
snapshot. Free clauses are not call-site obligations. -/
@[expose] def defaultAssertEvents
    (fac : Expression.Factory) (σ : CoreStore)
    (checks : ListMap CoreLabel Procedure.Check) : Trace Expression :=
  checks.toList.filterMap fun (label, check) =>
    if check.attr = .Default then
      some (.assert { factory := fac, store := σ, label := label, expr := check.expr, metadata := check.md })
    else
      none

/-- Capture every specification clause as an assumption event at a semantic
snapshot. Contract postconditions, including free ones, constrain the abstract
callee result. -/
@[expose] def assumeEvents
    (fac : Expression.Factory) (σ : CoreStore)
    (checks : ListMap CoreLabel Procedure.Check) : Trace Expression :=
  checks.toList.map fun (label, check) =>
    .assume { factory := fac, store := σ, label := label, expr := check.expr, metadata := check.md }

/-! ### Closure Capture for Function Declarations -/

/--
Build a list of substitutions from the store for the given identifiers.
Returns pairs of (identifier, value) for each identifier that has a value in the store.
-/
@[expose] def buildSubstitutions (σ : CoreStore) (ids : List Expression.Ident) : List (Expression.Ident × Expression.Expr) :=
  ids.filterMap (fun id =>
    match σ id with
    | some v => some (id, v)
    | none => none)

/--
Apply closure capture to a function declaration by substituting current variable
values into the function body and axioms. Variables that are function parameters
are not substituted (they are bound, not free in the closure sense).
-/
@[expose] def closureCapture
    (σ : CoreStore) (decl : PureFunc Expression) : PureFunc Expression :=
  let paramNames := decl.inputs.map (·.1)
  -- Get free variables from body (if it exists), excluding parameters
  let bodyFreeVars := match decl.body with
    | some body => (HasFvars.getFvars body).filter (· ∉ paramNames)
    | none => []
  -- Get free variables from axioms, excluding parameters
  let axiomFreeVars := decl.axioms.flatMap (fun ax =>
    (HasFvars.getFvars ax).filter (· ∉ paramNames))
  -- Combine and deduplicate
  let allFreeVars := (bodyFreeVars ++ axiomFreeVars).eraseDups
  -- Build substitutions from the store
  let substs := buildSubstitutions σ allFreeVars
  -- The replacement expressions must be closed (no dangling bvars).
  { decl with
    body := decl.body.map (fun b => HasSubstFvar.substFvars b substs)
    axioms := decl.axioms.map (fun ax => HasSubstFvar.substFvars ax substs) }

/--
Extend the factory with a new function definition by capturing the closure.
The closure capture substitutes current variable values from the store into
the function body and axioms. The returned factory handles applications of
the newly declared function by substituting arguments into the captured body.

Takes a parameter `φ` that specifies how to extend the factory with a captured
closure (without the store, since closure capture is handled here).
-/
@[expose] def EvalPureFunc (φ : Expression.Factory → PureFunc Expression → Expression.Factory) : Imperative.ExtendFactory Expression :=
  fun fac σ decl =>
    let capturedDecl := closureCapture σ decl
    φ fac capturedDecl

/-- Core-level small-step configuration. -/
@[expose] abbrev CoreConfig := Imperative.Config Expression Command

/-- Shared prologue of every call rule: evaluate the input and inout arguments,
    read the caller's `out` variables, and build the collision-free callee frame. -/
@[expose] def CallEntry (fac : Expression.Factory) (σ : CoreStore) (p : Procedure)
    (callArgs : List (CallArg Expression)) (σAO : CoreStore) : Prop :=
  ∃ inputVals outOnlyVals,
    EvalExpressions fac σ (CallArg.getInputExprs callArgs) inputVals ∧
    ReadValues fac σ (CallArg.getOutArgs callArgs) outOnlyVals ∧
    InitCallFrame p inputVals outOnlyVals σAO

/-- Shared epilogue of every call rule: read the callee's output formals in its
    final store and write them back positionally to the caller's `out`/`inout`
    variables. -/
@[expose] def CallExit (fac : Expression.Factory) (σ : CoreStore) (p : Procedure)
    (callArgs : List (CallArg Expression)) (σEnd σ' : CoreStore) : Prop :=
  ∃ outputVals,
    ReadValues fac σEnd (ListMap.keys p.header.outputs) outputVals ∧
    UpdateStates σ (CallArg.getLhs callArgs) outputVals σ'

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

/-- IsReflexive-transitive closure of `StepStmt` for the Core language,
    defined mutually with `EvalCommand` to satisfy strict positivity. -/
inductive CoreStepStar
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    CoreConfig → CoreConfig → Prop where
  | refl : CoreStepStar π φ c c
  | step :
    Imperative.StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
    CoreStepStar π φ c₂ c₃ →
    ----
    CoreStepStar π φ c₁ c₃

/-- Execution of a procedure body. Only structured bodies have an executable
    semantics; the `.cfg` arm of `Procedure.Body` has no inhabitant of
    `CoreBodyExec`.

    For structured bodies, the body is wrapped in `Stmt.block "" ss #[]` so that
    `funcDecl` extensions and other inner scoping introduced by the body do not
    leak past the procedure boundary.  This wrapping mirrors
    `Specification.AssertValidInProcedure` and the `procToVerifyStmt` pipeline. -/
inductive CoreBodyExec
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Procedure.Body → CoreStore → Expression.Factory → CoreStore → Expression.Factory → Bool → Prop where
  | structured :
    CoreStepStar π φ
      (.stmt (Stmt.block "" ss #[]) ⟨σ, fac, false⟩)
      (.terminal ρ') →
    CoreBodyExec π φ (.structured ss) σ fac ρ'.store ρ'.factory ρ'.hasFailure

inductive EvalCommand (π : String → Option Procedure) (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
  Expression.Factory → CoreStore → Command → CoreStore → Bool → Prop where
  | cmd_sem {fac σ c σ' f} :
    Imperative.EvalCmd (P := Expression) fac σ c σ' f →
    ----
    EvalCommand π φ fac σ (CmdExt.cmd c) σ' f

  /-- Arguments are matched positionally in three alignments: `inArgs`
      (`getInputExprs`) ↔ `p.header.inputs`; `lhs` (`getLhs`) ↔
      `p.header.outputs`; and `getOutArgs callArgs` ↔
      `ListMap.keys p.header.getOutputOnlyParams`. The third alignment follows
      from the second because every inout formal is passed as `.inoutArg`. -/
  | call_sem {σ n p callArgs σ' σ_final fac_final
      bodyFailed preFailed postFailed md fac σAO} :
    π n = .some p →
    CallEntry fac σ p callArgs σAO →
    EvalChecks fac σAO
      (Procedure.Spec.getDefaultCheckExprs p.spec.preconditions) preFailed →
    CoreBodyExec π φ p.body σAO fac σ_final fac_final bodyFailed →
    EvalChecks fac_final σ_final
      (Procedure.Spec.getDefaultCheckExprs p.spec.postconditions) postFailed →
    CallExit fac σ p callArgs σ_final σ' →
    ----
    EvalCommand π φ fac σ (CmdExt.call n callArgs md) σ'
      ((preFailed || bodyFailed) || postFailed)

end

/-!
### Mutual event semantics: `EvalCommandE` and `CoreBodyExecE`

The trace-producing call rule executes a Core body recursively. `CoreBodyExecE`
uses `ReflTransTrace` directly around `StepStmtE`; this nesting is strictly
positive in the mutually defined `EvalCommandE`.
-/

mutual

/-- Event-producing execution of a structured Core procedure body. -/
inductive CoreBodyExecE
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Procedure.Body → CoreStore → Expression.Factory → CoreStore →
      Expression.Factory → Trace Expression → Prop where
  | structured :
      ReflTransTrace
        (Imperative.StepStmtE Expression (EvalCommandE π φ) (EvalPureFunc φ))
        (.stmt (Stmt.block "" ss #[]) ⟨σ, fac, false⟩)
        emitted
        (.terminal ρ') →
      ----
      CoreBodyExecE π φ (.structured ss) σ fac ρ'.store ρ'.factory emitted

/-- Event-producing Core command semantics.

Base commands delegate to `EvalCmdE`. A procedure call emits its non-free
preconditions as assertions, executes its body from a frame where output-only
formals contain the copied caller values, and then emits its non-free
postconditions as assertions. Inout formals retain their incoming values for
body execution. Each contract event captures the callee store and factory in
which that clause is interpreted. -/
inductive EvalCommandE
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Expression.Factory → CoreStore → Command → CoreStore → Trace Expression → Prop where
  | cmd_sem {fac σ c σ' emitted} :
      EvalCmdE (P := Expression) fac σ c σ' emitted →
      ----
      EvalCommandE π φ fac σ (.cmd c) σ' emitted

  | call_sem {σ n p callArgs σ' σ_final
      fac_final bodyEvents md fac σAO} :
      π n = .some p →
      CallEntry fac σ p callArgs σAO →
      CoreBodyExecE π φ p.body σAO fac σ_final fac_final bodyEvents →
      CallExit fac σ p callArgs σ_final σ' →
      ----
      EvalCommandE π φ fac σ (.call n callArgs md) σ'
        (defaultAssertEvents fac σAO p.spec.preconditions ++
          bodyEvents ++
          defaultAssertEvents fac_final σ_final p.spec.postconditions)

end

/-- Reflexive-transitive Core statement execution with chronological events.

    `CoreBodyExecE.structured` must spell this closure out rather than use this
    abbreviation, because the abbreviation is declared after its own mutual
    block. -/
@[expose] abbrev CoreStepStarE
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :=
  ReflTransTrace
    (Imperative.StepStmtE Expression (EvalCommandE π φ) (EvalPureFunc φ))

/-- Core-level event-producing single-step relation. -/
@[expose] abbrev CoreStepE
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :=
  Imperative.StepStmtE Expression (EvalCommandE π φ) (EvalPureFunc φ)

/-- Core-level single-step relation. -/
@[expose] abbrev CoreStep
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :=
  Imperative.StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)

@[expose] abbrev EvalStatement (π : String → Option Procedure) (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Imperative.Env Expression → Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtSmall Expression (EvalCommand π φ) (EvalPureFunc φ)

@[expose] abbrev EvalStatements (π : String → Option Procedure) (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Imperative.Env Expression → List Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtsSmall Expression (EvalCommand π φ) (EvalPureFunc φ)


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
  | .block _ _ _ inner, aid => coreIsAtAssert inner aid
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

/-- Event-producing contract abstraction for Core commands.

Base commands retain `EvalCmdE` behavior. A procedure call emits non-free
preconditions as assertions at the initialized callee frame, havocs the output
formals, and then emits every postcondition as an assumption at the post-havoc
snapshot. No procedure body is executed. -/
inductive EvalCommandContractE (π : String → Option Procedure) :
    Expression.Factory → CoreStore → Command → CoreStore → Trace Expression → Prop where
  | cmd_sem {fac σ c σ' emitted} :
      EvalCmdE (P := Expression) fac σ c σ' emitted →
      ----
      EvalCommandContractE π fac σ (.cmd c) σ' emitted

  | call_sem {σ σO n p callArgs σ' md fac σAO} :
      π n = .some p →
      CallEntry fac σ p callArgs σAO →
      HavocVars fac σAO (ListMap.keys p.header.outputs) σO →
      CallExit fac σ p callArgs σO σ' →
      ----
      EvalCommandContractE π fac σ (.call n callArgs md) σ'
        (defaultAssertEvents fac σAO p.spec.preconditions ++
          assumeEvents fac σO p.spec.postconditions)

@[expose] abbrev EvalStatementContract (π : String → Option Procedure) (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Imperative.Env Expression → Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtSmall Expression (EvalCommandContract π) (EvalPureFunc φ)

@[expose] abbrev EvalStatementsContract (π : String → Option Procedure) (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Imperative.Env Expression → List Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtsSmall Expression (EvalCommandContract π) (EvalPureFunc φ)


end Core

end -- public section
