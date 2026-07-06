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



inductive ReadValues : SemanticStore P → List P.Ident → List P.Expr → Prop where
  | read_none :
    ReadValues _ [] []
  | read_some :
    σ x = .some v →
    ReadValues σ xs vs →
    ReadValues σ (x :: xs) (v :: vs)

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

/-- The evaluator handles old expressions correctly
-- It should specify the exact expression form that would map to the old store
-- This can be used to implement more general two-state functions, as in Dafny
-- https://dafny.org/latest/DafnyRef/DafnyRef#sec-two-state
-- where this condition will be asserted at procedures utilizing those two-state functions
-/
def WellFormedCoreEvalTwoState (f : Expression.Factory) (σ₀ σ : CoreStore) : Prop :=
      (∃ vs vs' σ₁, HavocVars f σ₀ vs σ₁ ∧ InitVars σ₁ vs' σ) ∧
      (∀ vs vs' σ₀ σ₁ σ,
        (HavocVars f σ₀ vs σ₁ ∧ InitVars σ₁ vs' σ) →
        ∀ v,
          -- "old g" in the post-state holds the pre-state value of g
          (v ∈ vs →
            Expression.eval f σ (.fvar () (CoreIdent.mkOld v.name) none) = σ₀ v) ∧
          -- if the variable is not modified, "old g" is the same as g
          (¬ v ∈ vs →
            Expression.eval f σ (.fvar () (CoreIdent.mkOld v.name) none) = σ v))

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

  /-- Arguments are matched positionally: `inArgs` (from `getInputExprs`)
      aligns with `p.header.inputs`, and `lhs` (from `getLhs`) aligns
      with `p.header.outputs`. -/
  | call_sem {σ₀ σ inArgs vals oVals σA σAO n p modvals callArgs σ' σ_final fac_final failed md fac} :
    π n = .some p →
    -- inArg exprs + fvar refs for inoutArg ids
    CallArg.getInputExprs callArgs = inArgs →
    -- caller-side output variables (inout + out);
    -- used by ReadValues and UpdateStates below
    CallArg.getLhs callArgs = lhs →
    EvalExpressions fac σ inArgs vals →
    -- pre-call values of lhs, needed to init callee output params
    ReadValues σ lhs oVals →
    -- caller store holds only values (true of all reachable stores); feeds the
    -- `WellFormedSemanticEvalVal`/`Var` conditions below
    WellFormedStore σ fac →
    WellFormedSemanticEvalVal (P := Expression) fac →
    WellFormedSemanticEvalVar (P := Expression) fac →
    WellFormedSemanticEvalBool (P := Expression) fac →
    WellFormedCoreEvalTwoState fac σ₀ σ →
    isDefinedOver (HasVarsTrans.allVarsTrans π) σ (Statement.call n callArgs md) →
    -- positional: vals[i] initializes p.header.inputs[i]
    InitStates σ (ListMap.keys (p.header.inputs)) vals σA →
    -- positional: oVals[i] initializes p.header.outputs[i]
    InitStates σA (ListMap.keys (p.header.outputs)) oVals σAO →
    (∀ pre, (Procedure.Spec.getCheckExprs p.spec.preconditions).contains pre →
      isDefinedOver (HasFvars.getFvars) σAO pre ∧
      Expression.eval fac σAO pre = .some HasBool.tt) →
    CoreBodyExec π φ p.body σAO fac σ_final fac_final failed →
    (∀ post, (Procedure.Spec.getCheckExprs p.spec.postconditions).contains post →
      isDefinedOver (HasFvars.getFvars) σAO post ∧
      Expression.eval fac_final σ_final post = .some HasBool.tt) →
    ReadValues σ_final (ListMap.keys (p.header.outputs)) modvals →
    -- positional: modvals[i] written back to lhs[i]
    UpdateStates σ lhs modvals σ' →
    ----
    EvalCommand π φ fac σ (CmdExt.call n callArgs md) σ' false

end

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

/-- Augment an environment with old-variable bindings for the modifies clause.

    For each `g ∈ modifies`, the store is extended so that
    `(withOldBindings modifies ρ).store (CoreIdent.mkOld g.name) = ρ.store g`.
    All other store lookups (including `g` itself) are unchanged.
    The `hasFailure` flag is preserved. -/
def withOldBindings
    (modifies : List Expression.Ident) (ρ : Env Expression) : Env Expression :=
  { ρ with store := fun id =>
      match modifies.find? (fun g => CoreIdent.mkOld g.name == id) with
      | some g => ρ.store g
      | none   => ρ.store id }

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
  | .stmt (.loop _ _ inv _ _) _, aid =>
    (aid.label, aid.expr) ∈ inv
  | .stmts ((.loop _ _ inv _ _) :: _) _, aid =>
    (aid.label, aid.expr) ∈ inv
  | .block _ _ _ inner, aid => coreIsAtAssert inner aid
  | .seq inner _, aid => coreIsAtAssert inner aid
  | _, _ => False

/-! ## Well-formed factory extension -/

/-- A well-formed factory extension preserves well-formedness properties
    through `funcDecl` steps (which extend the factory). -/
structure WFFactoryExtension (φ : Expression.Factory → Imperative.PureFunc Expression → Expression.Factory) : Prop where
  preserves_wfBool : ∀ f σ decl, Imperative.WellFormedSemanticEvalBool (P := Expression) f →
    Imperative.WellFormedSemanticEvalBool (P := Expression) (EvalPureFunc φ f σ decl)
  preserves_wfVar : ∀ f σ decl, Imperative.WellFormedSemanticEvalVar (P := Expression) f →
    Imperative.WellFormedSemanticEvalVar (P := Expression) (EvalPureFunc φ f σ decl)
  preserves_wfExprCongr : ∀ f σ decl,
    @Imperative.WellFormedSemanticEvalExprCongr Expression _ _ f →
    @Imperative.WellFormedSemanticEvalExprCongr Expression _ _ (EvalPureFunc φ f σ decl)

---------------------------------------------------------------------

inductive EvalCommandContract : (String → Option Procedure)  →
  Expression.Factory → CoreStore → Command → CoreStore → Bool → Prop where
  | cmd_sem {π fac σ c σ' f} :
    Imperative.EvalCmd (P := Expression) fac σ c σ' f →
    ----
    EvalCommandContract π fac σ (CmdExt.cmd c) σ' f

  /-- Contract-based semantics: like `EvalCommand.call_sem` but replaces
      body execution with havoc + postcondition check.
      Same positional matching as `EvalCommand.call_sem`. -/
  | call_sem {π σ σ₀ inArgs oVals vals σA σAO σO n p modvals callArgs σ' md fac} :
    π n = .some p →
    CallArg.getInputExprs callArgs = inArgs →
    CallArg.getLhs callArgs = lhs →
    EvalExpressions fac σ inArgs vals →
    ReadValues σ lhs oVals →
    -- caller store holds only values (see `EvalCommand.call_sem`)
    WellFormedStore σ fac →
    WellFormedSemanticEvalVal (P := Expression) fac →
    WellFormedSemanticEvalVar (P := Expression) fac →
    WellFormedSemanticEvalBool (P := Expression) fac →
    WellFormedCoreEvalTwoState fac σ₀ σ →
    isDefinedOver (HasVarsTrans.allVarsTrans π) σ (Statement.call n callArgs md) →
    -- positional: vals[i] initializes p.header.inputs[i]
    InitStates σ (ListMap.keys (p.header.inputs)) vals σA →
    -- positional: oVals[i] initializes p.header.outputs[i]
    InitStates σA (ListMap.keys (p.header.outputs)) oVals σAO →
    (∀ pre, (Procedure.Spec.getCheckExprs p.spec.preconditions).contains pre →
      isDefinedOver (HasFvars.getFvars) σAO pre ∧
      Expression.eval fac σAO pre = .some HasBool.tt) →
    HavocVars fac σAO (ListMap.keys p.header.outputs) σO →
    (∀ post, (Procedure.Spec.getCheckExprs p.spec.postconditions).contains post →
      isDefinedOver (HasFvars.getFvars) σAO post ∧
      Expression.eval fac σO post = .some HasBool.tt) →
    ReadValues σO (ListMap.keys (p.header.outputs)) modvals →
    -- positional: modvals[i] written back to lhs[i]
    UpdateStates σ lhs modvals σ' →
    ----
    EvalCommandContract π fac σ (.call n callArgs md) σ' false

@[expose] abbrev EvalStatementContract (π : String → Option Procedure) (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Imperative.Env Expression → Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtSmall Expression (EvalCommandContract π) (EvalPureFunc φ)

@[expose] abbrev EvalStatementsContract (π : String → Option Procedure) (φ : Expression.Factory → PureFunc Expression → Expression.Factory) :
    Imperative.Env Expression → List Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtsSmall Expression (EvalCommandContract π) (EvalPureFunc φ)


end Core

end -- public section
