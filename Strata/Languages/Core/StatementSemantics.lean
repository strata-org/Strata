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
import Std.Tactic.BVDecide.Normalize.Prop

---------------------------------------------------------------------

public section

namespace Core

/-- expressions that can't be reduced when evaluating -/
inductive Value : Core.Expression.Expr → Prop where
  | const :  Value (.const () _)
  | bvar  :  Value (.bvar () _)
  | op    :  Value (.op () _ _)
  | abs   :  Value (.abs () _ _ _)

open Imperative

instance : HasVal Core.Expression where value := Value

instance : HasFvar Core.Expression where
  mkFvar := (.fvar () · none)
  getFvar
  | .fvar _ v _ => some v
  | _ => none

instance : HasSubstFvar Core.Expression where
  substFvar := Lambda.LExpr.substFvar
  substFvars := Lambda.LExpr.substFvars

instance : HasIntOrder Core.Expression where
  eq    e1 e2 := .eq () e1 e2
  lt    e1 e2 := .app () (.app () Core.intLtOp e1) e2
  zero        := .intConst () 0
  intTy       := .forAll [] (.tcons "int" [])

instance : HasIdent Core.Expression where
  ident s := ⟨s, ()⟩

@[expose, match_pattern]
def Core.true : Core.Expression.Expr := .boolConst () Bool.true
@[expose, match_pattern]
def Core.false : Core.Expression.Expr := .boolConst () Bool.false

instance : HasBool Core.Expression where
  tt := Core.true
  ff := Core.false
  tt_is_not_ff := by unfold Core.true Core.false; unfold Lambda.LExpr.boolConst; simp
  boolTy := .forAll [] (.tcons "bool" [])

instance : HasNot Core.Expression where
  not
  | Core.true => Core.false
  | Core.false => Core.true
  | e => Lambda.LExpr.app () (Lambda.boolNotFunc (T:=CoreLParams)).opExpr e

@[expose] abbrev CoreEval := SemanticEval Expression
@[expose] abbrev CoreStore := SemanticStore Expression

/-- If a compound expression is defined, its subexpressions are defined. -/
structure WellFormedCoreEvalDefinedness (δ : CoreEval) : Prop where
  absdef:   (∀ σ m name ty e, (δ σ (.abs m name ty e)).isSome → (δ σ e).isSome)
  appdef:   (∀ σ m e₁ e₂, (δ σ (.app m e₁ e₂)).isSome → (δ σ e₁).isSome ∧ (δ σ e₂).isSome)
  eqdef:    (∀ σ m e₁ e₂, (δ σ (.eq m e₁ e₂)).isSome → (δ σ e₁).isSome ∧ (δ σ e₂).isSome)
  quantdef: (∀ σ m k name ty tr e, (δ σ (.quant m k name ty tr e)).isSome → (δ σ tr).isSome ∧ (δ σ e).isSome)
  itedef:   (∀ σ m c t e, (δ σ (.ite m c t e)).isSome → (δ σ c).isSome ∧ (δ σ t).isSome ∧ (δ σ e).isSome)

structure WellFormedCoreEvalCong (δ : CoreEval): Prop where
    abscongr: (∀ σ σ' e₁ e₁' ,
      δ σ e₁ = δ σ' e₁' →
      (∀ m name ty, δ σ (.abs m name ty e₁) = δ σ' (.abs m name ty e₁')))
    appcongr: (∀ σ σ' m e₁ e₁' e₂ e₂',
      δ σ e₁ = δ σ' e₁' →
      δ σ e₂ = δ σ' e₂' →
      (δ σ (.app m e₁ e₂) = δ σ' (.app m e₁' e₂')))
    eqcongr: (∀ σ σ' m e₁ e₁' e₂ e₂',
      δ σ e₁ = δ σ' e₁' →
      δ σ e₂ = δ σ' e₂' →
      (δ σ (.eq m e₁ e₂) = δ σ' (.eq m e₁' e₂')))
    quantcongr: (∀ σ σ' m k name ty e₁ e₁' e₂ e₂',
      δ σ e₁ = δ σ' e₁' →
      δ σ e₂ = δ σ' e₂' →
      (δ σ (.quant m k name ty e₁ e₂) = δ σ' (.quant m k name ty e₁' e₂')))
    itecongr: (∀ σ σ' m e₁ e₁' e₂ e₂' e₃ e₃',
      δ σ e₁ = δ σ' e₁' →
      δ σ e₂ = δ σ' e₂' →
      δ σ e₃ = δ σ' e₃' →
      (δ σ (.ite m e₃ e₁ e₂) = δ σ' (.ite m e₃' e₁' e₂')))
    /-- Definedness-propagation properties for compound expressions. -/
    definedness : WellFormedCoreEvalDefinedness δ

inductive EvalExpressions {P} [HasVarsPure P P.Expr] : SemanticEval P → SemanticStore P → List P.Expr → List P.Expr → Prop where
  | eval_none :
    EvalExpressions δ σ [] []
  | eval_some :
    isDefined σ (HasVarsPure.getVars e) →
    δ σ e = .some v →
    EvalExpressions δ σ es vs →
    EvalExpressions δ σ (e :: es) (v :: vs)

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

inductive HavocVars : SemanticStore P → List P.Ident → SemanticStore P → Prop where
  | update_none :
    HavocVars σ [] σ
  | update_some :
    UpdateState P σ x v σ' →
    HavocVars σ' xs σ'' →
    HavocVars σ (x :: xs) σ''

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
def WellFormedCoreEvalTwoState (δ : CoreEval) (σ₀ σ : CoreStore) : Prop :=
      (∃ vs vs' σ₁, HavocVars σ₀ vs σ₁ ∧ InitVars σ₁ vs' σ) ∧
      (∀ vs vs' σ₀ σ₁ σ,
        (HavocVars σ₀ vs σ₁ ∧ InitVars σ₁ vs' σ) →
        ∀ v,
          -- "old g" in the post-state holds the pre-state value of g
          (v ∈ vs →
            δ σ (.fvar () (CoreIdent.mkOld v.name) none) = σ₀ v) ∧
          -- if the variable is not modified, "old g" is the same as g
          (¬ v ∈ vs →
            δ σ (.fvar () (CoreIdent.mkOld v.name) none) = σ v))

/-! ### Closure Capture for Function Declarations -/

/--
Build a list of substitutions from the store for the given identifiers.
Returns pairs of (identifier, value) for each identifier that has a value in the store.
-/
def buildSubstitutions (σ : CoreStore) (ids : List Expression.Ident) : List (Expression.Ident × Expression.Expr) :=
  ids.filterMap (fun id =>
    match σ id with
    | some v => some (id, v)
    | none => none)

/--
Apply closure capture to a function declaration by substituting current variable
values into the function body and axioms. Variables that are function parameters
are not substituted (they are bound, not free in the closure sense).
-/
def closureCapture
    (σ : CoreStore) (decl : PureFunc Expression) : PureFunc Expression :=
  let paramNames := decl.inputs.map (·.1)
  -- Get free variables from body (if it exists), excluding parameters
  let bodyFreeVars := match decl.body with
    | some body => (HasVarsPure.getVars body).filter (· ∉ paramNames)
    | none => []
  -- Get free variables from axioms, excluding parameters
  let axiomFreeVars := decl.axioms.flatMap (fun ax =>
    (HasVarsPure.getVars ax).filter (· ∉ paramNames))
  -- Combine and deduplicate
  let allFreeVars := (bodyFreeVars ++ axiomFreeVars).eraseDups
  -- Build substitutions from the store
  let substs := buildSubstitutions σ allFreeVars
  -- The replacement expressions must be closed (no dangling bvars).
  { decl with
    body := decl.body.map (fun b => HasSubstFvar.substFvars b substs)
    axioms := decl.axioms.map (fun ax => HasSubstFvar.substFvars ax substs) }

/--
Extend the evaluator with a new function definition by capturing the closure.
The closure capture substitutes current variable values from the store into
the function body and axioms. The returned evaluator handles applications of
the newly declared function by substituting arguments into the captured body.

Takes a parameter `φ` that specifies how to extend the evaluator with a captured
closure (without the store, since closure capture is handled here).
-/
def EvalPureFunc (φ : CoreEval → PureFunc Expression → CoreEval) : Imperative.ExtendEval Expression :=
  fun δ σ decl =>
    let capturedDecl := closureCapture σ decl
    φ δ capturedDecl

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
    (φ : CoreEval → PureFunc Expression → CoreEval) :
    CoreConfig → CoreConfig → Prop where
  | refl : CoreStepStar π φ c c
  | step :
    Imperative.StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
    CoreStepStar π φ c₂ c₃ →
    ----
    CoreStepStar π φ c₁ c₃

/-- Execution of a procedure body. Only structured bodies have an executable
    semantics; the `.cfg` arm of `Procedure.Body` has no inhabitant of
    `CoreBodyExec`. -/
inductive CoreBodyExec
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :
    Procedure.Body → CoreStore → CoreEval → CoreStore → CoreEval → Bool → Prop where
  | structured :
    CoreStepStar π φ
      (.stmts ss ⟨σ, δ, false⟩)
      (.terminal ρ') →
    CoreBodyExec π φ (.structured ss) σ δ ρ'.store ρ'.eval ρ'.hasFailure

inductive EvalCommand (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) : CoreEval →
  CoreStore → Command → CoreStore → Bool → Prop where
  | cmd_sem {δ σ c σ' f} :
    Imperative.EvalCmd (P := Expression) δ σ c σ' f →
    ----
    EvalCommand π φ δ σ (CmdExt.cmd c) σ' f

  /-- Arguments are matched positionally: `inArgs` (from `getInputExprs`)
      aligns with `p.header.inputs`, and `lhs` (from `getLhs`) aligns
      with `p.header.outputs`. -/
  | call_sem {δ σ₀ σ inArgs vals oVals σA σAO n p modvals callArgs σ' σ_final δ_final failed md} :
    π n = .some p →
    -- inArg exprs + fvar refs for inoutArg ids
    CallArg.getInputExprs callArgs = inArgs →
    -- caller-side output variables (inout + out);
    -- used by ReadValues and UpdateStates below
    CallArg.getLhs callArgs = lhs →
    EvalExpressions (P:=Expression) δ σ inArgs vals →
    -- pre-call values of lhs, needed to init callee output params
    ReadValues σ lhs oVals →
    WellFormedSemanticEvalVal δ →
    WellFormedSemanticEvalVar δ →
    WellFormedSemanticEvalBool δ →
    WellFormedCoreEvalTwoState δ σ₀ σ →
    isDefinedOver (HasVarsTrans.allVarsTrans π) σ (Statement.call n callArgs md) →
    -- positional: vals[i] initializes p.header.inputs[i]
    InitStates σ (ListMap.keys (p.header.inputs)) vals σA →
    -- positional: oVals[i] initializes p.header.outputs[i]
    InitStates σA (ListMap.keys (p.header.outputs)) oVals σAO →
    (∀ pre, (Procedure.Spec.getCheckExprs p.spec.preconditions).contains pre →
      isDefinedOver (HasVarsPure.getVars) σAO pre ∧
      δ σAO pre = .some HasBool.tt) →
    CoreBodyExec π φ p.body σAO δ σ_final δ_final failed →
    (∀ post, (Procedure.Spec.getCheckExprs p.spec.postconditions).contains post →
      isDefinedOver (HasVarsPure.getVars) σAO post ∧
      δ_final σ_final post = .some HasBool.tt) →
    ReadValues σ_final (ListMap.keys (p.header.outputs)) modvals →
    -- positional: modvals[i] written back to lhs[i]
    UpdateStates σ lhs modvals σ' →
    ----
    EvalCommand π φ δ σ (CmdExt.call n callArgs md) σ' false

end

/-- Core-level single-step relation. -/
@[expose] abbrev CoreStep
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :=
  Imperative.StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)

@[expose] abbrev EvalStatement (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) :
    Imperative.Env Expression → Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtSmall Expression (EvalCommand π φ) (EvalPureFunc φ)

@[expose] abbrev EvalStatements (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) :
    Imperative.Env Expression → List Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtsSmall Expression (EvalCommand π φ) (EvalPureFunc φ)


/-! ## Old-variable environment augmentation -/

/-- Augment an environment with old-variable bindings for the modifies clause.

    For each `g ∈ modifies`, the store is extended so that
    `(withOldBindings modifies ρ).store (CoreIdent.mkOld g.name) = ρ.store g`.
    All other store lookups (including `g` itself) are unchanged.
    The evaluator and `hasFailure` flag are preserved. -/
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
  | .stmt (.loop _ _ inv _ _) _, aid => (aid.label, aid.expr) ∈ inv
  | .stmts ((.loop _ _ inv _ _) :: _) _, aid => (aid.label, aid.expr) ∈ inv
  | .block _ _ inner, aid => coreIsAtAssert inner aid
  | .seq inner _, aid => coreIsAtAssert inner aid
  | _, _ => False

/-! ## Well-formed evaluator extension -/

/-- A well-formed evaluator extension preserves `WellFormedSemanticEvalBool`
    through `funcDecl` steps.  This is the only step that modifies the
    evaluator; all other small-step rules leave it unchanged.

    Concrete instantiations of `φ` (e.g., lookup-table extensions) should
    prove this once at the instantiation site. -/
structure WFEvalExtension (φ : CoreEval → Imperative.PureFunc Expression → CoreEval) : Prop where
  preserves_wfBool : ∀ δ σ decl, Imperative.WellFormedSemanticEvalBool δ →
    Imperative.WellFormedSemanticEvalBool (EvalPureFunc φ δ σ decl)
  preserves_wfVar : ∀ δ σ decl, Imperative.WellFormedSemanticEvalVar δ →
    Imperative.WellFormedSemanticEvalVar (EvalPureFunc φ δ σ decl)
  preserves_wfCong : ∀ δ σ decl, WellFormedCoreEvalCong δ →
    WellFormedCoreEvalCong (EvalPureFunc φ δ σ decl)
  preserves_wfExprCongr : ∀ δ σ decl,
    @Imperative.WellFormedSemanticEvalExprCongr Expression _ δ →
    @Imperative.WellFormedSemanticEvalExprCongr Expression _ (EvalPureFunc φ δ σ decl)

---------------------------------------------------------------------

inductive EvalCommandContract : (String → Option Procedure)  → CoreEval →
  CoreStore → Command → CoreStore → Bool → Prop where
  | cmd_sem {π δ σ c σ' f} :
    Imperative.EvalCmd (P := Expression) δ σ c σ' f →
    ----
    EvalCommandContract π δ σ (CmdExt.cmd c) σ' f

  /-- Contract-based semantics: like `EvalCommand.call_sem` but replaces
      body execution with havoc + postcondition check.
      Same positional matching as `EvalCommand.call_sem`. -/
  | call_sem {π δ σ σ₀ inArgs oVals vals σA σAO σO n p modvals callArgs σ' md} :
    π n = .some p →
    CallArg.getInputExprs callArgs = inArgs →
    CallArg.getLhs callArgs = lhs →
    EvalExpressions (P:=Core.Expression) δ σ inArgs vals →
    ReadValues σ lhs oVals →
    WellFormedSemanticEvalVal δ →
    WellFormedSemanticEvalVar δ →
    WellFormedSemanticEvalBool δ →
    WellFormedCoreEvalTwoState δ σ₀ σ →
    isDefinedOver (HasVarsTrans.allVarsTrans π) σ (Statement.call n callArgs md) →
    -- positional: vals[i] initializes p.header.inputs[i]
    InitStates σ (ListMap.keys (p.header.inputs)) vals σA →
    -- positional: oVals[i] initializes p.header.outputs[i]
    InitStates σA (ListMap.keys (p.header.outputs)) oVals σAO →
    (∀ pre, (Procedure.Spec.getCheckExprs p.spec.preconditions).contains pre →
      isDefinedOver (HasVarsPure.getVars) σAO pre ∧
      δ σAO pre = .some HasBool.tt) →
    HavocVars σAO (ListMap.keys p.header.outputs) σO →
    (∀ post, (Procedure.Spec.getCheckExprs p.spec.postconditions).contains post →
      isDefinedOver (HasVarsPure.getVars) σAO post ∧
      δ σO post = .some HasBool.tt) →
    ReadValues σO (ListMap.keys (p.header.outputs)) modvals →
    -- positional: modvals[i] written back to lhs[i]
    UpdateStates σ lhs modvals σ' →
    ----
    EvalCommandContract π δ σ (.call n callArgs md) σ' false

@[expose] abbrev EvalStatementContract (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) :
    Imperative.Env Expression → Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtSmall Expression (EvalCommandContract π) (EvalPureFunc φ)

@[expose] abbrev EvalStatementsContract (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval) :
    Imperative.Env Expression → List Statement → Imperative.Env Expression → Prop :=
  Imperative.EvalStmtsSmall Expression (EvalCommandContract π) (EvalPureFunc φ)

end Core

end -- public section
