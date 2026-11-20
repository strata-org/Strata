/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Interpreter
public import Strata.Languages.Core.InterpreterEval
public import Strata.Languages.Core.Env
public import Strata.Languages.Core.Identifiers
public import Strata.Languages.Core.SMTEncoder
public import Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.LExprEval
public import Strata.Languages.Core.Counterexample.ModelAnonymous

/-! # Level-(c) counterexamples: solver models as Core expressions

Counterexamples live at three *levels*: level (a) is a run of the program, level (b) is a
valuation of a proof obligation's variables, and level (c) is the SMT solver's model.  This
module holds level (c) once the solver's terms are converted to Core expressions: the shapes
of a lifted model (`LExprModel`, `FlaggedLExprModel`), the annotation and type gating that
prepare a lifted model for the VC check (`annotateFlaggedModel`, `gateModelTypes`,
`checkedModel`), and the values a model gives the uninterpreted constants of the factory.

A Core `const c : T;` declared without a value is an *uninterpreted constant*: a
monomorphic nullary operator of the factory with no body, no concrete evaluator and no
axioms (`isUninterpretedConst`). The solver chooses its value together with the values of
the variables. A *constant interpretation* (`ConstInterp`) assigns values to such
constants; `SMT.Result.splitConsts` takes the interpretation of the constants
`interpretableConsts` offers out of a model.  Interpreting a constant is admissible only if
every constraint on it is evaluated by the check that consumes the interpretation. That check
evaluates the obligation's assumptions and goal. It does not see the axioms of the factory's
functions (`Func.axioms`), nor the axioms removed from the obligation as irrelevant to it,
which the solver did not see either. `interpretableConsts` therefore offers a constant only
when no factory axiom and no removed axiom mentions it.

Key definitions: `LExprModel`, `FlaggedLExprModel`, `obligationReadVars`,
`annotateConstrValue`, `gateModelTypes`, `checkedModel`, `ConstInterp`,
`interpretableConsts`, `SMT.Result.splitConsts`.
-/

namespace Core

open _root_.Lambda Imperative

public section

/-- Unfiltered model used for replay reconstruction. -/
abbrev LExprModel := List (CoreIdent × Lambda.LExpr CoreLParams.mono)

/-- Lifted model before the per-binding value flag is checked. -/
abbrev FlaggedLExprModel :=
  List (CoreIdent × Lambda.LExpr CoreLParams.mono × Bool)

/-- Every type-annotated free variable the obligation reads (`ProofObligation.getVars`): the
    goal's, plus each path-condition entry's (assumption bodies, `.det` varDecl right-hand
    sides, `distinct` operands), each (name, type) pair once, in order of first read.
    Declared varDecl *targets* are excluded — those are computed by `extendWithVarDecls'`,
    not read from the valuation. -/
def obligationReadVars (obligation : ProofObligation Expression) :
    List (Expression.Ident × Lambda.LMonoTy) :=
  (ProofObligation.getVars obligation).filterMap fun (name, ty?) => ty?.map (name, ·)

/-- Give every datatype-constructor operator of a lifted model value the type
    annotation its constructor has at the expected type `expected`.  A model lifts a
    constructor application with an unannotated head (`smtTermToLExpr`), so its
    `typeOf` is unknown and replay rejects it as ill-typed; the annotation is read
    off the constructor's signature in `F`, instantiating a polymorphic datatype's
    type parameters by unifying the constructor's output with `expected`.  A value
    that is not a constructor application of `F`, or whose constructor's output does
    not unify with `expected`, is returned unchanged. -/
partial def annotateConstrValue (F : @Lambda.Factory CoreLParams)
    (expected : Lambda.LMonoTy) (e : Expression.Expr) : Expression.Expr :=
  match e with
  | .fvar m n _ =>
    -- A solver's element of an uninterpreted sort becomes an anonymous value of that
    -- sort, named by the element and the sort (`Counterexample.ModelAnonymous`).
    if isSolverElementName n.name && isUninterpretedSort F expected &&
        Lambda.LMonoTy.freeVars expected == [] then
      .op m ⟨anonName n.name expected, n.metadata⟩ (some expected)
    else e
  | _ =>
  match Lambda.Factory.callOfLFunc F e false with
  | some (.op m name _, args, f) =>
    if !f.isConstr then e else
    let generic := Lambda.LMonoTy.mkArrow' f.output f.inputs.values
    let subst? : Option Lambda.Subst :=
      if f.typeArgs.isEmpty then some Lambda.Subst.empty
      else match Lambda.Constraints.unify [(expected, f.output)] Lambda.SubstInfo.empty with
        | .ok info => some info.subst
        | .error _ => none
    match subst? with
    | none => e
    | some S =>
      let inst (ty : Lambda.LMonoTy) : Lambda.LMonoTy := Lambda.LMonoTy.subst S ty
      let argTys := f.inputs.values.map inst
      let args' := (args.zip argTys).map fun (a, ty) => annotateConstrValue F ty a
      args'.foldl (fun acc a => .app m acc a) (.op m name (some (inst generic)))
  | _ => e

/-- `annotateConstrValue` applied to each binding of a lifted model whose variable
    the obligation reads at a known monomorphic type (`obligationReadVars`). -/
def annotateFlaggedModel (F : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression) (model : FlaggedLExprModel) :
    FlaggedLExprModel :=
  let tys := obligationReadVars obligation
  model.map fun (name, value, liftable) =>
    match tys.find? (fun entry => entry.1 == name) with
    | some (_, ty) =>
      let value' := annotateConstrValue F ty value
      -- A value holding an anonymous value is liftable when it is canonical once its
      -- anonymous values have their constructors (`extendAnon`).
      let liftable := liftable ||
        (!(anonElems value').isEmpty &&
          Lambda.LExpr.isValue (extendAnon F [value']) value')
      (name, value', liftable)
    | none => (name, value, liftable)

/-- A lifted model with the `value?` flag cleared on every binding whose value does not
    have each type the obligation reads its variable at (`obligationReadVars`, checked by
    `valueHasMonoType`). The VC check reads a flagged binding without checking its type,
    so only a value of the variable's type may keep the flag. Constructor values must
    carry their annotations (`annotateFlaggedModel`) to type-check. -/
def gateModelTypes (F : @Lambda.Factory CoreLParams) (obligation : ProofObligation Expression)
    (model : FlaggedLExprModel) : FlaggedLExprModel :=
  let tys := obligationReadVars obligation
  model.map fun (name, value, liftable) =>
    (name, value, liftable && tys.all fun (n, ty) => n != name || valueHasMonoType F value ty)

/-- A lifted model as the VC check reads it: annotated (`annotateFlaggedModel`), then
    type-gated (`gateModelTypes`). -/
def checkedModel (F : @Lambda.Factory CoreLParams) (obligation : ProofObligation Expression)
    (model : FlaggedLExprModel) : FlaggedLExprModel :=
  gateModelTypes F obligation (annotateFlaggedModel F obligation model)

/-- Values for uninterpreted constants, by constant name. -/
abbrev ConstInterp := List (String × LExpr CoreLParams.mono)

/-- Whether `f` is an uninterpreted constant: a monomorphic nullary operator that is
    not a constructor and has no body, no concrete evaluator and no axioms. -/
@[expose] def isUninterpretedConst (f : LFunc CoreLParams) : Bool :=
  f.inputs.isEmpty && f.typeArgs.isEmpty && !f.isConstr && f.body.isNone &&
    f.concreteEval.isNone && f.axioms.isEmpty

/-- The names of the operators the expressions of a path-condition entry mention. -/
def PathConditionEntry.opNames (entry : PathConditionEntry Expression) : List String :=
  (entryExprs entry).flatMap fun e => e.getOps.map (·.name)

/-- The uninterpreted constants of `F` (`isUninterpretedConst`) that `obligation`
    mentions and that no axiom of a function of `F` and no entry of `removed` mentions,
    with their types. `removed` are the path-condition entries removed from the
    obligation as irrelevant to it. -/
def interpretableConsts (F : @Lambda.Factory CoreLParams) (obligation : ProofObligation Expression)
    (removed : List (PathConditionEntry Expression)) : List (CoreIdent × LMonoTy) :=
  let mentioned := (obligation.obligation.getOps.map (·.name) ++
    obligation.assumptions.flatten.flatMap PathConditionEntry.opNames).eraseDups
  let candidates := mentioned.filterMap fun n =>
    (F[n]?).filter isUninterpretedConst
  if candidates.isEmpty then [] else
  let excluded := F.toArray.toList.flatMap (fun g => g.axioms.flatMap fun a =>
    a.getOps.map (·.name)) ++ removed.flatMap PathConditionEntry.opNames
  candidates.filterMap fun f =>
    if excluded.contains f.name.name then none else some (f.name, f.output)

/-- The model of `r` without the bindings of the constants `consts`, and the
    interpretation of those constants it gives: each constant whose term is a value
    (`smtTermIsValue`) whose lift has the constant's type, after annotation with the
    constructor types of `F` (`annotateConstrValue`). A result without a model is
    returned unchanged with the empty interpretation. -/
def _root_.Imperative.SMT.Result.splitConsts (r : Imperative.SMT.Result Expression.Ident)
    (consts : List (CoreIdent × LMonoTy)) (F : @Lambda.Factory CoreLParams)
    (constructorNames : Std.HashSet String) :
    Imperative.SMT.Result Expression.Ident × ConstInterp :=
  if consts.isEmpty then (r, []) else
  let split (m : Imperative.SMT.Model Expression.Ident) :
      Imperative.SMT.Model Expression.Ident × ConstInterp :=
    (m.toList.filter fun (k, _) => !consts.any (·.1 == k),
     consts.filterMap fun (c, ty) => do
       let t ← (m.toList.find? (·.1 == c)).map (·.2)
       let v := annotateConstrValue F ty (smtTermToLExpr t constructorNames)
       if smtTermIsValue t constructorNames && valueHasMonoType F v ty then some (c.name, v)
       else none)
  match r with
  | .sat m => let (m, I) := split m; (.sat m, I)
  | .unknown (some m) => let (m, I) := split m; (.unknown (some m), I)
  | other => (other, [])

end -- public section

end Core
