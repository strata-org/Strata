/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.EvalContext
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.InterpreterConfig

/-! # Level-`(b)` counterexamples and their validity (parametric in `P`)

A proof obligation `ProofObligation P` is a claim `A → Q` (assumptions `A`, goal
`Q`) over a flat set of variables.  A **level-`(b)` counterexample** is simply a
*valuation* of those variables: a semantic store (`SemanticStore P`, values `P.Val`) for the
specification check, a runtime store of value expressions for the executable check.
There is no input-vs-nondeterministic distinction at level `(b)` (that structure
is created later, by the `(b) → (a)` translation); a level-`(b)` counterexample
is just the valuation.

*Validity* of a valuation against an obligation is decided generically over a
`ObligationEvaluator` (an evaluator, the Boolean values it compares results with, and a
value-and-type gate): the specification instance `ObligationEvaluator.spec` evaluates with `P.eval`
on semantic stores, the runtime instance `ObligationEvaluator.runtime` with a runtime evaluator on
runtime stores.  `ρ` is a counterexample to the obligation's *validity* iff, under `ρ`, the
assumptions `A` reduce to true and the goal `Q` reduces to false.  Evaluation is
three-valued — it can be **stuck** (the evaluator returns `none`, or a value that is neither
the true nor the false value) — so validity is decided, refuted, or `cantValidate`, never
silently Boolean.

This module is parametric in `P : PureExpr` (needing `HasBool P` for the Boolean values and
decidable equality of values for distinctness and comparison). The SMT-model source of a valuation
is Core/Lambda-specific and lives in the `(c) → (b)` layer; nothing here mentions SMT.

Key definitions: `valuationObligationCheck'` (the three-valued check), `IsValuationObligationCex`
(the level-`(b)` counterexample property), `extendWithVarDecls'`, `assumptionsHold'`. -/

namespace Imperative

public section

/-- The reduction of a Boolean-valued expression under a valuation: it is the
    true literal, the false literal, or *stuck* (did not evaluate, or evaluated
    to a non-Boolean). -/
inductive BReduction where
  | isTrue
  | isFalse
  | stuck
  deriving Repr, BEq, DecidableEq

/-- What the level-`(b)` check needs of the values it computes with, for a factory type `F` and
    a value type `V`: an evaluator `ev` of expressions under a valuation of identifiers in `V`,
    the tests `isTt`/`isFf` of whether a value it returns is the true or the false value, and
    the value-and-type gate `valOk` a `.det` variable definition's value must pass.  The runtime
    check uses runtime factories and value expressions (`ObligationEvaluator.runtime`); the
    specification uses factories and semantic values (`ObligationEvaluator.spec`). -/
structure ObligationEvaluator (P : PureExpr) (F V : Type _) where
  ev : F → (P.Ident → Option V) → P.Expr → Option V
  /-- Whether a value is the true value, up to what the evaluator may change of it (for the
      runtime check, its metadata). -/
  isTt : F → V → Bool
  /-- Whether a value is the false value, as `isTt`. -/
  isFf : F → V → Bool
  valOk : F → V → P.Ty → Bool

/-- The runtime instantiation: a runtime evaluator `ev` over runtime stores, equality up to
    metadata with the Boolean constant expressions, and the language's executable value checks
    (`InterpLang.ops`). -/
@[expose] def ObligationEvaluator.runtime [HasBool P] [InterpLang P]
    (ev : InterpLang.RFactory P → RStore P → P.Expr → Option P.Expr) :
    ObligationEvaluator P (InterpLang.RFactory P) P.Expr :=
  { ev,
    isTt := fun _ v => InterpLang.eqModuloMeta v HasBool.tt,
    isFf := fun _ v => InterpLang.eqModuloMeta v HasBool.ff,
    valOk := fun f v ty => InterpLang.ops.isValue f v && InterpLang.ops.hasType f v ty }

open Classical in
/-- The specification instantiation: the specification evaluator `P.eval` over semantic stores,
    equality with the Boolean values of the factory, and the semantic typed-value predicate. -/
@[expose] noncomputable def ObligationEvaluator.spec [HasBool P] :
    ObligationEvaluator P P.Factory P.Val :=
  { ev := P.eval,
    isTt := fun f v => decide (v = HasBool.ttVal f),
    isFf := fun f v => decide (v = HasBool.ffVal f),
    valOk := fun f v ty => decide (HasVal.valueOfTy f v ty) }

variable {F V : Type _}

/-- Reduce one expression to a `BReduction` under valuation `store`, using the
    evaluator of `L`. -/
def reduceBool' [DecidableEq V] (L : ObligationEvaluator P F V)
    (factory : F) (store : P.Ident → Option V) (e : P.Expr) : BReduction :=
  match L.ev factory store e with
  | some v =>
    if L.isTt factory v then .isTrue
    else if L.isFf factory v then .isFalse
    else .stuck
  | none => .stuck

/-- Extend a valuation with the `.det` variable-definition entries of a path
    condition, so assumptions/goal see program-defined values, using the evaluator of `L`.
    `.nondet` varDecls and non-`varDecl` entries contribute no binding.

    A `.det` varDecl whose RHS `e` does not evaluate (`L.ev factory store e = none`) makes the
    extension **fail** (`none`): the VC evaluation is incomplete at that point, so no valuation
    can be threaded and the consumers turn this into `cantValidate`/`.stuck` rather than silently
    continuing with a stale store. -/
def extendWithVarDecls' [DecidableEq P.Ident] (L : ObligationEvaluator P F V)
    (factory : F) (store : P.Ident → Option V) :
    PathCondition P → Option (P.Ident → Option V)
  | [] => some store
  | .varDecl name ty (.det e) :: rest =>
    match L.ev factory store e with
    | some v =>
      -- A valuation is only a genuine countermodel if each `.det` initial
      -- assignment evaluates to a value of its declared type — the same
      -- `isValue`/`hasType` gate strict replay applies at `.init .det`.  Threading
      -- an ill-typed value would let the countermodel predicate accept a valuation
      -- replay would reject as `.illTypedValue`.
      if L.valOk factory v ty then
        extendWithVarDecls' L factory (fun y => if y = name then some v else store y) rest
      else none
    | none => none
  | _ :: rest => extendWithVarDecls' L factory store rest

/-- Whether a path-condition entry's constraint holds under the valuation, as a
    `BReduction`, using the evaluator of `L`.  `.assumption e` reduces `e`; `.distinct
    es` is true iff all listed expressions evaluate to pairwise-distinct values
    (stuck if any fails to evaluate); `.varDecl` carries no constraint
    (`isTrue`). -/
def entryHolds' [DecidableEq V] (L : ObligationEvaluator P F V)
    (factory : F) (store : P.Ident → Option V) :
    PathConditionEntry P → BReduction
  | .assumption _ e => reduceBool' L factory store e
  | .varDecl _ _ _ => .isTrue
  | .distinct _ es =>
    match es.mapM (fun e => L.ev factory store e) with
    | none => .stuck
    | some vs => if vs.Nodup then .isTrue else .isFalse

/-- Conjoin two `BReduction`s.  A conjunct proven *false* refutes the whole
    conjunction regardless of a stuck sibling, so `isFalse` dominates `stuck`;
    a stuck conjunct otherwise makes the conjunction stuck (never skipped or
    assumed true); only all-true is true. -/
def BReduction.and : BReduction → BReduction → BReduction
  | .isFalse, _ | _, .isFalse => .isFalse
  | .stuck, _ | _, .stuck => .stuck
  | .isTrue, .isTrue => .isTrue

/-- Conjoin (`BReduction.and`) the constraints of every entry of the path conditions
    `pcs` (`entryHolds'`), all evaluated under the one valuation `store`, using
    the evaluator of `L`. -/
def assumptionsHold' [DecidableEq V] (L : ObligationEvaluator P F V)
    (factory : F) (store : P.Ident → Option V) (pcs : PathConditions P) : BReduction :=
  pcs.flatten.foldl (init := .isTrue) fun a e => a.and (entryHolds' L factory store e)

/-- Executable three-valued check that valuation `ρ` is a level-`(b)`
    counterexample, using the evaluator of `L`.  The valuation is first extended with
    the `.det` varDecls of all path conditions, in order (`extendWithVarDecls'`);
    the assumptions `A` and the goal `Q` are both evaluated under that extended
    valuation.  `isValidityCheck = true` claims `A ∧ ¬Q` (genuine iff `A` reduces
    to true and `Q` to false); `isValidityCheck = false` claims `A ∧ Q` (genuine
    iff both reduce to true).  A failed extension, or a stuck `A` or `Q`, is
    `.cantValidate`.  This is the single implementation the runtime VC check
    (`Core.runVCCheck`) and the specification (`valuationObligationValidityCheck`) share;
    the runtime instantiates `L` at a fuel-bounded evaluator over runtime stores
    (`ObligationEvaluator.runtime`), the specification at `P.eval` over semantic stores
    (`ObligationEvaluator.spec`). -/
def valuationObligationCheck' [DecidableEq V] [DecidableEq P.Ident]
    (L : ObligationEvaluator P F V)
    (factory : F) (store : P.Ident → Option V) (obligation : ProofObligation P)
    (isValidityCheck : Bool) :
    CEValidationVerdict String :=
  match obligation.assumptions.foldlM (extendWithVarDecls' L factory · ·) store with
  | none => .cantValidate "varDecl RHS did not reduce"
  | some store =>
    let a := assumptionsHold' L factory store obligation.assumptions
    let q := reduceBool' L factory store obligation.obligation
    match a, q with
    | .stuck, _ => .cantValidate "path condition did not reduce to a boolean"
    | _, .stuck => .cantValidate "goal did not reduce to a boolean"
    | .isTrue, qb =>
      if isValidityCheck then
        (match qb with | .isFalse => .genuine | _ => .spurious)
      else
        (match qb with | .isTrue => .genuine | _ => .spurious)
    | _, _ => .spurious

open Classical in
/-- Three-valued check that valuation `ρ` is a level-`(b)` counterexample to the *validity* of
    `obligation`: `A` reduces to `true` and `Q` reduces to `false`.  Returns the payload-free
    validation verdict (`.genuine` when it is a counterexample, `.spurious` when `A`/`Q` are
    decided but do not witness a counterexample, `.cantValidate` when stuck).  Uses the
    specification evaluator `P.eval`. -/
@[reducible] noncomputable def valuationObligationValidityCheck [HasBool P] [DecidableEq P.Ident]
    (factory : P.Factory) (store : SemanticStore P) (obligation : ProofObligation P) :
    CEValidationVerdict String :=
  valuationObligationCheck' (P := P) ObligationEvaluator.spec factory store obligation
    (isValidityCheck := true)

/-- The `Prop` the check certifies: `ρ` is a level-`(b)` counterexample
    to the obligation's validity — assumptions reduce to true and the goal to
    false. -/
def IsValuationObligationCex [HasBool P] [DecidableEq P.Ident]
    (factory : P.Factory) (store : SemanticStore P) (obligation : ProofObligation P) :
    Prop :=
  valuationObligationValidityCheck factory store obligation = .genuine

end -- public section

end Imperative
