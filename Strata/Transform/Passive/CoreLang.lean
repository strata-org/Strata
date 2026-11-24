/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.Lang
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.AbstractionMarkers
public import Strata.DL.Lambda.LExprDenoteEval
public import Strata.DL.Lambda.LExprDenoteEvalProps
public import Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprDenoteEvalSubst
import Strata.Util.RealProps
import all Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote
import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.Denote.LConstSemEq
import Strata.DL.Lambda.Denote.LConstSemEqProps

/-! # Core as a language of the WP and SSA phases

The `WPOps` instance of Core expressions: identifier names, the conditional `.ite`, the view of a
conditional and of a Boolean literal (`LExpr.denoteBool`), the number of nodes (`LExpr.size`),
the substitution by a lookup function (`LExpr.substFvarsBy`), and the evaluation of operator
applications on constants under a factory of functions (the operator data `OpEnv`): equalities of
constants, `Bool.Not` of a Boolean constant (`constFold`), and an application of a function of
the factory to constants by the function's concrete evaluator (`concreteFold`); and the `WPLang`
instance, their laws, from the Lambda facts about evaluation and substitution.

`concreteFold` folds an application only when its operator is annotated with an instance of the
function's declared type, by a type substitution `tyInst?` finds, the application type checks at
the type of the constant the evaluator returns, and every argument is a constant.

Key definitions: `iteView?`, `constFold`, `tyInst?`, `concreteFold`, `recordableLam` (the function
values the SSA phase records), `substLam` (where it substitutes them), the `WPOps Expression` and
`WPLang Expression` instances.

Key theorems: `iteView?_size` — the parts of a conditional are smaller than it;
`tyInst?_subst` — the substitution `tyInst?` finds instantiates the type to the instance;
`coreEvaluator_WellFormedSemanticEvalOp` — under a factory whose functions are those of `fac`,
the Core evaluator agrees with the evaluation of operator applications under `fac`;
`coreEvaluator_WellFormedSemanticEvalSubstExprs` — the Core evaluator satisfies
`WellFormedSemanticEvalSubstExprs`. -/

open Imperative Lambda

namespace Core
namespace WP

public section

/-- The parts of a Core conditional. -/
@[expose] def iteView? : Expression.Expr → Option
    (Expression.Expr × Expression.Expr × Expression.Expr)
  | .ite _ c t f => some (c, t, f)
  | _ => none

/-- The parts of a Core conditional are smaller than it. -/
theorem iteView?_size {e c t f : Expression.Expr} (h : iteView? e = some (c, t, f)) :
    LExpr.size _ c < LExpr.size _ e ∧ LExpr.size _ t < LExpr.size _ e ∧
      LExpr.size _ f < LExpr.size _ e := by
  cases e <;> cases h; simp only [LExpr.size]; omega

/-- A conditional recognized by `iteView?` evaluates like the canonical conditional of its parts;
    the root location does not affect `Expression.eval` (`denoteEval`). -/
private theorem iteView?_eval_core {F : Expression.Factory} {σ : Imperative.SemanticStore Expression}
    {e c t f : Expression.Expr} (h : iteView? e = some (c, t, f)) :
    Expression.eval F σ e = Expression.eval F σ (.ite valueLoc c t f) := by
  cases e <;> simp only [iteView?] at h
  case ite m a b c' =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    apply Option.ext; intro v
    simp only [Lambda.LExpr.denoteEval_ite_iff]
  all_goals exact absurd h (by simp)

/-- A conditional recognized by `iteView?` has the free variables of the canonical conditional of
    its parts (the root location does not affect free variables). -/
private theorem iteView?_getFvars_core {e c t f : Expression.Expr} (y : Expression.Ident)
    (h : iteView? e = some (c, t, f)) :
    (y ∈ HasFvars.getFvars e ↔ y ∈ HasFvars.getFvars (.ite valueLoc c t f : Expression.Expr)) := by
  cases e <;> simp only [iteView?] at h
  case ite m a b c' =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [HasFvars.getFvars, LExpr.LExpr.getVars]
  all_goals exact absurd h (by simp)

/-- The annotated free-variable occurrences of a conditional recognized by `iteView?` are those
    of the canonical conditional of its parts. -/
private theorem typedFvars_iteView_core {e c t f : Expression.Expr} (p)
    (h : iteView? e = some (c, t, f)) :
    (p ∈ HasFvars.getTypedFvars e ↔
      p ∈ HasFvars.getTypedFvars (.ite valueLoc c t f : Expression.Expr)) := by
  cases e <;> cases h
  simp [HasFvars.getTypedFvars, Expression.typedFvars, LExpr.freeVars]

/-- The operators of a conditional recognized by `iteView?` are those of its parts. -/
theorem iteView?_getOps {e c t f : Expression.Expr} (h : iteView? e = some (c, t, f)) :
    HasOps.getOps e = HasOps.getOps c ++ HasOps.getOps t ++ HasOps.getOps f := by
  cases e <;> cases h <;> rfl

/-- A Core expression that `boolLit?` reads as a Boolean literal has no operator. -/
theorem boolLit?_getOps {e : Expression.Expr} {b : Bool} (h : LExpr.denoteBool e = some b) :
    HasOps.getOps e = [] := by
  unfold LExpr.denoteBool at h
  split at h <;> first | rfl | cases h

/-- A Core expression that `boolLit?` reads as `b` evaluates like the literal `b`. -/
private theorem boolLit?_eval_core {F : Expression.Factory} {σ : Imperative.SemanticStore Expression}
    {e : Expression.Expr} {b : Bool} (h : LExpr.denoteBool e = some b) :
    Expression.eval F σ e =
      Expression.eval F σ (if b then HasBool.tt (P := Expression) else HasBool.ff (P := Expression)) := by
  unfold LExpr.denoteBool at h
  split at h
  · rename_i m b0
    rw [Option.some.injEq] at h; subst h
    cases b0 <;>
      simp [HasBool.tt, HasBool.ff, Core.true, Core.false, Lambda.LExpr.boolConst,
        Lambda.LExpr.denoteEval_boolConst]
  · exact absurd h (by simp)

/-- The constant `constFold` gives an equality whose sides fold to `ca` and `cb`: the Boolean
    literal `LConst.semEq?` gives when the two literals have one type, and none otherwise. -/
@[expose] def constFoldEq : Option LConst → Option LConst → Option LConst
  | some ca, some cb =>
    if ca.ty = cb.ty then (LConst.semEq? (max ca.depth cb.depth) ca cb).map .boolConst else none
  | _, _ => none

/-- The constant `constFold` gives an application of `f` to an argument that folds to `c`: the
    negation of a Boolean literal when `f` is `Bool.Not`, and none otherwise. -/
@[expose] def constFoldApp (f : Expression.Expr) (c : Option LConst) : Option LConst :=
  if f = (Lambda.boolNotFunc (T := CoreLParams)).opExpr then
    match c with
    | some (.boolConst b) => some (.boolConst !b)
    | _ => none
  else none

/-- The constant a Core expression has in every store, for an expression built from constants by
    equalities of two constants of one type and by the Boolean negation `Bool.Not`.

    An equality of two literals is folded by comparing what they denote (`LConst.semEq?`), not
    how they are written, and is not folded when that comparison is undecided. Structural
    comparison is wrong for map literals: `{true ↦ 1, false ↦ 2}` and `{false ↦ 2, true ↦ 1}`
    denote one function, and so does `{true ↦ 1, false ↦ 2}` with any default, since both keys
    of `bool` are listed and the default is never reached.

    Only *well-typed* literals (`LConst.wt`) are folded, and this guard must not be dropped: a
    literal that is not well typed has no typing, so as an expression it has no value at all,
    while `constFold_eval` gives every folded literal one. Such a literal is a collection literal
    whose elements do not have the sort it declares, as in `LConst.sequenceConst .bool
    [.intConst 0]`. -/
@[expose] def constFold : Expression.Expr → Option LConst
  | .const _ c => if c.wt then some c else none
  | .eq _ a b => constFoldEq (constFold a) (constFold b)
  | .app _ f a => constFoldApp f (constFold a)
  | _ => none

/-- **`constFold` yields only well-typed literals.**  The `.const` case folds only a well-typed
    literal, and the `.eq` and `Bool.Not` cases build a Boolean literal, which is always well
    typed. -/
theorem constFold_wt : ∀ {e : Expression.Expr} {c : LConst}, constFold e = some c → c.wt = true
  | e, _, h => by
    cases e <;> simp only [constFold, constFoldEq, constFoldApp] at h
    all_goals (repeat' split at h) <;> try cases h
    all_goals first | assumption | rfl | (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 h; rfl)

mutual
/-- The bindings `acc` extended with those that send each type variable of `decl` to the type at
    its position in `ty`, positions where the two types disagree contributing nothing. -/
@[expose] def tyBind : LMonoTy → LMonoTy → List (TyIdentifier × LMonoTy) →
    List (TyIdentifier × LMonoTy)
  | .ftvar a, ty, acc => (a, ty) :: acc
  | .tcons _ ds, .tcons _ ts, acc => tyBinds ds ts acc
  | _, _, acc => acc

/-- `tyBind` on the types of two lists at equal positions, from the bindings `acc`. -/
@[expose] def tyBinds : List LMonoTy → List LMonoTy → List (TyIdentifier × LMonoTy) →
    List (TyIdentifier × LMonoTy)
  | d :: ds, t :: ts, acc => tyBinds ds ts (tyBind d t acc)
  | _, _, acc => acc
end

/-- A type substitution instantiating the type `decl` to the type `ty`: the bindings `tyBind`
    reads off `ty`, when they instantiate `decl` to `ty`. -/
@[expose] def tyInst? (decl ty : LMonoTy) : Option Subst :=
  let S : Subst := Strata.Util.HMaps.ofScopes [tyBind decl ty []]
  if decl.subst S = ty then some S else none

/-- The substitution `tyInst? decl ty` finds instantiates `decl` to `ty`. -/
theorem tyInst?_subst {decl ty : LMonoTy} {S : Subst} (h : tyInst? decl ty = some S) :
    decl.subst S = ty := by
  simp only [tyInst?, Option.ite_none_right_eq_some] at h
  exact Option.some.inj h.2 ▸ h.1

/-- The constant the concrete evaluator of a function of `fac` gives an application of the
    function to constants: the operator is annotated with an instance of the function's declared
    type (`tyInst?`), every argument is a constant, the evaluator, given that annotation, returns
    a constant and the application type checks at that constant's type. -/
@[expose] def concreteFold (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    Option LConst :=
  match fac.callOfLFunc e with
  | some (.op _ o (some ty), args, fn) =>
    if fn.name.name = o.name ∧
        (tyInst? (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)) ty).isSome ∧
        args.all LExpr.isConst = true then
      match fn.concreteEval.bind (fun ce => ce coreLoc (some ty) args) with
      | some (.const _ c) =>
        if c.wt = true ∧ LExpr.typeCheck [] e = some c.ty then some c else none
      | _ => none
    else none
  | _ => none

/-- An expression `concreteFold` folds to the literal `c` type checks at `c`'s type. -/
theorem concreteFold_typeCheck {fac : Lambda.Factory CoreLParams} {e : Expression.Expr}
    {c : LConst} (h : concreteFold fac e = some c) : LExpr.typeCheck [] e = some c.ty := by
  unfold concreteFold at h
  (repeat' split at h) <;> cases h
  exact ‹_ ∧ _›.2

/-- **`concreteFold` yields only well-typed literals**: it folds only to a well-typed result
    of the concrete evaluator. -/
theorem concreteFold_wt {fac : Lambda.Factory CoreLParams} {e : Expression.Expr}
    {c : LConst} (h : concreteFold fac e = some c) : c.wt = true := by
  unfold concreteFold at h
  (repeat' split at h) <;> cases h
  exact ‹_ ∧ _›.1

/-- The constant a Core expression folds to under the factory `fac`: `constFold`, otherwise
    `concreteFold`. -/
@[expose] def opFold (fac : Lambda.Factory CoreLParams) (e : Expression.Expr) : Option LConst :=
  match constFold e with
  | some c => some c
  | none => concreteFold fac e

/-- **`opFold` yields only well-typed literals.** -/
theorem opFold_wt {fac : Lambda.Factory CoreLParams} {e : Expression.Expr} {c : LConst}
    (h : opFold fac e = some c) : c.wt = true := by
  simp only [opFold] at h
  split at h
  · exact Option.some.inj h ▸ constFold_wt ‹_›
  · exact concreteFold_wt h

/-- The number of occurrences in `e` of the bound variable of de Bruijn index `k`. -/
@[expose] def bvarUses (k : Nat) : Expression.Expr → Nat
  | .bvar _ i => if i = k then 1 else 0
  | .abs _ _ _ b => bvarUses (k + 1) b
  | .quant _ _ _ _ tr b => bvarUses (k + 1) tr + bvarUses (k + 1) b
  | .app _ f a => bvarUses k f + bvarUses k a
  | .ite _ c t f => bvarUses k c + bvarUses k t + bvarUses k f
  | .eq _ a b => bvarUses k a + bvarUses k b
  | .const .. | .op .. | .fvar .. => 0

/-- Does every abstraction of the Core expression read its bound variable at most once? -/
@[expose] def affine : Expression.Expr → Bool
  | .abs _ _ _ b => bvarUses 0 b ≤ 1 && affine b
  | .quant _ _ _ _ tr b => affine tr && affine b
  | .app _ f a => affine f && affine a
  | .ite _ c t f => affine c && affine t && affine f
  | .eq _ a b => affine a && affine b
  | .const .. | .op .. | .bvar .. | .fvar .. => true

/-- Does the Core expression contain an abstraction? -/
@[expose] def hasAbs : Expression.Expr → Bool
  | .abs .. => true
  | .quant _ _ _ _ tr b => hasAbs tr || hasAbs b
  | .app _ f a => hasAbs f || hasAbs a
  | .ite _ c t f => hasAbs c || hasAbs t || hasAbs f
  | .eq _ a b => hasAbs a || hasAbs b
  | .const .. | .op .. | .bvar .. | .fvar .. => false

/-- Is the Core expression an abstraction each of whose abstractions reads its bound variable at
    most once (`affine`), or one whose body holds no abstraction? -/
@[expose] def recordableLam : Expression.Expr → Bool
  | e@(.abs _ _ _ b) => affine e || !hasAbs b
  | _ => false

/-- Is the Core expression a literal, an operator, or a variable that `atom` accepts: an argument
    a beta reduction may copy without growing the term by more than the copies of one node? -/
@[expose] def atomArg (atom : Expression.Ident → Bool) : Expression.Expr → Bool
  | .const .. | .op .. => true
  | .fvar _ y _ => atom y
  | _ => false

/-- Is every occurrence of the free variable `x` in the Core expression the operator of an
    application to an argument `atomArg atom` accepts? -/
@[expose] def appliedToAtoms (x : Expression.Ident) (atom : Expression.Ident → Bool) :
    Expression.Expr → Bool
  | .app _ (.fvar _ y _) a => (y != x || atomArg atom a) && appliedToAtoms x atom a
  | .fvar _ y _ => y != x
  | .app _ f a => appliedToAtoms x atom f && appliedToAtoms x atom a
  | .abs _ _ _ b => appliedToAtoms x atom b
  | .quant _ _ _ _ tr b => appliedToAtoms x atom tr && appliedToAtoms x atom b
  | .ite _ c t f => appliedToAtoms x atom c && appliedToAtoms x atom t && appliedToAtoms x atom f
  | .eq _ a b => appliedToAtoms x atom a && appliedToAtoms x atom b
  | .const .. | .op .. | .bvar .. => true

/-- May the SSA phase write the function value `v` in place of `x` in `e`: when `v` is `affine`
    (a beta reduction of it copies no argument), or when `e` applies `x` only to literals,
    operators and variables `atom` accepts (a beta reduction of it copies only such an
    argument).  Either way no beta reduction of an application of `v` in the result copies an
    argument larger than one node, and its result is smaller than the application. -/
@[expose] def substLam (v : Expression.Expr) (x : Expression.Ident)
    (atom : Expression.Ident → Bool) (e : Expression.Expr) : Bool :=
  affine v || appliedToAtoms x atom e

/-- Are the two Core expressions the same constant? -/
@[expose] def sameLit : Expression.Expr → Expression.Expr → Bool
  | .const _ c, .const _ d => decide (c = d)
  | _, _ => false

/-- Two Core expressions that `sameLit` accepts are the same literal up to its source location,
    so they have the same value in every store: the root metadata affects neither the free
    variables, nor the annotated type check, nor the denotation. -/
private theorem sameLit_eval {F : Expression.Factory} {σ : Imperative.SemanticStore Expression}
    {a b : Expression.Expr} (h : sameLit a b = true) :
    Expression.eval F σ a = Expression.eval F σ b := by
  unfold sameLit at h
  split at h
  · obtain rfl := of_decide_eq_true h
    exact LExpr.denoteEval_replaceMetadata1 F σ _ (.const _ _)
  · cases h

/-- The operations of the WP and SSA phases on Core expressions. -/
instance : Imperative.WP.WPOps Expression where
  name x := x.name
  ite c t e := .ite valueLoc c t e
  iteView? := iteView?
  size := LExpr.size _
  iteView?_size := iteView?_size
  boolLit? := LExpr.denoteBool
  substFn := LExpr.substFvarsBy
  tyBEq a b := decide (a = b)
  keepsTrueAssume := isAbstractionMarker
  lit? | .const _ _ => true | _ => false
  lam? | .abs _ _ _ _ => true | _ => false
  recordableLam? := recordableLam
  substLam? := substLam
  sameLit := sameLit
  OpEnv := Lambda.Factory CoreLParams
  evalOp? fac e := (opFold fac e).map (.const valueLoc)

/-- The laws of the operations of the WP and SSA phases on Core expressions. -/
instance : Imperative.WP.WPLang Expression where
  getFvars_tt := rfl
  getFvars_ff := rfl
  getFvars_ite c t e y := by
    change y ∈ LExpr.LExpr.getVars (LExpr.ite valueLoc c t e) ↔ _
    simp [HasFvars.getFvars, LExpr.LExpr.getVars]
  getFvars_substFvars e sm y h := by
    simp only [HasFvars.getFvars, getVars_eq_freeVars_idents] at h ⊢
    exact LExpr.freeVars_substFvars sm e y h
  getFvar_getFvars {e} {y} h := by
    cases e <;> simp_all [HasFvar.getFvar, HasFvars.getFvars, LExpr.LExpr.getVars]
  ev_ite_congr {F σ σ' c t e c' t' e' v} h hc ht he := by
    obtain ⟨b, vt, ve, h1, h2, h3, hs, rfl⟩ := (LExpr.denoteEval_ite_iff (T := CoreLParams)).mp h
    exact (LExpr.denoteEval_ite_iff (T := CoreLParams)).mpr
        ⟨b, vt, ve, hc _ h1, ht _ h2, he _ h3, hs, rfl⟩
  ev_ite_inv {F σ c t e v} h := by
    obtain ⟨b, vt, ve, h1, h2, h3, -, rfl⟩ := (LExpr.denoteEval_ite_iff (T := CoreLParams)).mp h
    cases b
    · exact .inr ⟨h1, h3⟩
    · exact .inl ⟨h1, h2⟩
  iteView?_eval h := by exact iteView?_eval_core h
  iteView?_getFvars y h := by exact iteView?_getFvars_core y h
  typedFvars_iteView p h := by exact typedFvars_iteView_core p h
  boolLit?_eval h := by exact boolLit?_eval_core h
  substFn_eq e look sm h := by
    simp only [HasSubstFvar.substFvars, LExpr.substFvars_eq_substFvarsBy]
    refine LExpr.substFvarsBy_congr e _ _ fun x hx => h x ?_
    simpa [HasFvars.getFvars, getVars_eq_freeVars_idents] using hx
  substFvars_nil e := by
    change Lambda.LExpr.substFvars e [] = e
    unfold Lambda.LExpr.substFvars
    rfl
  tyBEq_eq h := of_decide_eq_true h
  getTypedFvars_ite c t e p h := by
    change p ∈ Expression.typedFvars (LExpr.ite valueLoc c t e) at h
    simpa [HasFvars.getTypedFvars, Expression.typedFvars, LExpr.freeVars, List.filterMap_append,
      or_assoc] using h
  getTypedFvars_substFn e g p h := by
    change p ∈ Expression.typedFvars (LExpr.substFvarsBy e g) at h
    simp only [HasFvars.getTypedFvars, Expression.typedFvars, List.mem_filterMap,
      Option.map_eq_some_iff] at h ⊢
    obtain ⟨⟨x, τ?⟩, hx, τ, rfl, rfl⟩ := h
    rcases LExpr.mem_freeVars_substFvarsBy hx with ⟨hx, hg⟩ | ⟨y, tyy, r, hy, hg, hr⟩
    · exact .inl ⟨⟨_, hx, τ, rfl, rfl⟩, hg⟩
    · refine .inr ⟨y, r, ?_, hg, ⟨_, hr, τ, rfl, rfl⟩⟩
      change y ∈ LExpr.LExpr.getVars e
      rw [getVars_eq_freeVars_idents]
      exact List.mem_map.2 ⟨_, hy, rfl⟩
  sameLit_eval h := by exact sameLit_eval h
  getFvars_evalOp? {_ e r} h y hy := by
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h
    nomatch hy
  getTypedFvars_evalOp? {_ e r} h p hp := by
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h
    nomatch hp

/-! ## The evaluation of operator applications on constants -/

/-- A well-typed literal's value as a `SemValue` is its `constVal` at the sort of its type. -/
private theorem ofConst_eq_mk {tc : TyConstrInterp} {c : LConst} (hw : c.wt = true)
    {s : LSort} (hs : c.ty.substTyVars refTyVarVal = s) {x : SortDenote tc s}
    (hx : constVal tc s c = some x) : SemValue.ofConst tc c = ⟨tc, s, x⟩ := by
  subst hs
  exact Option.some.inj ((constVal_denoteConst refTyVarVal hw).symm.trans hx) ▸ rfl

/-- **Two well-typed literals of one type have equal values exactly as `semEq?` decides**, when
    it decides. -/
private theorem ofConst_eq_iff_semEq {tc : TyConstrInterp} [TyConstrInterp.AllInhabited tc]
    {ca cb : LConst} (hca : ca.wt = true) (hcb : cb.wt = true) (hty : ca.ty = cb.ty) {n : Nat}
    {b : Bool} (h : LConst.semEq? n ca cb = some b) :
    SemValue.ofConst tc ca = SemValue.ofConst tc cb ↔ b = true := by
  obtain ⟨y, hy⟩ : ∃ y, constVal tc (ca.ty.substTyVars refTyVarVal) cb = some y :=
    hty ▸ ⟨_, constVal_denoteConst refTyVarVal hcb⟩
  have hx := constVal_denoteConst (tcInterp := tc) refTyVarVal hca
  rw [ofConst_eq_mk hca rfl hx, ofConst_eq_mk hcb (by rw [hty]) hy, ← LConst.semEq?_sound n hx hy h]
  exact ⟨fun he => by cases he; rfl, fun he => by rw [he]⟩

/-- Under a factory whose evaluator respects Boolean negation (`WellFormedSemanticEvalBool`),
    `Bool.Not` applied to an expression with the Boolean value `b` has the value `!b`.  The law
    pins the interpretation of `Bool.Not` through a conditional with the value `b`, which
    `HasBoolOps.not` negates by `Bool.Not`. -/
private theorem eval_boolNot {F : Expression.Factory}
    (hB : WellFormedSemanticEvalBool (P := Expression) F) {σ : SemanticStore Expression}
    {m : ExpressionMetadata} {a : Expression.Expr} {b : Bool}
    (ha : Expression.eval F σ a = some (SemValue.ofBool F.model.tcInterp b)) :
    Expression.eval F σ (.app m (Lambda.boolNotFunc (T := CoreLParams)).opExpr a) =
      some (SemValue.ofBool F.model.tcInterp !b) := by
  have hite : Expression.eval F σ (.ite valueLoc (.boolConst valueLoc b) (.boolConst valueLoc b)
      (.boolConst valueLoc b)) = some (SemValue.ofBool F.model.tcInterp b) :=
    (LExpr.denoteEval_ite_iff (T := CoreLParams)).2 ⟨b, _, _, LExpr.denoteEval_const,
      LExpr.denoteEval_const, LExpr.denoteEval_const, rfl, by cases b <;> rfl⟩
  have hn : Expression.eval F σ (.app m (Lambda.boolNotFunc (T := CoreLParams)).opExpr
      (.ite valueLoc (.boolConst valueLoc b) (.boolConst valueLoc b) (.boolConst valueLoc b))) =
      some (SemValue.ofBool F.model.tcInterp !b) := by
    cases b <;> first | exact ((hB σ _).2.1 hite :) | exact ((hB σ _).1.1 hite :)
  obtain ⟨b', hb', hi⟩ := (LExpr.denoteEval_app_op_bool_iff (T := CoreLParams)).1 hn
  obtain rfl := SemValue.ofBool_injective (Option.some.inj (hite.symm.trans hb'))
  exact (LExpr.denoteEval_app_op_bool_iff (T := CoreLParams)).2 ⟨b, ha, hi⟩

/-- An expression `constFold` gives the constant `c` has the value of `c` in every store, under a
    factory whose evaluator respects Boolean negation. -/
private theorem constFold_eval {F : Expression.Factory}
    (hB : WellFormedSemanticEvalBool (P := Expression) F) (σ : SemanticStore Expression) :
    ∀ {e : Expression.Expr} {c : LConst}, constFold e = some c →
      Expression.eval F σ e = some (SemValue.ofConst F.model.tcInterp c)
  | .const _ c, _, h => by
    simp only [constFold] at h
    split at h <;> cases h
    exact LExpr.denoteEval_const ‹_›
  | .eq _ a b, c, h => by
    simp only [constFold, constFoldEq] at h
    split at h <;> try cases h
    rename_i ca cb ha hb
    split at h <;> try cases h
    rename_i hty
    have hca := constFold_eval hB σ ha
    have hcb := constFold_eval hB σ hb
    letI := F.model.allInhabited
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    have hiff := ofConst_eq_iff_semEq (tc := F.model.tcInterp) (constFold_wt ha)
      (constFold_wt hb) hty hr
    cases r
    · exact LExpr.denoteEval_eq_false (T := CoreLParams) hca hcb
        (by simp [SemValue.ofConst, hty]) fun he => by simpa using hiff.1 he
    · exact LExpr.denoteEval_eq_true (T := CoreLParams) hca
        (hcb.trans (congrArg some (hiff.2 rfl).symm))
  | .app _ f a, c, h => by
    simp only [constFold, constFoldApp] at h
    split at h <;> try cases h
    subst f
    split at h <;> try cases h
    exact eval_boolNot hB (constFold_eval hB σ ‹_›)
  | .op .., _, h | .bvar .., _, h | .fvar .., _, h | .abs .., _, h | .quant .., _, h
  | .ite .., _, h => by cases h

/-- A free variable of `e` is one of the operator or of an argument `getLFuncCall.go e acc`
    decomposes `e` into, and the arguments contain `acc`. -/
private theorem getLFuncCall_go_getVars (e : Expression.Expr) (acc : List Expression.Expr) :
    (∀ a ∈ acc, a ∈ (getLFuncCall.go e acc).2) ∧
    ∀ y ∈ LExpr.LExpr.getVars e, y ∈ LExpr.LExpr.getVars (getLFuncCall.go e acc).1 ∨
      ∃ a ∈ (getLFuncCall.go e acc).2, y ∈ LExpr.LExpr.getVars a := by
  fun_induction getLFuncCall.go e acc <;> grind [LExpr.LExpr.getVars]

/-- An expression `concreteFold` folds to the constant `c` under the functions of the factory
    `F` has, in every store, the value of `c`: the model interprets the function at the
    arguments' values as the evaluator's result. -/
private theorem concreteFold_eval {F : Expression.Factory} {fac : Lambda.Factory CoreLParams}
    (hF : F.factory = fac) (σ : SemanticStore Expression) {e : Expression.Expr} {c : LConst}
    (h : concreteFold fac e = some c) :
    Expression.eval F σ e = Expression.eval F σ (.const valueLoc c) := by
  subst hF
  unfold concreteFold at h
  split at h <;> try cases h
  rename_i m o ty args fn hcall
  split at h <;> try cases h
  obtain ⟨hn, hty, hargs⟩ := ‹_ ∧ _ ∧ _›
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.1 hty
  replace hty := (subst_mkArrow' S _ _).symm.trans (tyInst?_subst hS)
  split at h <;> try cases h
  rename_i m' _ hce
  split at h <;> try cases h
  obtain ⟨hcw, htc⟩ := ‹c.wt = true ∧ _›
  letI := F.model.allInhabited
  have hT := LExpr.typeCheck_to_HasTypeA htc
  have hgl : getLFuncCall.go e [] = _ := callOfLFunc_getLFuncCall hcall
  have hcl : ∀ y, y ∉ LExpr.LExpr.getVars e := by
    intro y hy
    rcases hgl ▸ (getLFuncCall_go_getVars e []).2 y hy with h2 | ⟨a, ha, hya⟩
    · simp [LExpr.LExpr.getVars] at h2
    · have hca := List.all_eq_true.1 hargs a ha
      cases a <;> simp_all [LExpr.isConst, LExpr.LExpr.getVars]
  have hann : ∀ e' : Expression.Expr, (∀ y, y ∉ LExpr.LExpr.getVars e') →
      e'.annotateFvars (ValStore.ann (T := CoreLParams) σ) = e' := fun e' h' =>
    LExpr.annotateFvars_eq_self e' fun x ty hx =>
      (h' x (LExpr.mem_getVars_of_mem_freeVars hx)).elim
  have hg : c.ty.IsGround := LConst.ty_isGround c
  have hd : ∀ e' : Expression.Expr, (∀ y, y ∉ LExpr.LExpr.getVars e') →
      ValStore.Defines (T := CoreLParams) σ F.model.tcInterp e' :=
    fun e' h' y hy => (h' y hy).elim
  have hcc : ∀ y, y ∉ LExpr.LExpr.getVars (LExpr.const valueLoc c : Expression.Expr) :=
    fun _ => nofun
  show LExpr.denoteEval (T := CoreLParams) F σ e = LExpr.denoteEval F σ (.const valueLoc c)
  rw [LExpr.denoteEval_of_hasTypeA (hd e hcl) ((hann e hcl).symm ▸ hT) hg,
    LExpr.denoteEval_of_hasTypeA (hd _ hcc) ((hann _ hcc).symm ▸ .const hcw) hg]
  unfold LExpr.denoteEvalResult
  refine congrArg some (SemValue.mk_eq_mk rfl ?_)
  obtain ⟨m0, nm, ty0, ⟨⟩, hlook⟩ := Factory.callOfLFunc_getElem? hcall
  obtain ⟨argTys, ty_op, mo, name, h_args, hty_op, ⟨⟩, hden⟩ :=
    callOfLFunc_denote F.model.tcInterp F.model.opInterp
      (ValStore.fvarVal F.model.tcInterp σ) F.tyVarVal hcall hT
  obtain ⟨hout, hins⟩ := LMonoTy.mkArrow'_injective ((h_args.length_eq.symm.trans
    (Factory.callOfLFunc_arity hcall)).trans ((List.length_map _).trans (List.length_map _)).symm)
    (hty_op.symm.trans hty.symm)
  subst hins
  have hcongr : ∀ {e1 e2 : Expression.Expr} {τ1 τ2 : LMonoTy} (_ : e1 = e2) (_ : τ1 = τ2)
      (h1 : e1.HasTypeA [] τ1) (h2 : e2.HasTypeA [] τ2),
      HEq (LExpr.denote F.model.tcInterp F.model.opInterp
        (ValStore.fvarVal F.model.tcInterp σ) F.tyVarVal .nil e1 τ1 h1)
        (LExpr.denote F.model.tcInterp F.model.opInterp
        (ValStore.fvarVal F.model.tcInterp σ) F.tyVarVal .nil e2 τ2 h2) :=
    fun he hτ _ _ => by subst he hτ; rfl
  have hres : (LExpr.const m' c : Expression.Expr).HasTypeA [] (fn.output.subst S) :=
    hout ▸ .const hcw
  have hconst : ∀ {m1 m2 : ExpressionMetadata} {τ1 τ2 : LMonoTy} (_ : τ1 = τ2)
      (h1 : (LExpr.const m1 c : Expression.Expr).HasTypeA [] τ1)
      (h2 : (LExpr.const m2 c : Expression.Expr).HasTypeA [] τ2),
      HEq (LExpr.denote F.model.tcInterp F.model.opInterp
        (ValStore.fvarVal F.model.tcInterp σ) F.tyVarVal .nil _ τ1 h1)
        (LExpr.denote F.model.tcInterp F.model.opInterp
        (ValStore.fvarVal F.model.tcInterp σ) F.tyVarVal .nil _ τ2 h2) :=
    fun hτ h1 h2 => by subst hτ; cases h1; cases h2; rfl
  have hci := opInterp_of_concreteEval_subst F.model hlook hn S (hty ▸ hce) F.tyVarVal
    (ValStore.fvarVal F.model.tcInterp σ) h_args hres
  have hop : ∀ {s1 s2 : LSort} (_ : s1 = s2),
      HEq (F.model.opInterp o.name s1) (F.model.opInterp o.name s2) := fun h => by subst h; rfl
  have happ : ∀ {L : List LSort} {r r' : LSort} (_ : r = r')
      {f : SortDenote F.model.tcInterp (LSort.mkArrow r L)}
      {f' : SortDenote F.model.tcInterp (LSort.mkArrow r' L)} (_ : HEq f f') xs,
      HEq (SortDenote.applyArgs F.model.tcInterp f xs)
        (SortDenote.applyArgs F.model.tcInterp f' xs) :=
    fun {_ _ _} hr {_ _} hf _ => by subst hr; cases hf; rfl
  refine (hcongr (hann e hcl) rfl _ hT).trans (heq_of_eq hden |>.trans ?_)
  refine (happ ?_ ((eqRec_heq _ _).trans (hop ?_)) _).trans
    ((heq_of_eq hci).symm.trans
      ((hconst hout.symm hres (.const hcw)).trans (hcongr (hann _ hcc).symm rfl _ _)))
  · exact congrArg _ hout
  · rw [← hty, substTyVars_mkArrow', ← hout]

/-- **The Core evaluation of operator applications on constants agrees with the evaluator**
    (`WellFormedSemanticEvalOp`) under the factory `fac`, for a factory `F` whose functions are
    those of `fac` and whose evaluator respects Boolean negation: the folded equalities of
    constants are decided by the semantics of `==`, `Bool.Not` is pinned by
    `WellFormedSemanticEvalBool`, and a function's concrete evaluator agrees with its
    interpretation in the model of `F`. -/
theorem coreEvaluator_WellFormedSemanticEvalOp (F : Expression.Factory)
    (fac : Lambda.Factory CoreLParams) (hfac : F.factory = fac)
    (hB : WellFormedSemanticEvalBool (P := Expression) F) :
    Imperative.WP.WellFormedSemanticEvalOp (P := Expression) F fac := by
  intro σ e r _ h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold opFold at hc
  split at hc <;> try cases hc
  · exact (LExpr.denoteEval_const (T := CoreLParams) (constFold_wt ‹_›)).trans
      (constFold_eval hB σ ‹_›).symm
  · exact (concreteFold_eval hfac σ hc).symm

/-- The Core evaluator commutes with substituting, for free variables, expressions whose values
    are the variables' values (`WellFormedSemanticEvalSubstExprs`). -/
theorem coreEvaluator_WellFormedSemanticEvalSubstExprs (F : Expression.Factory) :
    Imperative.WP.WellFormedSemanticEvalSubstExprs (P := Expression) F := by
  intro σ σ' _ _ sm e hsm hrest
  have hmem : ∀ {x ty}, (x, ty) ∈ e.freeVars → x ∈ HasFvars.getFvars (P := Expression) e :=
    fun hx => (getVars_eq_freeVars_idents e ▸ List.mem_map.2 ⟨_, hx, rfl⟩ :)
  show LExpr.denoteEval F σ' (LExpr.substFvars e sm) = LExpr.denoteEval F σ e
  rw [LExpr.substFvars_eq_substFvarsBy (T := CoreLParams)]
  exact LExpr.denoteEval_substFvarsBy_of_denoteEval _ e (fun x _ r hx hr => hsm x (hmem hx) r hr)
    fun x _ hx hn => hrest x (hmem hx) hn

end -- public section

end WP
end Core
