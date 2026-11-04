/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Identifiers
public import Strata.Languages.Core.CoreOp
public import Strata.DL.Imperative.HasVars
public import Strata.DL.Imperative.Cmd
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LState
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LTy
public import Strata.DL.Lambda.LExprEval
public import Strata.DL.Lambda.IntBoolFactory
import Strata.DL.Lambda.OperationalSemanticsProps
public import Strata.DL.Lambda.LExprDenoteEval
public import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprWFProps

namespace Core
open Std (ToFormat Format format)
---------------------------------------------------------------------

public section

open Imperative

abbrev ExpressionMetadata := Unit

/-- Core's expression language.  Its runtime factory is a Lambda factory bundled with a
consistent interpretation (`Lambda.ModeledFactory`); runtime values are semantic values
(`Lambda.SemValue`) of that interpretation, and expressions evaluate by
`Lambda.LExpr.denoteEval`, i.e. by their denotation.  The evaluator is not computable:
its compiled stand-in (`Lambda.LExpr.denoteEvalCode`) never returns, so executable code
must not call `Expression.eval`; it evaluates with the fuel-based `Lambda.LExpr.eval`. -/
abbrev Expression : PureExpr :=
   { Ident := CoreIdent,
     EqIdent := inferInstanceAs (DecidableEq (Lambda.Identifier Unit))
     Expr := Lambda.LExpr ⟨⟨ExpressionMetadata, Unit⟩, Lambda.LMonoTy⟩,
     Ty := Lambda.LTy,
     ExprMetadata := ExpressionMetadata,
     TyEnv := @Lambda.TEnv Unit inferInstance inferInstance,
     TyContext := @Lambda.LContext ⟨ExpressionMetadata, Unit⟩,
     Factory := Lambda.ModeledFactory CoreLParams,
     Val := Lambda.SemValue,
     eval := fun F σ e => Lambda.LExpr.denoteEval F σ e }

/-- The annotated free-variable occurrences of a Core expression, each annotation read as a
    monomorphic type scheme. -/
@[expose] def Expression.typedFvars (e : Expression.Expr) : List (CoreIdent × Expression.Ty) :=
  e.freeVars.filterMap fun (x, τ?) => τ?.map fun τ => (x, .forAll [] τ)

/-- The typing the annotations of a Core expression give: a free variable has the annotation of
    its first occurrence, read as a monomorphic type scheme, and no type when that occurrence is
    unannotated. -/
@[expose] def Expression.annotationTyping (e : Expression.Expr) : VarTyping Expression :=
  fun x => ((Lambda.LExpr.freeVars e).lookup x).bind (·.map (Lambda.LTy.forAll [] ·))

instance : HasFvars Expression where
  getFvars := Lambda.LExpr.LExpr.getVars
  getTypedFvars := Expression.typedFvars

instance : HasOps Expression where
  getOps := Lambda.LExpr.getOps

instance : Inhabited Expression.Expr where
  default := .intConst () 0

/-- Build an `LExpr.op` node from a structured `CoreOp`. -/
def coreOpExpr (op : CoreOp) (ty : Option Lambda.LMonoTy := none) : Expression.Expr :=
  .op () op.toString ty

/-- A runtime value belongs to a factory when it was produced under the factory's
interpretation of type constructors; it is a value of `ty` when moreover `ty` is the
(monomorphic) type of its sort. -/
instance : HasVal Core.Expression where
  value := fun f v => v.tc = f.model.tcInterp
  valueOfTy := fun f v ty => v.tc = f.model.tcInterp ∧ ty.toMonoType? = some v.sort.toMonoTy

instance : LawfulHasVal Core.Expression where
  valueOfTy_isVal := fun _ _ _ h => h.1
  valueOfTy_congr := by
    rintro f a b ty₁ ty₂ ⟨-, ha₁⟩ ⟨-, ha₂⟩ ⟨hb, hb₂⟩
    exact ⟨hb, ha₁.trans (ha₂.symm.trans hb₂)⟩

instance : HasFvar Core.Expression where
  mkFvar := (.fvar () · none)
  -- A Core variable's annotation is a monomorphic type, so a polymorphic one
  -- annotates nothing: `toMonoType?` yields `none` and the variable stays bare.
  mkTypedFvar := fun v ty => .fvar () v ty.toMonoType?
  getFvar
  | .fvar _ v _ => some v
  | _ => none

/-- Structural free-variable name rewrite for `Core.Expression`: rewrites each
`.fvar m name ty` to `.fvar m (g name) ty`, reconstructing every other node
unchanged.  Metadata `m`, binder names and type annotations `ty` are carried
through on every constructor, so this maps only free-variable *names*.  It is the
annotation-preserving counterpart of `Lambda.LExpr.substFvars`, which would
instead replace a whole node with a freshly built bare free variable and so drop
`ty`. -/
@[expose] def Expression.mapFvarNames (g : CoreIdent → CoreIdent) :
    Lambda.LExpr ⟨⟨ExpressionMetadata, Unit⟩, Lambda.LMonoTy⟩ →
    Lambda.LExpr ⟨⟨ExpressionMetadata, Unit⟩, Lambda.LMonoTy⟩
  | .const m c => .const m c
  | .bvar m i => .bvar m i
  | .op m o ty => .op m o ty
  | .fvar m name ty => .fvar m (g name) ty
  | .abs m name ty e' => .abs m name ty (Expression.mapFvarNames g e')
  | .quant m qk name ty tr' e' =>
      .quant m qk name ty (Expression.mapFvarNames g tr') (Expression.mapFvarNames g e')
  | .app m fn e' => .app m (Expression.mapFvarNames g fn) (Expression.mapFvarNames g e')
  | .ite m c t e' =>
      .ite m (Expression.mapFvarNames g c) (Expression.mapFvarNames g t)
        (Expression.mapFvarNames g e')
  | .eq m e1 e2 => .eq m (Expression.mapFvarNames g e1) (Expression.mapFvarNames g e2)

/-- Rename the free variables of a `Core.Expression` by name, defined as a
`mapFvarNames` through the first-match rename of each name (unchanged off the
sources).  Expressed in terms of `mapFvarNames`, so it preserves each node's
metadata, binder names and type annotations by construction — in particular it
never drops a `.fvar`'s type annotation `ty`. -/
@[expose] def Expression.renameFvars
    (e : Lambda.LExpr ⟨⟨ExpressionMetadata, Unit⟩, Lambda.LMonoTy⟩)
    (subst : List (CoreIdent × CoreIdent)) :
    Lambda.LExpr ⟨⟨ExpressionMetadata, Unit⟩, Lambda.LMonoTy⟩ :=
  Expression.mapFvarNames (Imperative.renameLookup (P := Core.Expression) subst) e

instance : HasSubstFvar Core.Expression where
  substFvar := Lambda.LExpr.substFvar
  substFvars := Lambda.LExpr.substFvars
  renameFvars := Expression.renameFvars

instance : HasIdent Core.Expression where
  ident s := ⟨s, ()⟩

/-- Syntactic free-variable laws for `Core.Expression`'s structural `Has*`
operations, independent of the evaluator: `mkFvar`/`getFvars`/`ident`
agree with the abstract `Lawful*` contracts. -/
instance : LawfulHasFvar Core.Expression where
  getFvar_mkFvar := fun _ => rfl
  getFvar_mkTypedFvar := fun _ _ => rfl
  getOps_mkTypedFvar := fun _ _ => rfl

instance : LawfulHasFvars Core.Expression where
  mkFvar_getFvars := fun _ => by
    simp [HasFvars.getFvars, HasFvar.mkFvar, Lambda.LExpr.LExpr.getVars]
  mkTypedFvar_getFvars := fun _ _ => by
    simp [HasFvars.getFvars, HasFvar.mkTypedFvar, Lambda.LExpr.LExpr.getVars]
  mem_getFvars_of_typed := fun e x ty h => by
    simp only [HasFvars.getTypedFvars, Expression.typedFvars, List.mem_filterMap,
      Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨y, τ?⟩, hmem, τ, -, rfl, -⟩ := h
    show y ∈ Lambda.LExpr.LExpr.getVars e
    rw [Lambda.getVars_eq_freeVars_idents]
    exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  mkTypedFvar_getTypedFvars := fun x ty => by
    intro p hp
    simp only [HasFvars.getTypedFvars, Expression.typedFvars, HasFvar.mkTypedFvar,
      Lambda.LExpr.freeVars, List.filterMap_cons, List.filterMap_nil] at hp
    cases ty with
    | forAll vs τ =>
      cases vs <;> simp_all [Lambda.LTy.toMonoType?]

instance : LawfulHasIdent Core.Expression where
  ident_inj := by
    intro a b h
    cases h
    rfl

@[expose, match_pattern]
def Core.true : Core.Expression.Expr := .boolConst () Bool.true
@[expose, match_pattern]
def Core.false : Core.Expression.Expr := .boolConst () Bool.false

/-- Syntactic check for integer numeral literals in Core. -/
@[expose] def Core.isNumeral : Core.Expression.Expr → Bool
  | .const _ (.intConst _) => Bool.true
  | _ => Bool.false

/-- Core's Boolean type is the monomorphic type `bool`. -/
theorem boolTy_toMonoType :
    (Lambda.LTy.forAll [] (.tcons "bool" [])).toMonoType? = some Lambda.LMonoTy.bool := by
  simp [Lambda.LTy.toMonoType?]; rfl

instance : HasBool Core.Expression where
  tt := Core.true
  ff := Core.false
  tt_is_not_ff := by unfold Core.true Core.false; unfold Lambda.LExpr.boolConst; simp
  boolTy := .forAll [] (.tcons "bool" [])
  ttVal f := Lambda.SemValue.ofBool f.model.tcInterp Bool.true
  ffVal f := Lambda.SemValue.ofBool f.model.tcInterp Bool.false
  ttVal_ne_ffVal _ h := by cases Lambda.SemValue.ofBool_injective h
  boolIsValOfTy := fun _ => ⟨⟨rfl, boolTy_toMonoType⟩, ⟨rfl, boolTy_toMonoType⟩⟩

instance : HasInt Core.Expression where
  zero        := .intConst () 0
  intTy       := .forAll [] (.tcons "int" [])
  isNumeral   := Core.isNumeral
  isNumeralVal v := v.sort.isInt
  zeroIsNumeral := by
    show Core.isNumeral (.intConst () 0) = Bool.true
    rfl
  numeralHasNoFvars n hn := by
    cases n with
    | const _ c => cases c <;> first | rfl | simp [Core.isNumeral] at hn
    | _ => simp [Core.isNumeral] at hn

instance : LawfulHasBool Core.Expression where
  tt_getFvars := rfl
  ff_getFvars := rfl

instance : HasIntOps Core.Expression where
  eq    e1 e2 := .eq () e1 e2
  lt    e1 e2 := .app () (.app () (@Lambda.intLtFunc CoreLParams _).opExpr e1) e2

instance : HasBoolOps Core.Expression where
  not
  | Core.true => Core.false
  | Core.false => Core.true
  | e => Lambda.LExpr.app () (Lambda.boolNotFunc (T:=CoreLParams)).opExpr e
  and e1 e2 := Lambda.LExpr.app () (Lambda.LExpr.app ()
    (Lambda.boolAndFunc (T:=CoreLParams)).opExpr e1) e2
  imp e1 e2 := Lambda.LExpr.app () (Lambda.LExpr.app ()
    (Lambda.boolImpliesFunc (T:=CoreLParams)).opExpr e1) e2

---------------------------------------------------------------------

end

end Core
