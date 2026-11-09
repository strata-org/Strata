/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LExprWF
public import Strata.DL.Lambda.Factory

/-! ## Relations and conditions on annotations, contexts and substitutions

Definitions that the typing proofs state their assumptions with: agreement of
registered-type tables, registered literal types, scope stacks whose lookups
agree up to aliases, contexts whose schemes are unquantified, rewrites of the
type annotations of an expression (`AnnotRel` and its instances `AnnotRewrite`
and `AnnotInstRewrite`), registered factory signatures, lists with no
generated type-variable name, and conditions that a substitution, context or
expression avoids given type variables or binds nothing. None of them mentions
the typing relation. -/

namespace Lambda

open Strata.Util (HMaps)

public section

/-- Two registered-type tables agree when they record the same arity
    for every name. -/
def TableAgree (ks1 ks2 : KnownTypes) : Prop := ∀ n : String, ks1[n]? = ks2[n]?

namespace LExpr

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta]
  [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] [HasGen T.IDMeta]
  [Std.ToFormat (LFunc T)]

/-- Every enabled literal type uses registered constructors
    at their recorded arities. -/
def LiteralTysKnown (C : LContext T) : Prop :=
  ∀ c : LConst, C.knownTypes.containsName c.tyName = true →
    LMonoTy.knownInstance c.ty C.knownTypes = true

/-- Two optional type schemes are related when they are equal, or both are
    unquantified and their types are equal up to aliases. -/
def SchemeRel (aliases : List TypeAlias) (sD sR : Option LTy) : Prop :=
  sD = sR ∨ ∃ d r, sD = some (.forAll [] d) ∧ sR = some (.forAll [] r) ∧
    AliasEquiv aliases d r

/-- Two type-scope stacks that answer every whole-stack lookup
    with related schemes. -/
def ScopeRel (aliases : List TypeAlias)
    (tsD tsR : HMaps (Identifier T.IDMeta) LTy) : Prop :=
  ∀ x, SchemeRel aliases (tsD.find? x) (tsR.find? x)

end LExpr

/-- Every type scheme a lookup in the context finds quantifies nothing. -/
def MonoScope {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]
    (Γ : TContext IDMeta) : Prop :=
  ∀ (z : Identifier IDMeta) (tz : LTy), Γ.types.find? z = some tz →
    LTy.boundVars tz = []

/-- One permitted rewrite of an optional free-variable annotation: keep the
    annotation, drop it, or replace it with a type variable. -/
inductive AnnotStep : Option LMonoTy → Option LMonoTy → Prop where
  | keep (a : Option LMonoTy) : AnnotStep a a
  | drop (a : Option LMonoTy) : AnnotStep a none
  | tyvar (a : Option LMonoTy) (v : TyIdentifier) :
      AnnotStep a (some (.ftvar v))

/-- `e'` is `e` with each free-variable annotation related by `fv` and each
    binder annotation by `bd` to the one at the same position; everything
    else is unchanged. -/
inductive AnnotRel {T : LExprParams}
    (fv bd : Option LMonoTy → Option LMonoTy → Prop) :
    LExpr T.mono → LExpr T.mono → Prop where
  | const (m : T.Metadata) (c : LConst) :
      AnnotRel fv bd (.const m c) (.const m c)
  | op (m : T.Metadata) (o : Identifier T.IDMeta) (ty : Option LMonoTy) :
      AnnotRel fv bd (.op m o ty) (.op m o ty)
  | bvar (m : T.Metadata) (i : Nat) : AnnotRel fv bd (.bvar m i) (.bvar m i)
  | fvar (m : T.Metadata) (z : Identifier T.IDMeta) {a a' : Option LMonoTy}
      (h : fv a a') : AnnotRel fv bd (.fvar m z a) (.fvar m z a')
  | abs (m : T.Metadata) (name : String) {ty ty' : Option LMonoTy}
      {b b' : LExpr T.mono}
      (hty : bd ty ty') (h : AnnotRel fv bd b b') :
      AnnotRel fv bd (.abs m name ty b) (.abs m name ty' b')
  | quant (m : T.Metadata) (k : QuantifierKind) (name : String)
      {ty ty' : Option LMonoTy} {tr tr' b b' : LExpr T.mono} (hty : bd ty ty')
      (htr : AnnotRel fv bd tr tr') (hb : AnnotRel fv bd b b') :
      AnnotRel fv bd (.quant m k name ty tr b) (.quant m k name ty' tr' b')
  | app (m : T.Metadata) {f f' e e' : LExpr T.mono}
      (hf : AnnotRel fv bd f f') (he : AnnotRel fv bd e e') :
      AnnotRel fv bd (.app m f e) (.app m f' e')
  | ite (m : T.Metadata) {c c' t t' e e' : LExpr T.mono}
      (hc : AnnotRel fv bd c c') (ht : AnnotRel fv bd t t')
      (he : AnnotRel fv bd e e') :
      AnnotRel fv bd (.ite m c t e) (.ite m c' t' e')
  | eq (m : T.Metadata) {e1 e1' e2 e2' : LExpr T.mono}
      (h1 : AnnotRel fv bd e1 e1') (h2 : AnnotRel fv bd e2 e2') :
      AnnotRel fv bd (.eq m e1 e2) (.eq m e1' e2')

/-- `e'` is `e` with the annotation of every free-variable occurrence rewritten
    by `AnnotStep`, and every binder annotation kept. -/
abbrev AnnotRewrite {T : LExprParams} : LExpr T.mono → LExpr T.mono → Prop :=
  AnnotRel AnnotStep Eq

/-! ## Fixed signatures, avoided variables, cleared substitutions, instances -/

/-- Every function of `F` has its input and output types registered in some
    table that registers `arrow` at arity 2 and no name of an alias of `A`. -/
@[expose] def FactorySigsFixed {T : LExprParams} (A : List TypeAlias)
    (F : Factory T) : Prop :=
  ∀ f ∈ F.toArray, ∃ ks : KnownTypes, ks["arrow"]? = some 2 ∧
    (∀ al ∈ A, ks.containsName al.name = false) ∧
    ∀ ty ∈ f.output :: f.inputs.values, LMonoTy.knownInstance ty ks = true

/-- No type variable in `ps` is bound by `S` or occurs free in
    a type `S` binds. -/
@[expose] def Subst.VarsAvoid (S : Subst) (ps : List TyIdentifier) : Prop :=
  ∀ v, (v ∈ HMaps.keys S ∨ v ∈ Subst.freeVars S) → v ∉ ps

/-- No type variable in `ps` occurs free in a type scheme the context stores. -/
@[expose] def TContext.VarsAvoid {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] (Γ : TContext IDMeta) (ps : List TyIdentifier) : Prop :=
  ∀ v ∈ TContext.knownTypeVars Γ, v ∉ ps

/-- Neither the substitution nor the context of `Env` mentions
    a type variable in `ps`. -/
@[expose] def TEnv.VarsAvoid {IDMeta : Type} [DecidableEq IDMeta]
    [Hashable IDMeta] (Env : TEnv IDMeta) (ps : List TyIdentifier) : Prop :=
  Subst.VarsAvoid Env.stateSubstInfo.subst ps ∧
    TContext.VarsAvoid Env.context ps

/-- `ps` contains no generated type-variable name. -/
def NoGenName (ps : List TyIdentifier) : Prop :=
  ∀ n : Nat, TState.tyPrefix ++ toString n ∉ ps

/-- No type variable in `ps` occurs free in a free-variable or binder
    annotation of `e`. -/
@[expose] def LExpr.AnnotsAvoid {T : LExprParams} (e : LExpr T.mono)
    (ps : List TyIdentifier) : Prop :=
  ∀ t ∈ LExpr.fvarAnnotations e ++ LExpr.binderAnnotations e,
    ∀ v ∈ LMonoTy.freeVars t, v ∉ ps

/-- The substitution has no keys. -/
def SubstClear (S : Subst) : Prop := HMaps.keys S = []

/-- Every scope below the newest one binds nothing. -/
def TailClear (S : Subst) : Prop := SubstClear (HMaps.pop S)

/-- `a'` instantiates `a`: both are absent, or `a'` is `a` with
    a substitution applied. -/
@[expose] def AnnotInstantiates (a' a : Option LMonoTy) : Prop :=
  (a' = none ∧ a = none) ∨ ∃ t ρ, a = some t ∧ a' = some (LMonoTy.subst [ρ] t)

/-- `e'` is `e` with every free-variable and binder annotation replaced by an
    instance of it. -/
abbrev AnnotInstRewrite {T : LExprParams} :
    LExpr T.mono → LExpr T.mono → Prop :=
  AnnotRel AnnotInstantiates AnnotInstantiates

end -- public section
end Lambda
