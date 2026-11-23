/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeSkolem
public import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
public import Strata.Languages.Core.Typing.Soundness.TypingAssumptions
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.Denote.LExprAnnotatedProps
public import Strata.DL.Lambda.Denote.LExprResolveAnnotated
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LExprTProps
public import Strata.DL.Lambda.TypeFactoryProps
public import Strata.Util.StringProps
public import Strata.Util.ListUtilsProps
public import Strata.Util.HMapsProps
import Strata.Util.NameProofs
import Strata.DL.Imperative.CmdProps
public import Strata.Languages.Core.WF
import Strata.Languages.Core.StatementProps
import Strata.Languages.Core.ProcedureProps
public import Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
import Strata.Languages.Core.CallWFProps
import Strata.Languages.Core.IdentifiersProps
import Strata.DL.Lambda.LTyWFCheckSound
import Strata.DL.Lambda.LTyWF
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import all Strata.DL.Lambda.Denote.LExprResolveAnnotated
import Strata.DL.Lambda.LExprAliasFree
import Strata.DL.Lambda.LExprAnnotRel
import Strata.DL.Lambda.LExprWFProps
import Strata.Languages.Core.Statement
import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.Stmt
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LTyProps
import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.LTyWFProps
import Strata.DL.Lambda.NamePrefixesProps
import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
import all Strata.Languages.Core.Typing.Props.TypeSkolemProps

/-! # Source-expression resolution

Resolving a source expression keeps its context and environment well formed, accepts only
well-scoped expressions, and leaves its annotations consistent with the solved substitution.

Key theorems:
* `SourceExpr.resolve_WellScoped`: resolution accepts only expressions whose free variables are
  declared.
* `SourceExpr.resolve_TEnvWF`: resolution keeps the environment well formed.
* `SourceExpr.resolves_tailClear`: resolving a list of expressions keeps the substitution scopes
  below the newest one clear.
* `SourceExpr.resolve_HasType_instAnnots`: a resolved expression, with annotations read
  through the solved substitution, has the resolved type. -/

public section

namespace Core

open Lambda Imperative

/-! ## Core source-expression resolution -/

namespace SourceExpr

/-- Resolving the aliases of a type scheme does not change the accumulated type substitution. -/
private theorem resolveAliases_stateSubstInfo
    (ty : LTy) (Env Env' : Expression.TyEnv) (mty : LMonoTy)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp only [LTy.resolveAliases, bind, Except.bind] at h
  elim_err h with result hinstantiate
  obtain ⟨mty0, genEnv0⟩ := result
  rw [LMonoTy.resolveAliases_env_eq mty0 _ mty Env' h]

/-- Instantiating a checked scheme does not change the accumulated type substitution. -/
private theorem instantiateWithCheck_stateSubstInfo
    (ty : LTy) (C : Expression.TyContext)
    (Env Env' : Expression.TyEnv) (mty : LMonoTy)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp only [LTy.instantiateWithCheck, bind, Except.bind] at h
  elim_err h with v hresolve
  obtain ⟨mty0, Env0⟩ := v
  elim_err h
  elim_err h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, hEnv⟩ := h
  rw [← hEnv]
  exact resolveAliases_stateSubstInfo ty Env Env0 mty0 hresolve

/-- Every environment steps to itself by a generator-only step. -/
theorem GenOnly.refl (Env : Expression.TyEnv) : GenOnly Env Env :=
  ⟨rfl, rfl, Nat.le_refl _⟩

/-- Two generator-only steps in a row make one generator-only step. -/
theorem GenOnly.trans {Env1 Env2 Env3 : Expression.TyEnv}
    (h12 : GenOnly Env1 Env2) (h23 : GenOnly Env2 Env3) : GenOnly Env1 Env3 :=
  ⟨h23.context.trans h12.context, h23.subst.trans h12.subst, Nat.le_trans h12.tyGen h23.tyGen⟩

/-- Generator-only steps preserve type-environment well-formedness. -/
theorem GenOnly.envWF {Env Env' : Expression.TyEnv} (h : GenOnly Env Env')
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env) :
    LExpr.TEnvWF (T := CoreLParams) Env' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h.context]
    exact hwf.aliasesWF
  · intro v hv n hn
    rw [h.subst] at hv
    exact hwf.substFreshForGen v hv n (Nat.le_trans h.tyGen hn)
  · intro v hv n hn
    rw [h.context] at hv
    exact hwf.ctxFreshForGen v hv n (Nat.le_trans h.tyGen hn)
  · intro y ty hy
    rw [h.context] at hy
    exact hwf.boundVarsNodup y ty hy
  · intro y ty hy v hv n hn
    rw [h.context] at hy
    exact hwf.boundVarsFresh y ty hy v hv n (Nat.le_trans h.tyGen hn)

/-- The checked annotation-instantiation step is generator-only. -/
theorem instantiateWithCheck_genOnly
    (ty : LTy) (C : Expression.TyContext)
    (Env Env' : Expression.TyEnv) (mty : LMonoTy)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    GenOnly Env Env' :=
  ⟨LExpr.LTy_instantiateWithCheck_context' ty C Env mty Env' h,
   instantiateWithCheck_stateSubstInfo ty C Env Env' mty h,
   LTy_instantiateWithCheck_tyGen_mono ty C Env mty Env' h⟩

/-- What annotation linking preserves: the context, a nondecreasing type-variable generator, a
    substitution absorbing the old one, and well-formedness. -/
private structure LinkProperties
    (Env Env' : Expression.TyEnv) : Prop where
  context : Env'.context = Env.context
  tyGen : Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen
  absorbs : Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst
  envWF : LExpr.TEnvWF (T := CoreLParams) Env →
    LExpr.TEnvWF (T := CoreLParams) Env'

/-- Consecutive annotation-linking steps compose. -/
private theorem LinkProperties.trans
    {Env₁ Env₂ Env₃ : Expression.TyEnv}
    (h₁₂ : LinkProperties Env₁ Env₂)
    (h₂₃ : LinkProperties Env₂ Env₃) :
    LinkProperties Env₁ Env₃ :=
  ⟨h₂₃.context.trans h₁₂.context,
   Nat.le_trans h₁₂.tyGen h₂₃.tyGen,
   Subst.absorbs_trans _ _ _ h₁₂.absorbs h₂₃.absorbs,
   fun hwf => h₂₃.envWF (h₁₂.envWF hwf)⟩

/-- `LinkProperties` is reflexive. -/
private theorem LinkProperties.refl
    (Env : Expression.TyEnv) :
    LinkProperties Env Env :=
  ⟨rfl, Nat.le_refl _, Subst.absorbs_refl _ Env.stateSubstInfo.isWF, id⟩

/-- A successful `linkAnnot` checked the annotation and the inferred type, which uses no future
    generated type variable, and adopted their unifier in the order `binder` selects. -/
private theorem linkAnnot_inv
    (C : Expression.TyContext) (binder : Bool) (ann ty : LMonoTy) (Env Env' : Expression.TyEnv)
    (h : linkAnnot C binder ann ty Env = .ok Env') :
    ∃ annResolved EI checked S,
      ann.typeCheckSource C Env TyVarAdmissibility.notGeneratedOrRigid = .ok (annResolved, EI) ∧
      LMonoTy.checkNoFutureGenVars ty EI.genEnv.genState = true ∧
      LMonoTy.typeCheckResolved ty C TyVarAdmissibility.all = .ok checked ∧
      Constraints.unify (if binder then [(ty, annResolved)] else [(annResolved, ty)])
        EI.stateSubstInfo = .ok S ∧
      Env' = EI.updateSubst S := by
  simp only [linkAnnot, bind, Except.bind] at h
  elim_err h with result hinst
  obtain ⟨annResolved, EI⟩ := result
  by_cases hfuture : LMonoTy.checkNoFutureGenVars ty EI.genEnv.genState = true
  · simp only [hfuture, ↓reduceIte] at h
    elim_err h with checked htype
    cases hunify : Constraints.unify (if binder then [(ty, annResolved)] else [(annResolved, ty)])
        EI.stateSubstInfo with
    | error err => simp [hunify, Except.mapError] at h
    | ok S =>
      simp only [hunify, Except.mapError, Except.ok.injEq] at h
      exact ⟨annResolved, EI, checked, S, hinst, hfuture, htype, hunify, h.symm⟩
  · simp [hfuture, throw, throwThe, MonadExceptOf.throw] at h

/-- A relation `R l E E'` on environments, indexed by the annotations handled, that is reflexive,
    composes and holds across one linking step relates the input and output of a successful
    `linkFVarAnnotations` under a list holding every free-variable annotation. -/
private theorem linkFVarAnnotations_preserves
    (C : Expression.TyContext) (R : List LMonoTy → Expression.TyEnv → Expression.TyEnv → Prop)
    (hrefl : ∀ E, R [] E E)
    (htrans : ∀ l1 l2 E1 E2 E3, R l1 E1 E2 → R l2 E2 E3 → R (l1 ++ l2) E1 E3)
    (hstep : ∀ (binder : Bool) (ann annResolved ty checked : LMonoTy)
      (E EI : Expression.TyEnv) (S : SubstInfo),
      ann.typeCheckSource C E TyVarAdmissibility.notGeneratedOrRigid = .ok (annResolved, EI) →
      LMonoTy.checkNoFutureGenVars ty EI.genEnv.genState = true →
      LMonoTy.typeCheckResolved ty C TyVarAdmissibility.all = .ok checked →
      Constraints.unify (if binder then [(ty, annResolved)] else [(annResolved, ty)])
        EI.stateSubstInfo = .ok S →
      R [ann] E (EI.updateSubst S)) :
    ∀ (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
      (Env Env' : Expression.TyEnv),
      linkFVarAnnotations C source typed Env = .ok Env' →
      ∃ l, (∀ t ∈ LExpr.fvarAnnotations source, t ∈ l) ∧ R l Env Env' := by
  have hlink : ∀ binder ann ty E E', linkAnnot C binder ann ty E = .ok E' → R [ann] E E' := by
    intro binder ann ty E E' h
    obtain ⟨annResolved, EI, checked, S, hinst, hfuture, htype, hunify, rfl⟩ :=
      linkAnnot_inv C binder ann ty E E' h
    exact hstep binder ann annResolved ty checked E EI S hinst hfuture htype hunify
  have hnone : ∀ E, ∃ l, (∀ t ∈ ([] : List LMonoTy), t ∈ l) ∧ R l E E :=
    fun E => ⟨[], fun _ ht => ht, hrefl E⟩
  have hcomp : ∀ (a b : List LMonoTy) E1 E2 E3,
      (∃ l, (∀ t ∈ a, t ∈ l) ∧ R l E1 E2) → (∃ l, (∀ t ∈ b, t ∈ l) ∧ R l E2 E3) →
      ∃ l, (∀ t ∈ a ++ b, t ∈ l) ∧ R l E1 E3 := by
    intro a b E1 E2 E3 ⟨l1, hl1, h12⟩ ⟨l2, hl2, h23⟩
    refine ⟨l1 ++ l2, ?_, htrans _ _ _ _ _ h12 h23⟩
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact List.mem_append_left _ (hl1 t ht)
    · exact List.mem_append_right _ (hl2 t ht)
  have hbinder : ∀ (ann ty : Option LMonoTy) E E', linkBinderAnnot C ann ty E = .ok E' →
      ∃ l, (∀ t ∈ ([] : List LMonoTy), t ∈ l) ∧ R l E E' := by
    intro ann ty E E' h
    match ann, ty, h with
    | some ann, some ty, h =>
      exact ⟨[ann], fun _ ht => absurd ht List.not_mem_nil, hlink _ _ _ _ _ h⟩
    | none, _, h =>
      simp only [linkBinderAnnot, Except.ok.injEq] at h
      subst h
      exact hnone E
    | some _, none, h =>
      simp only [linkBinderAnnot, Except.ok.injEq] at h
      subst h
      exact hnone E
  intro source
  induction source with
  | const sm sc =>
    intro typed Env Env' h
    cases typed <;> simp only [linkFVarAnnotations, Except.ok.injEq, reduceCtorEq] at h
    subst h
    exact hnone _
  | op sm op sty =>
    intro typed Env Env' h
    cases typed <;> simp only [linkFVarAnnotations, Except.ok.injEq, reduceCtorEq] at h
    subst h
    exact hnone _
  | bvar sm index =>
    intro typed Env Env' h
    cases typed <;> simp only [linkFVarAnnotations, Except.ok.injEq, reduceCtorEq] at h
    subst h
    exact hnone _
  | fvar sm x annotation =>
    intro typed Env Env' h
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case fvar tm y typedAnnotation =>
      cases annotation with
      | none =>
        simp only [linkFVarAnnotations] at h
        elim_err h
        simp only [Except.ok.injEq] at h
        subst Env'
        exact hnone Env
      | some ann =>
        by_cases hxy : (x == y) = true
        · simp only [linkFVarAnnotations, hxy, ↓reduceIte] at h
          exact ⟨[ann], fun t ht => ht, hlink _ _ _ _ _ h⟩
        · simp [linkFVarAnnotations, hxy, bind, Except.bind] at h
  | abs sm name annotation body ih =>
    intro typed Env Env' h
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case abs tm typedName typedAnnotation typedBody =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvI hann
      simpa only [LExpr.fvarAnnotations, List.nil_append] using
        hcomp [] _ _ _ _ (hbinder _ _ _ _ hann) (ih typedBody EnvI Env' h)
  | quant sm kind name annotation trigger body ihTrigger ihBody =>
    intro typed Env Env' h
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case quant tm typedKind typedName typedAnnotation typedTrigger typedBody =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvA hann
      elim_err h with EnvI htrigger
      have hrest := hcomp _ _ _ _ _ (ihTrigger typedTrigger EnvA EnvI htrigger)
        (ihBody typedBody EnvI Env' h)
      simpa only [LExpr.fvarAnnotations, List.nil_append] using
        hcomp [] _ _ _ _ (hbinder _ _ _ _ hann) hrest
  | app sm fn arg ihFn ihArg =>
    intro typed Env Env' h
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case app tm typedFn typedArg =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvI hfn
      exact hcomp _ _ _ _ _ (ihFn typedFn Env EnvI hfn) (ihArg typedArg EnvI Env' h)
  | ite sm cond thenBranch elseBranch ihCond ihThen ihElse =>
    intro typed Env Env' h
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case ite tm typedCond typedThen typedElse =>
      simp only [bind, Except.bind] at h
      elim_err h with Env₁ hcond
      elim_err h with Env₂ hthen
      exact hcomp _ _ _ _ _
        (hcomp _ _ _ _ _ (ihCond typedCond Env Env₁ hcond) (ihThen typedThen Env₁ Env₂ hthen))
        (ihElse typedElse Env₂ Env' h)
  | eq sm lhs rhs ihLhs ihRhs =>
    intro typed Env Env' h
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case eq tm typedLhs typedRhs =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvI hlhs
      exact hcomp _ _ _ _ _ (ihLhs typedLhs Env EnvI hlhs) (ihRhs typedRhs EnvI Env' h)

/-- Linking free-variable and binder annotations has `LinkProperties`. -/
private theorem linkFVarAnnotations_properties
    (C : Expression.TyContext) :
    ∀ (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
      (Env Env' : Expression.TyEnv),
      linkFVarAnnotations C source typed Env = .ok Env' →
      LinkProperties Env Env' := by
  intro source typed Env Env' h
  refine (linkFVarAnnotations_preserves C (fun _ => LinkProperties) LinkProperties.refl
    (fun _ _ _ _ _ h12 h23 => h12.trans h23) ?_ source typed Env Env' h).choose_spec.2
  intro binder ann annResolved ty _ Env EnvI S hinst hfuture _ hunify
  have hinstOld := typeCheckSource_notGeneratedOrRigid_instantiateWithCheck
    ann annResolved C Env EnvI hinst
  have hgen :=
    instantiateWithCheck_genOnly
      (.forAll [] ann) C Env EnvI annResolved hinstOld
  have hannFresh :=
    LExpr.LTy_instantiateWithCheck_freeVars_fresh
      (.forAll [] ann) C Env annResolved EnvI hinstOld
  have htypedFresh : ∀ v, v ∈ LMonoTy.freeVars ty →
      ∀ n, n ≥ EnvI.genEnv.genState.tyGen →
        v ≠ TState.tyPrefix ++ toString n :=
    Lambda.LExpr.checkNoFutureGenVars_imp_fresh ty EnvI.genEnv.genState hfuture
  refine ⟨hgen.context, by simpa only [TEnv.updateSubst] using hgen.tyGen, ?_, fun hwf => ?_⟩
  · have hsubst : Env.stateSubstInfo.subst = EnvI.stateSubstInfo.subst := by rw [hgen.subst]
    rw [hsubst]
    exact Constraints.unify_absorbs _ _ _ hunify
  · have hwfI := hgen.envWF hwf
    apply LExpr.TEnvWF_updateSubst_of_unify (T := CoreLParams) EnvI _ S hwfI hunify
    intro v hv n hn
    cases binder <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Constraints.freeVars, Constraint.freeVars,
        List.append_nil, List.mem_append] at hv
    · cases hv with
      | inl hv => exact hannFresh v hv n hn
      | inr hv => exact htypedFresh v hv n hn
    · cases hv with
      | inl hv => exact htypedFresh v hv n hn
      | inr hv => exact hannFresh v hv n hn

/-- When linking succeeds, each free-variable annotation is a valid source type against the
    starting aliases, with no reserved type-variable name. -/
private theorem linkFVarAnnotations_fvarAnnotsWF
    (C : Expression.TyContext) :
    ∀ (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
      (Env Env' : Expression.TyEnv),
      linkFVarAnnotations C source typed Env = .ok Env' →
      TypeSpec.FVarAnnotsWF C TyVarAdmissibility.notGeneratedOrRigid
        Env.context.aliases source := by
  intro source typed Env Env' h
  have hpres := linkFVarAnnotations_preserves C
    (fun l E E' => E'.context = E.context ∧
      ∀ t ∈ l, ∃ r, SourceTyWF C TyVarAdmissibility.notGeneratedOrRigid E.context.aliases t r)
    (fun _ => ⟨rfl, fun t ht => absurd ht List.not_mem_nil⟩) ?htrans ?hstep source typed Env Env' h
  · obtain ⟨l, hsub, hR⟩ := hpres
    intro t ht
    exact hR.2 t (hsub t ht)
  case htrans =>
    intro l1 l2 E1 E2 E3 h12 h23
    refine ⟨h23.1.trans h12.1, ?_⟩
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact h12.2 t ht
    · rw [← h12.1]
      exact h23.2 t ht
  case hstep =>
    intro _ ann annResolved ty _ E EI S hinst _ _ _
    have hinstOld := typeCheckSource_notGeneratedOrRigid_instantiateWithCheck
      ann annResolved C E EI hinst
    refine ⟨(instantiateWithCheck_genOnly (.forAll [] ann) C E EI annResolved hinstOld).context,
      ?_⟩
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨annResolved, LMonoTy.typeCheckSource_sound t annResolved C E EI _ hinst⟩

/-- Linking free-variable and binder annotations preserves a registered substitution range. -/
private theorem linkFVarAnnotations_RangeKnown
    (C : Expression.TyContext) :
    ∀ (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
      (Env Env' : Expression.TyEnv),
      linkFVarAnnotations C source typed Env = .ok Env' →
      Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes →
      Subst.RangeKnown Env'.stateSubstInfo.subst C.knownTypes := by
  intro source typed Env Env' h
  refine (linkFVarAnnotations_preserves C
    (fun _ E E' => Subst.RangeKnown E.stateSubstInfo.subst C.knownTypes →
      Subst.RangeKnown E'.stateSubstInfo.subst C.knownTypes)
    (fun _ hrange => hrange) (fun _ _ _ _ _ h12 h23 hrange => h23 (h12 hrange)) ?_
    source typed Env Env' h).choose_spec.2
  intro binder ann annResolved ty checked Env EnvI S hinst _ htype hunify hrange
  have hinstOld := typeCheckSource_notGeneratedOrRigid_instantiateWithCheck
    ann annResolved C Env EnvI hinst
  have hrangeI : Subst.RangeKnown EnvI.stateSubstInfo.subst C.knownTypes := by
    rw [instantiateWithCheck_stateSubstInfo
      (.forAll [] ann) C Env EnvI annResolved hinstOld]
    exact hrange
  have hannKnown :
      LMonoTy.knownInstance annResolved C.knownTypes = true :=
    LTy_instantiateWithCheck_knownInstance
      (.forAll [] ann) C Env annResolved EnvI hinstOld
  have htypedKnown : LMonoTy.knownInstance ty C.knownTypes = true := by
    simp only [LMonoTy.typeCheckResolved] at htype
    elim_err htype
    elim_err htype with hknown
    exact hknown
  have hconstraints : ∀ constraint ∈ (if binder then [(ty, annResolved)] else [(annResolved, ty)]),
      LMonoTy.knownInstance constraint.1 C.knownTypes = true ∧
        LMonoTy.knownInstance constraint.2 C.knownTypes = true := by
    intro constraint hconstraint
    cases binder <;>
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hconstraint <;>
      subst constraint
    · exact ⟨hannKnown, htypedKnown⟩
    · exact ⟨htypedKnown, hannKnown⟩
  simpa only [TEnv.updateSubst] using
    Constraints.unify_RangeKnown C.knownTypes _ EnvI.stateSubstInfo S hunify hrangeI hconstraints

/-- Core source resolution succeeds only if no binder annotation names a generated or rigid
    type variable. -/
private theorem resolve_reservedBinderAnnot?_eq_none
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    reservedBinderAnnot? source = none := by
  cases hreserved : reservedBinderAnnot? source with
  | none => rfl
  | some _ =>
    simp only [resolve, hreserved, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
      reduceCtorEq] at h

/-- Core source resolution is ordinary Lambda resolution followed by annotation linking. -/
theorem resolve_decompose
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    ∃ EnvR,
      LExpr.resolve C Env source = .ok (typed, EnvR) ∧
      linkFVarAnnotations C source typed EnvR = .ok Env' := by
  have hreserved := resolve_reservedBinderAnnot?_eq_none C Env Env' source typed h
  simp only [resolve, hreserved, bind, Except.bind] at h
  elim_err h with result hresolve
  obtain ⟨typedR, EnvR⟩ := result
  elim_err h with EnvL hlink
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨EnvR, hresolve, hlink⟩

/-- If `reservedBinderAnnot?` finds nothing, every binder annotation's type variables are
    neither generated nor rigid. -/
private theorem binderAnnotTyVarsAdmissible_of_reservedBinderAnnot?_eq_none (e : Expression.Expr)
    (h : reservedBinderAnnot? e = none) :
    TypeSpec.BinderAnnotTyVarsAdmissible TyVarAdmissibility.notGeneratedOrRigid e := by
  intro t ht v hv
  have hall := List.find?_eq_none.mp h t ht
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hall
  exact List.all_eq_true.mp hall v hv

/-- When Core source resolution succeeds, no binder annotation names a generated or rigid type
    variable. -/
theorem resolve_binderAnnotTyVarsAdmissible
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    TypeSpec.BinderAnnotTyVarsAdmissible TyVarAdmissibility.notGeneratedOrRigid source :=
  binderAnnotTyVarsAdmissible_of_reservedBinderAnnot?_eq_none source
    (resolve_reservedBinderAnnot?_eq_none C Env Env' source typed h)

/-- Adding the free-variable error to an action succeeds exactly when the action succeeds, with
    the same result. -/
theorem orFreeVarError_eq_ok {ε α : Type} {freeVarErr : Unit → Except ε Unit}
    {act : Except ε α} {a : α} :
    orFreeVarError freeVarErr act = .ok a ↔ act = .ok a := by
  unfold orFreeVarError
  cases act with
  | ok b => rfl
  | error err =>
    cases freeVarErr () <;> simp only [reduceCtorEq]

/-- Linking succeeds only on a source and a typed expression of the same shape with the same
    free-variable names, so every free variable of the source is one of the typed expression. -/
theorem linkFVarAnnotations_getVars (C : Expression.TyContext) :
    ∀ (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
      (Env Env' : Expression.TyEnv),
      linkFVarAnnotations C source typed Env = .ok Env' →
      ∀ x ∈ LExpr.LExpr.getVars source, x ∈ LExpr.LExpr.getVars typed := by
  intro source
  induction source with
  | const | op | bvar =>
    intro _ _ _ _ x hx
    simp only [LExpr.LExpr.getVars, List.not_mem_nil] at hx
  | fvar sm x annotation =>
    intro typed Env Env' h y hy
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case fvar tm z typedAnnotation =>
      have hxz : (x == z) = true := by
        cases annotation with
        | none =>
          simp only [linkFVarAnnotations] at h
          split at h
          · assumption
          · simp at h
        | some ann =>
          by_cases hb : (x == z) = true
          · exact hb
          · simp [linkFVarAnnotations, hb, bind, Except.bind] at h
      have heq : x = z := beq_iff_eq.mp hxz
      simp only [LExpr.LExpr.getVars, List.mem_singleton] at hy ⊢
      rw [hy, heq]
  | abs sm name annotation body ih =>
    intro typed Env Env' h x hx
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case abs tm typedName typedAnnotation typedBody =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvI hann
      simp only [LExpr.LExpr.getVars] at hx ⊢
      exact ih typedBody EnvI Env' h x hx
  | quant sm kind name annotation trigger body ihTrigger ihBody =>
    intro typed Env Env' h x hx
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case quant tm typedKind typedName typedAnnotation typedTrigger typedBody =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvA hann
      elim_err h with EnvI htrigger
      simp only [LExpr.LExpr.getVars, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihTrigger typedTrigger EnvA EnvI htrigger x hx)
      · exact Or.inr (ihBody typedBody EnvI Env' h x hx)
  | app sm fn arg ihFn ihArg =>
    intro typed Env Env' h x hx
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case app tm typedFn typedArg =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvI hfn
      simp only [LExpr.LExpr.getVars, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihFn typedFn Env EnvI hfn x hx)
      · exact Or.inr (ihArg typedArg EnvI Env' h x hx)
  | ite sm cond thenBranch elseBranch ihCond ihThen ihElse =>
    intro typed Env Env' h x hx
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case ite tm typedCond typedThen typedElse =>
      simp only [bind, Except.bind] at h
      elim_err h with Env₁ hcond
      elim_err h with Env₂ hthen
      simp only [LExpr.LExpr.getVars, List.mem_append] at hx ⊢
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl (ihCond typedCond Env Env₁ hcond x hx))
      · exact Or.inl (Or.inr (ihThen typedThen Env₁ Env₂ hthen x hx))
      · exact Or.inr (ihElse typedElse Env₂ Env' h x hx)
  | eq sm lhs rhs ihLhs ihRhs =>
    intro typed Env Env' h x hx
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case eq tm typedLhs typedRhs =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvI hlhs
      simp only [LExpr.LExpr.getVars, List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (ihLhs typedLhs Env EnvI hlhs x hx)
      · exact Or.inr (ihRhs typedRhs EnvI Env' h x hx)

/-- Core source resolution accepts only expressions whose free variables are all declared in the
    input context. A free variable named like a generated binder is captured by that binder during
    elaboration, and annotation linking then rejects the mismatch. -/
theorem resolve_WellScoped
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    LExpr.WellScoped source Env.context := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' source typed h
  intro x hx
  have hsrc : x.1 ∈ LExpr.LExpr.getVars source := by
    rw [getVars_eq_freeVars_idents]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  have htyped := linkFVarAnnotations_getVars C source typed EnvR Env' hlink x.1 hsrc
  have hout : x.1 ∈ LExpr.LExpr.getVars
      (LExpr.unresolved (LExpr.applySubstT typed EnvR.stateSubstInfo.subst)) := by
    rw [LExpr.Proofs.getVars_unresolved, LExpr.Proofs.getVars_applySubstT]
    exact htyped
  rw [getVars_eq_freeVars_idents] at hout
  obtain ⟨⟨y, ann⟩, hmem, hy⟩ := List.mem_map.mp hout
  obtain ⟨sch, hfind⟩ := Lambda.resolve_fvar_declared C Env EnvR source typed hresolve
    EnvR.stateSubstInfo.subst hmem
  simp only at hy
  rw [hy] at hfind
  unfold TContext.knownVars
  exact Strata.Util.HMaps.find?_mem_keys Env.context.types hfind

/-- Core source resolution returns the typing context of the Lambda resolution it runs. -/
private theorem resolve_context_of_lambda
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    ∃ EnvR, LExpr.resolve C Env source = .ok (typed, EnvR) ∧ Env'.context = EnvR.context := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' source typed h
  exact ⟨EnvR, hresolve, (linkFVarAnnotations_properties C source typed EnvR Env' hlink).context⟩

/-- Core source resolution returns an environment with at least one type scope. -/
theorem resolve_context_types_ne
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    Env'.context.types ≠ [] := by
  obtain ⟨EnvR, hresolve, hcontext⟩ := resolve_context_of_lambda C Env Env' source typed h
  rw [hcontext]
  exact LExpr.resolve_context_types_ne source typed C Env EnvR hresolve

/-- Core source resolution preserves, up to equivalence, the type scopes below the newest one,
    and keeps the aliases. -/
theorem resolve_context_pop_equiv
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    Strata.Util.HMaps.Equiv Env'.context.types.pop Env.context.types.pop ∧
      Env'.context.aliases = Env.context.aliases := by
  obtain ⟨EnvR, hresolve, hcontext⟩ := resolve_context_of_lambda C Env Env' source typed h
  rw [hcontext]
  exact LExpr.resolve_context_pop_equiv source typed C Env EnvR hresolve

/-- When Core source resolution starts from an empty type-scope stack, the resulting type-scope
    stack is equivalent to a single empty scope, and the aliases are unchanged. -/
theorem resolve_context_of_empty
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) (hnil : Env.context.types = []) :
    Strata.Util.HMaps.Equiv Env'.context.types [Strata.Util.HMap.empty] ∧
      Env'.context.aliases = Env.context.aliases := by
  obtain ⟨EnvR, hresolve, hcontext⟩ := resolve_context_of_lambda C Env Env' source typed h
  rw [hcontext]
  exact LExpr.resolve_context_of_empty source typed C Env EnvR hresolve hnil

/-- When Core source resolution starts from a nonempty type-scope stack, the resulting context
    is equivalent to the starting one. -/
theorem resolve_context_equiv_of_ne
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) (hne : Env.context.types ≠ []) :
    TContext.Equiv (T := CoreLParams) Env'.context Env.context := by
  obtain ⟨EnvR, hresolve, hcontext⟩ := resolve_context_of_lambda C Env Env' source typed h
  rw [hcontext]
  exact LExpr.resolve_context_equiv_of_ne source typed C Env EnvR hresolve hne

/-- When Core source resolution succeeds, each free-variable annotation is a valid source type
    against the starting aliases, with no reserved type-variable name. -/
theorem resolve_fvarAnnotsWF
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    TypeSpec.FVarAnnotsWF C TyVarAdmissibility.notGeneratedOrRigid
      Env.context.aliases source := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' source typed h
  rw [← (LExpr.resolve_context_pop_equiv source typed C Env EnvR hresolve).2]
  exact linkFVarAnnotations_fvarAnnotsWF C source typed EnvR Env' hlink

/-- Core source resolution preserves a registered substitution range and reports a registered
    result type. -/
private theorem resolve_RangeKnown
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env'))
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (hfac : FactorySigWF C.functions)
    (harrow : C.knownTypes["arrow"]? = some 2)
    (hbool : C.knownTypes["bool"]? = some 0)
    (hlit : LExpr.LiteralTysKnown C)
    (hrange : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown Env'.stateSubstInfo.subst C.knownTypes ∧
      LMonoTy.knownInstance typed.toLMonoTy C.knownTypes = true := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' source typed h
  obtain ⟨hrangeR, htyped⟩ := Lambda.resolve_RangeKnown
    source typed C Env EnvR hresolve hwf hfac harrow hbool hlit hrange
  exact ⟨linkFVarAnnotations_RangeKnown C source typed EnvR Env' hlink hrangeR, htyped⟩

/-- Core source resolution in a fresh substitution scope preserves lookups and closedness once
    that scope is popped. -/
theorem resolve_pushSubstScope_context_FindEq
    (C : Expression.TyContext) (Env : Expression.TyEnv) (e : Expression.Expr)
    (i : Identifiers Unit) (typed : LExprT CoreLParams.mono) (Env' : Expression.TyEnv)
    (h : resolve { C with idents := i } Env.pushEmptySubstScope e = .ok (typed, Env'))
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env) (hfac : FactorySigWF C.functions) :
    TContext.FindEq (T := CoreLParams) Env'.popSubstScope.context Env.context ∧
      (LExpr.checkContextTypesClosed (T := CoreLParams) Env →
        LExpr.checkContextTypesClosed (T := CoreLParams) Env'.popSubstScope) := by
  obtain ⟨EnvR, hresolve, hcontext⟩ := resolve_context_of_lambda
    { C with idents := i } Env.pushEmptySubstScope Env' e typed h
  obtain ⟨hfind, hclosed⟩ := LExpr.resolve_pushSubstScope_context_FindEq
    C Env e i (typed, EnvR) hresolve hwf hfac
  constructor
  · change TContext.FindEq (T := CoreLParams) Env'.context Env.context
    rw [hcontext]
    simpa only [TEnv.popSubstScope, TEnv.context] using hfind
  · intro hc
    change List.all Env'.context.types (fun x =>
      x.all fun _ ty => LTy.freeVars ty == []) = true
    rw [hcontext]
    simpa only [TEnv.popSubstScope, LExpr.checkContextTypesClosed, TEnv.context] using
      hclosed hc

/-- Core source resolution preserves type-environment well-formedness. -/
theorem resolve_TEnvWF
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env'))
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (hfac : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) Env' := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' source typed h
  have hwfR := Lambda.resolve_TEnvWF source typed C Env EnvR hresolve hwf hfac
  exact (linkFVarAnnotations_properties C source typed EnvR Env' hlink).envWF hwfR

/-- `arrowDomain?` reads the domain that `isArrow` reports. -/
private theorem isArrow_of_arrowDomain? {t d : LMonoTy} (h : arrowDomain? t = some d) :
    ∃ c, t.isArrow = some (d, c) := by
  unfold arrowDomain? at h
  split at h
  · rename_i xty cod
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨cod, rfl⟩
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- Linking a binder annotation keeps the type scope and only refines the substitution. -/
private theorem linkBinderAnnot_context_absorbs (C : Expression.TyContext)
    (ann ty : Option LMonoTy) (Env Env' : Expression.TyEnv)
    (h : linkBinderAnnot C ann ty Env = .ok Env') :
    Env'.context = Env.context ∧
      Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  match ann, ty, h with
  | some a, some t, h =>
    obtain ⟨annResolved, EI, -, S', hinst, -, -, hunify, rfl⟩ := linkAnnot_inv C true a t Env Env' h
    have hEI : EI = Env := LMonoTy.resolveAliases_env_eq a Env annResolved EI
      (LMonoTy.typeCheckSource_resolveAliases a annResolved C Env EI _ hinst)
    subst hEI
    exact ⟨rfl, Constraints.unify_absorbs _ _ _ hunify⟩
  | none, _, h =>
    simp only [linkBinderAnnot, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, Subst.absorbs_refl _ Env.stateSubstInfo.isWF⟩
  | some _, none, h =>
    simp only [linkBinderAnnot, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, Subst.absorbs_refl _ Env.stateSubstInfo.isWF⟩

/-- Linking annotations keeps a substitution avoiding `ps` when the annotations of the source and
    of the resolved expression avoid `ps`. -/
private theorem linkFVarAnnotations_varsAvoid (C : Expression.TyContext) {ps : List TyIdentifier} :
    ∀ (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
      (Env Env' : Expression.TyEnv),
      linkFVarAnnotations C source typed Env = .ok Env' →
      TContext.AliasesWF Env.context → LExpr.AnnotsAvoid source ps →
      LExpr.AnnotsAvoid (LExpr.unresolved typed) ps →
      Subst.VarsAvoid Env.stateSubstInfo.subst ps →
      Subst.VarsAvoid Env'.stateSubstInfo.subst ps := by
  have hlink : ∀ binder ann ty E E', linkAnnot C binder ann ty E = .ok E' →
      TContext.AliasesWF E.context → (∀ v ∈ LMonoTy.freeVars ann, v ∉ ps) →
      (∀ v ∈ LMonoTy.freeVars ty, v ∉ ps) →
      Subst.VarsAvoid E.stateSubstInfo.subst ps → Subst.VarsAvoid E'.stateSubstInfo.subst ps := by
    intro binder ann ty E E' h haw hann hty hS
    obtain ⟨annResolved, EI, -, S, hinst, -, -, hunify, rfl⟩ :=
      linkAnnot_inv C binder ann ty E E' h
    have hres := LMonoTy.typeCheckSource_resolveAliases ann annResolved C E EI _ hinst
    have hEI : EI = E := LMonoTy.resolveAliases_env_eq ann E annResolved EI hres
    subst hEI
    have hR : ∀ v ∈ LMonoTy.freeVars annResolved, v ∉ ps := fun v hv =>
      hann v (LExpr.LMonoTy_resolveAliases_freeVars_subset ann EI annResolved EI hres haw v hv)
    simp only [TEnv.updateSubst]
    refine Constraints.unify_varsAvoid hunify hS (Constraints.freeVars_varsAvoid ?_)
    intro c hc
    cases binder <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hc <;>
      subst hc
    · exact ⟨hR, hty⟩
    · exact ⟨hty, hR⟩
  have hbinder : ∀ (ann ty : Option LMonoTy) E E', linkBinderAnnot C ann ty E = .ok E' →
      TContext.AliasesWF E.context → (∀ a ∈ ann.toList, ∀ v ∈ LMonoTy.freeVars a, v ∉ ps) →
      (∀ a ∈ ty.toList, ∀ v ∈ LMonoTy.freeVars a, v ∉ ps) →
      Subst.VarsAvoid E.stateSubstInfo.subst ps → Subst.VarsAvoid E'.stateSubstInfo.subst ps := by
    intro ann ty E E' h haw hann hty hS
    match ann, ty, h with
    | some a, some t, h =>
      exact hlink true a t E E' h haw (hann a (List.mem_singleton.mpr rfl))
        (hty t (List.mem_singleton.mpr rfl)) hS
    | none, _, h =>
      simp only [linkBinderAnnot, Except.ok.injEq] at h
      subst h
      exact hS
    | some _, none, h =>
      simp only [linkBinderAnnot, Except.ok.injEq] at h
      subst h
      exact hS
  have hctx : ∀ s t E E', linkFVarAnnotations C s t E = .ok E' → E'.context = E.context :=
    fun s t E E' h => (linkFVarAnnotations_properties C s t E E' h).context
  intro source
  induction source with
  | const sm sc =>
    intro typed Env Env' h _ _ _ hS
    cases typed <;> simp only [linkFVarAnnotations, Except.ok.injEq, reduceCtorEq] at h
    subst h
    exact hS
  | op sm op sty =>
    intro typed Env Env' h _ _ _ hS
    cases typed <;> simp only [linkFVarAnnotations, Except.ok.injEq, reduceCtorEq] at h
    subst h
    exact hS
  | bvar sm index =>
    intro typed Env Env' h _ _ _ hS
    cases typed <;> simp only [linkFVarAnnotations, Except.ok.injEq, reduceCtorEq] at h
    subst h
    exact hS
  | fvar sm x annotation =>
    intro typed Env Env' h haw hsrc htyp hS
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case fvar tm y typedAnnotation =>
      cases annotation with
      | none =>
        simp only [linkFVarAnnotations] at h
        elim_err h
        simp only [Except.ok.injEq] at h
        subst Env'
        exact hS
      | some ann =>
        by_cases hxy : (x == y) = true
        · simp only [linkFVarAnnotations, hxy, ↓reduceIte] at h
          refine hlink false ann tm.type Env Env' h haw
            (hsrc.of_fvar ann (List.mem_singleton.mpr rfl)) ?_ hS
          exact htyp.of_fvar tm.type (List.mem_singleton.mpr rfl)
        · simp [linkFVarAnnotations, hxy, bind, Except.bind] at h
  | abs sm name annotation body ih =>
    intro typed Env Env' h haw hsrc htyp hS
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case abs tm typedName typedAnnotation typedBody =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvI hann
      obtain ⟨hsrcAnn, hsrcBody⟩ := hsrc.of_abs
      have htypAbs : LExpr.AnnotsAvoid (LExpr.unresolved typedBody) ps ∧
          ∀ d, arrowDomain? tm.type = some d → ∀ v ∈ LMonoTy.freeVars d, v ∉ ps := by
        have hu : ∀ e', LExpr.AnnotsAvoid
            (LExpr.unresolved (.abs tm typedName typedAnnotation typedBody)) ps →
            e' = LExpr.unresolved typedBody → LExpr.AnnotsAvoid e' ps := by
          intro e' h' he'
          subst he'
          simp only [LExpr.unresolved] at h'
          split at h' <;> exact h'.of_abs.2
        refine ⟨hu _ htyp rfl, ?_⟩
        intro d hd
        obtain ⟨c, hc⟩ := isArrow_of_arrowDomain? hd
        simp only [LExpr.unresolved, hc] at htyp
        exact htyp.of_abs.1 d (List.mem_singleton.mpr rfl)
      have hdom : ∀ d ∈ (arrowDomain? tm.type).toList, ∀ v ∈ LMonoTy.freeVars d, v ∉ ps := by
        intro d hd
        refine htypAbs.2 d ?_
        simpa only [Option.mem_toList] using hd
      have hSI := hbinder annotation (arrowDomain? tm.type) Env EnvI hann haw hsrcAnn hdom hS
      exact ih typedBody EnvI Env' h ((linkBinderAnnot_context_absorbs C _ _ _ _ hann).1 ▸ haw)
        hsrcBody htypAbs.1 hSI
  | quant sm kind name annotation trigger body ihTrigger ihBody =>
    intro typed Env Env' h haw hsrc htyp hS
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case quant tm typedKind typedName typedAnnotation typedTrigger typedBody =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvA hann
      elim_err h with EnvI htrigger
      obtain ⟨hsrcAnn, hsrcTr, hsrcBody⟩ := hsrc.of_quant
      simp only [LExpr.unresolved] at htyp
      obtain ⟨htypAnn, htypTr, htypBody⟩ := htyp.of_quant
      have hSA := hbinder annotation (some tm.type) Env EnvA hann haw hsrcAnn htypAnn hS
      have hawA : TContext.AliasesWF EnvA.context :=
        (linkBinderAnnot_context_absorbs C _ _ _ _ hann).1 ▸ haw
      have hSI := ihTrigger typedTrigger EnvA EnvI htrigger hawA hsrcTr htypTr hSA
      exact ihBody typedBody EnvI Env' h (hctx _ _ _ _ htrigger ▸ hawA) hsrcBody htypBody hSI
  | app sm fn arg ihFn ihArg =>
    intro typed Env Env' h haw hsrc htyp hS
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case app tm typedFn typedArg =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvI hfn
      obtain ⟨hsrc1, hsrc2⟩ := hsrc.of_app
      simp only [LExpr.unresolved] at htyp
      obtain ⟨htyp1, htyp2⟩ := htyp.of_app
      exact ihArg typedArg EnvI Env' h (hctx _ _ _ _ hfn ▸ haw) hsrc2 htyp2
        (ihFn typedFn Env EnvI hfn haw hsrc1 htyp1 hS)
  | ite sm cond thenBranch elseBranch ihCond ihThen ihElse =>
    intro typed Env Env' h haw hsrc htyp hS
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case ite tm typedCond typedThen typedElse =>
      simp only [bind, Except.bind] at h
      elim_err h with Env₁ hcond
      elim_err h with Env₂ hthen
      obtain ⟨hsrc1, hsrc2, hsrc3⟩ := hsrc.of_ite
      simp only [LExpr.unresolved] at htyp
      obtain ⟨htyp1, htyp2, htyp3⟩ := htyp.of_ite
      have haw₁ : TContext.AliasesWF Env₁.context := hctx _ _ _ _ hcond ▸ haw
      have hS₁ := ihCond typedCond Env Env₁ hcond haw hsrc1 htyp1 hS
      have hS₂ := ihThen typedThen Env₁ Env₂ hthen haw₁ hsrc2 htyp2 hS₁
      exact ihElse typedElse Env₂ Env' h (hctx _ _ _ _ hthen ▸ haw₁) hsrc3 htyp3 hS₂
  | eq sm lhs rhs ihLhs ihRhs =>
    intro typed Env Env' h haw hsrc htyp hS
    cases typed <;> try simp only [linkFVarAnnotations, reduceCtorEq] at h
    case eq tm typedLhs typedRhs =>
      simp only [bind, Except.bind] at h
      elim_err h with EnvI hlhs
      obtain ⟨hsrc1, hsrc2⟩ := hsrc.of_eq
      simp only [LExpr.unresolved] at htyp
      obtain ⟨htyp1, htyp2⟩ := htyp.of_eq
      exact ihRhs typedRhs EnvI Env' h (hctx _ _ _ _ hlhs ▸ haw) hsrc2 htyp2
        (ihLhs typedLhs Env EnvI hlhs haw hsrc1 htyp1 hS)

/-- Core source resolution keeps an environment avoiding `ps` and reports a type avoiding `ps`,
    when `ps` holds no generated name and the source's annotations avoid `ps`. -/
theorem resolve_varsAvoid {ps : List TyIdentifier}
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env'))
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env) (hne : Env.context.types ≠ [])
    (hfac : FactorySigWF C.functions) (hgen : NoGenName ps)
    (hsrc : LExpr.AnnotsAvoid source ps) (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Env' ps ∧ ∀ v ∈ LMonoTy.freeVars typed.toLMonoTy, v ∉ ps := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' source typed h
  obtain ⟨hSR, hty, hann⟩ :=
    Lambda.resolve_varsAvoid source typed C Env EnvR hresolve hwf hfac hgen hE
  have hctxR := LExpr.resolve_context_equiv_of_ne source typed C Env EnvR hresolve hne
  have hctx' := (linkFVarAnnotations_properties C source typed EnvR Env' hlink).context
  refine ⟨⟨linkFVarAnnotations_varsAvoid C source typed EnvR Env' hlink
    (hctxR.symm.aliasesWF hwf.aliasesWF) hsrc hann hSR, ?_⟩, hty⟩
  rw [hctx']
  exact hE.2.of_equiv hctxR

/-- Resolving source expressions keeps an environment avoiding `ps` and reports types avoiding
    `ps`, when `ps` holds no generated name and the sources' annotations avoid `ps`. -/
theorem resolves_varsAvoid {ps : List TyIdentifier}
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (es : List Expression.Expr) (typed : List (LExprT CoreLParams.mono))
    (h : resolves C Env es = .ok (typed, Env'))
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env) (hne : Env.context.types ≠ [])
    (hfac : FactorySigWF C.functions) (hgen : NoGenName ps)
    (hsrc : ∀ e ∈ es, LExpr.AnnotsAvoid e ps) (hE : TEnv.VarsAvoid Env ps) :
    TEnv.VarsAvoid Env' ps ∧ ∀ et ∈ typed, ∀ v ∈ LMonoTy.freeVars et.toLMonoTy, v ∉ ps := by
  induction es generalizing Env typed with
  | nil =>
    simp only [resolves, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hE, fun _ het => absurd het List.not_mem_nil⟩
  | cons e es ih =>
    simp only [resolves, bind, Except.bind] at h
    elim_err h with r1 h1
    obtain ⟨t1, E1⟩ := r1
    elim_err h with r2 h2
    obtain ⟨ts, E2⟩ := r2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hE1, hk1⟩ :=
      resolve_varsAvoid C Env E1 e t1 h1 hwf hne hfac hgen (hsrc e List.mem_cons_self) hE
    have hwf1 := resolve_TEnvWF C Env E1 e t1 h1 hwf hfac
    have hne1 := (resolve_context_equiv_of_ne C Env E1 e t1 h1 hne).symm.types_ne_nil hne
    obtain ⟨hE2, hks⟩ := ih E1 ts h2 hwf1 hne1
      (fun e' he' => hsrc e' (List.mem_cons_of_mem e he')) hE1
    refine ⟨hE2, fun et het => ?_⟩
    rcases List.mem_cons.mp het with rfl | het
    · exact hk1
    · exact hks et het

/-- Linking annotations keeps the substitution scopes below the newest one clear. -/
private theorem linkFVarAnnotations_tailClear (C : Expression.TyContext) :
    ∀ (source : Expression.Expr) (typed : LExprT CoreLParams.mono) (Env Env' : Expression.TyEnv),
      linkFVarAnnotations C source typed Env = .ok Env' →
      TailClear Env.stateSubstInfo.subst → TailClear Env'.stateSubstInfo.subst := by
  intro source typed Env Env' h
  refine (linkFVarAnnotations_preserves C
    (fun _ E E' => TailClear E.stateSubstInfo.subst → TailClear E'.stateSubstInfo.subst)
    (fun _ hS => hS) (fun _ _ _ _ _ h12 h23 hS => h23 (h12 hS)) ?_
    source typed Env Env' h).choose_spec.2
  intro _ ann annResolved _ _ E EI S hinst _ _ hunify hS
  have hEI : EI = E := LMonoTy.resolveAliases_env_eq ann E annResolved EI
    (LMonoTy.typeCheckSource_resolveAliases ann annResolved C E EI _ hinst)
  subst hEI
  exact Constraints.unify_tailClear hunify hS

/-- Core source resolution keeps the substitution scopes below the newest one clear. -/
theorem resolve_tailClear (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (h : resolve C Env e = .ok (et, Env'))
    (hS : TailClear Env.stateSubstInfo.subst) : TailClear Env'.stateSubstInfo.subst := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' e et h
  obtain ⟨Env0, etAux, h_res, -, -, -, h_subst0, -⟩ :=
    LExpr.resolve_resolveAux_init e et C Env EnvR hresolve
  have hR : TailClear EnvR.stateSubstInfo.subst :=
    LExpr.resolveAux_tailClear C e Env0 EnvR etAux h_res (h_subst0 ▸ hS)
  exact linkFVarAnnotations_tailClear C e et EnvR Env' hlink hR

/-- Core source resolution preserves every lookup and the aliases, even from an empty
    type-scope stack. -/
theorem resolve_context_FindEq
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    TContext.FindEq (T := CoreLParams) Env'.context Env.context := by
  cases htypes : Env.context.types with
  | nil =>
    have hctx : TContext.Equiv (T := CoreLParams) Env'.context
        { Env.context with types := [Strata.Util.HMap.empty] } :=
      resolve_context_of_empty C Env Env' source typed h htypes
    exact hctx.toFindEq.trans (TContext.FindEq.single_empty_of_nil htypes)
  | cons first rest =>
    exact (resolve_context_equiv_of_ne C Env Env' source typed h
      (htypes ▸ List.cons_ne_nil first rest)).toFindEq

/-- Core source resolution never decreases the type-variable generator. -/
theorem resolve_genState_tyGen_mono
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' source typed h
  exact Nat.le_trans
    (Lambda.resolve_genState_tyGen_mono source typed C Env EnvR hresolve)
    (linkFVarAnnotations_properties C source typed EnvR Env' hlink).tyGen

/-- Core source resolution extends the substitution produced by ordinary Lambda resolution. -/
theorem resolve_link_absorbs
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    ∃ EnvR,
      LExpr.resolve C Env source = .ok (typed, EnvR) ∧
      Subst.absorbs Env'.stateSubstInfo.subst EnvR.stateSubstInfo.subst := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' source typed h
  exact ⟨EnvR, hresolve,
    (linkFVarAnnotations_properties C source typed EnvR Env' hlink).absorbs⟩

/-- The annotation-linking phase never decreases the generator produced by Lambda resolution. -/
theorem resolve_link_genState_tyGen_mono
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    ∃ EnvR,
      LExpr.resolve C Env source = .ok (typed, EnvR) ∧
      EnvR.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' source typed h
  exact ⟨EnvR, hresolve,
    (linkFVarAnnotations_properties C source typed EnvR Env' hlink).tyGen⟩

/-- Empty source-expression list resolution returns the input environment. -/
theorem resolves_nil (C : Expression.TyContext) (Env : Expression.TyEnv) :
    resolves C Env [] = .ok ([], Env) := by rfl

/-- Nonempty source-expression list resolution exposes its left-to-right sequencing. -/
private theorem resolves_cons
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (e : Expression.Expr) (es : List Expression.Expr) :
    resolves C Env (e :: es) = (do
      let (headTyped, Env) ← resolve C Env e
      let (restTyped, Env) ← resolves C Env es
      .ok (headTyped :: restTyped, Env)) := rfl

/-- Resolving `e :: es` resolves `e`, then `es` from the resulting environment, and lists `e`'s
    result first. -/
theorem resolves_cons_inv {C : Expression.TyContext} {Env Env' : Expression.TyEnv}
    {e : Expression.Expr} {es : List Expression.Expr} {ets : List (LExprT CoreLParams.mono)}
    (h : resolves C Env (e :: es) = .ok (ets, Env')) :
    ∃ et Env1 etsR, resolve C Env e = .ok (et, Env1) ∧ resolves C Env1 es = .ok (etsR, Env') ∧
      ets = et :: etsR := by
  rw [resolves_cons] at h
  cases hr : resolve C Env e with
  | error err =>
    rw [hr] at h
    simp only [bind, Except.bind, reduceCtorEq] at h
  | ok r =>
    obtain ⟨et, Env1⟩ := r
    rw [hr] at h
    simp only [bind, Except.bind] at h
    cases hs : resolves C Env1 es with
    | error err =>
      rw [hs] at h
      simp only [reduceCtorEq] at h
    | ok r =>
      obtain ⟨etsR, Env2⟩ := r
      rw [hs] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨et, Env1, etsR, rfl, hs, rfl⟩

/-- Resolving a source expression keeps its literals. -/
theorem resolve_getConsts_eq (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (source : Expression.Expr) (typed : LExprT CoreLParams.mono)
    (h : resolve C Env source = .ok (typed, Env')) :
    LExpr.getConsts typed = LExpr.getConsts source := by
  obtain ⟨EnvR, hres, -⟩ := resolve_decompose C Env Env' source typed h
  have hconsts := Lambda.resolve_getConsts_eq C Env EnvR source typed hres []
  rw [Lambda.LExpr.Proofs.getConsts_unresolved,
    Lambda.LExpr.Proofs.getConsts_applySubstT] at hconsts
  exact hconsts

/-- Resolving a list of source expressions keeps the literals of each. -/
theorem resolves_getConsts_eq (C : Expression.TyContext) (Env : Expression.TyEnv) :
    ∀ (es : List Expression.Expr) (Env' : Expression.TyEnv)
      (ets : List (LExprT CoreLParams.mono)),
      resolves C Env es = .ok (ets, Env') →
      List.Rel₂ (fun t e => LExpr.getConsts t = LExpr.getConsts e) ets es
  | [], Env', ets, h => by
    rw [resolves_nil] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Rel₂.nil
  | e :: es, Env', ets, h => by
    obtain ⟨et, Env1, etsR, hres, hrest, rfl⟩ := resolves_cons_inv h
    exact List.Rel₂.cons (resolve_getConsts_eq C Env Env1 e et hres)
      (resolves_getConsts_eq C Env1 es Env' etsR hrest)

/-- If resolving one expression preserves `I` and gives a result satisfying `Q`, resolving a
    list preserves `I` and returns one result per expression, each satisfying `Q`. -/
theorem resolves_preserves
    (C : Expression.TyContext) (I : Expression.TyEnv → Prop)
    (Q : LExprT CoreLParams.mono → Prop)
    (hstep : ∀ (E E' : Expression.TyEnv) (e : Expression.Expr) (et : LExprT CoreLParams.mono),
      resolve C E e = .ok (et, E') → I E → I E' ∧ Q et) :
    ∀ (Env Env' : Expression.TyEnv) (es : List Expression.Expr)
      (typed : List (LExprT CoreLParams.mono)),
      resolves C Env es = .ok (typed, Env') → I Env →
      I Env' ∧ typed.length = es.length ∧ ∀ et ∈ typed, Q et := by
  intro Env Env' es
  induction es generalizing Env with
  | nil =>
    intro typed h hI
    rw [resolves_nil] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hI, rfl, fun et het => absurd het List.not_mem_nil⟩
  | cons e rest ih =>
    intro typed h hI
    rw [resolves_cons] at h
    cases hhead : resolve C Env e with
    | error err =>
      rw [hhead] at h
      simp only [bind, Except.bind, reduceCtorEq] at h
    | ok result =>
      obtain ⟨et0, EnvI⟩ := result
      rw [hhead] at h
      simp only [bind, Except.bind] at h
      cases htail : resolves C EnvI rest with
      | error err =>
        rw [htail] at h
        simp only [reduceCtorEq] at h
      | ok result =>
        obtain ⟨typedRest, EnvR⟩ := result
        rw [htail] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hhd := hstep Env EnvI e et0 hhead hI
        have htl := ih EnvI typedRest htail hhd.1
        refine ⟨htl.1, ?_, ?_⟩
        · simp only [List.length_cons, htl.2.1]
        · intro et het
          rcases List.mem_cons.mp het with rfl | hrest
          · exact hhd.2
          · exact htl.2.2 et hrest

/-- Resolving source expressions preserves a nonempty type-scope stack. -/
theorem resolves_context_types_ne
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (es : List Expression.Expr) (typed : List (LExprT CoreLParams.mono))
    (h : resolves C Env es = .ok (typed, Env'))
    (hne : Env.context.types ≠ []) :
    Env'.context.types ≠ [] :=
  (resolves_preserves C (fun E => E.context.types ≠ []) (fun _ => True)
    (fun E E' e et hres _ => ⟨resolve_context_types_ne C E E' e et hres, trivial⟩)
    Env Env' es typed h hne).1

/-- Resolving a list of Core source expressions keeps the type scopes below the newest one
    equivalent and the aliases unchanged. -/
theorem resolves_context_pop_equiv
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (es : List Expression.Expr) (typed : List (LExprT CoreLParams.mono))
    (h : resolves C Env es = .ok (typed, Env')) :
    Strata.Util.HMaps.Equiv Env'.context.types.pop Env.context.types.pop ∧
      Env'.context.aliases = Env.context.aliases :=
  (resolves_preserves C
    (fun E => Strata.Util.HMaps.Equiv E.context.types.pop Env.context.types.pop ∧
      E.context.aliases = Env.context.aliases)
    (fun _ => True)
    (fun E E' e et hres hE =>
      ⟨⟨(resolve_context_pop_equiv C E E' e et hres).1.trans hE.1,
        (resolve_context_pop_equiv C E E' e et hres).2.trans hE.2⟩, trivial⟩)
    Env Env' es typed h ⟨Strata.Util.HMaps.Equiv.refl _, rfl⟩).1

/-- Source-expression list resolution never decreases the generated type-variable counter. -/
theorem resolves_genState_tyGen_mono
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (es : List Expression.Expr) (typed : List (LExprT CoreLParams.mono))
    (h : resolves C Env es = .ok (typed, Env')) :
    Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen :=
  (resolves_preserves C (fun E => Env.genEnv.genState.tyGen ≤ E.genEnv.genState.tyGen)
    (fun _ => True)
    (fun E E' e et hres hE =>
      ⟨Nat.le_trans hE (resolve_genState_tyGen_mono C E E' e et hres), trivial⟩)
    Env Env' es typed h (Nat.le_refl _)).1

/-- Source-expression list resolution preserves type-environment well-formedness. -/
theorem resolves_TEnvWF
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (es : List Expression.Expr) (typed : List (LExprT CoreLParams.mono))
    (h : resolves C Env es = .ok (typed, Env'))
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (hfac : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) Env' :=
  (resolves_preserves C (fun E => LExpr.TEnvWF (T := CoreLParams) E) (fun _ => True)
    (fun E E' e et hres hwfE => ⟨resolve_TEnvWF C E E' e et hres hwfE hfac, trivial⟩)
    Env Env' es typed h hwf).1

/-- Resolving a list of Core source expressions keeps the substitution scopes below the newest
    one clear. -/
theorem resolves_tailClear (C : Expression.TyContext) :
    ∀ (es : List Expression.Expr) (Env Env' : Expression.TyEnv)
      (ets : List (LExprT CoreLParams.mono)),
      resolves C Env es = .ok (ets, Env') →
      LExpr.TEnvWF (T := CoreLParams) Env → FactorySigWF C.functions →
      TailClear Env.stateSubstInfo.subst → TailClear Env'.stateSubstInfo.subst :=
  fun es Env Env' ets h hwf hfac hS =>
    (resolves_preserves C
      (fun E => LExpr.TEnvWF (T := CoreLParams) E ∧ TailClear E.stateSubstInfo.subst)
      (fun _ => True)
      (fun E E' e et hres hE =>
        ⟨⟨resolve_TEnvWF C E E' e et hres hE.1 hfac,
          resolve_tailClear C E E' e et hres hE.2⟩, trivial⟩)
      Env Env' es ets h ⟨hwf, hS⟩).1.2

/-- Resolving a list of expressions keeps the substitution's range registered and gives each a
    registered type, when function arrows, Booleans and literal types are registered. -/
private theorem resolves_TEnvWF_RangeKnown_tys_known
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (es : List Expression.Expr) (typed : List (LExprT CoreLParams.mono))
    (h : resolves C Env es = .ok (typed, Env'))
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (hfac : FactorySigWF C.functions)
    (harrow : C.knownTypes["arrow"]? = some 2)
    (hbool : C.knownTypes["bool"]? = some 0)
    (hlit : LExpr.LiteralTysKnown C)
    (hrange : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown Env'.stateSubstInfo.subst C.knownTypes ∧
      ∀ et ∈ typed, LMonoTy.knownInstance et.toLMonoTy C.knownTypes = true :=
  let res := resolves_preserves C
    (fun E => LExpr.TEnvWF (T := CoreLParams) E ∧
      Subst.RangeKnown E.stateSubstInfo.subst C.knownTypes)
    (fun et => LMonoTy.knownInstance et.toLMonoTy C.knownTypes = true)
    (fun E E' e et hres hE =>
      have hI := resolve_RangeKnown C E E' e et hres hE.1 hfac harrow hbool hlit hE.2
      ⟨⟨resolve_TEnvWF C E E' e et hres hE.1 hfac, hI.1⟩, hI.2⟩)
    Env Env' es typed h ⟨hwf, hrange⟩
  ⟨res.1.2, res.2.2⟩

end SourceExpr

/-- A successful expected-type resolution is an expression resolution, one unification and a
    substitution update. -/
private theorem resolveWithType_decompose
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env')) :
    ∃ EnvR S,
      SourceExpr.resolve C Env e = .ok (et, EnvR)
      ∧ Constraints.unify [(et.toLMonoTy, mty)] EnvR.stateSubstInfo = .ok S
      ∧ Env' = EnvR.updateSubst S := by
  unfold resolveWithType at h
  simp only [bind, Except.bind] at h
  elim_err h with result hresolve
  obtain ⟨etR, EnvR⟩ := result
  elim_err h with S hunify
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨EnvR, S, Except.mapError_ok_h' hresolve, Except.mapError_ok_h' hunify, rfl⟩

/-- Expected-type resolution starts with a Lambda resolution whose substitution the final one
    absorbs, and the final substitution equates the resolved and expected types. -/
private theorem resolveWithType_resolve_solved
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env')) :
    ∃ EnvDirect, LExpr.resolve C Env e = .ok (et, EnvDirect) ∧
      Subst.absorbs Env'.stateSubstInfo.subst EnvDirect.stateSubstInfo.subst ∧
      LMonoTy.subst Env'.stateSubstInfo.subst et.toLMonoTy =
        LMonoTy.subst Env'.stateSubstInfo.subst mty := by
  obtain ⟨EnvR, S, hsource, hunify, rfl⟩ := resolveWithType_decompose C Env Env' e et mty h
  obtain ⟨EnvDirect, hres, hlinkAbs⟩ := SourceExpr.resolve_link_absorbs C Env EnvR e et hsource
  exact ⟨EnvDirect, hres,
    Subst.absorbs_trans _ _ _ hlinkAbs (Constraints.unify_absorbs _ _ _ hunify),
    Constraints.unify_sound _ _ _ hunify (et.toLMonoTy, mty) List.mem_cons_self⟩

/-- Against a type with no free variables, expected-type resolution starts with a Lambda
    resolution, and every substitution absorbing the final one absorbs that resolution's
    substitution and sends the resolved type to the expected type. -/
private theorem resolveWithType_ground_solved
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (h_ground : LMonoTy.freeVars mty = []) :
    ∃ EnvDirect, LExpr.resolve C Env e = .ok (et, EnvDirect) ∧
      ∀ S : Subst, Subst.absorbs S Env'.stateSubstInfo.subst →
        Subst.absorbs S EnvDirect.stateSubstInfo.subst ∧
          LMonoTy.subst S et.toLMonoTy = mty := by
  obtain ⟨EnvDirect, hres, hAbs, hsolved⟩ :=
    resolveWithType_resolve_solved C Env Env' e et mty h
  have hfix : ∀ S : Subst, LMonoTy.subst S mty = mty := by
    intro S
    apply LMonoTy.subst_no_relevant_keys
    intro x hx
    rw [h_ground] at hx
    exact absurd hx List.not_mem_nil
  refine ⟨EnvDirect, hres, fun S hS => ⟨Subst.absorbs_trans _ _ _ hAbs hS, ?_⟩⟩
  exact (LMonoTy.subst_eq_of_absorbs S Env'.stateSubstInfo.subst et.toLMonoTy mty hS
    hsolved).trans (hfix S)

/-- If `resolveWithType` succeeds against a type with no free type variables, the source
    expression has that type under polymorphic typing. -/
theorem resolveWithType_HasType_ground
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (h_ground : LMonoTy.freeVars mty = [])
    (h_envwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactorySigWF C.functions)
    (h_ws : LExpr.WellScoped e Env.context)
    (h_mono : MonoScope Env.context) :
    LExpr.HasType C (TContext.subst Env.context Env'.stateSubstInfo.subst) e
      (.forAll [] mty) := by
  obtain ⟨EnvR, hres, hsolve⟩ := resolveWithType_ground_solved C Env Env' e et mty h h_ground
  obtain ⟨h_absR, h_solved⟩ := hsolve _ (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)
  have h_pkf : LExpr.Subst.polyKeysFresh (T := CoreLParams) Env'.stateSubstInfo.subst
      Env.context :=
    polyKeysFresh_of_MonoScope (T := CoreLParams) _ Env.context h_mono
  have hcore := LExpr.resolve_HasType_core (T := CoreLParams) e et C Env EnvR hres
    h_envwf h_fwf h_ws
  have h_ty := hcore.1 _ h_absR Env'.stateSubstInfo.isWF h_pkf e (LExpr.AnnotFits.refl _ _ _ e _)
  rw [h_solved] at h_ty
  exact h_ty

/-- If `resolveWithType` succeeds at `bool`, the source expression has type `bool` under
    polymorphic typing. -/
theorem resolveWithType_HasType_bool
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono)
    (h : resolveWithType C Env e LMonoTy.bool = .ok (et, Env'))
    (h_envwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactorySigWF C.functions)
    (h_ws : LExpr.WellScoped e Env.context)
    (h_mono : MonoScope Env.context) :
    LExpr.HasType C (TContext.subst Env.context Env'.stateSubstInfo.subst) e
      (.forAll [] LMonoTy.bool) :=
  resolveWithType_HasType_ground C Env Env' e et LMonoTy.bool h rfl h_envwf h_fwf h_ws h_mono

/-- Resolving against a ground expected type preserves environment well-formedness. -/
theorem resolveWithType_TEnvWF_ground
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (h_ground : LMonoTy.freeVars mty = [])
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) Env' := by
  obtain ⟨EnvR, S, hresolve, hunify, rfl⟩ :=
    resolveWithType_decompose C Env Env' e et mty h
  have h_res : LExpr.TEnvWF (T := CoreLParams) EnvR :=
    SourceExpr.resolve_TEnvWF C Env EnvR e et hresolve h_env h_fac
  obtain ⟨EnvDirect, hresolveDirect, hlinkGen⟩ :=
    SourceExpr.resolve_link_genState_tyGen_mono C Env EnvR e et hresolve
  have h_et_fresh :=
    resolve_result_type_fresh C Env EnvDirect e et hresolveDirect h_env h_fac
  have h_constraints : ∀ v,
      v ∈ Constraints.freeVars [(et.toLMonoTy, mty)] →
      ∀ n, n ≥ EnvR.genEnv.genState.tyGen →
        v ≠ TState.tyPrefix ++ toString n := by
    intro v hv
    simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil] at hv
    rw [h_ground, List.append_nil] at hv
    intro n hn
    exact h_et_fresh v hv n (Nat.le_trans hlinkGen hn)
  exact LExpr.TEnvWF_updateSubst_of_unify (T := CoreLParams) EnvR
    [(et.toLMonoTy, mty)] S h_res hunify h_constraints

/-- Expected-type resolution absorbs the incoming substitution. -/
theorem resolveWithType_absorbs
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  obtain ⟨EnvR, S, hresolve, hunify, rfl⟩ :=
    resolveWithType_decompose C Env Env' e et mty h
  obtain ⟨EnvDirect, hresolveDirect, hlinkAbs⟩ :=
    SourceExpr.resolve_link_absorbs C Env EnvR e et hresolve
  have hsourceAbs :
      Subst.absorbs EnvR.stateSubstInfo.subst Env.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _
      (resolve_absorbs C Env EnvDirect e et hresolveDirect h_env h_fac)
      hlinkAbs
  exact Subst.absorbs_trans _ _ _
    hsourceAbs
    (Constraints.unify_absorbs _ _ _ hunify)

/-- Expected-type resolution never decreases the type-variable generator counter. -/
theorem resolveWithType_genState_tyGen_mono
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env')) :
    Env.genEnv.genState.tyGen ≤ Env'.genEnv.genState.tyGen := by
  obtain ⟨EnvR, S, hresolve, -, rfl⟩ :=
    resolveWithType_decompose C Env Env' e et mty h
  simpa only [TEnv.updateSubst] using
    SourceExpr.resolve_genState_tyGen_mono C Env EnvR e et hresolve

/-- Expected-type resolution keeps the substitution's range registered when function arrows,
    Booleans, literal types and the expected type are registered. -/
theorem resolveWithType_RangeKnown
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (hwf : LExpr.TEnvWF (T := CoreLParams) Env) (hfac : FactorySigWF C.functions)
    (harrow : C.knownTypes["arrow"]? = some 2) (hbool : C.knownTypes["bool"]? = some 0)
    (hlit : LExpr.LiteralTysKnown C)
    (hmty : LMonoTy.knownInstance mty C.knownTypes = true)
    (hrange : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown Env'.stateSubstInfo.subst C.knownTypes := by
  obtain ⟨EnvR, S, hresolve, hunify, rfl⟩ :=
    resolveWithType_decompose C Env Env' e et mty h
  obtain ⟨hrangeR, hkn⟩ := SourceExpr.resolve_RangeKnown C Env EnvR e et hresolve hwf hfac
    harrow hbool hlit hrange
  have hcs : Constraints.Known [(et.toLMonoTy, mty)] C.knownTypes := by
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact ⟨hkn, hmty⟩
  simpa only [TEnv.updateSubst] using
    Constraints.unify_RangeKnown C.knownTypes _ _ _ hunify hrangeR hcs

/-- Under a substitution `S` absorbing the resolver's, the output of `LExpr.resolve` agrees with
    the alias-resolved input scope under `S` and a table whose signatures name no input alias. -/
theorem resolve_annotAgree
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context) (h_sigs : FactorySigsFixed Env.context.aliases C.functions)
    (S : Subst) (h_abs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    TypeSpec.ScopesAnnotAgree C (TContext.subst Env.context.resolveTypes S).types
      (LExpr.unresolved (LExpr.applySubstT et S)) := by
  refine ⟨fun x ann hx => ?_, fun o ty ho => ?_, ?_⟩
  · obtain ⟨ty, hfind, rfl⟩ :=
      resolve_fvarAnnots_agree C Env Env' e et h h_env h_fac h_mono S h_abs x ann hx
    exact TContext_types_subst_find _ S x _ hfind
  · obtain ⟨f, xs, body, hf, hty, τ, rfl⟩ :=
      resolve_opAnnots C Env Env' e et h h_env h_fac S o ty ho
    refine ⟨f, xs, body, hf, hty, τ, ?_⟩
    rw [h_sigs.resolveTy_body (T := CoreLParams) (Factory.getElem?_is_some_implies_mem hf) hty]
  · exact resolve_getOps_mem C Env Env' e et h h_env h_fac S

/-- Under any substitution `S` absorbing the final one, the output of `resolveWithType` agrees
    with the alias-resolved input scope under `S` and a table whose signatures name no input
    alias. -/
theorem resolveWithType_annotAgree
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context) (h_sigs : FactorySigsFixed Env.context.aliases C.functions)
    (S : Subst) (h_abs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    TypeSpec.ScopesAnnotAgree C (TContext.subst Env.context.resolveTypes S).types
      (LExpr.unresolved (LExpr.applySubstT et S)) := by
  obtain ⟨EnvDirect, hres, hAbs, -⟩ := resolveWithType_resolve_solved C Env Env' e et mty h
  exact resolve_annotAgree C Env EnvDirect e et hres h_env h_fac h_mono h_sigs S
    (Subst.absorbs_trans _ _ _ hAbs h_abs)

/-- When `resolveWithType` succeeds, every free-variable annotation of the expression is a valid
    source type against the starting aliases and uses no reserved type-variable name. -/
theorem resolveWithType_fvarAnnotsWF
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env')) :
    TypeSpec.FVarAnnotsWF C TyVarAdmissibility.notGeneratedOrRigid
      Env.context.aliases e := by
  obtain ⟨EnvR, S, hsource, -, -⟩ := resolveWithType_decompose C Env Env' e et mty h
  exact SourceExpr.resolve_fvarAnnotsWF C Env EnvR e et hsource

/-- When `resolveWithType` succeeds, no binder annotation of the expression names a generated or
    rigid type variable. -/
theorem resolveWithType_binderAnnotTyVarsAdmissible
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env')) :
    TypeSpec.BinderAnnotTyVarsAdmissible TyVarAdmissibility.notGeneratedOrRigid e := by
  obtain ⟨EnvR, S, hsource, -, -⟩ := resolveWithType_decompose C Env Env' e et mty h
  exact SourceExpr.resolve_binderAnnotTyVarsAdmissible C Env EnvR e et hsource

/-- Resolution against an expected type accepts only expressions whose free variables are all
    declared in the input context. -/
theorem resolveWithType_WellScoped
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env')) :
    LExpr.WellScoped e Env.context := by
  obtain ⟨EnvR, S, hsource, -, -⟩ := resolveWithType_decompose C Env Env' e et mty h
  exact SourceExpr.resolve_WellScoped C Env EnvR e et hsource

/-! ### Resolving against an expected type -/

/-- If an expression is not a free variable, neither is its resolved form after substituting and
    deskolemizing its annotations. -/
private theorem resolveWithType_stored_ne_fvar_of_ne_fvar
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (e : Expression.Expr) (expected : LMonoTy) (et : LExprT CoreLParams.mono)
    (h : resolveWithType C Env e expected = .ok (et, Env'))
    (hn : ∀ mid x ann, e ≠ .fvar mid x ann) (σ : RigidNames) (S : Subst) :
    ∀ mid x ann,
      finishDeskolemized σ S et ≠ .fvar mid x ann := by
  unfold finishDeskolemized
  have hresolve : ∃ EnvR, LExpr.resolve C Env e = .ok (et, EnvR) := by
    unfold resolveWithType at h
    simp only [bind, Except.bind] at h
    elim_err h with v hmapres
    obtain ⟨etR, EnvR⟩ := v
    elim_err h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨het, -⟩ := h
    subst het
    have hsource : SourceExpr.resolve C Env e = .ok (etR, EnvR) :=
      Except.mapError_ok_h' hmapres
    obtain ⟨EnvDirect, hdirect, -⟩ :=
      SourceExpr.resolve_decompose C Env EnvR e etR hsource
    exact ⟨EnvDirect, hdirect⟩
  obtain ⟨EnvR, hresolve⟩ := hresolve
  unfold LExpr.resolve at hresolve
  simp only [bind, Except.bind] at hresolve
  split at hresolve
  · exact absurd hresolve (by simp)
  · rename_i resolved haux
    obtain ⟨et0, Env0⟩ := resolved
    simp only [Except.ok.injEq, Prod.mk.injEq] at hresolve
    obtain ⟨het, -⟩ := hresolve
    subst het
    cases e
    case fvar mid x ann =>
      exact absurd rfl (hn mid x ann)
    all_goals
      simp only [LExpr.resolveAux, bind, Except.bind] at haux <;>
      repeat' (split at haux <;>
        try simp only [reduceCtorEq] at haux)
    all_goals
      try simp only [reduceCtorEq] at haux
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at haux
      obtain ⟨het0, -⟩ := haux
      subst het0
      simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, implies_true, LExpr.applySubstT,
          LExpr.replaceMetadata, LExpr.unresolved]
    all_goals
      intro mid x ann heq
      repeat' split at heq
      all_goals simp [LExpr.replaceUserProvidedType] at heq

/-- Resolving a free variable against any expected type gives an annotated free variable of the
    same name. -/
private theorem resolveWithType_fvar_shape
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (m : CoreLParams.Metadata) (x : CoreIdent) (ann : Option LMonoTy) (expected : LMonoTy)
    (et : LExprT CoreLParams.mono)
    (h : resolveWithType C Env (.fvar m x ann) expected = .ok (et, Env')) :
    ∃ md ty, et = .fvar md x (some ty) := by
  obtain ⟨EnvDirect, hresolve, -⟩ := resolveWithType_resolve_solved C Env Env' _ et expected h
  unfold LExpr.resolve at hresolve
  simp only [bind, Except.bind] at hresolve
  split at hresolve
  · exact absurd hresolve (by simp)
  · rename_i resolved haux
    obtain ⟨et0, Env0⟩ := resolved
    simp only [Except.ok.injEq, Prod.mk.injEq] at hresolve
    obtain ⟨het, -⟩ := hresolve
    subst het
    obtain ⟨ty, -, rfl⟩ := LExpr.resolveAux_fvar_shape C _ _ m x ann _ haux
    exact ⟨_, _, rfl⟩

/-- Resolving at `bool` in a fresh substitution scope preserves environment well-formedness once
    that scope is popped. -/
private theorem resolveWithType_pop_TEnvWF
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (h : resolveWithType C Env.pushEmptySubstScope e LMonoTy.bool = .ok (et, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) Env'.popSubstScope := by
  have h_push : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env h_env
  exact popSubstScope_preserves_TEnvWF (T := CoreLParams) Env'
    (resolveWithType_TEnvWF_ground C Env.pushEmptySubstScope Env' e et LMonoTy.bool h
      rfl h_push h_fac)

/-- Resolving against a ground expected type gives an elaborated expression annotation-consistent
    at that type under every substitution absorbing the final one. -/
theorem resolveWithType_HasTypeA_ground_absorbing
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (h_ground : LMonoTy.freeVars mty = [])
    (h_envwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (S : Subst) (h_abs : Subst.absorbs S Env'.stateSubstInfo.subst) :
    LExpr.HasTypeA [] (LExpr.unresolved (LExpr.applySubstT et S)) mty := by
  obtain ⟨EnvR, hres, hsolve⟩ := resolveWithType_ground_solved C Env Env' e et mty h h_ground
  obtain ⟨h_absR, h_solved⟩ := hsolve S h_abs
  have hA := resolve_HasTypeA_subst e et C Env EnvR hres h_envwf h_fwf h_resolved S h_absR
  rw [LExpr.applySubstT_toLMonoTy, h_solved] at hA
  exact hA

/-- If `resolveWithType` succeeds against a ground expected type, the elaborated expression with
    the final substitution applied is annotation-consistent at that type. -/
private theorem resolveWithType_HasTypeA_ground
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (h_ground : LMonoTy.freeVars mty = [])
    (h_envwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    LExpr.HasTypeA [] (LExpr.unresolved (LExpr.applySubstT et Env'.stateSubstInfo.subst))
      mty :=
  resolveWithType_HasTypeA_ground_absorbing C Env Env' e et mty h h_ground h_envwf h_fwf
    h_resolved _ (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)

/-- Expected-type resolution keeps the constants of its input, under any type substitution. -/
private theorem resolveWithType_getConsts_eq
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env')) (S : Subst) :
    LExpr.getConsts (LExpr.unresolved (LExpr.applySubstT et S)) = LExpr.getConsts e := by
  obtain ⟨EnvDirect, hres, -, -⟩ := resolveWithType_resolve_solved C Env Env' e et mty h
  exact Lambda.resolve_getConsts_eq C Env EnvDirect e et hres S

/-- Literals of an expression that resolves successfully keep types fixed by deskolemization in
    its elaboration under any type substitution. -/
theorem ConstTysFixed_resolveWithType {σ : RigidNames}
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env')) (S : Subst)
    (hc : ConstTysFixed σ e) :
    ConstTysFixed σ (LExpr.unresolved (LExpr.applySubstT et S)) := by
  intro c hmem
  rw [resolveWithType_getConsts_eq C Env Env' e et mty h S] at hmem
  exact hc c hmem

/-- If `resolveWithType` succeeds at `bool`, the elaborated expression with the final substitution
    applied is annotation-consistent at `bool`. -/
theorem resolveWithType_HasTypeA_bool
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono)
    (h : resolveWithType C Env e LMonoTy.bool = .ok (et, Env'))
    (h_envwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    LExpr.HasTypeA [] (LExpr.unresolved (LExpr.applySubstT et Env'.stateSubstInfo.subst))
      LMonoTy.bool :=
  resolveWithType_HasTypeA_ground C Env Env' e et LMonoTy.bool h rfl h_envwf h_fwf h_resolved

/-- After expected-type resolution, every binder annotation of the elaborated expression is
    registered under any substitution absorbing the final one whose range is registered. -/
theorem resolveWithType_binderAnnotations_known_absorbing
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (h_envwf : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactorySigWF C.functions)
    (S : Subst) (h_abs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (h_range : Subst.RangeKnown S C.knownTypes) :
    ∀ t ∈ LExpr.binderAnnotations (LExpr.unresolved (LExpr.applySubstT et S)),
      t.knownInstance C.knownTypes = true := by
  obtain ⟨EnvR, Su, hsource, hunify, rfl⟩ := resolveWithType_decompose C Env Env' e et mty h
  obtain ⟨EnvDirect, hres, hlinkAbs⟩ := SourceExpr.resolve_link_absorbs C Env EnvR e et hsource
  have h_outer : Subst.absorbs S EnvR.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ (Constraints.unify_absorbs _ _ _ hunify) h_abs
  exact resolve_binderAnnotations_known C Env EnvDirect e et hres h_envwf h_fwf S
    (Subst.absorbs_trans _ _ _ hlinkAbs h_outer) h_range

/-- After expected-type resolution against a registered type, every binder annotation of the
    elaborated expression is registered under the final substitution, when arrows, Booleans,
    literal types and the incoming substitution's range are registered. -/
theorem resolveWithType_binderAnnotations_known
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Core.Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (h : resolveWithType C Env e mty = .ok (et, Env'))
    (h_envwf : LExpr.TEnvWF (T := CoreLParams) Env) (h_fwf : FactorySigWF C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2) (h_bool : C.knownTypes["bool"]? = some 0)
    (h_lit : LExpr.LiteralTysKnown C)
    (h_mty : LMonoTy.knownInstance mty C.knownTypes = true)
    (h_range : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    ∀ t ∈ LExpr.binderAnnotations
        (LExpr.unresolved (LExpr.applySubstT et Env'.stateSubstInfo.subst)),
      t.knownInstance C.knownTypes = true :=
  resolveWithType_binderAnnotations_known_absorbing C Env Env' e et mty h h_envwf h_fwf _
    (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)
    (resolveWithType_RangeKnown C Env Env' e et mty h h_envwf h_fwf h_arrow h_bool
      h_lit h_mty h_range)

/-! ## Annotations read through the solved substitution -/

/-- Every free variable of `u` substituted by `restrictTo g t` is free in `g v` for some free
    variable `v` of `u`, when `u`'s free variables are among `t`'s. -/
private theorem freeVars_subst_restrictTo (g : TyIdentifier → LMonoTy) (t : LMonoTy) :
    ∀ u : LMonoTy, (∀ v ∈ LMonoTy.freeVars u, v ∈ LMonoTy.freeVars t) →
      ∀ x ∈ LMonoTy.freeVars (LMonoTy.subst [restrictTo g t] u),
        ∃ v ∈ LMonoTy.freeVars u, x ∈ LMonoTy.freeVars (g v) := by
  intro u
  induction u with
  | ftvar y =>
    intro hsub x hx
    have hy : y ∈ LMonoTy.freeVars t := hsub y (List.mem_singleton.mpr rfl)
    rw [restrictTo_ftvar g t y hy] at hx
    exact ⟨y, List.mem_singleton.mpr rfl, hx⟩
  | bitvec n =>
    intro _ x hx
    rw [LMonoTy.subst_bitvec] at hx
    simp only [LMonoTy.freeVars, List.not_mem_nil] at hx
  | tcons name args ih =>
    intro hsub x hx
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map, LMonoTy.freeVars] at hx
    obtain ⟨a', ha', hxa⟩ := LMonoTys.freeVars_exists hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨v, hv, hxv⟩ :=
      ih a ha (fun v hv => hsub v (LMonoTys.freeVars_mem_subset ha hv)) x hxa
    exact ⟨v, LMonoTys.freeVars_mem_subset ha hv, hxv⟩

/-- Every free type variable of a read annotation is free in the annotation or in a type `Δ`
    binds. -/
theorem freeVars_instAnnotTy (Δ : TypeSpec.WrittenEnv) (t : LMonoTy) :
    ∀ x ∈ LMonoTy.freeVars (TypeSpec.instAnnotTy Δ t),
      x ∈ LMonoTy.freeVars t ∨ ∃ v u, Δ v = some u ∧ x ∈ LMonoTy.freeVars u := by
  intro x hx
  rw [instAnnotTy_eq] at hx
  obtain ⟨v, hv, hxv⟩ := freeVars_subst_restrictTo _ t t (fun v hv => hv) x hx
  unfold readTyVar at hxv
  split at hxv
  · cases hΔ : Δ v with
    | none =>
      rw [hΔ, Option.getD_none] at hxv
      simp only [LMonoTy.freeVars, List.mem_singleton] at hxv
      subst hxv
      exact Or.inl hv
    | some u =>
      rw [hΔ, Option.getD_some] at hxv
      exact Or.inr ⟨v, u, hΔ, hxv⟩
  · simp only [LMonoTy.freeVars, List.mem_singleton] at hxv
    subst hxv
    exact Or.inl hv

/-! ### Annotations read through every name's image under a substitution -/

/-- For a well-formed `S`, an annotation read through `S` and then substituted by `S` equals the
    annotation substituted by `S`. -/
private theorem subst_instAnnotTy_substEnv {S : Subst} (hwf : SubstWF S) (t : LMonoTy) :
    LMonoTy.subst S (TypeSpec.instAnnotTy (substEnv S) t) = LMonoTy.subst S t := by
  rw [instAnnotTy_eq]
  refine LMonoTy.subst_subst_of_pointwise [restrictTo (readTyVar (substEnv S)) t] S S t ?_
  intro v hv
  symm
  rw [restrictTo_ftvar _ t v hv]
  unfold readTyVar
  split
  · simp only [substEnv, Option.getD_some]
    exact (LMonoTy.subst_idempotent S hwf (.ftvar v)).symm
  · rfl

/-- `restrictTo` of `S`'s images on `t` acts on `t` as `S` does. -/
private theorem subst_restrictTo_subst (S : Subst) (t : LMonoTy) :
    LMonoTy.subst [restrictTo (fun w => LMonoTy.subst S (.ftvar w)) t] t = LMonoTy.subst S t := by
  apply agree_on_freeVars_implies_subst_eq
  intro v hv
  exact restrictTo_ftvar _ t v hv

/-- An annotation read through a well-formed `S` is compatible with every type alias-equivalent to
    its substitution by `S`. -/
private theorem annotCompat_instAnnotTy_substEnv {S : Subst} (hwf : SubstWF S)
    {aliases : List TypeAlias} {t x : LMonoTy}
    (h : AliasEquiv aliases (LMonoTy.subst S t) x) :
    LExpr.AnnotCompat aliases (TypeSpec.instAnnotTy (substEnv S) t) x := by
  refine ⟨restrictTo (fun w => LMonoTy.subst S (.ftvar w)) (TypeSpec.instAnnotTy (substEnv S) t),
    ?_⟩
  rw [subst_restrictTo_subst, subst_instAnnotTy_substEnv hwf]
  exact h

/-- An annotation read through a well-formed `S` is a valid source type, with every type
    variable allowed, when its substitution by `S` is. -/
private theorem sourceTyWF_instAnnotTy_substEnv {C : Expression.TyContext} {S : Subst}
    (hwf : SubstWF S) {aliases : List TypeAlias} {t : LMonoTy}
    (h : ∃ r, SourceTyWF C TyVarAdmissibility.all aliases (LMonoTy.subst S t) r) :
    ∃ r, SourceTyWF C TyVarAdmissibility.all aliases
      (TypeSpec.instAnnotTy (substEnv S) t) r := by
  obtain ⟨r, hr⟩ := h
  refine SourceTyWF.of_subst [restrictTo (fun w => LMonoTy.subst S (.ftvar w))
    (TypeSpec.instAnnotTy (substEnv S) t)] (r' := r) ?_
  rw [subst_restrictTo_subst, subst_instAnnotTy_substEnv hwf]
  exact hr

namespace SourceExpr

/-- After linking an annotation to an inferred type, the annotation read through any well-formed
    `S` absorbing the result is compatible with the type under `S`, and a valid source type when
    the type under `S` is registered. -/
private theorem linkAnnot_readFits (C : Expression.TyContext) (binder : Bool) (ann ty : LMonoTy)
    (Env Env' : Expression.TyEnv) (h : linkAnnot C binder ann ty Env = .ok Env')
    (haw : TContext.AliasesWF Env.context)
    (hfresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (S : Subst) (habs : Subst.absorbs S Env'.stateSubstInfo.subst) (hwf : SubstWF S) :
    LExpr.AnnotCompat Env.context.aliases (TypeSpec.instAnnotTy (substEnv S) ann)
        (LMonoTy.subst S ty) ∧
      (LMonoTy.knownInstance (LMonoTy.subst S ty) C.knownTypes = true →
        ∃ r, SourceTyWF C TyVarAdmissibility.all Env.context.aliases
          (TypeSpec.instAnnotTy (substEnv S) ann) r) := by
  obtain ⟨annResolved, EI, -, S', hinst, -, -, hunify, rfl⟩ :=
    linkAnnot_inv C binder ann ty Env Env' h
  have hres := LMonoTy.typeCheckSource_resolveAliases ann annResolved C Env EI _ hinst
  have hEI : EI = Env := LMonoTy.resolveAliases_env_eq ann Env annResolved EI hres
  subst hEI
  have hae : AliasEquiv EI.context.aliases ann annResolved :=
    LExpr.resolveAliases_aliasEquiv (Γ := EI.context) ann EI annResolved EI hres rfl
  have heq : LMonoTy.subst S annResolved = LMonoTy.subst S ty := by
    have hS' : Subst.absorbs S S'.subst := habs
    cases binder
    · have h1 := LExpr.unify_makes_equal annResolved ty _ _ hunify
      rw [← LMonoTy.subst_absorbs S S'.subst _ hS', h1, LMonoTy.subst_absorbs S S'.subst _ hS']
    · have h1 := LExpr.unify_makes_equal ty annResolved _ _ hunify
      rw [← LMonoTy.subst_absorbs S S'.subst annResolved hS', ← h1,
        LMonoTy.subst_absorbs S S'.subst _ hS']
  have hSae : AliasEquiv EI.context.aliases (LMonoTy.subst S ann) (LMonoTy.subst S ty) := by
    have h1 := LExpr.AliasEquiv_subst _ ann annResolved S hae (fun a ha => haw a ha)
    rwa [heq] at h1
  refine ⟨annotCompat_instAnnotTy_substEnv hwf hSae, fun hkn => ?_⟩
  refine sourceTyWF_instAnnotTy_substEnv hwf ?_
  exact SourceTyWF.subst_of_resolves_knownInstance (fun a ha => haw a ha) hfresh S
    (LMonoTy.resolveAliases_sourceTyResolves ann EI annResolved EI hres) (heq ▸ hkn)

/-- The domain `arrowDomain?` reads off a type is the first component `isArrow` returns. -/
private theorem arrowDomain?_eq_isArrow (t : LMonoTy) :
    arrowDomain? t = t.isArrow.map Prod.fst := by
  unfold arrowDomain? LMonoTy.isArrow
  split <;> simp_all

/-- After linking a resolved expression's annotations, the expression with its annotations read
    through any well-formed `S` absorbing the result fits the typed result, provided the stored
    binder annotations under `S` are registered. -/
private theorem linkFVarAnnotations_readFits (C : Expression.TyContext) :
    ∀ (source : Expression.Expr) (typed : LExprT CoreLParams.mono) (Env Env' : Expression.TyEnv),
      linkFVarAnnotations C source typed Env = .ok Env' →
      TContext.AliasesWF Env.context →
      (∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false) →
      ∀ S : Subst, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
      TypeSpec.BinderAnnotsKnown C
        (LExpr.replaceUserProvidedType typed.unresolved (LMonoTy.subst S)) →
      LExpr.AnnotFits C Env.context.aliases S source typed
        (TypeSpec.instAnnots (substEnv S) source) := by
  intro source
  induction source with
  | const | op | bvar =>
    intro typed _ _ _ _ _ _ _ _ _
    cases typed <;> simp only [LExpr.AnnotFits, TypeSpec.instAnnots]
  | fvar sm x ann =>
    intro typed Env Env' h haw hfresh S habs hwf _
    cases ann with
    | none =>
      cases typed <;> simp only [LExpr.AnnotFits, TypeSpec.instAnnots, Option.map_none]
    | some a =>
      cases typed <;> simp only [linkFVarAnnotations, reduceCtorEq] at h
      rename_i tm y fty
      simp only [bind, Except.bind] at h
      split at h
      · obtain ⟨hcompat, -⟩ := linkAnnot_readFits C false a _ Env Env' h haw hfresh S habs hwf
        simp only [LExpr.AnnotFits, TypeSpec.instAnnots, Option.map_some]
        exact Or.inr ⟨_, rfl, hcompat⟩
      · exact absurd h (by simp)
  | abs sm sname sann body ih =>
    intro typed Env Env' h haw hfresh S habs hwf hknown
    cases typed <;> simp only [linkFVarAnnotations, reduceCtorEq] at h
    rename_i tm tname tann tbody
    simp only [bind, Except.bind] at h
    elim_err h with E1 h1
    obtain ⟨hctx1, -⟩ := linkBinderAnnot_context_absorbs C _ _ Env E1 h1
    have hprops := linkFVarAnnotations_properties C body tbody E1 Env' h
    have habs1 := Subst.absorbs_trans _ _ _ hprops.absorbs habs
    have hknownBody : TypeSpec.BinderAnnotsKnown C
        (LExpr.replaceUserProvidedType tbody.unresolved (LMonoTy.subst S)) := by
      intro t ht
      refine hknown t ?_
      simp only [LExpr.unresolved]
      split <;> simp only [LExpr.replaceUserProvidedType, LExpr.binderAnnotations,
        List.mem_append] <;> exact Or.inr ht
    have hbody := ih tbody E1 Env' h (hctx1 ▸ haw) (hctx1 ▸ hfresh) S habs hwf hknownBody
    rw [hctx1] at hbody
    simp only [LExpr.AnnotFits, TypeSpec.instAnnots]
    refine ⟨_, _, rfl, ?_, hbody⟩
    cases sann with
    | none => exact Or.inl rfl
    | some a =>
      refine Or.inr ⟨_, rfl, ?_⟩
      intro dty hd
      have hdom : arrowDomain? tm.type = some dty := by rw [arrowDomain?_eq_isArrow]; exact hd
      rw [hdom] at h1
      obtain ⟨hcompat, hvalid⟩ := linkAnnot_readFits C true a dty Env E1 h1 haw hfresh S habs1 hwf
      refine ⟨hcompat, hvalid ?_⟩
      refine hknown _ ?_
      obtain ⟨aty, cod, hiA⟩ : ∃ aty cod, tm.type.isArrow = some (aty, cod) := by
        cases hiA : tm.type.isArrow with
        | none => rw [hiA] at hd; cases hd
        | some p => exact ⟨p.1, p.2, rfl⟩
      rw [hiA, Option.map_some, Option.some.injEq] at hd
      subst hd
      simp only [LExpr.unresolved, hiA, LExpr.replaceUserProvidedType, LExpr.binderAnnotations,
        Option.map_some, Option.toList_some, List.mem_append, List.mem_singleton, true_or]
  | quant sm sk sname sann trig body iht ihb =>
    intro typed Env Env' h haw hfresh S habs hwf hknown
    cases typed <;> simp only [linkFVarAnnotations, reduceCtorEq] at h
    rename_i tm tk tname tann ttrig tbody
    simp only [bind, Except.bind] at h
    elim_err h with E1 h1
    elim_err h with E2 h2
    obtain ⟨hctx1, -⟩ := linkBinderAnnot_context_absorbs C _ _ Env E1 h1
    have hprops2 := linkFVarAnnotations_properties C trig ttrig E1 E2 h2
    have hprops := linkFVarAnnotations_properties C body tbody E2 Env' h
    have habs2 := Subst.absorbs_trans _ _ _ hprops.absorbs habs
    have habs1 := Subst.absorbs_trans _ _ _ hprops2.absorbs habs2
    have hctx2 : E2.context = Env.context := hprops2.context.trans hctx1
    simp only [TypeSpec.BinderAnnotsKnown, LExpr.unresolved, LExpr.replaceUserProvidedType,
      LExpr.binderAnnotations, List.mem_append, or_imp, forall_and] at hknown
    have htrig := iht ttrig E1 E2 h2 (hctx1 ▸ haw) (hctx1 ▸ hfresh) S habs2 hwf hknown.1.2
    have hbody := ihb tbody E2 Env' h (hctx2 ▸ haw) (hctx2 ▸ hfresh) S habs hwf hknown.2
    rw [hctx1] at htrig
    rw [hctx2] at hbody
    simp only [LExpr.AnnotFits, TypeSpec.instAnnots]
    refine ⟨_, _, _, rfl, ?_, htrig, hbody⟩
    cases sann with
    | none => exact Or.inl rfl
    | some a =>
      refine Or.inr ⟨_, rfl, ?_⟩
      intro dty hd
      rw [Option.some.injEq] at hd
      subst hd
      obtain ⟨hcompat, hvalid⟩ := linkAnnot_readFits C true a _ Env E1 h1 haw hfresh S habs1 hwf
      exact ⟨hcompat, hvalid (hknown.1.1 _ (List.mem_singleton_self _))⟩
  | app sm s1 s2 ih1 ih2 | eq sm s1 s2 ih1 ih2 =>
    intro typed Env Env' h haw hfresh S habs hwf hknown
    cases typed <;> simp only [linkFVarAnnotations, reduceCtorEq] at h
    rename_i tm t1 t2
    simp only [bind, Except.bind] at h
    elim_err h with E1 h1
    have hprops1 := linkFVarAnnotations_properties C s1 t1 Env E1 h1
    have hprops := linkFVarAnnotations_properties C s2 t2 E1 Env' h
    have habs1 := Subst.absorbs_trans _ _ _ hprops.absorbs habs
    simp only [TypeSpec.BinderAnnotsKnown, LExpr.unresolved, LExpr.replaceUserProvidedType,
      LExpr.binderAnnotations, List.mem_append, or_imp, forall_and] at hknown
    have h1' := ih1 t1 Env E1 h1 haw hfresh S habs1 hwf hknown.1
    have h2' := ih2 t2 E1 Env' h (hprops1.context ▸ haw) (hprops1.context ▸ hfresh) S habs hwf
      hknown.2
    rw [hprops1.context] at h2'
    simp only [LExpr.AnnotFits, TypeSpec.instAnnots]
    exact ⟨_, _, rfl, h1', h2'⟩
  | ite sm c t f ihc iht ihf =>
    intro typed Env Env' h haw hfresh S habs hwf hknown
    cases typed <;> simp only [linkFVarAnnotations, reduceCtorEq] at h
    rename_i tm ct tt ft
    simp only [bind, Except.bind] at h
    elim_err h with E1 h1
    elim_err h with E2 h2
    have hprops1 := linkFVarAnnotations_properties C c ct Env E1 h1
    have hprops2 := linkFVarAnnotations_properties C t tt E1 E2 h2
    have hprops := linkFVarAnnotations_properties C f ft E2 Env' h
    have habs2 := Subst.absorbs_trans _ _ _ hprops.absorbs habs
    have habs1 := Subst.absorbs_trans _ _ _ hprops2.absorbs habs2
    have hctx2 : E2.context = Env.context := hprops2.context.trans hprops1.context
    simp only [TypeSpec.BinderAnnotsKnown, LExpr.unresolved, LExpr.replaceUserProvidedType,
      LExpr.binderAnnotations, List.mem_append, or_imp, forall_and] at hknown
    have hc' := ihc ct Env E1 h1 haw hfresh S habs1 hwf hknown.1.1
    have ht' := iht tt E1 E2 h2 (hprops1.context ▸ haw) (hprops1.context ▸ hfresh) S habs2 hwf
      hknown.1.2
    have hf' := ihf ft E2 Env' h (hctx2 ▸ haw) (hctx2 ▸ hfresh) S habs hwf hknown.2
    rw [hprops1.context] at ht'
    rw [hctx2] at hf'
    simp only [LExpr.AnnotFits, TypeSpec.instAnnots]
    exact ⟨_, _, _, rfl, hc', ht', hf'⟩

end SourceExpr

/-- When the checker resolves a source expression, the expression with its annotations read
    through any well-formed `S` absorbing the final substitution has the resolved type under `S`,
    provided the stored binder annotations under `S` are registered. -/
theorem SourceExpr.resolve_HasType_instAnnots
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (e : Expression.Expr)
    (et : LExprT CoreLParams.mono)
    (h : SourceExpr.resolve C Env e = .ok (et, Env'))
    (hscope : LExpr.WellScoped e Env.context)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope Env.context)
    (h_aliasNames : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (S : Subst) (h_absorbs : Subst.absorbs S Env'.stateSubstInfo.subst) (h_wf : SubstWF S)
    (h_known : TypeSpec.BinderAnnotsKnown C (LExpr.applyTypeSubst et.unresolved S)) :
    LExpr.HasType C (TContext.subst Env.context S) (TypeSpec.instAnnots (substEnv S) e)
      (.forAll [] (LMonoTy.subst S et.toLMonoTy)) := by
  obtain ⟨EnvR, hresolve, hlink⟩ := resolve_decompose C Env Env' e et h
  have hprops := SourceExpr.linkFVarAnnotations_properties C e et EnvR Env' hlink
  have hctxR : TContext.FindEq (T := CoreLParams) EnvR.context Env.context := by
    rw [← hprops.context]
    exact resolve_context_FindEq C Env Env' e et h
  have hfits := SourceExpr.linkFVarAnnotations_readFits C e et EnvR Env' hlink
    (fun a ha => h_env.aliasesWF a (hctxR.2 ▸ ha))
    (hctxR.2 ▸ h_aliasNames) S h_absorbs
    h_wf (LExpr.applyTypeSubst_eq_replaceUserProvidedType _ _ ▸ h_known)
  rw [hctxR.2] at hfits
  have hcore := LExpr.resolve_HasType_core (T := CoreLParams) e et C Env EnvR hresolve h_env
    h_fac hscope
  exact hcore.1 S (Subst.absorbs_trans _ _ _ hprops.absorbs h_absorbs) h_wf
    (polyKeysFresh_of_MonoScope (T := CoreLParams) S Env.context h_mono) _ hfits

end Core

end -- public section
