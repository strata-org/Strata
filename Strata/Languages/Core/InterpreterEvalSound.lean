/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterDomainProps
public import Strata.Languages.Core.FactoryEvalSoundWF
import all Strata.Languages.Core.FactoryEvalSoundWF
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.Languages.Core.Interpreter
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import all Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.DL.Lambda.LExprEvalAnnotateProps
import Strata.DL.Lambda.OperationalSemanticsProps

/-! # Core's bounded evaluator is sound for `denoteEval`

On a runtime store denoting a semantic store, every value Core's bounded evaluator `evalBounded`
commits to denotes the value of the reference evaluator `Lambda.LExpr.denoteEval`
(`BoundedEvalSoundAt`), at every modeled factory whose factory meets the conditions of
evaluator soundness (`Lambda.Factory.EvalSoundWF`) and whose short-circuit evaluators commute
with re-annotating free variables (`Lambda.Factory.ShortCircuitAnnotates`): at every modeled
factory over a well-formed factory each of whose functions is a function of `Core.Factory` or a
user function meeting `UserFuncWF`, which `userFuncChecked` decides for monomorphic user
functions; in particular at every modeled factory over `Core.Factory`.

Key definitions: `EvalFactoryWF`, `fvarsAnnotatedBy`, `userFuncChecked`. Key theorems:
`boundedEvalSoundAt_of_evalSoundWF`, `boundedEvalSoundAt_of_evalFactoryWF`,
`evalFactoryWF_of_userFuncs`, `userFuncWF_of_userFuncChecked`, `boundedEvalSoundAt_of_userFuncs`,
`evalFactoryWF_coreFactory`, `boundedEvalSoundAt_coreFactory`.
-/

namespace Core
open Imperative Lambda

public section

/-- The operator check `opsInstantiated` implies `Lambda.OpsConsistent`. -/
private theorem opsConsistent_of_opsInstantiated {F : Lambda.Factory CoreLParams} :
    ∀ {e : Expression.Expr}, opsInstantiated F e = true → OpsConsistent F e := by
  intro e
  induction e with
  | op m name ty =>
    intro h
    unfold opsInstantiated at h
    unfold OpsConsistent
    cases hfn : F[name.name]? with
    | none => trivial
    | some fn =>
      simp only [hfn] at h ⊢
      cases hS : fn.opTypeSubst (.op m name ty) <;> cases ty <;> simp_all
  | app _ _ _ ih1 ih2 =>
    intro h
    simp only [opsInstantiated, Bool.and_eq_true] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | abs _ _ _ _ ih => exact ih
  | ite _ _ _ _ ih1 ih2 ih3 =>
    intro h
    simp only [opsInstantiated, Bool.and_eq_true] at h
    exact ⟨ih1 h.1.1, ih2 h.1.2, ih3 h.2⟩
  | eq _ _ _ ih1 ih2 =>
    intro h
    simp only [opsInstantiated, Bool.and_eq_true] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | quant _ _ _ _ _ _ ih1 ih2 =>
    intro h
    simp only [opsInstantiated, Bool.and_eq_true] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | const | bvar | fvar => intro _; trivial

/-- Re-annotating free variables leaves `opsInstantiated` unchanged. -/
private theorem opsInstantiated_annotateFvars (F : Lambda.Factory CoreLParams)
    (A : CoreIdent → Option LMonoTy) (e : Expression.Expr) :
    opsInstantiated F (e.annotateFvars A) = opsInstantiated F e := by
  induction e <;> simp_all [opsInstantiated, LExpr.annotateFvars]

/-- The type map listing the variables `xs` with the types `f` gives them finds `f x` at every
    `x ∈ xs`. -/
private theorem find?_map_pair (f : CoreIdent → LMonoTy) :
    ∀ (xs : List CoreIdent) (x : CoreIdent), x ∈ xs →
      Map.find? (xs.map fun y => (y, f y)) x = some (f x)
  | [], _, h => nomatch h
  | y :: ys, x, h => by
    by_cases hyx : y = x
    · subst hyx; simp [Map.find?]
    · simp only [List.map_cons, Map.find?, hyx, ↓reduceIte]
      exact find?_map_pair f ys x ((List.mem_cons.1 h).resolve_left (Ne.symm hyx))

/-- A free variable of `e` annotated by `runtimeAnn σr` is annotated as the type map of
    `e`'s variables says, when every variable of `e` has a runtime annotation. -/
private theorem fvars_annotated_by_annotate (A : CoreIdent → Option LMonoTy)
    (tyMap : Map CoreIdent LMonoTy) :
    ∀ (e : Expression.Expr),
      (∀ x ∈ LExpr.LExpr.getVars e, ∃ ty, A x = some ty ∧ Map.find? tyMap x = some ty) →
      fvars_annotated_by tyMap (e.annotateFvars A) := by
  intro e
  induction e with
  | fvar m x ty =>
    intro h
    obtain ⟨t, hA, hf⟩ := h x (by simp [LExpr.LExpr.getVars])
    simp only [LExpr.annotateFvars, hA, fvars_annotated_by]
    intro t' ht'
    rw [hf] at ht'
    exact Option.some.inj ht'
  | const | op | bvar => intro _; trivial
  | abs _ _ _ _ ih => exact fun h => ih h
  | app _ _ _ ih1 ih2 =>
    intro h
    exact ⟨ih1 fun x hx => h x (by simp [LExpr.LExpr.getVars, hx]),
      ih2 fun x hx => h x (by simp [LExpr.LExpr.getVars, hx])⟩
  | ite _ _ _ _ ih1 ih2 ih3 =>
    intro h
    exact ⟨ih1 fun x hx => h x (by simp [LExpr.LExpr.getVars, hx]),
      ih2 fun x hx => h x (by simp [LExpr.LExpr.getVars, hx]),
      ih3 fun x hx => h x (by simp [LExpr.LExpr.getVars, hx])⟩
  | eq _ _ _ ih1 ih2 =>
    intro h
    exact ⟨ih1 fun x hx => h x (by simp [LExpr.LExpr.getVars, hx]),
      ih2 fun x hx => h x (by simp [LExpr.LExpr.getVars, hx])⟩
  | quant _ _ _ _ _ _ ih1 ih2 =>
    intro h
    exact ⟨ih1 fun x hx => h x (by simp [LExpr.LExpr.getVars, hx]),
      ih2 fun x hx => h x (by simp [LExpr.LExpr.getVars, hx])⟩

/-- An expression without free variables is annotated by every type map. -/
private theorem fvars_annotated_by_of_getVars_nil (tyMap : Map CoreIdent LMonoTy) :
    ∀ (e : Expression.Expr), LExpr.LExpr.getVars e = [] → fvars_annotated_by tyMap e := by
  intro e
  induction e with
  | fvar => intro h; simp [LExpr.LExpr.getVars] at h
  | const | op | bvar => intro _; trivial
  | abs _ _ _ _ ih => exact fun h => ih h
  | app _ _ _ ih1 ih2 =>
    intro h
    simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | ite _ _ _ _ ih1 ih2 ih3 =>
    intro h
    simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff] at h
    exact ⟨ih1 h.1.1, ih2 h.1.2, ih3 h.2⟩
  | eq _ _ _ ih1 ih2 =>
    intro h
    simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | quant _ _ _ _ _ _ ih1 ih2 =>
    intro h
    simp only [LExpr.LExpr.getVars, List.append_eq_nil_iff] at h
    exact ⟨ih1 h.1, ih2 h.2⟩

/-- Annotating no free variable leaves an expression unchanged. -/
private theorem annotateFvars_none (e : Expression.Expr) :
    e.annotateFvars (fun _ => none) = e := by
  induction e <;> simp_all [LExpr.annotateFvars]

/-- Equal expressions without free variables have equal denotations under any two free-variable
    valuations. -/
private theorem denote_closed_eq {tc : TyConstrInterp} {op : OpInterp tc}
    {fv fv' : FreeVarVal CoreLParams tc} {vt : TyVarVal} {e e' : Expression.Expr} {τ : LMonoTy}
    (he : e' = e) (hc : LExpr.LExpr.getVars e = []) (h : LExpr.HasTypeA [] e τ)
    (h' : LExpr.HasTypeA [] e' τ) :
    LExpr.denote tc op fv' vt .nil e' τ h' = LExpr.denote tc op fv vt .nil e τ h := by
  subst he
  refine denote_closed_fvarVal_irrel tc op vt ?_ h' h
  rw [getVars_eq_freeVars_idents, List.map_eq_nil_iff] at hc
  simp [LExpr.closed, hc]

/-- **Core's bounded evaluator is sound** at a modeled factory `F` whose factory meets the
    conditions of evaluator soundness (`Lambda.Factory.EvalSoundWF`) and whose short-circuit
    evaluators commute with re-annotating free variables: on a runtime store denoting a semantic
    store `σ`, every value `evalBounded` commits to denotes the value `denoteEval` gives the
    expression on `σ`. -/
theorem boundedEvalSoundAt_of_evalSoundWF (F : Expression.Factory)
    (hF : Lambda.Factory.EvalSoundWF F.factory)
    (hSC : Lambda.Factory.ShortCircuitAnnotates F.factory) :
    BoundedEvalSoundAt Expression F := by
  intro n σr σ e r hS hev
  have hFS : Factory.EvalSoundWFS F.factory := hF
  have hWF : FactoryWF F.factory := hFS.wf.choose_spec.factoryWF
  have hIdent : ∀ a b : CoreLParams.Identifier, a.name = b.name → a = b :=
    fun ⟨_, _⟩ ⟨_, _⟩ h => by cases h; rfl
  obtain ⟨hd, heval, htc, hops⟩ := evalBounded_eq_some_iff.1 hev
  replace heval : LExpr.eval n F.factory σr e = (r, .value true) := heval
  have hden : ∀ x r', σr x = some r' → ∃ w, σ x = some w ∧ InterpLang.Denotes F r' w :=
    fun x r' hx => by
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 fun h => by simp [(hS.1 x).1 h] at hx
      exact ⟨w, hw, hS.2 x r' w hx hw⟩
  have hclosed : ∀ x r', σr x = some r' → LExpr.LExpr.getVars r' = [] := fun x r' hx => by
    obtain ⟨_, _, hD⟩ := hden x r' hx
    exact isValue_getVars_nil _ _ (denotes_iff.1 hD).1
  simp only [evalTypedDomain, Bool.and_eq_true, List.all_eq_true, Option.any_eq_true,
    runtimeAnn_eq_ann hS] at hd
  obtain ⟨hb, τ, hτ, hg⟩ := hd
  let A := ValStore.ann (T := CoreLParams) σ
  have hA : ∀ x, A x = (σr x).bind (LExpr.typeCheck []) := fun x =>
    (congrFun (runtimeAnn_eq_ann hS) x).symm
  let σ' : RStore Expression := fun x => if x ∈ LExpr.LExpr.getVars e then σr x else none
  have hσ' : ∀ x v, σ' x = some v → x ∈ LExpr.LExpr.getVars e ∧ σr x = some v := fun x v h => by
    by_cases hx : x ∈ LExpr.LExpr.getVars e
    · exact ⟨hx, by simpa [σ', hx] using h⟩
    · simp [σ', hx] at h
  have hσ'closed : ∀ x v, σ' x = some v → LExpr.LExpr.getVars v = [] :=
    fun x v h => hclosed x v (hσ' x v h).2
  have heval' : LExpr.eval n F.factory σ' (e.annotateFvars A) = (r, .value true) := by
    rw [eval_annotateFvars hIdent n F.factory σ' hWF hSC hσ'closed A e
      (fun x hx => by simpa [σ', hx] using hb x hx),
      ← eval_env_congr hIdent n F.factory σr σ' hWF hσ'closed e
        (fun x hx => (ite_eq_left hx).symm)]
    exact heval
  let tyMap : Map CoreIdent LMonoTy :=
    (LExpr.LExpr.getVars e).map fun x => (x, (A x).getD .bool)
  have htyA : ∀ x ∈ LExpr.LExpr.getVars e, ∃ ty, A x = some ty ∧ Map.find? tyMap x = some ty :=
    fun x hx => by
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (hb x hx)
      obtain ⟨w, -, hD⟩ := hden x r' hr'
      refine ⟨_, by rw [hA, hr']; exact denotes_typeCheck hD, ?_⟩
      rw [find?_map_pair _ _ x hx, hA, hr', Option.bind_some, denotes_typeCheck hD]
      rfl
  have hwt : ∀ x v ty, σ' x = some v → Map.find? tyMap x = some ty → LExpr.HasTypeA [] v ty :=
    fun x v ty h hf => by
      obtain ⟨hx, hv⟩ := hσ' x v h
      obtain ⟨ty', hA', hf'⟩ := htyA x hx
      rw [hf] at hf'
      rw [← Option.some.inj hf', hA, hv, Option.bind_some] at hA'
      exact LExpr.typeCheck_to_HasTypeA hA'
  let hEnvWF : Env.StepWF F.factory σ' :=
    { typed := ⟨tyMap, hwt, fun x v h => ⟨_, (htyA x (hσ' x v h).1).choose_spec.2⟩⟩
      lc := fun x v h => by
        obtain ⟨ty, -, hf⟩ := htyA x (hσ' x v h).1
        exact HasTypeA_nil_lcAt (hwt x v ty h hf)
      ops := fun x v h => by
        obtain ⟨hx, hv⟩ := hσ' x v h
        simp only [evalOpsChecked, Bool.and_eq_true, List.all_eq_true] at hops
        have hx' := hops.2 x hx
        rw [hv] at hx'
        exact opsConsistent_of_opsInstantiated hx'
      annot := fun x v h => fvars_annotated_by_of_getVars_nil _ v (hσ'closed x v h) }
  letI := F.model.allInhabited
  have hEnvIC : Env.InterpConsistentAt (T := CoreLParams) F.model.tcInterp F.model.opInterp
      (ValStore.fvarVal (T := CoreLParams) F.model.tcInterp σ) F.tyVarVal σ' := by
    intro x v ty h hty
    obtain ⟨hx, hv⟩ := hσ' x v h
    obtain ⟨w, hw, hD⟩ := hden x v hv
    obtain ⟨-, -, hev⟩ := denotes_iff.1 hD
    obtain ⟨-, τv, hτv, -, rfl⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).1 hev
    have hann : v.annotateFvars (ValStore.ann (T := CoreLParams) fun _ => none) = v :=
      annotateFvars_none v
    have hτ_eq : τv = ty := HasTypeA_unique hτv (by rw [hann]; exact hty)
    subst hτ_eq
    simp only [ValStore.fvarVal, hw, Option.bind_some, LExpr.denoteEvalResult]
    rw [SemValue.read_self ⟨F.model.tcInterp, _, _⟩, Option.getD_some]
    exact (denote_closed_eq hann (hσ'closed x v h) hty hτv).symm
  have h₁ : LExpr.HasTypeA [] (e.annotateFvars A) τ := LExpr.typeCheck_to_HasTypeA hτ
  have hOps : OpsConsistent F.factory (e.annotateFvars A) := by
    simp only [evalOpsChecked, Bool.and_eq_true] at hops
    exact opsConsistent_of_opsInstantiated (by rw [opsInstantiated_annotateFvars]; exact hops.1)
  obtain ⟨h₂, hdeq⟩ := eval_denote_soundAt F.model.tcInterp F.model.opInterp
    (ValStore.fvarVal (T := CoreLParams) F.model.tcInterp σ) F.tyVarVal (n := n) h₁ hEnvWF
    (hFS.step _) hFS.wf.choose_spec F.model.interpConsistent F.model.constrConsistent hEnvIC hOps
    (fvars_annotated_by_annotate A tyMap e htyA)
  have hr : (LExpr.eval n F.factory σ' (e.annotateFvars A)).fst = r := by rw [heval']
  have hrv : LExpr.isValue F.factory r = true := by
    have h := eval_value_isValue n F.factory σr e (b := true) (by rw [heval])
    rwa [heval] at h
  have hrc := isValue_getVars_nil _ _ hrv
  have hgr : τ.IsGround := isGroundTy_iff.1 hg
  refine ⟨e.denoteEvalResult F σ τ h₁, (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).2
    ⟨fun x hx => ?_, τ, h₁, hgr, rfl⟩, denotes_iff.2 ⟨hrv, htc, ?_⟩⟩
  · obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (hb x hx)
    obtain ⟨w, hw, hD⟩ := hden x r' hr'
    exact ⟨w, hw, LExpr.denoteEval_tc (denotes_iff.1 hD).2.2⟩
  · have hann : r.annotateFvars (ValStore.ann (T := CoreLParams) fun _ => none) = r :=
      annotateFvars_none r
    have h₂' : LExpr.HasTypeA [] r τ := hr ▸ h₂
    refine (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).2
      ⟨fun x hx => by simp [hrc] at hx, τ, by rw [hann]; exact h₂', hgr, ?_⟩
    simp only [LExpr.denoteEvalResult]
    congr 1
    rw [hdeq]
    exact (denote_closed_eq (hann.trans hr.symm) (hr.symm ▸ hrc) h₂ _).symm

/-- The conditions on a Core factory under which Core's bounded evaluator is sound at every model
    of it (`boundedEvalSoundAt_of_evalFactoryWF`): the factory meets the conditions of evaluator
    soundness (`Lambda.Factory.EvalSoundWF`: it and a type factory are well formed, and function
    bodies, at the type substitutions inlining uses and once inlined, and concrete evaluators
    preserve typing, operator annotations and free-variable annotations), and its short-circuit
    evaluators commute with re-annotating free variables
    (`Lambda.Factory.ShortCircuitAnnotates`). -/
@[expose] def EvalFactoryWF (f : Lambda.Factory CoreLParams) : Prop :=
  Lambda.Factory.EvalSoundWF f ∧ Lambda.Factory.ShortCircuitAnnotates f

/-- `Core.Factory` meets `EvalFactoryWF`. -/
theorem evalFactoryWF_coreFactory : EvalFactoryWF Core.Factory :=
  ⟨factory_evalSoundWF, factory_shortCircuitAnnotates⟩

/-- **Core's bounded evaluator is sound** at every modeled factory whose factory meets
    `EvalFactoryWF`. -/
theorem boundedEvalSoundAt_of_evalFactoryWF (F : Expression.Factory)
    (hF : EvalFactoryWF F.factory) : BoundedEvalSoundAt Expression F :=
  boundedEvalSoundAt_of_evalSoundWF F hF.1 hF.2

/-- **Core's bounded evaluator is sound at Core's built-in factory**: at every modeled factory
    over `Core.Factory`, on a runtime store denoting a semantic store, every value `evalBounded`
    commits to denotes the value `denoteEval` gives the expression. -/
theorem boundedEvalSoundAt_coreFactory (F : Expression.Factory) (hF : F.factory = Core.Factory) :
    BoundedEvalSoundAt Expression F :=
  boundedEvalSoundAt_of_evalFactoryWF F (hF ▸ evalFactoryWF_coreFactory)

/-- Whether every free variable of `e` is annotated, with the type `tyMap` gives it when `tyMap`
    gives it one (the decided form of `Lambda.fvars_annotated_by`). -/
@[expose] def fvarsAnnotatedBy (tyMap : Map CoreIdent LMonoTy) : Expression.Expr → Bool
  | .fvar _ x (some ty) => (Map.find? tyMap x).all fun ty' => decide (ty = ty')
  | .fvar _ _ none => false
  | .app _ f a => fvarsAnnotatedBy tyMap f && fvarsAnnotatedBy tyMap a
  | .abs _ _ _ body => fvarsAnnotatedBy tyMap body
  | .ite _ c t f => fvarsAnnotatedBy tyMap c && fvarsAnnotatedBy tyMap t && fvarsAnnotatedBy tyMap f
  | .eq _ a b => fvarsAnnotatedBy tyMap a && fvarsAnnotatedBy tyMap b
  | .quant _ _ _ _ tr body => fvarsAnnotatedBy tyMap tr && fvarsAnnotatedBy tyMap body
  | _ => true

/-- The check `fvarsAnnotatedBy` implies `Lambda.fvars_annotated_by`. -/
private theorem fvars_annotated_by_of_fvarsAnnotatedBy (tyMap : Map CoreIdent LMonoTy) :
    ∀ {e : Expression.Expr}, fvarsAnnotatedBy tyMap e = true → fvars_annotated_by tyMap e := by
  intro e
  induction e with
  | fvar m x ty =>
    intro h
    cases ty with
    | none => simp [fvarsAnnotatedBy] at h
    | some ty =>
      intro ty' hf
      simp only [fvarsAnnotatedBy, hf, Option.all_some, decide_eq_true_eq] at h
      exact h
  | app _ _ _ ih1 ih2 =>
    intro h
    simp only [fvarsAnnotatedBy, Bool.and_eq_true] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | abs _ _ _ _ ih => exact ih
  | ite _ _ _ _ ih1 ih2 ih3 =>
    intro h
    simp only [fvarsAnnotatedBy, Bool.and_eq_true] at h
    exact ⟨ih1 h.1.1, ih2 h.1.2, ih3 h.2⟩
  | eq _ _ _ ih1 ih2 =>
    intro h
    simp only [fvarsAnnotatedBy, Bool.and_eq_true] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | quant _ _ _ _ _ _ ih1 ih2 =>
    intro h
    simp only [fvarsAnnotatedBy, Bool.and_eq_true] at h
    exact ⟨ih1 h.1, ih2 h.2⟩
  | const | op | bvar => intro _; trivial

/-- Whether the function `fn` of the factory `F` is a monomorphic user function whose body, if
    any, meets the conditions of `UserFuncWF`: it has no concrete evaluator, is not a constructor
    and has no type arguments, and its body type checks at the output type, annotates its free
    variables with the types of the parameters (`fvarsAnnotatedBy`), and annotates its operators
    with instances of their types in `F` (`opsInstantiated`). -/
@[expose] def userFuncChecked (F : Lambda.Factory CoreLParams) (fn : Lambda.LFunc CoreLParams) :
    Bool :=
  fn.concreteEval.isNone && !fn.isConstr && fn.typeArgs.isEmpty &&
    match fn.body with
    | none => true
    | some body => decide (body.typeCheck [] = some fn.output) &&
        fvarsAnnotatedBy fn.inputs body && opsInstantiated F body

/-- A function `userFuncChecked` accepts meets `UserFuncWF`: having no type arguments, it is
    inlined at the empty type substitution, which leaves its body unchanged. -/
theorem userFuncWF_of_userFuncChecked {F : Lambda.Factory CoreLParams}
    {fn : Lambda.LFunc CoreLParams} (h : userFuncChecked F fn = true) : UserFuncWF F fn := by
  simp only [userFuncChecked, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true',
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨hce, hc⟩, hta⟩, hb⟩ := h
  refine ⟨hce, hc, fun body hbody => ?_⟩
  simp only [hbody, decide_eq_true_eq, Bool.and_eq_true] at hb
  obtain ⟨⟨hty, hann⟩, hops⟩ := hb
  refine ⟨LExpr.typeCheck_to_HasTypeA hty, fvars_annotated_by_of_fvarsAnnotatedBy _ hann,
    fun callee args S hS => ?_⟩
  simp only [LFunc.computeTypeSubst, LFunc.opTypeSubst, hta, List.isEmpty_nil, ↓reduceIte,
    Option.some.injEq] at hS
  subst hS
  simp only [LExpr.applyTypeSubst, Subst.hasEmptyScopes_empty, ↓reduceIte]
  exact opsConsistent_of_opsInstantiated hops

/-- A well-formed factory each of whose functions is a function of `Core.Factory` or a user
    function meeting `UserFuncWF` meets `EvalFactoryWF`. -/
theorem evalFactoryWF_of_userFuncs (f : Lambda.Factory CoreLParams) (hWF : Lambda.FactoryWF f)
    (hfns : ∀ fn ∈ f.toArray, fn ∈ Core.Factory.toArray ∨ UserFuncWF f fn) : EvalFactoryWF f :=
  ⟨programFactory_evalSoundWF f hWF hfns, programFactory_shortCircuitAnnotates f hfns⟩

/-- **Core's bounded evaluator is sound at program factories**: at every modeled factory over a
    well-formed factory each of whose functions is a function of `Core.Factory` or a user function
    meeting `UserFuncWF` (for instance one `userFuncChecked` accepts), on a runtime store denoting
    a semantic store, every value `evalBounded` commits to denotes the value `denoteEval` gives
    the expression. -/
theorem boundedEvalSoundAt_of_userFuncs (F : Expression.Factory) (hWF : Lambda.FactoryWF F.factory)
    (hfns : ∀ fn ∈ F.factory.toArray, fn ∈ Core.Factory.toArray ∨ UserFuncWF F.factory fn) :
    BoundedEvalSoundAt Expression F :=
  boundedEvalSoundAt_of_evalFactoryWF F (evalFactoryWF_of_userFuncs _ hWF hfns)

end -- public section

end Core
