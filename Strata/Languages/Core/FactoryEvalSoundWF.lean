/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
public import Strata.DL.Lambda.LExprEvalAnnotateProps
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.Languages.Core.Factory
import all Strata.Languages.Core.Logic.FactoryInterp
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Factory
import Strata.Util.ListMapProps
import Strata.DL.Lambda.LExprProps

/-! # Program factories meet the conditions of evaluator soundness

A well-formed factory each of whose functions is a function of `Core.Factory` or a user function
meeting `UserFuncWF` (no concrete evaluator, not a constructor, a body that is well typed at its
signature, annotates its parameters with their declared types, and is `OpsConsistent` at the type
substitutions inlining uses) satisfies the conditions under which `LExpr.eval` preserves
denotation (`Lambda.Factory.EvalSoundWF`), and its short-circuit evaluators commute with
re-annotating free variables (`Lambda.Factory.ShortCircuitAnnotates`). `Core.Factory` is such a
factory.

Key definitions: `Core.UserFuncWF`. Key theorems: `Core.programFactory_evalSoundWF`,
`Core.programFactory_shortCircuitAnnotates`, `Core.factory_evalSoundWF`,
`Core.factory_shortCircuitAnnotates`.
-/

namespace Core

public section

/-- The shape of the results of a factory function's concrete evaluator: a well-typed constant
    of the function's output type, or the second of exactly two arguments when both inputs and
    the output have type `bool`. -/
private def EvalShape (fn : Lambda.LFunc CoreLParams) : Prop :=
  ∀ ceval, fn.concreteEval = some ceval → ∀ md opTy args r, ceval md opTy args = some r →
    (∃ m c, r = .const m c ∧ c.wt = true ∧ c.ty = fn.output) ∨
    (∃ x, args = [x, r] ∧ fn.inputs.map Prod.snd = [.bool, .bool] ∧ fn.output = .bool)

/-- The concrete evaluator of a short-circuit factory function commutes with re-annotating the
    free variables of the arguments after the first. -/
private def SCShape (fn : Lambda.LFunc CoreLParams) : Prop :=
  Strata.DL.Util.FuncAttr.hasShortCircuit fn.attr = true →
    ∀ ceval, fn.concreteEval = some ceval →
    ∀ md opTy (a : Lambda.LExpr CoreLParams.mono) rest A,
      ceval md opTy (a :: rest.map (Lambda.LExpr.annotateFvars A)) =
        (ceval md opTy (a :: rest)).map (Lambda.LExpr.annotateFvars A)

open Lambda in
/-- A `unaryOp` evaluator returns a constant of its output type, provided the literal builder
    of the output type builds constants of that type; it is not a short-circuit function. -/
private theorem unaryOp_shape {inTy outTy : LMonoTy} {InV OutV : Type} [ToString OutV]
    [LambdaLeanType inTy InV] [LambdaLeanType outTy OutV]
    {n : CoreLParams.Identifier} {f : InV → OutV} {pre hI hO hp}
    (hmk : ∀ md (v : OutV), ∃ m c, LambdaLeanType.mkConst (ty := outTy) CoreLParams md v =
      .const m c ∧ c.wt = true ∧ c.ty = outTy := by intro md v; exact ⟨_, _, rfl, rfl, rfl⟩) :
    EvalShape (unaryOp n f pre hI hO hp).func ∧ SCShape (unaryOp n f pre hI hO hp).func := by
  refine ⟨fun ceval hce md opTy args r h => .inl ?_, fun h => nomatch h⟩
  cases hce
  simp only at h
  split at h
  · split at h
    · cases h
      exact hmk md _
    · cases h
  · cases h

open Lambda in
/-- A `binaryOp` evaluator returns a constant of its output type, provided the literal builder
    of the output type builds constants of that type; it is not a short-circuit function. -/
private theorem binaryOp_shape {inTy outTy : LMonoTy} {InV OutV : Type} [ToString OutV]
    [LambdaLeanType inTy InV] [LambdaLeanType outTy OutV]
    {n : CoreLParams.Identifier} {g : InV → InV → OutV} {guard pre hI hO hp}
    (hmk : ∀ md (v : OutV), ∃ m c, LambdaLeanType.mkConst (ty := outTy) CoreLParams md v =
      .const m c ∧ c.wt = true ∧ c.ty = outTy := by intro md v; exact ⟨_, _, rfl, rfl, rfl⟩) :
    EvalShape (binaryOp n g guard pre hI hO hp).func ∧
      SCShape (binaryOp n g guard pre hI hO hp).func := by
  refine ⟨fun ceval hce md opTy args r h => .inl ?_, fun h => nomatch h⟩
  cases hce
  simp only at h
  split at h
  · split at h
    · split at h
      · cases h
        exact hmk md _
      · cases h
    · cases h
  · cases h

open Lambda in
/-- A `shortCircuitOp` evaluator returns a Boolean constant or its second argument, and commutes
    with re-annotating the free variables of the arguments after the first. -/
private theorem shortCircuitOp_shape {n : CoreLParams.Identifier} {absorb decided : Bool} :
    EvalShape (shortCircuitOp n absorb decided).func ∧
      SCShape (shortCircuitOp n absorb decided).func := by
  refine ⟨fun ceval hce md opTy args r h => ?_, fun _ ceval hce md opTy a rest A => ?_⟩
  · cases hce
    simp only at h
    split at h
    · split at h
      · split at h
        · cases h
          exact .inl ⟨_, _, rfl, rfl, rfl⟩
        · cases h
          exact .inr ⟨_, rfl, rfl, rfl⟩
      · cases h
    · cases h
  · cases hce
    rcases rest with _ | ⟨y, _ | ⟨z, t⟩⟩
    · rfl
    · simp only [List.map]
      split <;> (try split) <;> rfl
    · rfl

/-- Every function of `Core.Factory`'s underlying array has an evaluator of the shape
    `EvalShape` and, if it is a short-circuit function, one that commutes with re-annotation. -/
private theorem all_shape :
    ∀ wf ∈ Core.WFFactoryArray.toList, EvalShape wf.func ∧ SCShape wf.func := by
  unfold Core.WFFactoryArray
  simp only [Array.toList_appendList, List.forall_mem_append]
  repeat' apply And.intro
  all_goals
    repeat (refine List.forall_mem_cons.mpr ⟨?_, ?_⟩; rotate_left)
    exact List.forall_mem_nil _
  all_goals
    first
    | exact unaryOp_shape
    | exact binaryOp_shape
    | exact shortCircuitOp_shape
    | exact unaryOp_shape (inTy := .bitvec _) (outTy := .int) (pre := []) (hI := rfl)
        (hO := rfl) (hp := nofun)
    | exact unaryOp_shape (inTy := .int) (outTy := .bitvec _) (pre := []) (hI := rfl)
        (hO := rfl) (hp := nofun)
    | exact ⟨fun _ hce => (nomatch hce), fun _ _ hce => (nomatch hce)⟩

/-- Every function of `Core.Factory` has an evaluator of the shape `EvalShape` and, if it is a
    short-circuit function, one that commutes with re-annotation. -/
private theorem shape_of_mem {fn : Lambda.LFunc CoreLParams} (h : fn ∈ Core.Factory.toArray) :
    EvalShape fn ∧ SCShape fn := by
  obtain ⟨wf, hwf, rfl⟩ :=
    Array.mem_map.mp (Lambda.Factory.ofArray_mem (a := Core.WFFactoryArray.map (·.func)) h)
  exact all_shape wf (Array.mem_def.mp hwf)

/-- The type of a constant has no type variables, so type substitution leaves it unchanged. -/
private theorem LConst_ty_subst (c : Lambda.LConst) (S : Lambda.Subst) :
    c.ty.subst S = c.ty :=
  Lambda.LMonoTy.subst_no_relevant_keys _ _ (by
    intro x hx; rw [Lambda.LConst.ty_freeVars] at hx; cases hx)

/-- A concrete evaluator of a `Core.Factory` function returns, on arguments well typed at the
    input types instantiated by `S`, a result well typed at the output type instantiated by `S`. -/
private theorem evalWt_of_mem {fn : Lambda.LFunc CoreLParams} (hfn : fn ∈ Core.Factory.toArray)
    {ceval md opTy args r} (hce : fn.concreteEval = some ceval) (S : Lambda.Subst)
    (h : ceval md opTy args = some r)
    (hargs : List.Rel₂ (Lambda.LExpr.HasTypeA [])
      args ((fn.inputs.map Prod.snd).map (Lambda.LMonoTy.subst S))) :
    Lambda.LExpr.HasTypeA [] r (fn.output.subst S) := by
  rcases (shape_of_mem hfn).1 ceval hce md opTy args r h with
    ⟨m, c, rfl, hw, hc⟩ | ⟨x, rfl, hin, hout⟩
  · rw [← hc, LConst_ty_subst]
    exact .const hw
  · rw [hin] at hargs
    rw [hout]
    cases hargs with
    | cons _ h2 => cases h2 with
      | cons h3 _ => exact h3

/-- A concrete evaluator of a `Core.Factory` function returns a result satisfying a property `P`
    of expressions that holds of every constant, on arguments that satisfy `P`. -/
private theorem evalPres_of_mem {fn : Lambda.LFunc CoreLParams} (hfn : fn ∈ Core.Factory.toArray)
    {ceval md opTy args r} (hce : fn.concreteEval = some ceval) (h : ceval md opTy args = some r)
    (P : Lambda.LExpr CoreLParams.mono → Prop) (hc : ∀ m c, P (.const m c))
    (hargs : ∀ a ∈ args, P a) : P r := by
  rcases (shape_of_mem hfn).1 ceval hce md opTy args r h with ⟨m, c, rfl, -⟩ | ⟨x, rfl, -⟩
  · exact hc m c
  · exact hargs r (by simp)

/-- A function a factory names belongs to the factory's underlying array. -/
private theorem getElem_mem_toArray {F : Lambda.Factory CoreLParams} {f : String} (hf : f ∈ F) :
    F[f] ∈ F.toArray := by
  change Lambda.Factory.get F f hf ∈ F.toArray
  simp only [Lambda.Factory.get]
  exact Array.getElem_mem _

/-- Substituting the free variables of `e` simultaneously keeps free-variable annotations when
    the substitution binds every free variable of `e` to an expression annotated by `tyMap`. -/
private theorem fvars_annotated_by_go {tyMap : Map CoreIdent Lambda.LMonoTy}
    {sm : Map CoreIdent Expression.Expr}
    (hsm : ∀ k v, Map.find? sm k = some v → Lambda.fvars_annotated_by tyMap v) :
    ∀ (e : Expression.Expr) (d : Nat),
      (∀ x ∈ Lambda.LExpr.LExpr.getVars e, Map.find? sm x ≠ none) →
      Lambda.fvars_annotated_by tyMap (Lambda.LExpr.substFvarsLifting.go sm e d) := by
  intro e
  induction e with
  | fvar m x ty =>
    intro d h
    simp only [Lambda.LExpr.substFvarsLifting.go]
    split
    · next v hv => exact Lambda.fvars_annotated_by_replaceMetadata1 m (Lambda.fvars_annotated_by_liftBVars (hsm _ _ hv))
    · next hn => exact absurd hn (h x (by simp [Lambda.LExpr.LExpr.getVars]))
  | const | op | bvar => intro _ _; trivial
  | abs _ _ _ _ ih => exact fun d h => ih (d + 1) h
  | app _ _ _ ih1 ih2 =>
    intro d h
    exact ⟨ih1 d fun x hx => h x (by simp [Lambda.LExpr.LExpr.getVars, hx]),
      ih2 d fun x hx => h x (by simp [Lambda.LExpr.LExpr.getVars, hx])⟩
  | ite _ _ _ _ ih1 ih2 ih3 =>
    intro d h
    exact ⟨ih1 d fun x hx => h x (by simp [Lambda.LExpr.LExpr.getVars, hx]),
      ih2 d fun x hx => h x (by simp [Lambda.LExpr.LExpr.getVars, hx]),
      ih3 d fun x hx => h x (by simp [Lambda.LExpr.LExpr.getVars, hx])⟩
  | eq _ _ _ ih1 ih2 =>
    intro d h
    exact ⟨ih1 d fun x hx => h x (by simp [Lambda.LExpr.LExpr.getVars, hx]),
      ih2 d fun x hx => h x (by simp [Lambda.LExpr.LExpr.getVars, hx])⟩
  | quant _ _ _ _ _ _ ih1 ih2 =>
    intro d h
    exact ⟨ih1 (d + 1) fun x hx => h x (by simp [Lambda.LExpr.LExpr.getVars, hx]),
      ih2 (d + 1) fun x hx => h x (by simp [Lambda.LExpr.LExpr.getVars, hx])⟩

/-- Substituting with the empty map leaves an expression unchanged. -/
private theorem go_nil (e : Expression.Expr) (d : Nat) :
    Lambda.LExpr.substFvarsLifting.go [] e d = e := by
  induction e generalizing d <;> simp_all [Lambda.LExpr.substFvarsLifting.go, Map.find?]

/-- In a well-formed factory, inlining a function body keeps free-variable annotations at every
    type map: the body's free variables are its parameters, which inlining replaces by the
    arguments. -/
private theorem bodyInlineAnnotated_of_wf {F : Lambda.Factory CoreLParams}
    (hWF : Lambda.FactoryWF F) (tyMap : Map CoreIdent Lambda.LMonoTy) :
    Lambda.Factory.BodyInlineAnnotated F tyMap := by
  intro f hf body S args hb hlen hargs
  have hsm : ∀ k v, Map.find? (F[f].inputs.keys.zip args) k = some v →
      Lambda.fvars_annotated_by tyMap v :=
    fun _ v hv => hargs v (List.of_mem_zip (Map.find?_mem _ _ _ hv)).2
  have hfound : ∀ x ∈ Lambda.LExpr.LExpr.getVars (body.applyTypeSubst S),
      Map.find? (F[f].inputs.keys.zip args) x ≠ none := by
    intro x hx
    rw [Lambda.getVars_applyTypeSubst] at hx
    have hk := Lambda.lfunc_body_getVars_subset_keys (fun ⟨_, _⟩ ⟨_, _⟩ h => by cases h; rfl)
      _ (hWF.lfuncs_wf _ (getElem_mem_toArray hf)) body hb x hx
    apply Map_find?_ne_none_of_mem_keys
    have hle : F[f].inputs.keys.length ≤ args.length := by
      rw [hlen, ListMap.keys_eq_map_fst]
      exact Nat.le_of_eq (List.length_map _)
    rw [Map.keys_eq_map_fst (F[f].inputs.keys.zip args), List.map_fst_zip hle]
    exact hk
  unfold Lambda.LExpr.substFvarsLifting
  split
  · rename_i hne
    rw [← go_nil (body.applyTypeSubst S) 0]
    have he : F[f].inputs.keys.zip args = [] := by
      cases h : F[f].inputs.keys.zip args
      · rfl
      · simp [h, Map.isEmpty] at hne
    rw [he] at hfound
    exact fvars_annotated_by_go (fun _ _ h => by simp [Map.find?] at h) _ 0 hfound
  · exact fvars_annotated_by_go hsm _ 0 hfound

/-- The conditions on a function `fn` of a program factory `F` that is not a function of
    `Core.Factory` (a user function): it has no concrete evaluator and is not a constructor, and
    its body, if any, is well typed at the declared output type, annotates its parameters with
    their declared types, and satisfies `OpsConsistent` (its operators are annotated with
    instances of their types in `F`) at every type substitution inlining computes for a call. -/
def UserFuncWF (F : Lambda.Factory CoreLParams) (fn : Lambda.LFunc CoreLParams) : Prop :=
  fn.concreteEval = none ∧ fn.isConstr = false ∧
    ∀ body, fn.body = some body →
      Lambda.LExpr.HasTypeA [] body fn.output ∧ Lambda.fvars_annotated_by fn.inputs body ∧
      ∀ callee args S, fn.computeTypeSubst callee args = some S →
        Lambda.OpsConsistent F (body.applyTypeSubst S)

open FactoryInterpModel in
/-- A well-formed factory each of whose functions is a function of `Core.Factory` or a user
    function meeting `UserFuncWF` meets the conditions of `Lambda.eval_denote_soundAt`: it is well
    formed with the empty type factory, its bodies are well typed and `OpsConsistent` and stay
    annotated once inlined, and its concrete evaluators, all of `Core.Factory`, return well-typed
    results on well-typed arguments, literals or one of their arguments. -/
theorem programFactory_evalSoundWF (F : Lambda.Factory CoreLParams) (hWF : Lambda.FactoryWF F)
    (hfns : ∀ fn ∈ F.toArray, fn ∈ Core.Factory.toArray ∨ UserFuncWF F fn) :
    Lambda.Factory.EvalSoundWF F := by
  have hc : ∀ f (hf : f ∈ F), F[f] ∈ Core.Factory.toArray ∨ UserFuncWF F (F[f]) := fun f hf =>
    hfns _ (getElem_mem_toArray hf)
  refine ⟨⟨#[], hWF, fun fn hfn hct => ?_, ⟨by simp [Lambda.TypeFactory.allDatatypes]⟩⟩,
    fun tyMap => ⟨fun f hf body hb => ?_, fun f hf _ hce _ _ _ S h hargs => ?_,
      fun f hf body callee args S hb hS => ?_, fun f hf _ _ _ _ _ hce h => ?_,
      bodyInlineAnnotated_of_wf hWF tyMap, fun f hf _ _ _ _ _ hce h => ?_⟩⟩
  · exact ((hfns fn hfn).elim (fun h => Bool.false_ne_true ((all_not_constr fn h).symm.trans hct))
      fun h => Bool.false_ne_true (h.2.1.symm.trans hct)).elim
  · exact (hc f hf).elim (fun h => nomatch (all_bodies_none _ h).symm.trans hb)
      fun h => ⟨(h.2.2 body hb).1, (h.2.2 body hb).2.1⟩
  · exact (hc f hf).elim (fun h' => evalWt_of_mem h' hce S h hargs)
      fun h' => nomatch h'.1.symm.trans hce
  · exact (hc f hf).elim (fun h => nomatch (all_bodies_none _ h).symm.trans hb)
      fun h => (h.2.2 body hb).2.2 callee args S hS
  · exact (hc f hf).elim (fun h' => evalPres_of_mem h' hce h.symm _ fun _ _ => trivial)
      fun h' => nomatch h'.1.symm.trans hce
  · exact (hc f hf).elim (fun h' => evalPres_of_mem h' hce h.symm _ fun _ _ => trivial)
      fun h' => nomatch h'.1.symm.trans hce

/-- The short-circuit evaluators of a factory each of whose functions is a function of
    `Core.Factory` or a user function meeting `UserFuncWF` commute with re-annotating the free
    variables of their unevaluated arguments: they are those of `Core.Factory` (`Bool.And`,
    `Bool.Or`, `Bool.Implies`). -/
theorem programFactory_shortCircuitAnnotates (F : Lambda.Factory CoreLParams)
    (hfns : ∀ fn ∈ F.toArray, fn ∈ Core.Factory.toArray ∨ UserFuncWF F fn) :
    Lambda.Factory.ShortCircuitAnnotates F :=
  fun lf hlf hsc ceval hce => (hfns lf hlf).elim (fun h => (shape_of_mem h).2 hsc ceval hce)
    fun h => nomatch h.1.symm.trans hce

/-- `Core.Factory` meets the conditions of `Lambda.eval_denote_soundAt`: it is well formed with
    the empty type factory, no function has a body, and its concrete evaluators return well-typed
    results on well-typed arguments, literals or one of their arguments. -/
theorem factory_evalSoundWF : Lambda.Factory.EvalSoundWF Core.Factory :=
  programFactory_evalSoundWF _ Core.WFFactory.toFactory_wf fun _ h => .inl h

/-- The short-circuit evaluators of `Core.Factory` (`Bool.And`, `Bool.Or`, `Bool.Implies`)
    commute with re-annotating the free variables of their unevaluated arguments. -/
theorem factory_shortCircuitAnnotates : Lambda.Factory.ShortCircuitAnnotates Core.Factory :=
  programFactory_shortCircuitAnnotates _ fun _ h => .inl h

end -- public section

end Core
