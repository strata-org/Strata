/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterEvalSound
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExpr
import all Strata.Languages.Core.Interpreter
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.DL.Lambda.OperationalSemanticsProps
import Strata.Languages.Core.InterpreterProps
import all Strata.DL.Lambda.LExprEvalAnnotateProps
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote
import Strata.Util.ListUtilsProps
import Strata.Util.ListMapProps
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.Denote.LExprDenoteSubst
import all Strata.DL.Lambda.Denote.Assumptions
import Strata.DL.Lambda.Denote.LExprDenoteConsts

/-! # Computable expression evaluation in Core

Core's bounded evaluator `evalBounded` reaches the value the reference evaluator
`Expression.eval` (`Lambda.LExpr.denoteEval`) gives an expression only on part of Core: it does
not decide quantifiers (`∀ x : int. x == x` denotes `true`, and `LExpr.eval` never reduces it), it
does not evaluate functions without a concrete evaluator or a body it unfolds (map, set and
sequence operations, polymorphic operators, uninterpreted functions), and a concrete evaluator may
leave a call undecided (`Int.Div` on a zero divisor, whose reference value the model gives). This
module states the expressions on which it does, and the closure laws of that class.

*Computable expression evaluation* (`ComputableEval F σ e`) is that predicate: on every runtime
store denoting `σ`, every typing of `e` (its free variables annotated with the sorts of their
values) is at the type of a literal `c` whose value is the value `Expression.eval F σ e` gives,
so the value can be reified as a literal, and `evalBounded` computes that literal. The literal
is primitive (`LConst.isPrimitive`: not a map or sequence literal); the evaluator's equality test
does not decide every equality of map literals. It implies
the reach fact the engine-realizable relations carry (`engEvalReach_of_computableEval`).

The class is closed under what Core programs use, at a modeled factory meeting the conditions of
evaluator soundness (`EvalFactoryWF`):
* primitive literals (`computableEval_const`), and variables bound to their values
  (`computableEval_fvar`, on a factory none of whose constructors produces a value of a literal
  type, `ConstrsNotLit`);
* conditionals and equalities of computable expressions (`computableEval_ite`,
  `computableEval_eq`);
* calls of factory operators whose concrete evaluator computes every call on literals
  (`ComputableOp`, `computableEval_op`): monomorphic, not constructors, without a body, their
  concrete evaluator either returning a literal of the output type on literals of the input
  types (`CevalTotal`), or, for a short-circuiting connective, returning a literal or one of the
  remaining arguments once the first one is a literal (`CevalShortCircuits`);
* calls of monomorphic user functions the evaluator unfolds (`inline` or `inlineIfAllValues`),
  whose body reads only its parameters and is computable once they are replaced by literals of
  their types (`computableEval_userFn`).

Key definitions: `ComputableEval`, `ConstrsNotLit`, `LitsOfTypes`, `CevalTotal`,
`CevalShortCircuits`, `ComputableOp`. Key theorems: the closure laws above,
`engEvalReach_of_computableEval`, `denotes_const_iff`. -/

namespace Core
open Lambda Imperative
public section

/-- **Computable expression evaluation** of `e` on the semantic store `σ` under the modeled
    factory `F`: on every runtime store `σr` denoting `σ`, for every typing of `e` at a type `τ`
    (its free variables, all bound in `σ` to values of `F`'s model, annotated with the sorts of
    their values), `τ` is the type of a primitive literal `c` (`LConst.isPrimitive`) whose
    value is the value `Expression.eval` gives `e`, and the bounded evaluator computes the literal
    `c` at some fuel. -/
@[expose] def ComputableEval (F : Expression.Factory) (σ : SemanticStore Expression)
    (e : Expression.Expr) : Prop :=
  ∀ (σr : RStore Expression) (τ : LMonoTy), StoreDenotes F σr σ →
    ValStore.Defines (T := CoreLParams) σ F.model.tcInterp e →
    (e.annotateFvars (ValStore.ann (T := CoreLParams) σ)).HasTypeA [] τ →
    ∃ c : LConst, c.isPrimitive = true ∧ c.ty = τ ∧
      Expression.eval F σ e = some (SemValue.ofConst F.model.tcInterp c) ∧
      ∃ n m, evalBounded n F.factory σr e = some (.const m c)

/-- A well-typed literal (`LConst.wt`) denotes exactly the value of its constant. -/
theorem denotes_const_iff {F : Expression.Factory} {m : ExpressionMetadata} {c : LConst}
    {v : Expression.Val} (hc : c.wt = true) :
    InterpLang.Denotes F (.const m c) v ↔ v = SemValue.ofConst F.model.tcInterp c := by
  refine ⟨fun h => ?_, fun h => h ▸ denotes_literal (LExpr.denoteEval_const hc)⟩
  have h2 := (denotes_iff.1 h).2.2
  rw [LExpr.denoteEval_const (T := CoreLParams) hc] at h2
  exact (Option.some.inj h2).symm

/-- A literal that denotes a value is well typed (`LConst.wt`). -/
private theorem denotes_const_wt {F : Expression.Factory} {m : ExpressionMetadata} {c : LConst}
    {v : Expression.Val} (h : InterpLang.Denotes F (.const m c) v) : c.wt = true :=
  LExpr.denoteEval_const_wt (denotes_iff.1 h).2.2

/-- Once the bounded evaluator commits a literal for `e`, primitive when it has the type of `e`,
    the literal's value is `e`'s value and every typing of `e` is at the literal's type. -/
private theorem computable_of_evalBounded {F : Expression.Factory} (hF : EvalFactoryWF F.factory)
    {σr : RStore Expression} {σ : SemanticStore Expression} {e : Expression.Expr} {τ : LMonoTy}
    {n : Nat} {m : ExpressionMetadata} {c : LConst} (hS : StoreDenotes F σr σ)
    (hty : (e.annotateFvars (ValStore.ann (T := CoreLParams) σ)).HasTypeA [] τ)
    (h : evalBounded n F.factory σr e = some (.const m c))
    (hdec : c.ty = τ → c.isPrimitive = true) :
    ∃ c' : LConst, c'.isPrimitive = true ∧ c'.ty = τ ∧
      Expression.eval F σ e = some (SemValue.ofConst F.model.tcInterp c') ∧
      ∃ n m, evalBounded n F.factory σr e = some (.const m c') := by
  obtain ⟨v, hv, hd⟩ := boundedEvalSoundAt_of_evalFactoryWF F hF n σr σ e _ hS h
  obtain rfl := (denotes_const_iff (denotes_const_wt hd)).1 hd
  have hct : c.ty = τ := by
    obtain ⟨-, τ', hτ', hg, hres⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).1 hv
    obtain rfl := HasTypeA_unique hty hτ'
    have hs : c.ty.substTyVars refTyVarVal = τ.substTyVars F.tyVarVal :=
      congrArg SemValue.sort hres
    rw [(LConst.ty_isGround c).substTyVars_eq refTyVarVal F.tyVarVal] at hs
    exact (LConst.ty_isGround c).eq_of_substTyVars_eq hg hs
  exact ⟨c, hdec hct, hct, hv, n, m, h⟩


/-- No constructor of the factory produces a value of a primitive literal type (`bool`, `int`,
    `real`, `string`, a bit-vector type), under any type substitution: the values of primitive
    literal types are then literals (`eq_const_of_isValue`). -/
@[expose] def ConstrsNotLit (F : Lambda.Factory CoreLParams) : Prop :=
  ∀ fn ∈ F.toArray, fn.isConstr = true → ∀ S (c : LConst), c.isPrimitive = true →
    LMonoTy.subst S fn.output ≠ c.ty

/-- **Values of primitive literal types are literals.** On a factory none of whose constructors
    produces a value of a primitive literal type (`ConstrsNotLit`), a value that type checks
    against the factory (`typeCheckWith`) to the type of a primitive literal is a literal. -/
private theorem eq_const_of_isValue {F : Lambda.Factory CoreLParams} (hF : ConstrsNotLit F)
    {e : Expression.Expr} {c : LConst} (hcp : c.isPrimitive = true)
    (hc : LExpr.isValue F e = true)
    (ht : LExpr.typeCheckWith F [] e = some c.ty) : ∃ m c', e = .const m c' := by
  unfold LExpr.typeCheckWith at ht
  split at ht
  rotate_left
  · cases ht
  rename_i hops
  unfold LExpr.isValue at hc
  split at hc
  · exact ⟨_, _, rfl⟩
  · cases ‹Option LMonoTy›
    · simp [LExpr.typeCheck] at ht
    · simp only [LExpr.typeCheck, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at ht
      obtain ⟨_, -, ha⟩ := ht
      exact absurd ha.symm (LConst.ty_ne_arrow c _ _)
  · cases hc
  split at hc
  rotate_left
  · cases hc
  rename_i op args fn hcall
  have hle : args.length ≤ fn.inputs.length := by
    simp only [Factory.callOfLFunc] at hcall
    repeat' split at hcall
    all_goals simp_all only [imp_false, List.map_subtype, List.unattach_attach, List.all_map,
        Function.id_comp, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, List.all_eq_true,
        reduceCtorEq, ↓reduceIte, Nat.ble_eq, Option.some.injEq, Prod.mk.injEq]
  obtain ⟨m, name, ty, rfl, hget⟩ := Factory.callOfLFunc_getElem? hcall
  have hgl := callOfLFunc_getLFuncCall hcall
  have hspec := getLFuncCall_spec (LExpr.typeCheck_to_HasTypeA ht)
  rw [hgl] at hspec
  obtain ⟨tys, hrel, hop⟩ := hspec
  have hlen := hrel.length_eq.symm
  replace hop := LExpr.HasTypeA_to_typeCheck hop
  simp only [getLFuncCall] at hgl
  have hops' := opsConsistent_getLFuncCall_go e [] hops
  rw [hgl] at hops'
  cases ty
  · cases hop
  simp only [LExpr.typeCheck, Option.some.injEq] at hop
  subst hop
  simp only [LExpr.opsConsistent, hget] at hops'
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp hops'
  have hops' := (LMonoTy.matchSubst_sound hS).symm
  rw [subst_mkArrow'] at hops'
  have hd := LMonoTy.mkArrow'_eq_drop hops' (by
    rw [hlen, List.length_map]
    exact Nat.le_trans hle (Nat.le_of_eq (List.length_map _).symm))
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at hc
  revert hd
  cases hdrop : List.drop tys.length (List.map (LMonoTy.subst _) (List.map Prod.snd fn.inputs))
  · have hn : ¬ args.length < fn.inputs.length := by
      simp only [List.drop_eq_nil_iff, List.length_map] at hdrop
      exact Nat.not_lt_of_le (hlen ▸ (List.length_map _) ▸ hdrop)
    exact fun hd => absurd hd.symm
      (hF fn (Factory.getElem?_is_some_implies_mem hget) (hc.1.resolve_right hn) _ c hcp)
  · exact fun hd => absurd hd (LConst.ty_ne_arrow c _ _)

/-- A primitive literal is computable. -/
theorem computableEval_const (F : Expression.Factory) (hF : EvalFactoryWF F.factory)
    (σ : SemanticStore Expression) (m : ExpressionMetadata) {c : LConst}
    (hc : c.isPrimitive = true) : ComputableEval F σ (.const m c) := fun _ _ hS _ hty =>
  computable_of_evalBounded hF hS hty (evalBounded_const 0 _ _ m c (HasTypeA.const_wt hty))
    fun _ => hc

/-- A variable bound to the value of a primitive literal, or unbound, is
    computable, on a factory none of whose constructors produces a value of a literal type. -/
theorem computableEval_fvar (F : Expression.Factory) (hF : EvalFactoryWF F.factory)
    (hlit : ConstrsNotLit F.factory) {σ : SemanticStore Expression} {m : ExpressionMetadata}
    {x : CoreIdent} {ty : Option LMonoTy}
    (hx : ∀ v, σ x = some v →
      ∃ c, c.isPrimitive = true ∧ v = SemValue.ofConst F.model.tcInterp c) :
    ComputableEval F σ (.fvar m x ty) := by
  intro σr τ hS hd hty
  obtain ⟨w, hw, -⟩ := hd x (by simp [LExpr.LExpr.getVars])
  obtain ⟨c, hcd, rfl⟩ := hx w hw
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 fun h => by simp [(hS.1 x).2 h] at hw
  have hD := hS.2 x r _ hr hw
  obtain ⟨hv, hw', -⟩ := denotes_iff.1 hD
  have htc : r.typeCheckWith F.factory [] = some c.ty := by
    obtain ⟨τ', hτ'⟩ := Option.isSome_iff_exists.1 hw'
    have h1 := denotes_typeCheck hD
    unfold LExpr.typeCheckWith at hτ' ⊢
    split at hτ' <;> simp_all only [SemValue.ofConst, Option.some.injEq, forall_eq',
        SemValue.mk.injEq, true_and, LConst.ty_isGround c, ↓reduceIte, Bool.not_eq_true,
        reduceCtorEq]
  obtain ⟨m', c', rfl⟩ := eq_const_of_isValue hlit hcd hv htc
  have hw'' : c'.wt = true := (typeCheckWith_const_isSome _ _ _).symm.trans hw'
  have hcc : c'.ty = c.ty := by
    simpa [LExpr.typeCheckWith, LExpr.opsConsistent, LExpr.typeCheck, hw''] using htc
  have hnv : LExpr.isValue F.factory (.fvar m x ty : Expression.Expr) = false := by
    simp [LExpr.isValue.eq_def, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
  have hnc : F.factory.callOfLFunc (.fvar m x ty : Expression.Expr) = none := by
    simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
  refine computable_of_evalBounded hF hS hty (n := 1)
    (evalBounded_eq_some_iff.2 ⟨?_, ?_, hw', ?_⟩) fun _ => LConst.isPrimitive_of_ty hw'' hcc hcd
  · exact evalTypedDomain_fvar hr
      (by simpa [LExpr.typeCheck, hw'', isGroundTy_iff] using LConst.ty_isGround c')
  · simp only [LExpr.eval, hnv, hnc, LExpr.evalCore, hr, hv]
    rfl
  · exact evalOpsChecked_fvar hr rfl


/-- The bounded evaluator returns the literal `LExpr.eval` reduces `e` to, fully, when `e` is in
    the domain of the reference evaluator at the literal's type and passes the operator check. -/
private theorem evalBounded_of_eval {F : Expression.Factory} {σr : RStore Expression}
    {σ : SemanticStore Expression} {e : Expression.Expr} {n : Nat} {m : ExpressionMetadata}
    {c : LConst} (hS : StoreDenotes F σr σ)
    (hd : ValStore.Defines (T := CoreLParams) σ F.model.tcInterp e)
    (hty : (e.annotateFvars (ValStore.ann (T := CoreLParams) σ)).HasTypeA [] c.ty)
    (hops : evalOpsChecked F.factory σr e = true)
    (he : LExpr.eval n F.factory σr e = (.const m c, .value true)) (hw : c.wt = true) :
    evalBounded n F.factory σr e = some (.const m c) :=
  evalBounded_eq_some_iff.2 ⟨(evalTypedDomain_iff hS e).2
    ⟨_, LExpr.denoteEval_of_hasTypeA hd hty (LConst.ty_isGround c)⟩, he,
    typeCheckWith_const _ _ _ hw, hops⟩

/-- A conditional of computable expressions is computable. -/
theorem computableEval_ite (F : Expression.Factory) (hF : EvalFactoryWF F.factory)
    {σ : SemanticStore Expression} {m : ExpressionMetadata} {c t f : Expression.Expr}
    (hc : ComputableEval F σ c) (ht : ComputableEval F σ t) (hf : ComputableEval F σ f) :
    ComputableEval F σ (.ite m c t f) := by
  intro σr τ hS hd hty
  obtain ⟨htc, htt, htf⟩ := HasTypeA.ite_inv hty
  have hsub : ∀ {d : Expression.Expr}, (∀ x ∈ LExpr.LExpr.getVars d,
      x ∈ LExpr.LExpr.getVars (.ite m c t f : Expression.Expr)) →
      ValStore.Defines (T := CoreLParams) σ F.model.tcInterp d := fun h x hx => hd x (h x hx)
  obtain ⟨cc, hccd, hcc, -, n1, m1, h1⟩ := hc σr _ hS (hsub fun x hx => by
    simp [LExpr.LExpr.getVars, hx]) htc
  obtain ⟨ct, hctd, rfl, -, n2, m2, h2⟩ := ht σr _ hS (hsub fun x hx => by
    simp [LExpr.LExpr.getVars, hx]) htt
  obtain ⟨cf, hcfd, hcf, -, n3, m3, h3⟩ := hf σr _ hS (hsub fun x hx => by
    simp [LExpr.LExpr.getVars, hx]) htf
  obtain ⟨-, e1, -, o1⟩ := evalBounded_eq_some_iff.1 h1
  obtain ⟨-, e2, -, o2⟩ := evalBounded_eq_some_iff.1 h2
  obtain ⟨-, e3, -, o3⟩ := evalBounded_eq_some_iff.1 h3
  obtain ⟨b, rfl⟩ := LConst.eq_boolConst_of_ty (LConst.wt_of_isPrimitive hccd) hcc
  have hle : ∀ {k n : Nat} {d v : Expression.Expr}, k ≤ n →
      LExpr.eval k F.factory σr d = (v, .value true) →
      LExpr.eval n F.factory σr d = (v, .value true) :=
    fun hk h => eval_value_true_mono_le _ _ _ _ hk _ _ h
  have hops : evalOpsChecked F.factory σr (.ite m c t f) = true := by
    simp_all only [LExpr.LExpr.getVars, List.append_assoc, List.mem_append, implies_true,
        evalOpsChecked, Bool.and_eq_true, List.all_eq_true, opsInstantiated, Bool.and_self,
        List.all_append, Bool.true_and, and_self]
  have hnv : LExpr.isValue F.factory (.ite m c t f : Expression.Expr) = false := by
    simp [LExpr.isValue.eq_def, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
  have hnc : F.factory.callOfLFunc (.ite m c t f : Expression.Expr) = none := by
    simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
  have hc' := hle (n := n1 + n2 + n3) (by omega) e1
  have ht' := hle (n := n1 + n2 + n3) (by omega) e2
  have hf' := hle (n := n1 + n2 + n3) (by omega) e3
  cases b
  · refine computable_of_evalBounded hF hS hty (n := n1 + n2 + n3 + 1) (m := m3)
      (evalBounded_of_eval hS hd (hcf ▸ hty) hops ?_ (LConst.wt_of_isPrimitive hcfd))
      fun _ => hcfd
    simp only [LExpr.eval, hnv, hnc, LExpr.evalCore, LExpr.evalIte, hc', hf']
    rfl
  · refine computable_of_evalBounded hF hS hty (n := n1 + n2 + n3 + 1) (m := m2)
      (evalBounded_of_eval hS hd hty hops ?_ (LConst.wt_of_isPrimitive hctd))
      fun _ => hctd
    simp only [LExpr.eval, hnv, hnc, LExpr.evalCore, LExpr.evalIte, hc', ht']
    rfl


/-- The evaluator's equality test decides every equality of two primitive literals. -/
private theorem eql_const (F : Lambda.Factory CoreLParams) (m1 m2 : ExpressionMetadata)
    {c1 c2 : LConst} (h1 : c1.isPrimitive = true) (h2 : c2.isPrimitive = true) :
    ∃ b, LExpr.eql F (.const m1 c1 : Expression.Expr) (.const m2 c2) = some b := by
  rw [LExpr.eql.eq_def (T := ⟨⟨ExpressionMetadata, Unit⟩, LMonoTy⟩)]
  simp only [LConst.eql, LConst.eqDecidable_of_isPrimitive h1,
    LConst.eqDecidable_of_isPrimitive h2, Bool.and_self, ↓reduceIte]
  cases c1 == c2 <;> split <;> exact ⟨_, rfl⟩

/-- An equality of computable expressions is computable. -/
theorem computableEval_eq (F : Expression.Factory) (hF : EvalFactoryWF F.factory)
    {σ : SemanticStore Expression} {m : ExpressionMetadata} {a b : Expression.Expr}
    (ha : ComputableEval F σ a) (hb : ComputableEval F σ b) :
    ComputableEval F σ (.eq m a b) := by
  intro σr τ hS hd hty
  obtain ⟨τ', rfl, hta, htb⟩ := HasTypeA.eq_inv hty
  have hsub : ∀ {d : Expression.Expr}, (∀ x ∈ LExpr.LExpr.getVars d,
      x ∈ LExpr.LExpr.getVars (.eq m a b : Expression.Expr)) →
      ValStore.Defines (T := CoreLParams) σ F.model.tcInterp d := fun h x hx => hd x (h x hx)
  obtain ⟨ca, hca, -, -, n1, m1, h1⟩ := ha σr _ hS (hsub fun x hx => by
    simp [LExpr.LExpr.getVars, hx]) hta
  obtain ⟨cb, hcb, -, -, n2, m2, h2⟩ := hb σr _ hS (hsub fun x hx => by
    simp [LExpr.LExpr.getVars, hx]) htb
  obtain ⟨-, e1, -, o1⟩ := evalBounded_eq_some_iff.1 h1
  obtain ⟨-, e2, -, o2⟩ := evalBounded_eq_some_iff.1 h2
  have ha' := eval_value_true_mono_le _ _ _ (n1 + n2) (by omega) _ _ e1
  have hb' := eval_value_true_mono_le _ _ _ (n1 + n2) (by omega) _ _ e2
  have hops : evalOpsChecked F.factory σr (.eq m a b) = true := by
    simp_all only [LExpr.LExpr.getVars, List.mem_append, evalOpsChecked, Bool.and_eq_true,
        List.all_eq_true, opsInstantiated, Bool.and_self, List.all_append, Bool.true_and,
        implies_true, and_self]
  have hnv : LExpr.isValue F.factory (.eq m a b : Expression.Expr) = false := by
    simp [LExpr.isValue.eq_def, Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
  have hnc : F.factory.callOfLFunc (.eq m a b : Expression.Expr) = none := by
    simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go]
  obtain ⟨bv, hbv⟩ := eql_const F.factory m1 m2 hca hcb
  refine computable_of_evalBounded hF hS hty (n := n1 + n2 + 1) (m := m) (c := .boolConst bv)
    (evalBounded_of_eval hS hd hty hops ?_ rfl) fun _ => rfl
  simp only [LExpr.eval, hnv, hnc, LExpr.evalCore, LExpr.evalEq, ha', hb', hbv]
  rfl


/-- A call of a factory function at full arity is also one when partial applications are
    allowed. -/
private theorem callOfLFunc_partial {F : Lambda.Factory CoreLParams} {e : Expression.Expr} {x}
    (h : F.callOfLFunc e = some x) : F.callOfLFunc e true = some x := by
  simp only [Factory.callOfLFunc] at h ⊢
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> simp_all only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, Option.some.injEq,
      Nat.ble_self_eq_true, beq_eq_false_iff_ne, ne_eq, reduceCtorEq]

/-- A full-arity call of a factory function that is not a constructor is not a value. -/
private theorem isValue_call {F : Lambda.Factory CoreLParams} {e op : Expression.Expr}
    {args : List Expression.Expr} {fn : LFunc CoreLParams}
    (h : F.callOfLFunc e = some (op, args, fn)) (hc : fn.isConstr = false) :
    LExpr.isValue F e = false := by
  have hp := callOfLFunc_partial h
  have hl := Factory.callOfLFunc_arity h
  rw [LExpr.isValue.eq_def]
  split
  · simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h
  · simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h
  · simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h
  · split
    · rename_i hp'
      rw [hp] at hp'
      cases hp'
      simp [hc, hl]
    · rfl

/-- Equal arrow chains with argument lists of equal lengths have equal results and arguments. -/
private theorem mkArrow'_inj {a b : LMonoTy} : ∀ {xs ys : List LMonoTy},
    LMonoTy.mkArrow' a xs = LMonoTy.mkArrow' b ys → xs.length = ys.length → a = b ∧ xs = ys
  | [], [], h, _ => ⟨h, rfl⟩
  | x :: xs, y :: ys, h, hl => by
    simp only [LMonoTy.mkArrow', LMonoTy.arrow, LMonoTy.tcons.injEq, List.cons.injEq] at h
    obtain ⟨hab, hxy⟩ := mkArrow'_inj h.2.2.1 (by simpa using hl)
    exact ⟨hab, by rw [h.2.1, hxy]⟩

/-- The operator node and arguments of an application spine carry its `opsInstantiated` check
    and its free variables. -/
private theorem getLFuncCall_go_ops_vars (F : Lambda.Factory CoreLParams) (e : Expression.Expr)
    (acc : List Expression.Expr) :
    ((opsInstantiated F e && acc.all (opsInstantiated F)) =
      (opsInstantiated F (getLFuncCall.go e acc).1 &&
        (getLFuncCall.go e acc).2.all (opsInstantiated F))) ∧
    ∀ x, (x ∈ LExpr.LExpr.getVars e ∨ ∃ a ∈ acc, x ∈ LExpr.LExpr.getVars a) ↔
      (x ∈ LExpr.LExpr.getVars (getLFuncCall.go e acc).1 ∨
        ∃ a ∈ (getLFuncCall.go e acc).2, x ∈ LExpr.LExpr.getVars a) := by
  fun_induction getLFuncCall.go e acc
  · rename_i ih
    refine ⟨?_, fun x => ?_⟩
    · rw [← ih.1]
      simp only [opsInstantiated, List.cons_append, List.nil_append, List.all_cons]
      cases opsInstantiated F _ <;> cases opsInstantiated F _ <;> cases opsInstantiated F _ <;> rfl
    · rw [← ih.2]
      simp only [LExpr.LExpr.getVars, List.mem_append, List.cons_append, List.nil_append,
        List.mem_cons, exists_eq_or_imp]
      grind
  · refine ⟨?_, fun x => ?_⟩
    · simp only [opsInstantiated, List.cons_append, List.nil_append, List.all_cons, Bool.and_assoc]
    · simp [LExpr.LExpr.getVars]
  · exact ⟨rfl, fun _ => Iff.rfl⟩


/-- Arguments `LExpr.eval` reduces fully to the values `ls` are reduced to `ls`, every one fully. -/
private theorem eval_args_split {F : Lambda.Factory CoreLParams} {σr : RStore Expression}
    {N : Nat} : ∀ {args ls : List Expression.Expr},
    args.map (LExpr.eval N F σr) = ls.map (·, .value true) →
      List.map (fun a => (LExpr.eval N F σr a).fst) args = ls ∧
        (args.all fun a => (LExpr.eval N F σr a).snd.isValueTrue) = true
  | [], [], _ => ⟨rfl, rfl⟩
  | a :: args, l :: ls, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := eval_args_split h.2
    simp only [List.map_cons, h.1, h1, List.all_cons, h2, Bool.and_true]
    exact ⟨trivial, rfl⟩

/-- `LExpr.eval` of a call of an operator without a body, applied to arguments it reduces fully to
    the values `ls`, returns the literal the concrete evaluator gives on `ls`. -/
private theorem eval_call_ceval {F : Lambda.Factory CoreLParams} {σr : RStore Expression} {N : Nat}
    {e op : Expression.Expr} {args ls : List Expression.Expr} {fn : LFunc CoreLParams}
    {ceval : ConcreteEval CoreLParams} {m : ExpressionMetadata} {c : LConst}
    (hcall : F.callOfLFunc e = some (op, args, fn)) (hc : fn.isConstr = false)
    (hb : fn.body = none) (hsc : LExpr.shortCircuitCall? fn args = none)
    (hce : fn.concreteEval = some ceval)
    (hargs : args.map (LExpr.eval N F σr) = ls.map (·, .value true))
    (hlits : ls.all (LExpr.isValue F) = true)
    (hres : ceval (LExpr.mkApp e.metadata op ls).metadata op.opTy? ls = some (.const m c)) :
    LExpr.eval (N + 1) F σr e = (.const m c, .value true) := by
  obtain ⟨hmap, hall⟩ := eval_args_split hargs
  simp only [LExpr.eval, isValue_call hcall hc, hcall, hsc, LExpr.List_map_fst_map_eval,
    LExpr.List_all_snd_isValueTrue_map_eval, hmap, hall, hb, hlits, hce, hres,
    Option.isSome_none, Bool.false_and, Bool.true_or, Bool.false_eq_true, ↓reduceIte,
    ↓reduceDIte, eval_value_identity _ _ _ _ (isValue_const_true F m c),
    LExpr.combineEvalResValueFlag_eq_pair]
  rfl


/-- `LExpr.eval` of a call of a short-circuiting operator whose first argument it reduces fully to
    a value returns what it reduces the concrete evaluator's result to, when that is a literal. -/
private theorem eval_call_shortCircuit {F : Lambda.Factory CoreLParams} {σr : RStore Expression}
    {N : Nat} {e op a e' la : Expression.Expr} {rest : List Expression.Expr}
    {fn : LFunc CoreLParams} {ceval : ConcreteEval CoreLParams}
    {m : ExpressionMetadata} {c : LConst}
    (hcall : F.callOfLFunc e = some (op, a :: rest, fn)) (hc : fn.isConstr = false)
    (hsc : LExpr.shortCircuitCall? fn (a :: rest) = some (a, rest, ceval))
    (ha : LExpr.eval N F σr a = (la, .value true)) (hla : LExpr.isValue F la = true)
    (hres : ceval e.metadata op.opTy? (la :: rest) = some e')
    (he' : LExpr.eval N F σr e' = (.const m c, .value true)) :
    LExpr.eval (N + 1) F σr e = (.const m c, .value true) := by
  simp only [LExpr.eval, isValue_call hcall hc, hcall, hsc, LExpr.evalShortCircuit, ha, hla, hres,
    he', Bool.false_eq_true, ↓reduceIte, LExpr.combineEvalResValueFlag_eq_pair]
  rfl

/-- `LExpr.eval` of a call of a function it unfolds, applied to arguments it reduces fully to the
    values `ls`, returns what it reduces the instantiated body to, when that is a literal. -/
private theorem eval_call_body {F : Lambda.Factory CoreLParams} {σr : RStore Expression} {N : Nat}
    {e op body : Expression.Expr} {args ls : List Expression.Expr} {fn : LFunc CoreLParams}
    {S : Subst} {m : ExpressionMetadata} {c : LConst}
    (hcall : F.callOfLFunc e = some (op, args, fn)) (hc : fn.isConstr = false)
    (hb : fn.body = some body) (hsc : LExpr.shortCircuitCall? fn args = none)
    (hinl : (fn.attr.contains .inline ||
      Strata.DL.Util.FuncAttr.hasInlineIfAllValues fn.attr && ls.all (LExpr.isInlineArg F)) = true)
    (hS : fn.computeTypeSubst op ls = some S)
    (hargs : args.map (LExpr.eval N F σr) = ls.map (·, .value true))
    (hres : LExpr.eval N F σr ((body.applyTypeSubst S).substFvarsLifting (fn.inputs.keys.zip ls))
      = (.const m c, .value true)) :
    LExpr.eval (N + 1) F σr e = (.const m c, .value true) := by
  obtain ⟨hmap, hall⟩ := eval_args_split hargs
  have hcond : ((fn.body.isSome && ((fn.attr.contains .inline ||
      match Strata.DL.Util.FuncAttr.findInlineIfConstr fn.attr with
      | some i => (Option.map (LExpr.isConstrApp F) ls[i]?).getD false
      | none => false) ||
      Strata.DL.Util.FuncAttr.hasInlineIfAllValues fn.attr && ls.all (LExpr.isInlineArg F)))
      = true) := by
    rw [hb]
    revert hinl
    cases fn.attr.contains .inline <;> simp <;> grind
  simp only [LExpr.eval, isValue_call hcall hc, hcall, hsc, LExpr.List_map_fst_map_eval,
    LExpr.List_all_snd_isValueTrue_map_eval, hmap, hall, Bool.false_eq_true, ↓reduceIte,
    hS]
  have hg : ∀ h', fn.body.get h' = body := by rw [hb]; intro; rfl
  split
  · simp only [hg, hres, LExpr.combineEvalResValueFlag_eq_pair]
    rfl
  · rename_i h
    exact absurd hcond h


/-- `args` are primitive literals (`LConst.isPrimitive`) of the types `tys`, in order. -/
@[expose] def LitsOfTypes (args : List Expression.Expr) (tys : List LMonoTy) : Prop :=
  List.Rel₂ (fun a ty => ∃ m c, a = .const m c ∧ LConst.ty c = ty ∧ c.isPrimitive = true)
    args tys

/-- `List.Rel₂` is monotone in its relation on the members of its first list. -/
private theorem _root_.List.Rel₂.imp_mem {α β} {R S : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, (∀ a ∈ l, ∀ b, R a b → S a b) → List.Rel₂ R l l' →
      List.Rel₂ S l l'
  | _, _, _, .nil => .nil
  | _, _, h, .cons hab hrest =>
    .cons (h _ (List.mem_cons_self ..) _ hab)
      (List.Rel₂.imp_mem (fun a ha => h a (List.mem_cons_of_mem _ ha)) hrest)

/-- `List.Rel₂` of a mapped first list relates the original list by the composed relation. -/
private theorem _root_.List.Rel₂.of_map {α β γ} {R : β → γ → Prop} {f : α → β} :
    ∀ {l : List α} {l' : List γ}, List.Rel₂ R (l.map f) l' → List.Rel₂ (fun a b => R (f a) b) l l'
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h hr => .cons h (List.Rel₂.of_map hr)

/-- The argument values the bounded evaluator commits as literals are reached together at every
    large enough fuel by `LExpr.eval`. -/
private theorem args_lits {F : Lambda.Factory CoreLParams} {σr : RStore Expression} :
    ∀ {args : List Expression.Expr} {tys : List LMonoTy},
      List.Rel₂ (fun a ty => ∃ n m c, LConst.ty c = ty ∧ c.isPrimitive = true ∧
        evalBounded n F σr a = some (.const m c)) args tys →
      ∃ N ls, LitsOfTypes ls tys ∧
        ∀ k, N ≤ k → args.map (LExpr.eval k F σr) = ls.map (·, .value true)
  | _, _, .nil => ⟨0, [], .nil, fun _ _ => rfl⟩
  | _, _, .cons ⟨n, m, c, hc, hcd, h⟩ hrest => by
    obtain ⟨N, ls, hls, hk⟩ := args_lits hrest
    obtain ⟨-, he, -⟩ := evalBounded_eq_some_iff.1 h
    refine ⟨n + N, .const m c :: ls, .cons ⟨m, c, rfl, hc, hcd⟩ hls, fun k hk' => ?_⟩
    simp only [List.map_cons, eval_value_true_mono_le _ _ _ k (by omega) _ _ he,
      hk k (by omega)]

/-- The operator node and arguments of a call carry its operator check and free variables. -/
private theorem call_ops_vars {F : Lambda.Factory CoreLParams} {e op : Expression.Expr}
    {args : List Expression.Expr} {fn : LFunc CoreLParams}
    (hcall : F.callOfLFunc e = some (op, args, fn)) :
    opsInstantiated F e = (opsInstantiated F op && args.all (opsInstantiated F)) ∧
      ∀ x, x ∈ LExpr.LExpr.getVars e ↔ ∃ a ∈ args, x ∈ LExpr.LExpr.getVars a := by
  have hg := callOfLFunc_getLFuncCall hcall
  obtain ⟨m, name, ty, rfl, -⟩ := Factory.callOfLFunc_getElem? hcall
  simp only [getLFuncCall] at hg
  have h := getLFuncCall_go_ops_vars F e []
  rw [hg] at h
  refine ⟨by simpa using h.1, fun x => ?_⟩
  simpa [LExpr.LExpr.getVars] using h.2 x

/-- The guard's operator check holds on a call whose operator node passes `opsInstantiated` and
    whose arguments pass the check. -/
private theorem evalOpsChecked_call {F : Lambda.Factory CoreLParams} {σr : RStore Expression}
    {e op : Expression.Expr} {args : List Expression.Expr} {fn : LFunc CoreLParams}
    (hcall : F.callOfLFunc e = some (op, args, fn)) (hop : opsInstantiated F op = true)
    (hargs : ∀ a ∈ args, evalOpsChecked F σr a = true) : evalOpsChecked F σr e = true := by
  obtain ⟨ho, hv⟩ := call_ops_vars hcall
  simp only [evalOpsChecked, Bool.and_eq_true, List.all_eq_true] at hargs ⊢
  refine ⟨by simp only [ho, hop, Bool.true_and, List.all_eq_true]; exact fun a ha => (hargs a ha).1,
    fun x hx => ?_⟩
  obtain ⟨a, ha, hxa⟩ := (hv x).1 hx
  exact (hargs a ha).2 x hxa

/-- On a call of a monomorphic function whose operator node is annotated with the function's
    type, every typing of the call is at the function's output type, its arguments typed at the
    input types. -/
private theorem call_types {F : Lambda.Factory CoreLParams} {A : CoreIdent → Option LMonoTy}
    {e op : Expression.Expr} {args : List Expression.Expr} {fn : LFunc CoreLParams}
    {τ : LMonoTy} (hcall : F.callOfLFunc e = some (op, args, fn)) (hmono : fn.typeArgs = [])
    (hop : opsInstantiated F op = true) (hty : (e.annotateFvars A).HasTypeA [] τ) :
    τ = fn.output ∧
      List.Rel₂ (fun a ty => (a.annotateFvars A).HasTypeA [] ty) args (fn.inputs.map Prod.snd) := by
  have hca : F.callOfLFunc (e.annotateFvars A) = some (op,
      args.map (·.annotateFvars A), fn) := by
    rw [callOfLFunc_annotateFvars F A e false, hcall]
    rfl
  obtain ⟨m', name', ty', rfl, hget⟩ := Factory.callOfLFunc_getElem? hcall
  obtain ⟨argTys, tyOp, m, name, hop', hrel, htyOp, hlen⟩ := callOfLFunc_output_type hca hty
  injection hop' with _ hn ht
  subst hn ht
  simp only [opsInstantiated, hget, LFunc.opTypeSubst, hmono, List.isEmpty_nil, ↓reduceIte,
    beq_iff_eq, LMonoTy.subst, Subst.hasEmptyScopes_empty] at hop
  obtain ⟨h1, h2⟩ := mkArrow'_inj (htyOp.symm.trans hop) (by
    rw [← hrel.length_eq]
    exact hlen.trans
      (List.length_map (as := (fn.inputs : List (CoreIdent × LMonoTy))) Prod.snd).symm)
  exact ⟨h1, List.Rel₂.of_map (h2 ▸ hrel)⟩


/-- The concrete evaluator `ceval` of `fn` computes every call on primitive literals of `fn`'s
    input types, at every operator annotation, as a primitive literal of its output type. -/
@[expose] def CevalTotal (fn : LFunc CoreLParams) (ceval : ConcreteEval CoreLParams) : Prop :=
  ∀ md ty args, LitsOfTypes args (fn.inputs.map Prod.snd) →
    ∃ m c, ceval md ty args = some (.const m c) ∧ LConst.ty c = fn.output ∧
      c.isPrimitive = true

/-- The concrete evaluator `ceval` of the short-circuiting connective `fn`, whose inputs and output
    have one type: on a primitive literal first argument, at every operator annotation, it returns
    a primitive literal of that type or one of the remaining arguments, whatever they are. -/
@[expose] def CevalShortCircuits (fn : LFunc CoreLParams) (ceval : ConcreteEval CoreLParams) :
    Prop :=
  fn.inputs ≠ [] ∧ (∀ ty ∈ fn.inputs.map Prod.snd, ty = fn.output) ∧
    ∀ md ty a rest, LitsOfTypes [a] [fn.output] → rest.length + 1 = fn.inputs.length →
      ∃ e', ceval md ty (a :: rest) = some e' ∧
        ((∃ m c, e' = .const m c ∧ LConst.ty c = fn.output ∧ c.isPrimitive = true) ∨
          e' ∈ rest)

/-- **A factory operator the evaluator computes on literals**: monomorphic, not a constructor,
    without a body, with a concrete evaluator that computes every call on literals: by
    `CevalShortCircuits` when the operator short-circuits, by `CevalTotal` otherwise. -/
structure ComputableOp (fn : LFunc CoreLParams) : Prop where
  /-- The operator has no type arguments. -/
  mono : fn.typeArgs = []
  /-- The operator is not a constructor. -/
  notConstr : fn.isConstr = false
  /-- The operator has no body. -/
  noBody : fn.body = none
  /-- The operator's concrete evaluator computes every call on literals. -/
  eval : ∃ ceval, fn.concreteEval = some ceval ∧
    (if Strata.DL.Util.FuncAttr.hasShortCircuit fn.attr then CevalShortCircuits fn ceval
     else CevalTotal fn ceval)

/-- A member of a list of literals of the types `tys` is a literal of one of them. -/
theorem LitsOfTypes.mem {ls : List Expression.Expr} {tys : List LMonoTy}
    (h : LitsOfTypes ls tys) {l : Expression.Expr} (hl : l ∈ ls) :
    ∃ m c, l = .const m c ∧ LConst.ty c ∈ tys ∧ c.isPrimitive = true := by
  obtain ⟨ty, hty, m, c, rfl, hc, hcd⟩ := List.Rel₂.exists_of_mem_left h hl
  exact ⟨m, c, rfl, hc ▸ hty, hcd⟩

/-- Literals are values. -/
private theorem LitsOfTypes.all_isValue {F : Lambda.Factory CoreLParams} {ls : List Expression.Expr}
    {tys : List LMonoTy} (h : LitsOfTypes ls tys) : ls.all (LExpr.isValue F) = true :=
  List.all_eq_true.2 fun l hl => by
    obtain ⟨m, c, rfl, -, -⟩ := h.mem hl
    exact isValue_const_true F m c

/-- The facts the closure of computable evaluation under calls gathers from the arguments. -/
private theorem call_args_facts (F : Expression.Factory) {σ : SemanticStore Expression}
    {σr : RStore Expression} {e op : Expression.Expr} {args : List Expression.Expr}
    {fn : LFunc CoreLParams} {τ : LMonoTy} (hS : StoreDenotes F σr σ)
    (hcall : F.factory.callOfLFunc e = some (op, args, fn)) (hmono : fn.typeArgs = [])
    (hop : opsInstantiated F.factory op = true) (hargs : ∀ a ∈ args, ComputableEval F σ a)
    (hd : ValStore.Defines (T := CoreLParams) σ F.model.tcInterp e)
    (hty : (e.annotateFvars (ValStore.ann (T := CoreLParams) σ)).HasTypeA [] τ) :
    τ = fn.output ∧ evalOpsChecked F.factory σr e = true ∧
      ∃ N ls, LitsOfTypes ls (fn.inputs.map Prod.snd) ∧
        ∀ k, N ≤ k → args.map (LExpr.eval k F.factory σr) = ls.map (·, .value true) := by
  obtain ⟨hτ, hrel⟩ := call_types hcall hmono hop hty
  have hv := (call_ops_vars hcall).2
  have hdef : ∀ a ∈ args, ValStore.Defines (T := CoreLParams) σ F.model.tcInterp a :=
    fun a ha x hx => hd x ((hv x).2 ⟨a, ha, hx⟩)
  have hlits := hrel.imp_mem (S := fun a ty => ∃ n m c, LConst.ty c = ty ∧
      c.isPrimitive = true ∧ evalBounded n F.factory σr a = some (.const m c)) fun a ha ty h => by
    obtain ⟨c, hcd, hc, -, n, m, hb⟩ := hargs a ha σr ty hS (hdef a ha) h
    exact ⟨n, m, c, hc, hcd, hb⟩
  refine ⟨hτ, evalOpsChecked_call hcall hop fun a ha => ?_, args_lits hlits⟩
  obtain ⟨ty, -, n, m, c, -, -, hb⟩ := hlits.exists_of_mem_left ha
  exact (evalBounded_eq_some_iff.1 hb).2.2.2

/-- A call of an operator the evaluator computes on literals (`ComputableOp`), annotated with an
    instance of its type (`opsInstantiated`), on computable arguments is computable. -/
theorem computableEval_op (F : Expression.Factory) (hF : EvalFactoryWF F.factory)
    {σ : SemanticStore Expression} {e op : Expression.Expr} {args : List Expression.Expr}
    {fn : LFunc CoreLParams} (hcall : F.factory.callOfLFunc e = some (op, args, fn))
    (hfn : ComputableOp fn) (hop : opsInstantiated F.factory op = true)
    (hargs : ∀ a ∈ args, ComputableEval F σ a) : ComputableEval F σ e := by
  intro σr τ hS hd hty
  obtain ⟨rfl, hops, N, ls, hls, hk⟩ := call_args_facts F hS hcall hfn.mono hop hargs hd hty
  obtain ⟨ceval, hce, hcases⟩ := hfn.eval
  cases hsc : Strata.DL.Util.FuncAttr.hasShortCircuit fn.attr
  · rw [hsc] at hcases
    obtain ⟨m, c, hres, hct, hcd⟩ :=
      hcases (LExpr.mkApp e.metadata op ls).metadata op.opTy? ls hls
    refine computable_of_evalBounded hF hS hty (n := N + 1) (m := m)
      (evalBounded_of_eval hS hd (hct ▸ hty) hops ?_ (LConst.wt_of_isPrimitive hcd))
      fun _ => hcd
    exact eval_call_ceval hcall hfn.notConstr hfn.noBody (by simp [LExpr.shortCircuitCall?, hsc])
      hce (hk N (Nat.le_refl _)) hls.all_isValue hres
  · rw [hsc] at hcases
    obtain ⟨hne, hall, htot⟩ := hcases
    have hlen := Factory.callOfLFunc_arity hcall
    obtain ⟨a, rest, rfl⟩ : ∃ a rest, args = a :: rest := by
      cases args with
      | nil => exact absurd (List.length_eq_zero_iff.1 hlen.symm) hne
      | cons a rest => exact ⟨a, rest, rfl⟩
    have hkN := hk N (Nat.le_refl _)
    obtain ⟨la, ls', rfl⟩ : ∃ la ls', ls = la :: ls' := by
      cases ls with
      | nil => cases hkN
      | cons la ls' => exact ⟨la, ls', rfl⟩
    simp only [List.map_cons, List.cons.injEq] at hkN
    have hla : LitsOfTypes [la] [fn.output] := by
      obtain ⟨m, c, rfl, hc, hcd⟩ := hls.mem List.mem_cons_self
      exact .cons ⟨m, c, rfl, hall _ hc, hcd⟩ .nil
    obtain ⟨e', hres, he'⟩ := htot e.metadata op.opTy? la rest hla (by simpa using hlen)
    obtain ⟨m, c, he'', hct, hcd⟩ : ∃ m c,
        LExpr.eval N F.factory σr e' = (.const m c, .value true) ∧
        LConst.ty c = fn.output ∧ c.isPrimitive = true := by
      rcases he' with ⟨m, c, rfl, hc, hcd⟩ | hmem
      · exact ⟨m, c, eval_value_identity _ _ _ _ (isValue_const_true _ m c), hc, hcd⟩
      · have hm := List.mem_map_of_mem (f := LExpr.eval N F.factory σr) hmem
        rw [hkN.2] at hm
        obtain ⟨l, hl, hl'⟩ := List.mem_map.1 hm
        obtain ⟨m, c, rfl, hc, hcd⟩ := hls.mem (List.mem_cons_of_mem _ hl)
        exact ⟨m, c, hl'.symm, hall _ hc, hcd⟩
    obtain ⟨m', c', hla'⟩ : ∃ m c, la = .const m c := by
      obtain ⟨m, c, rfl, -⟩ := hls.mem List.mem_cons_self
      exact ⟨m, c, rfl⟩
    refine computable_of_evalBounded hF hS hty (n := N + 1) (m := m)
      (evalBounded_of_eval hS hd (hct ▸ hty) hops ?_ (LConst.wt_of_isPrimitive hcd))
      fun _ => hcd
    exact eval_call_shortCircuit hcall hfn.notConstr
      (by simp [LExpr.shortCircuitCall?, hsc, hce]) hkN.1
      (hla' ▸ isValue_const_true _ m' c') hres he''


/-- A body that reads only the parameters `ks` has no free variable once the parameters are
    replaced by literals. -/
theorem getVars_inline_nil {body : Expression.Expr} {ks : List CoreIdent}
    {ls : List Expression.Expr} {tys : List LMonoTy}
    (hvars : ∀ x ∈ LExpr.LExpr.getVars body, x ∈ ks) (hlen : ks.length = ls.length)
    (hls : LitsOfTypes ls tys) :
    LExpr.LExpr.getVars (body.substFvarsLifting (ks.zip ls)) = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 fun y hy => ?_
  rcases getVars_substFvarsLifting_mem _ _ _ hy with ⟨hb, hn⟩ | ⟨k, v, hf, hv⟩
  · refine Map_find?_ne_none_of_mem_keys (ks.zip ls : Map CoreIdent Expression.Expr) y ?_ hn
    rw [Map.keys_eq_map_fst (ks.zip ls : Map CoreIdent Expression.Expr)]
    exact (List.map_fst_zip (Nat.le_of_eq hlen)).symm ▸ hvars y hb
  · have hm := Map_find?_some_mem_values _ k v hf
    rw [List.map_snd_zip (Nat.le_of_eq hlen.symm)] at hm
    obtain ⟨m, c, rfl, -, -⟩ := hls.mem hm
    simp [LExpr.LExpr.getVars] at hv

/-- The body of a well-typed factory function, its parameters replaced by literals of their
    types, is well typed at the function's output type. -/
private theorem inline_hasType {F : Lambda.Factory CoreLParams} (hF : EvalFactoryWF F)
    {name : String} {fn : LFunc CoreLParams} {body : Expression.Expr}
    {ls : List Expression.Expr} (hget : F[name]? = some fn) (hb : fn.body = some body)
    (hls : LitsOfTypes ls (fn.inputs.map Prod.snd)) :
    (body.substFvarsLifting (fn.inputs.keys.zip ls)).HasTypeA [] fn.output := by
  have hwt := ((hF.1 : Factory.EvalSoundWFS F).step []).wt name
    (Factory.getElem?_some_implies_mem hget) body
  rw [Factory.getElem?_some_getElem hget] at hwt
  obtain ⟨hty, hann⟩ := hwt hb
  have hlen : fn.inputs.keys.length = ls.length := by
    rw [ListMap.keys.length, hls.length_eq]
    exact (List.length_map (as := (fn.inputs : List (CoreIdent × LMonoTy))) Prod.snd).symm
  refine substFvarsLifting_typeCheck (tys := fn.inputs.map Prod.snd) ?_ ?_ hty
  · rw [List.map_snd_zip (Nat.le_of_eq hlen.symm)]
    exact hls.imp fun a ty ⟨m, c, h, hc, hcd⟩ =>
      h ▸ hc ▸ .const (LConst.wt_of_isPrimitive hcd)
  · rw [List.map_fst_zip (Nat.le_of_eq hlen), ListMap.keys_eq_map_fst]
    have hz : ∀ l : List (CoreIdent × LMonoTy), (l.map Prod.fst).zip (l.map Prod.snd) = l :=
      fun l => by rw [← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]
    exact (hz fn.inputs).symm ▸ hann


/-- A call of a monomorphic user function the evaluator unfolds (`inline` or `inlineIfAllValues`,
    with a body and no concrete evaluator, not a constructor), annotated with an instance of its
    type, on computable arguments, is computable when its body reads only its parameters and is
    computable once they are replaced by literals of their types. -/
theorem computableEval_userFn (F : Expression.Factory) (hF : EvalFactoryWF F.factory)
    {σ : SemanticStore Expression} {e op body : Expression.Expr} {args : List Expression.Expr}
    {fn : LFunc CoreLParams} (hcall : F.factory.callOfLFunc e = some (op, args, fn))
    (hmono : fn.typeArgs = []) (hc : fn.isConstr = false) (hce : fn.concreteEval = none)
    (hb : fn.body = some body)
    (hinl : (fn.attr.contains .inline ||
      Strata.DL.Util.FuncAttr.hasInlineIfAllValues fn.attr) = true)
    (hvars : ∀ x ∈ LExpr.LExpr.getVars body, x ∈ fn.inputs.keys)
    (hop : opsInstantiated F.factory op = true) (hargs : ∀ a ∈ args, ComputableEval F σ a)
    (hbody : ∀ ls, LitsOfTypes ls (fn.inputs.map Prod.snd) →
      ComputableEval F σ (body.substFvarsLifting (fn.inputs.keys.zip ls))) :
    ComputableEval F σ e := by
  intro σr τ hS hd hty
  obtain ⟨rfl, hops, N, ls, hls, hk⟩ := call_args_facts F hS hcall hmono hop hargs hd hty
  obtain ⟨m', name, ty', rfl, hget⟩ := Factory.callOfLFunc_getElem? hcall
  have hlen : fn.inputs.keys.length = ls.length := by
    rw [ListMap.keys.length, hls.length_eq]
    exact (List.length_map (as := (fn.inputs : List (CoreIdent × LMonoTy))) Prod.snd).symm
  have hclosed := getVars_inline_nil hvars hlen hls
  have hann : (body.substFvarsLifting (fn.inputs.keys.zip ls)).annotateFvars
      (ValStore.ann (T := CoreLParams) σ) = body.substFvarsLifting (fn.inputs.keys.zip ls) :=
    annotateFvars_of_getVars_nil _ hclosed
  obtain ⟨c, hcd, hct, -, n', m, hbi⟩ := hbody ls hls σr _ hS
    (fun x hx => by simp [hclosed] at hx) (hann ▸ inline_hasType hF hget hb hls)
  obtain ⟨-, hei, -⟩ := evalBounded_eq_some_iff.1 hbi
  refine computable_of_evalBounded hF hS hty (n := N + n' + 1) (m := m)
    (evalBounded_of_eval hS hd (hct ▸ hty) hops ?_ (LConst.wt_of_isPrimitive hcd))
      fun _ => hcd
  refine eval_call_body (S := Subst.empty) hcall hc hb (by simp [LExpr.shortCircuitCall?, hce])
    ?_ (by simp [LFunc.computeTypeSubst, LFunc.opTypeSubst, hmono]) (hk _ (by omega)) ?_
  · have hia : ls.all (LExpr.isInlineArg F.factory) = true := List.all_eq_true.2 fun l hl => by
      obtain ⟨m, c, rfl, -, -⟩ := hls.mem hl
      simp [LExpr.isInlineArg]
    simpa [hia] using hinl
  · simpa [LExpr.applyTypeSubst] using eval_value_true_mono_le _ _ _ _ (by omega) _ _ hei


/-- **Computable evaluation gives the reach fact**: the engine reaches the reference value of a
    computable expression (`EngEvalReach`). -/
theorem engEvalReach_of_computableEval {F : Expression.Factory} {σ : SemanticStore Expression}
    {e : Expression.Expr} (h : ComputableEval F σ e) : EngEvalReach Expression F σ e := by
  intro σr v hS hv
  obtain ⟨hd, τ, hτ, -, -⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).1 hv
  obtain ⟨c, -, -, hc, n, m, hb⟩ := h σr τ hS hd hτ
  have hw : c.wt = true := by
    have hck := (evalBounded_eq_some_iff.1 hb).2.2.1
    rwa [typeCheckWith_const_isSome] at hck
  exact ⟨n, _, hb, (Option.some.inj (hc.symm.trans hv)) ▸
    denotes_literal (LExpr.denoteEval_const hw)⟩

end
end Core
