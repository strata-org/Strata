/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InterpreterReachBuiltins
import all Strata.Languages.Core.InterpreterReach
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.LExpr
import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.DL.Imperative.CmdSemanticsProps
import all Strata.Languages.Core.Factory
import all Strata.Languages.Core.FactoryEvalSoundWF
public import Strata.Languages.Core.Logic.FactoryInterp
import all Strata.Languages.Core.Logic.FactoryInterp

/-! # A static criterion on Core programs for computable evaluation

A decidable criterion on Core programs under which every reference run is replayed by the engine
(reference ⇒ engine):
* the *computable fragment* of expressions (`FragmentExpr`, decided by `fragmentExpr`):
  literals, variables, conditionals, equalities, and calls, annotated with an instance of their
  type, of the functions of the fragment (`fragmentFns`): built-in operators computed on literals
  (`isComputableBuiltinFn`) and user functions the evaluator unfolds whose bodies read only their
  parameters and are in the fragment relative to the functions before them (`userFnInFragment`);
* the statements and procedures of the fragment (`CmdInFragment`, `StmtInFragment`,
  `BlockInFragment`, `ConfigInFragment`, `ProcInFragment`, decided by their lower-case
  counterparts): every `init` type is a type of literals (`isLitTy`), and every deterministic
  guard, right-hand side, assertion and cover condition, call argument and specification clause
  is in the computable fragment, and so is every guard of a conditional transfer of a CFG body
  (`TransferInFragment`, `CFGInFragment`);
* the criterion `programInFragment`, read by `programInFragment_iff`.

Excluded, with the reason: quantifiers and abstractions (the evaluator does not decide them);
bound variables; maps, sets, sequences, real arithmetic, regular expressions and uninterpreted
functions (no concrete evaluator); division, remainder and shifts (guarded concrete evaluators);
polymorphic operators and datatypes (values of literal types only); user functions without
`inline` or `inlineIfAllValues` or calling later functions (not unfolded, or possibly recursive);
`init` of a non-literal type.

On a factory meeting `FragmentFactoryWF` (program factories do:
`fragmentFactoryWF_of_userFuncs`), the expressions of the fragment are computable on stores of
literals (`computableEval_of_inFragment`), programs of the fragment keep stores of literals along
their runs, so every expression they evaluate is computable (`evalsComputable_of_inFragment`),
and every event they emit has a computable condition (`run_events_inFragment`).

Key theorems: `fragmentExpr_iff`, `inFragment_iff`, `stmtInFragment_iff`,
`programInFragment_iff`, `fragmentFns_sound`, `computableEval_of_inFragment`,
`evalsComputable_of_inFragment`, and the completeness corollaries
`core_replayComplete_of_programInFragment`,
`core_replayComplete_of_deterministic_programInFragment`,
`core_runCoreInterp_complete_eval_of_programInFragment`. -/

namespace Core

open Imperative Lambda

public section

/-! ## The computable fragment of expressions -/

/-- **The computable fragment of expressions** of the factory `F`, relative to a predicate `ok` on
    its functions: primitive literals (`LConst.isPrimitive`), variables, conditionals, equalities,
    and calls of functions `ok` admits, their operator annotated with an instance of its type
    (`opsInstantiated`). Map and sequence literals, binders (`abs`, quantifiers), bound
    variables, and calls of other functions are excluded. -/
inductive FragmentExpr (F : Lambda.Factory CoreLParams) (ok : LFunc CoreLParams → Prop) :
    Expression.Expr → Prop where
  /-- A primitive literal. -/
  | const (m : ExpressionMetadata) (c : LConst) : c.isPrimitive = true →
      FragmentExpr F ok (.const m c)
  /-- A variable. -/
  | fvar (m : ExpressionMetadata) (x : CoreIdent) (ty : Option LMonoTy) :
      FragmentExpr F ok (.fvar m x ty)
  /-- A conditional. -/
  | ite {m : ExpressionMetadata} {c t f : Expression.Expr} : FragmentExpr F ok c →
      FragmentExpr F ok t → FragmentExpr F ok f → FragmentExpr F ok (.ite m c t f)
  /-- An equality. -/
  | eq {m : ExpressionMetadata} {a b : Expression.Expr} : FragmentExpr F ok a →
      FragmentExpr F ok b → FragmentExpr F ok (.eq m a b)
  /-- A call of a function `ok` admits. -/
  | call {e op : Expression.Expr} {args : List Expression.Expr} {fn : LFunc CoreLParams} :
      F.callOfLFunc e = some (op, args, fn) → ok fn → opsInstantiated F op = true →
      (∀ a ∈ args, FragmentExpr F ok a) → FragmentExpr F ok e

/-- The arguments of a call of a factory function are smaller than the call. -/
theorem callOfLFunc_args_smaller {F : Lambda.Factory CoreLParams} {e op : Expression.Expr}
    {args : List Expression.Expr} {fn : LFunc CoreLParams}
    (h : F.callOfLFunc e = some (op, args, fn)) : ∀ a ∈ args, a.sizeOf < e.sizeOf :=
  Factory.callOfLFunc_smaller (T := CoreLParams.mono) h

/-- The decision procedure for the computable fragment (`FragmentExpr`), relative to a Boolean
    test `ok` on functions. -/
@[expose] def fragmentExpr (F : Lambda.Factory CoreLParams) (ok : LFunc CoreLParams → Bool)
    (e : Expression.Expr) : Bool :=
  match e with
  | .const _ c => c.isPrimitive
  | .fvar _ _ _ => true
  | .ite _ c t f => fragmentExpr F ok c && fragmentExpr F ok t && fragmentExpr F ok f
  | .eq _ a b => fragmentExpr F ok a && fragmentExpr F ok b
  | e' =>
    match h : F.callOfLFunc e' with
    | some (op, args, fn) => ok fn && opsInstantiated F op &&
        args.attach.all fun ⟨a, ha⟩ =>
          have : a.sizeOf < e'.sizeOf := callOfLFunc_args_smaller h a ha
          fragmentExpr F ok a
    | none => false
  termination_by e.sizeOf
  decreasing_by all_goals first | (simp_wf; omega) | assumption

/-- A call of a factory function is not a literal, variable, conditional or equality. -/
private theorem callOfLFunc_shape {F : Lambda.Factory CoreLParams} {e op : Expression.Expr}
    {args : List Expression.Expr} {fn : LFunc CoreLParams}
    (h : F.callOfLFunc e = some (op, args, fn)) :
    (∀ m c, e ≠ .const m c) ∧ (∀ m x ty, e ≠ .fvar m x ty) ∧
      (∀ m c t f, e ≠ .ite m c t f) ∧ ∀ m a b, e ≠ .eq m a b := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rintro rfl <;>
    simp [Factory.callOfLFunc, getLFuncCall, getLFuncCall.go] at h

/-- **The fragment check decides the computable fragment**: `fragmentExpr F ok e` holds exactly
    when `e` is in the computable fragment relative to the functions `ok` admits. -/
theorem fragmentExpr_iff (F : Lambda.Factory CoreLParams) (ok : LFunc CoreLParams → Bool)
    (e : Expression.Expr) : fragmentExpr F ok e = true ↔ FragmentExpr F (ok · = true) e := by
  induction e using fragmentExpr.induct F with
  | case1 m c =>
    rw [fragmentExpr]
    refine ⟨.const m c, fun h => ?_⟩
    cases h with
    | const _ _ hc => exact hc
    | call hcall => exact absurd rfl ((callOfLFunc_shape hcall).1 _ _)
  | case2 m x ty => exact ⟨fun _ => .fvar m x ty, fun _ => by simp [fragmentExpr]⟩
  | case3 m c t f ihc iht ihf =>
    rw [fragmentExpr]
    simp only [Bool.and_eq_true, ihc, iht, ihf]
    refine ⟨fun ⟨⟨hc, ht⟩, hf⟩ => .ite hc ht hf, fun h => ?_⟩
    cases h with
    | ite hc ht hf => exact ⟨⟨hc, ht⟩, hf⟩
    | call hcall => exact absurd rfl ((callOfLFunc_shape hcall).2.2.1 _ _ _ _)
  | case4 m a b iha ihb =>
    rw [fragmentExpr]
    simp only [Bool.and_eq_true, iha, ihb]
    refine ⟨fun ⟨ha, hb⟩ => .eq ha hb, fun h => ?_⟩
    cases h with
    | eq ha hb => exact ⟨ha, hb⟩
    | call hcall => exact absurd rfl ((callOfLFunc_shape hcall).2.2.2 _ _ _)
  | case5 e hc hf hi heq op args fn hcall ih =>
    rw [fragmentExpr.eq_def]
    split
    · exact absurd rfl (hc _ _)
    · exact absurd rfl (hf _ _ _)
    · exact absurd rfl (hi _ _ _ _)
    · exact absurd rfl (heq _ _ _)
    · split
      · rename_i op' args' fn' hcall'
        obtain ⟨rfl, rfl, rfl⟩ : op = op' ∧ args = args' ∧ fn = fn' := by
          simpa using hcall.symm.trans hcall'
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_attach, true_implies,
          Subtype.forall]
        refine ⟨fun ⟨⟨hok, hop⟩, ha⟩ => .call hcall hok hop fun a h => (ih a h).1 (ha a h),
          fun h => ?_⟩
        cases h with
        | call hcall'' hok hop ha =>
          obtain ⟨rfl, rfl, rfl⟩ : op = _ ∧ args = _ ∧ fn = _ := by
            simpa using hcall.symm.trans hcall''
          exact ⟨⟨hok, hop⟩, fun a h => (ih a h).2 (ha a h)⟩
        | _ => first | exact absurd rfl (hc _ _) | exact absurd rfl (hf _ _ _) |
            exact absurd rfl (hi _ _ _ _) | exact absurd rfl (heq _ _ _)
      · rename_i hn
        exact absurd (hn.symm.trans hcall) nofun
  | case6 e hc hf hi heq hcall =>
    rw [fragmentExpr.eq_def]
    split
    · exact absurd rfl (hc _ _)
    · exact absurd rfl (hf _ _ _)
    · exact absurd rfl (hi _ _ _ _)
    · exact absurd rfl (heq _ _ _)
    · split
      · rename_i hs
        exact absurd (hcall.symm.trans hs) nofun
      · refine ⟨nofun, fun h => ?_⟩
        cases h with
        | call hcall' => exact absurd (hcall.symm.trans hcall') nofun
        | _ => first | exact absurd rfl (hc _ _) | exact absurd rfl (hf _ _ _) |
            exact absurd rfl (hi _ _ _ _) | exact absurd rfl (heq _ _ _)

/-! ## Computable expression evaluation on the fragment -/

/-- A user function the evaluator computes on literals: monomorphic, not a constructor, without a
    concrete evaluator, unfolded by the evaluator (`inline` or `inlineIfAllValues`), with a body
    that reads only its parameters and is computable, at every store, once they are replaced by
    literals of their types. -/
@[expose] def UserFnComputable (F : Expression.Factory) (fn : LFunc CoreLParams) : Prop :=
  fn.typeArgs = [] ∧ fn.isConstr = false ∧ fn.concreteEval = none ∧
    (fn.attr.contains .inline || Strata.DL.Util.FuncAttr.hasInlineIfAllValues fn.attr) = true ∧
    ∃ body, fn.body = some body ∧ (∀ x ∈ LExpr.LExpr.getVars body, x ∈ fn.inputs.keys) ∧
      ∀ σ ls, LitsOfTypes ls (fn.inputs.map Prod.snd) →
        ComputableEval F σ (body.substFvarsLifting (fn.inputs.keys.zip ls))

/-- **Computable evaluation on the fragment**: at a modeled factory meeting `EvalFactoryWF` none
    of whose constructors produces a value of a literal type, an expression of the computable
    fragment whose functions are computed on literals (`ComputableOp`, `UserFnComputable`) is
    computable on every store binding its variables to values of literals. -/
theorem computableEval_of_fragment (F : Expression.Factory) (hF : EvalFactoryWF F.factory)
    (hlit : ConstrsNotLit F.factory) {ok : LFunc CoreLParams → Prop}
    (hok : ∀ fn, F.factory[fn.name.name]? = some fn → ok fn →
      ComputableOp fn ∨ UserFnComputable F fn)
    {σ : SemanticStore Expression} {e : Expression.Expr} (h : FragmentExpr F.factory ok e)
    (hσ : ∀ x ∈ LExpr.LExpr.getVars e, ∀ v, σ x = some v →
      ∃ c, c.isPrimitive = true ∧ v = SemValue.ofConst F.model.tcInterp c) :
    ComputableEval F σ e := by
  induction h with
  | const m c hc => exact computableEval_const F hF σ m hc
  | fvar m x ty =>
    exact computableEval_fvar F hF hlit (hσ x (by simp [LExpr.LExpr.getVars]))
  | ite _ _ _ ihc iht ihf =>
    exact computableEval_ite F hF
      (ihc fun x hx => hσ x (by simp [LExpr.LExpr.getVars, hx]))
      (iht fun x hx => hσ x (by simp [LExpr.LExpr.getVars, hx]))
      (ihf fun x hx => hσ x (by simp [LExpr.LExpr.getVars, hx]))
  | eq _ _ iha ihb =>
    exact computableEval_eq F hF
      (iha fun x hx => hσ x (by simp [LExpr.LExpr.getVars, hx]))
      (ihb fun x hx => hσ x (by simp [LExpr.LExpr.getVars, hx]))
  | call hcall hfn hop _ ih =>
    have hargs := fun a ha => ih a ha fun x hx =>
      hσ x (callOfLFunc_getVars_args _ _ _ _ _ hcall a ha x hx)
    obtain ⟨m, name, ty, rfl, hget⟩ := Factory.callOfLFunc_getElem? hcall
    rcases hok _ (Factory.getElem?_name hget ▸ hget) hfn with
      hc | ⟨hm, hc, hce, hinl, body, hb, hv, hbody⟩
    · exact computableEval_op F hF hcall hc hop hargs
    · exact computableEval_userFn F hF hcall hm hc hce hb hinl hv hop hargs (hbody σ)

/-! ## The fragment is closed under replacing variables by literals -/

/-- Replacing free variables (`substFvarsLifting.go`) commutes with reading an application spine
    headed by an operator: it replaces them in the arguments. -/
private theorem getLFuncCall_go_subst (sm : Map CoreIdent Expression.Expr) (d : Nat)
    (e : Expression.Expr) (acc : List Expression.Expr)
    (hop : ∃ m name ty, (getLFuncCall.go e acc).1 = .op m name ty) :
    getLFuncCall.go (LExpr.substFvarsLifting.go (T := CoreLParams) sm e d)
        (acc.map (LExpr.substFvarsLifting.go (T := CoreLParams) sm · d)) =
      ((getLFuncCall.go e acc).1,
        (getLFuncCall.go e acc).2.map (LExpr.substFvarsLifting.go (T := CoreLParams) sm · d)) := by
  fun_induction getLFuncCall.go e acc
  · rename_i ih
    simpa [LExpr.substFvarsLifting.go, getLFuncCall.go] using ih hop
  · simp [LExpr.substFvarsLifting.go, getLFuncCall.go]
  · obtain ⟨m, name, ty, rfl⟩ := hop
    simp [LExpr.substFvarsLifting.go, getLFuncCall.go]

/-- Replacing free variables keeps a call of a factory function a call of the same function, its
    arguments replaced in. -/
private theorem callOfLFunc_subst {F : Lambda.Factory CoreLParams}
    (sm : Map CoreIdent Expression.Expr) (d : Nat) {e op : Expression.Expr}
    {args : List Expression.Expr} {fn : LFunc CoreLParams}
    (h : F.callOfLFunc e = some (op, args, fn)) :
    F.callOfLFunc (LExpr.substFvarsLifting.go (T := CoreLParams) sm e d) =
      some (op, args.map (LExpr.substFvarsLifting.go (T := CoreLParams) sm · d), fn) := by
  have hg := callOfLFunc_getLFuncCall h
  obtain ⟨m, name, ty, rfl, hget⟩ := Factory.callOfLFunc_getElem? h
  have hl := Factory.callOfLFunc_arity h
  simp only [getLFuncCall] at hg
  have hs := getLFuncCall_go_subst sm d e [] (by rw [hg]; exact ⟨m, name, ty, rfl⟩)
  rw [hg] at hs
  simp only [List.map_nil] at hs
  simp only [Factory.callOfLFunc, getLFuncCall, hs, hget, List.length_map, hl, beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte]

/-- **The fragment is closed under replacing variables by literals**: replacing the variables
    `ks` of an expression of the computable fragment by literals keeps it in the fragment. -/
theorem fragmentExpr_inline {F : Lambda.Factory CoreLParams} {ok : LFunc CoreLParams → Prop}
    {ks : List CoreIdent} {ls : List Expression.Expr} {tys : List LMonoTy}
    (hls : LitsOfTypes ls tys) {e : Expression.Expr} (h : FragmentExpr F ok e) :
    FragmentExpr F ok (e.substFvarsLifting (ks.zip ls)) := by
  unfold LExpr.substFvarsLifting
  split
  · exact h
  · generalize 0 = d
    induction h generalizing d with
    | const m c hc => exact .const m c hc
    | fvar m x ty =>
      simp only [LExpr.substFvarsLifting.go]
      split
      · rename_i l hl
        obtain ⟨⟨k, l'⟩, hp, rfl⟩ := List.mem_map.1 (Map_find?_some_mem_values _ x l hl)
        obtain ⟨m', c, rfl, -, hc⟩ := hls.mem (List.of_mem_zip hp).2
        exact .const m c hc
      · exact .fvar m x ty
    | ite _ _ _ ihc iht ihf => exact .ite (ihc d) (iht d) (ihf d)
    | eq _ _ iha ihb => exact .eq (iha d) (ihb d)
    | call hcall hfn hop _ ih =>
      exact .call (callOfLFunc_subst _ d hcall) hfn hop fun a ha => by
        obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
        exact ih a' ha' d

/-! ## The functions of the fragment -/

/-- Whether the user function `fn` is in the computable fragment, its body calling only the
    functions named in `acc`: monomorphic, not a constructor, without a concrete evaluator,
    unfolded by the evaluator (`inline` or `inlineIfAllValues`), with a body that reads only its
    parameters and is in the computable fragment relative to `acc`. -/
@[expose] def userFnInFragment (F : Lambda.Factory CoreLParams) (acc : List String)
    (fn : LFunc CoreLParams) : Bool :=
  fn.typeArgs.isEmpty && !fn.isConstr && fn.concreteEval.isNone &&
    (fn.attr.contains .inline || Strata.DL.Util.FuncAttr.hasInlineIfAllValues fn.attr) &&
    match fn.body with
    | some body => (LExpr.LExpr.getVars body).all (· ∈ fn.inputs.keys) &&
        fragmentExpr F (fun g => acc.contains g.name.name) body
    | none => false

/-- The names of the functions of the computable fragment, accumulated along a list of a
    factory's functions in order onto `acc`: a built-in operator `isComputableBuiltinFn` admits,
    or a user function in the fragment relative to the functions accepted before it. -/
@[expose] def fragmentFnsFrom (F : Lambda.Factory CoreLParams) :
    List (LFunc CoreLParams) → List String → List String
  | [], acc => acc
  | fn :: fns, acc => fragmentFnsFrom F fns
      (if isComputableBuiltinFn fn || userFnInFragment F acc fn then fn.name.name :: acc else acc)

/-- **The functions of the computable fragment** of the factory `F`, by name: its functions, in
    order, that are built-in operators `isComputableBuiltinFn` admits or user functions in the
    fragment relative to the functions before them (`userFnInFragment`). -/
@[expose] def fragmentFns (F : Lambda.Factory CoreLParams) : List String :=
  fragmentFnsFrom F F.toArray.toList []

/-- A function a factory looks up under the name of a function of its array is that function. -/
private theorem getElem?_of_mem_name {F : Lambda.Factory CoreLParams} {fn fn' : LFunc CoreLParams}
    (hmem : fn ∈ F.toArray) (h : F[fn.name.name]? = some fn') : fn' = fn := by
  obtain ⟨hs, hget⟩ := Factory.mem_name_eq_getElem hmem rfl
  exact (Factory.getElem?_some_getElem h).symm.trans hget

/-- The conditions under which the fragment's functions are computed on literals: the model's
    factory meets the conditions of evaluator soundness (`EvalFactoryWF`), none of its constructors
    produces a value of a literal type, and every function of it with a concrete evaluator is a
    function of `Core.Factory`. -/
@[expose] def FragmentFactoryWF (F : Expression.Factory) : Prop :=
  EvalFactoryWF F.factory ∧ ConstrsNotLit F.factory ∧
    ∀ fn ∈ F.factory.toArray, fn.concreteEval.isSome = true → fn ∈ Core.Factory.toArray

/-- A user function `userFnInFragment` accepts relative to a list of names of functions computed
    on literals is computed on literals. -/
private theorem userFnComputable_of_check {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {acc : List String}
    (hacc : ∀ fn, F.factory[fn.name.name]? = some fn → fn.name.name ∈ acc →
      ComputableOp fn ∨ UserFnComputable F fn)
    {fn : LFunc CoreLParams} (h : userFnInFragment F.factory acc fn = true) :
    UserFnComputable F fn := by
  unfold userFnInFragment at h
  simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true', Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨hmono, hc⟩, hce⟩, hinl⟩, hb⟩ := h
  split at hb
  · rename_i body hbody
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hvars, hfrag⟩ := hb
    refine ⟨hmono, hc, hce, hinl, body, hbody, hvars, fun σ ls hls => ?_⟩
    have hlen : fn.inputs.keys.length = ls.length := by
      rw [ListMap.keys.length, hls.length_eq]
      exact (List.length_map (as := (fn.inputs : List (CoreIdent × LMonoTy))) Prod.snd).symm
    have hclosed := getVars_inline_nil hvars hlen hls
    refine computableEval_of_fragment F hF.1 hF.2.1
      (ok := fun g => acc.contains g.name.name = true)
      (fun g hg hin => hacc g hg (List.contains_iff_mem.1 hin))
      (fragmentExpr_inline hls ((fragmentExpr_iff _ _ _).1 hfrag)) fun x hx => ?_
    simp [hclosed] at hx
  · cases hb

/-- No function of `Core.Factory` is a constructor. -/
private theorem coreFactory_not_constr {fn : LFunc CoreLParams} (h : fn ∈ Core.Factory.toArray) :
    fn.isConstr = false := by
  have hall : (Core.WFFactoryArray.toList.all fun w => !w.func.isConstr) = true := by
    simp only [Core.WFFactoryArray, Array.toList_appendList]
    decide +kernel
  obtain ⟨w, hw, rfl⟩ := Array.mem_map.mp (Lambda.Factory.ofArray_mem h)
  simpa using List.all_eq_true.mp hall w (Array.mem_toList_iff.mpr hw)

/-- **Program factories meet `FragmentFactoryWF`**: a well-formed factory each of whose functions
    is a function of `Core.Factory` or a user function meeting `UserFuncWF` (the conditions of
    `evalFactoryWF_of_userFuncs`) does. -/
theorem fragmentFactoryWF_of_userFuncs (F : Expression.Factory) (hWF : Lambda.FactoryWF F.factory)
    (hfns : ∀ fn ∈ F.factory.toArray, fn ∈ Core.Factory.toArray ∨ UserFuncWF F.factory fn) :
    FragmentFactoryWF F := by
  refine ⟨evalFactoryWF_of_userFuncs _ hWF hfns, fun fn hfn hc => ?_, fun fn hfn hce => ?_⟩
  · rcases hfns fn hfn with h | h
    · exact absurd (coreFactory_not_constr h ▸ hc) Bool.false_ne_true
    · exact absurd (h.2.1 ▸ hc) Bool.false_ne_true
  · rcases hfns fn hfn with h | h
    · exact h
    · simp [h.1] at hce

/-- Every modeled factory over `Core.Factory` meets `FragmentFactoryWF`. -/
theorem fragmentFactoryWF_coreFactory (F : Expression.Factory) (hF : F.factory = Core.Factory) :
    FragmentFactoryWF F :=
  fragmentFactoryWF_of_userFuncs F (hF ▸ Core.WFFactory.toFactory_wf) fun _ h => .inl (hF ▸ h)

/-- Every function `fragmentFnsFrom` accepts, from a list of functions of the factory and onto
    a list of names of functions computed on literals, is computed on literals. -/
private theorem fragmentFnsFrom_sound {F : Expression.Factory} (hF : FragmentFactoryWF F) :
    ∀ (fns : List (LFunc CoreLParams)) (acc : List String), (∀ fn ∈ fns, fn ∈ F.factory.toArray) →
      (∀ fn, F.factory[fn.name.name]? = some fn → fn.name.name ∈ acc →
        ComputableOp fn ∨ UserFnComputable F fn) →
      ∀ fn, F.factory[fn.name.name]? = some fn → fn.name.name ∈ fragmentFnsFrom F.factory fns acc →
        ComputableOp fn ∨ UserFnComputable F fn
  | [], _, _, hacc => hacc
  | g :: fns, acc, hmem, hacc => by
    refine fragmentFnsFrom_sound hF fns _ (fun fn h => hmem fn (List.mem_cons_of_mem _ h)) ?_
    split
    · rename_i hok
      intro fn hfn hin
      rcases List.mem_cons.1 hin with hn | hn
      · have hg := hmem g List.mem_cons_self
        obtain rfl := getElem?_of_mem_name hg (hn ▸ hfn)
        rcases Bool.or_eq_true_iff.1 hok with hb | hu
        · exact .inl (computableOp_of_builtin (hF.2.2 fn hg (Bool.and_eq_true_iff.1 hb).1) hb)
        · exact .inr (userFnComputable_of_check hF hacc hu)
      · exact hacc fn hfn hn
    · exact hacc

/-- **The functions of the fragment are computed on literals**, on a factory meeting
    `FragmentFactoryWF`: every function of the factory `fragmentFns` names is a built-in operator
    computed on literals (`ComputableOp`) or a user function computed on literals
    (`UserFnComputable`). -/
theorem fragmentFns_sound {F : Expression.Factory} (hF : FragmentFactoryWF F) :
    ∀ fn, F.factory[fn.name.name]? = some fn → fn.name.name ∈ fragmentFns F.factory →
      ComputableOp fn ∨ UserFnComputable F fn :=
  fragmentFnsFrom_sound hF _ [] (fun _ h => Array.mem_def.2 h) fun _ _ h => nomatch h

/-! ## Expressions whose values are not real

The semantics of `real` is `Strata.Util.Real`, whose values are not all literals, so the fragment
keeps real values out of the stores of its runs: an arbitrary value of a variable holding a real
could be irrational, and no literal would denote it. A type annotation of an expression of the
fragment never has `real` as its result type (`notRealResult`), so neither does the expression's
type (`notRealResult_of_hasTypeA`). -/

/-- Whether a type is not `real`, nor a function type whose result, after all its arguments, is
    `real`. -/
@[expose] def notRealResult : LMonoTy → Bool
  | .tcons "real" [] => false
  | .tcons "arrow" [_, r] => notRealResult r
  | _ => true

/-- Whether every literal and type annotation of an expression has a type that `notRealResult`
    accepts: in particular, the expression has no `real` literal. -/
@[expose] def annNotReal : Expression.Expr → Bool
  | .const _ c => notRealResult c.ty
  | .op _ _ ty => ty.all notRealResult
  | .fvar _ _ ty => ty.all notRealResult
  | .bvar _ _ => true
  | .abs _ _ ty b => ty.all notRealResult && annNotReal b
  | .quant _ _ _ ty tr b => ty.all notRealResult && annNotReal tr && annNotReal b
  | .app _ f a => annNotReal f && annNotReal a
  | .ite _ c t f => annNotReal c && annNotReal t && annNotReal f
  | .eq _ a b => annNotReal a && annNotReal b

/-- The type of an expression whose annotations `annNotReal` accepts, in a context of such types,
    is not `real`, nor a function type with result `real`. -/
private theorem notRealResult_of_hasTypeA {Δ : List LMonoTy} {e : Expression.Expr} {τ : LMonoTy}
    (h : LExpr.HasTypeA Δ e τ) (hΔ : ∀ t ∈ Δ, notRealResult t = true)
    (he : annNotReal e = true) : notRealResult τ = true := by
  induction h with
  | const => exact he
  | op => simpa [annNotReal] using he
  | fvar => simpa [annNotReal] using he
  | bvar hi => exact hΔ _ (List.mem_of_getElem? hi)
  | abs _ ih =>
    simp only [annNotReal, Bool.and_eq_true, Option.all_some] at he
    exact ih (fun t ht => by
      rcases List.mem_cons.1 ht with rfl | ht
      · exact he.1
      · exact hΔ t ht) he.2
  | quant => rfl
  | app _ _ ihf _ =>
    simp only [annNotReal, Bool.and_eq_true] at he
    exact ihf hΔ he.1
  | ite _ _ _ _ iht _ =>
    simp only [annNotReal, Bool.and_eq_true] at he
    exact iht hΔ he.1.2
  | eq => rfl

/-- Annotating the free variables of an expression `annNotReal` accepts with types
    `notRealResult` accepts keeps it accepted. -/
private theorem annNotReal_annotateFvars {ann : CoreIdent → Option LMonoTy}
    (hann : ∀ x t, ann x = some t → notRealResult t = true) {e : Expression.Expr}
    (he : annNotReal e = true) : annNotReal (e.annotateFvars ann) = true := by
  induction e with
  | fvar m x ty =>
    simp only [LExpr.annotateFvars, annNotReal] at he ⊢
    split
    · rename_i t ht; exact by simpa using hann x t ht
    · exact he
  | _ => simp_all [LExpr.annotateFvars, annNotReal]

/-- **The expressions of the fragment** of the factory `F`: the computable fragment relative to
    the functions of the fragment (`fragmentFns`), with no annotation of result type `real`
    (`annNotReal`). -/
abbrev InFragment (F : Lambda.Factory CoreLParams) (e : Expression.Expr) : Prop :=
  FragmentExpr F (·.name.name ∈ fragmentFns F) e ∧ annNotReal e = true

/-- The decision procedure for `InFragment`. -/
@[expose] def inFragment (F : Lambda.Factory CoreLParams) (e : Expression.Expr) : Bool :=
  fragmentExpr F (fun g => (fragmentFns F).contains g.name.name) e && annNotReal e

/-- `inFragment` decides `InFragment`. -/
theorem inFragment_iff (F : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    inFragment F e = true ↔ InFragment F e := by
  rw [inFragment, Bool.and_eq_true, fragmentExpr_iff]
  simp only [List.contains_iff_mem]

/-- **Computable evaluation of the fragment**: on a factory meeting `FragmentFactoryWF`, an
    expression of the fragment is computable on every store binding its variables to values of
    primitive literals. -/
theorem computableEval_of_inFragment {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {σ : SemanticStore Expression} {e : Expression.Expr} (h : InFragment F.factory e)
    (hσ : ∀ x ∈ LExpr.LExpr.getVars e, ∀ v, σ x = some v →
      ∃ c, c.isPrimitive = true ∧ v = SemValue.ofConst F.model.tcInterp c) :
    ComputableEval F σ e :=
  computableEval_of_fragment F hF.1 hF.2.1 (fun fn hfn hin => fragmentFns_sound hF fn hfn hin) h.1
    hσ

/-! ## The static criterion on programs -/

/-- Whether a monomorphic type is a type of literals: `bool`, `int`, `string`, or a bit-vector
    type. `real` is excluded, for the reason given at the start of this section, for instance
    `var x : real; havoc x`. Deterministic real code (literals, copies, conditionals) could be
    readmitted under the invariant that every stored real is the value of a rational literal. -/
@[expose] def isLitMonoTy : LMonoTy → Bool
  | .tcons "bool" [] => true
  | .tcons "int" [] => true
  | .tcons "string" [] => true
  | .bitvec _ => true
  | _ => false

/-- Whether a type is a monomorphic type of literals. -/
@[expose] def isLitTy (ty : Expression.Ty) : Bool := ty.toMonoType?.any isLitMonoTy

/-- A semantic value of a sort whose type is a type of literals is the value of a primitive
    literal whose type is not `real`. -/
theorem eq_ofConst_of_isLitMonoTy {v : SemValue} (h : isLitMonoTy v.sort.toMonoTy = true) :
    ∃ c, c.isPrimitive = true ∧ notRealResult c.ty = true ∧ v = SemValue.ofConst v.tc c := by
  obtain ⟨tc, s, val⟩ := v
  cases s with
  | bitvec n => exact ⟨.bitvecConst n val, rfl, rfl, rfl⟩
  | tcons name args =>
    simp only [LSort.toMonoTy] at h
    unfold isLitMonoTy at h
    split at h <;> rename_i heq
    all_goals first
      | (injection heq with h1 h2
         subst h1
         cases args with
         | cons _ _ => cases h2
         | nil =>
           first
           | exact ⟨.boolConst val, rfl, rfl, rfl⟩
           | exact ⟨.intConst val, rfl, rfl, rfl⟩
           | exact ⟨.strConst val, rfl, rfl, rfl⟩)
      | cases heq
      | cases h

/-- A command is in the fragment `P` of expressions: the type of an `init` is a type of literals,
    and its deterministic right-hand side, that of a `set`, the condition of an `assert` or a
    `cover`, and every input argument of a call satisfy `P`. -/
@[expose] def CmdInFragment (P : Expression.Expr → Prop) : Command → Prop
  | .cmd (.init _ ty e _) => isLitTy ty = true ∧ ∀ e', e = .det e' → P e'
  | .cmd (.set _ e _) => ∀ e', e = .det e' → P e'
  | .cmd (.assert _ e _) => P e
  | .cmd (.cover _ e _) => P e
  | .cmd (.assume _ _ _) => True
  | .call _ args _ => ∀ e ∈ Calls.getInputExprs args, P e

mutual
/-- A statement is in the fragment `P` of expressions: its commands are (`CmdInFragment`), and the
    deterministic guards of its conditionals and loops satisfy `P`, at every nesting depth. -/
@[expose] def StmtInFragment (P : Expression.Expr → Prop) : Statement → Prop
  | .cmd c => CmdInFragment P c
  | .block _ ss _ => BlockInFragment P ss
  | .ite g tss ess _ => (∀ c, g = .det c → P c) ∧ BlockInFragment P tss ∧ BlockInFragment P ess
  | .loop g _ _ body _ => (∀ c, g = .det c → P c) ∧ BlockInFragment P body
  | .exit _ _ => True
  | .typeDecl _ _ => True

/-- Every statement of a block is in the fragment `P` of expressions. -/
@[expose] def BlockInFragment (P : Expression.Expr → Prop) : Statements → Prop
  | [] => True
  | s :: ss => StmtInFragment P s ∧ BlockInFragment P ss
end

/-- Every statement a configuration still executes is in the fragment `P` of expressions. -/
@[expose] def ConfigInFragment (P : Expression.Expr → Prop) : CoreConfig → Prop
  | .stmt s _ => StmtInFragment P s
  | .stmts ss _ => BlockInFragment P ss
  | .terminal _ => True
  | .exiting _ _ => True
  | .block _ _ inner => ConfigInFragment P inner
  | .seq inner ss => ConfigInFragment P inner ∧ BlockInFragment P ss

/-- A transfer command is in the fragment `P` of expressions: the guard of a conditional transfer
    satisfies `P`. -/
@[expose] def TransferInFragment (P : Expression.Expr → Prop) :
    DetTransferCmd String Expression → Prop
  | .condGoto c _ _ _ => P c
  | .finish _ => True

/-- A CFG is in the fragment `P` of expressions: the commands of each of its blocks are
    (`CmdInFragment`), and so is the block's transfer (`TransferInFragment`). -/
@[expose] def CFGInFragment (P : Expression.Expr → Prop)
    (g : Imperative.DetCFG Expression Command) : Prop :=
  ∀ lb ∈ g.blocks, (∀ c ∈ lb.2.cmds, CmdInFragment P c) ∧ TransferInFragment P lb.2.transfer

/-- A procedure is in the fragment `P` of expressions: it has a structured body in the fragment
    or a CFG body in the fragment, and the conditions of its pre- and postconditions satisfy
    `P`. -/
@[expose] def ProcInFragment (P : Expression.Expr → Prop) (p : Procedure) : Prop :=
  ((∃ ss, p.body = .structured ss ∧ BlockInFragment P ss) ∨
    ∃ g, p.body = .cfg g ∧ CFGInFragment P g) ∧
    (∀ lc ∈ p.spec.preconditions.toList, P lc.2.expr) ∧
    ∀ lc ∈ p.spec.postconditions.toList, P lc.2.expr

/-- The decision procedure for `CmdInFragment`. -/
@[expose] def cmdInFragment (fe : Expression.Expr → Bool) : Command → Bool
  | .cmd (.init _ ty e _) => isLitTy ty && (match e with | .det e => fe e | .nondet => true)
  | .cmd (.set _ e _) => match e with | .det e => fe e | .nondet => true
  | .cmd (.assert _ e _) => fe e
  | .cmd (.cover _ e _) => fe e
  | .cmd (.assume _ _ _) => true
  | .call _ args _ => (Calls.getInputExprs args).all fe

/-- The decision procedure for a deterministic guard in the fragment. -/
@[expose] def guardInFragment (fe : Expression.Expr → Bool) : ExprOrNondet Expression → Bool
  | .det c => fe c
  | .nondet => true

mutual
/-- The decision procedure for `StmtInFragment`. -/
@[expose] def stmtInFragment (fe : Expression.Expr → Bool) : Statement → Bool
  | .cmd c => cmdInFragment fe c
  | .block _ ss _ => blockInFragment fe ss
  | .ite g tss ess _ => guardInFragment fe g && blockInFragment fe tss && blockInFragment fe ess
  | .loop g _ _ body _ => guardInFragment fe g && blockInFragment fe body
  | .exit _ _ => true
  | .typeDecl _ _ => true

/-- The decision procedure for `BlockInFragment`. -/
@[expose] def blockInFragment (fe : Expression.Expr → Bool) : Statements → Bool
  | [] => true
  | s :: ss => stmtInFragment fe s && blockInFragment fe ss
end

/-- The decision procedure for `ConfigInFragment`. -/
@[expose] def configInFragment (fe : Expression.Expr → Bool) : CoreConfig → Bool
  | .stmt s _ => stmtInFragment fe s
  | .stmts ss _ => blockInFragment fe ss
  | .terminal _ => true
  | .exiting _ _ => true
  | .block _ _ inner => configInFragment fe inner
  | .seq inner ss => configInFragment fe inner && blockInFragment fe ss

/-- The decision procedure for `TransferInFragment`. -/
@[expose] def transferInFragment (fe : Expression.Expr → Bool) :
    DetTransferCmd String Expression → Bool
  | .condGoto c _ _ _ => fe c
  | .finish _ => true

/-- The decision procedure for `CFGInFragment`. -/
@[expose] def cfgInFragment (fe : Expression.Expr → Bool)
    (g : Imperative.DetCFG Expression Command) : Bool :=
  g.blocks.all fun lb => lb.2.cmds.all (cmdInFragment fe) && transferInFragment fe lb.2.transfer

/-- The decision procedure for `ProcInFragment`. -/
@[expose] def procInFragment (fe : Expression.Expr → Bool) (p : Procedure) : Bool :=
  (match p.body with | .structured ss => blockInFragment fe ss | .cfg g => cfgInFragment fe g) &&
    (p.spec.preconditions.toList.all fun lc => fe lc.2.expr) &&
    p.spec.postconditions.toList.all fun lc => fe lc.2.expr

/-- `cmdInFragment` decides `CmdInFragment`. -/
theorem cmdInFragment_iff (fe : Expression.Expr → Bool) (c : Command) :
    cmdInFragment fe c = true ↔ CmdInFragment (fe · = true) c := by
  cases c with
  | cmd c =>
    cases c with
    | init _ _ e _ => cases e <;> simp [cmdInFragment, CmdInFragment]
    | set _ e _ => cases e <;> simp [cmdInFragment, CmdInFragment]
    | _ => simp [cmdInFragment, CmdInFragment]
  | call _ args _ => simp [cmdInFragment, CmdInFragment]

/-- `guardInFragment` decides that a deterministic guard satisfies the fragment. -/
private theorem guardInFragment_iff (fe : Expression.Expr → Bool) (g : ExprOrNondet Expression) :
    guardInFragment fe g = true ↔ ∀ c, g = .det c → fe c = true := by
  cases g <;> simp [guardInFragment]

mutual
/-- `stmtInFragment` decides `StmtInFragment`. -/
theorem stmtInFragment_iff (fe : Expression.Expr → Bool) :
    ∀ s : Statement, stmtInFragment fe s = true ↔ StmtInFragment (fe · = true) s
  | .cmd c => by
    simp only [stmtInFragment, StmtInFragment]
    exact cmdInFragment_iff fe c
  | .block _ ss _ => by
    simp only [stmtInFragment, StmtInFragment]
    exact blockInFragment_iff fe ss
  | .ite g tss ess _ => by
    simp only [stmtInFragment, StmtInFragment, Bool.and_eq_true, guardInFragment_iff,
      blockInFragment_iff fe tss, blockInFragment_iff fe ess, and_assoc]
  | .loop g _ _ body _ => by
    simp only [stmtInFragment, StmtInFragment, Bool.and_eq_true, guardInFragment_iff,
      blockInFragment_iff fe body]
  | .exit _ _ => by simp [stmtInFragment, StmtInFragment]
  | .typeDecl _ _ => by simp [stmtInFragment, StmtInFragment]

/-- `blockInFragment` decides `BlockInFragment`. -/
theorem blockInFragment_iff (fe : Expression.Expr → Bool) :
    ∀ ss : Statements, blockInFragment fe ss = true ↔ BlockInFragment (fe · = true) ss
  | [] => by simp [blockInFragment, BlockInFragment]
  | s :: ss => by
    simp only [blockInFragment, BlockInFragment, Bool.and_eq_true, stmtInFragment_iff fe s,
      blockInFragment_iff fe ss]
end

/-- `configInFragment` decides `ConfigInFragment`. -/
theorem configInFragment_iff (fe : Expression.Expr → Bool) :
    ∀ c : CoreConfig, configInFragment fe c = true ↔ ConfigInFragment (fe · = true) c
  | .stmt s _ => stmtInFragment_iff fe s
  | .stmts ss _ => blockInFragment_iff fe ss
  | .terminal _ => by simp [configInFragment, ConfigInFragment]
  | .exiting _ _ => by simp [configInFragment, ConfigInFragment]
  | .block _ _ inner => configInFragment_iff fe inner
  | .seq inner ss => by
    simp only [configInFragment, ConfigInFragment, Bool.and_eq_true, configInFragment_iff fe inner,
      blockInFragment_iff fe ss]

/-- `cfgInFragment` decides `CFGInFragment`. -/
theorem cfgInFragment_iff (fe : Expression.Expr → Bool) (g : Imperative.DetCFG Expression Command) :
    cfgInFragment fe g = true ↔ CFGInFragment (fe · = true) g := by
  unfold cfgInFragment CFGInFragment
  refine List.all_eq_true.trans (forall₂_congr fun lb _ => ?_)
  cases h : lb.2.transfer <;>
    simp [transferInFragment, TransferInFragment, List.all_eq_true, cmdInFragment_iff]

/-- `procInFragment` decides `ProcInFragment`. -/
theorem procInFragment_iff (fe : Expression.Expr → Bool) (p : Procedure) :
    procInFragment fe p = true ↔ ProcInFragment (fe · = true) p := by
  unfold procInFragment ProcInFragment
  simp only [Bool.and_eq_true, List.all_eq_true, and_assoc]
  refine and_congr_left fun _ => ?_
  split <;> simp_all [blockInFragment_iff, cfgInFragment_iff]

/-! ## Runs of programs in the fragment -/

/-- A semantic value is the value of a primitive literal (`LConst.isPrimitive`) of the factory's
    model, of a type other than `real`. -/
@[expose] def LitVal (F : Expression.Factory) (v : Expression.Val) : Prop :=
  ∃ c, c.isPrimitive = true ∧ notRealResult c.ty = true ∧ v = SemValue.ofConst F.model.tcInterp c

/-- Every value of the store is the value of a literal (`LitVal`). -/
@[expose] def LitStore (F : Expression.Factory) (σ : CoreStore) : Prop :=
  ∀ x v, σ x = some v → LitVal F v

/-- Every environment a configuration executes in has the factory `F` and a store of literals. -/
@[expose] def ConfigLit (F : Expression.Factory) : CoreConfig → Prop
  | .stmt _ ρ => ρ.factory = F ∧ LitStore F ρ.store
  | .stmts _ ρ => ρ.factory = F ∧ LitStore F ρ.store
  | .terminal ρ => ρ.factory = F ∧ LitStore F ρ.store
  | .exiting _ ρ => ρ.factory = F ∧ LitStore F ρ.store
  | .block _ _ inner => ConfigLit F inner
  | .seq inner _ => ConfigLit F inner

/-- An event whose condition the fragment covers: an assertion or a cover at the factory `F`, at a
    store of literals, whose condition is in the fragment. -/
@[expose] def EventInFragment (F : Expression.Factory) : Event Expression → Prop
  | .assert a => a.factory = F ∧ LitStore F a.store ∧ InFragment F.factory a.expr
  | .cover a => a.factory = F ∧ LitStore F a.store ∧ InFragment F.factory a.expr
  | .assume _ => True

open Classical in
/-- A store of literals is denoted by a runtime store: each value by a literal of it. -/
private theorem exists_storeDenotes {F : Expression.Factory} {σ : CoreStore}
    (hσ : LitStore F σ) : ∃ σr : RStore Expression, StoreDenotes F σr σ := by
  refine ⟨fun x => (σ x).map fun v =>
    .const default (if h : LitVal F v then Classical.choose h else .boolConst false),
    fun x => by cases h : σ x <;> simp [h], fun x r v hr hx => ?_⟩
  simp only [hx, Option.map_some, Option.some.injEq] at hr
  subst hr
  split
  · have hc := Classical.choose_spec ‹LitVal F v›
    exact (denotes_const_iff (LConst.wt_of_isPrimitive hc.1)).2 hc.2.2
  · exact absurd (hσ x v hx) ‹_›

/-- In the model `Core.factoryInterp` of `Core.Factory`, the value of a primitive literal is
    reified, by the model's reification of primitive values (`FactoryInterpModel.reifyAt`), as
    that literal. -/
theorem reifyAt_ofConst {c : LConst} (hc : c.isPrimitive = true) :
    FactoryInterpModel.reifyAt (SemValue.ofConst FactoryInterpModel.tcInterp c).sort
      (SemValue.ofConst FactoryInterpModel.tcInterp c).val =
        (LExpr.const default c : Expression.Expr) := by
  cases c with
  | rationalConst r => exact FactoryInterpModel.reifyAt_ofRat r
  | mapConst => cases hc
  | sequenceConst => cases hc
  | _ => rfl

/-- The value of a computable expression on a store of literals, none of whose literals and
    annotations has result type `real`, is the value of a literal whose type is not `real`. -/
private theorem litVal_of_computable {F : Expression.Factory} {σ : CoreStore}
    {e : Expression.Expr} {v : Expression.Val} (hσ : LitStore F σ) (h : ComputableEval F σ e)
    (he : annNotReal e = true) (hv : Expression.eval F σ e = some v) : LitVal F v := by
  obtain ⟨hd, τ, hτ, -, -⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).1 hv
  obtain ⟨σr, hS⟩ := exists_storeDenotes hσ
  obtain ⟨c, hcp, hct, hc, -⟩ := h σr τ hS hd hτ
  refine ⟨c, hcp, hct ▸ notRealResult_of_hasTypeA hτ nofun (annNotReal_annotateFvars ?_ he),
    Option.some.inj (hv.symm.trans hc)⟩
  intro x t hx
  simp only [ValStore.ann, Option.map_eq_some_iff] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨c', -, hc', rfl⟩ := hσ x w hw
  simp only [SemValue.ofConst]
  exact (congrArg notRealResult (LConst.ty_isGround c')).trans hc'

/-- A point update of a store of literals by the value of a literal is a store of literals. -/
private theorem LitStore.update {F : Expression.Factory} {σ : CoreStore} {x : CoreIdent}
    {v : Expression.Val} (hσ : LitStore F σ) (hv : LitVal F v) :
    LitStore F (SemanticStore.update σ x v) := fun y w h => by
  unfold SemanticStore.update at h
  split at h
  · exact Option.some.inj h ▸ hv
  · exact hσ y w h

/-- Binding a fresh variable of a store of literals to the value of a literal gives a store of
    literals. -/
private theorem LitStore.init {F : Expression.Factory} {σ σ' : CoreStore} {x : CoreIdent}
    {v : Expression.Val} (hσ : LitStore F σ) (hv : LitVal F v)
    (h : InitState Expression σ x v σ') : LitStore F σ' := by
  obtain ⟨-, rfl⟩ := h.eq_update
  exact hσ.update hv

/-- Updating a variable of a store of literals to the value of a literal gives a store of
    literals. -/
private theorem LitStore.set {F : Expression.Factory} {σ σ' : CoreStore} {x : CoreIdent}
    {v : Expression.Val} (hσ : LitStore F σ) (hv : LitVal F v)
    (h : UpdateState Expression σ x v σ') : LitStore F σ' := by
  obtain ⟨-, rfl⟩ := h.eq_update
  exact hσ.update hv

/-- Binding fresh variables of a store of literals to values of literals gives a store of
    literals. -/
private theorem LitStore.inits {F : Expression.Factory} {σ σ' : CoreStore} {xs : List CoreIdent}
    {vs : List Expression.Val} (hσ : LitStore F σ) (hv : ∀ v ∈ vs, LitVal F v)
    (h : InitStates σ xs vs σ') : LitStore F σ' := by
  induction h with
  | init_none => exact hσ
  | init_some hi _ ih =>
    exact ih (hσ.init (hv _ List.mem_cons_self) hi) fun v h => hv v (List.mem_cons_of_mem _ h)

/-- Updating variables of a store of literals to values of literals gives a store of literals. -/
private theorem LitStore.sets {F : Expression.Factory} {σ σ' : CoreStore} {xs : List CoreIdent}
    {vs : List Expression.Val} (hσ : LitStore F σ) (hv : ∀ v ∈ vs, LitVal F v)
    (h : UpdateStates σ xs vs σ') : LitStore F σ' := by
  induction h with
  | update_none => exact hσ
  | update_some hu _ ih =>
    exact ih (hσ.set (hv _ List.mem_cons_self) hu) fun v h => hv v (List.mem_cons_of_mem _ h)

/-- The values read from a store of literals are values of literals. -/
private theorem LitStore.read {F : Expression.Factory} {σ : SemanticStore Expression}
    {xs : List Expression.Ident} {vs : List Expression.Val} (hσ : LitStore F σ)
    (h : ReadValues F σ xs vs) : ∀ v ∈ vs, LitVal F v := by
  induction h with
  | read_none => exact nofun
  | read_some hx _ _ ih =>
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hσ _ _ hx
    · exact ih v hv

/-- The values of computable expressions on a store of literals are values of literals. -/
private theorem LitStore.evals {F : Expression.Factory} {σ : CoreStore}
    {es : List Expression.Expr} {vs : List Expression.Val} (hσ : LitStore F σ)
    (hc : ∀ e ∈ es, ComputableEval F σ e ∧ annNotReal e = true)
    (h : EvalExpressions (P := Expression) F σ es vs) :
    ∀ v ∈ vs, LitVal F v := by
  induction h with
  | eval_none => exact nofun
  | eval_some _ he _ ih =>
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact litVal_of_computable hσ (hc _ List.mem_cons_self).1 (hc _ List.mem_cons_self).2 he
    · exact ih hσ (fun e' h' => hc e' (List.mem_cons_of_mem _ h')) v hv

/-- The type of a primitive literal whose type is not `real` is a type of literals. -/
private theorem isLitMonoTy_ty {c : LConst} (hc : c.isPrimitive = true)
    (h : notRealResult c.ty = true) : isLitMonoTy c.ty = true := by
  cases c <;> first | rfl | cases h | cases hc

/-- A value of a type of literals is the value of a literal. -/
private theorem litVal_of_valueOfTy {F : Expression.Factory} {v : Expression.Val}
    {ty : Expression.Ty} (hty : isLitTy ty = true) (h : HasVal.valueOfTy F v ty) : LitVal F v := by
  obtain ⟨htc, hv⟩ := h
  simp only [isLitTy, hv, Option.any_some] at hty
  obtain ⟨c, hcp, hcr, hc⟩ := eq_ofConst_of_isLitMonoTy hty
  exact ⟨c, hcp, hcr, htc ▸ hc⟩

/-- A value of the type of the value a variable of a store of literals holds is the value of a
    literal. -/
private theorem litVal_of_valueOfStoredTy {F : Expression.Factory} {σ : CoreStore}
    {x : CoreIdent} {v : Expression.Val} (hσ : LitStore F σ)
    (h : HasVal.valueOfStoredTy (P := Expression) F σ x v) : LitVal F v := by
  obtain ⟨prev, ty, hp, ⟨-, hpt⟩, hvt⟩ := h
  obtain ⟨c, hcp, hcr, rfl⟩ := hσ x prev hp
  refine litVal_of_valueOfTy ?_ hvt
  simp only [isLitTy, hpt, Option.any_some]
  exact (congrArg isLitMonoTy (LConst.ty_isGround c)).trans (isLitMonoTy_ty hcp hcr)

/-- **Base commands of the fragment keep stores of literals**: a reference evaluation of a base
    command in the fragment from a store of literals ends in a store of literals and emits only
    events the fragment covers. -/
private theorem evalCmdE_inFragment {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {σ σ' : SemanticStore Expression} {c : Imperative.Cmd Expression} {evs : Trace Expression}
    (h : EvalCmdE (P := Expression) F σ c σ' evs) (hσ : LitStore F σ)
    (hc : CmdInFragment (InFragment F.factory) (.cmd c)) :
    LitStore F σ' ∧ ∀ ev ∈ evs, EventInFragment F ev := by
  have hcomp : ∀ e, InFragment F.factory e → ComputableEval F σ e :=
    fun e he => computableEval_of_inFragment hF he fun x _ v hx => (hσ x v hx).imp fun _ h => ⟨h.1, h.2.2⟩
  cases h with
  | eval_init he i _ _ =>
    exact ⟨hσ.init (litVal_of_computable hσ (hcomp _ (hc.2 _ rfl)) (hc.2 _ rfl).2 he) i, nofun⟩
  | eval_init_unconstrained i hty _ => exact ⟨hσ.init (litVal_of_valueOfTy hc.1 hty) i, nofun⟩
  | eval_set he u _ _ =>
    exact ⟨hσ.set (litVal_of_computable hσ (hcomp _ (hc _ rfl)) (hc _ rfl).2 he) u, nofun⟩
  | eval_set_nondet u hty _ => exact ⟨hσ.set (litVal_of_valueOfStoredTy hσ hty) u, nofun⟩
  | eval_assert => exact ⟨hσ, by simpa [EventInFragment] using ⟨hσ, hc⟩⟩
  | eval_assume => exact ⟨hσ, by simp [EventInFragment]⟩
  | eval_cover => exact ⟨hσ, by simpa [EventInFragment] using ⟨hσ, hc⟩⟩

/-- Projecting a store of literals through a parent store gives a store of literals. -/
private theorem LitStore.project {F : Expression.Factory} {σp σ : CoreStore} (hσ : LitStore F σ) :
    LitStore F (projectStore σp σ) := fun x v h => by
  unfold projectStore at h
  split at h
  · exact hσ x v h
  · cases h

/-- **Steps of the fragment keep stores of literals**: a reference step over a command relation
    that keeps stores of literals at the factory `F`, from a configuration in the fragment whose
    environments have the factory `F` and stores of literals, reaches such a configuration and
    emits only events the fragment covers. -/
private theorem step_inFragment {F : Expression.Factory} {E : CoreCmdRel}
    (hE : ∀ σ cmd σ' evs, E F σ cmd σ' evs → LitStore F σ →
      CmdInFragment (InFragment F.factory) cmd → LitStore F σ' ∧ ∀ ev ∈ evs, EventInFragment F ev)
    {x y : CoreConfig} {evs : List (Event Expression)} (hs : StepStmtE Expression E x evs y)
    (hx : ConfigLit F x) (hxc : ConfigInFragment (InFragment F.factory) x) :
    ConfigLit F y ∧ ConfigInFragment (InFragment F.factory) y ∧
      ∀ ev ∈ evs, EventInFragment F ev := by
  induction hs with
  | step_cmd h =>
    obtain ⟨hf, hl⟩ := hx
    rw [hf] at h
    obtain ⟨hl', hev⟩ := hE _ _ _ _ h hl hxc
    exact ⟨⟨hf, hl'⟩, trivial, hev⟩
  | step_seq_inner _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih hx hxc.1
    exact ⟨h1, ⟨h2, hxc.2⟩, h3⟩
  | step_block_body _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih hx hxc
    exact ⟨h1, h2, h3⟩
  | step_block_done | step_block_exit_match =>
    exact ⟨⟨hx.1, hx.2.project⟩, trivial, nofun⟩
  | step_block_exit_mismatch => exact ⟨⟨hx.1, hx.2.project⟩, trivial, nofun⟩
  | _ =>
    simp_all [ConfigLit, ConfigInFragment, StmtInFragment, BlockInFragment, InFragment]

/-- Runs of the fragment keep stores of literals: the multi-step form of `step_inFragment`. -/
private theorem star_inFragment {F : Expression.Factory} {E : CoreCmdRel}
    (hE : ∀ σ cmd σ' evs, E F σ cmd σ' evs → LitStore F σ →
      CmdInFragment (InFragment F.factory) cmd → LitStore F σ' ∧ ∀ ev ∈ evs, EventInFragment F ev)
    {x y : CoreConfig} {evs : List (Event Expression)} (h : StepStmtStarE Expression E x evs y)
    (hx : ConfigLit F x) (hxc : ConfigInFragment (InFragment F.factory) x) :
    ConfigLit F y ∧ ConfigInFragment (InFragment F.factory) y ∧
      ∀ ev ∈ evs, EventInFragment F ev := by
  induction h with
  | refl => exact ⟨hx, hxc, nofun⟩
  | step _ _ _ _ _ hs _ ih =>
    obtain ⟨h1, h2, h3⟩ := step_inFragment hE hs hx hxc
    obtain ⟨h4, h5, h6⟩ := ih h1 h2
    exact ⟨h4, h5, fun ev hev => (List.mem_append.1 hev).elim (h3 ev) (h6 ev)⟩

/-- A CFG configuration of the fragment whose environment has the factory `F` and a store of
    literals: its CFG is in the fragment (`CFGInFragment`), and so are the residual commands and
    the transfer of the block it executes. -/
private def CFGConfigOK (F : Expression.Factory) (P : Expression.Expr → Prop) :
    CFGConfig String Command Expression → Prop
  | .atBlock g _ ρ => CFGInFragment P g ∧ ρ.factory = F ∧ LitStore F ρ.store
  | .inBlock g _ cs tr ρ => CFGInFragment P g ∧ (∀ c ∈ cs, CmdInFragment P c) ∧
      TransferInFragment P tr ∧ ρ.factory = F ∧ LitStore F ρ.store
  | .terminal ρ => ρ.factory = F ∧ LitStore F ρ.store

/-- **CFG steps of the fragment keep stores of literals**: a reference CFG step over a command
    relation that keeps stores of literals at the factory `F`, from a CFG configuration of the
    fragment whose environment has the factory `F` and a store of literals (`CFGConfigOK`),
    reaches such a CFG configuration and emits only events the fragment covers. -/
private theorem cfgStep_inFragment {F : Expression.Factory} {E : CoreCmdRel}
    (hE : ∀ σ cmd σ' evs, E F σ cmd σ' evs → LitStore F σ →
      CmdInFragment (InFragment F.factory) cmd → LitStore F σ' ∧ ∀ ev ∈ evs, EventInFragment F ev)
    {x y : CFGConfig String Command Expression} {evs : List (Event Expression)}
    (hs : StepCFGE Expression E x evs y) (hx : CFGConfigOK F (InFragment F.factory) x) :
    CFGConfigOK F (InFragment F.factory) y ∧ ∀ ev ∈ evs, EventInFragment F ev := by
  cases hs with
  | step_cmd h =>
    obtain ⟨hg, hcs, htr, hf, hl⟩ := hx
    rw [hf] at h
    obtain ⟨hl', hev⟩ := hE _ _ _ _ h hl (hcs _ List.mem_cons_self)
    exact ⟨⟨hg, fun c hc => hcs c (List.mem_cons_of_mem _ hc), htr, hf, hl'⟩, hev⟩
  | fetch h =>
    obtain ⟨hg, hf, hl⟩ := hx
    obtain ⟨_, _, he, -⟩ := List.lookup_eq_some_iff.1 h
    obtain ⟨h1, h2⟩ := hg _ (he ▸ List.mem_append_right _ List.mem_cons_self)
    exact ⟨⟨hg, h1, h2, hf, hl⟩, nofun⟩
  | goto_true | goto_false => exact ⟨⟨hx.1, hx.2.2.2⟩, nofun⟩
  | finish => exact ⟨hx.2.2.2, nofun⟩

/-- CFG runs of the fragment keep stores of literals: the multi-step form of
    `cfgStep_inFragment`. -/
private theorem cfgStar_inFragment {F : Expression.Factory} {E : CoreCmdRel}
    (hE : ∀ σ cmd σ' evs, E F σ cmd σ' evs → LitStore F σ →
      CmdInFragment (InFragment F.factory) cmd → LitStore F σ' ∧ ∀ ev ∈ evs, EventInFragment F ev)
    {x y : CFGConfig String Command Expression} {evs : List (Event Expression)}
    (h : StepCFGStarE Expression E x evs y) (hx : CFGConfigOK F (InFragment F.factory) x) :
    CFGConfigOK F (InFragment F.factory) y ∧ ∀ ev ∈ evs, EventInFragment F ev := by
  induction h with
  | refl => exact ⟨hx, nofun⟩
  | step _ _ _ _ _ hs _ ih =>
    obtain ⟨h1, h2⟩ := cfgStep_inFragment hE hs hx
    obtain ⟨h3, h4⟩ := ih h1
    exact ⟨h3, fun ev hev => (List.mem_append.1 hev).elim (h2 ev) (h4 ev)⟩

/-- The assertion events a list of specification clauses in the fragment emits at a store of
    literals are covered by the fragment. -/
private theorem defaultAssertEvents_inFragment {F : Expression.Factory} {σ : CoreStore}
    {checks : ListMap String (Imperative.Check Expression)} (hσ : LitStore F σ)
    (hc : ∀ lc ∈ checks.toList, InFragment F.factory lc.2.expr) :
    ∀ ev ∈ Calls.defaultAssertEvents F σ checks, EventInFragment F ev := by
  intro ev hev
  simp only [Calls.defaultAssertEvents, List.mem_filterMap] at hev
  obtain ⟨lc, hlc, hev⟩ := hev
  split at hev
  · cases hev
    exact ⟨rfl, hσ, hc lc hlc⟩
  · cases hev

/-- The callee frame a call of the fragment builds from a store of literals is a store of
    literals. -/
private theorem callEntry_lit {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {σ σAO : CoreStore} {p : Procedure} {args : List (CallArg Expression)} (hσ : LitStore F σ)
    (hargs : ∀ e ∈ Calls.getInputExprs args, InFragment F.factory e)
    (he : CallEntry F σ p args σAO) : LitStore F σAO := by
  obtain ⟨ins, outs, hins, houts, σA, σIO, hA, hIO, rfl⟩ := he
  have hA' := LitStore.inits (σ := emptyStore) (fun _ _ h => by cases h)
    (hσ.evals (fun e h => ⟨computableEval_of_inFragment hF (hargs e h)
      fun x _ v hx => (hσ x v hx).imp fun _ h => ⟨h.1, h.2.2⟩, (hargs e h).2⟩) hins) hA
  have hIO' := hA'.inits (hσ.read houts) hIO
  intro x v hx
  unfold Calls.withOldSnapshots at hx
  split at hx
  · exact hIO' _ v hx
  · exact hIO' x v hx

/-- **Commands of the fragment keep stores of literals**, calls included: in a program every
    procedure of which is in the fragment, a reference evaluation of a command of the fragment at
    the factory `F` from a store of literals ends in a store of literals and emits only events the
    fragment covers. -/
private theorem evalCommandE_inFragment {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {π : String → Option Procedure}
    (hprocs : ∀ n p, π n = some p → ProcInFragment (InFragment F.factory) p)
    {f : Expression.Factory} {σ σ' : CoreStore} {cmd : Command} {evs : Trace Expression}
    (h : EvalCommandE π f σ cmd σ' evs) :
    f = F → LitStore F σ → CmdInFragment (InFragment F.factory) cmd →
      LitStore F σ' ∧ ∀ ev ∈ evs, EventInFragment F ev := by
  induction h using EvalCmdExtE.induct with
  | cmd_sem h =>
    rintro rfl hσ hc
    exact evalCmdE_inFragment hF h hσ hc
  | @call_sem _ _ _ _ _ σF bev _ f _ hπ he _ hx ih =>
    intro hf hσ hc
    subst f
    obtain ⟨hbody, hpre, hpost⟩ := hprocs _ _ hπ
    have hAO := callEntry_lit hF hσ hc he
    obtain ⟨hfin, hbev⟩ : LitStore F σF ∧ ∀ ev ∈ bev, EventInFragment F ev := by
      rcases ih with ⟨ss', ρ', hss', rfl, hr⟩ | ⟨g', ρ', hg', rfl, hr⟩ <;>
        rcases hbody with ⟨ss, hss, hblk⟩ | ⟨g, hg, hcfg⟩
      · cases hss.symm.trans hss'
        obtain ⟨⟨-, hfin⟩, -, hbev⟩ :=
          star_inFragment (fun _ _ _ _ ⟨_, hm⟩ hl hc => hm rfl hl hc) hr ⟨rfl, hAO⟩ hblk
        exact ⟨hfin, hbev⟩
      · cases hss'.symm.trans hg
      · cases hg'.symm.trans hss
      · cases hg.symm.trans hg'
        obtain ⟨⟨-, hfin⟩, hbev⟩ :=
          cfgStar_inFragment (fun _ _ _ _ ⟨_, hm⟩ hl hc => hm rfl hl hc) hr ⟨hcfg, rfl, hAO⟩
        exact ⟨hfin.project, hbev⟩
    obtain ⟨-, outs, hread, hupd, -⟩ := hx
    refine ⟨hσ.sets (hfin.read hread) hupd, fun ev hev => ?_⟩
    rcases List.mem_append.1 hev with hev | hev
    · rcases List.mem_append.1 hev with hev | hev
      · refine defaultAssertEvents_inFragment hAO (fun lc hlc => ?_) ev hev
        obtain ⟨lc', hlc', rfl⟩ := List.mem_map.1 hlc
        exact hpre lc' hlc'
      · exact hbev ev hev
    · exact defaultAssertEvents_inFragment hfin hpost ev hev

/-- The statement in active position of a configuration of the fragment whose environments have
    the factory `F` and stores of literals is in the fragment, under such an environment. -/
private theorem ActiveStmt.inFragment {F : Expression.Factory} {P : Expression.Expr → Prop}
    {x : CoreConfig} {ρ : Imperative.Env Expression} {s : Statement} (ha : ActiveStmt x ρ s)
    (hx : ConfigLit F x) (hxc : ConfigInFragment P x) :
    (ρ.factory = F ∧ LitStore F ρ.store) ∧ StmtInFragment P s := by
  induction ha with
  | here => exact ⟨hx, hxc⟩
  | seq _ ih => exact ih hx hxc.1
  | block _ ih => exact ih hx hxc

/-- The expressions a statement of the fragment evaluates are in the fragment. -/
private theorem StmtInFragment.evalExprs {P : Expression.Expr → Prop} {s : Statement}
    (h : StmtInFragment P s) : ∀ e ∈ stmtEvalExprs s, P e := by
  intro e he
  unfold stmtEvalExprs at he
  split at he <;> simp only [List.mem_singleton, List.not_mem_nil] at he
  all_goals first
    | (subst he; first | exact h.1 _ rfl | exact h.2 _ rfl | exact h _ rfl)
    | exact h e he

mutual
/-- **Programs of the fragment keep stores of literals along their visits**: from a configuration
    of the fragment whose environments have the factory `F` and stores of literals, in a program
    every procedure of which is in the fragment, every configuration the reference semantics
    visits (`Visits`) is such a configuration. -/
private theorem visits_inFragment {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {π : String → Option Procedure}
    (hprocs : ∀ n p, π n = some p → ProcInFragment (InFragment F.factory) p) {c : CoreConfig}
    (hc : ConfigLit F c) (hcc : ConfigInFragment (InFragment F.factory) c) :
    ∀ {d : CoreConfig}, Visits π c d →
      ConfigLit F d ∧ ConfigInFragment (InFragment F.factory) d
  | _, .refl => ⟨hc, hcc⟩
  | _, .step hv hs => by
    obtain ⟨h1, h2⟩ := visits_inFragment hF hprocs hc hcc hv
    obtain ⟨h1, h2, -⟩ := step_inFragment
      (fun _ _ _ _ h hl hcmd => evalCommandE_inFragment hF hprocs h rfl hl hcmd) hs h1 h2
    exact ⟨h1, h2⟩
  | _, .call hv ha hp hb he => by
    obtain ⟨h1, h2⟩ := visits_inFragment hF hprocs hc hcc hv
    obtain ⟨⟨hf, hl⟩, hs⟩ := ha.inFragment h1 h2
    obtain ⟨⟨ss, hss, hblk⟩ | ⟨g, hg, -⟩, -, -⟩ := hprocs _ _ hp
    · cases hb.symm.trans hss
      rw [hf] at he ⊢
      exact ⟨⟨rfl, callEntry_lit hF hl hs he⟩, hblk⟩
    · cases hb.symm.trans hg
  | _, .cfgCall hv hp hb he => by
    obtain ⟨-, hcs, -, hf, hl⟩ := visitsCFG_inFragment hF hprocs hc hcc hv
    obtain ⟨⟨ss, hss, hblk⟩ | ⟨g, hg, -⟩, -, -⟩ := hprocs _ _ hp
    · cases hb.symm.trans hss
      rw [hf] at he ⊢
      exact ⟨⟨rfl, callEntry_lit hF hl (hcs _ List.mem_cons_self) he⟩, hblk⟩
    · cases hb.symm.trans hg

/-- Programs of the fragment keep stores of literals along their CFG visits: under the hypotheses
    of `visits_inFragment`, every CFG configuration the reference semantics visits in a CFG callee
    body (`VisitsCFG`) is a CFG configuration of the fragment whose environment has the factory
    `F` and a store of literals (`CFGConfigOK`). -/
private theorem visitsCFG_inFragment {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {π : String → Option Procedure}
    (hprocs : ∀ n p, π n = some p → ProcInFragment (InFragment F.factory) p) {c : CoreConfig}
    (hc : ConfigLit F c) (hcc : ConfigInFragment (InFragment F.factory) c) :
    ∀ {d : CFGConfig String Command Expression}, VisitsCFG π c d →
      CFGConfigOK F (InFragment F.factory) d
  | _, .call hv ha hp hb he => by
    obtain ⟨h1, h2⟩ := visits_inFragment hF hprocs hc hcc hv
    obtain ⟨⟨hf, hl⟩, hs⟩ := ha.inFragment h1 h2
    obtain ⟨⟨ss, hss, -⟩ | ⟨g, hg, hcfg⟩, -, -⟩ := hprocs _ _ hp
    · cases hb.symm.trans hss
    · cases hb.symm.trans hg
      rw [hf] at he ⊢
      exact ⟨hcfg, rfl, callEntry_lit hF hl hs he⟩
  | _, .cfgCall hv hp hb he => by
    obtain ⟨-, hcs, -, hf, hl⟩ := visitsCFG_inFragment hF hprocs hc hcc hv
    obtain ⟨⟨ss, hss, -⟩ | ⟨g, hg, hcfg⟩, -, -⟩ := hprocs _ _ hp
    · cases hb.symm.trans hss
    · cases hb.symm.trans hg
      rw [hf] at he ⊢
      exact ⟨hcfg, rfl, callEntry_lit hF hl (hcs _ List.mem_cons_self) he⟩
  | _, .step hv hs =>
    (cfgStep_inFragment (fun _ _ _ _ h hl hcmd => evalCommandE_inFragment hF hprocs h rfl hl hcmd)
      hs (visitsCFG_inFragment hF hprocs hc hcc hv)).1
end

/-- **The fragment's evaluations are computable** (the static criterion implies the run
    condition): in a program every procedure of which is in the fragment, on a factory meeting
    `FragmentFactoryWF`, every expression a reference run from a configuration of the fragment
    whose environments have the factory `F` and stores of literals evaluates, in structured and
    CFG callee bodies alike, is computable (`EvalsComputable`). -/
theorem evalsComputable_of_inFragment {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {π : String → Option Procedure}
    (hprocs : ∀ n p, π n = some p → ProcInFragment (InFragment F.factory) p) {c : CoreConfig}
    (hc : ConfigLit F c) (hcc : ConfigInFragment (InFragment F.factory) c) :
    EvalsComputable π c := by
  have hcomp : ∀ {σ : CoreStore} {e}, LitStore F σ → InFragment F.factory e →
      ComputableEval F σ e := fun hl he =>
    computableEval_of_inFragment hF he fun x _ v hx => (hl x v hx).imp fun _ h => ⟨h.1, h.2.2⟩
  refine ⟨fun d hd ρ s ha e he => ?_, fun d hd e he => ?_⟩
  · obtain ⟨hdl, hdc⟩ := visits_inFragment hF hprocs hc hcc hd
    obtain ⟨⟨hf, hl⟩, hs⟩ := ha.inFragment hdl hdc
    exact hf ▸ hcomp hl (hs.evalExprs e he)
  · have hd' := visitsCFG_inFragment hF hprocs hc hcc hd
    rcases d with _ | ⟨_, _, _ | ⟨cmd, _⟩, _ | _, _⟩ | _
    all_goals simp only [cfgEvalExprs, List.not_mem_nil, List.mem_singleton] at he
    · obtain ⟨-, -, htr, hf, hl⟩ := hd'
      subst he
      exact hf ▸ hcomp hl htr
    all_goals obtain ⟨-, hcs, -, hf, hl⟩ := hd'
    all_goals
      exact hf ▸ hcomp hl
        (StmtInFragment.evalExprs (s := .cmd cmd) (hcs cmd List.mem_cons_self) e he)

/-- Every event a reference run of the fragment emits, from a configuration of the fragment whose
    environments have the factory `F` and stores of literals, in a program every procedure of
    which is in the fragment, is covered by the fragment (`EventInFragment`). -/
theorem run_events_inFragment {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {π : String → Option Procedure}
    (hprocs : ∀ n p, π n = some p → ProcInFragment (InFragment F.factory) p) {c c' : CoreConfig}
    {evs : List (Event Expression)} (hc : ConfigLit F c)
    (hcc : ConfigInFragment (InFragment F.factory) c) (h : CoreStepStarE π c evs c') :
    ∀ ev ∈ evs, EventInFragment F ev :=
  (star_inFragment (fun _ _ _ _ h hl hcmd => evalCommandE_inFragment hF hprocs h rfl hl hcmd)
    h hc hcc).2.2

/-! ## Completeness of Core replay on programs of the fragment -/

/-- **The static criterion on Core programs**: the statements a configuration still executes and
    every procedure of `procs` are in the fragment of the factory `F` (`inFragment`): every type
    of an `init` is a type of literals, every deterministic guard, right-hand side, assertion and
    cover condition, call argument and specification clause is in the computable fragment, and so
    is every guard of a conditional transfer of a CFG body. -/
@[expose] def programInFragment (F : Lambda.Factory CoreLParams) (procs : List Procedure)
    (c : CoreConfig) : Bool :=
  configInFragment (inFragment F) c && procs.all (procInFragment (inFragment F))

/-- The fragment predicate `inFragment` reads as `InFragment`. -/
private theorem inFragment_eq (F : Lambda.Factory CoreLParams) :
    (inFragment F · = true) = InFragment F :=
  funext fun e => propext (inFragment_iff F e)

/-- **The static criterion reads as**: the configuration and every procedure of `procs` are in
    the fragment (`ConfigInFragment`, `ProcInFragment` with the expressions of the fragment). -/
theorem programInFragment_iff (F : Lambda.Factory CoreLParams) (procs : List Procedure)
    (c : CoreConfig) :
    programInFragment F procs c = true ↔ ConfigInFragment (InFragment F) c ∧
      ∀ p ∈ procs, ProcInFragment (InFragment F) p := by
  simp only [programInFragment, Bool.and_eq_true, configInFragment_iff, List.all_eq_true,
    procInFragment_iff, inFragment_eq]

/-- The event `ev` is a failure of the target obligation under the reference evaluator: an
    assertion of the target whose condition evaluates to `ffVal`, or a cover of the target whose
    condition evaluates to `ttVal`. -/
@[expose] def RefFailure (target : AssertId Expression) : Event Expression → Prop
  | .assert a => target.label = a.label ∧ target.md = a.metadata ∧
      Expression.eval a.factory a.store a.expr = some (HasBool.ffVal a.factory)
  | .cover a => target.label = a.label ∧ target.md = a.metadata ∧
      Expression.eval a.factory a.store a.expr = some (HasBool.ttVal a.factory)
  | .assume _ => False

/-- A failure under the reference evaluator of an event the fragment covers has a computable
    condition. -/
private theorem computableFailure_of_ref {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {target : AssertId Expression} :
    ∀ {ev : Event Expression}, EventInFragment F ev → RefFailure target ev →
      ComputableFailure target ev
  | .assert _, ⟨hf, hl, he⟩, ⟨h1, h2, h3⟩ =>
    ⟨h1, h2, h3, hf ▸ computableEval_of_inFragment hF he fun x _ v hx =>
      (hl x v hx).imp fun _ h => ⟨h.1, h.2.2⟩⟩
  | .cover _, ⟨hf, hl, he⟩, ⟨h1, h2, h3⟩ =>
    ⟨h1, h2, h3, hf ▸ computableEval_of_inFragment hF he fun x _ v hx =>
      (hl x v hx).imp fun _ h => ⟨h.1, h.2.2⟩⟩

/-- The facts the static criterion gives about a program whose procedures are among `procs`:
    its procedures are in the fragment, and every expression a run from `c` evaluates is
    computable. -/
private theorem criterion_facts {F : Expression.Factory} (hF : FragmentFactoryWF F)
    {π : String → Option Procedure} {procs : List Procedure}
    (hπ : ∀ n p, π n = some p → p ∈ procs) {c : CoreConfig}
    (hcrit : programInFragment F.factory procs c = true) (hc : ConfigLit F c) :
    (∀ n p, π n = some p → ProcInFragment (InFragment F.factory) p) ∧ EvalsComputable π c := by
  obtain ⟨hcc, hps⟩ := (programInFragment_iff _ _ _).1 hcrit
  have hprocs := fun n p h => hps p (hπ n p h)
  exact ⟨hprocs, evalsComputable_of_inFragment hF hprocs hc hcc⟩

/-- **Completeness of Core replay on programs of the fragment** (reference ⇒ engine).  Let the
    procedures of `π` be among `procs` and the modeled factory meet `FragmentFactoryWF`.  If the
    configuration `cex.cfg` stands for and the procedures pass the static criterion
    (`programInFragment`), its environments have the factory and stores of literals, and a reference
    run of `π` from it emits a failure of the target (`RefFailure`), then the run has a choice
    sequence `cs` (`Calls.RunChoices`) such that, whenever `cex.oracle` begins with a runtime
    segment witnessing `cs` (`OracleWitness`) that passes `choose`'s type check (`OracleTyped`),
    `cex` replayed with its own oracle reaches that failure (`genuine`) at every sufficiently large
    fuel and call-depth limit. -/
theorem core_replayComplete_of_programInFragment {F : Expression.Factory}
    (π : String → Option Procedure) (procs : List Procedure)
    (hπ : ∀ n p, π n = some p → p ∈ procs) (hF : FragmentFactoryWF F)
    (target : AssertId Expression) (cex : CexA Expression Command)
    {evs : List (Event Expression)} {final : Config Expression Command} (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hcrit : programInFragment F.factory procs (cex.cfg.abs F) = true)
    (hstart : ConfigLit F (cex.cfg.abs F)) (hrun : CoreStepStarE π (cex.cfg.abs F) evs final)
    (hfail : ∃ ev ∈ evs, RefFailure target ev) :
    ∃ cs, Calls.RunChoices π (cex.cfg.abs F) evs final cs ∧
      ∀ rs : List Expression.Expr, rs <+: cex.oracle → OracleWitness F rs cs →
        OracleTyped F (ChoiceRecord.typed Expression) rs cs →
          ∃ f0, ∀ fuel d, f0 ≤ fuel → f0 ≤ d → genuine π target fuel cex d := by
  obtain ⟨hprocs, hcomp⟩ := criterion_facts hF hπ hcrit hstart
  obtain ⟨ev, hev, hf⟩ := hfail
  have hcf := computableFailure_of_ref hF
    (run_events_inFragment hF hprocs hstart ((programInFragment_iff _ _ _).1 hcrit).1 hrun ev hev)
    hf
  exact core_replayComplete_of_evalsComputable π target cex hd ht hcomp hrun
    ⟨ev, hev, hcf⟩

/-- **Completeness of Core replay on deterministic programs of the fragment** (reference ⇒
    engine).  Under the hypotheses of `core_replayComplete_of_programInFragment`, if moreover the
    program is deterministic (`Calls.ProgDeterministic`), then `cex`, replayed with its own oracle,
    reaches the failure the reference run emits (`genuine`) at every sufficiently large fuel and
    call-depth limit. -/
theorem core_replayComplete_of_deterministic_programInFragment {F : Expression.Factory}
    (π : String → Option Procedure) (procs : List Procedure)
    (hπ : ∀ n p, π n = some p → p ∈ procs) (hF : FragmentFactoryWF F)
    (target : AssertId Expression) (cex : CexA Expression Command)
    {evs : List (Event Expression)} {final : Config Expression Command} (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hcrit : programInFragment F.factory procs (cex.cfg.abs F) = true)
    (hstart : ConfigLit F (cex.cfg.abs F)) (hdet : Calls.ProgDeterministic π (cex.cfg.abs F))
    (hrun : CoreStepStarE π (cex.cfg.abs F) evs final) (hfail : ∃ ev ∈ evs, RefFailure target ev) :
    ∃ f0, ∀ fuel d, f0 ≤ fuel → f0 ≤ d → genuine π target fuel cex d := by
  obtain ⟨cs, hcs, h⟩ := core_replayComplete_of_programInFragment π procs hπ hF target cex
    hd ht hcrit hstart hrun hfail
  obtain rfl := Calls.runChoices_nil_of_deterministic hdet hcs
  exact h [] List.nil_prefix ⟨rfl, nofun⟩ nofun

/-- **Whole-run Core `EvalM` completeness on deterministic programs of the fragment** (reference ⇒
    engine).  Let the procedures of `π` be among `procs` and the modeled factory meet
    `FragmentFactoryWF`.  If `start` and the procedures pass the static criterion
    (`programInFragment`), the environments of `start` have the factory and stores of literals, the
    program is deterministic, and a reference run of `π` from `start` ends in a done configuration
    `final` whose events go through at `opts` for every list of well-formed runtime events standing
    for them, then `runCoreInterp π` at `EvalM` from every interpreter configuration denoting
    `start` reaches one denoting `final`, from every state at every large enough fuel and call-depth
    limit, prepending runtime events denoting exactly the run's events to the trace. -/
theorem core_runCoreInterp_complete_eval_of_programInFragment {F : Expression.Factory}
    (π : String → Option Procedure) (procs : List Procedure)
    (hπ : ∀ n p, π n = some p → p ∈ procs) (hF : FragmentFactoryWF F)
    (opts : EvalOpts)
    {start final : Config Expression Command} {evs : List (Event Expression)}
    (istart : IConfig Expression Command) (hstart : istart.Denotes F start)
    (hcrit : programInFragment F.factory procs start = true) (hlits : ConfigLit F start)
    (hdet : Calls.ProgDeterministic π start) (hrun : CoreStepStarE π start evs final)
    (hdone : Config.Done final)
    (hemit : ∀ revs : List (IEvent Expression), (∀ ev ∈ revs, Calls.EvGood F ev) →
      revs.map (REvent.abs F) = evs → EvalEmitsOk opts revs) (st : EvalState) :
    ∃ (f0 : Nat) (final' : IConfig Expression Command) (st' : EvalState), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        evalRun (runCoreInterp π fuel istart d) opts st = (.ok final', st'))
      ∧ obsEval.TraceExt F st st' evs := by
  obtain ⟨-, hcomp⟩ := criterion_facts hF hπ hcrit hlits
  exact core_runCoreInterp_complete_eval_of_computable π opts istart hstart hdet hcomp
    hrun hdone hemit st

end

end Core
