/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CFGSemantics
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.LExprDenoteEval
public import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExpr
import Strata.Util.ListMapProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Util.FuncAttr
public import Strata.Languages.Core.FactoryWF

/-!
## `Imperative.WellFormedSemanticEval*` instances for Core

Core's evaluator is denotational (`Lambda.LExpr.denoteEval`, see `Core.Expression`).  This
module proves the `WellFormedSemanticEvalVal`/`Var`/`ExprCongr`/`Mono`/`Rename`/`Bool`/`Int`
/`SubstLits` laws for it, from the generic laws of `denoteEval`, and bundles them as
`coreEvaluator_WellFormedSemanticEval`.  Only the negation law needs a hypothesis on the
factory: that it resolves `Bool.Not` to Core's built-in negation, so that every consistent
interpretation interprets it as `!`.

It also provides the factory-membership facts `coreFactory_boolNot`, `coreFactory_intLt`,
`coreFactory_intLe`, `coreFactory_intGe`, `coreFactory_intGt`, `coreFactory_intAdd`,
`coreFactory_intSub` and `coreFactory_intMul`, sharing the generic `coreFactory_get?_of_mem`,
and the operator expressions `coreIntLeOpExpr` / `coreIntAddOpExpr`.

For operators with a concrete evaluator, `opInterp_of_concreteEval` says that every consistent
model interprets the operator as its concrete evaluator computes, and `eval_app2_op` evaluates
an operator applied to two values to its interpretation at them.
-/

---------------------------------------------------------------------

public section

namespace Core

open Imperative

abbrev CoreEval := SemanticEval Expression
abbrev CoreStore := SemanticStore Expression

/-- Core's evaluator is denotational evaluation. -/
theorem Expression.eval_eq (f : Expression.Factory) (σ : CoreStore) (e : Expression.Expr) :
    Expression.eval f σ e = Lambda.LExpr.denoteEval f σ e := rfl

/-- The free variables of a Core expression are the names of its `freeVars`. -/
private theorem mem_getFvars_iff {e : Expression.Expr} {x : CoreIdent} :
    x ∈ HasFvars.getFvars (P := Expression) e ↔ ∃ ty, (x, ty) ∈ e.freeVars := by
  show x ∈ Lambda.LExpr.LExpr.getVars e ↔ _
  rw [Lambda.getVars_eq_freeVars_idents]
  simp

/-- The Core evaluator produces only values of the factory and evaluates the Boolean
    constants to the factory's Booleans. -/
theorem coreEvaluator_WellFormedSemanticEvalVal (f : Expression.Factory) :
    WellFormedSemanticEvalVal (P := Expression) f where
  outputsAreValues := fun _ _ _ _ heval => Lambda.LExpr.denoteEval_tc heval
  eval_tt := fun _ => Lambda.LExpr.denoteEval_boolConst
  eval_ff := fun _ => Lambda.LExpr.denoteEval_boolConst

/-- The Core evaluator resolves free variables via the store: evaluating a free
    variable yields its store binding (on well-formed stores). -/
theorem coreEvaluator_WellFormedSemanticEvalVar (f : Expression.Factory) :
    WellFormedSemanticEvalVar (P := Expression) f := by
  intro e v σ hwfs hget
  cases e with
  | fvar m x ty =>
    simp only [HasFvar.getFvar, Option.some.injEq] at hget
    subst hget
    show Lambda.LExpr.denoteEval f σ (.fvar m x ty) = σ x
    cases hx : σ x with
    | none => exact Lambda.LExpr.denoteEval_fvar_none hx
    | some w => exact Lambda.LExpr.denoteEval_fvar hx (hwfs x w hx)
  | _ => simp [HasFvar.getFvar] at hget

/-- The Core evaluator agrees on stores that agree on the free variables of the
    expression. -/
theorem coreEvaluator_WellFormedSemanticEvalExprCongr (f : Expression.Factory) :
    WellFormedSemanticEvalExprCongr (P := Expression) f := by
  intro e σ σ' _ _ hagree
  exact Lambda.LExpr.denoteEval_congr e fun x ty hx => hagree x (mem_getFvars_iff.mpr ⟨ty, hx⟩)

/-- The Core evaluator is monotone under store extension. -/
theorem coreEvaluator_WellFormedSemanticEvalMono (f : Expression.Factory) :
    WellFormedSemanticEvalMono (P := Expression) f :=
  fun _ _ _ _ hext heval => Lambda.LExpr.denoteEval_mono hext heval

/-- The Core evaluator commutes with substituting variables for variables
    (`WellFormedSemanticEvalRename`): the substituted variables are re-annotated from the
    store, so renaming by a variable-only map is reading the store through it. -/
theorem coreEvaluator_WellFormedSemanticEvalRename (f : Expression.Factory) :
    WellFormedSemanticEvalRename (P := Expression) f := by
  intro e σ' sm _ hVarsDef
  show Lambda.LExpr.denoteEval f σ' (Lambda.LExpr.substFvars e sm) =
    Lambda.LExpr.denoteEval f (substStoreExpr σ' sm) e
  rw [Lambda.LExpr.substFvars_eq_substFvarsBy (T := CoreLParams)]
  refine Lambda.LExpr.denoteEval_substFvarsBy _ e (fun x _ r _ hr => ?_) (fun x _ _ hn => ?_)
  · obtain ⟨y, hy, -⟩ := hVarsDef x r hr
    cases r with
    | fvar m z ty =>
      simp only [HasFvar.getFvar, Option.some.injEq] at hy
      subst hy
      refine .inl ⟨m, z, ty, rfl, ?_⟩
      simp [substStoreExpr, hr, HasFvar.getFvar]
    | _ => simp [HasFvar.getFvar] at hy
  · simp [substStoreExpr, hn]

/-- The Core evaluator commutes with a by-name free-variable rename
    (`WellFormedSemanticEvalRenameFvars`). -/
theorem coreEvaluator_WellFormedSemanticEvalRenameFvars (f : Expression.Factory) :
    WellFormedSemanticEvalRenameFvars (P := Expression) f := by
  intro e σ' subst _ _
  have hmap : ∀ g (e : Expression.Expr),
      Expression.mapFvarNames g e = Lambda.LExpr.mapFvarNames g e := by
    intro g e
    induction e <;> simp_all [Expression.mapFvarNames, Lambda.LExpr.mapFvarNames]
  show Lambda.LExpr.denoteEval f σ' (Expression.renameFvars e subst) = _
  rw [Expression.renameFvars, hmap, Lambda.LExpr.denoteEval_mapFvarNames (T := CoreLParams)]
  rfl

/-- The Core evaluator satisfies the well-formedness conditions that do not involve the Boolean
    or integer operations (variables, values, agreement on free variables, renaming). -/
theorem coreEvaluator_WellFormedSemanticEvalBase (f : Expression.Factory) :
    WellFormedSemanticEvalBase (P := Expression) f :=
  ⟨coreEvaluator_WellFormedSemanticEvalVar f, coreEvaluator_WellFormedSemanticEvalVal f,
    coreEvaluator_WellFormedSemanticEvalExprCongr f,
    coreEvaluator_WellFormedSemanticEvalRename f⟩

/-- Substituting variables by variables holding the same value, or by Boolean literals equal to
    the value, preserves evaluation (`WellFormedSemanticEvalSubstLits`). -/
theorem coreEvaluator_WellFormedSemanticEvalSubstLits (F : Expression.Factory) :
    WellFormedSemanticEvalSubstLits (P := Expression) F := by
  intro σ σ' _ _ sm e hsm hrest
  show Lambda.LExpr.denoteEval F σ' (Lambda.LExpr.substFvars e sm) = Lambda.LExpr.denoteEval F σ e
  rw [Lambda.LExpr.substFvars_eq_substFvarsBy (T := CoreLParams)]
  refine Lambda.LExpr.denoteEval_substFvarsBy _ e (fun x _ r _ hr => ?_)
    (fun x ty hx hn => hrest x (mem_getFvars_iff.mpr ⟨ty, hx⟩) hn)
  rcases hsm x r hr with ⟨y, hv | ⟨_, hv⟩, hy, -⟩ | ⟨rfl, hσ⟩ | ⟨rfl, hσ⟩
  · exact .inl ⟨_, y, _, hv, hy⟩
  · exact .inl ⟨_, y, _, hv, hy⟩
  · exact .inr ⟨_, true, rfl, hσ⟩
  · exact .inr ⟨_, false, rfl, hσ⟩

/-!
## `WellFormedSemanticEvalBool` for Core
-/

/-- In every consistent interpretation of a factory that resolves `Bool.Not` to Core's
    built-in negation, `Bool.Not` is interpreted as `!`. -/
theorem boolNot_opInterp_of_lookup {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory)
    (hlookup : factory["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func)
    (b : Bool) :
    (model.opInterp "Bool.Not" (Lambda.LSort.mkArrow .bool [.bool]) b : Bool) = !b := by
  have hmem : "Bool.Not" ∈ factory :=
    Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget : factory["Bool.Not"]'hmem = (Lambda.boolNotFunc (T := CoreLParams)).func :=
    Lambda.Factory.getElem?_some_getElem hlookup
  have hsome : (factory["Bool.Not"]'hmem).concreteEval.isSome = true := by rw [hget]; rfl
  obtain ⟨ceval, h_ceval_eq⟩ := Option.isSome_iff_exists.mp hsome
  have h_ic := model.interpConsistent.2 "Bool.Not" hmem ceval h_ceval_eq
  rw [hget] at h_ic h_ceval_eq
  unfold Lambda.LFunc.InterpConsistentEval at h_ic
  have h_eval : ceval () [.boolConst () b] = some (.boolConst () (!b)) := by
    have key : (Lambda.boolNotFunc (T := CoreLParams)).func.concreteEval.bind
        (fun ce => ce () [.boolConst () b]) = some (.boolConst () (!b)) := by
      cases b <;> rfl
    rw [h_ceval_eq, Option.bind_some] at key
    exact key
  have vt : Lambda.TyVarVal := fun _ => .bool
  have fv : Lambda.FreeVarVal CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  have h_inst := h_ic vt fv () Lambda.Subst.empty [.boolConst () b] (.boolConst () (!b)) h_eval
  have h_args : List.Rel₂ (Lambda.LExpr.HasTypeA (T := CoreLParams) [])
      [.boolConst () b] [Lambda.LMonoTy.bool] := .cons .const .nil
  have h_result : Lambda.LExpr.HasTypeA (T := CoreLParams) [] (.boolConst () (!b)) .bool := .const
  have h_eq := h_inst h_args h_result
  change (!b) = model.opInterp "Bool.Not" (Lambda.LSort.mkArrow .bool [.bool]) b at h_eq
  exact h_eq.symm

/-- `boolNotFunc`'s operator expression is the `Bool.Not` operator at `bool → bool`. -/
private theorem boolNot_opExpr :
    (Lambda.boolNotFunc (T := CoreLParams)).opExpr =
      Lambda.LExpr.op () ⟨"Bool.Not", ()⟩ (some (Lambda.LMonoTy.arrow .bool .bool)) := rfl

/-- The Core evaluator respects Boolean negation when the factory resolves `Bool.Not`
    to Core's built-in negation. -/
theorem coreEvaluator_WellFormedSemanticEvalBool (f : Expression.Factory)
    (hBN : f.factory["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func) :
    Imperative.WellFormedSemanticEvalBool (P := Expression) f := by
  intro σ e
  have hevT : Expression.eval f σ Core.true = some (HasBool.ttVal f) :=
    Lambda.LExpr.denoteEval_boolConst
  have hevF : Expression.eval f σ Core.false = some (HasBool.ffVal f) :=
    Lambda.LExpr.denoteEval_boolConst
  have hTF : (some (HasBool.ttVal f) : Option Expression.Val) ≠ some (HasBool.ffVal f) :=
    fun h => HasBool.ttVal_ne_ffVal f (Option.some.inj h)
  have hApp : ∀ (e0 : Expression.Expr),
      (Expression.eval f σ e0 = some (HasBool.ttVal f) ↔
        Expression.eval f σ (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)
          = some (HasBool.ffVal f)) ∧
      (Expression.eval f σ e0 = some (HasBool.ffVal f) ↔
        Expression.eval f σ (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0)
          = some (HasBool.ttVal f)) := by
    intro e0
    have key : ∀ b', Expression.eval f σ
        (Lambda.LExpr.app () (Lambda.boolNotFunc (T := CoreLParams)).opExpr e0) =
          some (Lambda.SemValue.ofBool f.model.tcInterp b') ↔
        Expression.eval f σ e0 = some (Lambda.SemValue.ofBool f.model.tcInterp (!b')) := by
      intro b'
      show Lambda.LExpr.denoteEval f σ _ = _ ↔ Lambda.LExpr.denoteEval f σ e0 = _
      rw [boolNot_opExpr, Lambda.LExpr.denoteEval_app_op_bool_iff (T := CoreLParams)]
      constructor
      · rintro ⟨b, hb, rfl⟩
        have := boolNot_opInterp_of_lookup f.model hBN b
        simp only at this ⊢
        rw [this, Bool.not_not]
        exact hb
      · intro h
        refine ⟨!b', h, ?_⟩
        have := boolNot_opInterp_of_lookup f.model hBN (!b')
        simp only at this ⊢
        rw [this, Bool.not_not]
    exact ⟨(key false).symm, (key true).symm⟩
  cases e with
  | const m c =>
    cases c with
    | boolConst b =>
      cases b with
      | true =>
        exact ⟨⟨fun _ => hevF, fun _ => hevT⟩,
               ⟨fun h => absurd (hevT.symm.trans h) hTF,
                fun h => absurd (hevF.symm.trans h) hTF.symm⟩⟩
      | false =>
        exact ⟨⟨fun h => absurd (hevF.symm.trans h) hTF.symm,
                fun h => absurd (hevT.symm.trans h) hTF⟩,
               ⟨fun _ => hevT, fun _ => hevF⟩⟩
    | intConst i => exact hApp _
    | strConst s => exact hApp _
    | rationalConst r => exact hApp _
    | bitvecConst n bv => exact hApp _
  | op m o ty => exact hApp _
  | bvar m i => exact hApp _
  | fvar m x ty => exact hApp _
  | abs m pn ty b => exact hApp _
  | quant m k pn ty tr b => exact hApp _
  | app m fn arg => exact hApp _
  | ite m cc t el => exact hApp _
  | eq m e1 e2 => exact hApp _

/-- `Bool.Not` resolves in the concrete `Core.Factory` to `boolNotFunc`. -/
theorem coreFactory_boolNot :
    (Core.Factory)["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func := by
  have hname : (Lambda.boolNotFunc (T := CoreLParams)).func.name.name = "Bool.Not" := rfl
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hmem : (Lambda.boolNotFunc (T := CoreLParams)).func ∈ WFFactoryArray.map (·.func) := by
    refine Array.mem_map.mpr ⟨Lambda.boolNotFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail)
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory, ← hname]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup


/-!
## `WellFormedSemanticEvalInt` for Core
-/

/-- `intLtFunc`'s operator expression is the `Int.Lt` operator at `int → int → bool`. -/
private theorem intLt_opExpr :
    (Lambda.intLtFunc (T := CoreLParams)).opExpr =
      Lambda.LExpr.op () ⟨"Int.Lt", ()⟩
        (some (Lambda.LMonoTy.arrow .int (Lambda.LMonoTy.arrow .int .bool))) := rfl

/-- The Core evaluator reduces the comparison of two integer values to a Boolean. -/
theorem coreEvaluator_WellFormedSemanticEvalInt (f : Expression.Factory) :
    Imperative.WellFormedSemanticEvalInt (P := Expression) f where
  ltReduces := by
    intro σ x y nx ny hx hnx hy hny
    have hint : ∀ {v : Expression.Val}, HasInt.isNumeralVal v = Bool.true →
        v.sort = Lambda.LMonoTy.int.substTyVars f.tyVarVal := by
      intro v hv
      obtain ⟨tc, s, val⟩ := v
      simp only [HasInt.isNumeralVal] at hv
      cases s with
      | tcons n args =>
        simp only [Lambda.LSort.isInt] at hv
        split at hv
        · rename_i h; exact h.trans rfl
        · simp at hv
      | bitvec => simp [Lambda.LSort.isInt] at hv
    obtain ⟨v, hv, hvs⟩ := Lambda.LExpr.denoteEval_app2_op (m := ()) (m' := ()) (m'' := ())
      (o := ⟨"Int.Lt", ()⟩) (c := .bool) rfl rfl rfl hx (hint hnx) hy (hint hny)
    have hvtc := Lambda.LExpr.denoteEval_tc hv
    obtain ⟨tc, s, val⟩ := v
    simp only at hvs hvtc
    subst hvs hvtc
    show Lambda.LExpr.denoteEval f σ
          (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y) = _ ∨
        Lambda.LExpr.denoteEval f σ
          (.app () (.app () (Lambda.intLtFunc (T := CoreLParams)).opExpr x) y) = _
    rw [intLt_opExpr, hv]
    cases val
    · exact .inr rfl
    · exact .inl rfl

/-- A function in `WFFactoryArray` resolves in `Core.Factory` under its own name
    when supplied with its array-membership witness. -/
private theorem coreFactory_get?_of_mem {wf : Lambda.WFLFunc CoreLParams}
    (hmem : wf.func ∈ WFFactoryArray.map (·.func)) :
    (Core.Factory)[wf.func.name.name]? = some wf.func := by
  have hCoreFactory : Core.Factory
      = Lambda.Factory.ofArray (WFFactoryArray.map (·.func)) := rfl
  have hnodup : List.Nodup ((WFFactoryArray.map (·.func)).toList.map (·.name.name)) :=
    WFFactoryArray_func_name_nodup
  rw [hCoreFactory]
  exact Lambda.Factory.get?_ofArray_of_mem hmem hnodup

/-- `Int.Lt` resolves in the concrete `Core.Factory` to `intLtFunc`. -/
theorem coreFactory_intLt :
    (Core.Factory)["Int.Lt"]? = some (Lambda.intLtFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intLtFunc (T := CoreLParams)) (by
    refine Array.mem_map.mpr ⟨Lambda.intLtFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- `Int.Le` resolves in the concrete `Core.Factory` to `intLeFunc`. -/
theorem coreFactory_intLe :
    (Core.Factory)["Int.Le"]? = some (Lambda.intLeFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intLeFunc (T := CoreLParams)) (by
    refine Array.mem_map.mpr ⟨Lambda.intLeFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- `Int.Add` resolves in the concrete `Core.Factory` to `intAddFunc`. -/
theorem coreFactory_intAdd :
    (Core.Factory)["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intAddFunc (T := CoreLParams)) (by
    refine Array.mem_map.mpr ⟨Lambda.intAddFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- `Int.Sub` resolves in the concrete `Core.Factory` to `intSubFunc`. -/
theorem coreFactory_intSub :
    (Core.Factory)["Int.Sub"]? = some (Lambda.intSubFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intSubFunc (T := CoreLParams)) (by
    refine Array.mem_map.mpr ⟨Lambda.intSubFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- `Int.Ge` resolves in the concrete `Core.Factory` to `intGeFunc`. -/
theorem coreFactory_intGe :
    (Core.Factory)["Int.Ge"]? = some (Lambda.intGeFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intGeFunc (T := CoreLParams)) (by
    refine Array.mem_map.mpr ⟨Lambda.intGeFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- `Int.Gt` resolves in the concrete `Core.Factory` to `intGtFunc`. -/
theorem coreFactory_intGt :
    (Core.Factory)["Int.Gt"]? = some (Lambda.intGtFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intGtFunc (T := CoreLParams)) (by
    refine Array.mem_map.mpr ⟨Lambda.intGtFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- `Int.Mul` resolves in the concrete `Core.Factory` to `intMulFunc`. -/
theorem coreFactory_intMul :
    (Core.Factory)["Int.Mul"]? = some (Lambda.intMulFunc (T := CoreLParams)).func :=
  coreFactory_get?_of_mem (wf := Lambda.intMulFunc (T := CoreLParams)) (by
    refine Array.mem_map.mpr ⟨Lambda.intMulFunc (T := CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]
    unfold WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

/-- The concrete `Int.Le` operator expression on `Core.Factory`.  Exposed as a plain
    `def` (not `intLeFunc.opExpr` inline) so downstream modules — e.g. tests that are not
    `module`s — can name it without re-triggering the `String → Identifier` coercion that
    would demand an `Inhabited CoreLParams.IDMeta` instance. -/
def coreIntLeOpExpr : Expression.Expr := (Lambda.intLeFunc (T := CoreLParams)).opExpr

/-- The concrete `Int.Add` operator expression on `Core.Factory`; see `coreIntLeOpExpr`. -/
def coreIntAddOpExpr : Expression.Expr := (Lambda.intAddFunc (T := CoreLParams)).opExpr


/-!
## Instance of the full `WellFormedSemanticEval` bundle
--/

/-- The Core evaluator satisfies every well-formedness condition for a factory that resolves
    `Bool.Not` to Core's built-in negation. -/
theorem coreEvaluator_WellFormedSemanticEval (f : Expression.Factory)
    (hBN : f.factory["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func) :
    Imperative.WellFormedSemanticEval (P := Expression) f where
  bool := coreEvaluator_WellFormedSemanticEvalBool f hBN
  val := coreEvaluator_WellFormedSemanticEvalVal f
  var := coreEvaluator_WellFormedSemanticEvalVar f
  exprCongr := coreEvaluator_WellFormedSemanticEvalExprCongr f
  int := coreEvaluator_WellFormedSemanticEvalInt f
  mono := coreEvaluator_WellFormedSemanticEvalMono f
  rename := coreEvaluator_WellFormedSemanticEvalRename f

/-- Specialization of `coreEvaluator_WellFormedSemanticEval` to runtime factories over the
    concrete `Core.Factory`, which resolves `Bool.Not` to `boolNotFunc`. -/
theorem coreFactory_WellFormedSemanticEval (f : Expression.Factory)
    (hf : f.factory = Core.Factory) :
    Imperative.WellFormedSemanticEval (P := Expression) f :=
  coreEvaluator_WellFormedSemanticEval f (hf ▸ coreFactory_boolNot)

/-! ## Operators interpreted by their concrete evaluators -/

open _root_.Lambda

/-- **Interpretation of a concretely evaluated function.**  If the concrete evaluator of the
    function `name` maps the well-typed argument expressions `args` to `res`, every consistent
    model interprets `name` at the argument denotations as the denotation of `res`. -/
theorem opInterp_of_concreteEval {factory : Lambda.Factory CoreLParams}
    (model : Lambda.Interp factory) {name : String} {fn : Lambda.LFunc CoreLParams}
    (hlookup : factory[name]? = some fn) (hname : fn.name.name = name)
    {args : List Expression.Expr} {res : Expression.Expr}
    (heval : fn.concreteEval.bind (fun ce => ce () args) = some res)
    (vt : Lambda.TyVarVal) (fv : Lambda.FreeVarVal CoreLParams model.tcInterp)
    (h_args : List.Rel₂ (Lambda.LExpr.HasTypeA []) args
      ((fn.inputs.map Prod.snd).map (Lambda.LMonoTy.subst Lambda.Subst.empty)))
    (h_result : Lambda.LExpr.HasTypeA [] res (fn.output.subst Lambda.Subst.empty)) :
    Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil res _ h_result =
      Lambda.SortDenote.applyArgs model.tcInterp
        (model.opInterp name (Lambda.LSort.mkArrow
          ((fn.output.subst Lambda.Subst.empty).substTyVars vt)
          (((fn.inputs.map Prod.snd).map (Lambda.LMonoTy.subst Lambda.Subst.empty)).map
            (Lambda.LMonoTy.substTyVars vt))))
        (Lambda.denoteArgs model.tcInterp model.opInterp fv vt .nil args _ h_args) := by
  have hmem : name ∈ factory := Lambda.Factory.getElem?_some_implies_mem hlookup
  have hget := Lambda.Factory.getElem?_some_getElem hlookup
  cases hce : fn.concreteEval with
  | none => rw [hce] at heval; cases heval
  | some ceval =>
    rw [hce, Option.bind_some] at heval
    have h_ic := model.interpConsistent.2 name hmem ceval (by rw [hget]; exact hce)
    rw [hget] at h_ic
    rw [← hname]
    exact h_ic vt fv () Lambda.Subst.empty args res heval h_args h_result

/-- **Binary operator evaluation.**  An operator annotated `a → b → c`, at ground types,
    applied to arguments with values `va` and `vb` evaluates to `w` when the model interprets
    the operator at `va` and `vb` as `w`. -/
theorem eval_app2_op {f : Expression.Factory} (name : String) {m m' m'' : ExpressionMetadata}
    {a b c : LMonoTy}
    (ha : a.IsGround) (hb : b.IsGround) (hc : c.IsGround)
    {σ : CoreStore} {x y : Expression.Expr}
    {va : SortDenote f.model.tcInterp (a.substTyVars f.tyVarVal)}
    {vb : SortDenote f.model.tcInterp (b.substTyVars f.tyVarVal)}
    {w : SortDenote f.model.tcInterp (c.substTyVars f.tyVarVal)}
    (hx : Expression.eval f σ x = some ⟨f.model.tcInterp, a.substTyVars f.tyVarVal, va⟩)
    (hy : Expression.eval f σ y = some ⟨f.model.tcInterp, b.substTyVars f.tyVarVal, vb⟩)
    (hop : (f.model.opInterp name
        ((LMonoTy.arrow a (LMonoTy.arrow b c)).substTyVars f.tyVarVal)
      : SortDenote f.model.tcInterp (a.substTyVars f.tyVarVal) →
        SortDenote f.model.tcInterp (b.substTyVars f.tyVarVal) →
        SortDenote f.model.tcInterp (c.substTyVars f.tyVarVal)) va vb = w) :
    Expression.eval f σ
        (.app m (.app m' (.op m'' ⟨name, ()⟩ (some (LMonoTy.arrow a (LMonoTy.arrow b c)))) x) y) =
      some ⟨f.model.tcInterp, c.substTyVars f.tyVarVal, w⟩ := by
  rw [← hop]
  exact LExpr.denoteEval_app2_op_val (T := CoreLParams) ha hb hc hx hy

end Core

end -- public section
