/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.ModelToValuation
public import Strata.Languages.Core.Interpreter
public import Strata.DL.Imperative.Counterexample.Valuation
import all Strata.DL.Imperative.Counterexample.Valuation
import all Strata.DL.Lambda.LExprEvalProps
import Strata.Languages.Core.InterpreterProps
import Strata.Languages.Core.InterpreterDomainProps
import all Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.Util.RealProps
public import Strata.Languages.Core.InterpreterEvalSound
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps

/-! # Properties of the `(c) → (b)` translation: the soundness bridge and interpreted constants

**Key theorems.**
* `runVCCheck_genuine_isValuationObligationCex`: if the runtime VC check reports a validity query as
  `genuine` for a lifted model, the values it computes for the `.distinct` entries are primitive
  literals (`DistinctLiteralsAt`), and the bounded evaluator is sound at the factory `M`
  (`BoundedEvalSoundAt`), then every semantic valuation the model's runtime valuation
  (`modelValuation`) denotes satisfies the genuineness *specification* `IsValuationObligationCex`.
* `runVCCheck_genuine_fixpoint`: the same verdict holds for the check over the fixpoint
  evaluator `evalFully` on the same runtime valuation.
* `withConsts_getElem?`: `withConsts F I` holds, under each name, `F`'s function with
  `interpretConst I` applied, and nothing else.
* `withConsts_interpConsistent`: an interpretation of the operators consistent with
  `withConsts F I` is consistent with `F`. The constants are free in `F`, so fixing them
  to their values only restricts the interpretations; a counterexample under one of
  them is a counterexample with the constants left uninterpreted.
* `runVCCheck_genuine_isValuationObligationCexWith`: a `genuine` VC-check verdict under
  `withConsts F I` entails `IsValuationObligationCexWith F I` for the model's valuation.

`Core.runVCCheck` and the specification `IsValuationObligationCex` share one implementation,
`Imperative.valuationObligationCheck'` (assumption/goal reduction, `.det`-varDecl threading,
`.distinct`/`Nodup` distinctness, `BReduction.and` aggregation), and differ only in the
evaluator, the Boolean values and the value check they instantiate it with.  Each runtime step
on a runtime store is matched by a specification step on a semantic store it denotes
(`StoreDenotes`): evaluation by `BoundedEvalSoundAt`, the `.det`-varDecl value check by
`valueOfTy_of_ops`, Boolean reductions through the denotations of the Boolean literals, and
distinctness because distinct literals denote distinct values.  A `genuine` runtime verdict
requires every `.det` right-hand side on the path to evaluate (an extension that fails is
`cantValidate`), so the two checks thread related stores throughout. -/

namespace Core

open Imperative _root_.Lambda

public section

/-! ## The evaluator step -/

/-- `reduceBool'` transfers from the bounded to the fixpoint evaluator on the
    *same* store: a decided (`isTrue`/`isFalse`) bounded reduction is the same
    decided fixpoint reduction. -/
private theorem reduceBool'_transfer
    (fuel : Nat) (F : @Lambda.Factory CoreLParams) (s : RStore Expression)
    (e : Expression.Expr) :
    (reduceBool' (.runtime (evalBounded fuel)) F s e = .isTrue →
      reduceBool' (.runtime (LExpr.evalFully (TBase := CoreLParams))) F s e = .isTrue) ∧
    (reduceBool' (.runtime (evalBounded fuel)) F s e = .isFalse →
      reduceBool' (.runtime (LExpr.evalFully (TBase := CoreLParams))) F s e = .isFalse) := by
  simp only [reduceBool', ObligationEvaluator.runtime]
  grind [evalBounded_refines_evalFully]

/-- A successful bounded `mapM` evaluation is the same fixpoint `mapM` evaluation. -/
private theorem mapM_evalBounded_transfer
    (fuel : Nat) (F : @Lambda.Factory CoreLParams) (s : RStore Expression) :
    ∀ (es vs : List Expression.Expr), es.mapM (evalBounded fuel F s) = some vs →
      es.mapM (LExpr.evalFully F s) = some vs :=
  fun es => by induction es <;> grind [Option.bind_eq_some_iff, evalBounded_refines_evalFully]

/-- `entryHolds'` transfers `isTrue` from the bounded to the fixpoint evaluator
    on the same store. -/
private theorem entryHolds'_transfer_isTrue
    (fuel : Nat) (F : @Lambda.Factory CoreLParams) (s : RStore Expression)
    (entry : PathConditionEntry Expression)
    (h : entryHolds' (.runtime (evalBounded fuel)) F s entry = .isTrue) :
    entryHolds' (.runtime (LExpr.evalFully (TBase := CoreLParams))) F s entry = .isTrue := by
  cases entry with
  | assumption _ e => exact (reduceBool'_transfer fuel F s e).1 h
  | varDecl => rfl
  | distinct _ es =>
    simp only [entryHolds', ObligationEvaluator.runtime] at h ⊢
    grind [mapM_evalBounded_transfer]

/-! ## `BReduction.and` / fold helpers -/

/-- `a.and b = isTrue` forces both to be `isTrue`. -/
private theorem and_isTrue_split (a b : BReduction) (h : a.and b = .isTrue) :
    a = .isTrue ∧ b = .isTrue := by cases a <;> cases b <;> trivial

/-- A `.and`-fold that ends `isTrue` must have started from an `isTrue` seed. -/
private theorem foldl_and_isTrue_seed {α : Type} (g : α → BReduction) :
    ∀ (xs : List α) (seed : BReduction),
      xs.foldl (fun a x => a.and (g x)) seed = .isTrue → seed = .isTrue :=
  fun xs => by induction xs <;> grind [and_isTrue_split]

/-! ## `.det`-varDecl store threading transfers exactly (bounded ⟹ fixpoint) -/

/-- A successful bounded store-extension transfers to the fixpoint evaluator with
    the **same** resulting store. -/
private theorem extendWithVarDecls'_transfer
    (fuel : Nat) (F : @Lambda.Factory CoreLParams) :
    ∀ (pc : PathCondition Expression) (s s' : RStore Expression),
      extendWithVarDecls' (.runtime (evalBounded fuel)) F s pc = some s' →
      extendWithVarDecls' (.runtime (LExpr.evalFully (TBase := CoreLParams))) F s pc = some s' :=
    fun pc store => by
  fun_induction extendWithVarDecls' (.runtime (evalBounded _)) _ store pc <;>
    simp only [extendWithVarDecls', ObligationEvaluator.runtime] at * <;>
    grind [evalBounded_refines_evalFully]

/-- A successful bounded `foldlM` store-extension over all path conditions
    transfers to the fixpoint evaluator with the same resulting store. -/
private theorem foldlM_extendWithVarDecls'_transfer
    (fuel : Nat) (F : @Lambda.Factory CoreLParams) :
    ∀ (pcs : PathConditions Expression) (s s' : RStore Expression),
      pcs.foldlM (extendWithVarDecls' (.runtime (evalBounded fuel)) F · ·) s =
        some s' →
      pcs.foldlM (extendWithVarDecls' (.runtime (LExpr.evalFully (TBase := CoreLParams))) F · ·) s =
        some s' :=
  fun pcs => by
  induction pcs <;> grind [Option.bind_eq_some_iff, extendWithVarDecls'_transfer]

/-! ## Assumption transfer

The assumptions are conjoined (`BReduction.and`) entry by entry under the threaded
store.  A conjunction that is `.isTrue` has every conjunct `.isTrue`, and each
conjunct transfers from the bounded to the fixpoint evaluator on that store
(`entryHolds'_transfer_isTrue`). -/

/-- A `.and`-fold ending `isTrue` stays `isTrue` when each `isTrue` summand of a member of the
    list is replaced by an `isTrue` one. -/
private theorem foldl_and_mono_mem {α : Type} {g g' : α → BReduction} :
    ∀ (xs : List α) (seed : BReduction), (∀ x ∈ xs, g x = .isTrue → g' x = .isTrue) →
      xs.foldl (fun a x => a.and (g x)) seed = .isTrue →
        xs.foldl (fun a x => a.and (g' x)) seed = .isTrue
  | [], _, _, h => h
  | x :: xs, seed, hg, h => by
    simp only [List.foldl_cons] at h ⊢
    obtain ⟨hs, hx⟩ := and_isTrue_split _ _ (foldl_and_isTrue_seed g xs _ h)
    rw [hs, hx] at h
    rw [hs, hg x (List.mem_cons_self ..) hx]
    exact foldl_and_mono_mem xs _ (fun y hy => hg y (List.mem_cons_of_mem _ hy)) h

/-- **The assumptions transfer `isTrue`** from the bounded to the fixpoint evaluator on
    the same store. -/
private theorem assumptionsHold'_transfer
    (fuel : Nat) (F : @Lambda.Factory CoreLParams) (s : RStore Expression)
    (pcs : PathConditions Expression)
    (h : assumptionsHold' (.runtime (evalBounded fuel)) F s pcs = .isTrue) :
    assumptionsHold' (.runtime (LExpr.evalFully (TBase := CoreLParams))) F s pcs = .isTrue :=
  foldl_and_mono_mem _ _ (fun x _ => entryHolds'_transfer_isTrue _ _ _ x) h

/-! ## The bridge -/

/-- A validity check is `genuine` exactly when the `.det`-varDecl store extension succeeds and,
    on the extended store, the assumptions reduce to `isTrue` and the goal to `isFalse`. -/
private theorem valuationObligationCheck'_genuine_iff {F V : Type _} [DecidableEq V]
    (L : ObligationEvaluator Expression F V) (factory : F) (store : Expression.Ident → Option V)
    (obligation : ProofObligation Expression) :
    valuationObligationCheck' L factory store obligation true = .genuine ↔
      ∃ s, obligation.assumptions.foldlM (extendWithVarDecls' L factory · ·) store = some s ∧
        assumptionsHold' L factory s obligation.assumptions = .isTrue ∧
        reduceBool' L factory s obligation.obligation = .isFalse := by
  simp only [valuationObligationCheck']
  split <;> grind

/-- **The runtime half of the `(c) → (b)` bridge.**  For every obligation, fuel and lifted
    model: if the runtime VC check `runVCCheck` reports the validity query as `genuine`, the
    same check over the fixpoint evaluator `LExpr.evalFully` on the same runtime valuation
    (`modelValuation`) reports it `genuine` too. -/
theorem runVCCheck_genuine_fixpoint
    (F : @Lambda.Factory CoreLParams) (fuel : Nat)
    (liftedModel : List (Expression.Ident × Lambda.LExpr CoreLParams.mono × Bool))
    (obligation : ProofObligation Expression)
    (h : runVCCheck F fuel liftedModel obligation true =
      Imperative.CEValidationVerdict.genuine) :
    valuationObligationCheck' (.runtime (LExpr.evalFully (TBase := CoreLParams))) F
      (modelValuation (valuationDefaults F obligation) liftedModel) obligation true =
      .genuine := by
  obtain ⟨s, hs, hA, hQ⟩ := (valuationObligationCheck'_genuine_iff ..).1 h
  exact (valuationObligationCheck'_genuine_iff ..).2
    ⟨s, foldlM_extendWithVarDecls'_transfer _ _ _ _ _ hs,
    assumptionsHold'_transfer _ _ _ _ hA, (reduceBool'_transfer _ _ _ _).2 hQ⟩

/-! ## From the runtime check to the specification check

Under a factory `M` on which the bounded evaluator is sound (`BoundedEvalSoundAt`), every
runtime step of the check is matched by a specification step on a semantic store the runtime
store denotes. -/

section Spec

variable {M : Expression.Factory} {F : @Lambda.Factory CoreLParams} {fuel : Nat}

/-- A literal denotes the value of its constant. -/
private theorem denotes_const {c : Lambda.LConst} {v : Expression.Val}
    (h : InterpLang.Denotes M (.const default c) v) :
    v = Lambda.SemValue.ofConst M.model.tcInterp c :=
  Option.some.inj ((denotes_iff.1 h).2.2.symm.trans
    (Lambda.LExpr.denoteEval_const (Lambda.LExpr.denoteEval_const_wt (denotes_iff.1 h).2.2)))

/-- Two primitive literals with the same value are the same literal. -/
private theorem ofConst_injective {tc : Lambda.TyConstrInterp} {c₁ c₂ : Lambda.LConst}
    (hp₁ : c₁.isPrimitive = true) (hp₂ : c₂.isPrimitive = true)
    (h : Lambda.SemValue.ofConst tc c₁ = Lambda.SemValue.ofConst tc c₂) : c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> try cases hp₁ <;> try cases hp₂
  all_goals simp only [Lambda.SemValue.ofConst, Lambda.LConst.ty,
    Lambda.LMonoTy.substTyVars, Lambda.LMonoTy.substTyVars.map] at h <;>
    first
    | (cases h; rfl)
    | (injection h with _ _ h; simp only [Lambda.denoteConst] at h
       exact congrArg _ (Strata.Util.Real.ofRat_inj.mp h))
    | (have hs := congrArg Lambda.SemValue.sort h; simp at hs)

/-- A value the bounded evaluator commits on a runtime store denoting `σ` denotes the value of
    the specification evaluator on `σ`. -/
private theorem ev_spec (hM : InterpLang.rfactory M = F)
    (hEval : BoundedEvalSoundAt Expression M) {s : RStore Expression}
    {σ : SemanticStore Expression} (hs : StoreDenotes M s σ) {e r : Expression.Expr}
    (h : evalBounded fuel F s e = some r) :
    ∃ v, Expression.eval M σ e = some v ∧ InterpLang.Denotes M r v :=
  hEval fuel s σ e r hs (hM ▸ h)

open Classical in
/-- A decided runtime Boolean reduction is the same specification reduction on a semantic
    store the runtime store denotes. -/
private theorem reduceBool'_spec (hM : InterpLang.rfactory M = F)
    (hEval : BoundedEvalSoundAt Expression M) {s : RStore Expression}
    {σ : SemanticStore Expression} (hs : StoreDenotes M s σ) (e : Expression.Expr) :
    (reduceBool' (bcRuntime fuel) F s e = .isTrue →
      reduceBool' ObligationEvaluator.spec M σ e = .isTrue) ∧
    (reduceBool' (bcRuntime fuel) F s e = .isFalse →
      reduceBool' ObligationEvaluator.spec M σ e = .isFalse) := by
  simp only [reduceBool', ObligationEvaluator.runtime, ObligationEvaluator.spec]
  cases h : evalBounded fuel F s e with
  | none => simp
  | some r =>
    obtain ⟨v, hv, hd⟩ := ev_spec hM hEval hs h
    have htt := InterpLangBool.denote_of_eqModuloMeta_tt M r v (P := Expression)
    have hff := InterpLangBool.denote_of_eqModuloMeta_ff M r v (P := Expression)
    have hne := HasBool.ttVal_ne_ffVal (P := Expression) M
    grind

/-- Binding a name to a runtime value and to a value it denotes keeps the store relation. -/
private theorem storeDenotes_update {s : RStore Expression} {σ : SemanticStore Expression}
    (hs : StoreDenotes M s σ) (x : Expression.Ident) {r : Expression.Expr} {v : Expression.Val}
    (hd : InterpLang.Denotes M r v) :
    StoreDenotes M (fun y => if y = x then some r else s y)
      (fun y => if y = x then some v else σ y) := by
  refine ⟨fun y => ?_, fun y r' v' h1 h2 => ?_⟩
  · by_cases hy : y = x <;> simp [hy, hs.1 y]
  · by_cases hy : y = x
    · simp only [hy, ↓reduceIte, Option.some.injEq] at h1 h2
      exact h1 ▸ h2 ▸ hd
    · simp only [hy, ↓reduceIte] at h1 h2
      exact hs.2 y r' v' h1 h2

open Classical in
/-- A successful runtime store extension is matched by a specification extension of a
    semantic store the runtime store denotes, to a store the extended runtime store denotes. -/
private theorem extendWithVarDecls'_spec (hM : InterpLang.rfactory M = F)
    (hEval : BoundedEvalSoundAt Expression M) :
    ∀ (pc : PathCondition Expression) (s s' : RStore Expression) (σ : SemanticStore Expression),
      StoreDenotes M s σ → extendWithVarDecls' (bcRuntime fuel) F s pc = some s' →
      ∃ σ', extendWithVarDecls' ObligationEvaluator.spec M σ pc = some σ' ∧
        StoreDenotes M s' σ' := by
  intro pc
  induction pc with
  | nil => exact fun s s' σ hs h => ⟨σ, rfl, Option.some.inj h ▸ hs⟩
  | cons entry rest ih =>
    intro s s' σ hs h
    rcases entry with _ | ⟨x, ty, _ | e⟩ | _
    all_goals simp only [extendWithVarDecls'] at h ⊢
    case varDecl.det =>
      simp only [ObligationEvaluator.runtime] at h
      split at h <;> (try split at h) <;> try cases h
      rename_i r hr hok
      obtain ⟨v, hv, hd⟩ := ev_spec hM hEval hs hr
      have hty : HasVal.valueOfTy M v ty := by
        subst hM
        exact valueOfTy_of_ops hd (Bool.and_eq_true _ _ ▸ hok).2
      have hv' : LExpr.denoteEval M σ _ = some v := hv
      simp only [ObligationEvaluator.spec, hv', hty, decide_true, ↓reduceIte]
      exact ih _ _ _ (storeDenotes_update hs x hd) h
    all_goals exact ih _ _ _ hs h

/-- A runtime evaluation of a list to literals is matched by a specification evaluation to
    their values. -/
private theorem mapM_spec_consts (hM : InterpLang.rfactory M = F)
    (hEval : BoundedEvalSoundAt Expression M) {s : RStore Expression}
    {σ : SemanticStore Expression} (hs : StoreDenotes M s σ) :
    ∀ (es : List Expression.Expr) (cs : List Lambda.LConst),
      es.mapM (evalBounded fuel F s) = some (cs.map (.const default)) →
      es.mapM (Expression.eval M σ) = some (cs.map (Lambda.SemValue.ofConst M.model.tcInterp))
  | [], cs, h => by cases cs <;> simp_all
  | e :: es, cs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨r, hr, rs, hrs, hcs⟩ := h
    cases cs with
    | nil => simp at hcs
    | cons c cs =>
      simp only [List.map_cons, List.cons.injEq] at hcs
      obtain ⟨rfl, rfl⟩ := hcs
      obtain ⟨v, hv, hd⟩ := ev_spec hM hEval hs hr
      rw [List.mapM_cons, hv, mapM_spec_consts hM hEval hs es cs hrs, denotes_const hd]
      rfl

/-- A list of runtime values that are all primitive literals is the list of their literals. -/
private theorem exists_consts : ∀ (rs : List Expression.Expr),
    (∀ r ∈ rs, ∃ c, c.isPrimitive = true ∧ r = .const default c) →
      ∃ cs : List Lambda.LConst, (∀ c ∈ cs, c.isPrimitive = true) ∧ rs = cs.map (.const default)
  | [], _ => ⟨[], by simp, rfl⟩
  | r :: rs, h => by
    obtain ⟨c, hc, rfl⟩ := h r (List.mem_cons_self ..)
    obtain ⟨cs, hcs, rfl⟩ := exists_consts rs fun r hr => h r (List.mem_cons_of_mem _ hr)
    exact ⟨c :: cs, by simp_all, rfl⟩

open Classical in
/-- A runtime path-condition entry that holds is a specification entry that holds, on a
    semantic store the runtime store denotes, when the entry's `.distinct` values are
    primitive literals. -/
private theorem entryHolds'_spec (hM : InterpLang.rfactory M = F)
    (hEval : BoundedEvalSoundAt Expression M) {s : RStore Expression}
    {σ : SemanticStore Expression} (hs : StoreDenotes M s σ)
    (entry : PathConditionEntry Expression)
    (hlit : ∀ l es, entry = .distinct l es →
      ∀ rs, es.mapM (evalBounded fuel F s) = some rs → ∀ r ∈ rs,
        ∃ c, c.isPrimitive = true ∧ r = .const default c)
    (h : entryHolds' (bcRuntime fuel) F s entry = .isTrue) :
    entryHolds' ObligationEvaluator.spec M σ entry = .isTrue := by
  cases entry with
  | assumption _ e => exact (reduceBool'_spec hM hEval hs e).1 h
  | varDecl => rfl
  | distinct l es =>
    simp only [entryHolds', ObligationEvaluator.runtime] at h
    split at h <;> (try split at h) <;> try cases h
    rename_i rs hrs hnd
    obtain ⟨cs, hp, rfl⟩ := exists_consts rs (hlit l es rfl rs hrs)
    simp only [entryHolds']
    erw [mapM_spec_consts hM hEval hs es cs hrs]
    have hvs : (cs.map (Lambda.SemValue.ofConst M.model.tcInterp)).Nodup :=
      List.pairwise_map.2 ((List.pairwise_map.1 hnd).imp_of_mem fun h₁ h₂ hne heq =>
        hne (congrArg _ (ofConst_injective (hp _ h₁) (hp _ h₂) heq)))
    simp only [hvs, ↓reduceIte]

/-- A successful runtime extension over all path conditions is matched by a specification
    extension of a semantic store the runtime store denotes. -/
private theorem foldlM_extendWithVarDecls'_spec (hM : InterpLang.rfactory M = F)
    (hEval : BoundedEvalSoundAt Expression M) :
    ∀ (pcs : PathConditions Expression) (s s' : RStore Expression) (σ : SemanticStore Expression),
      StoreDenotes M s σ →
      pcs.foldlM (extendWithVarDecls' (bcRuntime fuel) F · ·) s = some s' →
      ∃ σ', pcs.foldlM (extendWithVarDecls' ObligationEvaluator.spec M · ·) σ = some σ' ∧
        StoreDenotes M s' σ'
  | [], s, s', σ, hs, h => ⟨σ, rfl, Option.some.inj h ▸ hs⟩
  | pc :: pcs, s, s', σ, hs, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨s1, h1, h2⟩ := h
    obtain ⟨σ1, hσ1, hs1⟩ := extendWithVarDecls'_spec hM hEval pc s s1 σ hs h1
    obtain ⟨σ', hσ', hs'⟩ := foldlM_extendWithVarDecls'_spec hM hEval pcs s1 s' σ1 hs1 h2
    exact ⟨σ', ⟨σ1, hσ1, hσ'⟩, hs'⟩

end Spec

open Classical in
/-- **The `(c) → (b)` soundness bridge.**  For every obligation, fuel and lifted model, and
    every factory `M` whose runtime factory is `F` and on which the bounded evaluator is sound
    (`BoundedEvalSoundAt`): if the runtime VC check `runVCCheck` reports the validity query as
    `genuine`, and the values it computes for the `.distinct` entries are primitive
    literals (`DistinctLiteralsAt`, on the store it threads), every semantic valuation `σ` that the
    runtime valuation built from the model (`modelValuation`) denotes (`StoreDenotes`) is a
    level-`(b)` counterexample (`IsValuationObligationCex`): under the specification evaluator, the
    obligation's assumptions reduce to true and its goal to false. -/
theorem runVCCheck_genuine_isValuationObligationCex
    (M : Expression.Factory) (F : @Lambda.Factory CoreLParams) (hM : InterpLang.rfactory M = F)
    (hEval : BoundedEvalSoundAt Expression M)
    (fuel : Nat)
    (liftedModel : List (Expression.Ident × Lambda.LExpr CoreLParams.mono × Bool))
    (obligation : ProofObligation Expression) (σ : SemanticStore Expression)
    (hσ : StoreDenotes M (modelValuation (valuationDefaults F obligation) liftedModel) σ)
    (hdist : ∀ s, obligation.assumptions.foldlM (extendWithVarDecls' (bcRuntime fuel) F · ·)
        (modelValuation (valuationDefaults F obligation) liftedModel) = some s →
      DistinctLiteralsAt F fuel s obligation)
    (h : runVCCheck F fuel liftedModel obligation true =
      Imperative.CEValidationVerdict.genuine) :
    Imperative.IsValuationObligationCex (P := Expression) M σ obligation := by
  obtain ⟨s, hs, hA, hQ⟩ := (valuationObligationCheck'_genuine_iff ..).1 h
  obtain ⟨σ', hσ', hs'⟩ := foldlM_extendWithVarDecls'_spec hM hEval _ _ _ _ hσ hs
  exact (valuationObligationCheck'_genuine_iff ..).2 ⟨σ', hσ', foldl_and_mono_mem _ _
    (fun x hx => entryHolds'_spec hM hEval hs' x fun l es hl => hdist s hs l es (hl ▸ hx)) hA,
    (reduceBool'_spec hM hEval hs' _).2 hQ⟩

/-- `runVCCheck_genuine_isValuationObligationCex` for a factory `M` whose functions meet
    `EvalFactoryWF` (which `evalFactoryWF_of_userFuncs` gives program factories), in place of the
    soundness of the bounded evaluator at `M` (`BoundedEvalSoundAt`), which `EvalFactoryWF` implies:
    a `genuine` verdict makes every valuation the model's runtime valuation denotes a level-`(b)`
    counterexample. -/
theorem runVCCheck_genuine_isValuationObligationCex_of_evalFactoryWF
    (M : Expression.Factory)
    (F : @Lambda.Factory CoreLParams)
    (hM : InterpLang.rfactory M = F)
    (hEvalF : EvalFactoryWF M.factory)
    (fuel : Nat)
    (liftedModel : List (Expression.Ident × Lambda.LExpr CoreLParams.mono × Bool))
    (obligation : ProofObligation Expression)
    (σ : SemanticStore Expression)
    (hσ : StoreDenotes M (modelValuation (valuationDefaults F obligation) liftedModel) σ)
    (hdist : ∀ s, obligation.assumptions.foldlM (extendWithVarDecls' (bcRuntime fuel) F · ·)
        (modelValuation (valuationDefaults F obligation) liftedModel) = some s →
      DistinctLiteralsAt F fuel s obligation)
    (h : runVCCheck F fuel liftedModel obligation true =
      Imperative.CEValidationVerdict.genuine) :
    Imperative.IsValuationObligationCex (P := Expression) M σ obligation :=
  runVCCheck_genuine_isValuationObligationCex M F hM (boundedEvalSoundAt_of_evalFactoryWF M hEvalF)
    fuel liftedModel obligation σ hσ hdist h

/-! ## Interpreted constants -/

/-- `interpretConst` keeps the function's name. -/
private theorem interpretConst_name (I : ConstInterp) (f : LFunc CoreLParams) :
    (interpretConst I f).name = f.name := by
  unfold interpretConst
  split <;> (try split) <;> rfl

/-- `withConsts F I` holds, under each name, `F`'s function with `interpretConst I`
    applied, and nothing under a name `F` does not hold. -/
theorem withConsts_getElem? (F : @Lambda.Factory CoreLParams) (I : ConstInterp) (n : String) :
    (withConsts F I)[n]? = (F[n]?).map (interpretConst I) := by
  unfold withConsts
  split
  · rename_i hI
    cases h : F[n]? <;> simp [interpretConst, List.isEmpty_iff.mp hI]
  · have hnodup : ((F.toArray.map (interpretConst I)).toList.map (·.name.name)).Nodup := by
      simpa [Function.comp_def, interpretConst_name] using Factory.name_nodup F
    cases h : F[n]? with
    | some f =>
      have hm := Array.mem_map_of_mem (f := interpretConst I)
        (Factory.getElem?_is_some_implies_mem h)
      have hget := Factory.get?_ofArray_of_mem hm hnodup
      simpa [interpretConst_name, Factory.getElem?_name h] using hget
    | none =>
      cases h' : (Factory.ofArray (F.toArray.map (interpretConst I)))[n]? with
      | none => rfl
      | some g =>
        obtain ⟨f, hf, rfl⟩ := Array.mem_map.mp
          (Factory.ofArray_mem (Factory.getElem?_is_some_implies_mem h'))
        have hn := interpretConst_name I f ▸ Factory.getElem?_name h'
        obtain ⟨hs, -⟩ := Factory.mem_name_eq_getElem hf hn
        simp [Factory.getElem?_of_mem hs] at h

/-- An interpretation of the operators consistent with `withConsts F I` (every bodied
    function and every concrete evaluator agrees with it) is consistent with `F`. -/
theorem withConsts_interpConsistent {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    (F : @Lambda.Factory CoreLParams) (I : ConstInterp)
    (h : Factory.InterpConsistent tcInterp opInterp (withConsts F I)) :
    Factory.InterpConsistent tcInterp opInterp F := by
  have hget (f : String) (hf : f ∈ F) (hc : isUninterpretedConst (F[f]) = false) :
      ∃ hf' : f ∈ withConsts F I, (withConsts F I)[f]'hf' = F[f] := by
    have he : (withConsts F I)[f]? = some (F[f]) := by
      simp only [withConsts_getElem?, Factory.getElem?_of_mem hf, Option.map_some, interpretConst]
      split <;> simp [hc]
    exact ⟨Factory.getElem?_some_implies_mem he, Factory.getElem?_some_getElem he⟩
  unfold Factory.InterpConsistent at h ⊢
  refine ⟨fun f hf body hb => ?_, fun f hf ceval hc => ?_⟩
  · obtain ⟨hf', he⟩ := hget f hf (by simp [isUninterpretedConst, hb])
    exact he ▸ h.1 f hf' body (he ▸ hb)
  · obtain ⟨hf', he⟩ := hget f hf (by simp [isUninterpretedConst, hc])
    exact he ▸ h.2 f hf' ceval (he ▸ hc)

/-- **The `(c) → (b)` bridge with interpreted constants.** A `genuine` validity verdict of
    the VC check under `withConsts F I` (the factory `F` with each constant of `I` fixed
    to its model value), whose `.distinct` values are primitive literals
    (`DistinctLiteralsAt`), makes the valuation of the lifted solver model a counterexample to
    the obligation (assumptions true, goal false) with the constants of `I` interpreted, under
    every factory whose runtime factory is `withConsts F I` on which the bounded evaluator is
    sound (`BoundedEvalSoundAt`). -/
theorem runVCCheck_genuine_isValuationObligationCexWith (F : @Lambda.Factory CoreLParams)
    (I : ConstInterp) (fuel : Nat)
    (liftedModel : List (Expression.Ident × Lambda.LExpr CoreLParams.mono × Bool))
    (obligation : ProofObligation Expression)
    (hEval : ∀ M : Expression.Factory, InterpLang.rfactory M = withConsts F I →
      BoundedEvalSoundAt Expression M)
    (hdist : ∀ s, obligation.assumptions.foldlM
        (extendWithVarDecls' (bcRuntime fuel) (withConsts F I) · ·)
        (modelValuation (valuationDefaults (withConsts F I) obligation) liftedModel) = some s →
      DistinctLiteralsAt (withConsts F I) fuel s obligation)
    (h : runVCCheck (withConsts F I) fuel liftedModel obligation true =
      Imperative.CEValidationVerdict.genuine) :
    IsValuationObligationCexWith F I
      (modelValuation (valuationDefaults (withConsts F I) obligation) liftedModel)
      obligation :=
  fun M hM σ hσ =>
    runVCCheck_genuine_isValuationObligationCex M _ hM (hEval M hM) _ _ _ σ hσ hdist h

/-- **The `(c) → (b)` bridge with interpreted constants, at factories meeting
    `EvalFactoryWF`.** A `genuine` validity verdict of the VC check under `withConsts F I` (the
    factory `F` with each constant of `I` fixed to its model value), whose `.distinct` values are
    primitive literals (`DistinctLiteralsAt`), makes the valuation of the lifted solver model a
    counterexample to the obligation (assumptions true, goal false) with the constants of `I`
    interpreted, when the functions of `withConsts F I` meet the conditions under which the
    bounded evaluator is sound (`EvalFactoryWF`, which `evalFactoryWF_of_userFuncs` gives program
    factories, the interpreted constants being user functions with literal bodies). -/
theorem runVCCheck_genuine_isValuationObligationCexWith_of_evalFactoryWF
    (F : @Lambda.Factory CoreLParams)
    (I : ConstInterp) (fuel : Nat)
    (liftedModel : List (Expression.Ident × Lambda.LExpr CoreLParams.mono × Bool))
    (obligation : ProofObligation Expression)
    (hEvalF : EvalFactoryWF (withConsts F I))
    (hdist : ∀ s, obligation.assumptions.foldlM
        (extendWithVarDecls' (bcRuntime fuel) (withConsts F I) · ·)
        (modelValuation (valuationDefaults (withConsts F I) obligation) liftedModel) = some s →
      DistinctLiteralsAt (withConsts F I) fuel s obligation)
    (h : runVCCheck (withConsts F I) fuel liftedModel obligation true =
      Imperative.CEValidationVerdict.genuine) :
    IsValuationObligationCexWith F I
      (modelValuation (valuationDefaults (withConsts F I) obligation) liftedModel)
      obligation :=
  runVCCheck_genuine_isValuationObligationCexWith F I fuel liftedModel obligation
    (fun M hM => boundedEvalSoundAt_of_evalFactoryWF M
      (by rw [show M.factory = _ from hM]; exact hEvalF)) hdist h

end -- public section

end Core
