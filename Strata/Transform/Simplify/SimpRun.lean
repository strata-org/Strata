/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.StmtSim
public import Strata.Transform.Simplify.Precondition
import all Strata.Transform.Simplify.StmtSim
import all Strata.Transform.Simplify.Precondition
import all Strata.Transform.Simplify.ExprCorrect
import all Strata.Transform.Simplify.Expr
import all Strata.Transform.Simplify.FoldFactory
import all Strata.DL.Lambda.Denote.ReachesModMeta
import all Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.Languages.Core.InstExprTyping
import Strata.DL.Lambda.OperationalSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.DL.Imperative.BigStep.SemProps

/-! # The simplification pass against a run of the body

The expressions of a body that satisfies the precondition (`ExprOK`) are, in a store that
gives the variables of the body their types (`TypedOn`), well-formed against the store
(`exprGood_of_ok`) and, when their variables are bound, evaluate (`eval_of_ok`). These are
the facts the simulation of each command of the body reads.

Key results: one command of the body is matched by its simplification (`simp_cmd`), and a
run of a list of the body, or a run stopped after a command, is matched by a run of its
simplification from the same store, to the same outcome, with related events (`simp_run`,
`simp_reach`).
-/

namespace Core.Simplify

open Lambda Imperative

/-- The store gives each variable among `T` that it binds a value of the type `Γ` gives it. -/
def TypedOn (M : Expression.Factory) (Γ : VarTyping Expression) (T : List CoreIdent)
    (σ : SemanticStore Expression) : Prop :=
  ∀ y ∈ T, ∀ ty v, Γ y = some ty → σ y = some v → HasVal.valueOfTy M v ty

/-- The entry condition `StoreTypedBy` is `TypedOn` on the body's entry variables, with every
    bound entry variable typed by `Γ`. -/
theorem storeTypedBy_iff {M : Expression.Factory} {Γ : VarTyping Expression}
    {ss : List Statement} {σ : SemanticStore Expression} :
    StoreTypedBy M Γ ss σ ↔ TypedOn M Γ (Block.entryVars ss) σ ∧
      ∀ x ∈ Block.entryVars ss, (σ x).isSome → (Γ x).isSome := by
  constructor
  · intro h
    refine ⟨fun y hy ty v ht hv => ?_, fun x hx hs => ?_⟩
    · obtain ⟨ty', ht', hval⟩ := h y hy v hv
      rw [ht] at ht'; cases ht'; exact hval
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨ty, ht, -⟩ := h x hx v hv
      simp [ht]
  · rintro ⟨hT, hb⟩ x hx v hv
    obtain ⟨ty, ht⟩ := Option.isSome_iff_exists.mp (hb x hx (by simp [hv]))
    exact ⟨ty, ht, hT x hx ty v ht hv⟩

/-- An expression of the body whose variables are among `T` and bound is well-formed against
    a store typed by `Γ` on `T`. -/
private theorem exprGood_of_ok {F : Lambda.Factory CoreLParams} {c : List String}
    {M : Expression.Factory} {Γ : VarTyping Expression} {T : List CoreIdent}
    {σ : SemanticStore Expression} {e : Expression.Expr} {ty : Expression.Ty}
    (hok : ExprOK F Γ e ty) (hty : TypedOn M Γ T σ)
    (hT : e.NamesIn (fun y : CoreIdent => y ∈ T)) (hd : ValStore.Defines σ M.model.tcInterp e) :
    ExprGood (withoutInline c F) M σ (fun y : CoreIdent => y ∈ T) e := by
  obtain ⟨⟨τ, -, -, hdef, -⟩, hops, hann⟩ := hok
  refine ⟨(opsConsistent_withoutInline c F e).mpr hops, fun y a hy => ?_, hT⟩
  have hyv : y ∈ LExpr.LExpr.getVars e := by
    rw [getVars_eq_freeVars_idents]; exact List.mem_map.mpr ⟨_, hy, rfl⟩
  obtain ⟨v, hv, -⟩ := hd y hyv
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hdef y hyv)
  obtain ⟨-, hm⟩ := hty y (hT y a hy) t v ht hv
  refine ⟨v, hv, ?_⟩
  rcases LExpr.annotateFvars_eq_self_freeVars hann y a hy with h | h <;>
    simp only [ht, Option.bind_some, hm] at h
  · cases h
  · exact h.symm

/-- An expression of the body whose variables are bound evaluates in a store typed by `Γ`. -/
private theorem eval_of_ok {F : Lambda.Factory CoreLParams} {c : List String}
    {M : Expression.Factory} {Γ : VarTyping Expression} {T : List CoreIdent}
    {σ : SemanticStore Expression} {e : Expression.Expr} {ty : Expression.Ty}
    (hok : ExprOK F Γ e ty) (hty : TypedOn M Γ T σ)
    (hT : e.NamesIn (fun y : CoreIdent => y ∈ T)) (hd : ValStore.Defines σ M.model.tcInterp e) :
    ∃ v, e.denoteEval M σ = some v ∧ HasVal.valueOfTy M v ty := by
  have hg := exprGood_of_ok (c := c) hok hty hT hd
  obtain ⟨⟨τ, hτ, hgr, -, hT'⟩, -, hann⟩ := hok
  rw [hann, ← hg.ann.annotate_eq] at hT'
  refine ⟨_, LExpr.denoteEval_of_hasTypeA hd hT' hgr, rfl, ?_⟩
  show ty.toMonoType? = some (τ.substTyVars M.tyVarVal).toMonoTy
  rw [hgr.substTyVars_eq M.tyVarVal Lambda.refTyVarVal, hgr, hτ]


/-! ## The setting of a run -/

/-- The context fields the traversal never changes. -/
def Ctx.Fixed (ctx base : Ctx) : Prop :=
  ctx.factory = base.factory ∧ ctx.foldFactory = base.foldFactory ∧ ctx.carriers = base.carriers

/-- A context keeps its own fixed fields. -/
theorem Ctx.Fixed.refl (base : Ctx) : base.Fixed base := ⟨rfl, rfl, rfl⟩

/-- Replacing the recorded values keeps the fixed fields. -/
private theorem Ctx.Fixed.values {base ctx : Ctx} (h : ctx.Fixed base)
    (vs : Map CoreIdent Expression.Expr) :
    ({ ctx with values := vs } : Ctx).Fixed base := h

/-- Forgetting values keeps the fixed fields. -/
private theorem Ctx.Fixed.invalidate {base ctx : Ctx} (h : ctx.Fixed base)
    (names : Std.HashSet String) :
    (ctx.invalidate names).Fixed base := by
  unfold Ctx.invalidate Ctx.invalidateBy; split <;> (try split) <;> (try split) <;> exact h

/-- Forgetting one variable's values keeps the fixed fields. -/
private theorem Ctx.Fixed.invalidateVar {base ctx : Ctx} (h : ctx.Fixed base) (x : CoreIdent) :
    (ctx.invalidateVar x).Fixed base := h

/-- Recording a value keeps the fixed fields. -/
private theorem Ctx.Fixed.record {base ctx : Ctx} (h : ctx.Fixed base) (x : CoreIdent)
    (e : Expression.Expr) : (ctx.record x e).Fixed base := by
  unfold Ctx.record; split <;> exact h

/-- Joining the contexts of a branch keeps the fixed fields. -/
private theorem Ctx.Fixed.join {base ctx : Ctx} (h : ctx.Fixed base) (live : List Ctx)
    (a d : Std.HashSet String) : (ctx.join live a d).Fixed base := by
  unfold Ctx.join; split
  · exact h
  · suffices ∀ (c : Ctx) agreed, c.Fixed base → (recordAgreed c agreed).Fixed base from
      this _ _ (h.invalidate a)
    intro c agreed hc
    induction agreed generalizing c with
    | nil => exact hc
    | cons p rest ih => exact ih _ hc

/-- What a run of a body assumes of the base context and the model: the fold factory is the
    model's factory with `inline` weakened and satisfies the assumptions of the denotational
    semantics under every typing. -/
structure Setup (base : Ctx) (M : Expression.Factory) : Prop where
  fold : base.foldFactory = withoutInline base.carriers base.factory
  model : M.factory = base.factory
  wf : ∃ tf, Factory.WF base.foldFactory tf
  step : ∀ tyMap : Map CoreIdent LMonoTy, Factory.StepWFOn base.foldFactory tyMap

/-- What holds at every point of a run: the context records sound values over names among
    `T`, the store gives the names among `T` their `Γ` types, holds values of the model, and
    binds every name among `T` that `Γ` types. -/
structure Inv (base : Ctx) (M : Expression.Factory) (T : List CoreIdent)
    (Γ : VarTyping Expression) (ctx : Ctx) (σ : SemanticStore Expression) : Prop where
  fixed : ctx.Fixed base
  vs : ValuesSound ctx M σ
  names : ∀ x r, (x, r) ∈ ctx.values.toList → x ∈ T ∧ r.NamesIn (fun y : CoreIdent => y ∈ T)
  typed : TypedOn M Γ T σ
  wf : WellFormedStore σ M
  /-- Every name among `T` the typing types is bound. -/
  bound : ∀ y ∈ T, (Γ y).isSome → (σ y).isSome

/-- **Simplifying an expression of the body at a point of a run.** An expression the
    precondition types, whose variables are among `T` and bound, simplifies to one that is
    well-formed against the store and evaluates to the same value. -/
private theorem simp_expr {base ctx : Ctx} {M : Expression.Factory} {T : List CoreIdent}
    {Γ : VarTyping Expression}
    {σ : SemanticStore Expression} (S : Setup base M) (I : Inv base M T Γ ctx σ)
    {e : Expression.Expr} {ty : Expression.Ty} (hok : ExprOK base.factory Γ e ty)
    (hT : e.NamesIn (fun y : CoreIdent => y ∈ T)) (hd : ValStore.Defines σ M.model.tcInterp e) :
    ExprGood ctx.foldFactory M σ (fun y : CoreIdent => y ∈ T) (simplifyExpr ctx e) ∧
      ∀ v, e.denoteEval M σ = some v → (simplifyExpr ctx e).denoteEval M σ = some v := by
  have hfa : ctx.factory = base.factory := I.fixed.1
  have hfo : ctx.foldFactory = base.foldFactory := I.fixed.2.1
  have hca : ctx.carriers = base.carriers := I.fixed.2.2
  obtain ⟨tf, hwf⟩ := S.wf
  have hok' : ctx.FactoriesOK := ⟨by rw [hfo, hfa, hca, S.fold], hfo ▸ hwf.factoryWF⟩
  have hfold : ctx.foldFactory = withoutInline base.carriers M.factory := by
    rw [hfo, S.fold, S.model]
  have hg := exprGood_of_ok (c := base.carriers) hok I.typed hT hd
  rw [← S.fold, ← hfo] at hg
  refine simplifyExpr_eval (tf := tf) hok' I.vs (fun y v hv => I.wf y v hv)
    (fun x r hx => I.names x r (Map.find?_mem _ _ _ hx)) (hfo ▸ hwf)
    (fun _ _ => hfo ▸ S.step _)
    (hfold ▸ (Interp.withoutInline base.carriers M.model).interpConsistent)
    (hfold ▸ (Interp.withoutInline base.carriers M.model).constrConsistent) hg


/-! ## Commands -/

/-- An expression whose free variables the store binds, in a store of model values. -/
private theorem defines_of_bound {M : Expression.Factory} {σ : SemanticStore Expression}
    (hwf : WellFormedStore σ M) {e : Expression.Expr}
    (h : ∀ i ∈ HasFvars.getFvars (P := Expression) e, (σ i).isSome) :
    ValStore.Defines σ M.model.tcInterp e := by
  intro x hx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h x hx)
  exact ⟨v, hv, hwf x v hv⟩

/-- An expression whose free variables are among `T` has its names among `T`. -/
private theorem namesIn_of_getFvars {T : List CoreIdent} {e : Expression.Expr}
    (h : ∀ y ∈ HasFvars.getFvars (P := Expression) e, y ∈ T) :
    e.NamesIn (fun y : CoreIdent => y ∈ T) :=
  fun y _ hy => h y (mem_getFvars_of_freeVars hy)

/-- Forgetting `x` keeps the values sound in a store that changed only at `x`. -/
private theorem ValuesSound.invalidateVar {ctx : Ctx} {M : ModeledFactory CoreLParams}
    {σ σ' : ValStore CoreLParams} (h : ValuesSound ctx M σ) {x : CoreIdent}
    (hσ : ∀ y : CoreIdent, y ≠ x → σ' y = σ y) : ValuesSound (ctx.invalidateVar x) M σ' := by
  intro y r hm
  obtain ⟨hm, hyx, hfv⟩ := mem_invalidateVar hm
  exact (h y r hm).transfer (hσ y fun h => hyx (h ▸ rfl))
    (fun z ty hz => hσ z fun h => hfv z (mem_getFvars_of_freeVars hz) (h ▸ rfl))

/-- The store part of the invariant after an `init`. -/
private theorem store_init {M : Expression.Factory} {T : List CoreIdent}
    {Γ : VarTyping Expression}
    {σ σ1 : SemanticStore Expression} {x : CoreIdent} {ty : Expression.Ty} {v : SemValue}
    (hty : TypedOn M Γ T σ)
    (hwf : WellFormedStore σ M) (h1 : σ1 x = some v) (hfr : ∀ y, x ≠ y → σ1 y = σ y)
    (hv : HasVal.valueOfTy M v ty)
    (hb : ∀ y ∈ T, (Γ y).isSome → (σ y).isSome) :
    TypedOn M (Γ.extend [(x, ty)]) T σ1 ∧ WellFormedStore σ1 M ∧
      (∀ y ∈ T, (Γ.extend [(x, ty)] y).isSome → (σ1 y).isSome) := by
  rw [VarTyping.extend_singleton]
  refine ⟨fun y hy t w ht hw => ?_, fun y w hw => ?_, fun y hy ht => ?_⟩ <;>
    by_cases hxy : x = y
  · subst hxy; simp only [ite_true, Option.some.injEq] at ht; subst ht
    rw [h1] at hw; cases hw; exact hv
  · simp only [Ne.symm hxy, ite_false] at ht
    rw [hfr y hxy] at hw; exact hty y hy t w ht hw
  · subst hxy; rw [h1] at hw; cases hw; exact hv.1
  · rw [hfr y hxy] at hw; exact hwf y w hw
  · subst hxy; simp [h1]
  · simp only [Ne.symm hxy, ite_false] at ht
    rw [hfr y hxy]; exact hb y hy ht

/-- The store part of the invariant after a `set`. -/
private theorem store_set {M : Expression.Factory} {T : List CoreIdent}
    {Γ : VarTyping Expression}
    {σ σ1 : SemanticStore Expression} {x : CoreIdent} {v : SemValue}
    (hty : TypedOn M Γ T σ)
    (hwf : WellFormedStore σ M) (h1 : σ1 x = some v) (hfr : ∀ y, x ≠ y → σ1 y = σ y)
    (hst : HasVal.valueOfStoredTy (P := Expression) M σ x v)
    (hb : ∀ y ∈ T, (Γ y).isSome → (σ y).isSome) :
    TypedOn M Γ T σ1 ∧ WellFormedStore σ1 M ∧ (∀ y ∈ T, (Γ y).isSome → (σ1 y).isSome) := by
  obtain ⟨p, t0, hp, hpt, hvt⟩ := hst
  have hs := sort_eq_of_valueOfTy hvt hpt
  refine ⟨fun y hy t w ht hw => ?_, fun y w hw => ?_, fun y hy ht => ?_⟩ <;>
    by_cases hxy : x = y
  · subst hxy; rw [h1] at hw; cases hw
    exact ⟨hvt.1, by rw [hs]; exact (hty x hy t p ht hp).2⟩
  · rw [hfr y hxy] at hw; exact hty y hy t w ht hw
  · subst hxy; rw [h1] at hw; cases hw; exact hvt.1
  · rw [hfr y hxy] at hw; exact hwf y w hw
  · subst hxy; simp [h1]
  · rw [hfr y hxy]; exact hb y hy ht


section
open Imperative.BigStep

/-- The events a condition command emits are related to those of its simplification when the
    condition's value is kept. -/
private theorem check_rel {M : Expression.Factory} {σ : SemanticStore Expression} {l : String}
    {md : MetaData Expression} {e e' : Expression.Expr}
    (h : ∀ v, e.denoteEval M σ = some v ↔ e'.denoteEval M σ = some v) :
    (∀ w, (evalInterp (P := Expression)).holds w
        { factory := M, store := σ, label := l, expr := e, metadata := md } ↔
      (evalInterp (P := Expression)).holds w
        { factory := M, store := σ, label := l, expr := e', metadata := md }) :=
  fun _ => h _

/-- **One command, simplified.** A step of a command of the body is matched by a step of its
    simplification from the same store to the same store, with related events, and the
    invariant holds after it under the command's typing. -/
theorem simp_cmd {base ctx : Ctx} {M : Expression.Factory} {T : List CoreIdent}
    {Γ : VarTyping Expression}
    {σ σ1 : SemanticStore Expression} (S : Setup base M) (I : Inv base M T Γ ctx σ)
    {c : Imperative.Cmd Expression} (hok : Stmt.exprsOKIn base.factory Γ (.cmd (.cmd c)))
    (hT : ∀ y ∈ Stmt.idents (.cmd (.cmd c) : Statement), y ∈ T)
    {evs : List (Event Expression)} (h : EvalE M σ (.cmd c) σ1 evs) :
    ∃ evs', EvalE M σ (.cmd (simpCmd ctx c).1) σ1 evs' ∧
      List.Rel₂ (Event.WeakensAssume (evalInterp (P := Expression))) evs evs' ∧
      Inv base M T (Γ.extend (Cmd.typedDefinedVars c)) (simpCmd ctx c).2 σ1 := by
  match c, h with
  | .init x ty (.det e) md, .eval_init hev hinit hty hvar =>
    obtain ⟨h0, h1, hfr⟩ := hinit
    have hTe : e.NamesIn (fun y : CoreIdent => y ∈ T) :=
      namesIn_of_getFvars fun y hy => hT y (List.mem_cons_of_mem _ hy)
    obtain ⟨hg, hpres⟩ := simp_expr S I hok hTe (LExpr.denoteEval_defines hev)
    have he' := hpres _ hev
    rw [simpCmd_init_det]
    refine ⟨[], .eval_init he' (.init h0 h1 hfr) hty hvar, .nil, ?_⟩
    obtain ⟨ht', hwf', hb'⟩ := store_init I.typed I.wf h1 hfr hty I.bound
    refine ⟨I.fixed.record _ _, I.vs.record h1 (fun y hy => hfr y (Ne.symm hy)) he' hg.ops hg.ann,
      fun y r hm => ?_, ht', hwf', hb'⟩
    rcases mem_record hm with ⟨rfl, rfl⟩ | ⟨hm, -⟩
    · exact ⟨hT y List.mem_cons_self, hg.names⟩
    · exact I.names y r hm
  | .init x ty .nondet md, .eval_init_unconstrained hinit hty hvar =>
    obtain ⟨h0, h1, hfr⟩ := hinit
    rw [simpCmd_init_nondet]
    refine ⟨[], .eval_init_unconstrained (.init h0 h1 hfr) hty hvar, .nil, ?_⟩
    obtain ⟨ht', hwf', hb'⟩ := store_init I.typed I.wf h1 hfr hty I.bound
    exact ⟨I.fixed.invalidateVar _, I.vs.invalidateVar (fun y hy => hfr y (Ne.symm hy)),
      fun y r hm => I.names y r (mem_invalidateVar hm).1, ht', hwf', hb'⟩
  | .set x (.det e) md, .eval_set hev hup hst hvar =>
    obtain ⟨hp, h1, hfr⟩ := hup
    obtain ⟨ty, -, hok⟩ := hok
    have hTe : e.NamesIn (fun y : CoreIdent => y ∈ T) :=
      namesIn_of_getFvars fun y hy => hT y (List.mem_cons_of_mem _ hy)
    obtain ⟨hg, hpres⟩ := simp_expr S I hok hTe (LExpr.denoteEval_defines hev)
    have he' := hpres _ hev
    rw [simpCmd_set_det]
    refine ⟨[], .eval_set he' (.update hp h1 hfr) hst hvar, .nil, ?_⟩
    obtain ⟨ht', hwf', hb'⟩ := store_set I.typed I.wf h1 hfr hst I.bound
    refine ⟨I.fixed.record _ _, I.vs.record h1 (fun y hy => hfr y (Ne.symm hy)) he' hg.ops hg.ann,
      fun y r hm => ?_, ht', hwf', hb'⟩
    rcases mem_record hm with ⟨rfl, rfl⟩ | ⟨hm, -⟩
    · exact ⟨hT y List.mem_cons_self, hg.names⟩
    · exact I.names y r hm
  | .set x .nondet md, .eval_set_nondet hup hst hvar =>
    obtain ⟨hp, h1, hfr⟩ := hup
    rw [simpCmd_set_nondet]
    refine ⟨[], .eval_set_nondet (.update hp h1 hfr) hst hvar, .nil, ?_⟩
    obtain ⟨ht', hwf', hb'⟩ := store_set I.typed I.wf h1 hfr hst I.bound
    exact ⟨I.fixed.invalidateVar _, I.vs.invalidateVar (fun y hy => hfr y (Ne.symm hy)),
      fun y r hm => I.names y r (mem_invalidateVar hm).1, ht', hwf', hb'⟩
  | .assert l e md, .eval_assert =>
    have hTe : e.NamesIn (fun y : CoreIdent => y ∈ T) := namesIn_of_getFvars hT
    have hd := defines_of_bound I.wf fun i hi => I.bound i (hT i hi) (by
      obtain ⟨_, -, -, hdef, -⟩ := hok.1; exact hdef i hi)
    obtain ⟨-, hpres⟩ := simp_expr S I hok hTe hd
    obtain ⟨v, hv, -⟩ := eval_of_ok (c := base.carriers) hok I.typed hTe hd
    rw [simpCmd_assert]
    refine ⟨_, .eval_assert, .cons ⟨rfl, rfl, check_rel fun u => ?_⟩ .nil, I⟩
    rw [hv, hpres v hv]
  | .assume l e md, .eval_assume =>
    have hTe : e.NamesIn (fun y : CoreIdent => y ∈ T) := namesIn_of_getFvars hT
    rw [simpCmd_assume]
    refine ⟨_, .eval_assume, .cons ⟨rfl, rfl, fun _ hh => ?_⟩ .nil, I⟩
    exact (simp_expr S I hok hTe (LExpr.denoteEval_defines hh)).2 _ hh
  | .cover l e md, .eval_cover =>
    have hTe : e.NamesIn (fun y : CoreIdent => y ∈ T) := namesIn_of_getFvars hT
    have hd := defines_of_bound I.wf fun i hi => I.bound i (hT i hi) (by
      obtain ⟨_, -, -, hdef, -⟩ := hok.1; exact hdef i hi)
    obtain ⟨-, hpres⟩ := simp_expr S I hok hTe hd
    obtain ⟨v, hv, -⟩ := eval_of_ok (c := base.carriers) hok I.typed hTe hd
    rw [simpCmd_cover]
    refine ⟨_, .eval_cover, .cons ⟨rfl, rfl, check_rel fun u => ?_⟩ .nil, I⟩
    rw [hv, hpres v hv]

end


/-! ## What a run keeps of the store -/

section Keep
open Imperative.BigStep

/-- The store keeps model values, and every variable bound before keeps a value of its
    sort. -/
def Keeps (M : Expression.Factory) (σ σ' : SemanticStore Expression) : Prop :=
  WellFormedStore σ' M ∧
    ∀ y v, σ y = some v → ∃ w, σ' y = some w ∧ w.sort.toMonoTy = v.sort.toMonoTy

/-- Projecting on the store a run started from keeps what the run kept. -/
private theorem keeps_proj {M : Expression.Factory} {σ σa : SemanticStore Expression}
    (h : Keeps M σ σa) : Keeps M σ (projectStore σ σa) := by
  refine ⟨fun y w hw => ?_, fun y v hv => ?_⟩
  · simp only [projectStore] at hw; split at hw
    · exact h.1 y w hw
    · cases hw
  · obtain ⟨w, hw, hs⟩ := h.2 y v hv
    exact ⟨w, by simp [projectStore, hv, hw], hs⟩

/-- A run keeps the store's model values and the sorts of the variables bound before it. -/
private theorem brun_keeps {M : Expression.Factory} {ss : PStmts Expression}
    {σ : SemanticStore Expression} {evs : List (Event Expression)} {o : Outcome Expression}
    (h : BRun M ss σ evs o) (hwf : WellFormedStore σ M) : Keeps M σ o.store := by
  obtain ⟨hwf', hag⟩ := brun_typed h hwf
  refine ⟨hwf', fun y v hv => ?_⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (brun_dom h y (by simp [hv]))
  obtain ⟨_, hp, hw'⟩ := hag y v w hv hw
  exact ⟨w, hw, sort_eq_of_valueOfTy hw' hp⟩

/-- The store part of the invariant survives a run that keeps the store. -/
private theorem store_keeps {M : Expression.Factory} {T : List CoreIdent}
    {Γ : VarTyping Expression}
    {σ σ' : SemanticStore Expression} (hty : TypedOn M Γ T σ)
    (hk : Keeps M σ σ') (hb : ∀ y, (σ' y).isSome → (σ y).isSome)
    (hbd : ∀ y ∈ T, (Γ y).isSome → (σ y).isSome) :
    TypedOn M Γ T σ' ∧ (∀ y ∈ T, (Γ y).isSome → (σ' y).isSome) := by
  have hget : ∀ y w, σ' y = some w → ∃ v, σ y = some v ∧ w.sort.toMonoTy = v.sort.toMonoTy := by
    intro y w hw
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hb y (by simp [hw]))
    obtain ⟨w', hw', hs⟩ := hk.2 y v hv
    rw [hw] at hw'; cases hw'
    exact ⟨v, hv, hs⟩
  refine ⟨fun y hy t w ht hw => ?_, fun y hy ht => ?_⟩
  · obtain ⟨v, hv, hs⟩ := hget y w hw
    exact ⟨hk.1 y w hw, by rw [hs]; exact (hty y hy t v ht hv).2⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hbd y hy ht)
    obtain ⟨w, hw, -⟩ := hk.2 y v hv
    simp [hw]

/-- A variable bound after a projection was bound before it. -/
private theorem projectStore_isSome {σ σa : SemanticStore Expression} (y : CoreIdent)
    (h : (projectStore σ σa y).isSome) : (σ y).isSome := by
  simp only [projectStore] at h; split at h
  · assumption
  · cases h

end Keep


/-! ## Statements -/

/-- An expression `isTrue` holds of is the constant `true`. -/
private theorem eq_true_of_isTrue {c : Expression.Expr} (h : c.isTrue = true) :
    ∃ m, c = .const m (.boolConst true) := by
  unfold LExpr.isTrue at h; split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- An expression `isFalse` holds of is the constant `false`. -/
private theorem eq_false_of_isFalse {c : Expression.Expr} (h : c.isFalse = true) :
    ∃ m, c = .const m (.boolConst false) := by
  unfold LExpr.isFalse at h; split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- The arm a guard evaluating to `b` selects is among the live arms. -/
private theorem mem_liveArms {M : Expression.Factory} {σ : SemanticStore Expression}
    {c : Expression.Expr} {b : Bool}
    (hc : c.denoteEval M σ = some (SemValue.ofBool M.model.tcInterp b)) (a₁ a₂ : Ctx) :
    (if b then a₁ else a₂) ∈ liveArms (.det c) [a₁, a₂] := by
  rw [liveArms_det]
  have hne : ∀ m b', c = .const m (.boolConst b') → b' = b := by
    rintro m b' rfl
    rw [LExpr.denoteEval_boolConst (T := CoreLParams)] at hc
    exact SemValue.ofBool_injective (Option.some.inj hc)
  split
  · rename_i ht; obtain ⟨m, rfl⟩ := eq_true_of_isTrue ht
    cases hne m true rfl; simp
  · split
    · rename_i _ hf; obtain ⟨m, rfl⟩ := eq_false_of_isFalse hf
      cases hne m false rfl; simp
    · cases b <;> simp


section Run
open Imperative.BigStep

/-- The invariant after a branch whose arm `arm` ran to its normal end `σa`. -/
private theorem inv_ite {base ctx armCtx : Ctx} {M : Expression.Factory} {T : List CoreIdent}
    {Γ Γa : VarTyping Expression}
    {σ σa : SemanticStore Expression} {live : List Ctx} {ts es arm : List Statement}
    {evs : List (Event Expression)}
    (I : Inv base M T Γ ctx σ) (Ia : Inv base M T Γa armCtx σa) (hmem : armCtx ∈ live)
    (hrun : BRun M arm σ evs (.normal σa))
    (harm : ∀ z, z ∈ Block.modifiedOrDefinedVars (P := Expression) (C := Command) arm false →
      z ∈ Block.modifiedOrDefinedVars (P := Expression) (C := Command) ts false ++
        Block.modifiedOrDefinedVars (P := Expression) (C := Command) es false)
    (hdef : ∀ z, z ∈ Block.definedVars (P := Expression) (C := Command) arm false →
      z ∈ Block.definedVars (P := Expression) (C := Command) ts false ++
        Block.definedVars (P := Expression) (C := Command) es false) :
    Inv base M T Γ
      (ctx.join live ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).vars
        ((simpStmts ctx ts).2.2.union (simpStmts ctx es).2.2).defined) (projectStore σ σa) := by
  have hw := (simpStmts_writes ctx ts).union (simpStmts_writes ctx es)
  have hk := keeps_proj (brun_keeps hrun I.wf)
  obtain ⟨ht, hb⟩ := store_keeps I.typed hk projectStore_isSome I.bound
  refine ⟨I.fixed.join _ _ _, ?_, fun y r hm => ?_, ht, hk.1, hb⟩
  · exact ValuesSound.join I.vs Ia.vs hmem (Ia.fixed.2.1.trans I.fixed.2.1.symm) hw
      (fun z hz => brun_frame_modifiedOrDefined hrun z fun h => hz (harm z h))
      (fun z hz h0 => brun_undef hrun z (fun h => hz (hdef z h)) h0)
  · rcases mem_join hm with ⟨-, -, hall, -⟩ | ⟨hb, -⟩
    · obtain ⟨v', hv', hb⟩ := hall armCtx hmem
      obtain ⟨hy, hn⟩ := Ia.names y v' hv'
      refine ⟨hy, fun z ty hz => hn z ty ?_⟩
      have he : v'.eraseMetadata = r.eraseMetadata := LExpr.replaceMetadata_const_of_beq () hb
      rw [← LExpr.freeVars_eraseMetadata, ← he, LExpr.freeVars_eraseMetadata] at hz
      exact hz
    · exact I.names y r hb

/-- The invariant after a block whose body ran from `σ` to the outcome `o`. -/
private theorem inv_block {base ctx : Ctx} {M : Expression.Factory} {T : List CoreIdent}
    {Γ : VarTyping Expression}
    {σ : SemanticStore Expression} {ss : List Statement} {evs : List (Event Expression)}
    {o : Outcome Expression} (I : Inv base M T Γ ctx σ) (hrun : BRun M ss σ evs o) :
    Inv base M T Γ ({ ctx with values := (simpStmts ctx ss).2.1.values }.invalidate
      (simpStmts ctx ss).2.2.vars) (projectStore σ o.store) := by
  have hk := keeps_proj (brun_keeps hrun I.wf)
  obtain ⟨ht, hb⟩ := store_keeps I.typed hk projectStore_isSome I.bound
  refine ⟨(I.fixed.values _).invalidate _, I.vs.block ss (brun_frame_modifiedOrDefined hrun),
    fun y r hm => ?_, ht, hk.1, hb⟩
  have hw := simpStmts_writes ctx ss
  obtain ⟨hm, hyv, -⟩ := mem_invalidate hm
  exact I.names y r (simpStmts_values_sub ctx ss hm (fun h => hyv ((hw.vars_iff _).mpr h)))


mutual
/-- **The simplified list matches the run of the list.** A run of a list of the body from a
    point where the invariant holds is matched by a run of its simplification, from the same
    store to the same outcome, with related events; after a normal end the invariant holds
    again. -/
theorem simp_run {base : Ctx} {M : Expression.Factory} {T : List CoreIdent}
    (S : Setup base M) :
    ∀ {ss : PStmts Expression} {σ : SemanticStore Expression} {evs : List (Event Expression)}
      {o : Outcome Expression}, BRun M ss σ evs o →
    ∀ {ctx : Ctx} {Γ : VarTyping Expression}, Inv base M T Γ ctx σ →
      Block.exprsOKIn base.factory Γ ss → (∀ y ∈ Block.idents ss, y ∈ T) →
      Block.noLoops ss = true →
      ∃ evs', BRun M (simpStmts ctx ss).1 σ evs' o ∧
        List.Rel₂ (Event.WeakensAssume (evalInterp (P := Expression))) evs evs' ∧
        ∀ σ', o = .normal σ' → ∃ Γ', Inv base M T Γ' (simpStmts ctx ss).2.1 σ'
  | _, _, _, _, .nil, ctx, Γ, I, _, _, _ => by
    rw [simpStmts_nil]
    exact ⟨[], .nil, .nil, fun σ' h => by cases h; exact ⟨Γ, I⟩⟩
  | _, _, _, _, .cons_normal (s := s) (rest := rest) h1 h2, ctx, Γ, I, hok, hT, hnl => by
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    obtain ⟨hs, hrest⟩ := hok
    have hT1 : ∀ y ∈ Stmt.idents s, y ∈ T := fun y hy => hT y (by simp [Block.idents, hy])
    have hT2 : ∀ y ∈ Block.idents rest, y ∈ T := fun y hy => hT y (by simp [Block.idents, hy])
    obtain ⟨s', evs1', hout, h1', hm1, hinv1⟩ := simp_runS S h1 I hs hT1 hnl.1
    obtain ⟨evs2', h2', hm2, hinv2⟩ := simp_run S h2 (hinv1 _ rfl) hrest hT2 hnl.2
    rw [simpStmts_cons, hout]
    exact ⟨evs1' ++ evs2', .cons_normal h1' h2', hm1.append hm2, hinv2⟩
  | _, _, _, _, .cons_exit (s := s) (rest := rest) h1, ctx, Γ, I, hok, hT, hnl => by
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    obtain ⟨hs, -⟩ := hok
    have hT1 : ∀ y ∈ Stmt.idents s, y ∈ T := fun y hy => hT y (by simp [Block.idents, hy])
    obtain ⟨s', evs1', hout, h1', hm1, -⟩ := simp_runS S h1 I hs hT1 hnl.1
    rw [simpStmts_cons, hout]
    exact ⟨evs1', .cons_exit h1', hm1, fun _ h => by cases h⟩
/-- **One statement, simplified.** `simp_run` for a statement, which `simpStmt` turns into
    a single statement; after a normal end the invariant holds under the statement's
    typing. -/
private theorem simp_runS {base : Ctx} {M : Expression.Factory} {T : List CoreIdent}
    (S : Setup base M) :
    ∀ {s : PStmt Expression} {σ : SemanticStore Expression} {evs : List (Event Expression)}
      {o : Outcome Expression}, BRunS M s σ evs o →
    ∀ {ctx : Ctx} {Γ : VarTyping Expression}, Inv base M T Γ ctx σ →
      Stmt.exprsOKIn base.factory Γ s → (∀ y ∈ Stmt.idents s, y ∈ T) →
      Stmt.noLoops s = true →
      ∃ s' evs', (simpStmt ctx s).1 = [s'] ∧ BRunS M s' σ evs' o ∧
        List.Rel₂ (Event.WeakensAssume (evalInterp (P := Expression))) evs evs' ∧
        ∀ σ', o = .normal σ' →
          Inv base M T (Γ.extend (Stmt.typedDefinedVars (P := Expression) s))
            (simpStmt ctx s).2.1 σ'
  | _, _, _, _, .cmd (c := .cmd c) h, ctx, Γ, I, hok, hT, _ => by
    obtain ⟨evs', h', hm, I'⟩ := simp_cmd S I hok hT h
    rw [simpStmt_cmd]
    exact ⟨_, evs', rfl, .cmd h', hm, fun σ' ho => by cases ho; exact I'⟩
  | _, _, _, _, .cmd (c := .call _ _ _ _) h, _, _, _, _, _, _ => h.elim
  | _, _, _, _, .ite_true (c := c) (tss := ts) (ess := es) (md := md) hc h, ctx, Γ, I, hok, hT,
      hnl => by
    simp only [Stmt.exprsOKIn] at hok
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨hcok, hts, -⟩ := hok
    have hTc : c.NamesIn (fun y : CoreIdent => y ∈ T) := namesIn_of_getFvars fun y hy =>
      hT y (by simp [Stmt.idents, ExprOrNondet.getVars, hy])
    have hc' := (simp_expr S I hcok hTc (LExpr.denoteEval_defines hc)).2 _ hc
    obtain ⟨evs', h', hm, hinv⟩ := simp_run S h I hts
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl.1
    rw [simpStmt_ite_det_eq]
    refine ⟨_, evs', rfl, .ite_true hc' h', hm, fun σ' ho => ?_⟩
    obtain ⟨σa, rfl, rfl⟩ := Outcome.proj_normal ho
    obtain ⟨Γa, Ia⟩ := hinv σa rfl
    exact inv_ite I Ia (mem_liveArms (b := true) hc' _ _) h
      (fun z hz => List.mem_append_left _ hz) (fun z hz => List.mem_append_left _ hz)
  | _, _, _, _, .ite_false (c := c) (tss := ts) (ess := es) (md := md) hc h, ctx, Γ, I, hok, hT,
      hnl => by
    simp only [Stmt.exprsOKIn] at hok
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨hcok, -, hes⟩ := hok
    have hTc : c.NamesIn (fun y : CoreIdent => y ∈ T) := namesIn_of_getFvars fun y hy =>
      hT y (by simp [Stmt.idents, ExprOrNondet.getVars, hy])
    have hc' := (simp_expr S I hcok hTc (LExpr.denoteEval_defines hc)).2 _ hc
    obtain ⟨evs', h', hm, hinv⟩ := simp_run S h I hes
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl.2
    rw [simpStmt_ite_det_eq]
    refine ⟨_, evs', rfl, .ite_false hc' h', hm, fun σ' ho => ?_⟩
    obtain ⟨σa, rfl, rfl⟩ := Outcome.proj_normal ho
    obtain ⟨Γa, Ia⟩ := hinv σa rfl
    exact inv_ite I Ia (mem_liveArms (b := false) hc' _ _) h
      (fun z hz => List.mem_append_right _ hz) (fun z hz => List.mem_append_right _ hz)
  | _, _, _, _, .ite_nondet_true (tss := ts) (ess := es) (md := md) h, ctx, Γ, I, hok, hT,
      hnl => by
    simp only [Stmt.exprsOKIn] at hok
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨evs', h', hm, hinv⟩ := simp_run S h I hok.1
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl.1
    rw [simpStmt_ite_nondet_eq]
    refine ⟨_, evs', rfl, .ite_nondet_true h', hm, fun σ' ho => ?_⟩
    obtain ⟨σa, rfl, rfl⟩ := Outcome.proj_normal ho
    obtain ⟨Γa, Ia⟩ := hinv σa rfl
    exact inv_ite I Ia (by rw [liveArms_nondet]; simp) h
      (fun z hz => List.mem_append_left _ hz) (fun z hz => List.mem_append_left _ hz)
  | _, _, _, _, .ite_nondet_false (tss := ts) (ess := es) (md := md) h, ctx, Γ, I, hok, hT,
      hnl => by
    simp only [Stmt.exprsOKIn] at hok
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨evs', h', hm, hinv⟩ := simp_run S h I hok.2
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl.2
    rw [simpStmt_ite_nondet_eq]
    refine ⟨_, evs', rfl, .ite_nondet_false h', hm, fun σ' ho => ?_⟩
    obtain ⟨σa, rfl, rfl⟩ := Outcome.proj_normal ho
    obtain ⟨Γa, Ia⟩ := hinv σa rfl
    exact inv_ite I Ia (by rw [liveArms_nondet]; simp) h
      (fun z hz => List.mem_append_right _ hz) (fun z hz => List.mem_append_right _ hz)
  | _, _, _, _, .block (ss := ss) (l := l) (md := md) h, ctx, Γ, I, hok, hT, hnl => by
    simp only [Stmt.exprsOKIn] at hok
    rw [Stmt.noLoops_block] at hnl
    obtain ⟨evs', h', hm, -⟩ := simp_run S h I hok
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl
    rw [simpStmt_block_eq]
    refine ⟨_, evs', rfl, .block h', hm, fun σ' ho => ?_⟩
    rw [Outcome.block_normal ho]
    exact inv_block I h
  | _, _, _, _, .exit (l := l) (md := md), ctx, Γ, I, _, _, _ => by
    rw [simpStmt_exit]
    exact ⟨_, [], rfl, .exit, .nil, fun _ h => by cases h⟩
  | _, _, _, _, .typeDecl (tc := tc) (md := md), ctx, Γ, I, _, _, _ => by
    rw [simpStmt_typeDecl]
    exact ⟨_, [], rfl, .typeDecl, .nil, fun σ' h => by cases h; exact I⟩
  | _, _, _, _, .loop_exit _, _, _, _, _, _, hnl
  | _, _, _, _, .loop_iter _ _ _, _, _, _, _, _, hnl
  | _, _, _, _, .loop_break _ _, _, _, _, _, _, hnl => by simp [Stmt.noLoops_loop] at hnl
end


mutual
/-- **The simplified list matches every prefix of a run of the list**: `simp_run` for a run
    that stops right after a command. -/
theorem simp_reach {base : Ctx} {M : Expression.Factory} {T : List CoreIdent}
    (S : Setup base M) :
    ∀ {ss : PStmts Expression} {σ : SemanticStore Expression} {evs : List (Event Expression)},
      BReach M ss σ evs →
    ∀ {ctx : Ctx} {Γ : VarTyping Expression}, Inv base M T Γ ctx σ →
      Block.exprsOKIn base.factory Γ ss → (∀ y ∈ Block.idents ss, y ∈ T) →
      Block.noLoops ss = true →
      ∃ evs', BReach M (simpStmts ctx ss).1 σ evs' ∧
        List.Rel₂ (Event.WeakensAssume (evalInterp (P := Expression))) evs evs'
  | _, _, _, .here (s := s) (rest := rest) h, ctx, Γ, I, hok, hT, hnl => by
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    obtain ⟨hs, -⟩ := hok
    have hT1 : ∀ y ∈ Stmt.idents s, y ∈ T := fun y hy => hT y (by simp [Block.idents, hy])
    obtain ⟨s', evs', hout, h', hm⟩ := simp_reachS S h I hs hT1 hnl.1
    rw [simpStmts_cons, hout]
    exact ⟨evs', .here h', hm⟩
  | _, _, _, .later (s := s) (rest := rest) h1 h2, ctx, Γ, I, hok, hT, hnl => by
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    obtain ⟨hs, hrest⟩ := hok
    have hT1 : ∀ y ∈ Stmt.idents s, y ∈ T := fun y hy => hT y (by simp [Block.idents, hy])
    have hT2 : ∀ y ∈ Block.idents rest, y ∈ T := fun y hy => hT y (by simp [Block.idents, hy])
    obtain ⟨s', evs1', hout, h1', hm1, hinv1⟩ := simp_runS S h1 I hs hT1 hnl.1
    obtain ⟨evs2', h2', hm2⟩ := simp_reach S h2 (hinv1 _ rfl) hrest hT2 hnl.2
    rw [simpStmts_cons, hout]
    exact ⟨evs1' ++ evs2', .later h1' h2', hm1.append hm2⟩
/-- `simp_reach` for a statement. -/
private theorem simp_reachS {base : Ctx} {M : Expression.Factory} {T : List CoreIdent}
    (S : Setup base M) :
    ∀ {s : PStmt Expression} {σ : SemanticStore Expression} {evs : List (Event Expression)},
      BReachS M s σ evs →
    ∀ {ctx : Ctx} {Γ : VarTyping Expression}, Inv base M T Γ ctx σ →
      Stmt.exprsOKIn base.factory Γ s → (∀ y ∈ Stmt.idents s, y ∈ T) →
      Stmt.noLoops s = true →
      ∃ s' evs', (simpStmt ctx s).1 = [s'] ∧ BReachS M s' σ evs' ∧
        List.Rel₂ (Event.WeakensAssume (evalInterp (P := Expression))) evs evs'
  | _, _, _, .cmd (c := .cmd c) h hne, ctx, Γ, I, hok, hT, _ => by
    obtain ⟨evs', h', hm, -⟩ := simp_cmd S I hok hT h
    rw [simpStmt_cmd]
    exact ⟨_, evs', rfl, .cmd h' (hm.ne_nil hne), hm⟩
  | _, _, _, .cmd (c := .call _ _ _ _) h _, _, _, _, _, _, _ => h.elim
  | _, _, _, .ite_true (c := c) (tss := ts) (ess := es) (md := md) hc h, ctx, Γ, I, hok, hT,
      hnl => by
    simp only [Stmt.exprsOKIn] at hok
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨hcok, hts, -⟩ := hok
    have hTc : c.NamesIn (fun y : CoreIdent => y ∈ T) := namesIn_of_getFvars fun y hy =>
      hT y (by simp [Stmt.idents, ExprOrNondet.getVars, hy])
    have hc' := (simp_expr S I hcok hTc (LExpr.denoteEval_defines hc)).2 _ hc
    obtain ⟨evs', h', hm⟩ := simp_reach S h I hts
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl.1
    rw [simpStmt_ite_det_eq]
    exact ⟨_, evs', rfl, .ite_true hc' h', hm⟩
  | _, _, _, .ite_false (c := c) (tss := ts) (ess := es) (md := md) hc h, ctx, Γ, I, hok, hT,
      hnl => by
    simp only [Stmt.exprsOKIn] at hok
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨hcok, -, hes⟩ := hok
    have hTc : c.NamesIn (fun y : CoreIdent => y ∈ T) := namesIn_of_getFvars fun y hy =>
      hT y (by simp [Stmt.idents, ExprOrNondet.getVars, hy])
    have hc' := (simp_expr S I hcok hTc (LExpr.denoteEval_defines hc)).2 _ hc
    obtain ⟨evs', h', hm⟩ := simp_reach S h I hes
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl.2
    rw [simpStmt_ite_det_eq]
    exact ⟨_, evs', rfl, .ite_false hc' h', hm⟩
  | _, _, _, .ite_nondet_true (tss := ts) (ess := es) (md := md) h, ctx, Γ, I, hok, hT,
      hnl => by
    simp only [Stmt.exprsOKIn] at hok
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨evs', h', hm⟩ := simp_reach S h I hok.1
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl.1
    rw [simpStmt_ite_nondet_eq]
    exact ⟨_, evs', rfl, .ite_nondet_true h', hm⟩
  | _, _, _, .ite_nondet_false (tss := ts) (ess := es) (md := md) h, ctx, Γ, I, hok, hT,
      hnl => by
    simp only [Stmt.exprsOKIn] at hok
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨evs', h', hm⟩ := simp_reach S h I hok.2
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl.2
    rw [simpStmt_ite_nondet_eq]
    exact ⟨_, evs', rfl, .ite_nondet_false h', hm⟩
  | _, _, _, .block (ss := ss) (l := l) (md := md) h, ctx, Γ, I, hok, hT, hnl => by
    simp only [Stmt.exprsOKIn] at hok
    rw [Stmt.noLoops_block] at hnl
    obtain ⟨evs', h', hm⟩ := simp_reach S h I hok
      (fun y hy => hT y (by simp [Stmt.idents, hy])) hnl
    rw [simpStmt_block_eq]
    exact ⟨_, evs', rfl, .block h', hm⟩
  | _, _, _, .loop_here _ _, _, _, _, _, _, hnl
  | _, _, _, .loop_later _ _ _, _, _, _, _, _, hnl => by simp [Stmt.noLoops_loop] at hnl
end

end Run

end Core.Simplify
