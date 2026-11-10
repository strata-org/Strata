/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.Assumptions
public import Strata.DL.Lambda.LExprDenoteEval
public import Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprType
import all Strata.DL.Lambda.LTyUnifyProps
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.Util.ListMapProps

/-! # Renaming the operators of an expression

How renaming the operators of an expression interacts with typing, denotation and
evaluation.

## Key results

- `LExpr.typeCheck_renameOps`, `LExpr.HasTypeA_renameOps_iff` — renaming keeps typing.
- `denote_renameOps`, `LExpr.denoteEval_renameOps` — a renamed expression denotes and
  evaluates, under the renamed model, as the original does.
- `opsConsistent_op_of_ground_instance`, `opsConsistent_op_of_mono` — an operator annotated
  with a ground instance of its function's signature, or with the signature of a monomorphic
  function, is `OpsConsistent`.
-/

public section

namespace Lambda

variable {T : LExprParams}

/-- Rename every operator `o` annotated `ty` to `g o ty`, keeping metadata and
    annotations. -/
@[expose] def LExpr.renameOps (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) :
    LExpr T.mono → LExpr T.mono
  | .const m c => .const m c
  | .op m o ty => .op m (g o ty) ty
  | .bvar m i => .bvar m i
  | .fvar m x ty => .fvar m x ty
  | .abs m n ty e => .abs m n ty (renameOps g e)
  | .quant m k n ty tr e => .quant m k n ty (renameOps g tr) (renameOps g e)
  | .app m f a => .app m (renameOps g f) (renameOps g a)
  | .ite m c t e => .ite m (renameOps g c) (renameOps g t) (renameOps g e)
  | .eq m a b => .eq m (renameOps g a) (renameOps g b)

/-- Renaming operators does not change the result of type checking. -/
theorem LExpr.typeCheck_renameOps (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta)
    (Δ : List LMonoTy) (e : LExpr T.mono) :
    LExpr.typeCheck Δ (e.renameOps g) = LExpr.typeCheck Δ e := by
  induction e generalizing Δ with
  | const | bvar | fvar => rfl
  | op _ _ ty => cases ty <;> rfl
  | abs _ _ ty _ ih => cases ty <;> simp [LExpr.renameOps, LExpr.typeCheck, ih]
  | quant _ _ _ ty _ _ ih1 ih2 => cases ty <;> simp [LExpr.renameOps, LExpr.typeCheck, ih1, ih2]
  | app _ _ _ ih1 ih2 => simp [LExpr.renameOps, LExpr.typeCheck, ih1, ih2]
  | ite _ _ _ _ ih1 ih2 ih3 => simp [LExpr.renameOps, LExpr.typeCheck, ih1, ih2, ih3]
  | eq _ _ _ ih1 ih2 => simp [LExpr.renameOps, LExpr.typeCheck, ih1, ih2]

/-- A renamed expression has exactly the types of the original. -/
theorem LExpr.HasTypeA_renameOps_iff
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta)
    {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy} :
    (e.renameOps g).HasTypeA Δ τ ↔ e.HasTypeA Δ τ := by
  rw [LExpr.HasTypeA_iff_typeCheck, LExpr.HasTypeA_iff_typeCheck, LExpr.typeCheck_renameOps]

/-- Renaming preserves a typing derivation. -/
theorem LExpr.HasTypeA_renameOps
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta)
    {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy} (h : e.HasTypeA Δ τ) :
    (e.renameOps g).HasTypeA Δ τ :=
  (LExpr.HasTypeA_renameOps_iff g).mpr h

/-- Every annotated operator of `e`, renamed by `g`, is read by `op'` as `op` reads it. -/
@[expose] def LExpr.OpsReadAs {tc : TyConstrInterp} (op op' : OpInterp tc)
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) (e : LExpr T.mono) : Prop :=
  ∀ p ∈ e.opAnnots, op' (g p.1 (some p.2)).name = op p.1.name

/-- A denotation of `e` under `op` is a denotation of `e` with operators renamed by `g` under
    `op'`, when `op'` reads each renamed operator of `e` as `op` reads it. -/
private theorem Denotes.renameOps {tc : TyConstrInterp} {op op' : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal}
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta)
    {Δ : List LMonoTy} {bv : BVarVal tc vt Δ} {e : LExpr T.mono} {τ : LMonoTy}
    {h : e.HasTypeA Δ τ} {v : TyDenote tc vt τ}
    (hd : Denotes tc op fv vt bv e τ h v) (hops : LExpr.OpsReadAs op op' g e) :
    Denotes tc op' fv vt bv (e.renameOps g) τ (LExpr.HasTypeA_renameOps g h) v := by
  induction hd with
  | const => exact .const _
  | op _ =>
    rename_i o ty _
    have hro : op' (g o (some ty)).name = op o.name :=
      hops (o, ty) (by simp [LExpr.opAnnots])
    show Denotes tc op' fv vt _ (.op _ (g o (some ty)) (some ty)) ty _ (op o.name _)
    rw [← hro]
    exact .op _
  | fvar => exact .fvar _
  | bvar => exact .bvar _
  | abs _ _ ih => exact .abs _ (fun x => ih x (fun p hp => hops p (by simpa [LExpr.opAnnots] using
      hp)))
  | app _ _ _ ih1 ih2 =>
    exact .app _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
  | ite_true _ _ _ ih1 ih2 =>
    exact .ite_true _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
  | ite_false _ _ _ ih1 ih2 =>
    exact .ite_false _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
  | eq_true _ _ _ ih1 ih2 =>
    exact .eq_true _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
  | eq_false _ _ _ hne ih1 ih2 =>
    exact .eq_false _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))) hne
  | quant_all_true _ _ ih =>
    exact .quant_all_true _ (fun x => ih x (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
  | quant_all_false _ w _ ih =>
    exact .quant_all_false _ w (ih (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
  | quant_exist_true _ w _ ih =>
    exact .quant_exist_true _ w (ih (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))
  | quant_exist_false _ _ ih =>
    exact .quant_exist_false _ (fun x => ih x (fun p hp => hops p (by simp [LExpr.opAnnots, hp])))

/-- **Renaming law for denotation.** A renamed expression denotes under `op'` what the
    original denotes under `op`, when `op'` reads each renamed operator as `op` reads the
    original. -/
theorem denote_renameOps {tc : TyConstrInterp} {op op' : OpInterp tc} {fv : FreeVarVal T tc}
    {vt : TyVarVal} (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta)
    {Δ : List LMonoTy} (bv : BVarVal tc vt Δ) {e : LExpr T.mono} {τ : LMonoTy}
    (h : e.HasTypeA Δ τ) (h' : (e.renameOps g).HasTypeA Δ τ)
    (hops : LExpr.OpsReadAs op op' g e) :
    LExpr.denote tc op' fv vt bv (e.renameOps g) τ h' = LExpr.denote tc op fv vt bv e τ h :=
  (Denotes_denote (Denotes.renameOps g (denote_Denotes _ _ _ _ bv e τ h) hops)).symm

/-- Annotating the free variables of a renamed expression is renaming the annotated
    expression. -/
private theorem LExpr.annotateFvars_renameOps
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta)
    (ann : Identifier T.IDMeta → Option LMonoTy) (e : LExpr T.mono) :
    (e.renameOps g).annotateFvars ann = (e.annotateFvars ann).renameOps g := by
  induction e <;> simp_all [LExpr.renameOps, LExpr.annotateFvars]

/-- Renaming operators keeps the free variables. -/
theorem LExpr.getVars_renameOps
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) (e : LExpr T.mono) :
    LExpr.LExpr.getVars (e.renameOps g) = LExpr.LExpr.getVars e := by
  induction e <;> simp_all [LExpr.renameOps, LExpr.LExpr.getVars]

/-- Annotating free variables keeps the annotated operators. -/
private theorem LExpr.opAnnots_annotateFvars (ann : Identifier T.IDMeta → Option LMonoTy)
    (e : LExpr T.mono) : (e.annotateFvars ann).opAnnots = e.opAnnots := by
  induction e <;> simp_all [LExpr.annotateFvars, LExpr.opAnnots]

/-- Denotations of two equal expressions are heterogeneously equal, whatever their typing
    derivations. -/
private theorem denote_heq_of_eq' {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal} {e₁ e₂ : LExpr T.mono} {τ : LMonoTy} (he : e₁ = e₂)
    (h₁ : e₁.HasTypeA [] τ) (h₂ : e₂.HasTypeA [] τ) :
    HEq (LExpr.denote tc op fv vt .nil e₁ τ h₁) (LExpr.denote tc op fv vt .nil e₂ τ h₂) := by
  subst he; rfl

/-- **Renaming law for evaluation.** Evaluating a renamed expression in a model `M'` that
    shares `M`'s carriers and type-variable sorts, and reads each renamed operator as `M`
    reads the original, gives what evaluating the original in `M` gives. -/
theorem LExpr.denoteEval_renameOps [DecidableEq T.IDMeta] {M M' : ModeledFactory T}
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) (σ : ValStore T)
    (e : LExpr T.mono)
    (htc : M'.model.tcInterp = M.model.tcInterp)
    (hinh : HEq M'.model.allInhabited M.model.allInhabited)
    (htv : M'.tyVarVal = M.tyVarVal)
    (hops : ∀ p ∈ e.opAnnots,
      HEq (M'.model.opInterp (g p.1 (some p.2)).name) (M.model.opInterp p.1.name)) :
    (e.renameOps g).denoteEval M' σ = e.denoteEval M σ := by
  obtain ⟨F', ⟨tc', op', inh', ic', as', cc'⟩, tv'⟩ := M'
  obtain ⟨F, ⟨tc, op, inh, ic, as, cc⟩, tv⟩ := M
  dsimp only at htc hinh htv hops ⊢
  subst htc htv
  obtain rfl := eq_of_heq hinh
  have hops' : LExpr.OpsReadAs op op' g (e.annotateFvars σ.ann) := by
    intro p hp
    rw [LExpr.opAnnots_annotateFvars] at hp
    exact eq_of_heq (hops p hp)
  have hann := LExpr.annotateFvars_renameOps g σ.ann e
  apply Option.ext
  intro v
  rw [LExpr.denoteEval_eq_some_iff, LExpr.denoteEval_eq_some_iff]
  simp only [ValStore.Defines, LExpr.getVars_renameOps]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hτ' : (e.annotateFvars σ.ann).HasTypeA [] τ :=
      (LExpr.HasTypeA_renameOps_iff g).mp (hann ▸ hτ)
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    refine eq_of_heq ((denote_heq_of_eq' hann hτ (LExpr.HasTypeA_renameOps g hτ')).trans ?_)
    rw [denote_renameOps g .nil hτ' _ hops']
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hτ' : ((e.renameOps g).annotateFvars σ.ann).HasTypeA [] τ :=
      hann ▸ LExpr.HasTypeA_renameOps g hτ
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    refine eq_of_heq (HEq.symm ((denote_heq_of_eq' hann hτ' (LExpr.HasTypeA_renameOps g hτ)).trans
        ?_))
    rw [denote_renameOps g .nil hτ _ hops']

end Lambda

end -- public section

namespace Lambda

/-- **An operator annotated with a ground instance of its function's signature is
    `OpsConsistent`**, for a polymorphic function. -/
theorem opsConsistent_op_of_ground_instance {T : LExprParams} {F : Factory T} {m :
    T.mono.base.Metadata}
    {o : T.Identifier} {ty : LMonoTy} {fn : LFunc T} (hfn : F[o.name]? = some fn)
    (hpoly : fn.typeArgs ≠ []) (hty : ty.freeVars = [])
    (hinst : ∃ σ : Subst, ty = LMonoTy.subst σ (LMonoTy.mkArrow' fn.output (fn.inputs.map
        Prod.snd))) :
    OpsConsistent F (.op m o (some ty)) := by
  obtain ⟨σ, hσ⟩ := hinst
  have hv : fn.inputs.values = fn.inputs.map Prod.snd := ListMap.values_eq_map_snd _
  obtain ⟨si, hu, hsi⟩ := Constraints_unify_ground_instance_complete ty
    (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)) σ hty hσ.symm
  unfold OpsConsistent
  rw [hfn]
  simp only
  have hts : LFunc.opTypeSubst fn (.op m o (some ty)) = some si.subst := by
    unfold LFunc.opTypeSubst
    simp only [List.isEmpty_iff, hpoly, ↓reduceIte, hv, hu]
  rw [hts]
  exact hsi.symm

/-- **An operator of a monomorphic function annotated with its signature is
    `OpsConsistent`.** -/
theorem opsConsistent_op_of_mono {T : LExprParams} {F : Factory T} {m : T.mono.base.Metadata}
    {o : T.Identifier} {fn : LFunc T} (hfn : F[o.name]? = some fn) (hmono : fn.typeArgs = []) :
    OpsConsistent F (.op m o (some (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)))) := by
  unfold OpsConsistent
  rw [hfn]
  simp only
  have hts : LFunc.opTypeSubst fn (.op m o (some (LMonoTy.mkArrow' fn.output
      (fn.inputs.map Prod.snd)))) = some Subst.empty := by
    unfold LFunc.opTypeSubst
    simp [hmono]
  rw [hts]
  simp only [Subst.empty]; exact (LMonoTy.subst_nil _).symm

end Lambda
