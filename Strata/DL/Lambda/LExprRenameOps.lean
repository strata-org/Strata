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
import Strata.DL.Lambda.Denote.LExprDenoteConsts
public import Strata.DL.Lambda.LConstData
import all Strata.DL.Lambda.LConstData
import Strata.Util.ListMapProps
import all Strata.DL.Lambda.LTyProps
import Strata.DL.Lambda.LTyMatchProps

/-! # Renaming the operators of an expression

How renaming the operators of an expression interacts with typing, denotation and
evaluation.

## Key results

- `LExpr.typeCheck_renameOps`, `LExpr.HasTypeA_renameOps_iff` — renaming keeps typing.
- `denote_renameOps`, `LExpr.denoteEval_renameOps` — a renamed expression denotes and
  evaluates, under the renamed model, as the original does.
- `LExpr.renameOpNodes_eq_renameOps` — on an expression whose constants hold no datatype
  value, renaming the operator nodes (`LExpr.renameOpNodes`) is `LExpr.renameOps`.
- `opsConsistent_op_of_instance`, `opsConsistent_op_of_mono` — an operator annotated
  with an instance of its function's signature, or with the signature of a monomorphic
  function, is `OpsConsistent`.
-/

public section

namespace Lambda

variable {T : LExprParams}

mutual
/-- Renaming datatype operators keeps a constant's sort and well-typedness. -/
private theorem LConst.renameData_sort_wt (f : String → LSort → String) :
    ∀ c : LConst, (c.renameData f).sort = c.sort ∧ (c.renameData f).wt = c.wt
  | .intConst _ | .strConst _ | .rationalConst _ | .bitvecConst _ _ | .boolConst _ => ⟨rfl, rfl⟩
  | .mapConst k v d ⟨es⟩ => ⟨rfl, by
    simp only [LConst.renameData, LConst.wt, (LConst.renameData_sort_wt f d).1,
      (LConst.renameData_sort_wt f d).2, LConst.renameDataEntries_wt f k v es]⟩
  | .sequenceConst a ⟨es⟩ => ⟨rfl, by
    simp only [LConst.renameData, LConst.wt, LConst.renameDataElems_wt f a es]⟩
  | .dataConst n as s ⟨es⟩ => ⟨rfl, by
    simp only [LConst.renameData, LConst.wt, LConst.renameDataElems_wtArgs f as es]⟩
/-- `LConst.renameData_sort_wt` for map entries. -/
private theorem LConst.renameDataEntries_wt (f : String → LSort → String) (k v : LSort) :
    ∀ es, LConst.wtEntries k v (LConst.renameDataEntries f es) = LConst.wtEntries k v es
  | [] => rfl
  | (a, b) :: rest => by
    simp only [LConst.renameDataEntries, LConst.wtEntries, (LConst.renameData_sort_wt f a).1,
      (LConst.renameData_sort_wt f a).2, (LConst.renameData_sort_wt f b).1,
      (LConst.renameData_sort_wt f b).2, LConst.renameDataEntries_wt f k v rest]
/-- `LConst.renameData_sort_wt` for sequence elements. -/
private theorem LConst.renameDataElems_wt (f : String → LSort → String) (s : LSort) :
    ∀ es, LConst.wtElems s (LConst.renameDataElems f es) = LConst.wtElems s es
  | [] => rfl
  | a :: rest => by
    simp only [LConst.renameDataElems, LConst.wtElems, (LConst.renameData_sort_wt f a).1,
      (LConst.renameData_sort_wt f a).2, LConst.renameDataElems_wt f s rest]
/-- `LConst.renameData_sort_wt` for the arguments of a datatype value. -/
private theorem LConst.renameDataElems_wtArgs (f : String → LSort → String) :
    ∀ (ss : List LSort) es, LConst.wtArgs ss (LConst.renameDataElems f es) = LConst.wtArgs ss es
  | [], [] | [], _ :: _ | _ :: _, [] => rfl
  | s :: ss, a :: rest => by
    simp only [LConst.renameDataElems, LConst.wtArgs, (LConst.renameData_sort_wt f a).1,
      (LConst.renameData_sort_wt f a).2, LConst.renameDataElems_wtArgs f ss rest]
end

mutual
/-- Renaming every datatype operator to itself leaves a constant unchanged. -/
private theorem LConst.renameData_id : ∀ c : LConst, c.renameData (fun n _ => n) = c
  | .intConst _ | .strConst _ | .rationalConst _ | .bitvecConst _ _ | .boolConst _ => rfl
  | .mapConst k v d ⟨es⟩ => by
    simp only [LConst.renameData, LConst.renameData_id d, LConst.renameDataEntries_id es]
  | .sequenceConst a ⟨es⟩ => by simp only [LConst.renameData, LConst.renameDataElems_id es]
  | .dataConst n as s ⟨es⟩ => by simp only [LConst.renameData, LConst.renameDataElems_id es]
/-- `LConst.renameData_id` for map entries. -/
private theorem LConst.renameDataEntries_id :
    ∀ es, LConst.renameDataEntries (fun n _ => n) es = es
  | [] => rfl
  | (a, b) :: rest => by
    simp only [LConst.renameDataEntries, LConst.renameData_id a, LConst.renameData_id b,
      LConst.renameDataEntries_id rest]
/-- `LConst.renameData_id` for lists of constants. -/
private theorem LConst.renameDataElems_id : ∀ es, LConst.renameDataElems (fun n _ => n) es = es
  | [] => rfl
  | a :: rest => by
    simp only [LConst.renameDataElems, LConst.renameData_id a, LConst.renameDataElems_id rest]
end

/-- Renaming datatype operators keeps a constant's type. -/
private theorem LConst.renameData_ty (f : String → LSort → String) (c : LConst) :
    (c.renameData f).ty = c.ty := by
  cases hw : c.wt
  · rw [LConst.ty_of_not_wt hw, LConst.ty_of_not_wt ((LConst.renameData_sort_wt f c).2.trans hw)]
  · rw [LConst.ty_of_wt hw, LConst.ty_of_wt ((LConst.renameData_sort_wt f c).2.trans hw),
      (LConst.renameData_sort_wt f c).1]

section
variable {tc : TyConstrInterp} {op op' : OpInterp tc} {f : String → LSort → String}

mutual
/-- A constant with its datatype operators renamed by `f` has under `op'` the value the constant
    has under `op`, when `op'` reads each renamed operator as `op` reads the original. -/
private theorem constVal_renameData :
    ∀ (s : LSort) (c : LConst), (∀ p ∈ c.dataOps, op' (f p.1 p.2) p.2 = op p.1 p.2) →
      constVal tc op' s (c.renameData f) = constVal tc op s c
  | _, .boolConst _, _ | _, .intConst _, _ | _, .rationalConst _, _ | _, .strConst _, _
  | _, .bitvecConst _ _, _ => by simp only [LConst.renameData]; unfold constVal; rfl
  | _, .mapConst k v d ⟨es⟩, h => by
    simp only [LConst.dataOps, List.mem_append] at h
    simp only [LConst.renameData]
    unfold constVal
    rw [constVal_renameData v d (fun p hp => h p (.inl hp)),
      constValEntries_renameData k v es (fun p hp => h p (.inr hp))]
  | _, .sequenceConst a ⟨es⟩, h => by
    simp only [LConst.renameData]
    unfold constVal
    rw [constValElems_renameData a es h]
  | _, .dataConst n as srt ⟨es⟩, h => by
    simp only [LConst.dataOps, List.mem_cons] at h
    simp only [LConst.renameData]
    unfold constVal
    rw [h _ (.inl rfl), constValArgs_renameData as es (fun p hp => h p (.inr hp))]
/-- `constVal_renameData` for map entries. -/
private theorem constValEntries_renameData : ∀ (k v : LSort) (es : List (LConst × LConst)),
    (∀ p ∈ LConst.dataOpsEntries es, op' (f p.1 p.2) p.2 = op p.1 p.2) →
    constValEntries tc op' k v (LConst.renameDataEntries f es) = constValEntries tc op k v es
  | _, _, [], _ => rfl
  | k, v, (a, b) :: r, h => by
    simp only [LConst.dataOpsEntries, List.mem_append] at h
    simp only [LConst.renameDataEntries]
    unfold constValEntries
    rw [constVal_renameData k a (fun p hp => h p (.inl (.inl hp))),
      constVal_renameData v b (fun p hp => h p (.inl (.inr hp))),
      constValEntries_renameData k v r (fun p hp => h p (.inr hp))]
/-- `constVal_renameData` for sequence elements. -/
private theorem constValElems_renameData : ∀ (a : LSort) (es : List LConst),
    (∀ p ∈ LConst.dataOpsElems es, op' (f p.1 p.2) p.2 = op p.1 p.2) →
    constValElems tc op' a (LConst.renameDataElems f es) = constValElems tc op a es
  | _, [], _ => rfl
  | a, e :: r, h => by
    simp only [LConst.dataOpsElems, List.mem_append] at h
    simp only [LConst.renameDataElems]
    unfold constValElems
    rw [constVal_renameData a e (fun p hp => h p (.inl hp)),
      constValElems_renameData a r (fun p hp => h p (.inr hp))]
/-- `constVal_renameData` for the arguments of a datatype value. -/
private theorem constValArgs_renameData : ∀ (ss : List LSort) (es : List LConst),
    (∀ p ∈ LConst.dataOpsElems es, op' (f p.1 p.2) p.2 = op p.1 p.2) →
    constValArgs tc op' ss (LConst.renameDataElems f es) = constValArgs tc op ss es
  | [], [], _ | [], _ :: _, _ | _ :: _, [], _ => by
    simp only [LConst.renameDataElems]; unfold constValArgs; rfl
  | s :: ss, e :: r, h => by
    simp only [LConst.dataOpsElems, List.mem_append] at h
    simp only [LConst.renameDataElems]
    unfold constValArgs
    rw [constVal_renameData s e (fun p hp => h p (.inl hp)),
      constValArgs_renameData ss r (fun p hp => h p (.inr hp))]
end

/-- A constant with its datatype operators renamed denotes under `op'` what the constant denotes
    under `op`, when `op'` reads each renamed operator as `op` reads the original. -/
private theorem denote_const_renameData {fv : FreeVarVal T tc} {vt : TyVarVal} {Δ : List LMonoTy}
    (bv : BVarVal tc vt Δ) {m : T.Metadata} {c : LConst} {τ : LMonoTy}
    (hd : ∀ p ∈ c.dataOps, op' (f p.1 p.2) p.2 = op p.1 p.2)
    (h : LExpr.HasTypeA Δ (.const m c : LExpr T.mono) τ)
    (h' : LExpr.HasTypeA Δ (.const m (c.renameData f) : LExpr T.mono) τ) :
    LExpr.denote tc op' fv vt bv (.const m (c.renameData f)) τ h' =
      LExpr.denote tc op fv vt bv (.const m c) τ h := by
  have key : ∀ {o : OpInterp tc} {c : LConst} (h : LExpr.HasTypeA Δ (.const m c : LExpr T.mono) τ),
      constVal tc o (τ.substTyVars vt) c = some (LExpr.denote tc o fv vt bv (.const m c) τ h) := by
    intro o c h
    cases h with
    | const hw => rw [denote_const]; exact constVal_denoteConst vt hw
  exact Option.some.inj ((key h').symm.trans ((constVal_renameData _ c hd).trans (key h)))
end

mutual
/-- A constant holding no datatype value (`LConst.hasData`) has no datatype operators. -/
theorem LConst.dataOps_eq_nil : ∀ c : LConst, c.hasData = false → c.dataOps = []
  | .intConst _, _ | .strConst _, _ | .rationalConst _, _ | .bitvecConst _ _, _
  | .boolConst _, _ => rfl
  | .mapConst _ _ d ⟨es⟩, h => by
    simp only [LConst.hasData, Bool.or_eq_false_iff] at h
    simp only [LConst.dataOps, LConst.dataOps_eq_nil d h.1, LConst.dataOpsEntries_eq_nil es h.2,
      List.append_nil]
  | .sequenceConst _ ⟨es⟩, h => by
    simp only [LConst.dataOps, LConst.dataOpsElems_eq_nil es (by simpa [LConst.hasData] using h)]
  | .dataConst .., h => by simp [LConst.hasData] at h
/-- `LConst.dataOps_eq_nil` for map entries. -/
private theorem LConst.dataOpsEntries_eq_nil :
    ∀ es, LConst.hasDataEntries es = false → LConst.dataOpsEntries es = []
  | [], _ => rfl
  | (a, b) :: rest, h => by
    simp only [LConst.hasDataEntries, Bool.or_eq_false_iff] at h
    simp only [LConst.dataOpsEntries, LConst.dataOps_eq_nil a h.1.1, LConst.dataOps_eq_nil b h.1.2,
      LConst.dataOpsEntries_eq_nil rest h.2, List.append_nil]
/-- `LConst.dataOps_eq_nil` for lists of constants. -/
private theorem LConst.dataOpsElems_eq_nil :
    ∀ es, LConst.hasDataElems es = false → LConst.dataOpsElems es = []
  | [], _ => rfl
  | a :: rest, h => by
    simp only [LConst.hasDataElems, Bool.or_eq_false_iff] at h
    simp only [LConst.dataOpsElems, LConst.dataOps_eq_nil a h.1,
      LConst.dataOpsElems_eq_nil rest h.2, List.append_nil]
end

mutual
/-- Renaming the datatype operators of a constant holding no datatype value leaves it unchanged. -/
private theorem LConst.renameData_of_hasData (f : String → LSort → String) :
    ∀ c : LConst, c.hasData = false → c.renameData f = c
  | .intConst _, _ | .strConst _, _ | .rationalConst _, _ | .bitvecConst _ _, _
  | .boolConst _, _ => rfl
  | .mapConst k v d ⟨es⟩, h => by
    simp only [LConst.hasData, Bool.or_eq_false_iff] at h
    simp only [LConst.renameData, LConst.renameData_of_hasData f d h.1,
      LConst.renameDataEntries_of_hasData f es h.2]
  | .sequenceConst a ⟨es⟩, h => by
    simp only [LConst.renameData,
      LConst.renameDataElems_of_hasData f es (by simpa [LConst.hasData] using h)]
  | .dataConst .., h => by simp [LConst.hasData] at h
/-- `LConst.renameData_of_hasData` for map entries. -/
private theorem LConst.renameDataEntries_of_hasData (f : String → LSort → String) :
    ∀ es, LConst.hasDataEntries es = false → LConst.renameDataEntries f es = es
  | [], _ => rfl
  | (a, b) :: rest, h => by
    simp only [LConst.hasDataEntries, Bool.or_eq_false_iff] at h
    simp only [LConst.renameDataEntries, LConst.renameData_of_hasData f a h.1.1,
      LConst.renameData_of_hasData f b h.1.2, LConst.renameDataEntries_of_hasData f rest h.2]
/-- `LConst.renameData_of_hasData` for lists of constants. -/
private theorem LConst.renameDataElems_of_hasData (f : String → LSort → String) :
    ∀ es, LConst.hasDataElems es = false → LConst.renameDataElems f es = es
  | [], _ => rfl
  | a :: rest, h => by
    simp only [LConst.hasDataElems, Bool.or_eq_false_iff] at h
    simp only [LConst.renameDataElems, LConst.renameData_of_hasData f a h.1,
      LConst.renameDataElems_of_hasData f rest h.2]
end

/-- Rename every operator `o` annotated `ty` to `g o ty`, keeping metadata, annotations and
    constants. -/
@[expose] def LExpr.renameOpNodes
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) :
    LExpr T.mono → LExpr T.mono
  | .const m c => .const m c
  | .op m o ty => .op m (g o ty) ty
  | .bvar m i => .bvar m i
  | .fvar m x ty => .fvar m x ty
  | .abs m n ty e => .abs m n ty (renameOpNodes g e)
  | .quant m k n ty tr e => .quant m k n ty (renameOpNodes g tr) (renameOpNodes g e)
  | .app m f a => .app m (renameOpNodes g f) (renameOpNodes g a)
  | .ite m c t e => .ite m (renameOpNodes g c) (renameOpNodes g t) (renameOpNodes g e)
  | .eq m a b => .eq m (renameOpNodes g a) (renameOpNodes g b)

variable [Inhabited T.IDMeta]

/-- The name `g` renames the operator `n` of a datatype value of sort `srt` to: the name of `g`
    applied to `n` at the type naming `srt`. -/
@[expose] def dataRen
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) (n : String) (srt : LSort) :
    String :=
  (g ⟨n, default⟩ (some srt.toMonoTy)).name

/-- Rename every operator `o` annotated `ty` to `g o ty`, keeping metadata and
    annotations, and the operator of every datatype value inside a constant by `dataRen g`. -/
@[expose] def LExpr.renameOps
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) :
    LExpr T.mono → LExpr T.mono
  | .const m c => .const m (c.renameData (dataRen g))
  | .op m o ty => .op m (g o ty) ty
  | .bvar m i => .bvar m i
  | .fvar m x ty => .fvar m x ty
  | .abs m n ty e => .abs m n ty (renameOps g e)
  | .quant m k n ty tr e => .quant m k n ty (renameOps g tr) (renameOps g e)
  | .app m f a => .app m (renameOps g f) (renameOps g a)
  | .ite m c t e => .ite m (renameOps g c) (renameOps g t) (renameOps g e)
  | .eq m a b => .eq m (renameOps g a) (renameOps g b)

/-- On an expression none of whose constants holds a datatype value (`LConst.hasData`),
    renaming the operator nodes is renaming every operator. -/
theorem LExpr.renameOpNodes_eq_renameOps
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) (e : LExpr T.mono)
    (h : ∀ c ∈ e.getConsts, c.hasData = false) : e.renameOpNodes g = e.renameOps g := by
  induction e <;> simp_all [LExpr.renameOpNodes, LExpr.renameOps, LExpr.getConsts,
    LConst.renameData_of_hasData]

/-- Renaming operators does not change the result of type checking. -/
theorem LExpr.typeCheck_renameOps
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta)
    (Δ : List LMonoTy) (e : LExpr T.mono) :
    LExpr.typeCheck Δ (e.renameOps g) = LExpr.typeCheck Δ e := by
  induction e generalizing Δ with
  | const _ c =>
    simp only [LExpr.renameOps, LExpr.typeCheck, (LConst.renameData_sort_wt (dataRen g) c).2,
      LConst.renameData_ty]
  | bvar | fvar => rfl
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
    `op'`, when `op'` reads each renamed operator of `e` as `op` reads it, and each operator of a
    datatype value in a constant (`LConst.dataOps`), renamed by `dataRen g`, as `op` reads it. -/
private theorem Denotes.renameOps {tc : TyConstrInterp} {op op' : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal}
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta)
    {Δ : List LMonoTy} {bv : BVarVal tc vt Δ} {e : LExpr T.mono} {τ : LMonoTy}
    {h : e.HasTypeA Δ τ} {v : TyDenote tc vt τ}
    (hd : Denotes tc op fv vt bv e τ h v) (hops : LExpr.OpsReadAs op op' g e)
    (hdata : ∀ c ∈ e.getConsts, ∀ p ∈ c.dataOps, op' (dataRen g p.1 p.2) p.2 = op p.1 p.2) :
    Denotes tc op' fv vt bv (e.renameOps g) τ (LExpr.HasTypeA_renameOps g h) v := by
  induction hd with
  | const =>
    rename_i bv' m c hc
    have hr := denote_Denotes tc op' fv vt bv' (.const m (c.renameData (dataRen g))) c.ty
      (LExpr.HasTypeA_renameOps g hc)
    have e := denote_const_renameData (fv := fv) bv' (hdata c (List.mem_singleton_self c)) hc
      (LExpr.HasTypeA_renameOps g hc)
    rw [e] at hr
    exact hr
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
      hp)) (fun c hc => hdata c (by simpa [LExpr.getConsts] using hc)))
  | app _ _ _ ih1 ih2 =>
    exact .app _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
  | ite_true _ _ _ ih1 ih2 =>
    exact .ite_true _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
  | ite_false _ _ _ ih1 ih2 =>
    exact .ite_false _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
  | eq_true _ _ _ ih1 ih2 =>
    exact .eq_true _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
  | eq_false _ _ _ hne ih1 ih2 =>
    exact .eq_false _ (ih1 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
      (ih2 (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc]))) hne
  | quant_all_true _ _ ih =>
    exact .quant_all_true _ (fun x => ih x (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
  | quant_all_false _ w _ ih =>
    exact .quant_all_false _ w (ih (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
  | quant_exist_true _ w _ ih =>
    exact .quant_exist_true _ w (ih (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))
  | quant_exist_false _ _ ih =>
    exact .quant_exist_false _ (fun x => ih x (fun p hp => hops p (by simp [LExpr.opAnnots, hp]))
      (fun c hc => hdata c (by simp [LExpr.getConsts, hc])))

/-- **Renaming law for denotation.** A renamed expression denotes under `op'` what the
    original denotes under `op`, when `op'` reads each renamed operator as `op` reads the
    original, and each operator of a datatype value in a constant (`LConst.dataOps`) as `op`
    reads it. -/
theorem denote_renameOps {tc : TyConstrInterp} {op op' : OpInterp tc} {fv : FreeVarVal T tc}
    {vt : TyVarVal} (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta)
    {Δ : List LMonoTy} (bv : BVarVal tc vt Δ) {e : LExpr T.mono} {τ : LMonoTy}
    (h : e.HasTypeA Δ τ) (h' : (e.renameOps g).HasTypeA Δ τ)
    (hops : LExpr.OpsReadAs op op' g e)
    (hdata : ∀ c ∈ e.getConsts, ∀ p ∈ c.dataOps, op' (dataRen g p.1 p.2) p.2 = op p.1 p.2) :
    LExpr.denote tc op' fv vt bv (e.renameOps g) τ h' = LExpr.denote tc op fv vt bv e τ h :=
  (Denotes_denote (Denotes.renameOps g (denote_Denotes _ _ _ _ bv e τ h) hops hdata)).symm

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

omit [Inhabited T.IDMeta] in
/-- Annotating free variables keeps the annotated operators. -/
private theorem LExpr.opAnnots_annotateFvars (ann : Identifier T.IDMeta → Option LMonoTy)
    (e : LExpr T.mono) : (e.annotateFvars ann).opAnnots = e.opAnnots := by
  induction e <;> simp_all [LExpr.annotateFvars, LExpr.opAnnots]

omit [Inhabited T.IDMeta] in
/-- Annotating free variables keeps the constants. -/
private theorem LExpr.getConsts_annotateFvars (ann : Identifier T.IDMeta → Option LMonoTy)
    (e : LExpr T.mono) : (e.annotateFvars ann).getConsts = e.getConsts := by
  induction e <;> simp_all [LExpr.annotateFvars, LExpr.getConsts]

omit [Inhabited T.IDMeta] in
/-- Denotations of two equal expressions are heterogeneously equal, whatever their typing
    derivations. -/
private theorem denote_heq_of_eq' {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal} {e₁ e₂ : LExpr T.mono} {τ : LMonoTy} (he : e₁ = e₂)
    (h₁ : e₁.HasTypeA [] τ) (h₂ : e₂.HasTypeA [] τ) :
    HEq (LExpr.denote tc op fv vt .nil e₁ τ h₁) (LExpr.denote tc op fv vt .nil e₂ τ h₂) := by
  subst he; rfl

/-- **Renaming law for evaluation.** Evaluating a renamed expression in a model `M'` that
    shares `M`'s carriers and type-variable sorts, and reads each renamed operator as `M`
    reads the original and each operator of a datatype value in a constant as `M` reads it,
    gives what evaluating the original in `M` gives. -/
theorem LExpr.denoteEval_renameOps [DecidableEq T.IDMeta] {M M' : ModeledFactory T}
    (g : Identifier T.IDMeta → Option LMonoTy → Identifier T.IDMeta) (σ : ValStore T)
    (e : LExpr T.mono)
    (htc : M'.model.tcInterp = M.model.tcInterp)
    (hinh : HEq M'.model.allInhabited M.model.allInhabited)
    (htv : M'.tyVarVal = M.tyVarVal)
    (hops : ∀ p ∈ e.opAnnots,
      HEq (M'.model.opInterp (g p.1 (some p.2)).name) (M.model.opInterp p.1.name))
    (hdata : ∀ c ∈ e.getConsts, ∀ p ∈ c.dataOps,
      HEq (M'.model.opInterp (dataRen g p.1 p.2) p.2) (M.model.opInterp p.1 p.2)) :
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
  have hdata' : ∀ c ∈ (e.annotateFvars σ.ann).getConsts, ∀ p ∈ c.dataOps,
      op' (dataRen g p.1 p.2) p.2 = op p.1 p.2 := fun c hc p hp =>
    eq_of_heq (hdata c (LExpr.getConsts_annotateFvars σ.ann e ▸ hc) p hp)
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
    rw [denote_renameOps g .nil hτ' _ hops' hdata']
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hτ' : ((e.renameOps g).annotateFvars σ.ann).HasTypeA [] τ :=
      hann ▸ LExpr.HasTypeA_renameOps g hτ
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    refine eq_of_heq (HEq.symm ((denote_heq_of_eq' hann hτ' (LExpr.HasTypeA_renameOps g hτ)).trans
        ?_))
    rw [denote_renameOps g .nil hτ _ hops' hdata']

end Lambda

end -- public section

namespace Lambda

/-- **An operator annotated with an instance of its function's signature is
    `OpsConsistent`**, for a function whose input and output types mention
    only its type parameters. -/
theorem opsConsistent_op_of_instance {T : LExprParams} {F : Factory T}
    {m : T.mono.base.Metadata}
    {o : T.Identifier} {ty : LMonoTy} {fn : LFunc T} (hfn : F[o.name]? = some fn)
    (hins : ∀ t, t ∈ fn.inputs.values → t.freeVars ⊆ fn.typeArgs)
    (hout : fn.output.freeVars ⊆ fn.typeArgs)
    (hinst : ∃ σ : Subst, ty = LMonoTy.subst σ (LMonoTy.mkArrow' fn.output (fn.inputs.map
        Prod.snd))) :
    OpsConsistent F (.op m o (some ty)) := by
  obtain ⟨σ, hσ⟩ := hinst
  have hv : fn.inputs.values = fn.inputs.map Prod.snd :=
    ListMap.values_eq_map_snd _
  have hinsv : ∀ t ∈ fn.inputs.map Prod.snd, ∀ v ∈ t.freeVars,
      v ∈ fn.typeArgs := by
    intro t ht v hvt
    rw [← hv] at ht
    exact hins t ht hvt
  have hdecl : (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).freeVars
      ⊆ fn.typeArgs :=
    freeVars_mkArrow'_subset fn.output _ fn.typeArgs hout hinsv
  unfold OpsConsistent
  rw [hfn]
  simp only
  by_cases hpoly : fn.typeArgs = []
  · have hts : LFunc.opTypeSubst fn (.op m o (some ty)) = some Subst.empty := by
      unfold LFunc.opTypeSubst
      simp only [hpoly, List.isEmpty_nil, ↓reduceIte]
    rw [hts, hσ]
    apply agree_on_freeVars_implies_subst_eq
    intro v hvd
    have hvargs : v ∈ fn.typeArgs := hdecl hvd
    rw [hpoly] at hvargs
    cases hvargs
  · have hempty : ∀ a t, (Strata.Util.HMap.empty : SubstOne).find? a = some t →
        t = LMonoTy.subst σ (.ftvar a) := by
      intro a t h
      rw [Strata.Util.HMap.find?_empty] at h
      cases h
    obtain ⟨si, hm, -, -, hbound⟩ :=
      LMonoTy.matchTy?_subst_complete fn.typeArgs σ _ hdecl _ hempty
    have hts : LFunc.opTypeSubst fn (.op m o (some ty)) =
        some (fn.instanceSubst si) := by
      have hmv : LMonoTy.matchTy? fn.typeArgs Strata.Util.HMap.empty
          (LMonoTy.mkArrow' fn.output fn.inputs.values) ty = some si := by
        rw [hv, hσ]
        exact hm
      unfold LFunc.opTypeSubst LFuncDefined.opInstance?
      simp only [List.isEmpty_iff, hpoly, ↓reduceIte, Option.bind_eq_bind,
        Option.bind_some, hmv, Option.map_some]
    rw [hts, hσ]
    apply agree_on_freeVars_implies_subst_eq
    intro v hvd
    have hfind :
        (SubstOne.completeParams fn.typeArgs callTyVarPrefix si).find? v =
          some (LMonoTy.subst σ (.ftvar v)) :=
      SubstOne.completeParams_find?_of_find? _ _ _ _ _ (hbound v hvd)
    rw [LMonoTy.subst_unfold (LFunc.instanceSubst fn si)]
    simp only [LFunc.instanceSubst, Strata.Util.HMaps.find?_single_scope, hfind]

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

/-- Renaming every operator to itself leaves an expression unchanged. -/
theorem LExpr.renameOps_id {T : LExprParams} [Inhabited T.IDMeta] :
    ∀ e : LExpr T.mono, e.renameOps (fun o _ => o) = e := by
  intro e
  induction e with
  | const m c => exact congrArg (LExpr.const m) (LConst.renameData_id c)
  | _ => simp_all [LExpr.renameOps]

end Lambda
