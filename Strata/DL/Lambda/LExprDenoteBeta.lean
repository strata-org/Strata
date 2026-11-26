/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.LExprTypedBeta
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.Denote.LExprDenoteSubst
import Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprWFProps
import Strata.Util.HListProps

/-! # Beta reduction keeps the denotation

Substituting, for a bound variable of an expression, expressions that denote a value `val`
gives an expression with the denotation of the original one under `val` for the bound variable
(`denote_betaReduceK`), so contracting a redex keeps the denotation, and so does contracting
the redexes of an expression at any fuel (`denote_betaReduceRedexesFuel`).  Annotating the free
variables commutes with the contraction (`annotateFvars_betaReduceRedexesFuel`), and the
contraction adds no free variable, so an expression that evaluates keeps its value under the
contraction of its redexes (`LExpr.denoteEval_betaReduceRedexesFuel`,
`LExpr.denoteEval_betaReduceRedexesWith`).  The converse fails: `(λ x : int. 5) true` has no
value, and its contraction `5` has one.

Key theorems: `Lambda.LExpr.denoteEval_betaReduceRedexesWith`. -/

public section

namespace Lambda

variable {T : LExprParams}

/-- Inserting an element in an `HList` after its prefix `hxs` moves every element of the suffix
    one position on. -/
private theorem HList.get_append_insert {α : Type} {f : α → Type} {xs ys : List α} {a b : α}
    (hxs : HList f xs) (v : f b) (hys : HList f ys) :
    ∀ (j : Nat) (h : (xs ++ ys)[j]? = some a) (h' : (xs ++ b :: ys)[j + 1]? = some a),
      xs.length ≤ j → (hxs.append hys).get j h = (hxs.append (.cons v hys)).get (j + 1) h' := by
  induction hxs with
  | nil => intro j h h' _; simp [HList.append]
  | cons x xs ih =>
    intro j h h' hj
    cases j with
    | zero => simp at hj
    | succ j => exact ih j (by simpa using h) (by simpa using h') (by simpa using hj)


/-! ## Contracting the redexes -/

section Fuel

variable {T : LExprParamsT}
  (merge : T.base.Metadata → T.base.Metadata → T.base.Metadata → T.base.Metadata)

/-- The contraction of the redexes of an application: the application of the contractions of its
    parts, or, when the contraction of the function is an abstraction, the contraction of the
    substitution of the contracted argument into its body. -/
private theorem LExpr.betaReduceRedexesFuel_app (fuel : Nat) (m : T.base.Metadata)
    (fn arg : LExpr T) :
    LExpr.betaReduceRedexesFuel merge false (fuel + 1) (.app m fn arg) =
      match LExpr.betaReduceRedexesFuel merge false fuel fn with
      | .abs mAbs _ _ body => LExpr.betaReduceRedexesFuel merge false fuel
          (LExpr.betaReduceWith (fun mVar => LExpr.replaceMetadata1
            (merge mAbs (LExpr.betaReduceRedexesFuel merge false fuel arg).metadata mVar)
            (LExpr.betaReduceRedexesFuel merge false fuel arg)) body)
      | fn' => .app m fn' (LExpr.betaReduceRedexesFuel merge false fuel arg) := by
  simp only [LExpr.betaReduceRedexesFuel, LExpr.betaReduceRedexesFuel?]
  cases hf : LExpr.betaReduceRedexesFuel? merge false fuel fn <;>
    cases ha : LExpr.betaReduceRedexesFuel? merge false fuel arg <;>
    simp only [Option.getD_none, Option.getD_some, Option.isNone_none, Option.isNone_some] <;>
    split <;> simp_all

/-- The contraction of the redexes of an abstraction is the abstraction of the contraction of
    its body. -/
private theorem LExpr.betaReduceRedexesFuel_abs (fuel : Nat) (m : T.base.Metadata) (n : String)
    (ty : Option T.TypeType) (b : LExpr T) :
    LExpr.betaReduceRedexesFuel merge false (fuel + 1) (.abs m n ty b) =
      .abs m n ty (LExpr.betaReduceRedexesFuel merge false fuel b) := by
  simp only [LExpr.betaReduceRedexesFuel, LExpr.betaReduceRedexesFuel?]
  cases LExpr.betaReduceRedexesFuel? merge false fuel b <;> rfl

/-- The contraction of the redexes of a quantifier is the quantifier of the contractions of its
    trigger and body. -/
private theorem LExpr.betaReduceRedexesFuel_quant (fuel : Nat) (m : T.base.Metadata)
    (k : QuantifierKind) (n : String) (ty : Option T.TypeType) (tr b : LExpr T) :
    LExpr.betaReduceRedexesFuel merge false (fuel + 1) (.quant m k n ty tr b) =
      .quant m k n ty (LExpr.betaReduceRedexesFuel merge false fuel tr)
        (LExpr.betaReduceRedexesFuel merge false fuel b) := by
  simp only [LExpr.betaReduceRedexesFuel, LExpr.betaReduceRedexesFuel?]
  cases LExpr.betaReduceRedexesFuel? merge false fuel tr <;>
    cases LExpr.betaReduceRedexesFuel? merge false fuel b <;> rfl

/-- The contraction of the redexes of a conditional is the conditional of the contractions of
    its parts. -/
private theorem LExpr.betaReduceRedexesFuel_ite (fuel : Nat) (m : T.base.Metadata)
    (c t f : LExpr T) :
    LExpr.betaReduceRedexesFuel merge false (fuel + 1) (.ite m c t f) =
      .ite m (LExpr.betaReduceRedexesFuel merge false fuel c)
        (LExpr.betaReduceRedexesFuel merge false fuel t)
        (LExpr.betaReduceRedexesFuel merge false fuel f) := by
  simp only [LExpr.betaReduceRedexesFuel, LExpr.betaReduceRedexesFuel?]
  cases LExpr.betaReduceRedexesFuel? merge false fuel c <;>
    cases LExpr.betaReduceRedexesFuel? merge false fuel t <;>
    cases LExpr.betaReduceRedexesFuel? merge false fuel f <;> rfl

/-- The contraction of the redexes of an equality is the equality of the contractions of its
    sides. -/
private theorem LExpr.betaReduceRedexesFuel_eq (fuel : Nat) (m : T.base.Metadata) (a b : LExpr T) :
    LExpr.betaReduceRedexesFuel merge false (fuel + 1) (.eq m a b) =
      .eq m (LExpr.betaReduceRedexesFuel merge false fuel a)
        (LExpr.betaReduceRedexesFuel merge false fuel b) := by
  simp only [LExpr.betaReduceRedexesFuel, LExpr.betaReduceRedexesFuel?]
  cases LExpr.betaReduceRedexesFuel? merge false fuel a <;>
    cases LExpr.betaReduceRedexesFuel? merge false fuel b <;> rfl

end Fuel

variable (tc : TyConstrInterp) (op : OpInterp tc) (fv : FreeVarVal T tc) (vt : TyVarVal)

/-- **Substituting for a bound variable keeps the denotation.**  When every `s m` has the type
    `aty` in the context `Δ` and denotes `val` there, replacing the bound variable of index
    `Δa.length` of an expression of the context `Δa ++ aty :: Δ` by `s m` (lifted past `Δa`)
    gives an expression whose denotation is that of the original one with `val` for that bound
    variable. -/
private theorem denote_betaReduceK {s : T.mono.base.Metadata → LExpr T.mono} {aty : LMonoTy}
    {Δ : List LMonoTy} (bvΔ : BVarVal tc vt Δ) {val : TyDenote tc vt aty}
    (ha : ∀ m, (s m).HasTypeA Δ aty)
    (hval : ∀ m, LExpr.denote tc op fv vt bvΔ (s m) aty (ha m) = val) (e : LExpr T.mono) :
    ∀ {Δa : List LMonoTy} (bva : BVarVal tc vt Δa) {τ : LMonoTy}
      (he : e.HasTypeA (Δa ++ aty :: Δ) τ)
      (hr : (LExpr.betaReduceK Δa.length s e).HasTypeA (Δa ++ Δ) τ),
      LExpr.denote tc op fv vt (bva.append bvΔ) (LExpr.betaReduceK Δa.length s e) τ hr =
        LExpr.denote tc op fv vt (bva.append (.cons val bvΔ)) e τ he := by
  induction e with
  | const m c =>
    intro Δa bva τ he hr
    cases HasTypeA.const_inv he
    exact (Denotes_denote (Denotes.const _)).symm.trans (Denotes_denote (Denotes.const _))
  | op m o ty =>
    intro Δa bva τ he hr
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck he) (by simp [LExpr.typeCheck])
    | some ty =>
      cases HasTypeA.op_inv he
      exact (Denotes_denote (Denotes.op _)).symm.trans (Denotes_denote (Denotes.op _))
  | fvar m x ty =>
    intro Δa bva τ he hr
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck he) (by simp [LExpr.typeCheck])
    | some ty =>
      cases HasTypeA.fvar_inv he
      exact (Denotes_denote (Denotes.fvar _)).symm.trans (Denotes_denote (Denotes.fvar _))
  | bvar m i =>
    intro Δa bva τ he hr
    have hi := HasTypeA.bvar_inv he
    rw [denote_bvar]
    by_cases hik : i = Δa.length
    · subst hik
      have hτ : τ = aty := by simpa using hi.symm
      subst hτ
      simp only [LExpr.betaReduceK, BEq.rfl, ↓reduceIte] at hr ⊢
      rw [HList.get_append_cons_self]
      have hl := liftBVars_denote tc op fv vt (Δ₁ := []) (Δ_insert := Δa) (Δ_outer := Δ)
        (ha m) hr .nil bva bvΔ
      exact hl.trans (hval m)
    · by_cases hgt : i > Δa.length
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp only [LExpr.betaReduceK, show (j + 1 == Δa.length) = false by simpa using hik, hgt,
          Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel] at hr ⊢
        rw [denote_bvar]
        exact HList.get_append_insert bva val bvΔ j _ hi (by omega)
      · simp only [LExpr.betaReduceK, show (i == Δa.length) = false by simpa using hik, hgt,
          Bool.false_eq_true, ↓reduceIte] at hr ⊢
        rw [denote_bvar]
        have hlt : i < Δa.length := by omega
        rw [HList.get_append_left _ _ _ _ (by simpa [List.getElem?_append_left hlt] using hi),
          HList.get_append_left _ _ _ _ (by simpa [List.getElem?_append_left hlt] using hi)]
  | abs m n ty b ih =>
    intro Δa bva τ he hr
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck he) (by simp [LExpr.typeCheck])
    | some aty' =>
      obtain ⟨rty, rfl, hb⟩ := HasTypeA.abs_inv he
      have hb' : (LExpr.betaReduceK (Δa.length + 1) s b).HasTypeA (aty' :: Δa ++ Δ) rty :=
        LExpr.HasTypeA_betaReduceK ha hb (aty' :: Δa) rfl
      simp only [LExpr.betaReduceK] at hr ⊢
      rw [denote_abs _ hb' hr, denote_abs _ hb he]
      funext x
      exact ih (Δa := aty' :: Δa) (.cons x bva) hb hb'
  | quant m k n ty tr b ihtr ihb =>
    intro Δa bva τ he hr
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck he) (by simp [LExpr.typeCheck])
    | some qty =>
      obtain ⟨_, rfl, htr, hb⟩ := HasTypeA.quant_inv he
      have hb' : (LExpr.betaReduceK (Δa.length + 1) s b).HasTypeA (qty :: Δa ++ Δ) .bool :=
        LExpr.HasTypeA_betaReduceK ha hb (qty :: Δa) rfl
      simp only [LExpr.betaReduceK] at hr ⊢
      exact denote_quant_congr hb' hb hr he fun x => ihb (Δa := qty :: Δa) (.cons x bva) hb hb'
  | app m f a ihf iha =>
    intro Δa bva τ he hr
    obtain ⟨aty', hf, ha'⟩ := HasTypeA.app_inv he
    have hf' := LExpr.HasTypeA_betaReduceK ha hf Δa rfl
    have ha'' := LExpr.HasTypeA_betaReduceK ha ha' Δa rfl
    simp only [LExpr.betaReduceK] at hr ⊢
    rw [denote_app _ hf' ha'' hr, denote_app _ hf ha' he, ihf bva hf hf', iha bva ha' ha'']
  | ite m c t f ihc iht ihf =>
    intro Δa bva τ he hr
    obtain ⟨hc, ht, hf⟩ := HasTypeA.ite_inv he
    have hc' := LExpr.HasTypeA_betaReduceK ha hc Δa rfl
    have ht' := LExpr.HasTypeA_betaReduceK ha ht Δa rfl
    have hf' := LExpr.HasTypeA_betaReduceK ha hf Δa rfl
    simp only [LExpr.betaReduceK] at hr ⊢
    rw [denote_ite _ hc' ht' hf' hr, denote_ite _ hc ht hf he, ihc bva hc hc', iht bva ht ht',
      ihf bva hf hf']
  | eq m a b iha ihb =>
    intro Δa bva τ he hr
    obtain ⟨ty, rfl, ha', hb⟩ := HasTypeA.eq_inv he
    have ha'' := LExpr.HasTypeA_betaReduceK ha ha' Δa rfl
    have hb' := LExpr.HasTypeA_betaReduceK ha hb Δa rfl
    simp only [LExpr.betaReduceK] at hr ⊢
    by_cases heq : LExpr.denote tc op fv vt (bva.append (.cons val bvΔ)) a ty ha' =
        LExpr.denote tc op fv vt (bva.append (.cons val bvΔ)) b ty hb
    · rw [denote_eq_true _ ha'' hb' hr (by rw [iha bva ha' ha'', ihb bva hb hb']; exact heq),
        denote_eq_true _ ha' hb he heq]
    · rw [denote_eq_false _ ha'' hb' hr (by rw [iha bva ha' ha'', ihb bva hb hb']; exact heq),
        denote_eq_false _ ha' hb he heq]


/-- Equal expressions have equal denotations. -/
private theorem denote_eqE {Δ : List LMonoTy} (bv : BVarVal tc vt Δ) {e₁ e₂ : LExpr T.mono}
    {τ : LMonoTy} (he : e₁ = e₂) (h₁ : e₁.HasTypeA Δ τ) (h₂ : e₂.HasTypeA Δ τ) :
    LExpr.denote tc op fv vt bv e₁ τ h₁ = LExpr.denote tc op fv vt bv e₂ τ h₂ := by
  subst he
  rfl

/-- **Contracting the redexes keeps the denotation**, at any fuel and in any context of bound
    variables. -/
theorem denote_betaReduceRedexesFuel
    (merge : T.mono.base.Metadata → T.mono.base.Metadata → T.mono.base.Metadata →
      T.mono.base.Metadata) (fuel : Nat) :
    ∀ {Δ : List LMonoTy} (bv : BVarVal tc vt Δ) (e : LExpr T.mono) {τ : LMonoTy}
      (h : e.HasTypeA Δ τ) (h' : (LExpr.betaReduceRedexesFuel merge false fuel e).HasTypeA Δ τ),
      LExpr.denote tc op fv vt bv (LExpr.betaReduceRedexesFuel merge false fuel e) τ h' =
        LExpr.denote tc op fv vt bv e τ h := by
  induction fuel with
  | zero => intro Δ bv e τ h h'; rfl
  | succ fuel ih =>
    have hT := @LExpr.HasTypeA_betaReduceRedexesFuel T merge false fuel
    intro Δ bv e τ h h'
    cases e with
    | const | op | bvar | fvar => rfl
    | abs m n ty b =>
      cases ty with
      | none => exact absurd (LExpr.HasTypeA_to_typeCheck h) (by simp [LExpr.typeCheck])
      | some aty =>
        obtain ⟨rty, rfl, hb⟩ := HasTypeA.abs_inv h
        rw [denote_eqE tc op fv vt bv (LExpr.betaReduceRedexesFuel_abs merge fuel m n _ b) h'
          (.abs (hT hb)), denote_abs _ (hT hb), denote_abs _ hb]
        funext x
        exact ih _ b hb (hT hb)
    | quant m k n ty tr b =>
      cases ty with
      | none => exact absurd (LExpr.HasTypeA_to_typeCheck h) (by simp [LExpr.typeCheck])
      | some qty =>
        obtain ⟨_, rfl, htr, hb⟩ := HasTypeA.quant_inv h
        rw [denote_eqE tc op fv vt bv (LExpr.betaReduceRedexesFuel_quant merge fuel m k n _ tr b)
          h' (.quant (hT htr) (hT hb))]
        exact denote_quant_congr (hT hb) hb _ h fun x => ih _ b hb (hT hb)
    | ite m c t f =>
      obtain ⟨hc, ht, hf⟩ := HasTypeA.ite_inv h
      rw [denote_eqE tc op fv vt bv (LExpr.betaReduceRedexesFuel_ite merge fuel m c t f) h'
        (.ite (hT hc) (hT ht) (hT hf)), denote_ite _ (hT hc) (hT ht) (hT hf),
        denote_ite _ hc ht hf h, ih _ c hc, ih _ t ht, ih _ f hf]
    | eq m a b =>
      obtain ⟨ty, rfl, ha, hb⟩ := HasTypeA.eq_inv h
      rw [denote_eqE tc op fv vt bv (LExpr.betaReduceRedexesFuel_eq merge fuel m a b) h'
        (.eq (hT ha) (hT hb))]
      by_cases heq : LExpr.denote tc op fv vt bv a ty ha = LExpr.denote tc op fv vt bv b ty hb
      · rw [denote_eq_true _ (hT ha) (hT hb) _ (by rw [ih _ a ha, ih _ b hb]; exact heq),
          denote_eq_true _ ha hb h heq]
      · rw [denote_eq_false _ (hT ha) (hT hb) _ (by rw [ih _ a ha, ih _ b hb]; exact heq),
          denote_eq_false _ ha hb h heq]
    | app m fn arg =>
      obtain ⟨aty, hf, ha⟩ := HasTypeA.app_inv h
      have hf' := hT hf
      have ha' := hT ha
      rw [denote_app _ hf ha h, ← ih _ fn hf hf', ← ih _ arg ha ha']
      have hk := LExpr.betaReduceRedexesFuel_app merge fuel m fn arg
      generalize LExpr.betaReduceRedexesFuel merge false fuel fn = fn' at hf' hk
      cases fn' with
      | abs mAbs n ty body =>
        cases ty with
        | none => exact absurd (LExpr.HasTypeA_to_typeCheck hf') (by simp [LExpr.typeCheck])
        | some aty' =>
          obtain ⟨rty, he, hb⟩ := HasTypeA.abs_inv hf'
          cases he
          have hs := fun mVar => LExpr.HasTypeA_replaceMetadata1 (merge mAbs
            (LExpr.betaReduceRedexesFuel merge false fuel arg).metadata mVar) ha'
          have hc := LExpr.HasTypeA_betaReduceK hs hb [] rfl
          rw [denote_eqE tc op fv vt bv (e₂ := LExpr.betaReduceRedexesFuel merge false fuel
            (LExpr.betaReduceK [].length _ body)) hk h' (hT hc), ih _ _ hc (hT hc),
            denote_abs _ hb hf']
          exact denote_betaReduceK tc op fv vt bv hs
            (fun mVar => denote_replaceMetadata1 _ _ _ _ bv _ _) body .nil hb hc
      | _ =>
        rw [denote_eqE tc op fv vt bv (e₂ := .app m _ _) hk h' (.app hf' ha'),
          denote_app _ hf' ha']


/-! ## Annotating the free variables commutes with the contraction -/

section Annotate

variable {T : LExprParams} (ann : Identifier T.IDMeta → Option LMonoTy)

/-- Annotating the free variables keeps the root metadata. -/
private theorem metadata_annotateFvars (e : LExpr T.mono) :
    (e.annotateFvars ann).metadata = e.metadata := by
  cases e <;> rfl

/-- Annotating the free variables commutes with replacing the root metadata. -/
private theorem annotateFvars_replaceMetadata1 (r : T.mono.base.Metadata) (e : LExpr T.mono) :
    (LExpr.replaceMetadata1 r e).annotateFvars ann =
      LExpr.replaceMetadata1 r (e.annotateFvars ann) := by
  cases e <;> rfl

/-- Annotating the free variables commutes with lifting the bound variables. -/
private theorem annotateFvars_liftBVars (n : Nat) :
    ∀ (e : LExpr T.mono) (c : Nat),
      (LExpr.liftBVars n e c).annotateFvars ann = LExpr.liftBVars n (e.annotateFvars ann) c := by
  intro e
  induction e <;> intro c <;> simp_all [LExpr.liftBVars, LExpr.annotateFvars] <;> split <;> rfl

/-- Annotating the free variables commutes with substituting for a bound variable. -/
private theorem annotateFvars_betaReduceK (s : T.mono.base.Metadata → LExpr T.mono) :
    ∀ (e : LExpr T.mono) (k : Nat),
      (LExpr.betaReduceK k s e).annotateFvars ann =
        LExpr.betaReduceK k (fun m => (s m).annotateFvars ann) (e.annotateFvars ann) := by
  intro e
  induction e with
  | bvar m i =>
    intro k
    simp only [LExpr.betaReduceK, LExpr.annotateFvars]
    split
    · exact annotateFvars_liftBVars ann k _ 0
    · split <;> rfl
  | _ => intro k; simp_all [LExpr.betaReduceK, LExpr.annotateFvars]

/-- **Annotating the free variables commutes with contracting the redexes**, at any fuel. -/
private theorem annotateFvars_betaReduceRedexesFuel
    (merge : T.mono.base.Metadata → T.mono.base.Metadata → T.mono.base.Metadata →
      T.mono.base.Metadata) (fuel : Nat) :
    ∀ e : LExpr T.mono, (LExpr.betaReduceRedexesFuel merge false fuel e).annotateFvars ann =
      LExpr.betaReduceRedexesFuel merge false fuel (e.annotateFvars ann) := by
  induction fuel with
  | zero => intro e; rfl
  | succ fuel ih =>
    intro e
    cases e with
    | const | op | bvar | fvar => rfl
    | abs m n ty b =>
      simp only [LExpr.annotateFvars, LExpr.betaReduceRedexesFuel_abs, ih]
    | quant m k n ty tr b =>
      simp only [LExpr.annotateFvars, LExpr.betaReduceRedexesFuel_quant, ih]
    | ite m c t f =>
      simp only [LExpr.annotateFvars, LExpr.betaReduceRedexesFuel_ite, ih]
    | eq m a b =>
      simp only [LExpr.annotateFvars, LExpr.betaReduceRedexesFuel_eq, ih]
    | app m fn arg =>
      simp only [LExpr.annotateFvars, LExpr.betaReduceRedexesFuel_app, ← ih]
      cases LExpr.betaReduceRedexesFuel merge false fuel fn <;>
        simp only [LExpr.annotateFvars, ih, LExpr.betaReduceWith, annotateFvars_betaReduceK,
          annotateFvars_replaceMetadata1]
      rw [← ih arg, metadata_annotateFvars]

end Annotate

/-! ## Evaluation -/

/-- **An expression that evaluates keeps its value under the contraction of its redexes**, at
    any fuel. -/
theorem LExpr.denoteEval_betaReduceRedexesFuel [DecidableEq T.IDMeta] {M : ModeledFactory T}
    {σ : ValStore T}
    (merge : T.mono.base.Metadata → T.mono.base.Metadata → T.mono.base.Metadata →
      T.mono.base.Metadata) (fuel : Nat) {e : LExpr T.mono} {v : SemValue}
    (hv : e.denoteEval M σ = some v)
    (hvars : LExpr.LExpr.getVars (LExpr.betaReduceRedexesFuel merge false fuel e) ⊆
      LExpr.LExpr.getVars e) :
    (LExpr.betaReduceRedexesFuel merge false fuel e).denoteEval M σ = some v := by
  obtain ⟨hd, τ, hT, hg, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp hv
  have hann := annotateFvars_betaReduceRedexesFuel σ.ann merge fuel e
  have hT' : ((LExpr.betaReduceRedexesFuel merge false fuel e).annotateFvars σ.ann).HasTypeA [] τ :=
    hann ▸ LExpr.HasTypeA_betaReduceRedexesFuel merge false fuel hT
  refine LExpr.denoteEval_eq_some_iff.mpr ⟨fun x hx => hd x (hvars hx), τ, hT', hg, ?_⟩
  unfold LExpr.denoteEvalResult
  congr 1
  letI := M.model.allInhabited
  exact ((denote_eqE _ _ _ _ _ hann hT'
    (LExpr.HasTypeA_betaReduceRedexesFuel merge false fuel hT)).trans
    (denote_betaReduceRedexesFuel _ _ _ _ merge fuel _ _ hT _)).symm

/-- **An expression that evaluates keeps its value under the contraction of its redexes**
    (`LExpr.betaReduceRedexesWith`, at any metadata combinator). -/
theorem LExpr.denoteEval_betaReduceRedexesWith [DecidableEq T.IDMeta] {M : ModeledFactory T}
    {σ : ValStore T}
    (merge : T.mono.base.Metadata → T.mono.base.Metadata → T.mono.base.Metadata →
      T.mono.base.Metadata) {e : LExpr T.mono} {v : SemValue}
    (hv : e.denoteEval M σ = some v) :
    (LExpr.betaReduceRedexesWith merge e).denoteEval M σ = some v :=
  LExpr.denoteEval_betaReduceRedexesFuel merge _ hv (getVars_betaReduceRedexesWith_subset merge e)

end Lambda

end -- public section
