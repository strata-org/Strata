/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.Denote.LExprDenoteTySubst
import all Strata.DL.Lambda.Denote.LExprAnnotated
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
import all Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LTyProps
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote

/-! # Annotated typing under annotation rewriting, and its bridge to `HasType`

Key theorems: `LExpr.HasTypeA_replaceUserProvidedType_map` (rewriting
annotations by `φ` maps an annotated typing by `φ`),
`OpsConsistentR.of_opAnnots` with its `_body` and `_resolveTy` forms (operator
annotations that instantiate their signatures give `OpsConsistentR`), and
`HasType_of_HasTypeA_of_annots` (annotated typing whose free-variable
annotations the context holds gives `HasType`). -/

namespace Lambda

open LExpr
open Strata.Util (HMap HMaps)

public section

/-- Rewriting annotations by `φ` maps an annotated typing's context and type by `φ`, when `φ`
    preserves arrows, `bool`, and literal types. -/
theorem LExpr.HasTypeA_replaceUserProvidedType_map {T : LExprParams}
    (φ : LMonoTy → LMonoTy)
    (hφ_arrow : ∀ a b, φ (.arrow a b) = .arrow (φ a) (φ b))
    (hφ_bool : φ .bool = .bool)
    (hφ_const : ∀ c : LConst, φ c.ty = c.ty)
    (Δ : List LMonoTy) (e : LExpr T.mono) (τ : LMonoTy)
    (h : LExpr.HasTypeA Δ e τ) :
    LExpr.HasTypeA (Δ.map φ) (LExpr.replaceUserProvidedType e φ) (φ τ) := by
  induction h with
  | const hw => rw [hφ_const]; exact .const hw
  | op => exact .op
  | fvar => exact .fvar
  | bvar hlk =>
    apply LExpr.HasTypeA.bvar
    rw [List.getElem?_map, hlk]; rfl
  | abs _ ih =>
    rw [hφ_arrow]
    exact .abs ih
  | quant _ _ ih_tr ih_b =>
    rw [hφ_bool] at ih_b ⊢
    exact .quant ih_tr ih_b
  | app _ _ ih_fn ih_arg =>
    rw [hφ_arrow] at ih_fn
    exact .app ih_fn ih_arg
  | ite _ _ _ ih_c ih_t ih_e =>
    rw [hφ_bool] at ih_c
    exact .ite ih_c ih_t ih_e
  | eq _ _ ih1 ih2 =>
    rw [hφ_bool]
    exact .eq ih1 ih2

/-! ## `OpsConsistentR` from operator annotations -/

/-- A fully annotated expression satisfies `OpsConsistentR F` when every operator annotation is
    an instance of the signature of the function that `F` stores under the operator's name. -/
theorem OpsConsistentR.of_opAnnots {T : LExprParams} {F : Factory T} {e : LExpr T.mono}
    (hann : LExpr.fullyAnnotated e = true)
    (h : ∀ o ty, (o, ty) ∈ LExpr.opAnnots e → ∃ (fn : LFunc T) (τ : Subst),
      F[o.name]? = some fn ∧
        ty = LMonoTy.subst τ (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd))) :
    OpsConsistentR F e := by
  induction e with
  | const => exact .const
  | bvar => exact .bvar
  | fvar => exact .fvar
  | op m o ty =>
    cases ty with
    | none => simp [LExpr.fullyAnnotated] at hann
    | some t =>
      have h_mem : (o, t) ∈ LExpr.opAnnots (LExpr.op m o (some t)) := by
        simp [LExpr.opAnnots]
      obtain ⟨fn, τ, hfn, hty⟩ := h o t h_mem
      exact .op_in hfn hty
  | app m e1 e2 ih1 ih2 =>
    simp only [LExpr.fullyAnnotated, Bool.and_eq_true] at hann
    exact .app (ih1 hann.1 (fun o ty ho => h o ty (List.subset_append_left _ _ ho)))
      (ih2 hann.2 (fun o ty ho => h o ty (List.subset_append_right _ _ ho)))
  | abs m name ty body ih =>
    simp only [LExpr.fullyAnnotated] at hann
    exact .abs (ih hann h)
  | quant m k name ty tr body ih1 ih2 =>
    simp only [LExpr.fullyAnnotated, Bool.and_eq_true] at hann
    exact .quant (ih1 hann.1.2 (fun o ty ho => h o ty (List.subset_append_left _ _ ho)))
      (ih2 hann.2 (fun o ty ho => h o ty (List.subset_append_right _ _ ho)))
  | ite m c t f ih1 ih2 ih3 =>
    simp only [LExpr.fullyAnnotated, Bool.and_eq_true] at hann
    have hc : LExpr.opAnnots c ⊆ LExpr.opAnnots (.ite m c t f) :=
      List.subset_append_of_subset_left _ (List.subset_append_left _ _)
    have ht : LExpr.opAnnots t ⊆ LExpr.opAnnots (.ite m c t f) :=
      List.subset_append_of_subset_left _ (List.subset_append_right _ _)
    exact .ite (ih1 hann.1.1 (fun o ty ho => h o ty (hc ho)))
      (ih2 hann.1.2 (fun o ty ho => h o ty (ht ho)))
      (ih3 hann.2 (fun o ty ho => h o ty (List.subset_append_right _ _ ho)))
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.fullyAnnotated, Bool.and_eq_true] at hann
    exact .eq (ih1 hann.1 (fun o ty ho => h o ty (List.subset_append_left _ _ ho)))
      (ih2 hann.2 (fun o ty ho => h o ty (List.subset_append_right _ _ ho)))

/-- A fully annotated expression satisfies `OpsConsistentR F` when every operator annotation is
    an instance of the body of its function's type scheme and every signature type is registered. -/
theorem OpsConsistentR.of_opAnnots_body {T : LExprParams} [DecidableEq T.IDMeta]
    {ks : KnownTypes} {F : Factory T} {e : LExpr T.mono} (hsig : FactorySigsKnown ks F)
    (hann : LExpr.fullyAnnotated e = true)
    (h : ∀ o ty, (o, ty) ∈ LExpr.opAnnots e →
      ∃ f xs body, F[o.name]? = some f ∧ f.type = .ok (.forAll xs body) ∧
        ∃ τ, ty = LMonoTy.subst τ body) :
    OpsConsistentR F e := by
  refine OpsConsistentR.of_opAnnots hann fun o ty ho => ?_
  obtain ⟨f, xs, body, hf, hty, τ, rfl⟩ := h o ty ho
  have hmem := Factory.getElem?_is_some_implies_mem hf
  have hbody := LFunc.type_eq_mkArrow' hsig.1 hty (hsig.2 f hmem f.output List.mem_cons_self)
  simp only [LTy.forAll.injEq] at hbody
  refine ⟨f, τ, hf, ?_⟩
  rw [hbody.2]

/-- A fully annotated expression satisfies `OpsConsistentR F` when every operator annotation is
    an instance of its function's type-scheme body with `Γ`'s aliases resolved, and no alias of
    `Γ` is named in `ks`. -/
theorem OpsConsistentR.of_opAnnots_resolveTy {T : LExprParams} [DecidableEq T.IDMeta]
    [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] {ks : KnownTypes} {F : Factory T}
    {Γ : TContext T.IDMeta} {e : LExpr T.mono} (hsig : FactorySigsKnown ks F)
    (hfresh : ∀ al ∈ Γ.aliases, ks.containsName al.name = false)
    (hann : LExpr.fullyAnnotated e = true)
    (h : ∀ o ty, (o, ty) ∈ LExpr.opAnnots e →
      ∃ f xs body, F[o.name]? = some f ∧ f.type = .ok (.forAll xs body) ∧
        ∃ τ, ty = LMonoTy.subst τ (Γ.resolveTy body)) :
    OpsConsistentR F e := by
  refine OpsConsistentR.of_opAnnots_body hsig hann fun o ty ho => ?_
  obtain ⟨f, xs, body, hf, hty, τ, rfl⟩ := h o ty ho
  have hkn := LFunc.body_knownInstance hsig.1
    (hsig.2 f (Factory.getElem?_is_some_implies_mem hf)) hty
  exact ⟨f, xs, body, hf, hty, τ,
    congrArg (LMonoTy.subst τ) (TContext.resolveTy_of_knownInstance hfresh hkn)⟩

/-! ## From annotated typing to polymorphic typing

`HasTypeA` checks annotations internally, while `HasType` also consults the
ambient context and factory. The bridge below derives the second from the first
when the free-variable and operator annotations agree with those environments.
-/

/-! ### Typing an operator occurrence -/

/-- An annotated operator that names a factory function reporting a type, whose
    annotation instantiates the declared arrow type, is typed at its
    annotation. -/
private theorem HasType_op_of_OpsConsistentR {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta} {m : T.Metadata}
    {o : Identifier T.IDMeta} {τ : LMonoTy}
    (hop : OpsConsistentR C.functions (.op m o (some τ)))
    (hdecl : ∃ f ty, C.functions[o.name]? = some f ∧ f.type = .ok ty)
    (hsigwf : FactorySigWF C.functions)
    (hsig : FactorySigsKnown C.knownTypes C.functions) :
    LExpr.HasType C Γ (.op m o (some τ)) (.forAll [] τ) := by
  obtain ⟨f, ty_o, hfind, htype⟩ := hdecl
  have hmem : f ∈ C.functions.toArray :=
    Factory.getElem?_is_some_implies_mem hfind
  obtain ⟨tySubst, hτ⟩ := OpsConsistentR.op_inv_of_declared hfind hop
  have hform : ty_o = .forAll f.typeArgs
      (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)) :=
    LFunc.type_eq_mkArrow' hsig.1 htype
      (hsig.2 f hmem f.output List.mem_cons_self)
  obtain ⟨hnodup, hclosed⟩ := factory_type_nodup_closed hsigwf hfind htype
  subst hform
  simp only [LTy.boundVars, LTy.toMonoTypeUnsafe] at hnodup hclosed
  let tys : List LMonoTy :=
    f.typeArgs.map (fun a => LMonoTy.subst tySubst (.ftvar a))
  have hlen : tys.length = f.typeArgs.length := by
    simp only [tys, List.length_map]
  have hopen : LTy.openFull (.forAll f.typeArgs
      (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd))) tys = τ := by
    rw [LTy.openFull_eq_subst_ofZip, hτ]
    refine agree_on_freeVars_implies_subst_eq ?_
    intro v hv
    have hvmem : v ∈ f.typeArgs := hclosed v hv
    have hpair :
        (v, LMonoTy.subst tySubst (.ftvar v)) ∈ List.zip f.typeArgs tys :=
      List.mem_zip_map_self f.typeArgs
        (fun a => LMonoTy.subst tySubst (.ftvar a)) hvmem
    exact LMonoTy.subst_ftvar_of_some
      (Subst.find?_ofZip_of_mem_zip hnodup hpair)
  exact LExpr.HasType.top_annotated Γ m f o _ τ tys τ hfind htype hlen hopen
    AnnotCompat.of_eq

/-! ### The bridge's conditions on subexpressions -/

section BridgeSide

variable {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  {C : LContext T}

/-- The bridge's conditions on an expression in context `Γ`: operator
    annotations instantiate their signatures and name factory functions that
    report a type, `Γ` holds each annotated free variable at its annotation,
    and constant types and binder annotations are registered. -/
private structure BridgeSide (C : LContext T) (Γ : TContext T.IDMeta)
    (e : LExpr T.mono) : Prop where
  ops : OpsConsistentR C.functions e
  decl : ∀ o ∈ getOps e,
    ∃ f ty, C.functions[o.name]? = some f ∧ f.type = .ok ty
  ctx : ∀ y ann, (y, some ann) ∈ LExpr.freeVars e →
    Γ.types.find? y = some (.forAll [] ann)
  consts : ∀ c ∈ getConsts e, C.knownTypes.containsName c.tyName
  binders : ∀ t ∈ LExpr.binderAnnotations e,
    t.knownInstance C.knownTypes = true

/-- The bridge's conditions pass from `e` to an expression with consistent
    operator annotations whose operators, free variables, constants and binder
    annotations all occur in `e`. -/
private theorem BridgeSide.of_sub {Γ : TContext T.IDMeta} {e e' : LExpr T.mono}
    (h : BridgeSide C Γ e) (hops : OpsConsistentR C.functions e')
    (hO : getOps e' ⊆ getOps e) (hF : LExpr.freeVars e' ⊆ LExpr.freeVars e)
    (hC : getConsts e' ⊆ getConsts e)
    (hB : LExpr.binderAnnotations e' ⊆ LExpr.binderAnnotations e) :
    BridgeSide C Γ e' :=
  ⟨hops, fun o ho => h.decl o (hO ho), fun y ann hy => h.ctx y ann (hF hy),
    fun c hc => h.consts c (hC hc), fun t ht => h.binders t (hB ht)⟩

variable {Γ : TContext T.IDMeta} {m : T.Metadata}

/-- The bridge's conditions pass to the function of an application. -/
private theorem BridgeSide.app_fn {fn arg : LExpr T.mono}
    (h : BridgeSide C Γ (.app m fn arg)) : BridgeSide C Γ fn := by
  refine h.of_sub (OpsConsistentR.app_inv h.ops).1 ?_ ?_ ?_ ?_ <;>
    exact List.subset_append_left _ _

/-- The bridge's conditions pass to the argument of an application. -/
private theorem BridgeSide.app_arg {fn arg : LExpr T.mono}
    (h : BridgeSide C Γ (.app m fn arg)) : BridgeSide C Γ arg := by
  refine h.of_sub (OpsConsistentR.app_inv h.ops).2 ?_ ?_ ?_ ?_ <;>
    exact List.subset_append_right _ _

/-- The bridge's conditions pass to the condition of an if-then-else. -/
private theorem BridgeSide.ite_c {c t f : LExpr T.mono}
    (h : BridgeSide C Γ (.ite m c t f)) : BridgeSide C Γ c := by
  refine h.of_sub (OpsConsistentR.ite_inv h.ops).1 ?_ ?_ ?_ ?_ <;>
    exact fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)

/-- The bridge's conditions pass to the then branch of an if-then-else. -/
private theorem BridgeSide.ite_t {c t f : LExpr T.mono}
    (h : BridgeSide C Γ (.ite m c t f)) : BridgeSide C Γ t := by
  refine h.of_sub (OpsConsistentR.ite_inv h.ops).2.1 ?_ ?_ ?_ ?_ <;>
    exact fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)

/-- The bridge's conditions pass to the else branch of an if-then-else. -/
private theorem BridgeSide.ite_e {c t f : LExpr T.mono}
    (h : BridgeSide C Γ (.ite m c t f)) : BridgeSide C Γ f := by
  refine h.of_sub (OpsConsistentR.ite_inv h.ops).2.2 ?_ ?_ ?_ ?_ <;>
    exact List.subset_append_right _ _

/-- The bridge's conditions pass to the left side of an equality. -/
private theorem BridgeSide.eq_lhs {e1 e2 : LExpr T.mono}
    (h : BridgeSide C Γ (.eq m e1 e2)) : BridgeSide C Γ e1 := by
  refine h.of_sub (OpsConsistentR.eq_inv h.ops).1 ?_ ?_ ?_ ?_ <;>
    exact List.subset_append_left _ _

/-- The bridge's conditions pass to the right side of an equality. -/
private theorem BridgeSide.eq_rhs {e1 e2 : LExpr T.mono}
    (h : BridgeSide C Γ (.eq m e1 e2)) : BridgeSide C Γ e2 := by
  refine h.of_sub (OpsConsistentR.eq_inv h.ops).2 ?_ ?_ ?_ ?_ <;>
    exact List.subset_append_right _ _

/-- The bridge's conditions pass to the body of an abstraction. -/
private theorem BridgeSide.abs_body {name : String} {oty : Option LMonoTy}
    {body : LExpr T.mono} (h : BridgeSide C Γ (.abs m name oty body)) :
    BridgeSide C Γ body :=
  h.of_sub (OpsConsistentR.abs_inv h.ops) (List.Subset.refl _)
    (List.Subset.refl _) (List.Subset.refl _) (List.subset_append_right _ _)

/-- The bridge's conditions pass to the trigger of a quantifier. -/
private theorem BridgeSide.quant_tr {k : QuantifierKind} {name : String}
    {oty : Option LMonoTy} {tr body : LExpr T.mono}
    (h : BridgeSide C Γ (.quant m k name oty tr body)) : BridgeSide C Γ tr :=
  h.of_sub (OpsConsistentR.quant_inv h.ops).1 (List.subset_append_left _ _)
    (List.subset_append_left _ _) (List.subset_append_left _ _)
    (fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx))

/-- The bridge's conditions pass to the body of a quantifier. -/
private theorem BridgeSide.quant_body {k : QuantifierKind} {name : String}
    {oty : Option LMonoTy} {tr body : LExpr T.mono}
    (h : BridgeSide C Γ (.quant m k name oty tr body)) :
    BridgeSide C Γ body := by
  refine h.of_sub (OpsConsistentR.quant_inv h.ops).2 ?_ ?_ ?_ ?_ <;>
    exact List.subset_append_right _ _

/-- The bridge's conditions survive opening a binder at a variable `x` that the
    expression does not mention, once the context holds `x` at the binder's
    type. -/
private theorem BridgeSide.varOpen {e : LExpr T.mono} {x : T.Identifier}
    {aty : LMonoTy} (h : BridgeSide C Γ e) (hx : x ∉ LExpr.getVars e) :
    BridgeSide C { Γ with types := Γ.types.insert x (.forAll [] aty) }
      (LExpr.varOpen 0 (x, some aty) e) where
  ops := OpsConsistentR_varOpen (x, some aty) 0 e h.ops
  decl := by
    rw [getOps_varOpen]
    exact h.decl
  ctx := by
    intro y ann hy
    rcases varOpen_freeVars_subset 0 (x, some aty) e (y, some ann) hy with
      hyx | hmem
    · cases hyx
      exact HMaps.find?_insert_self Γ.types x (.forAll [] aty)
    · have hyvars : y ∈ LExpr.getVars e := by
        rw [getVars_eq_freeVars_idents]
        exact List.mem_map.mpr ⟨(y, some ann), hmem, rfl⟩
      have hne : y ≠ x := fun hyx => hx (hyx ▸ hyvars)
      rw [HMaps.find?_insert_ne Γ.types y x (.forAll [] aty) hne]
      exact h.ctx y ann hmem
  consts := by
    rw [getConsts_varOpen]
    exact h.consts
  binders := by
    rw [binderAnnotations_varOpen]
    exact h.binders

end BridgeSide

/-! ### The bridge theorem -/

/-- Annotated typing of an expression that meets the bridge's conditions gives
    the type derived by the typing rules. Proved by induction on the expression
    size. -/
private theorem HasType_of_HasTypeA_of_annots_aux {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Inhabited T.IDMeta]
    {C : LContext T} (hsigwf : FactorySigWF C.functions)
    (hsig : FactorySigsKnown C.knownTypes C.functions) :
    ∀ (n : Nat) (e : LExpr T.mono) (τ : LMonoTy) (Γ : TContext T.IDMeta),
      e.sizeOf ≤ n →
      LExpr.HasTypeA [] e τ →
      BridgeSide C Γ e →
      (∀ al ∈ Γ.aliases, KnownTypes.containsName C.knownTypes al.name = false) →
      LExpr.HasType C Γ e (.forAll [] τ) := by
  intro n
  induction n with
  | zero =>
    intro e τ Γ hsz _ _ _
    cases e <;> simp only [LExpr.sizeOf] at hsz <;> omega
  | succ n ih =>
    intro e τ Γ hsz hA hs hfresh
    cases e with
    | const m c =>
      have hτ := HasTypeA.const_inv hA
      subst hτ
      have hk : C.knownTypes.containsName c.tyName :=
        hs.consts c (List.mem_singleton_self c)
      cases c with
      | intConst i => exact .tint_const Γ m i hk
      | strConst t => exact .tstr_const Γ m t hk
      | rationalConst r => exact .treal_const Γ m r hk
      | bitvecConst w b => exact .tbitvec_const Γ m w b hk
      | boolConst b => exact .tbool_const Γ m b hk
      | mapConst k v d es => exact .tmap_const Γ m k v d es hk (HasTypeA.const_wt hA)
      | sequenceConst a es => exact .tseq_const Γ m a es hk (HasTypeA.const_wt hA)
    | bvar m i =>
      have hlookup := HasTypeA.bvar_inv hA
      rw [List.getElem?_nil] at hlookup
      exact nomatch hlookup
    | op m o oty =>
      have hoty := HasTypeA.op_inv_opt hA
      subst hoty
      exact HasType_op_of_OpsConsistentR hs.ops
        (hs.decl o (List.mem_singleton_self o)) hsigwf hsig
    | fvar m y oty =>
      have hoty := HasTypeA.fvar_inv_opt hA
      subst hoty
      have hctxy := hs.ctx y τ (List.mem_singleton_self _)
      have hopen : LTy.openFull (LTy.forAll [] τ) [] = τ :=
        openFull_forAll_nil τ []
      have hlen :
        ([] : List LMonoTy).length = (LTy.forAll [] τ).boundVars.length := rfl
      exact LExpr.HasType.tvar_annotated Γ m y (.forAll [] τ) τ [] τ
        hctxy hlen hopen AnnotCompat.of_eq
    | abs m name oty body =>
      obtain ⟨aty, rty, hoty, hτ, hbody⟩ := HasTypeA.abs_inv_opt hA
      subst hoty
      subst hτ
      have hbAty : aty.knownInstance C.knownTypes = true :=
        hs.binders aty (List.mem_append_left _ (List.mem_singleton_self aty))
      obtain ⟨x, hxnot⟩ := exists_notMem_getVars (T := T) body
      have hfresh' :
          LExpr.fresh ((x, some aty) : IdentT LMonoTy T.IDMeta) body :=
        fresh_of_notMem_getVars hxnot
      have hmonoA : LTy.isMonoType (LTy.forAll [] aty) = true := rfl
      have hmonoR : LTy.isMonoType (LTy.forAll [] rty) = true := rfl
      have hopenA :
          LExpr.HasTypeA [] (LExpr.varOpen 0 (x, some aty) body) rty :=
        varOpen_HasTypeA hbody
      have hszbody : (LExpr.varOpen 0 (x, some aty) body).sizeOf ≤ n := by
        rw [LExpr.varOpen_sizeOf]
        simp only [LExpr.sizeOf] at hsz
        omega
      have hbodyT := ih (LExpr.varOpen 0 (x, some aty) body) rty
        { Γ with types := Γ.types.insert x (.forAll [] aty) } hszbody hopenA
        (hs.abs_body.varOpen hxnot) hfresh
      have hvalidA : ∀ t, some aty = some t →
          ∃ r, SourceTyWF C TyVarAdmissibility.all Γ.aliases t r := by
        intro t ht
        cases ht
        exact ⟨_, SourceTyWF.self_of_knownInstance hfresh hbAty⟩
      exact LExpr.HasType.tabs Γ m name (x, some aty) (.forAll [] aty) body
        (.forAll [] rty) (some aty) hfresh' hmonoA hmonoR hbodyT
        (Or.inr ⟨aty, rfl, AnnotCompat.of_eq⟩) hvalidA
    | quant m k name oty tr body =>
      obtain ⟨qty, τ_tr, hoty, hτ, htr, hbody⟩ := HasTypeA.quant_inv_opt hA
      subst hoty
      subst hτ
      have hbQty : qty.knownInstance C.knownTypes = true :=
        hs.binders qty
          (List.mem_append_left _
            (List.mem_append_left _ (List.mem_singleton_self qty)))
      obtain ⟨x, hxnot⟩ :=
        exists_notMem_getVars (T := T) (LExpr.quant m k name (some qty) tr body)
      have hxnot_tr : x ∉ LExpr.getVars tr := fun hmem =>
        hxnot (List.mem_append_left _ hmem)
      have hxnot_body : x ∉ LExpr.getVars body := fun hmem =>
        hxnot (List.mem_append_right _ hmem)
      have hfresh' :
          LExpr.fresh ((x, some qty) : IdentT LMonoTy T.IDMeta) body :=
        fresh_of_notMem_getVars hxnot_body
      have hmonoQ : LTy.isMonoType (LTy.forAll [] qty) = true := rfl
      have hopenTr :
          LExpr.HasTypeA [] (LExpr.varOpen 0 (x, some qty) tr) τ_tr :=
        varOpen_HasTypeA htr
      have hopenBody :
          LExpr.HasTypeA [] (LExpr.varOpen 0 (x, some qty) body) .bool :=
        varOpen_HasTypeA hbody
      have hszTr : (LExpr.varOpen 0 (x, some qty) tr).sizeOf ≤ n := by
        rw [LExpr.varOpen_sizeOf]
        simp only [LExpr.sizeOf] at hsz
        omega
      have hszBody : (LExpr.varOpen 0 (x, some qty) body).sizeOf ≤ n := by
        rw [LExpr.varOpen_sizeOf]
        simp only [LExpr.sizeOf] at hsz
        omega
      have htrT := ih (LExpr.varOpen 0 (x, some qty) tr) τ_tr
        { Γ with types := Γ.types.insert x (.forAll [] qty) } hszTr hopenTr
        (hs.quant_tr.varOpen hxnot_tr) hfresh
      have hbodyT := ih (LExpr.varOpen 0 (x, some qty) body) .bool
        { Γ with types := Γ.types.insert x (.forAll [] qty) } hszBody hopenBody
        (hs.quant_body.varOpen hxnot_body) hfresh
      have hvalidQ : ∀ t, some qty = some t →
          ∃ r, SourceTyWF C TyVarAdmissibility.all Γ.aliases t r := by
        intro t ht
        cases ht
        exact ⟨_, SourceTyWF.self_of_knownInstance hfresh hbQty⟩
      exact LExpr.HasType.tquant Γ m k name tr (.forAll [] τ_tr) (x, some qty)
        (.forAll [] qty) body (some qty) hfresh' hmonoQ hbodyT htrT
        (Or.inr ⟨qty, rfl, AnnotCompat.of_eq⟩) hvalidQ
    | app m fn arg =>
      obtain ⟨aty, hfn, harg⟩ := HasTypeA.app_inv hA
      have hszfn : fn.sizeOf ≤ n := by
        simp only [LExpr.sizeOf] at hsz
        omega
      have hszarg : arg.sizeOf ≤ n := by
        simp only [LExpr.sizeOf] at hsz
        omega
      have hmonoA : LTy.isMonoType (LTy.forAll [] aty) = true := rfl
      have hmonoR : LTy.isMonoType (LTy.forAll [] τ) = true := rfl
      have hfnT := ih fn (.arrow aty τ) Γ hszfn hfn hs.app_fn hfresh
      have hargT := ih arg aty Γ hszarg harg hs.app_arg hfresh
      exact .tapp Γ m fn arg (.forAll [] τ) (.forAll [] aty) hmonoR hmonoA
        hfnT hargT
    | ite m c t e =>
      obtain ⟨hc, ht, he⟩ := HasTypeA.ite_inv hA
      have hszc : c.sizeOf ≤ n := by
        simp only [LExpr.sizeOf] at hsz
        omega
      have hszt : t.sizeOf ≤ n := by
        simp only [LExpr.sizeOf] at hsz
        omega
      have hsze : e.sizeOf ≤ n := by
        simp only [LExpr.sizeOf] at hsz
        omega
      have hcT := ih c .bool Γ hszc hc hs.ite_c hfresh
      have htT := ih t τ Γ hszt ht hs.ite_t hfresh
      have heT := ih e τ Γ hsze he hs.ite_e hfresh
      exact .tif Γ m c t e (.forAll [] τ) hcT htT heT
    | eq m e1 e2 =>
      obtain ⟨τ', hτ, h1, h2⟩ := HasTypeA.eq_inv hA
      subst hτ
      have hsz1 : e1.sizeOf ≤ n := by
        simp only [LExpr.sizeOf] at hsz
        omega
      have hsz2 : e2.sizeOf ≤ n := by
        simp only [LExpr.sizeOf] at hsz
        omega
      have h1T := ih e1 τ' Γ hsz1 h1 hs.eq_lhs hfresh
      have h2T := ih e2 τ' Γ hsz2 h2 hs.eq_rhs hfresh
      exact .teq Γ m e1 e2 (.forAll [] τ') h1T h2T

/-- Annotated typing gives polymorphic typing. If `e` has annotated typing `τ`,
    its operator annotations instantiate the factory signatures, and `Γ` holds
    every annotated free variable of `e` at its annotation as a monotype, then
    `e` has the monotype `τ` in `Γ`. The other hypotheses say that every
    operator names a factory function that reports a type, that the factory's
    signatures are well formed and registered, that every constant's type and
    binder annotation is registered, and that no alias of `Γ` is named like a
    registered type. -/
theorem HasType_of_HasTypeA_of_annots {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Inhabited T.IDMeta]
    {C : LContext T} {Γ : TContext T.IDMeta}
    {e : LExpr T.mono} {τ : LMonoTy}
    (hA : LExpr.HasTypeA [] e τ)
    (hctx : ∀ y ann, (y, some ann) ∈ LExpr.freeVars e →
      Γ.types.find? y = some (.forAll [] ann))
    (hop : OpsConsistentR C.functions e)
    (hdecl : ∀ o ∈ getOps e,
      ∃ f ty, C.functions[o.name]? = some f ∧ f.type = .ok ty)
    (hconst : ∀ c ∈ getConsts e, C.knownTypes.containsName c.tyName)
    (hsigwf : FactorySigWF C.functions)
    (hsig : FactorySigsKnown C.knownTypes C.functions)
    (hbind : ∀ t ∈ LExpr.binderAnnotations e,
      t.knownInstance C.knownTypes = true)
    (hfresh : ∀ al ∈ Γ.aliases,
      KnownTypes.containsName C.knownTypes al.name = false) :
    LExpr.HasType C Γ e (.forAll [] τ) :=
  HasType_of_HasTypeA_of_annots_aux hsigwf hsig e.sizeOf e τ Γ (Nat.le_refl _)
    hA ⟨hop, hdecl, hctx, hconst, hbind⟩ hfresh

end -- public section

end Lambda
