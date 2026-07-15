/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.Languages.Core.FunctionTypeSpec
import all Strata.Languages.Core.FunctionType
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprResolveProps
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst
import all Strata.DL.Util.Nodup
import all Strata.Languages.Core.InverseComponents

/-! ## Soundness of Function Typechecker

Relates the executable function typechecker `Function.typeCheck` to the
declarative typing specifications `FuncHasType` and `FuncHasTypeA`.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

/-! ### Helper Lemmas -/

/-- `LTy.subst` composition for a monomorphic (`forAll []`) scheme: applying `S`
    then a single scope `[s]` equals applying the single composite `Subst.compose s S`.
    Follows from `LMonoTy.subst_compose` through `subst_forAll_nil` (no binder
    interaction, since the scheme has no bound vars). -/
theorem LTy.subst_compose_forAll_nil (s : SubstOne) (S : Subst) (mty : LMonoTy) :
    LTy.subst [s] (LTy.subst S (.forAll [] mty)) =
    LTy.subst (Subst.compose s S) (.forAll [] mty) := by
  rw [LTy.subst_forAll_nil, LTy.subst_forAll_nil, LTy.subst_forAll_nil, LMonoTy.subst_compose]

/-- `TContext.types.subst.go` composition over a single scope of all-`forAll []`
    entries: applying `S` then `[s]` equals applying `Subst.compose s S`. The
    monotonicity hypothesis is membership-based (threads trivially through `cons`). -/
theorem TContext.types_subst_go_compose_forAll_nil (s : SubstOne) (S : Subst)
    (scope : Map (Identifier Unit) LTy)
    (h_mono : ∀ ty ∈ Map.values scope, ty.boundVars = []) :
    TContext.types.subst.go [s] (TContext.types.subst.go S scope) =
    TContext.types.subst.go (Subst.compose s S) scope := by
  induction scope with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨x, ty⟩ := hd
    have h_hd_mono : ty.boundVars = [] := h_mono ty (by simp [Map.values])
    have h_tl_mono : ∀ ty' ∈ Map.values tl, ty'.boundVars = [] :=
      fun ty' h' => h_mono ty' (by simp only [Map.values]; exact List.mem_cons_of_mem ty h')
    simp only [TContext.types.subst.go]
    rw [ih h_tl_mono]
    congr 1
    cases ty with
    | forAll xs m =>
      simp only [LTy.boundVars] at h_hd_mono
      subst h_hd_mono
      exact congrArg (Prod.mk x) (LTy.subst_compose_forAll_nil s S m)

/-- `TContext.types.subst` composition over all-`forAll []` scopes. -/
theorem TContext.types_subst_compose_forAll_nil (s : SubstOne) (S : Subst)
    (types : Maps (Identifier Unit) LTy)
    (h_mono : ∀ ty ∈ Maps.values types, ty.boundVars = []) :
    TContext.types.subst (TContext.types.subst types S) [s] =
    TContext.types.subst types (Subst.compose s S) := by
  induction types with
  | nil => rfl
  | cons scope rest ih =>
    have h_scope_mono : ∀ ty ∈ Map.values scope, ty.boundVars = [] :=
      fun ty h => h_mono ty (by simp only [Maps.values]; exact List.mem_append_left _ h)
    have h_rest_mono : ∀ ty ∈ Maps.values rest, ty.boundVars = [] :=
      fun ty h => h_mono ty (by simp only [Maps.values]; exact List.mem_append_right _ h)
    simp only [TContext.types.subst]
    rw [ih h_rest_mono, TContext.types_subst_go_compose_forAll_nil s S scope h_scope_mono]

/-- `TContext.subst` composition over a context whose entries are all `forAll []`
    (monomorphic). Applying `S` then `[s]` equals applying `Subst.compose s S`. -/
theorem TContext.subst_compose_forAll_nil (s : SubstOne) (S : Subst) (Γ : TContext Unit)
    (h_mono : ∀ ty ∈ Maps.values Γ.types, ty.boundVars = []) :
    TContext.subst (TContext.subst Γ S) [s] = TContext.subst Γ (Subst.compose s S) := by
  simp only [TContext.subst]
  exact congrArg (fun t => { Γ with types := t })
    (TContext.types_subst_compose_forAll_nil s S Γ.types h_mono)

/-- If `LFunc.type` succeeds, the type args are nodup. -/
theorem LFunc.type_typeArgs_nodup {T : LExprParams} [DecidableEq T.IDMeta]
    (f : LFunc T) (ty : LTy) (h : f.type = .ok ty) :
    f.typeArgs.Nodup := by
  simp only [LFunc.type, bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i _ h_tyargs_neg
  simp at h_tyargs_neg
  exact h_tyargs_neg

/-- If `LTy.freeVars (forAll xs m) = []`, then all free vars of `m` are in `xs`. -/
theorem LTy.freeVars_nil_imp_mem (xs : List TyIdentifier) (m : LMonoTy)
    (h : LTy.freeVars (.forAll xs m) = []) :
    ∀ v, v ∈ LMonoTy.freeVars m → v ∈ xs := by
  intro v hv
  simp only [LTy.freeVars] at h
  rcases Decidable.em (v ∈ xs) with hmem | hc
  · exact hmem
  · exfalso
    have hin : v ∈ (LMonoTy.freeVars m).removeAll xs := by
      simp only [List.removeAll, List.mem_filter, List.elem_eq_mem, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not]
      exact ⟨hv, hc⟩
    rw [h] at hin
    exact absurd hin List.not_mem_nil

/-- Applying a type substitution to an `AbsWF` `LExprT` preserves `HasTypeA`,
    mapping the type through `subst S`. The `AbsWF` precondition (every abs
    subnode has arrow-typed metadata) is essential: it is what makes `applySubstT`
    (rewriting metadata) commute with `applySubst` (rewriting annotation fields).
    It is established for `resolve` outputs by `resolve_AbsWF`. -/
theorem applySubstT_unresolved_HasTypeA {T : LExprParams} [DecidableEq T.IDMeta]
    (et : LExprT T.mono) (S : Subst) (Δ : List LMonoTy)
    (h_wf : LExprT.AbsWF et)
    (h : LExpr.HasTypeA Δ et.unresolved (et.toLMonoTy)) :
    LExpr.HasTypeA (Δ.map (LMonoTy.subst S)) (applySubstT et S).unresolved
      ((applySubstT et S).toLMonoTy) := by
  rw [applySubstT_toLMonoTy, applySubstT_unresolved_eq_applySubst et S h_wf]
  exact applySubst_typeCheck S h

/-- `AliasEquivList` relates lists of equal length (it is a pointwise relation). -/
theorem AliasEquivList.length_eq {al : List TypeAlias} :
    ∀ {as bs : LMonoTys}, AliasEquivList al as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons _ tl => by simp [AliasEquivList.length_eq tl]

/-- Formals-scope lookup: from the pointwise `AliasEquivList aliases (f <$> slice) inputs.values`,
    a key `x` bound to `forAll [] s` in the formals scope yields `AliasEquiv aliases (f s)` against
    the matching `inputs.values` entry. `f` is arbitrary (instantiated to `subst ρ` at the call site). -/
private theorem region_a_input_lookup {aliases : List TypeAlias}
    (inputs : List (Identifier CoreLParams.IDMeta × LMonoTy)) (slice : LMonoTys)
    (f : LMonoTy → LMonoTy) (x : Identifier CoreLParams.IDMeta) (s : LMonoTy)
    (h_len : slice.length = inputs.length)
    (h_ae : AliasEquivList aliases (slice.map f) (inputs.map Prod.snd))
    (h_fmls : Map.find?
      ((inputs.map Prod.fst).zip slice |>.map (fun p => (p.1, LTy.forAll [] p.2))) x
      = some (LTy.forAll [] s)) :
    ∃ mty', Map.find? (inputs.map (fun p => (p.1, LTy.forAll [] p.2))) x
        = some (LTy.forAll [] mty') ∧ AliasEquiv aliases (f s) mty' := by
  induction inputs generalizing slice with
  | nil =>
    simp only [List.map_nil] at h_fmls
    rw [show ([] : List (Identifier CoreLParams.IDMeta)).zip slice = [] from rfl] at h_fmls
    simp [Map.find?] at h_fmls
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    cases slice with
    | nil => simp at h_len
    | cons s0 srest =>
      simp only [List.map_cons, List.zip_cons_cons, Map.find?] at h_fmls ⊢
      cases h_ae with
      | cons h_hd h_tl =>
        by_cases hkx : k = x
        · rw [if_pos hkx] at h_fmls ⊢
          simp only [Option.some.injEq, LTy.forAll.injEq, true_and] at h_fmls
          refine ⟨v, rfl, ?_⟩
          rw [h_fmls] at h_hd
          exact h_hd
        · rw [if_neg hkx] at h_fmls ⊢
          have h_len' : srest.length = rest.length := by simpa using h_len
          exact ih srest h_len' h_tl h_fmls

/-- Monotonicity of the backward map across `goList`: existing entries are never
    overwritten. Parameterized by the per-element monotonicity of `go` (supplied by the
    structural IH at the `tcons` case of `go_bwd_mono`). -/
private theorem goList_bwd_mono (ts1 : List LMonoTy)
    (hgo : ∀ a ∈ ts1, ∀ (t2 : LMonoTy) (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
        LMonoTy.alphaEquivMap.go a t2 fwd bwd = some (fwd', bwd') →
        ∀ (y x : TyIdentifier), bwd[y]? = some x → bwd'[y]? = some x) :
    ∀ (ts2 : List LMonoTy) (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
      LMonoTy.alphaEquivMap.goList ts1 ts2 fwd bwd = some (fwd', bwd') →
      ∀ (y x : TyIdentifier), bwd[y]? = some x → bwd'[y]? = some x := by
  induction ts1 with
  | nil =>
    intro ts2 fwd bwd fwd' bwd' hgl y x hyx
    cases ts2 with
    | nil =>
      unfold LMonoTy.alphaEquivMap.goList at hgl
      simp only [Option.some.injEq, Prod.mk.injEq] at hgl
      obtain ⟨_, hb⟩ := hgl; rw [← hb]; exact hyx
    | cons b bs =>
      exact absurd hgl (by unfold LMonoTy.alphaEquivMap.goList; simp)
  | cons a as ih =>
    intro ts2 fwd bwd fwd' bwd' hgl y x hyx
    cases ts2 with
    | nil => exact absurd hgl (by unfold LMonoTy.alphaEquivMap.goList; simp)
    | cons b bs =>
      unfold LMonoTy.alphaEquivMap.goList at hgl
      cases hga : LMonoTy.alphaEquivMap.go a b fwd bwd with
      | none => rw [hga] at hgl; exact absurd hgl (by simp)
      | some fb =>
        obtain ⟨f1, b1⟩ := fb
        rw [hga] at hgl
        have hmono_a := hgo a (List.mem_cons_self ..) b fwd bwd f1 b1 hga y x hyx
        exact ih (fun c hc => hgo c (List.mem_cons_of_mem a hc)) bs f1 b1 fwd' bwd' hgl y x hmono_a

/-- Monotonicity of the backward map across `go`: existing entries are never overwritten. -/
private theorem go_bwd_mono (t1 : LMonoTy) :
    ∀ (t2 : LMonoTy) (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
      LMonoTy.alphaEquivMap.go t1 t2 fwd bwd = some (fwd', bwd') →
      ∀ (y x : TyIdentifier), bwd[y]? = some x → bwd'[y]? = some x := by
  induction t1 with
  | ftvar x1 =>
    intro t2 fwd bwd fwd' bwd' hgo y x hyx
    cases t2 with
    | ftvar y1 =>
      unfold LMonoTy.alphaEquivMap.go at hgo
      cases hfwd : fwd[x1]? with
      | some y' =>
        simp only [hfwd] at hgo
        by_cases hb : y' == y1
        · rw [if_pos hb] at hgo
          simp only [Option.some.injEq, Prod.mk.injEq] at hgo
          obtain ⟨_, hbeq⟩ := hgo; rw [← hbeq]; exact hyx
        · rw [if_neg hb] at hgo; exact absurd hgo (by simp)
      | none =>
        simp only [hfwd] at hgo
        cases hbwd : bwd[y1]? with
        | some x' =>
          simp only [hbwd] at hgo
          by_cases hb : x' == x1
          · rw [if_pos hb] at hgo
            simp only [Option.some.injEq, Prod.mk.injEq] at hgo
            obtain ⟨_, hbeq⟩ := hgo; rw [← hbeq]; exact hyx
          · rw [if_neg hb] at hgo; exact absurd hgo (by simp)
        | none =>
          simp only [hbwd] at hgo
          simp only [Option.some.injEq, Prod.mk.injEq] at hgo
          obtain ⟨_, hbeq⟩ := hgo
          rw [← hbeq]
          -- bwd' = bwd.insert y1 x1; entry at y (≠ y1, since bwd[y1]? = none ≠ some x) preserved
          have hy_ne : y1 ≠ y := by
            intro h; rw [h] at hbwd; rw [hbwd] at hyx; exact absurd hyx (by simp)
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by simpa only [beq_iff_eq] using hy_ne)]
          exact hyx
    | bitvec n => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | tcons n args => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
  | bitvec n1 =>
    intro t2 fwd bwd fwd' bwd' hgo y x hyx
    cases t2 with
    | bitvec n2 =>
      unfold LMonoTy.alphaEquivMap.go at hgo
      by_cases hn : n1 == n2
      · rw [if_pos hn] at hgo
        simp only [Option.some.injEq, Prod.mk.injEq] at hgo
        obtain ⟨_, hbeq⟩ := hgo; rw [← hbeq]; exact hyx
      · rw [if_neg hn] at hgo; exact absurd hgo (by simp)
    | ftvar y1 => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | tcons n args => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
  | tcons name1 args1 ih =>
    intro t2 fwd bwd fwd' bwd' hgo y x hyx
    cases t2 with
    | tcons name2 args2 =>
      unfold LMonoTy.alphaEquivMap.go at hgo
      by_cases hname : name1 != name2
      · rw [if_pos hname] at hgo; exact absurd hgo (by simp)
      · rw [if_neg hname] at hgo
        exact goList_bwd_mono args1 ih args2 fwd bwd fwd' bwd' hgo y x hyx
    | ftvar y1 => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | bitvec n => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)

/-- Inversion invariant for `goList`, threaded element by element. Given (P1) `bwd`
    inverts `S` and (P2) `fwd`/`bwd` are mutual inverses, success of
    `goList ts1 (ts1.map (subst S)) fwd bwd` preserves both, and the resulting `bwd'`
    contains a witness `(y, x)` for every free variable `x` of `ts1`. Parameterized by the
    per-element `go` inversion (supplied by the structural IH at `go_bwd_inverts`'s tcons). -/
private theorem goList_bwd_inverts (S : Subst) (ts1 : List LMonoTy)
    (ih : ∀ a ∈ ts1, ∀ (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
        LMonoTy.alphaEquivMap.go a (LMonoTy.subst S a) fwd bwd = some (fwd', bwd') →
        (∀ y x, bwd[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) →
        (∀ (x y : TyIdentifier), fwd[x]? = some y → bwd[y]? = some x) →
        ((∀ y x, bwd'[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) ∧
         (∀ (x y : TyIdentifier), fwd'[x]? = some y → bwd'[y]? = some x)) ∧
        (∀ x ∈ LMonoTy.freeVars a,
          ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y ∧ bwd'[y]? = some x)) :
    ∀ (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
      LMonoTy.alphaEquivMap.goList ts1 (ts1.map (LMonoTy.subst S)) fwd bwd = some (fwd', bwd') →
      (∀ y x, bwd[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) →
      (∀ (x y : TyIdentifier), fwd[x]? = some y → bwd[y]? = some x) →
      ((∀ y x, bwd'[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) ∧
       (∀ (x y : TyIdentifier), fwd'[x]? = some y → bwd'[y]? = some x)) ∧
      (∀ x ∈ LMonoTys.freeVars ts1,
        ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y ∧ bwd'[y]? = some x) := by
  induction ts1 with
  | nil =>
    intro fwd bwd fwd' bwd' hgl hP1 hP2
    rw [List.map_nil] at hgl
    unfold LMonoTy.alphaEquivMap.goList at hgl
    simp only [Option.some.injEq, Prod.mk.injEq] at hgl
    obtain ⟨hf, hb⟩ := hgl
    subst hf hb
    refine ⟨⟨hP1, hP2⟩, ?_⟩
    intro x hx
    simp only [LMonoTys.freeVars] at hx
    exact absurd hx (by simp)
  | cons a as ih_tail =>
    intro fwd bwd fwd' bwd' hgl hP1 hP2
    rw [List.map_cons] at hgl
    unfold LMonoTy.alphaEquivMap.goList at hgl
    cases hga : LMonoTy.alphaEquivMap.go a (LMonoTy.subst S a) fwd bwd with
    | none => rw [hga] at hgl; exact absurd hgl (by simp)
    | some fb =>
      obtain ⟨f1, b1⟩ := fb
      rw [hga] at hgl
      have hhead := ih a (List.mem_cons_self ..) fwd bwd f1 b1 hga hP1 hP2
      obtain ⟨⟨hP1_1, hP2_1⟩, hex_head⟩ := hhead
      have htail := ih_tail (fun c hc => ih c (List.mem_cons_of_mem a hc))
        f1 b1 fwd' bwd' hgl hP1_1 hP2_1
      obtain ⟨⟨hP1', hP2'⟩, hex_tail⟩ := htail
      refine ⟨⟨hP1', hP2'⟩, ?_⟩
      intro x hx
      simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hx
      cases hx with
      | inl hx_a =>
        obtain ⟨y, hsy, hb1y⟩ := hex_head x hx_a
        have hmono := goList_bwd_mono as (fun c _ => go_bwd_mono c)
          (as.map (LMonoTy.subst S)) f1 b1 fwd' bwd' hgl y x hb1y
        exact ⟨y, hsy, hmono⟩
      | inr hx_as => exact hex_tail x hx_as

/-- Inversion invariant for `go`: success of `go t1 (subst S t1) fwd bwd` preserves
    (P1) `bwd` inverts `S` and (P2) `fwd`/`bwd` mutual-inverse, and yields a witness in
    `bwd'` for every free variable of `t1`. The `ftvar` fwd-hit branch is exactly where
    P2 is consumed (to recover `bwd[y]? = some x` from `fwd[x]? = some y`). -/
private theorem go_bwd_inverts (S : Subst) (t1 : LMonoTy) :
    ∀ (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
      LMonoTy.alphaEquivMap.go t1 (LMonoTy.subst S t1) fwd bwd = some (fwd', bwd') →
      (∀ y x, bwd[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) →
      (∀ (x y : TyIdentifier), fwd[x]? = some y → bwd[y]? = some x) →
      ((∀ y x, bwd'[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) ∧
       (∀ (x y : TyIdentifier), fwd'[x]? = some y → bwd'[y]? = some x)) ∧
      (∀ x ∈ LMonoTy.freeVars t1,
        ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y ∧ bwd'[y]? = some x) := by
  induction t1 with
  | ftvar x1 =>
    intro fwd bwd fwd' bwd' hgo hP1 hP2
    cases hsub : LMonoTy.subst S (.ftvar x1) with
    | bitvec n =>
      rw [hsub] at hgo; exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | tcons nm ar =>
      rw [hsub] at hgo; exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | ftvar y1 =>
      rw [hsub] at hgo
      unfold LMonoTy.alphaEquivMap.go at hgo
      cases hfwd : fwd[x1]? with
      | some y' =>
        simp only [hfwd] at hgo
        by_cases hb : y' == y1
        · rw [if_pos hb] at hgo
          simp only [Option.some.injEq, Prod.mk.injEq] at hgo
          obtain ⟨hf, hbb⟩ := hgo
          subst hf hbb
          refine ⟨⟨hP1, hP2⟩, ?_⟩
          intro x hx
          simp only [LMonoTy.freeVars, List.mem_singleton] at hx
          subst hx
          refine ⟨y1, hsub, ?_⟩
          have hy : y' = y1 := by simpa only [beq_iff_eq] using hb
          rw [hy] at hfwd
          exact hP2 x y1 hfwd
        · rw [if_neg hb] at hgo; exact absurd hgo (by simp)
      | none =>
        simp only [hfwd] at hgo
        cases hbwd : bwd[y1]? with
        | some x' =>
          simp only [hbwd] at hgo
          by_cases hb : x' == x1
          · rw [if_pos hb] at hgo
            simp only [Option.some.injEq, Prod.mk.injEq] at hgo
            obtain ⟨hf, hbb⟩ := hgo
            subst hf hbb
            refine ⟨⟨hP1, hP2⟩, ?_⟩
            intro x hx
            simp only [LMonoTy.freeVars, List.mem_singleton] at hx
            subst hx
            refine ⟨y1, hsub, ?_⟩
            have hx' : x' = x := by simpa only [beq_iff_eq] using hb
            rw [hx'] at hbwd; exact hbwd
          · rw [if_neg hb] at hgo; exact absurd hgo (by simp)
        | none =>
          simp only [hbwd] at hgo
          simp only [Option.some.injEq, Prod.mk.injEq] at hgo
          obtain ⟨hf, hbb⟩ := hgo
          subst hf hbb
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro y x hyx
            rw [Std.HashMap.getElem?_insert] at hyx
            by_cases hyy1 : y1 == y
            · rw [if_pos hyy1] at hyx
              simp only [Option.some.injEq] at hyx
              subst hyx
              have hyeq : y1 = y := by simpa only [beq_iff_eq] using hyy1
              rw [← hyeq]; exact hsub
            · rw [if_neg hyy1] at hyx; exact hP1 y x hyx
          · intro x y hxy
            rw [Std.HashMap.getElem?_insert] at hxy
            rw [Std.HashMap.getElem?_insert]
            by_cases hxx1 : x1 == x
            · rw [if_pos hxx1] at hxy
              simp only [Option.some.injEq] at hxy
              subst hxy
              have hx1x : x1 = x := by simpa only [beq_iff_eq] using hxx1
              rw [if_pos (by simp), hx1x]
            · rw [if_neg hxx1] at hxy
              have hbwy := hP2 x y hxy
              by_cases hyy1 : y1 == y
              · have hyeq : y1 = y := by simpa only [beq_iff_eq] using hyy1
                rw [hyeq] at hbwd; rw [hbwd] at hbwy; exact absurd hbwy (by simp)
              · rw [if_neg hyy1]; exact hbwy
          · intro x hx
            simp only [LMonoTy.freeVars, List.mem_singleton] at hx
            subst hx
            refine ⟨y1, hsub, ?_⟩
            rw [Std.HashMap.getElem?_insert]; simp
  | bitvec n1 =>
    intro fwd bwd fwd' bwd' hgo hP1 hP2
    rw [LMonoTy.subst_bitvec] at hgo
    unfold LMonoTy.alphaEquivMap.go at hgo
    simp only [beq_self_eq_true, if_true, Option.some.injEq, Prod.mk.injEq] at hgo
    obtain ⟨hf, hbb⟩ := hgo
    subst hf hbb
    refine ⟨⟨hP1, hP2⟩, ?_⟩
    intro x hx
    simp only [LMonoTy.freeVars] at hx
    exact absurd hx (by simp)
  | tcons name1 args1 ih =>
    intro fwd bwd fwd' bwd' hgo hP1 hP2
    rw [LMonoTy.subst_unfold] at hgo
    unfold LMonoTy.alphaEquivMap.go at hgo
    by_cases hname : name1 != name1
    · rw [if_pos hname] at hgo; exact absurd hgo (by simp)
    · rw [if_neg hname] at hgo
      have hres := goList_bwd_inverts S args1 ih fwd bwd fwd' bwd' hgo hP1 hP2
      obtain ⟨hinv, hex⟩ := hres
      refine ⟨hinv, ?_⟩
      intro x hx
      simp only [LMonoTy.freeVars] at hx
      exact hex x hx

/-- Top-level specialization of `go_bwd_inverts`: when `alphaEquivMap monoty (subst S monoty)`
    succeeds with `bwdMap`, every free variable `x` of `monoty` has an image `y` with
    `subst S (ftvar x) = ftvar y` and `bwdMap[y]? = some x`. Obtained by running
    `go_bwd_inverts` at the empty accumulators (preconditions vacuous via `getElem?_empty`). -/
private theorem alphaEquivMap_self_subst_bwd (S : Subst) (monoty : LMonoTy)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap) :
    ∀ x ∈ LMonoTy.freeVars monoty,
      ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y ∧ bwdMap[y]? = some x := by
  unfold LMonoTy.alphaEquivMap at h_alpha
  cases hgo : LMonoTy.alphaEquivMap.go monoty (LMonoTy.subst S monoty) {} {} with
  | none => rw [hgo] at h_alpha; exact absurd h_alpha (by simp)
  | some fb =>
    obtain ⟨fwd0, bwd0⟩ := fb
    rw [hgo] at h_alpha
    simp only [Option.map_some, Option.some.injEq] at h_alpha
    subst h_alpha
    have hP1 : ∀ (y x : TyIdentifier),
        ({} : Std.HashMap TyIdentifier TyIdentifier)[y]? = some x →
        LMonoTy.subst S (.ftvar x) = .ftvar y := by
      intro y x hyx; rw [Std.HashMap.getElem?_empty] at hyx; exact absurd hyx (by simp)
    have hP2 : ∀ (x y : TyIdentifier),
        ({} : Std.HashMap TyIdentifier TyIdentifier)[x]? = some y →
        ({} : Std.HashMap TyIdentifier TyIdentifier)[y]? = some x := by
      intro x y hxy; rw [Std.HashMap.getElem?_empty] at hxy; exact absurd hxy (by simp)
    have hres := go_bwd_inverts S monoty {} {} fwd0 bwd0 hgo hP1 hP2
    exact hres.2

/-! ### `renameSubst`: the fresh→instantiation renaming

Built from `monoty.freeVars.eraseDups` as the inverse of the unifier `S` on those vars.
`alphaEquivMap` guarantees `subst S` acts as an injective variable renaming on `monoty`'s vars;
the lemmas below establish the lookup / `SubstWF` / inverse properties of `renameMap`. -/

/-- The new renaming scope as a plain `Map`. -/
private def renameMap (S : Subst) (vs : List TyIdentifier) : Map TyIdentifier LMonoTy :=
  vs.filterMap (fun x =>
    match LMonoTy.subst S (.ftvar x) with
    | .ftvar y => if x == y then none else some (y, LMonoTy.ftvar x)
    | _ => none)

/-- Injectivity of `σ : x ↦ (the y with subst S (ftvar x) = ftvar y)` on `freeVars monoty`,
    derived from the backward map being a function: if `subst S (ftvar x₁) = ftvar y` and
    `subst S (ftvar x₂) = ftvar y` with both `xᵢ ∈ freeVars monoty`, then `x₁ = x₂`. -/
private theorem alphaEquivMap_sigma_inj (S : Subst) (monoty : LMonoTy)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (x1 x2 y : TyIdentifier)
    (hx1 : x1 ∈ LMonoTy.freeVars monoty) (hx2 : x2 ∈ LMonoTy.freeVars monoty)
    (h1 : LMonoTy.subst S (.ftvar x1) = .ftvar y)
    (h2 : LMonoTy.subst S (.ftvar x2) = .ftvar y) :
    x1 = x2 := by
  obtain ⟨y1, hsy1, hby1⟩ := alphaEquivMap_self_subst_bwd S monoty bwdMap h_alpha x1 hx1
  obtain ⟨y2, hsy2, hby2⟩ := alphaEquivMap_self_subst_bwd S monoty bwdMap h_alpha x2 hx2
  rw [h1] at hsy1; rw [h2] at hsy2
  simp only [LMonoTy.ftvar.injEq] at hsy1 hsy2
  subst hsy1; subst hsy2
  rw [hby1] at hby2
  exact (Option.some.injEq _ _ ▸ hby2)

/-- Membership in the new `renameMap`: `(y, t) ∈ renameMap S vs` iff `t = ftvar x` for some
    `x ∈ vs` with `subst S (ftvar x) = ftvar y` and `x ≠ y`. Direct from `List.mem_filterMap`. -/
private theorem mem_renameMap_iff (S : Subst) (vs : List TyIdentifier)
    (y : TyIdentifier) (t : LMonoTy) :
    (y, t) ∈ Map.toList (renameMap S vs) ↔
      ∃ x, x ∈ vs ∧ t = LMonoTy.ftvar x ∧ LMonoTy.subst S (.ftvar x) = .ftvar y ∧ x ≠ y := by
  unfold renameMap Map.toList
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx_mem, hx_eq⟩
    cases hsub : LMonoTy.subst S (.ftvar x) with
    | ftvar y' =>
      rw [hsub] at hx_eq
      simp only at hx_eq
      by_cases hxy : x == y'
      · rw [if_pos hxy] at hx_eq; exact absurd hx_eq (by simp)
      · rw [if_neg hxy] at hx_eq
        simp only [Option.some.injEq, Prod.mk.injEq] at hx_eq
        obtain ⟨hy, ht⟩ := hx_eq
        refine ⟨x, hx_mem, ht.symm, ?_, ?_⟩
        · rw [hsub, hy]
        · rw [← hy]; simpa only [beq_iff_eq] using hxy
    | bitvec n => rw [hsub] at hx_eq; simp only at hx_eq; exact absurd hx_eq (by simp)
    | tcons nm ar => rw [hsub] at hx_eq; simp only at hx_eq; exact absurd hx_eq (by simp)
  · rintro ⟨x, hx_mem, ht, hsub, hxy⟩
    refine ⟨x, hx_mem, ?_⟩
    rw [hsub]
    simp only
    rw [if_neg (by simpa only [beq_iff_eq] using hxy), ht]

/-- A key of the new `renameMap` is the `S`-image of some instantiation variable. -/
private theorem mem_keys_renameMap (S : Subst) (vs : List TyIdentifier) (y : TyIdentifier)
    (h : y ∈ Map.keys (renameMap S vs)) :
    ∃ x, x ∈ vs ∧ LMonoTy.subst S (.ftvar x) = .ftvar y ∧ x ≠ y := by
  rw [Map.keys_eq_map_fst, List.mem_map] at h
  obtain ⟨p, hp_mem, hp_fst⟩ := h
  obtain ⟨y', t⟩ := p
  simp only at hp_fst; subst hp_fst
  obtain ⟨x, hx_mem, _, hsub, hxy⟩ := (mem_renameMap_iff S vs y' t).mp hp_mem
  exact ⟨x, hx_mem, hsub, hxy⟩

/-! ### New-shape `SubstWF` and inverse (the foregrounded composite-`S` building blocks) -/

/-- `Subst.freeVars` of the new `renameMap`: a free variable of its values is some `x ∈ vs`
    with `subst S (ftvar x) = ftvar y ≠ ftvar x`. (Values are exactly `ftvar x`.) -/
private theorem freeVars_renameMap (S : Subst) (vs : List TyIdentifier) (z : TyIdentifier)
    (h : z ∈ Subst.freeVars [renameMap S vs]) :
    ∃ y, LMonoTy.subst S (.ftvar z) = .ftvar y ∧ z ≠ y := by
  simp only [Subst.freeVars, Maps.values, List.append_nil] at h
  -- the single scope's values
  rw [show Map.values (renameMap S vs) = (renameMap S vs).map Prod.snd from by
    induction renameMap S vs with
    | nil => rfl
    | cons p t ih => cases p; simp only [Map.values, List.map_cons, ih]] at h
  obtain ⟨mty, hmty_mem, hmty_fv⟩ := List.mem_flatMap.mp h
  obtain ⟨p, hp_mem, hp_snd⟩ := List.mem_map.mp hmty_mem
  obtain ⟨ky, t⟩ := p
  obtain ⟨x, _, ht, hsub, hxy⟩ := (mem_renameMap_iff S vs ky t).mp hp_mem
  simp only at hp_snd
  rw [← hp_snd, ht] at hmty_fv
  simp only [LMonoTy.freeVars, List.mem_singleton] at hmty_fv
  subst hmty_fv
  exact ⟨ky, hsub, hxy⟩

/-- The free variables of `renameMap S vs`'s *values* lie in `vs`: every value is `ftvar x`
    for some `x ∈ vs`, so a value-occurring variable is exactly one of those `x`. -/
private theorem freeVars_renameMap_mem_vs (S : Subst) (vs : List TyIdentifier) (z : TyIdentifier)
    (h : z ∈ Subst.freeVars [renameMap S vs]) :
    z ∈ vs := by
  simp only [Subst.freeVars, Maps.values, List.append_nil] at h
  rw [show Map.values (renameMap S vs) = (renameMap S vs).map Prod.snd from by
    induction renameMap S vs with
    | nil => rfl
    | cons p t ih => cases p; simp only [Map.values, List.map_cons, ih]] at h
  obtain ⟨mty, hmty_mem, hmty_fv⟩ := List.mem_flatMap.mp h
  obtain ⟨p, hp_mem, hp_snd⟩ := List.mem_map.mp hmty_mem
  obtain ⟨ky, t⟩ := p
  obtain ⟨x, hx_mem, ht, _, _⟩ := (mem_renameMap_iff S vs ky t).mp hp_mem
  simp only at hp_snd
  rw [← hp_snd, ht] at hmty_fv
  simp only [LMonoTy.freeVars, List.mem_singleton] at hmty_fv
  subst hmty_fv
  exact hx_mem

/-- **`SubstWF` of the new renameSubst (single-scope).** Needs only idempotence of the
    well-formed `S`: a key `y` of `renameMap S vs` is `S`-fixed (`subst S (ftvar y) = ftvar y`,
    by idempotence applied to its preimage), while any value-occurrence of `y` would be a
    *moved* variable (`subst S (ftvar y) = ftvar y' ≠ ftvar y`) — contradiction.
    No inverse-pairing argument needed (the renaming is the inverse by construction). -/
private theorem substWF_renameMap_new (S : Subst) (hWF : SubstWF S) (vs : List TyIdentifier) :
    SubstWF [renameMap S vs] := by
  unfold SubstWF
  rw [List.all_eq_true]
  intro k hk_keys
  simp only [Maps.keys, List.append_nil] at hk_keys
  rw [decide_eq_true_eq]
  intro h_in_fv
  -- key side: subst S (ftvar x) = ftvar k for some x, x ≠ k.
  obtain ⟨x, _hx_mem, hsub_x, hxk⟩ := mem_keys_renameMap S vs k hk_keys
  -- value side: subst S (ftvar k) = ftvar y', k ≠ y'.
  obtain ⟨y', hsub_k, hky'⟩ := freeVars_renameMap S vs k h_in_fv
  -- idempotence: subst S (ftvar k) = subst S (subst S (ftvar x)) = subst S (ftvar x) = ftvar k.
  have h_idem : LMonoTy.subst S (LMonoTy.subst S (.ftvar x)) = LMonoTy.subst S (.ftvar x) :=
    LMonoTy.subst_idempotent S hWF (.ftvar x)
  rw [hsub_x] at h_idem
  -- so subst S (ftvar k) = ftvar k, contradicting subst S (ftvar k) = ftvar y' with k ≠ y'.
  rw [hsub_k] at h_idem
  simp only [LMonoTy.ftvar.injEq] at h_idem
  exact hky' h_idem.symm

/-- Generic: in a `Map` with nodup keys, membership determines `find?`. -/
private theorem Map.find?_of_mem_nodup {α β : Type} [DecidableEq α] (m : Map α β)
    (k : α) (v : β) (hmem : (k, v) ∈ Map.toList m) (hnd : (m.map Prod.fst).Nodup) :
    Map.find? m k = some v := by
  induction m with
  | nil => simp only [Map.toList] at hmem; exact absurd hmem (by simp)
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hk'_notin, hnd_rest⟩ := hnd
    simp only [Map.toList, List.mem_cons] at hmem
    rw [Map.find?]
    rcases hmem with h_hd | h_tl
    · simp only [Prod.mk.injEq] at h_hd; obtain ⟨hk, hv⟩ := h_hd
      rw [if_pos hk.symm, hv]
    · have hk'_ne : k' ≠ k := fun heq => hk'_notin (heq ▸ List.mem_map.mpr ⟨(k, v), h_tl, rfl⟩)
      rw [if_neg hk'_ne]; exact ih h_tl hnd_rest

/-- Keys of the new `renameMap` are nodup, from σ-injectivity on `vs` (⊆ `freeVars monoty`)
    plus `Nodup vs`: distinct preimages give distinct keys (σ injective), and the only
    preimage of a given key is unique. -/
private theorem renameMap_keys_nodup (monoty : LMonoTy) (S : Subst)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (vs : List TyIdentifier) (h_vs : ∀ v, v ∈ vs → v ∈ LMonoTy.freeVars monoty)
    (h_nd : vs.Nodup) :
    ((renameMap S vs).map Prod.fst).Nodup := by
  unfold renameMap
  induction vs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at h_nd
    obtain ⟨ha_notin, h_nd_rest⟩ := h_nd
    have h_vs_rest : ∀ v, v ∈ rest → v ∈ LMonoTy.freeVars monoty :=
      fun v hv => h_vs v (List.mem_cons_of_mem a hv)
    have ha_fv : a ∈ LMonoTy.freeVars monoty := h_vs a (List.mem_cons_self ..)
    rw [List.filterMap_cons]
    cases hsub : LMonoTy.subst S (.ftvar a) with
    | bitvec n => simp only; exact ih h_vs_rest h_nd_rest
    | tcons nm ar => simp only; exact ih h_vs_rest h_nd_rest
    | ftvar ya =>
      simp only
      by_cases haya : a == ya
      · rw [if_pos haya]; exact ih h_vs_rest h_nd_rest
      · rw [if_neg haya, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih h_vs_rest h_nd_rest⟩
        -- ya ∉ keys of the filtered rest: a key there is σ(a') for a' ∈ rest; σ inj ⟹ a = a' ∈ rest, contra.
        intro h_ya_in
        obtain ⟨p, hp_mem, hp_fst⟩ := List.mem_map.mp h_ya_in
        obtain ⟨a', ha'_mem, _, hsub', ha'ne⟩ := (mem_renameMap_iff S rest p.1 p.2).mp hp_mem
        rw [hp_fst] at hsub'
        have ha'_fv : a' ∈ LMonoTy.freeVars monoty := h_vs_rest a' ha'_mem
        have : a = a' := alphaEquivMap_sigma_inj S monoty bwdMap h_alpha a a' ya ha_fv ha'_fv hsub hsub'
        exact ha_notin (this ▸ ha'_mem)

/-- **Inverse leaf (new shape).** On a single free variable `x` of `monoty`, the new
    `renameMap` undoes `subst S`: `subst [renameMap S vs] (subst S (ftvar x)) = ftvar x`,
    where `vs` lists exactly `freeVars monoty`. Uses `alphaEquivMap_self_subst_bwd`
    (irreducible core: `subst S (ftvar x) = ftvar y`), σ-injectivity for the fixed-point
    case, and the find?-of-mem-nodup lookup for the moved case. -/
private theorem renameMap_inverse_ftvar (monoty : LMonoTy) (S : Subst)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (vs : List TyIdentifier) (h_vs : ∀ v, v ∈ vs ↔ v ∈ LMonoTy.freeVars monoty)
    (h_nd : vs.Nodup)
    (x : TyIdentifier) (hx : x ∈ LMonoTy.freeVars monoty) :
    LMonoTy.subst [renameMap S vs] (LMonoTy.subst S (.ftvar x)) = .ftvar x := by
  obtain ⟨y, hsy, _hby⟩ := alphaEquivMap_self_subst_bwd S monoty bwdMap h_alpha x hx
  have h_vs_sub : ∀ v, v ∈ vs → v ∈ LMonoTy.freeVars monoty := fun v hv => (h_vs v).mp hv
  have hnd := renameMap_keys_nodup monoty S bwdMap h_alpha vs h_vs_sub h_nd
  rw [hsy, LMonoTy.subst_unfold]
  simp only
  by_cases hxy : x = y
  · -- fixed point: y = x. No key equals y, else σ-injectivity forces the preimage = x.
    have h_none : Map.find? (renameMap S vs) y = none := by
      apply Map.findNone_eq_notmem_mapfst.mp
      intro hc
      obtain ⟨x', hx'_mem, hsub', hx'y⟩ := mem_keys_renameMap S vs y (by
        rw [Map.keys_eq_map_fst]; exact hc)
      have hx'_fv : x' ∈ LMonoTy.freeVars monoty := (h_vs x').mp hx'_mem
      have hxx' : x = x' := alphaEquivMap_sigma_inj S monoty bwdMap h_alpha x x' y hx hx'_fv hsy hsub'
      exact hx'y (hxy ▸ hxx'.symm ▸ rfl)
    rw [show Maps.find? [renameMap S vs] y = Map.find? (renameMap S vs) y from by
      simp only [Maps.find?, h_none], h_none, hxy]
  · -- moved: (y, ftvar x) ∈ renameMap, find? hits it.
    have hmem : (y, LMonoTy.ftvar x) ∈ Map.toList (renameMap S vs) :=
      (mem_renameMap_iff S vs y (.ftvar x)).mpr ⟨x, (h_vs x).mpr hx, rfl, hsy, hxy⟩
    have h_find : Map.find? (renameMap S vs) y = some (LMonoTy.ftvar x) :=
      Map.find?_of_mem_nodup (renameMap S vs) y (.ftvar x) hmem hnd
    rw [show Maps.find? [renameMap S vs] y = Map.find? (renameMap S vs) y from by
      simp only [Maps.find?, h_find], h_find]

/-- The new `renameMap` inverts the unification substitution on any monotype `t` whose free
    vars are all free in `monoty`: `subst [renameMap S vs] (subst S t) = t`, where `vs` lists
    exactly `freeVars monoty` (nodup). Structural lift of `renameMap_inverse_ftvar`. At the call
    site `t` is the declared output (a `destructArrow` component), free vars ⊆ `monoty`'s. -/
theorem renameMap_inverse (monoty t : LMonoTy) (S : Subst)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (vs : List TyIdentifier) (h_vs : ∀ v, v ∈ vs ↔ v ∈ LMonoTy.freeVars monoty)
    (h_nd : vs.Nodup)
    (h_sub : ∀ v, v ∈ LMonoTy.freeVars t → v ∈ LMonoTy.freeVars monoty) :
    LMonoTy.subst [renameMap S vs] (LMonoTy.subst S t) = t := by
  revert h_sub
  induction t with
  | ftvar x =>
    intro h_sub
    have hx : x ∈ LMonoTy.freeVars monoty :=
      h_sub x (by simp only [LMonoTy.freeVars, List.mem_singleton])
    exact renameMap_inverse_ftvar monoty S bwdMap h_alpha vs h_vs h_nd x hx
  | bitvec n =>
    intro _
    rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
  | tcons name args ih =>
    intro h_sub
    rw [LMonoTy.subst_unfold S (.tcons name args)]
    rw [LMonoTy.subst_unfold [renameMap S vs] (.tcons name (args.map (LMonoTy.subst S)))]
    simp only [List.map_map]
    congr 1
    have h_args : ∀ a ∈ args,
        (LMonoTy.subst [renameMap S vs] ∘ LMonoTy.subst S) a = a := by
      intro a ha
      simp only [Function.comp_apply]
      refine ih a ha (fun v hv => h_sub v ?_)
      simp only [LMonoTy.freeVars]
      exact LMonoTys.freeVars_mem_subset ha hv
    rw [List.map_congr_left h_args]
    simp only [List.map_id_fun', id_eq]

/-- Forward freeVars-monotonicity through substitution: a free var of `subst S (ftvar x)`,
    for `x` free in `mty`, is free in `subst S mty`. -/
private theorem LMonoTy.mem_freeVars_subst_of_mem (S : Subst) (mty : LMonoTy) (x : TyIdentifier)
    (hx : x ∈ LMonoTy.freeVars mty) :
    ∀ k, k ∈ LMonoTy.freeVars (LMonoTy.subst S (.ftvar x)) →
      k ∈ LMonoTy.freeVars (LMonoTy.subst S mty) := by
  intro k hk
  induction mty with
  | ftvar z =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at hx; subst hx; exact hk
  | bitvec n => simp only [LMonoTy.freeVars] at hx; exact absurd hx (by simp)
  | tcons name args ih =>
    simp only [LMonoTy.freeVars] at hx
    obtain ⟨a, ha_mem, ha_fv⟩ := LMonoTys.freeVars_exists hx
    rw [LMonoTy.subst_unfold]
    simp only [LMonoTy.freeVars]
    have ih_a := ih a ha_mem ha_fv
    exact LMonoTys.freeVars_mem_subset (List.mem_map_of_mem (f := LMonoTy.subst S) ha_mem) ih_a

/-- When unify solves `(output_mty, bodyty)` and alphaEquivMap provides a bwdMap,
    `subst userSubst (subst renameSubst (subst S bodyty)) = subst userSubst output_mty`.
    The `h_sub` precondition (output free vars ⊆ monoty free vars) lets
    `alphaEquivMap_renameSubst_inverse` apply; it holds since `output_mty` is a
    `monoty.destructArrow` component. -/
theorem typeCheck_body_type_eq
    (monoty output_mty bodyty : LMonoTy)
    (S : Subst)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (userSubst : Subst)
    (h_unify_eq : LMonoTy.subst S output_mty = LMonoTy.subst S bodyty)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (h_sub : ∀ v, v ∈ LMonoTy.freeVars output_mty → v ∈ LMonoTy.freeVars monoty) :
    LMonoTy.subst userSubst
        (LMonoTy.subst [renameMap S monoty.freeVars.eraseDups] (LMonoTy.subst S bodyty)) =
      LMonoTy.subst userSubst output_mty := by
  have h_inv := renameMap_inverse monoty output_mty S bwdMap h_alpha
    monoty.freeVars.eraseDups (fun v => List.mem_eraseDups) (eraseDups_Nodup _) h_sub
  rw [← h_unify_eq, h_inv]

/-- The full body-typing chain: starting from a resolved, `AbsWF`, well-typed body,
    apply the three substitutions (`unify`, `rename`, `user`) and land at the
    declared output type. Abstracts plan steps 1–7; used identically in all measure
    branches of `bodyTyped`. -/
theorem bodyTyped_chain {T : LExprParams} [DecidableEq T.IDMeta]
    (et₀ : LExprT T.mono) (S userSubst : Subst)
    (monoty output_mty : LMonoTy)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_wf : LExprT.AbsWF et₀)
    (h_typed : LExpr.HasTypeA [] et₀.unresolved (et₀.toLMonoTy))
    (h_unify_eq : LMonoTy.subst S output_mty = LMonoTy.subst S et₀.toLMonoTy)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (h_sub : ∀ v, v ∈ LMonoTy.freeVars output_mty → v ∈ LMonoTy.freeVars monoty) :
    LExpr.HasTypeA []
      (applySubstT
        (applySubstT
          (applySubstT et₀ S)
          [renameMap S monoty.freeVars.eraseDups])
        userSubst).unresolved
      (LMonoTy.subst userSubst output_mty) := by
  let renameSubst : Subst := [renameMap S monoty.freeVars.eraseDups]
  show LExpr.HasTypeA []
      (applySubstT (applySubstT (applySubstT et₀ S) renameSubst) userSubst).unresolved
      (LMonoTy.subst userSubst output_mty)
  -- Step 1→2: apply S
  have h1 := applySubstT_unresolved_HasTypeA et₀ S [] h_wf h_typed
  rw [List.map_nil] at h1
  -- Step 4: apply renameSubst
  have h_wf1 := applySubstT_AbsWF et₀ S h_wf
  have h2 := applySubstT_unresolved_HasTypeA (applySubstT et₀ S) renameSubst [] h_wf1 h1
  rw [List.map_nil] at h2
  -- Step 6: apply userSubst
  have h_wf2 := applySubstT_AbsWF (applySubstT et₀ S) renameSubst h_wf1
  have h3 := applySubstT_unresolved_HasTypeA
    (applySubstT (applySubstT et₀ S) renameSubst) userSubst [] h_wf2 h2
  rw [List.map_nil] at h3
  -- Rewrite the type: peel the three toLMonoTy substitutions, then use the
  -- alpha/unify type-equality.
  rw [applySubstT_toLMonoTy, applySubstT_toLMonoTy, applySubstT_toLMonoTy] at h3
  have h_eq := typeCheck_body_type_eq monoty output_mty et₀.toLMonoTy S bwdMap userSubst
    h_unify_eq h_alpha h_sub
  rw [h_eq] at h3
  exact h3

/-- The internal typing environment the body typechecker builds (empty scope + monomorphic input
    signature) is well-formed and aliases-resolved, so the measure branches of `bodyTyped` can
    invoke `resolve_HasTypeA`/`resolve_AbsWF`. -/
theorem typeCheck_internalEnv_wf
    (type : LTy) (C : LContext CoreLParams) (Env : TEnv Unit)
    (monoty : LMonoTy) (Env_inst : TEnv Unit)
    (pairs : List (CoreLParams.Identifier × LMonoTy))
    (h_inst : LTy.instantiateWithCheck type C Env = .ok (monoty, Env_inst))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_sig : ∀ p ∈ pairs, p.2 ∈ monoty.destructArrow) :
    TEnvWF (T := CoreLParams) (Env_inst.pushEmptyContext.addInNewestContext (T := CoreLParams)
        (pairs.map (fun p => (p.1, LTy.forAll [] p.2))))
    ∧ TContext.AliasesResolved (Env_inst.pushEmptyContext.addInNewestContext (T := CoreLParams)
        (pairs.map (fun p => (p.1, LTy.forAll [] p.2)))).context := by
  have h_envwf_inst : TEnvWF (T := CoreLParams) Env_inst :=
    LTy_instantiateWithCheck_TEnvWF (T := CoreLParams) type C Env monoty Env_inst h_inst h_wf
  have h_ctx_inst : Env_inst.context = Env.context :=
    LTy_instantiateWithCheck_context (T := CoreLParams) type C Env monoty Env_inst h_inst
  have h_resolved_inst : TContext.AliasesResolved Env_inst.context := by
    rw [h_ctx_inst]; exact h_resolved
  have h_fresh : ∀ p ∈ pairs,
      ∀ v, v ∈ LMonoTy.freeVars p.2 →
        ∀ n, n ≥ Env_inst.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
    intro p hp v hv n hn
    exact instantiateWithCheck_destructArrow_mem_fresh (T := CoreLParams) type C Env monoty Env_inst
      h_inst p.2 (h_sig p hp) v hv n hn
  have h_envwf_push : TEnvWF (T := CoreLParams) Env_inst.pushEmptyContext :=
    TEnvWF.of_pushEmptyContext (T := CoreLParams) Env_inst h_envwf_inst
  have h_gen_push : Env_inst.pushEmptyContext.genEnv.genState = Env_inst.genEnv.genState := rfl
  have h_fresh_push : ∀ p ∈ pairs,
      ∀ v, v ∈ LMonoTy.freeVars p.2 →
        ∀ n, n ≥ Env_inst.pushEmptyContext.genEnv.genState.tyGen →
          v ≠ TState.tyPrefix ++ toString n := by
    rw [h_gen_push]; exact h_fresh
  refine ⟨?_, ?_⟩
  · exact TEnvWF.of_addInNewestContext_mono (T := CoreLParams) Env_inst.pushEmptyContext
      pairs h_envwf_push h_fresh_push
  · exact TContext.AliasesResolved.of_addInNewestContext (T := CoreLParams) _ _
      (TContext.AliasesResolved.of_pushEmptyContext (T := CoreLParams) Env_inst h_resolved_inst)

/-- WF-only variant of `typeCheck_internalEnv_wf`: the internal body-resolution
    environment is well-formed, needing only `TEnvWF Env` (no `AliasesResolved`).
    This is what `resolve_HasType_core` requires, and unlike the bundled helper it
    is available in `_instantiated`, which only carries `checkContextTypesClosed`. -/
theorem typeCheck_internalEnv_TEnvWF
    (type : LTy) (C : LContext CoreLParams) (Env : TEnv Unit)
    (monoty : LMonoTy) (Env_inst : TEnv Unit)
    (pairs : List (CoreLParams.Identifier × LMonoTy))
    (h_inst : LTy.instantiateWithCheck type C Env = .ok (monoty, Env_inst))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_sig : ∀ p ∈ pairs, p.2 ∈ monoty.destructArrow) :
    TEnvWF (T := CoreLParams) (Env_inst.pushEmptyContext.addInNewestContext (T := CoreLParams)
        (pairs.map (fun p => (p.1, LTy.forAll [] p.2)))) := by
  have h_envwf_inst : TEnvWF (T := CoreLParams) Env_inst :=
    LTy_instantiateWithCheck_TEnvWF (T := CoreLParams) type C Env monoty Env_inst h_inst h_wf
  have h_fresh : ∀ p ∈ pairs,
      ∀ v, v ∈ LMonoTy.freeVars p.2 →
        ∀ n, n ≥ Env_inst.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
    intro p hp v hv n hn
    exact instantiateWithCheck_destructArrow_mem_fresh (T := CoreLParams) type C Env monoty Env_inst
      h_inst p.2 (h_sig p hp) v hv n hn
  have h_envwf_push : TEnvWF (T := CoreLParams) Env_inst.pushEmptyContext :=
    TEnvWF.of_pushEmptyContext (T := CoreLParams) Env_inst h_envwf_inst
  have h_gen_push : Env_inst.pushEmptyContext.genEnv.genState = Env_inst.genEnv.genState := rfl
  have h_fresh_push : ∀ p ∈ pairs,
      ∀ v, v ∈ LMonoTy.freeVars p.2 →
        ∀ n, n ≥ Env_inst.pushEmptyContext.genEnv.genState.tyGen →
          v ≠ TState.tyPrefix ++ toString n := by
    rw [h_gen_push]; exact h_fresh
  exact TEnvWF.of_addInNewestContext_mono (T := CoreLParams) Env_inst.pushEmptyContext
    pairs h_envwf_push h_fresh_push

/-! ### Per-field helper lemmas for annotated soundness -/

/-- The first projection of a zipped list is a sublist of the first list. -/
theorem List.map_fst_zip_sublist {α β : Type} (a : List α) (b : List β) :
    ((a.zip b).map Prod.fst).Sublist a := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons]
      exact (ih ys).cons₂ x

/-- The second projection of a zipped list is a sublist of the second list. -/
theorem List.map_snd_zip_sublist {α β : Type} (a : List α) (b : List β) :
    ((a.zip b).map Prod.snd).Sublist b := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons]
      exact (ih ys).cons₂ y

theorem Function.typeCheck_inputsNodup (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func'.inputs.keys.Nodup := by
  have h_nodup : func.inputs.keys.Nodup := Function.typeCheck_inputs_nodup C Env func func' Env' h
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  -- In every `.ok` branch, `func'.inputs = map (fun x => (x.fst, _)) (func.inputs.keys.zip _)`,
  -- so its keys are a sublist of `func.inputs.keys`, which is `Nodup`.
  have h_close : ∀ (g : CoreLParams.Identifier × LMonoTy → CoreLParams.Identifier × LMonoTy)
      (mtys : List LMonoTy) (hg : ∀ p, (g p).fst = p.fst),
      (ListMap.keys ((func.inputs.keys.zip mtys).map g)).Nodup := by
    intro g mtys hg
    rw [ListMap.keys_eq_map_fst, List.map_map]
    have h_eq : (Prod.fst ∘ g) = (fun p : CoreLParams.Identifier × LMonoTy => p.fst) := by
      funext p; simp [Function.comp, hg p]
    rw [h_eq]
    exact (List.map_fst_zip_sublist func.inputs.keys mtys).nodup h_nodup
  split at h
  · -- body = none
    split at h
    · simp at h
    · cases h
      exact h_close _ _ (fun _ => rfl)
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    rename_i alphaMap h_alphaMap
    elim_err h
    rename_i bwdMap h_alpha
    elim_err h
    elim_err h
    elim_err h
    elim_err h
    split at h
    · -- measure = some
      split at h
      · -- fvar
        elim_err h; cases h
        exact h_close _ _ (fun _ => rfl)
      · -- non-fvar
        elim_err h
        rename_i v_measure h_measure_resolve
        elim_err h
        rename_i h_measure_ty
        elim_err h; cases h
        exact h_close _ _ (fun _ => rfl)
    · -- measure = none
      elim_err h; cases h
      exact h_close _ _ (fun _ => rfl)

theorem Function.typeCheck_typeArgsNodup (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func'.typeArgs.Nodup := by
  have h_nodup : func.typeArgs.Nodup := by
    simp only [Function.typeCheck, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i type h_type
    exact LFunc.type_typeArgs_nodup func type h_type
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  -- In every `.ok` branch, `func'.typeArgs = map Prod.snd (_ .zip func.typeArgs)`,
  -- a sublist of `func.typeArgs`, which is `Nodup`.
  have h_close : ∀ (vs : List TyIdentifier),
      (List.map (fun x => x.snd) (vs.zip func.typeArgs)).Nodup := by
    intro vs
    exact (List.map_snd_zip_sublist vs func.typeArgs).nodup h_nodup
  split at h
  · -- body = none
    split at h
    · simp at h
    · cases h
      exact h_close _
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    rename_i alphaMap h_alphaMap
    elim_err h
    rename_i bwdMap h_alpha
    elim_err h
    elim_err h
    elim_err h
    elim_err h
    split at h
    · -- measure = some
      split at h
      · elim_err h; cases h
        exact h_close _
      · elim_err h
        rename_i v_measure h_measure_resolve
        elim_err h
        rename_i h_measure_ty
        elim_err h; cases h
        exact h_close _
    · -- measure = none
      elim_err h; cases h
      exact h_close _

/-- **D1 (rename-image).** Substituting the renaming `userSubst = [ids.zip (map ftvar tgts)]`
    into a monotype `W` whose free vars are all keys (`⊆ ids`) yields a monotype whose free
    vars are all renamed targets (`∈ (ids.zip tgts).map Prod.snd`). When `ids.length ≤
    tgts.length` (coverage), the keys are exactly `ids` and the targets are exactly
    `func'.typeArgs`. Reduces to the existing `LMonoTy.freeVars_subst_closed` with the fresh
    set instantiated to `tgts.take ids.length`. -/
private theorem freeVars_rename_subset
    (ids tgts : List TyIdentifier) (W : LMonoTy)
    (h_cov : ids.length ≤ tgts.length)
    (h_closed : ∀ v, v ∈ LMonoTy.freeVars W → v ∈ ids) :
    ∀ v, v ∈ LMonoTy.freeVars
        (LMonoTy.subst [(ids.zip tgts).map (fun x => (x.1, LMonoTy.ftvar x.2))] W) →
      v ∈ (ids.zip tgts).map Prod.snd := by
  -- Projecting the zip's snd component yields exactly the (truncated) target list.
  have e1 : ∀ (I T : List TyIdentifier), (I.zip T).map Prod.snd = T.take I.length := by
    intro I
    induction I with
    | nil => simp
    | cons a rest ih =>
      intro T
      cases T with
      | nil => simp
      | cons t trest =>
        simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.take_succ_cons, ih]
  -- The renaming substitution map equals the `zip ids (map ftvar …)` form `freeVars_subst_closed`
  -- expects, with the fresh set being `tgts.take ids.length`.
  have e2 : ∀ (I T : List TyIdentifier),
      (I.zip T).map (fun x => (x.1, LMonoTy.ftvar x.2)) =
        List.zip I (List.map LMonoTy.ftvar (T.take I.length)) := by
    intro I
    induction I with
    | nil => simp
    | cons a rest ih =>
      intro T
      cases T with
      | nil => simp
      | cons t trest =>
        simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.take_succ_cons, ih]
  intro v hv
  rw [e1 ids tgts]
  have h_len : (tgts.take ids.length).length = ids.length := by
    rw [List.length_take]; omega
  rw [e2 ids tgts] at hv
  -- `freeVars_subst_closed` requires a non-empty substitution scope. When `ids = []`,
  -- `h_closed` forces `W.freeVars = []`, so the conclusion is vacuous.
  cases ids with
  | nil =>
    simp only [List.length_nil, List.take_zero, List.zip_nil_left, List.map_nil] at hv
    rw [LMonoTy.subst_emptyS (by simp [Subst.hasEmptyScopes, Map.isEmpty])] at hv
    exact (h_closed v hv)
  | cons a rest =>
    have hSNE : Subst.hasEmptyScopes
        [List.zip (a :: rest) (List.map LMonoTy.ftvar (tgts.take (a :: rest).length))] = false := by
      cases h_tgts : tgts.take (a :: rest).length with
      | nil => rw [h_tgts] at h_len; simp at h_len
      | cons f frest => rfl
    exact LMonoTy.freeVars_subst_closed (a :: rest) (tgts.take (a :: rest).length) h_len W h_closed v hv

/-- **D2 (coverage).** The distinct free vars of an `LTy.instantiateWithCheck` output number
    at most the scheme's bound variables. The output's free vars are all freshly generated
    (`freeVars_subst_closed` + `resolveAliases` doesn't grow freeVars), and the fresh set is
    nodup with `length = boundVars.length`. -/
private theorem instantiateWithCheck_freeVars_eraseDups_length_le
    (type : LTy) (C : LContext CoreLParams) (Env : TEnv Unit)
    (monoty : LMonoTy) (Env' : TEnv Unit)
    (h : LTy.instantiateWithCheck type C Env = .ok (monoty, Env'))
    (h_closed : LTy.freeVars type = [])
    (h_aw : TContext.AliasesWF Env.context) :
    monoty.freeVars.eraseDups.length ≤ (LTy.boundVars type).length := by
  rcases type with ⟨xs, body⟩
  simp only [LTy.boundVars]
  -- The scheme is closed: every free var of the body is a bound var.
  have h_sub : ∀ v, v ∈ LMonoTy.freeVars body → v ∈ xs := by
    simp only [LTy.freeVars] at h_closed
    intro v hv
    rw [List.removeAll, List.filter_eq_nil_iff] at h_closed
    have hf := h_closed v hv
    simp_all
  -- Key: the instantiate-output free vars are covered by a fresh set whose length is `xs.length`.
  have h_fresh_cover : ∃ freshtvs : List TyIdentifier,
      freshtvs.length = xs.length ∧ ∀ v, v ∈ LMonoTy.freeVars monoty → v ∈ freshtvs := by
    simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_ra
    obtain ⟨mty_ra, Env_ra⟩ := v1
    elim_errs h
    cases h
    simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
    elim_err h_ra
    rename_i v2 h_inst
    obtain ⟨mty_inst, genEnv1⟩ := v2
    dsimp only at h_ra
    have h_ctx_inst : genEnv1.context = Env.genEnv.context :=
      LTy.instantiate_context (LTy.forAll xs body) Env.genEnv mty_inst genEnv1 h_inst
    have h_aw_ra : TContext.AliasesWF
        ({ genEnv := genEnv1, stateSubstInfo := Env.stateSubstInfo } : TEnv Unit).context := by
      simp only [TEnv.context]; rw [h_ctx_inst]; exact h_aw
    have h_ra_sub : ∀ v, v ∈ mty_ra.freeVars → v ∈ mty_inst.freeVars :=
      LMonoTy_resolveAliases_freeVars_subset (T := CoreLParams) mty_inst
        { genEnv := genEnv1, stateSubstInfo := Env.stateSubstInfo } mty_ra Env_ra h_ra h_aw_ra
    have h_inst_cover : ∃ freshtvs : List TyIdentifier,
        freshtvs.length = xs.length ∧ ∀ v, v ∈ mty_inst.freeVars → v ∈ freshtvs := by
      cases xs with
      | nil =>
        refine ⟨[], rfl, ?_⟩
        simp only [LTy.instantiate] at h_inst
        cases h_inst
        intro v hv
        exact h_sub v hv
      | cons a rest =>
        simp only [LTy.instantiate, Bind.bind, Except.bind] at h_inst
        elim_err h_inst
        rename_i v1 h_gen
        obtain ⟨freshtvs, genEnv2⟩ := v1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
        obtain ⟨h_mty, h_env⟩ := h_inst
        have h_flen : freshtvs.length = (a :: rest).length :=
          TGenEnv.genTyVars_length (a :: rest).length Env.genEnv freshtvs genEnv2 h_gen
        refine ⟨freshtvs, h_flen, ?_⟩
        rw [← h_mty]
        intro v hv
        have hSNE : Subst.hasEmptyScopes
            [List.zip (a :: rest) (List.map LMonoTy.ftvar freshtvs)] = false := by
          cases freshtvs with
          | nil => simp at h_flen
          | cons f frest => rfl
        exact LMonoTy.freeVars_subst_closed (a :: rest) freshtvs h_flen body h_sub v hv
    obtain ⟨freshtvs, h_len, h_cover_inst⟩ := h_inst_cover
    exact ⟨freshtvs, h_len, fun v hv => h_cover_inst v (h_ra_sub v hv)⟩
  obtain ⟨freshtvs, h_len, h_cover⟩ := h_fresh_cover
  -- `eraseDups` is nodup and ⊆ freshtvs, so its length ≤ freshtvs.length = xs.length.
  have h_nodup : monoty.freeVars.eraseDups.Nodup := eraseDups_Nodup _
  have h_sub_fresh : monoty.freeVars.eraseDups ⊆ freshtvs := by
    intro v hv
    exact h_cover v (List.mem_eraseDups.mp hv)
  calc monoty.freeVars.eraseDups.length
      ≤ freshtvs.length := List.subset_nodup_length h_nodup h_sub_fresh
    _ = xs.length := h_len

/-- Free vars of an `instantiateWithCheck` output of a **closed** scheme are all
    generator names `$__ty<k>`. The fresh vars come from `genTyVars`
    (`genTyVars_is_genName`); alias resolution does not grow free vars
    (`LMonoTy_resolveAliases_freeVars_subset`); and closedness forces every body
    free var into the substituted (bound) variables, so the output's free vars are
    a subset of the fresh generator set. -/
theorem instantiateWithCheck_freeVars_gen_prefixed
    (type : LTy) (C : LContext CoreLParams) (Env : TEnv Unit)
    (monoty : LMonoTy) (Env' : TEnv Unit)
    (h : LTy.instantiateWithCheck type C Env = .ok (monoty, Env'))
    (h_closed : LTy.freeVars type = [])
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v, v ∈ LMonoTy.freeVars monoty → ∃ (k: Nat), v = TState.tyPrefix ++ toString k := by
  rcases type with ⟨xs, body⟩
  -- The scheme is closed: every free var of the body is a bound var.
  have h_sub : ∀ v, v ∈ LMonoTy.freeVars body → v ∈ xs := by
    simp only [LTy.freeVars] at h_closed
    intro v hv
    rw [List.removeAll, List.filter_eq_nil_iff] at h_closed
    have hf := h_closed v hv
    simp_all
  -- Same cover as `instantiateWithCheck_freeVars_eraseDups_length_le`, but tracking
  -- that the fresh set consists of generator names.
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_ra
  obtain ⟨mty_ra, Env_ra⟩ := v1
  elim_errs h
  cases h
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
  elim_err h_ra
  rename_i v2 h_inst
  obtain ⟨mty_inst, genEnv1⟩ := v2
  dsimp only at h_ra
  have h_ctx_inst : genEnv1.context = Env.genEnv.context :=
    LTy.instantiate_context (LTy.forAll xs body) Env.genEnv mty_inst genEnv1 h_inst
  have h_aw_ra : TContext.AliasesWF
      ({ genEnv := genEnv1, stateSubstInfo := Env.stateSubstInfo } : TEnv Unit).context := by
    simp only [TEnv.context]; rw [h_ctx_inst]; exact h_aw
  have h_ra_sub : ∀ v, v ∈ mty_ra.freeVars → v ∈ mty_inst.freeVars :=
    LMonoTy_resolveAliases_freeVars_subset (T := CoreLParams) mty_inst
      { genEnv := genEnv1, stateSubstInfo := Env.stateSubstInfo } mty_ra Env_ra h_ra h_aw_ra
  -- Every free var of the instantiate output is a generator name.
  have h_inst_gen : ∀ v, v ∈ mty_inst.freeVars → ∃ (k: Nat), v = TState.tyPrefix ++ toString k := by
    cases xs with
    | nil =>
      -- closed monomorphic: freeVars body ⊆ [] (vacuous)
      simp only [LTy.instantiate] at h_inst
      cases h_inst
      intro v hv
      exact absurd (h_sub v hv) (by simp)
    | cons a rest =>
      simp only [LTy.instantiate, Bind.bind, Except.bind] at h_inst
      elim_err h_inst
      rename_i v1 h_gen
      obtain ⟨freshtvs, genEnv2⟩ := v1
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
      obtain ⟨h_mty, h_env⟩ := h_inst
      have h_flen : freshtvs.length = (a :: rest).length :=
        TGenEnv.genTyVars_length (a :: rest).length Env.genEnv freshtvs genEnv2 h_gen
      rw [← h_mty]
      intro v hv
      have hSNE : Subst.hasEmptyScopes
          [List.zip (a :: rest) (List.map LMonoTy.ftvar freshtvs)] = false := by
        cases freshtvs with
        | nil => simp at h_flen
        | cons f frest => rfl
      have h_v_fresh : v ∈ freshtvs :=
        LMonoTy.freeVars_subst_closed (a :: rest) freshtvs h_flen body h_sub v hv
      obtain ⟨k, _, h_eq⟩ := TGenEnv.genTyVars_is_genName (T := CoreLParams)
        (a :: rest).length Env.genEnv freshtvs genEnv2 h_gen v h_v_fresh
      exact ⟨k, h_eq⟩
  intro v hv
  exact h_inst_gen v (h_ra_sub v hv)

theorem Function.typeCheck_noUndeclaredVars (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func'.output func'.inputs.values) →
      v ∈ func'.typeArgs := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  -- Coverage: distinct free vars of `monoty` number at most `type.boundVars` = `func.typeArgs`.
  have h_aw : TContext.AliasesWF Env.context := h_wf.aliasesWF
  have h_bv : LTy.boundVars type = func.typeArgs :=
    LFunc.type_boundVars_eq_typeArgs (T := CoreLParams) func type h_type
  have h_closed : LTy.freeVars type = [] := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_undecl
    exact h_undecl
  have h_cov : v_inst.fst.freeVars.eraseDups.length ≤ func.typeArgs.length := by
    rw [← h_bv]
    exact instantiateWithCheck_freeVars_eraseDups_length_le type C Env v_inst.fst v_inst.snd
      (by rw [Prod.eta]; exact h_inst) h_closed h_aw
  -- Every free var of `monoty` is a key (`∈ ids`) of `userSubst`.
  have h_in_ids : ∀ v, v ∈ v_inst.fst.freeVars → v ∈ v_inst.fst.freeVars.eraseDups :=
    fun v hv => List.mem_eraseDups.mpr hv
  -- `h_close` works on the whole `subst userSubst (mkArrow' RO ins)` term; its free vars are all in
  -- `monoty.freeVars` (inputs are destructArrow slices, RO is the reconstructed output), so D1 applies.
  have h_close : ∀ v, v ∈ LMonoTy.freeVars
      (LMonoTy.subst
          [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
        (LMonoTy.mkArrow'
          (((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
              (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
            (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast)
          ((func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)).map
            (fun x => x.2)))) →
      v ∈ (v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map Prod.snd := by
    intro v hv
    refine freeVars_rename_subset v_inst.fst.freeVars.eraseDups func.typeArgs _ h_cov ?_ v hv
    intro w hw
    apply h_in_ids
    rw [LMonoTy.freeVars_mkArrow', List.mem_append] at hw
    cases hw with
    | inl h_args =>
      -- w is a free var of some input monotype (a `take` of `destructArrow`).
      obtain ⟨x, hx_mem, hx_w⟩ := LMonoTys.freeVars_exists h_args
      simp only [List.mem_map] at hx_mem
      obtain ⟨p, hp_mem, hp_eq⟩ := hx_mem
      have h_p2_destr : p.2 ∈ v_inst.fst.destructArrow :=
        List.mem_of_mem_take (List.of_mem_zip hp_mem).2
      rw [← hp_eq] at hx_w
      exact LMonoTy.mem_destructArrow_freeVars_subset v_inst.fst p.2 h_p2_destr hx_w
    | inr h_ret =>
      -- `h_ret : w ∈ freeVars RO`; `RO` is exactly the reconstructed output.
      exact LMonoTy.freeVars_reconstructedOutput_subset v_inst.fst func.inputs.keys.length w h_ret
  -- `mkArrow' func'.output func'.inputs.values = subst userSubst (mkArrow' RO ins)` by
  -- `subst_mkArrow'` (output) and `ListMap.values`/`map_map` (inputs); `h_close` then closes.
  have h_finish : ∀ v, v ∈ LMonoTy.freeVars
      ((LMonoTy.subst
          [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
          (((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
              (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
            (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast)).mkArrow'
        ((func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)).map
          (fun x => LMonoTy.subst
            [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
            x.2))) →
      v ∈ (v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map Prod.snd := by
    intro v hv
    apply h_close v
    rw [subst_mkArrow', List.map_map]
    exact hv
  split at h
  · -- body = none
    split at h
    · simp at h
    · cases h
      intro v hv
      rw [ListMap.values_eq_map_snd, List.map_map] at hv
      exact h_finish v hv
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    rename_i alphaMap h_alphaMap
    elim_err h
    rename_i bwdMap h_alpha
    elim_err h
    elim_err h
    elim_err h
    elim_err h
    split at h
    · split at h
      · elim_err h; cases h
        intro v hv
        rw [ListMap.values_eq_map_snd, List.map_map] at hv
        exact h_finish v hv
      · elim_err h
        rename_i v_measure h_measure_resolve
        elim_err h
        rename_i h_measure_ty
        elim_err h; cases h
        intro v hv
        rw [ListMap.values_eq_map_snd, List.map_map] at hv
        exact h_finish v hv
    · elim_err h; cases h
      intro v hv
      rw [ListMap.values_eq_map_snd, List.map_map] at hv
      exact h_finish v hv

theorem Function.typeCheck_bodyTyped_annotated (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ body, func'.body = some body →
      LExpr.HasTypeA [] body (func'.output) := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  split at h
  · -- body = none: func'.body = func.body = none, so bodyTyped is vacuous
    rename_i h_body_none
    split at h
    · simp at h
    · cases h
      intro body h_eq
      simp only [h_body_none, reduceCtorEq] at h_eq
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    -- alphaEquivMap + measure handling
    split at h <;> try contradiction
    · -- alphaEquivMap = some
      rename_i alphaMap h_alphaMap
      elim_err h
      rename_i bwdMap h_alpha
      -- The input pairs inserted into the internal env, and the reconstructed
      -- output monotype. Both are built from `v_inst.fst.destructArrow`.
      have h_pairs_sig : ∀ p ∈ func.inputs.keys.zip
          (List.take func.inputs.keys.length v_inst.fst.destructArrow),
          p.2 ∈ v_inst.fst.destructArrow := by
        intro p hp
        exact List.mem_of_mem_take (List.of_mem_zip hp).2
      -- Internal env WF + aliases-resolved, via the packaged helper.
      have h_internal := typeCheck_internalEnv_wf type C Env v_inst.fst v_inst.snd
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
        h_inst h_wf h_resolved h_pairs_sig
      obtain ⟨h_envwf_internal, h_resolved_internal⟩ := h_internal
      -- Body resolution facts on the internal env. The internal env in `h_resolve`
      -- is defeq to the one in `h_internal` (`inputMonoSignature` unfolds to the
      -- mapped pairs).
      have h_body_wf : LExprT.AbsWF v_resolve.fst :=
        resolve_AbsWF body v_resolve.fst C _ v_resolve.snd
          (by rw [Prod.eta]; exact h_resolve) h_envwf_internal h_fwf
      have h_body_typed : LExpr.HasTypeA [] v_resolve.fst.unresolved v_resolve.fst.toLMonoTy :=
        resolve_HasTypeA body v_resolve.fst C _ v_resolve.snd
          (by rw [Prod.eta]; exact h_resolve) h_envwf_internal h_fwf h_resolved_internal
      -- Unify soundness gives the type equality the chain needs.
      have h_unify' : Constraints.unify
          [(LMonoTy.mkArrow'
              ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
            v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo = .ok v_unify := by
        cases hc : Constraints.unify
            [(LMonoTy.mkArrow'
                ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                  (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
                (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
              v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo with
        | error e => rw [hc] at h_unify; simp [Except.mapError] at h_unify
        | ok w => rw [hc] at h_unify; simp [Except.mapError] at h_unify; rw [h_unify]
      have h_unify_eq := Constraints.unify_sound _ _ _ h_unify' _ List.mem_cons_self
      -- The full body-typing chain. The renaming is now built directly from
      -- `v_inst.fst.freeVars.eraseDups` (the new checker shape), with `alphaMap` as the
      -- bwd witness for the inverse property.
      have h_chain := bodyTyped_chain v_resolve.fst v_unify.subst
        [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
        v_inst.fst _ alphaMap h_body_wf h_body_typed h_unify_eq
        h_alphaMap
        (LMonoTy.freeVars_reconstructedOutput_subset v_inst.fst func.inputs.keys.length)
      -- measure cases: split on func.measure then on fvar/non-fvar.
      -- All three branches define the same body/output, so they all close via h_chain.
      elim_err h
      elim_err h
      elim_err h
      elim_err h
      split at h
      · -- measure = some
        split at h
        · -- fvar case
          elim_err h; cases h
          intro body' h_eq
          injection h_eq with h_eq'
          subst h_eq'
          exact h_chain
        · -- non-fvar case
          elim_err h
          rename_i v_measure h_measure_resolve
          elim_err h
          rename_i h_measure_ty
          elim_err h; cases h
          intro body' h_eq
          injection h_eq with h_eq'
          subst h_eq'
          exact h_chain
      · -- measure = none
        elim_err h; cases h
        intro body' h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact h_chain

theorem Function.typeCheck_measureTyped_annotated (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ m, func'.measure = some m →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      LExpr.HasTypeA [] m .int := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  split at h
  · -- body = none: the typechecker now rejects a measure on a bodiless function,
    -- so on the success path `func.measure = none`, hence `func'.measure = none`
    -- and the obligation is vacuous.
    rename_i h_body_none
    split at h
    · simp at h
    · rename_i h_measure_none
      cases h
      intro m h_eq h_nonfvar
      rw [Option.not_isSome_iff_eq_none] at h_measure_none
      rw [h_measure_none] at h_eq; exact absurd h_eq (by simp)
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    · -- alphaEquivMap = some
      rename_i alphaMap h_alphaMap
      elim_err h
      rename_i bwdMap h_alpha
      -- Internal env WF + aliases-resolved, via the packaged helper.
      have h_pairs_sig : ∀ p ∈ func.inputs.keys.zip
          (List.take func.inputs.keys.length v_inst.fst.destructArrow),
          p.2 ∈ v_inst.fst.destructArrow := by
        intro p hp
        exact List.mem_of_mem_take (List.of_mem_zip hp).2
      have h_internal := typeCheck_internalEnv_wf type C Env v_inst.fst v_inst.snd
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
        h_inst h_wf h_resolved h_pairs_sig
      obtain ⟨h_envwf_internal, h_resolved_internal⟩ := h_internal
      -- Well-formedness and aliases-resolved of the body-resolve output env.
      have h_body_envwf : TEnvWF (T := CoreLParams) v_resolve.snd :=
        resolve_TEnvWF body v_resolve.fst C _ v_resolve.snd
          (by rw [Prod.eta]; exact h_resolve) h_envwf_internal h_fwf
      have h_body_props := resolve_properties body v_resolve.fst C _ v_resolve.snd
        (by rw [Prod.eta]; exact h_resolve) h_envwf_internal h_fwf h_resolved_internal
      -- The unify result is gen-fresh for the body env: discharge via
      -- `unify_preserves_SubstFreshForGen`.
      have h_unify' : Constraints.unify
          [(LMonoTy.mkArrow'
              ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
            v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo = .ok v_unify := by
        cases hc : Constraints.unify
            [(LMonoTy.mkArrow'
                ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                  (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
                (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
              v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo with
        | error e => rw [hc] at h_unify; simp [Except.mapError] at h_unify
        | ok w => rw [hc] at h_unify; simp [Except.mapError] at h_unify; rw [h_unify]
      -- Constraint free vars are gen-fresh for the body env's gen state.
      have h_fresh_cs : ∀ v, v ∈ Constraints.freeVars
          [(LMonoTy.mkArrow'
              ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
            v_resolve.fst.toLMonoTy)] →
          ∀ n, n ≥ v_resolve.snd.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
        intro v hv n hn
        simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
          List.mem_append] at hv
        cases hv with
        | inl h_ret =>
          -- retty's free vars ⊆ freeVars v_inst.fst, fresh for Env_inst. The body
          -- env's gen counter is ≥ Env_inst's (push/addInNewest preserve it,
          -- resolve is monotone), so freshness carries up.
          have h_in_mono : v ∈ LMonoTy.freeVars v_inst.fst :=
            LMonoTy.freeVars_reconstructedOutput_subset v_inst.fst func.inputs.keys.length v h_ret
          have h_internal_gen :
              v_resolve.snd.genEnv.genState.tyGen ≥ v_inst.snd.genEnv.genState.tyGen := by
            have h_mono := h_body_props.1
            rw [show (v_inst.snd.pushEmptyContext.addInNewestContext
                (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
                  (func.inputs.keys.zip
                    (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).genEnv.genState
                = v_inst.snd.genEnv.genState from rfl] at h_mono
            exact h_mono
          exact LTy_instantiateWithCheck_freeVars_fresh type C Env v_inst.fst v_inst.snd
            h_inst v h_in_mono n (Nat.le_trans h_internal_gen hn)
        | inr h_body =>
          -- bodyty = v_resolve.fst.toLMonoTy, fresh for the body env by resolve_properties.
          exact h_body_props.2.2 v h_body n hn
      have h_sf : SubstFreshForGen v_unify v_resolve.snd.genEnv.genState :=
        unify_preserves_SubstFreshForGen h_unify' h_body_envwf.substFreshForGen h_fresh_cs
      -- WF + aliases-resolved of the measure env (post-updateSubst).
      have h_envwf_measure : TEnvWF (T := CoreLParams) (v_resolve.snd.updateSubst v_unify) :=
        TEnvWF.of_updateSubst h_body_envwf h_sf
      have h_resolved_measure :
          TContext.AliasesResolved (v_resolve.snd.updateSubst v_unify).context :=
        h_body_props.2.1
      -- Measure split.
      elim_err h
      elim_err h
      elim_err h
      elim_err h
      split at h
      · -- measure = some
        split at h
        · -- fvar case: func'.measure = func.measure = some (.fvar ...), which the
          -- non-fvar hypothesis forbids.
          rename_i fmeta fname fann h_measure_fvar
          elim_err h
          rename_i v_meas h_meas
          cases h
          intro m h_eq h_nonfvar
          dsimp only at h_eq
          rw [show (pure func.measure : Except Std.Format _) = Except.ok func.measure from rfl]
            at h_meas
          injection h_meas with h_meas'
          rw [← h_meas', h_measure_fvar] at h_eq
          injection h_eq with h_m
          exact absurd h_m.symm (h_nonfvar fmeta fname fann)
        · -- non-fvar case: measure resolved on the measure env, type int.
          rename_i h_not_fvar
          elim_err h
          rename_i v_measure h_measure_resolve
          elim_err h
          rename_i h_measure_ty
          -- New anti-refinement guard: the `protectedVars.find?` match. Its
          -- `some v` branch errors; close it and keep the `none` branch.
          elim_err h
          rename_i h_measure_norefine
          elim_err h
          rename_i v_final h_final
          cases h
          intro m h_eq h_nonfvar
          dsimp only at h_eq
          -- `m` is the userSubst-renamed resolved measure.
          rw [show (pure (some (unresolved
              (applySubstT v_measure.fst
                [List.map (fun x => (x.fst, LMonoTy.ftvar x.snd))
                  (v_inst.fst.freeVars.eraseDups.zip func.typeArgs)]))) :
              Except Std.Format _) =
            Except.ok (some (unresolved
              (applySubstT v_measure.fst
                [List.map (fun x => (x.fst, LMonoTy.ftvar x.snd))
                  (v_inst.fst.freeVars.eraseDups.zip func.typeArgs)]))) from rfl] at h_final
          injection h_final with h_final'
          rw [← h_final'] at h_eq
          injection h_eq with h_meq
          subst h_meq
          -- Resolve the measure under the rigidified context `Cm` and the internal env
          -- (formals pushed, pre-unify); `HasTypeA` ignores the rigid field.
          have h_measure_typed : LExpr.HasTypeA [] v_measure.fst.unresolved v_measure.fst.toLMonoTy :=
            resolve_HasTypeA _ v_measure.fst
              { C with rigidTypeVars := v_inst.fst.freeVars.eraseDups ++ C.rigidTypeVars }
              _ v_measure.snd
              (by rw [Prod.eta]; exact h_measure_resolve) h_envwf_internal h_fwf h_resolved_internal
          have h_measure_abswf : LExprT.AbsWF v_measure.fst :=
            resolve_AbsWF _ v_measure.fst
              { C with rigidTypeVars := v_inst.fst.freeVars.eraseDups ++ C.rigidTypeVars }
              _ v_measure.snd
              (by rw [Prod.eta]; exact h_measure_resolve) h_envwf_internal h_fwf
          have h_measure_int : v_measure.fst.toLMonoTy = .int := by
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_measure_ty
            exact h_measure_ty
          have h_applied := applySubstT_unresolved_HasTypeA v_measure.fst
            [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
            [] h_measure_abswf h_measure_typed
          rw [List.map_nil, applySubstT_toLMonoTy, h_measure_int] at h_applied
          rw [LMonoTy.int, LMonoTy.subst_tcons, LMonoTys.subst_nil] at h_applied
          exact h_applied
      · -- measure = none: func'.measure = none, vacuous.
        elim_err h
        rename_i v_none h_none
        cases h
        intro m h_eq h_nonfvar
        dsimp only at h_eq
        rw [show (pure none : Except Std.Format (Option (LExpr CoreLParams.mono))) = Except.ok none
          from rfl] at h_none
        injection h_none with h_none'
        rw [← h_none'] at h_eq
        exact absurd h_eq (by simp)

/-! ### Soundness Theorems -/

/--
Annotated soundness: if `Function.typeCheck` succeeds, the output function
satisfies `FuncHasTypeA`.
-/
theorem Function.typeCheck_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ Γ, FuncHasTypeA C Γ func' := by
  intro Γ
  exact {
    inputsNodup := Function.typeCheck_inputsNodup C Env func func' Env' h
    typeArgsNodup := Function.typeCheck_typeArgsNodup C Env func func' Env' h
    noUndeclaredVars := Function.typeCheck_noUndeclaredVars C Env func func' Env' h h_wf
    bodyTyped := Function.typeCheck_bodyTyped_annotated C Env func func' Env' h h_wf h_fwf h_resolved
    measureTyped := Function.typeCheck_measureTyped_annotated C Env func func' Env' h h_wf h_fwf h_resolved
  }

/-! ### Field lemmas for polymorphic soundness (about the *original* `func`)

These mirror the `func'` field lemmas above, but conclude about the original
`func`, as required by `FuncHasType C func`. -/

/-- `inputsNodup` for the original function: recoverable from `func.type` succeeding. -/
theorem Function.typeCheck_inputsNodup_orig (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func.inputs.keys.Nodup :=
  Function.typeCheck_inputs_nodup C Env func func' Env' h

/-- `typeArgsNodup` for the original function: recoverable from `func.type` succeeding. -/
theorem Function.typeCheck_typeArgsNodup_orig (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func.typeArgs.Nodup := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i type h_type
  exact LFunc.type_typeArgs_nodup func type h_type

mutual
/-- Reverse of `LMonoTy.freeVars_destructArrow_subset`: every free variable of a
    monotype is a free variable of its `destructArrow` decomposition. -/
theorem LMonoTy.freeVars_subset_destructArrow (mty : LMonoTy) :
    LMonoTy.freeVars mty ⊆ LMonoTys.freeVars (LMonoTy.destructArrow mty) := by
  unfold LMonoTy.destructArrow
  split
  · rename_i t1 trest
    simp only [LMonoTy.freeVars, LMonoTys.freeVars_of_cons]
    intro v hv
    rw [List.mem_append] at hv ⊢
    rcases hv with h | h
    · left; exact h
    · right; exact LMonoTys.freeVars_subset_destructArrow trest h
  · intro v hv
    simp only [LMonoTys.freeVars, List.append_nil]
    exact hv

/-- List-level reverse: free variables of `mtys` are free variables of its
    `destructArrow`. -/
theorem LMonoTys.freeVars_subset_destructArrow (mtys : LMonoTys) :
    LMonoTys.freeVars mtys ⊆ LMonoTys.freeVars (LMonoTys.destructArrow mtys) := by
  cases mtys with
  | nil => simp only [LMonoTys.destructArrow, List.Subset.refl]
  | cons ty rest =>
    simp only [LMonoTys.destructArrow, LMonoTys.freeVars_of_cons]
    intro v hv
    rw [LMonoTys.freeVars_append, List.mem_append] at *
    rcases hv with h | h
    · left; exact LMonoTy.freeVars_subset_destructArrow ty h
    · right; exact LMonoTys.freeVars_subset_destructArrow rest h
end

/-- `noUndeclaredVars` for the original function: all free type variables of the
    signature monotype are declared in `typeArgs`. -/
theorem Function.typeCheck_noUndeclaredVars_orig (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values) →
      v ∈ func.typeArgs := by
  -- Recover `func.type = .ok type` and the undeclared-vars guard `LTy.freeVars type = []`.
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  rename_i h_undecl
  have h_closed : LTy.freeVars type = [] := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_undecl
    exact h_undecl
  -- Decompose `func.type` to get `type = .forAll func.typeArgs sigBody` with an explicit `sigBody`
  -- determined by `func.inputs.values`.
  simp only [LFunc.type, bind, Except.bind, pure, Except.pure] at h_type
  split at h_type <;> try contradiction
  split at h_type <;> try contradiction
  split at h_type <;> try contradiction
  -- A common closing step shared by both `inputs.values` cases: from `v ∈ sigBody.freeVars`,
  -- the guard `sigBody.freeVars.removeAll func.typeArgs = []` gives `v ∈ func.typeArgs`.
  have h_guard : ∀ sigBody : LMonoTy, type = LTy.forAll func.typeArgs sigBody →
      ∀ w, w ∈ LMonoTy.freeVars sigBody → w ∈ func.typeArgs := by
    intro sigBody h_ty w hw
    rw [h_ty, LTy.freeVars, List.removeAll, List.filter_eq_nil_iff] at h_closed
    have h_not := h_closed w hw
    simp only [List.elem_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Decidable.not_not] at h_not
    exact h_not
  intro v hv
  rw [LMonoTy.freeVars_mkArrow', List.mem_append] at hv
  split at h_type
  · -- inputs.values = []: sigBody = func.output
    rename_i h_iv
    rw [Except.ok.injEq] at h_type
    refine h_guard func.output h_type.symm v ?_
    rcases hv with h | h
    · rw [h_iv, LMonoTys.freeVars] at h; exact absurd h (List.not_mem_nil)
    · exact h
  · -- inputs.values = ity :: irest: sigBody = mkArrow ity (irest ++ destructArrow output)
    rename_i ity irest h_iv
    rw [Except.ok.injEq] at h_type
    refine h_guard (ity.mkArrow (irest ++ LMonoTy.destructArrow func.output)) h_type.symm v ?_
    rw [LMonoTy.freeVars_mkArrow, LMonoTys.freeVars_append, List.mem_append, List.mem_append]
    rw [h_iv, LMonoTys.freeVars_of_cons, List.mem_append] at hv
    rcases hv with h | h
    · rcases h with h | h
      · left; exact h
      · right; left; exact h
    · right; right; exact LMonoTy.freeVars_subset_destructArrow func.output h

-- `Function.typeCheck_inverse_components` (the shared per-component alias adapter) now lives in
-- `Strata/Languages/Core/InverseComponents.lean` (proven, 0 sorry). It gains two hypotheses
-- `h_known`/`h_arrow2`, discharged at the call sites below.

/-- **`h_fresh` bridge.** From `TContextAliasEquiv` (the Γ→Γ' direction, giving
    `AliasEquiv mty' mty` per key), non-dropping aliases, and a domain-containment fact
    (`h_dom`: every key bound in Γ' is bound in Γ), derive the Γ'→Γ per-key freshness
    reflection that `HasType_context_aliasEquiv` requires. The free-var equality along
    each per-key `AliasEquiv` is `AliasEquiv_preserves_freeVars`, which holds precisely
    because the `TEnv.addTypeAlias` phantom guard makes aliases non-dropping. -/
theorem Function.hfresh_of_aliasEquiv
    (aliases : List TypeAlias) (Γ Γ' : TContext CoreLParams.IDMeta)
    (h_ali : AliasesNonDropping aliases)
    (h_ctx : TContextAliasEquiv (T := CoreLParams) aliases Γ Γ')
    (h_dom : ∀ (x : CoreLParams.Identifier) ty', Γ'.types.find? x = some ty' →
      ∃ ty0, Γ.types.find? x = some ty0) :
    ∀ (x : CoreLParams.Identifier) (ty' : LTy), Γ'.types.find? x = some ty' →
      ∀ a, a ∈ LTy.freeVars ty' →
        ∃ ty0, Γ.types.find? x = some ty0 ∧ a ∈ LTy.freeVars ty0 := by
  intro x ty' h_find' a h_a
  obtain ⟨ty0, h_find0⟩ := h_dom x ty' h_find'
  obtain ⟨mty, mty', h_ty0_eq, h_find'_eq, h_ae⟩ := h_ctx x ty0 h_find0
  rw [h_find'_eq] at h_find'
  simp only [Option.some.injEq] at h_find'
  subst h_find'
  subst h_ty0_eq
  refine ⟨.forAll [] mty, h_find0, ?_⟩
  simp only [LTy.freeVars, List.removeAll_nil] at h_a ⊢
  exact (AliasEquiv_preserves_freeVars aliases h_ali mty' mty h_ae a).mp h_a

/-- Domain-containment fact for `hfresh_of_aliasEquiv`: every key bound in
    `funcContext Env.context func` is bound in `TContext.subst Γ0 ρ`, given the `h_find_eq`
    key-agreement (as in `contextAliasEquiv_base`) and the formals/`take`-slice length match. -/
theorem Function.hdom_base (Env : TEnv Unit)
    (func : Function) (v_inst : LMonoTy × TEnv Unit) (ρ : Subst)
    (Γ0 : TContext Unit)
    (h_len : (List.take func.inputs.keys.length v_inst.fst.destructArrow).length
      = func.inputs.keys.length)
    (h_find_eq : ∀ x,
      Maps.find? Γ0.types x =
        Maps.find?
          ((List.map (fun p => (p.fst, LTy.forAll [] p.snd))
              (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))
            :: Env.context.types) x) :
    ∀ (x : CoreLParams.Identifier) ty', (funcContext Env.context func).types.find? x = some ty' →
      ∃ ty0, (TContext.subst Γ0 ρ).types.find? x = some ty0 := by
  intro x ty' h_find'
  unfold funcContext at h_find'
  simp only [Maps.push, Maps.find?] at h_find'
  suffices h_base : ∃ ty0, Maps.find?
      ((List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))
        :: Env.context.types) x = some ty0 by
    obtain ⟨ty0, h0⟩ := h_base
    rw [← h_find_eq x] at h0
    exact ⟨LTy.subst ρ ty0, TContext.subst_find_some Γ0 ρ x ty0 h0⟩
  simp only [Maps.find?]
  cases h_fm : Map.find?
      (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))) x with
  | some tyF => exact ⟨tyF, rfl⟩
  | none =>
    have h_inp_none : Map.find? (List.map (fun x => (x.fst, LTy.forAll [] x.snd)) func.inputs) x = none := by
      have h_comp : ∀ (l : List (Identifier Unit × LMonoTy)),
          l.map (Prod.fst ∘ (fun p => (p.1, LTy.forAll [] p.2))) = l.map Prod.fst := by
        intro l; apply List.map_congr_left; intro a _; rfl
      have h_notin_fm : x ∉ (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))).map Prod.fst :=
        Map.findNone_eq_notmem_mapfst.mpr h_fm
      rw [List.map_map, h_comp] at h_notin_fm
      have h_zip_keys : (func.inputs.keys.zip
          (List.take func.inputs.keys.length v_inst.fst.destructArrow)).map Prod.fst
          = func.inputs.keys := List.map_fst_zip (Nat.le_of_eq h_len.symm)
      rw [h_zip_keys] at h_notin_fm
      apply Map.findNone_eq_notmem_mapfst.mp
      rw [List.map_map, h_comp]
      rwa [← ListMap.keys_eq_map_fst]
    rw [h_inp_none] at h_find'
    exact ⟨ty', h_find'⟩

/-- Shared core of the body and measure context-alias proofs, parameterized over the resolution
    context `Γ0` by a `find?`-agreement hypothesis `h_find_eq` against `FORMALS :: ambient`. Given
    that, the three conjuncts (`.aliases`-equality, `TContextAliasEquiv`, and the Γ'→Γ freshness
    reflection) against `funcContext Env.context func` follow from the renaming `ρ`: Region A
    (formals) via `region_a_input_lookup`; Region B (ambient) via `h_ambient_mono` + ρ-freshness. -/
theorem Function.contextAliasEquiv_base (Env : TEnv Unit)
    (func : Function) (v_inst : LMonoTy × TEnv Unit) (ρ : Subst)
    (Γ0 : TContext Unit)
    (h_aliases0 : Γ0.aliases = Env.context.aliases)
    (h_ρ_keys : ∀ x ∈ Maps.keys ρ, TContext.isFresh (T := CoreLParams) x Env.context)
    (h_ae_ins : AliasEquivList Env.context.aliases
      (LMonoTy.subst ρ <$> List.take func.inputs.keys.length v_inst.fst.destructArrow)
      func.inputs.values)
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    -- Aliases are non-dropping (WF + reverse), enforced by `TEnv.addTypeAlias`. Drives the
    -- Γ'→Γ freshness reflection (3rd conjunct) via `AliasEquiv_preserves_freeVars`.
    (h_ali_nd : AliasesNonDropping Env.context.aliases)
    -- `Γ0`'s stored types agree with `FORMALS :: Env.context.types` at every key.
    -- This is where each consumer discharges that its inner subst layers are the
    -- identity on visible bindings.
    (h_find_eq : ∀ x,
      Maps.find? Γ0.types x =
        Maps.find?
          ((List.map (fun p => (p.fst, LTy.forAll [] p.snd))
              (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))
            :: Env.context.types) x) :
    (TContext.subst Γ0 ρ).aliases = (funcContext Env.context func).aliases ∧
    TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
      (TContext.subst Γ0 ρ) (funcContext Env.context func) ∧
    (∀ (x : CoreLParams.Identifier) (ty' : LTy),
      (funcContext Env.context func).types.find? x = some ty' →
      ∀ a, a ∈ LTy.freeVars ty' →
        ∃ ty0, (TContext.subst Γ0 ρ).types.find? x = some ty0 ∧ a ∈ LTy.freeVars ty0) := by
  -- Length fact for `hdom_base`, from the input alias-equiv list.
  have h_len : (List.take func.inputs.keys.length v_inst.fst.destructArrow).length
      = func.inputs.keys.length := by
    have h_ae_len := AliasEquivList.length_eq h_ae_ins
    rw [show (LMonoTy.subst ρ <$> List.take func.inputs.keys.length v_inst.fst.destructArrow)
        = (List.take func.inputs.keys.length v_inst.fst.destructArrow).map (LMonoTy.subst ρ)
      from rfl, List.length_map] at h_ae_len
    rw [h_ae_len, ListMap.keys_eq_map_fst, List.length_map, ListMap.values_eq_map_snd,
      List.length_map]
  have h_alias_conj : (TContext.subst Γ0 ρ).aliases = (funcContext Env.context func).aliases := by
    -- aliases equality: ρ preserves aliases; `funcContext` keeps `Env`'s aliases.
    rw [TContext.subst_aliases, h_aliases0]
    rfl
  have h_equiv : TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
      (TContext.subst Γ0 ρ) (funcContext Env.context func) := by
    -- TContextAliasEquiv
    intro x ty h_find
    -- Peel the ρ layer, then rewrite through `h_find_eq` to the base context.
    rw [TContext.subst] at h_find
    obtain ⟨ty1, h1, he1⟩ := TContext_types_subst_find_reverse _ ρ x ty h_find
    rw [h_find_eq x] at h1
    rw [Maps.find?] at h1
    have h_ty_eq : ty = LTy.subst ρ ty1 := he1
    cases h_formals : Map.find?
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))) x with
    | some tyF =>
      -- Region A (formals scope).
      rw [h_formals] at h1
      simp only [Option.some.injEq] at h1
      have h_mem := Map.find?_mem _ x tyF h_formals
      obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp h_mem
      have h_tyF : tyF = LTy.forAll [] p.2 := (Prod.mk.injEq .. ▸ hp_eq).2.symm
      have h_ty_final : ty = LTy.forAll [] (LMonoTy.subst ρ p.2) := by
        rw [h_ty_eq, ← h1, h_tyF, LTy.subst_forAll_nil]
      have h_len : (List.take func.inputs.keys.length v_inst.fst.destructArrow).length
          = func.inputs.length := by
        have h_ae_len := AliasEquivList.length_eq h_ae_ins
        rw [show (LMonoTy.subst ρ <$> List.take func.inputs.keys.length v_inst.fst.destructArrow)
            = (List.take func.inputs.keys.length v_inst.fst.destructArrow).map (LMonoTy.subst ρ)
          from rfl, List.length_map, ListMap.values_eq_map_snd, List.length_map] at h_ae_len
        exact h_ae_len
      have h_fmls' : Map.find?
          (((func.inputs.map Prod.fst).zip
              (List.take func.inputs.keys.length v_inst.fst.destructArrow)).map
            (fun p => (p.1, LTy.forAll [] p.2))) x = some (LTy.forAll [] p.2) := by
        rw [← ListMap.keys_eq_map_fst]; rw [← h_tyF]; exact h_formals
      have h_ae_ins' : AliasEquivList Env.context.aliases
          ((List.take func.inputs.keys.length v_inst.fst.destructArrow).map (LMonoTy.subst ρ))
          (func.inputs.map Prod.snd) := by
        rw [← ListMap.values_eq_map_snd]; exact h_ae_ins
      obtain ⟨mty', h_find', h_ae'⟩ := region_a_input_lookup func.inputs
        (List.take func.inputs.keys.length v_inst.fst.destructArrow) (LMonoTy.subst ρ) x p.2
        h_len h_ae_ins' h_fmls'
      refine ⟨LMonoTy.subst ρ p.2, mty', h_ty_final, ?_, AliasEquiv.symm h_ae'⟩
      unfold funcContext
      simp only [Maps.push, Maps.find?]
      rw [h_find']
    | none =>
      -- Region B (ambient scope).
      rw [h_formals] at h1
      simp only [] at h1
      have h_bv : LTy.boundVars ty1 = [] := h_ambient_mono ty1 (Maps.find?_mem_values _ h1)
      cases ty1 with
      | forAll xs mty0 =>
        simp only [LTy.boundVars] at h_bv
        subst h_bv
        have h_rho_id : LMonoTy.subst ρ mty0 = mty0 := by
          apply LMonoTy.subst_no_relevant_keys
          intro k hk_fv hk_key
          exact h_ρ_keys k hk_key x (LTy.forAll [] mty0) h1
            (by rw [LTy.freeVars, List.removeAll_nil]; exact hk_fv)
        have h_rhs_lookup : (funcContext Env.context func).types.find? x
            = some (LTy.forAll [] mty0) := by
          have h_len : (List.take func.inputs.keys.length v_inst.fst.destructArrow).length
              = func.inputs.values.length := by
            have h_ae_len := AliasEquivList.length_eq h_ae_ins
            rw [show (LMonoTy.subst ρ <$> List.take func.inputs.keys.length v_inst.fst.destructArrow)
                = (List.take func.inputs.keys.length v_inst.fst.destructArrow).map (LMonoTy.subst ρ)
              from rfl, List.length_map] at h_ae_len
            exact h_ae_len
          have h_vk : func.inputs.values.length = func.inputs.keys.length := by
            rw [ListMap.values_eq_map_snd, ListMap.keys_eq_map_fst, List.length_map, List.length_map]
          have h_keys_eq : (func.inputs.keys.zip
              (List.take func.inputs.keys.length v_inst.fst.destructArrow)).map Prod.fst
              = func.inputs.keys := List.map_fst_zip (Nat.le_of_eq (by rw [h_len, h_vk]))
          have h_comp : ∀ (l : List (Identifier Unit × LMonoTy)),
              l.map (Prod.fst ∘ (fun p => (p.1, LTy.forAll [] p.2))) = l.map Prod.fst := by
            intro l; apply List.map_congr_left; intro a _; rfl
          have hx_notin : x ∉ func.inputs.keys := by
            have h_nm := (Map.findNone_eq_notmem_mapfst
              (m := List.map (fun p => (p.fst, LTy.forAll [] p.snd))
                (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))
              (a := x)).mpr h_formals
            rw [List.map_map, h_comp] at h_nm
            rwa [h_keys_eq] at h_nm
          unfold funcContext
          simp only [Maps.push, Maps.find?]
          have h_rhs_none : Map.find?
              (func.inputs.map (fun p => (p.1, LTy.forAll [] p.2))) x = none := by
            apply (Map.findNone_eq_notmem_mapfst).mp
            rw [List.map_map, h_comp]
            rw [ListMap.keys_eq_map_fst] at hx_notin
            exact hx_notin
          rw [h_rhs_none]; exact h1
        refine ⟨mty0, mty0, ?_, h_rhs_lookup, Lambda.AliasEquiv.refl⟩
        rw [h_ty_eq, LTy.subst_forAll_nil, h_rho_id]
  -- Assemble: aliases-eq, the equivalence, and the Γ'→Γ freshness reflection.
  refine ⟨h_alias_conj, h_equiv, ?_⟩
  -- freshness reflection via `hfresh_of_aliasEquiv` + `hdom_base` (needs `h_ali_nd`, `h_len`).
  have h_ctx' : TContextAliasEquiv (T := CoreLParams) Env.context.aliases
      (TContext.subst Γ0 ρ) (funcContext Env.context func) := by
    have h_fc_al : (funcContext Env.context func).aliases = Env.context.aliases := rfl
    rw [h_fc_al] at h_equiv; exact h_equiv
  exact Function.hfresh_of_aliasEquiv Env.context.aliases (TContext.subst Γ0 ρ)
    (funcContext Env.context func) h_ali_nd h_ctx'
    (Function.hdom_base Env func v_inst ρ Γ0 h_len h_find_eq)

/-- The context-alias facts for `Γ_inst = ((FORMALS :: ambient).subst v_unify.subst).subst
    renameSubst`, shared by the body and measure instantiated lemmas. Proves `h_find_eq` (the inner
    `v_unify`+`renameSubst` layers are the identity on visible bindings: Region A formals via the
    alpha-equiv roundtrip, Region B ambient via the rigid + generalization guards) and delegates the
    ρ-walk to `contextAliasEquiv_base`. -/
theorem Function.contextAliasEquiv_facts (C : LContext CoreLParams) (Env : TEnv Unit)
    (func : Function) (type : LTy) (v_inst : LMonoTy × TEnv Unit) (ρ : Subst)
    (v_unify : SubstInfo) (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_inst : type.instantiateWithCheck C Env = .ok v_inst)
    (h_alphaMap : v_inst.fst.alphaEquivMap (LMonoTy.subst v_unify.subst v_inst.fst) = some bwdMap)
    (h_gen_none : List.find?
      (fun v => (TContext.types.knownTypeVars
        (TContext.types.subst Env.context.types v_unify.subst)).contains v)
      (LMonoTy.subst v_unify.subst v_inst.fst).freeVars = none)
    (h_rigid_fixed : ∀ v ∈ C.rigidTypeVars,
      LMonoTy.subst v_unify.subst (LMonoTy.ftvar v) = LMonoTy.ftvar v)
    (h_ρ_keys : ∀ x ∈ Maps.keys ρ, TContext.isFresh (T := CoreLParams) x Env.context)
    (h_ae_ins : AliasEquivList Env.context.aliases
      (LMonoTy.subst ρ <$> List.take func.inputs.keys.length v_inst.fst.destructArrow)
      func.inputs.values)
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    (h_ali_nd : AliasesNonDropping Env.context.aliases) :
    let FORMALS : Map (Identifier CoreLParams.IDMeta) LTy :=
      List.map (fun p => (p.fst, LTy.forAll [] p.snd))
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
    let renameSubst : Subst := [renameMap v_unify.subst v_inst.fst.freeVars.eraseDups]
    let Γ_inst : TContext Unit :=
      ((v_inst.snd.pushEmptyContext.addInNewestContext FORMALS).context.subst v_unify.subst).subst renameSubst
    (TContext.subst Γ_inst ρ).aliases = (funcContext Env.context func).aliases ∧
    TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
      (TContext.subst Γ_inst ρ) (funcContext Env.context func) ∧
    (∀ (x : CoreLParams.Identifier) (ty' : LTy),
      (funcContext Env.context func).types.find? x = some ty' →
      ∀ a, a ∈ LTy.freeVars ty' →
        ∃ ty0, (TContext.subst Γ_inst ρ).types.find? x = some ty0 ∧ a ∈ LTy.freeVars ty0) := by
  intro FORMALS renameSubst Γ_inst
  have h_ctx_eq : v_inst.snd.context = Env.context :=
    LTy_instantiateWithCheck_context' type C Env v_inst.fst v_inst.snd
      (by rw [Prod.eta]; exact h_inst)
  -- The internal env's `.types` reduces to `FORMALS :: Env.context.types`.
  have h_int_types : (v_inst.snd.pushEmptyContext.addInNewestContext FORMALS).context.types
      = FORMALS :: Env.context.types := by
    have e1 : (v_inst.snd.pushEmptyContext.addInNewestContext FORMALS).context.types
        = FORMALS :: v_inst.snd.context.types := by
      simp only [TEnv.pushEmptyContext, TEnv.addInNewestContext, TEnv.updateContext,
        TEnv.context, Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]
      rfl
    rw [e1, h_ctx_eq]
  -- `Γ_inst.aliases` = `Env.context.aliases` (ρ/renameSubst/v_unify preserve aliases).
  have h_aliases0 : Γ_inst.aliases = Env.context.aliases := by
    show (TContext.subst (TContext.subst
      (v_inst.snd.pushEmptyContext.addInNewestContext FORMALS).context v_unify.subst)
      renameSubst).aliases = _
    rw [TContext.subst_aliases, TContext.subst_aliases]
    show v_inst.snd.context.aliases = _
    rw [h_ctx_eq]
  -- Body-specific obligation: the inner `v_unify`+`renameSubst` layers are the identity
  -- on every visible binding, so `Γ_inst.types` agrees with the base context at every key.
  -- Region A (formals) uses the alpha-equiv roundtrip; Region B (ambient) uses the rigid check +
  -- generalization guard. The ρ-walk + funcContext matching is delegated to `contextAliasEquiv_base`.
  have h_find_eq : ∀ x,
      Maps.find? Γ_inst.types x = Maps.find? (FORMALS :: Env.context.types) x := by
    intro x
    have h_Γinst_types : Γ_inst.types =
        TContext.types.subst
          (TContext.types.subst (FORMALS :: Env.context.types) v_unify.subst) renameSubst := by
      show TContext.types.subst (TContext.types.subst
        (v_inst.snd.pushEmptyContext.addInNewestContext FORMALS).context.types v_unify.subst)
        renameSubst = _
      rw [h_int_types]
    rw [h_Γinst_types]
    cases h_base : Maps.find? (FORMALS :: Env.context.types) x with
    | none =>
      rw [TContext_types_subst_find_none _ _ _
        (TContext_types_subst_find_none _ _ _ h_base)]
    | some ty0 =>
      have e2 := TContext_types_subst_find _ renameSubst x _
        (TContext_types_subst_find _ v_unify.subst x ty0 h_base)
      rw [e2]
      -- Per-entry identity: `subst renameSubst (subst v_unify ty0) = ty0`.
      rw [Maps.find?] at h_base
      have h_id : LTy.subst renameSubst (LTy.subst v_unify.subst ty0) = ty0 := by
        cases h_formals : Map.find? FORMALS x with
        | some tyF =>
          -- Region A (formals scope).
          rw [h_formals] at h_base
          simp only [Option.some.injEq] at h_base
          subst h_base
          have h_mem := Map.find?_mem FORMALS x tyF h_formals
          obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp h_mem
          have h_tyF : tyF = LTy.forAll [] p.2 := (Prod.mk.injEq .. ▸ hp_eq).2.symm
          have hp_slice : p.2 ∈ List.take func.inputs.keys.length v_inst.fst.destructArrow :=
            (List.of_mem_zip hp_mem).2
          have h_round : LMonoTy.subst renameSubst (LMonoTy.subst v_unify.subst p.2) = p.2 := by
            have h_sub : ∀ v, v ∈ LMonoTy.freeVars p.2 → v ∈ LMonoTy.freeVars v_inst.fst := by
              intro v hv
              exact LMonoTy.mem_destructArrow_freeVars_subset v_inst.fst p.2
                (List.mem_of_mem_take hp_slice) hv
            exact renameMap_inverse v_inst.fst p.2 v_unify.subst bwdMap h_alphaMap
              v_inst.fst.freeVars.eraseDups (fun v => List.mem_eraseDups) (eraseDups_Nodup _) h_sub
          rw [h_tyF, LTy.subst_forAll_nil, LTy.subst_forAll_nil, h_round]
        | none =>
          -- Region B (ambient scope).
          rw [h_formals] at h_base
          simp only [] at h_base
          have h_bv : LTy.boundVars ty0 = [] := h_ambient_mono ty0 (Maps.find?_mem_values _ h_base)
          cases ty0 with
          | forAll xs mty0 =>
            simp only [LTy.boundVars] at h_bv
            subst h_bv
            have h_fv_rigid : ∀ v ∈ LMonoTy.freeVars mty0, v ∈ C.rigidTypeVars := by
              intro v hv
              have h_lv := h_ambient_rigid x (LTy.forAll [] mty0) h_base v
              rw [LTy.freeVars, List.removeAll_nil] at h_lv
              exact h_lv hv
            have h_unify_id : LMonoTy.subst v_unify.subst mty0 = mty0 := by
              have h_eq := agree_on_freeVars_implies_subst_eq (S₁ := v_unify.subst) (S₂ := [])
                (ty := mty0) (fun v hv => by
                  rw [h_rigid_fixed v (h_fv_rigid v hv), LMonoTy.subst_emptyS (by rfl)])
              rw [h_eq, LMonoTy.subst_emptyS (by rfl)]
            have h_rename_id : LMonoTy.subst renameSubst mty0 = mty0 := by
              apply LMonoTy.subst_no_relevant_keys
              intro k hk_fv hk_key
              have h_find_subst : Maps.find? (TContext.types.subst Env.context.types v_unify.subst) x
                  = some (LTy.subst v_unify.subst (LTy.forAll [] mty0)) :=
                TContext_types_subst_find _ _ _ _ h_base
              rw [LTy.subst_forAll_nil, h_unify_id] at h_find_subst
              have h_known : k ∈ TContext.types.knownTypeVars
                  (TContext.types.subst Env.context.types v_unify.subst) := by
                have hh := @TContext.mem_knownTypeVars_of_find CoreLParams _
                  { types := TContext.types.subst Env.context.types v_unify.subst, aliases := [] }
                  x (LTy.forAll [] mty0) k h_find_subst
                  (by rw [LTy.freeVars, List.removeAll_nil]; exact hk_fv)
                simpa only [TContext.knownTypeVars] using hh
              -- New shape: a key `k` of `renameMap` has a preimage `x' ∈ freeVars v_inst.fst`
              -- with `subst v_unify (ftvar x') = ftvar k`, so `k` is free in `subst v_unify v_inst.fst`.
              have hk_keys' : k ∈ Map.keys (renameMap v_unify.subst v_inst.fst.freeVars.eraseDups) := by
                unfold Maps.keys at hk_key
                simpa only [List.append_nil, Maps.keys] using hk_key
              obtain ⟨x', hx'_mem, hx'_sub, _⟩ :=
                mem_keys_renameMap v_unify.subst v_inst.fst.freeVars.eraseDups k hk_keys'
              have hx'_fv : x' ∈ LMonoTy.freeVars v_inst.fst := List.mem_eraseDups.mp hx'_mem
              have hk_inst : k ∈ LMonoTy.freeVars (LMonoTy.subst v_unify.subst v_inst.fst) := by
                have hmono := LMonoTy.mem_freeVars_subst_of_mem v_unify.subst v_inst.fst x' hx'_fv k
                rw [hx'_sub] at hmono
                exact hmono (by simp [LMonoTy.freeVars])
              have h_not := List.find?_eq_none.mp h_gen_none k hk_inst
              exact h_not (List.contains_iff_mem.mpr h_known)
            rw [LTy.subst_forAll_nil, h_unify_id, LTy.subst_forAll_nil, h_rename_id]
      rw [h_id]
  -- Delegate the shared ρ-walk to the base lemma.
  exact Function.contextAliasEquiv_base Env func v_inst ρ Γ_inst
    h_aliases0 h_ρ_keys h_ae_ins h_ambient_mono h_ali_nd h_find_eq

/-- Every value in a `forAll []`-map has no bound variables. Drives the FORMALS scope of
    `internalContext_values_mono`. -/
theorem mem_values_map_forAll_nil_boundVars (l : List (CoreLParams.Identifier × LMonoTy)) (ty : LTy)
    (h : ty ∈ Map.values (List.map (fun p => (p.fst, LTy.forAll [] p.snd)) l)) :
    ty.boundVars = [] := by
  induction l with
  | nil => simp [Map.values] at h
  | cons hd tl ih =>
    simp only [List.map_cons, Map.values, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; rfl
    · exact ih h

/-- The internal body-resolution context `(FORMALS :: ambient)` is monomorphic: every
    value is `forAll [] _` (formals by construction; ambient by `h_ambient_mono`). Stated
    over `Maps.values` so it captures every physical entry (drives `TContext.subst`
    composition and `polyKeysFresh` in `bodyComposite_pack`). -/
theorem Function.internalContext_values_mono (C : LContext CoreLParams) (Env : TEnv Unit)
    (func : Function) (type : LTy) (v_inst : LMonoTy × TEnv Unit)
    (h_inst : type.instantiateWithCheck C Env = .ok v_inst)
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = []) :
    ∀ ty ∈ Maps.values
      (v_inst.snd.pushEmptyContext.addInNewestContext
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.types,
      ty.boundVars = [] := by
  -- Reduce the internal context's types to `FORMALS :: Env.context.types`, then split
  -- `Maps.values` into the FORMALS scope (all `forAll []` by construction) and the ambient
  -- scope (all mono by the values-based `h_ambient_mono`).
  have h_ctx_eq : v_inst.snd.context = Env.context :=
    LTy_instantiateWithCheck_context' type C Env v_inst.fst v_inst.snd (by rw [Prod.eta]; exact h_inst)
  have h_types : (v_inst.snd.pushEmptyContext.addInNewestContext
      (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.types
      = (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))
        :: Env.context.types := by
    have e1 : (v_inst.snd.pushEmptyContext.addInNewestContext
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.types
        = (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))
          :: v_inst.snd.context.types := by
      simp only [TEnv.pushEmptyContext, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
        Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]
      rfl
    rw [e1, h_ctx_eq]
  intro ty h_mem
  rw [h_types, Maps.values.eq_def, List.mem_append] at h_mem
  rcases h_mem with h_formals | h_ambient
  · exact mem_values_map_forAll_nil_boundVars _ ty h_formals
  · exact h_ambient_mono ty h_ambient

/-- Every key and range variable of the body's return-type unification `v_unify` avoids
    `func.typeArgs` — the provenance fact behind `SubstWF` of the composite (the offending `a ↦ a`
    entries cannot arise since no user type argument enters `v_unify`). Proved from
    `resolve_freeVars_pred`, `Constraints.unify_pred`, and `freeVars_reconstructedOutput_subset`,
    with the instantiation-side closure facts (`hA`/`h_ctx`/`h_subin`) as hypotheses. -/
theorem Function.vunify_avoids_typeArgs (C : LContext CoreLParams) (Env_int : TEnv Unit)
    (func : Function) (v_inst : LMonoTy × TEnv Unit)
    (body : LExpr ({ Metadata := ExpressionMetadata, IDMeta := Unit } : LExprParams).mono)
    (v_resolve : LExprT ({ Metadata := ExpressionMetadata, IDMeta := Unit } : LExprParams).mono × TEnv Unit)
    (v_unify : SubstInfo)
    (h_resolve : LExpr.resolve C Env_int body = .ok (v_resolve.fst, v_resolve.snd))
    (h_envwf : TEnvWF (T := CoreLParams) Env_int)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env_int.context)
    (h_unify : Constraints.unify
      [(LMonoTy.mkArrow'
          ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
            (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
        (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
        v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo = .ok v_unify)
    (hA : ∀ v, v ∈ LMonoTy.freeVars v_inst.fst → v ∉ func.typeArgs)
    (h_ctx : ∀ v, v ∈ TContext.knownTypeVars Env_int.context → v ∉ func.typeArgs)
    (h_subin : ∀ v, (v ∈ Maps.keys Env_int.stateSubstInfo.subst ∨
                      v ∈ Subst.freeVars Env_int.stateSubstInfo.subst) → v ∉ func.typeArgs)
    -- No generated type variable is a user `typeArg` (from the gen-prefix guard, extracted from `h`).
    (h_gen_avoids : ∀ (k : Nat), (TState.tyPrefix ++ toString k) ∉ func.typeArgs) :
    (∀ k, k ∈ Maps.keys v_unify.subst → k ∉ func.typeArgs) ∧
    (∀ k, k ∈ Subst.freeVars v_unify.subst → k ∉ func.typeArgs) := by
  obtain ⟨hB, hC⟩ := resolve_freeVars_pred body v_resolve.fst C Env_int v_resolve.snd
    h_resolve h_envwf h_fwf h_resolved (· ∉ func.typeArgs) h_ctx h_subin
    (fun v k h_eq => h_eq ▸ h_gen_avoids k)
  have h_cs : ∀ v, v ∈ Constraints.freeVars
      [(LMonoTy.mkArrow'
          ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
            (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
        (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
        v_resolve.fst.toLMonoTy)] → v ∉ func.typeArgs := by
    intro v hv
    simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil, List.mem_append] at hv
    rcases hv with h_out | h_body
    · exact hA v (LMonoTy.freeVars_reconstructedOutput_subset v_inst.fst func.inputs.keys.length v h_out)
    · exact hB v h_body
  exact Constraints.unify_pred h_unify (· ∉ func.typeArgs) h_cs
    (fun v hv => hC v (Or.inl hv)) (fun v hv => hC v (Or.inr hv))

/-- **Provenance bundle for `bodyComposite_wf`.** Packages the four facts the composite-`SubstWF`
    proof consumes: `hC1`/`hC2` (the ρ₀-contract, from `LTy_instantiateWithCheck_inverse`) and
    `hVU`/`hUT` (the `v_unify` provenance, from `Function.vunify_avoids_typeArgs`). -/
theorem Function.bodyComposite_wf_hyps
    (func : Function) (type : LTy) (v_inst : LMonoTy × TEnv Unit)
    (v_unify : SubstInfo) (ρ₀ : SubstOne)
    (h_type : func.type = .ok type)
    -- C1/C2 raw, from the strengthened `LTy_instantiateWithCheck_inverse` (ρ₀-contract):
    (h_ρ₀_range : ∀ v, v ∈ Subst.freeVars [ρ₀] → v ∈ LTy.boundVars type)
    (h_ρ₀_cover : ∀ v, v ∈ LMonoTy.freeVars v_inst.fst → v ∈ Map.keys ρ₀)
    -- `vunify_avoids_typeArgs` outputs (keys + range of v_unify avoid typeArgs) and the
    -- instantiation-side closure `hA` (freeVars v_inst.fst avoid typeArgs). `hUT` is derived.
    (hVU : ∀ k, k ∈ Maps.keys v_unify.subst → k ∉ func.typeArgs)
    (hVUr : ∀ k, k ∈ Subst.freeVars v_unify.subst → k ∉ func.typeArgs)
    (hA : ∀ v, v ∈ LMonoTy.freeVars v_inst.fst → v ∉ func.typeArgs) :
    (∀ v, v ∈ Subst.freeVars [ρ₀] → v ∈ func.typeArgs) ∧
    (∀ v, v ∈ LMonoTy.freeVars v_inst.fst → v ∈ Map.keys ρ₀) ∧
    (∀ k, k ∈ Maps.keys v_unify.subst → k ∉ func.typeArgs) ∧
    (∀ v, v ∈ LMonoTy.freeVars (LMonoTy.subst v_unify.subst v_inst.fst) → v ∉ func.typeArgs) := by
  have h_bv : LTy.boundVars type = func.typeArgs :=
    LFunc.type_boundVars_eq_typeArgs (T := CoreLParams) func type h_type
  -- hUT: unified-type vars ⊆ freeVars v_inst.fst ∪ v_unify range, both avoid typeArgs.
  have hUT : ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.subst v_unify.subst v_inst.fst) →
      v ∉ func.typeArgs := by
    intro v hv
    have h_sub := LMonoTy.freeVars_of_subst_subset v_unify.subst v_inst.fst hv
    rw [List.mem_append] at h_sub
    rcases h_sub with h_orig | h_range
    · exact hA v h_orig
    · exact hVUr v h_range
  refine ⟨fun v hv => ?_, h_ρ₀_cover, hVU, hUT⟩
  rw [← h_bv]; exact h_ρ₀_range v hv

/-- The sequential composite `S = compose ρ₀ (compose rs₀ v_unify)` is `SubstWF`. Proved via
    `SubstWF_compose_of_cover`, not factor-by-factor: the inner `compose rs₀ v_unify` need not be
    `SubstWF` (it can carry a self-identity entry `(x, ftvar x)` when the unified type reuses an
    instantiation var `x`), but `ρ₀` scrubs it since `x ∈ keys ρ₀`. -/
theorem Function.bodyComposite_wf
    (func : Function) (v_inst : LMonoTy × TEnv Unit)
    (v_unify : SubstInfo) (ρ₀ : SubstOne)
    (h_wf_ρ : SubstWF [ρ₀] = true)
    -- ρ₀-contract: C1 = ρ₀'s range is the user type arguments; C2 = ρ₀'s keys cover the instantiation vars.
    (hC1 : ∀ v, v ∈ Subst.freeVars [ρ₀] → v ∈ func.typeArgs)
    (hC2 : ∀ v, v ∈ LMonoTy.freeVars v_inst.fst → v ∈ Map.keys ρ₀)
    -- provenance from `vunify_avoids_typeArgs` (+ its `$__ty`-world chain):
    -- v_unify keys avoid typeArgs; the unified type's vars avoid typeArgs.
    (hVU : ∀ k, k ∈ Maps.keys v_unify.subst → k ∉ func.typeArgs)
    (hUT : ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.subst v_unify.subst v_inst.fst) → v ∉ func.typeArgs) :
    SubstWF (Subst.compose ρ₀ (Subst.compose
      (renameMap v_unify.subst v_inst.fst.freeVars.eraseDups)
      v_unify.subst)) = true := by
  let rs₀ : SubstOne := renameMap v_unify.subst v_inst.fst.freeVars.eraseDups
  have h_keys_eq : Maps.keys (Subst.compose rs₀ v_unify.subst)
      = Maps.keys v_unify.subst ++ Map.keys rs₀ := by
    rw [Subst.compose, Maps.keys_append, Subst.keys_of_apply_eq]
    show Maps.keys v_unify.subst ++ Maps.keys [rs₀] = _
    simp [Maps.keys]
  -- hkeys: every key of the inner composite avoids ρ₀'s range (= user typeArgs).
  have hkeys : ∀ k ∈ Maps.keys (Subst.compose rs₀ v_unify.subst), k ∉ Subst.freeVars [ρ₀] := by
    intro k hk h_in_rho
    have hk_ta : k ∈ func.typeArgs := hC1 k h_in_rho
    rw [h_keys_eq, List.mem_append] at hk
    rcases hk with h_vu | h_rs
    · exact hVU k h_vu hk_ta
    · -- a key `k` of `rs₀` is `subst v_unify.subst (ftvar x) = ftvar k` for `x ∈ freeVars v_inst.fst`,
      -- so `k ∈ freeVars (subst v_unify.subst v_inst.fst)` by forward monotonicity.
      obtain ⟨x, hx_mem, hsub_x, _⟩ :=
        mem_keys_renameMap v_unify.subst v_inst.fst.freeVars.eraseDups k h_rs
      have hx_fv : x ∈ LMonoTy.freeVars v_inst.fst := List.mem_eraseDups.mp hx_mem
      have hk_fv : k ∈ LMonoTy.freeVars (LMonoTy.subst v_unify.subst v_inst.fst) := by
        apply LMonoTy.mem_freeVars_subst_of_mem v_unify.subst v_inst.fst x hx_fv k
        rw [hsub_x]; simp only [LMonoTy.freeVars, List.mem_singleton]
      exact hUT k hk_fv hk_ta
  -- hcover: every key of the inner composite that occurs in its own range is an instantiation
  -- var (hence covered by ρ₀). The self-referential characterization `hSelf` is direct from the
  -- new `renameMap` value characterization (values are `ftvar x`, `x ∈ freeVars v_inst.fst`).
  have hSelf : ∀ k, k ∈ Maps.keys (Subst.compose rs₀ v_unify.subst) →
      k ∈ Subst.freeVars (Subst.compose rs₀ v_unify.subst) →
      k ∈ LMonoTy.freeVars v_inst.fst := by
    -- A key of the inner composite also in its range must be an instantiation var: the scrubbed
    -- `freeVars v_unify` part is impossible for a key, so it occurs in `rs₀`'s values.
    intro k hk_key hk_fv
    have h_wf_rs : SubstWF [rs₀] :=
      substWF_renameMap_new v_unify.subst v_unify.isWF v_inst.fst.freeVars.eraseDups
    have h_scrub := Subst.freeVars_compose_subset_scrub rs₀ v_unify.subst h_wf_rs k hk_fv
    rcases h_scrub with h_rs_fv | ⟨h_vu_fv, h_not_rskey⟩
    · exact List.mem_eraseDups.mp
        (freeVars_renameMap_mem_vs v_unify.subst v_inst.fst.freeVars.eraseDups k h_rs_fv)
    · rw [h_keys_eq, List.mem_append] at hk_key
      rcases hk_key with h_vu_key | h_rs_key
      · exfalso
        have hwf := v_unify.isWF
        simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at hwf
        exact hwf k h_vu_key h_vu_fv
      · exact absurd h_rs_key h_not_rskey
  have hcover : ∀ k ∈ Maps.keys (Subst.compose rs₀ v_unify.subst),
      k ∈ Subst.freeVars (Subst.compose rs₀ v_unify.subst) → k ∈ Map.keys ρ₀ := by
    intro k hk h_fv
    exact hC2 k (hSelf k hk h_fv)
  exact SubstWF_compose_of_cover ρ₀ _ h_wf_ρ hkeys hcover

/-- Folds the threefold `ρ ∘ renameSubst ∘ v_unify.subst` into one substitution `S` that acts as the
    composition on the internal context and on `bodyty`, absorbs the resolve substitution, is
    `SubstWF`, and is `polyKeysFresh` over the (monomorphic) internal context — so instantiating
    `resolve_HasType_core.1` at `S` once yields the post-ρ body judgment. -/
theorem Function.bodyComposite_pack
    (func : Function) (v_inst : LMonoTy × TEnv Unit)
    (v_resolve : LExprT ({ Metadata := ExpressionMetadata, IDMeta := Unit } : LExprParams).mono × TEnv Unit)
    (v_unify : SubstInfo) (ρ : Subst) (ρ₀ : SubstOne)
    (bodyty : LMonoTy)
    -- `ρ` is single-scope.
    (h_ρ_single : ρ = [ρ₀])
    -- `v_unify` absorbs the resolve substitution (from `Constraints.unify_absorbs` at the call site).
    (h_absorbs : v_unify.subst.absorbs v_resolve.snd.stateSubstInfo.subst)
    -- Every entry of the internal context is monomorphic (formals are `forAll []`; ambient by
    -- `h_ambient_mono`). Drives both the context-composition law and `polyKeysFresh`.
    (h_mono : ∀ ty ∈ Maps.values
      (v_inst.snd.pushEmptyContext.addInNewestContext
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.types,
      ty.boundVars = [])
    -- `SubstWF` of the full composite `S = compose ρ₀ (compose rs₀ v_unify)`. Supplied by
    -- `bodyComposite_wf`. NOT decomposed factor-by-factor: the inner
    -- `compose rs₀ v_unify` is NOT itself `SubstWF` (it can carry a self-identity entry `(x, ftvar x)`
    -- when the unified type reuses an instantiation var), which `ρ₀` scrubs — see
    -- `SubstWF_compose_of_cover`.
    (h_wf_S : SubstWF (Subst.compose ρ₀ (Subst.compose
      (renameMap v_unify.subst v_inst.fst.freeVars.eraseDups)
      v_unify.subst)) = true) :
    let FORMALS : Map (Identifier CoreLParams.IDMeta) LTy :=
      List.map (fun p => (p.fst, LTy.forAll [] p.snd))
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
    let renameSubst : Subst :=
      [renameMap v_unify.subst v_inst.fst.freeVars.eraseDups]
    let Γ_int : TContext Unit := (v_inst.snd.pushEmptyContext.addInNewestContext FORMALS).context
    ∃ S : Subst,
        ((Γ_int.subst v_unify.subst).subst renameSubst).subst ρ = Γ_int.subst S ∧
        LMonoTy.subst ρ (LMonoTy.subst renameSubst (LMonoTy.subst v_unify.subst bodyty))
          = LMonoTy.subst S bodyty ∧
        S.absorbs v_resolve.snd.stateSubstInfo.subst ∧
        SubstWF S = true ∧
        Subst.polyKeysFresh (T := CoreLParams) S Γ_int := by
  intro FORMALS renameSubst Γ_int
  subst h_ρ_single
  -- The single sequential composite (rename folded into unify, then ρ₀ on top).
  let rs₀ : SubstOne := renameMap v_unify.subst v_inst.fst.freeVars.eraseDups
  have h_rseq : renameSubst = [rs₀] := rfl
  let S₁ : Subst := Subst.compose rs₀ v_unify.subst
  let S : Subst := Subst.compose ρ₀ S₁
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · -- context acts-as: fold the three TContext.subst layers via the composition law.
    show ((Γ_int.subst v_unify.subst).subst renameSubst).subst [ρ₀] = Γ_int.subst (Subst.compose ρ₀ S₁)
    rw [h_rseq,
        TContext.subst_compose_forAll_nil rs₀ v_unify.subst Γ_int h_mono,
        TContext.subst_compose_forAll_nil ρ₀ S₁ Γ_int h_mono]
  · -- type acts-as: two applications of `LMonoTy.subst_compose`.
    show LMonoTy.subst [ρ₀] (LMonoTy.subst renameSubst (LMonoTy.subst v_unify.subst bodyty))
      = LMonoTy.subst (Subst.compose ρ₀ S₁) bodyty
    rw [h_rseq, LMonoTy.subst_compose rs₀ v_unify.subst bodyty, LMonoTy.subst_compose ρ₀ S₁ bodyty]
  · -- absorbs: S = compose ρ₀ S₁ acts as `[ρ₀] ∘ [rs₀] ∘ v_unify`, and v_unify
    -- absorbs v_resolve, so applying the two outer layers to both sides preserves it.
    show (Subst.compose ρ₀ S₁).absorbs v_resolve.snd.stateSubstInfo.subst
    intro a t h_find
    have h3 : LMonoTy.subst S₁ t = LMonoTy.subst S₁ (.ftvar a) := by
      have e1 : LMonoTy.subst S₁ t = LMonoTy.subst [rs₀] (LMonoTy.subst v_unify.subst t) :=
        (LMonoTy.subst_compose rs₀ v_unify.subst t).symm
      have e2 : LMonoTy.subst S₁ (.ftvar a) =
          LMonoTy.subst [rs₀] (LMonoTy.subst v_unify.subst (.ftvar a)) :=
        (LMonoTy.subst_compose rs₀ v_unify.subst (.ftvar a)).symm
      rw [e1, e2, h_absorbs a t h_find]
    rw [← LMonoTy.subst_compose ρ₀ S₁ t, ← LMonoTy.subst_compose ρ₀ S₁ (.ftvar a), h3]
  · -- SubstWF: the full composite is well-formed (`bodyComposite_wf`,
    -- via `SubstWF_compose_of_cover` — the inner factor need not be WF).
    show SubstWF (Subst.compose ρ₀ S₁) = true
    exact h_wf_S
  · -- polyKeysFresh: vacuous — every entry of `Γ_int` is mono (`h_mono`), so the
    -- `boundVars ty ≠ []` guard never fires.
    intro a _ x ty h_find h_bv
    exact absurd (h_mono ty (Maps.find?_mem_values Γ_int.types h_find)) h_bv

/-- The gen-prefix guard rejects any input type arg starting with `$__ty`, so a
    successful check implies no `func.typeArgs` element has that reserved prefix. -/
theorem Function.typeCheck_input_typeArgs_no_gen_prefix (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    ∀ ta, ta ∈ func.typeArgs → ¬ ("$__ty".toList.isPrefixOf ta.toList = true) := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  -- `h_genprefix : ¬(func.typeArgs.filter (prefix) != [])`, i.e. the filtered list is empty.
  rw [bne_iff_ne, ne_eq, Decidable.not_not] at h_genprefix
  intro ta hta h_pref
  have h_mem : ta ∈ func.typeArgs.filter
      (fun ta => TState.tyPrefix.toList.isPrefixOf ta.toList) := by
    rw [List.mem_filter]
    exact ⟨hta, by simpa [TState.tyPrefix] using h_pref⟩
  rw [h_genprefix] at h_mem
  exact absurd h_mem (by simp)

/-- Turn the negated `collidesWithAmbient` guard into the per-`typeArg` avoidance fact.
    Shared by the extraction lemma and the body-soundness proof (both `h_ctx_avoids` and
    `h_subin_avoids`), which have the negated guard in scope after unwrapping. -/
theorem Function.not_collidesWithAmbient_avoid (Env : TEnv Unit) (func : Function)
    (h : ¬ Function.collidesWithAmbient Env func = true) :
    ∀ ta, ta ∈ func.typeArgs → ta ∉ Function.ambientTyVars Env := by
  intro ta hta h_in
  apply h
  rw [Function.collidesWithAmbient, List.any_eq_true]
  refine ⟨ta, hta, ?_⟩
  simpa using h_in

/-- A type variable in `knownTypeVars.go` of a `forAll []`-map comes from the freeVars of
    one of the mapped monotypes. Used to split the FORMALS scope of the internal context. -/
theorem mem_go_map_forAll_nil (l : List (CoreLParams.Identifier × LMonoTy)) (v : TyIdentifier)
    (h : v ∈ TContext.types.knownTypeVars.go
      (List.map (fun p => (p.fst, LTy.forAll [] p.snd)) l)) :
    ∃ p ∈ l, v ∈ LMonoTy.freeVars p.snd := by
  induction l with
  | nil => simp [TContext.types.knownTypeVars.go] at h
  | cons hd tl ih =>
    simp only [List.map_cons, TContext.types.knownTypeVars.go, LTy.freeVars,
      List.removeAll_nil, List.mem_append] at h
    rcases h with h_hd | h_tl
    · exact ⟨hd, List.mem_cons_self, h_hd⟩
    · obtain ⟨p, hp, hpv⟩ := ih h_tl
      exact ⟨p, List.mem_cons_of_mem _ hp, hpv⟩

/-- `knownTypeVars` of the internal body-resolution context splits into the FORMALS scope
    (`go FORMALS`) and the ambient `knownTypeVars`. The `pushEmptyContext` head contributes
    nothing; `addInNewestContext` prepends FORMALS as the newest map. -/
theorem knownTypeVars_pushEmpty_addInNewest (Env : TEnv Unit)
    (FORMALS : List (CoreLParams.Identifier × LMonoTy)) :
    TContext.knownTypeVars (Env.pushEmptyContext.addInNewestContext
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd)) FORMALS)).context =
      TContext.types.knownTypeVars.go
          (List.map (fun p => (p.fst, LTy.forAll [] p.snd)) FORMALS) ++
        TContext.knownTypeVars Env.context := by
  simp only [TEnv.pushEmptyContext, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
    Maps.addInNewest, Maps.newest, Maps.pop, Maps.push, TContext.knownTypeVars,
    TContext.types.knownTypeVars]
  rfl

/-- Sibling of `typeCheck_input_typeArgs_no_gen_prefix` for the ambient-collision guard:
    a successful `typeCheck` guarantees no `func.typeArg` collides with an ambient type
    variable of `Env`. Extracted (not assumed) from the `collidesWithAmbient` guard. -/
theorem Function.typeCheck_input_typeArgs_avoid_ambient (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    ∀ ta, ta ∈ func.typeArgs → ta ∉ Function.ambientTyVars Env := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h            -- genprefix pure
  elim_err h            -- concreteEval if
  elim_err h            -- concreteEval pure
  elim_err h            -- isConstr if
  elim_err h            -- isConstr pure
  elim_err h with h_ambient  -- ambient if
  -- `h_ambient : ¬(Function.collidesWithAmbient Env func = true)`.
  exact Function.not_collidesWithAmbient_avoid Env func h_ambient

/-- **Shared: internal-context known-type-vars avoid `func.typeArgs`.** Used by BOTH the body
    (`h_ctx_avoids`) and measure (`hSmKeys`) paths — the internal resolution context
    (`pushEmptyContext.addInNewestContext FORMALS`) has the same shape in both. FORMALS scope →
    `h_inst_avoids`; ambient scope → the ambient-collision guard (`h_avoid_ambient`). -/
theorem Function.internalContext_knownTypeVars_avoid_typeArgs
    (Env : TEnv Unit) (func : Function) (v_inst : LMonoTy × TEnv Unit)
    (h_ctx_eq : v_inst.snd.context = Env.context)
    (h_inst_avoids : ∀ v, v ∈ LMonoTy.freeVars v_inst.fst → v ∉ func.typeArgs)
    (h_avoid_ambient : ∀ ta, ta ∈ func.typeArgs → ta ∉ Function.ambientTyVars Env) :
    ∀ v, v ∈ TContext.knownTypeVars
        (v_inst.snd.pushEmptyContext.addInNewestContext
          (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
            (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context →
        v ∉ func.typeArgs := by
  intro v hv h_ta
  rw [knownTypeVars_pushEmpty_addInNewest, List.mem_append] at hv
  rcases hv with h_formals | h_ambient_kv
  · obtain ⟨p, hp_mem, hpv⟩ := mem_go_map_forAll_nil _ v h_formals
    have hp_slice : p.2 ∈ List.take func.inputs.keys.length v_inst.fst.destructArrow :=
      (List.of_mem_zip hp_mem).2
    have hv_inst : v ∈ LMonoTy.freeVars v_inst.fst :=
      LMonoTy.mem_destructArrow_freeVars_subset v_inst.fst p.2
        (List.mem_of_mem_take hp_slice) hpv
    exact h_inst_avoids v hv_inst h_ta
  · rw [h_ctx_eq] at h_ambient_kv
    have h_amb : v ∈ Function.ambientTyVars Env := by
      rw [Function.ambientTyVars]
      exact List.mem_append_left _ (List.mem_append_left _ h_ambient_kv)
    exact h_avoid_ambient v h_ta h_amb

/-- **Shared: internal-context substitution avoids `func.typeArgs`.** Companion to
    `internalContext_knownTypeVars_avoid_typeArgs` for keys/range of the env's substitution
    (= the ambient substitution, since `pushEmptyContext`/`addInNewestContext`/`instantiateWithCheck`
    do not change it). Used by both the body and measure paths. -/
theorem Function.internalContext_subst_avoid_typeArgs
    (type : LTy) (C : LContext CoreLParams) (Env : TEnv Unit) (func : Function)
    (v_inst : LMonoTy × TEnv Unit)
    (h_inst : LTy.instantiateWithCheck type C Env = .ok v_inst)
    (h_avoid_ambient : ∀ ta, ta ∈ func.typeArgs → ta ∉ Function.ambientTyVars Env) :
    ∀ v, (v ∈ Maps.keys
          (v_inst.snd.pushEmptyContext.addInNewestContext
            (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
              (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).stateSubstInfo.subst ∨
        v ∈ Subst.freeVars
          (v_inst.snd.pushEmptyContext.addInNewestContext
            (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
              (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).stateSubstInfo.subst) →
        v ∉ func.typeArgs := by
  have h_sub_eq : (v_inst.snd.pushEmptyContext.addInNewestContext
      (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
        (func.inputs.keys.zip
          (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).stateSubstInfo.subst
      = Env.stateSubstInfo.subst := by
    rw [TEnv.addInNewestContext_stateSubstInfo]
    show v_inst.snd.stateSubstInfo.subst = Env.stateSubstInfo.subst
    rw [LTy_instantiateWithCheck_preserves_stateSubstInfo type C Env v_inst.fst v_inst.snd
      (by rw [Prod.eta]; exact h_inst)]
  intro v hv h_ta
  rw [h_sub_eq] at hv
  have h_amb : v ∈ Function.ambientTyVars Env := by
    rw [Function.ambientTyVars]
    rcases hv with h_keys | h_range
    · exact List.mem_append_left _ (List.mem_append_right _ h_keys)
    · exact List.mem_append_right _ h_range
  exact h_avoid_ambient v h_ta h_amb

/-- **Instantiated body judgment.** The `typeCheck` pipeline resolves the body in an *instantiated*
    context `Γ_inst` (formals bound to fresh-tyvar, alias-resolved monotypes) at an instantiated
    output `output_inst`, with a renaming `ρ` (fresh → user names) whose application recovers the
    user-facing context/output up to type-alias equivalence. `typeCheck_bodyTyped` then chains
    `talias` (output alias) and `HasType_context_aliasEquiv` (context alias). -/
theorem Function.typeCheck_bodyTyped_instantiated (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    -- TODO(preservation): no context alias is named `"arrow"` (so resolution distributes over the
    -- arrow spine). Enforced by `TEnv.addTypeAlias` (rejects names colliding with `C.knownTypes`).
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- TODO(preservation): ambient bindings' free tyvars are rigid (ambient region of `TContextAliasEquiv`).
    -- Established by ProcedureType.setupInputEnv; preserved by checkAnnotCompat/goBlock; vacuous at top level.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): ambient bindings are monomorphic (`forAll []`), as `TContextAliasEquiv` requires.
    -- Established by setupInputEnv + CmdType var-decls; preserved by checkAnnotCompat/goBlock; vacuous at top level.
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    -- TODO(preservation): aliases are non-dropping (enforced by the `TEnv.addTypeAlias` phantom-arg
    -- guard); makes `AliasEquiv` free-var preserving, needed by `HasType_context_aliasEquiv`'s `tgen`.
    (h_ali_nd : AliasesNonDropping Env.context.aliases)
    (h_arrow_wf : ArrowKnownBinary C) :
    ∀ body, func.body = some body →
      ∃ (Γ_inst : TContext Unit) (output_inst : LMonoTy) (ρ : Subst),
        HasType C (TContext.subst Γ_inst ρ) body (.forAll [] (LMonoTy.subst ρ output_inst)) ∧
        SubstWF ρ ∧
        (TContext.subst Γ_inst ρ).aliases = (funcContext Env.context func).aliases ∧
        TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
          (TContext.subst Γ_inst ρ) (funcContext Env.context func) ∧
        (∀ (x : CoreLParams.Identifier) (ty' : LTy),
          (funcContext Env.context func).types.find? x = some ty' →
          ∀ a, a ∈ LTy.freeVars ty' →
            ∃ ty0, (TContext.subst Γ_inst ρ).types.find? x = some ty0 ∧ a ∈ LTy.freeVars ty0) ∧
        _root_.Lambda.AliasEquiv (funcContext Env.context func).aliases
          (LMonoTy.subst ρ output_inst) func.output := by
  intro body h_body
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h with h_ambient
  elim_err h
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  rw [h_body] at h
  simp only at h
  -- undeclared type-variable guard on the body
  split at h
  · simp only [reduceCtorEq] at h
  -- body = some branch, guard passed
  elim_err h
  rename_i v_resolve h_resolve
  elim_err h
  rename_i v_unify h_unify
  split at h <;> try contradiction
  -- alphaEquivMap = some
  rename_i alphaMap h_alphaMap
  elim_err h
  rename_i bwdMap h_alpha
  -- Extract the rigid-typevar check from `h` before discarding it: the typechecker
  -- only reaches `.ok` when `List.find? (subst ≠ id) rigidTypeVars = none`, i.e. `v_unify.subst`
  -- fixes every rigid type variable. (Needed for Region B of the context-alias conjunct.)
  have h_rigid_fixed : ∀ v ∈ C.rigidTypeVars,
      LMonoTy.subst v_unify.subst (LMonoTy.ftvar v) = LMonoTy.ftvar v := by
    intro v hv
    cases h_find : List.find?
        (fun v => LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst
          (LMonoTy.ftvar v) != LMonoTy.ftvar v) C.rigidTypeVars with
    | some w => rw [h_find] at h; simp only [reduceCtorEq] at h
    | none =>
      have h_all := List.find?_eq_none.mp h_find v hv
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_all
      simpa only [TEnv.updateSubst] using h_all
  -- Extract the generalization guard from `h`: the typechecker only reaches `.ok` when
  -- no to-be-generalized var (free in `subst v_unify.subst v_inst.fst`) is also free in the
  -- substituted ambient context. (Needed for Region B B1b: `renameSubst` keys lie in that
  -- generalized-var set, hence are disjoint from ambient free vars.)
  have h_rigid_none : List.find?
      (fun v => LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst
        (LMonoTy.ftvar v) != LMonoTy.ftvar v) C.rigidTypeVars = none := by
    cases hr : List.find?
        (fun v => LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst
          (LMonoTy.ftvar v) != LMonoTy.ftvar v) C.rigidTypeVars with
    | some w => rw [hr] at h; simp only [reduceCtorEq] at h
    | none => rfl
  rw [h_rigid_none] at h
  simp only [pure, Except.pure] at h
  have h_gen_none : List.find?
      (fun v => (TContext.types.knownTypeVars
        (TContext.types.subst Env.context.types
          (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst)).contains v)
      (LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst v_inst.fst).freeVars = none := by
    cases hg : List.find?
        (fun v => (TContext.types.knownTypeVars
          (TContext.types.subst Env.context.types
            (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst)).contains v)
        (LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst v_inst.fst).freeVars with
    | some w => rw [hg] at h; simp only [reduceCtorEq] at h
    | none => rfl
  clear h
  -- Abbreviations matching the typechecker's terms (no `set`: Strata has no Mathlib).
  let renameSubst : Subst := [renameMap v_unify.subst v_inst.fst.freeVars.eraseDups]
  let userSubst : Subst :=
    [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
  let bodyty : LMonoTy := v_resolve.fst.toLMonoTy
  -- The input signature pairs inserted into the internal env.
  have h_pairs_sig : ∀ p ∈ func.inputs.keys.zip
      (List.take func.inputs.keys.length v_inst.fst.destructArrow),
      p.2 ∈ v_inst.fst.destructArrow := by
    intro p hp
    exact List.mem_of_mem_take (List.of_mem_zip hp).2
  -- Internal env well-formedness (no AliasesResolved needed).
  have h_internalwf := typeCheck_internalEnv_TEnvWF type C Env v_inst.fst v_inst.snd
    (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
    (by rw [Prod.eta]; exact h_inst) h_wf h_pairs_sig
  -- Unwrap the mapError on the unify result.
  have h_unify' : Constraints.unify
      [(LMonoTy.mkArrow'
          ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
            (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
        (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
        v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo = .ok v_unify := by
    cases hc : Constraints.unify
        [(LMonoTy.mkArrow'
            ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
              (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
          (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
          v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo with
    | error e => rw [hc] at h_unify; simp [Except.mapError] at h_unify
    | ok w => rw [hc] at h_unify; simp [Except.mapError] at h_unify; rw [h_unify]
  -- SubstWF facts.
  have h_wf_unify : SubstWF v_unify.subst := v_unify.isWF
  have h_wf_rename : SubstWF renameSubst :=
    substWF_renameMap_new v_unify.subst h_wf_unify v_inst.fst.freeVars.eraseDups
  -- WellScoped on the internal env (knownVars only grows).
  have h_ws_internal : WellScoped body (v_inst.snd.pushEmptyContext.addInNewestContext
      (LFunc.inputMonoSignature
        { name := func.name, typeArgs := v_inst.fst.freeVars.eraseDups, isConstr := func.isConstr,
          isRecursive := func.isRecursive,
          inputs := func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow),
          output :=
            ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                  (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
          body := some body, attr := func.attr, concreteEval := func.concreteEval, axioms := func.axioms,
          preconditions := func.preconditions, measure := func.measure })).context := by
    -- `knownVars` of the internal context = formals' keys ++ `knownVars Env.context`,
    -- so `h_ws`'s membership (into the ambient suffix) lifts via `List.mem_append`.
    have h_ctx_eq : v_inst.snd.context = Env.context :=
      LTy_instantiateWithCheck_context' type C Env v_inst.fst v_inst.snd
        (by rw [Prod.eta]; exact h_inst)
    intro x hx
    have h_amb : x.1 ∈ TContext.knownVars Env.context := h_ws body h_body x hx
    -- The internal `.types` is `<formals signature> :: Env.context.types`.
    show x.1 ∈ TContext.knownVars _
    rw [TContext.knownVars]
    generalize hFSIG : LFunc.inputMonoSignature
        { name := func.name, typeArgs := v_inst.fst.freeVars.eraseDups, isConstr := func.isConstr,
          isRecursive := func.isRecursive,
          inputs := func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow),
          output :=
            ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                  (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
          body := some body, attr := func.attr, concreteEval := func.concreteEval, axioms := func.axioms,
          preconditions := func.preconditions, measure := func.measure } = FSIG
    have h_int_types : (v_inst.snd.pushEmptyContext.addInNewestContext FSIG).context.types
        = FSIG :: Env.context.types := by
      simp only [TEnv.pushEmptyContext, TEnv.addInNewestContext, TEnv.updateContext,
        TEnv.context, Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]
      exact congrArg (FSIG :: ·.types) h_ctx_eq
    show x.1 ∈ TContext.knownVars.go _
    rw [h_int_types]
    show x.1 ∈ _ ++ TContext.knownVars.go Env.context.types
    rw [List.mem_append]
    right
    exact h_amb
  -- The resolve-core typing judgment, universally over absorbing substitutions.
  have h_core := resolve_HasType_core body v_resolve.fst C _ v_resolve.snd
    (by rw [Prod.eta]; exact h_resolve) h_internalwf h_fwf h_ws_internal
  -- Instantiate S := v_unify.subst.
  have h_absorbs : Subst.absorbs v_unify.subst v_resolve.snd.stateSubstInfo.subst :=
    Constraints.unify_absorbs _ _ _ h_unify'
  -- `polyKeysFresh` is vacuous: every binding in the internal context is monomorphic
  -- (formals are `forAll []` by construction; ambient bindings by `h_ambient_mono`), so the
  -- `boundVars ty ≠ []` guard never fires.
  have h_poly_fresh : Subst.polyKeysFresh (T := CoreLParams) v_unify.subst
      (v_inst.snd.pushEmptyContext.addInNewestContext
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context := by
    have h_ctx_eq : v_inst.snd.context = Env.context :=
      LTy_instantiateWithCheck_context' type C Env v_inst.fst v_inst.snd
        (by rw [Prod.eta]; exact h_inst)
    intro a _ x ty h_find h_bv
    -- The internal `.types` is `<formals> :: Env.context.types`; the lookup is monomorphic.
    have h_int_types : (v_inst.snd.pushEmptyContext.addInNewestContext
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.types
        = (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
            (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))
          :: Env.context.types := by
      simp only [TEnv.pushEmptyContext, TEnv.addInNewestContext, TEnv.updateContext,
        TEnv.context, Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]
      exact congrArg (_ :: ·.types) h_ctx_eq
    rw [h_int_types] at h_find
    simp only [Maps.find?] at h_find
    -- `ty` is monomorphic, so `boundVars ty = []`, contradicting `h_bv`.
    have h_mono : LTy.boundVars ty = [] := by
      cases h_fmls : Map.find?
          (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
            (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))) x with
      | some tyF =>
        rw [h_fmls] at h_find
        simp only [Option.some.injEq] at h_find
        -- Formals entries are `forAll [] _`.
        have h_mem := Map.find?_mem _ x tyF h_fmls
        obtain ⟨p, _, hp_eq⟩ := List.mem_map.mp h_mem
        rw [← h_find]
        have h_tyF : tyF = LTy.forAll [] p.2 := (Prod.mk.injEq .. ▸ hp_eq).2.symm
        rw [h_tyF]; rfl
      | none =>
        rw [h_fmls] at h_find
        simp only at h_find
        exact h_ambient_mono ty (Maps.find?_mem_values _ h_find)
    exact absurd h_mono h_bv
  have h_unify_typed := h_core.1 v_unify.subst h_absorbs h_wf_unify h_poly_fresh
  -- `output_inst = subst renameSubst (subst v_unify.subst bodyty)` equals the reconstructed
  -- output RO (in fresh declaration-order instantiation vars); `renameSubst` inverts unify's
  -- renaming via `alphaEquivMap_renameSubst_inverse`.
  have h_unify_eq := Constraints.unify_sound _ _ _ h_unify' _ List.mem_cons_self
  have h_out_eq : LMonoTy.subst renameSubst (LMonoTy.subst v_unify.subst bodyty) =
      ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
          (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
        (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast := by
    have h_inv := renameMap_inverse v_inst.fst
      (((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
          (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
        (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast)
      v_unify.subst alphaMap h_alphaMap
      v_inst.fst.freeVars.eraseDups (fun v => List.mem_eraseDups) (eraseDups_Nodup _)
      (LMonoTy.freeVars_reconstructedOutput_subset v_inst.fst func.inputs.keys.length)
    rw [← h_unify_eq]; exact h_inv
  -- The declaration-order instantiation inverse `ρ` (NOT the appearance-order `userSubst`):
  -- `resolveAliases SIG = subst ρ v_inst.fst` (structural, general form).
  obtain ⟨ρ₀, Env_r, h_wf_ρ, h_ra, h_ρ₀_keys, h_ρ₀_cover, h_ρ₀_range, h_ρ₀_ftvar⟩ :=
    LTy_instantiateWithCheck_inverse type C Env v_inst.fst v_inst.snd
      (by rw [Prod.eta]; exact h_inst) h_wf.aliasesWF (by simpa [bne_iff_ne] using h_undecl)
      (by
        have h_filter_nil : List.filter
            (fun ta => TState.tyPrefix.toList.isPrefixOf ta.toList) func.typeArgs = [] := by
          simpa [bne_iff_ne] using h_genprefix
        intro x hx h_pref
        rw [LFunc.type_boundVars_eq_typeArgs func type h_type] at hx
        have h_mem : x ∈ List.filter
            (fun ta => TState.tyPrefix.toList.isPrefixOf ta.toList) func.typeArgs := by
          rw [List.mem_filter]; exact ⟨hx, by simpa [TState.tyPrefix] using h_pref⟩
        rw [h_filter_nil] at h_mem; exact absurd h_mem (by simp))
  -- The single-scope renaming, packaged as a `Subst` for the downstream lemmas.
  let ρ : Subst := [ρ₀]
  have hρ : ρ = [ρ₀] := rfl
  have h_ρ_keys : ∀ x ∈ Maps.keys ρ, TContext.isFresh (T := CoreLParams) x Env.context := by
    intro x hx
    apply h_ρ₀_keys x
    simpa only [hρ, Maps.keys, Map.keys, List.append_nil] using hx
  -- Per-component alias facts (shared adapter), used by both the output and context conjuncts.
  obtain ⟨h_ae_out, h_ae_ins⟩ :=
    Function.typeCheck_inverse_components C Env func type v_inst ρ Env_r h_type h_ra
      h_wf.aliasesWF h_aliases_not_known
      (by intro mty hmty; apply h_ρ₀_ftvar mty; simpa [hρ, Maps.values, Map.values, List.append_nil] using hmty)
      h_arrow_wf
      (knownInstance_of_instantiateWithCheck type C Env v_inst h_inst)
  -- Assemble the existential. The two context-alias conjuncts are the shared facts.
  have h_cae := Function.contextAliasEquiv_facts C Env func type v_inst ρ v_unify alphaMap
    h_inst h_alphaMap h_gen_none h_rigid_fixed h_ρ_keys
    h_ae_ins h_ambient_rigid h_ambient_mono h_ali_nd
  -- The post-ρ body judgment, obtained by instantiating `resolve_HasType_core.1` at the composite
  -- of `v_unify.subst` with the `renameSubst ∘ ρ` renaming.
  have h_ht_post : HasType C
      (TContext.subst (((v_inst.snd.pushEmptyContext.addInNewestContext
          (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
            (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.subst
          v_unify.subst).subst renameSubst) ρ)
      body
      (.forAll [] (LMonoTy.subst ρ
        (LMonoTy.subst renameSubst (LMonoTy.subst v_unify.subst bodyty)))) := by
    -- A single composite `S` folding `ρ ∘ renameSubst ∘ v_unify.subst` (from `bodyComposite_pack`);
    -- instantiating `h_core.1` at `S` yields the post-ρ judgment.
    -- The internal context is monomorphic: every value is `forAll []` (formals) or
    -- ambient (`h_ambient_mono`). Reuses the reasoning from `h_poly_fresh`.
    have h_mono_ctx : ∀ ty ∈ Maps.values
        (v_inst.snd.pushEmptyContext.addInNewestContext
          (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
            (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.types,
        ty.boundVars = [] :=
      Function.internalContext_values_mono C Env func type v_inst h_inst h_ambient_mono
    -- Provenance facts (below) that `func.typeArgs` never enter instantiation/resolution/unification,
    -- needed by `bodyComposite_wf`; they rest on instantiation freshness and the closed signature
    -- (the `undeclaredVars` guard gives `LTy.freeVars type = []`).
    have h_closed : LTy.freeVars type = [] := by simpa [bne_iff_ne] using h_undecl
    -- A generator name `$__ty<k>` is never a user `typeArg` (the gen-prefix guard `h_genprefix`
    -- says no `func.typeArg` carries the `$__ty` prefix).
    have h_ta_filter_nil : List.filter
        (fun ta => TState.tyPrefix.toList.isPrefixOf ta.toList) func.typeArgs = [] := by
      simpa [bne_iff_ne] using h_genprefix
    have h_gen_avoids : ∀ (k : Nat), (TState.tyPrefix ++ toString k) ∉ func.typeArgs := by
      intro k h_in
      have h_mem : (TState.tyPrefix ++ toString k) ∈ List.filter
          (fun ta => TState.tyPrefix.toList.isPrefixOf ta.toList) func.typeArgs := by
        rw [List.mem_filter]
        exact ⟨h_in, by simp [TState.tyPrefix]⟩
      rw [h_ta_filter_nil] at h_mem
      exact absurd h_mem (by simp)
    have h_inst_avoids : ∀ v, v ∈ LMonoTy.freeVars v_inst.fst → v ∉ func.typeArgs := by
      intro v hv
      obtain ⟨k, h_eq⟩ := instantiateWithCheck_freeVars_gen_prefixed type C Env v_inst.fst v_inst.snd
        (by rw [Prod.eta]; exact h_inst) h_closed h_wf.aliasesWF v hv
      rw [h_eq]; exact h_gen_avoids k
    have h_ctx_eq : v_inst.snd.context = Env.context :=
      LTy_instantiateWithCheck_context' type C Env v_inst.fst v_inst.snd
        (by rw [Prod.eta]; exact h_inst)
    have h_avoid_ambient : ∀ ta, ta ∈ func.typeArgs → ta ∉ Function.ambientTyVars Env :=
      Function.not_collidesWithAmbient_avoid Env func h_ambient
    -- FORMALS scope → `h_inst_avoids`; ambient scope → the ambient-collision guard. Shared lemma.
    have h_ctx_avoids := Function.internalContext_knownTypeVars_avoid_typeArgs Env func v_inst
      h_ctx_eq h_inst_avoids h_avoid_ambient
    -- The internal env's substitution is the ambient one; keys/range ⊆ ambientTyVars. Shared lemma.
    have h_subin_avoids := Function.internalContext_subst_avoid_typeArgs type C Env func v_inst
      h_inst h_avoid_ambient
    have h_resolved_int : TContext.AliasesResolved
        (v_inst.snd.pushEmptyContext.addInNewestContext
          (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
            (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context :=
      (typeCheck_internalEnv_wf type C Env v_inst.fst v_inst.snd
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
        (by rw [Prod.eta]; exact h_inst) h_wf h_resolved h_pairs_sig).2
    -- `v_unify` avoids `func.typeArgs` on keys and range.
    obtain ⟨hVU, hVUr⟩ := Function.vunify_avoids_typeArgs C
      (v_inst.snd.pushEmptyContext.addInNewestContext
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))))
      func v_inst body v_resolve v_unify
      (by rw [Prod.eta]; exact h_resolve) h_internalwf h_fwf h_resolved_int h_unify'
      h_inst_avoids h_ctx_avoids h_subin_avoids h_gen_avoids
    -- Provenance bundle for the composite `SubstWF`.
    obtain ⟨hC1, hC2, hVU', hUT⟩ := Function.bodyComposite_wf_hyps func type v_inst v_unify ρ₀
      h_type h_ρ₀_range h_ρ₀_cover hVU hVUr h_inst_avoids
    -- The composite is `SubstWF` (via `SubstWF_compose_of_cover`; the inner 2-cycle is scrubbed).
    have h_wf_S := Function.bodyComposite_wf func v_inst v_unify ρ₀
      h_wf_ρ hC1 hC2 hVU' hUT
    -- Pack the threefold composite into a single `S` acting as `ρ ∘ rename ∘ v_unify`.
    obtain ⟨S, h_ctx, h_ty, h_abs, h_wf, h_poly⟩ := Function.bodyComposite_pack func
      v_inst v_resolve v_unify ρ ρ₀ bodyty hρ h_absorbs h_mono_ctx h_wf_S
    rw [h_ctx, h_ty]
    exact h_core.1 S h_abs h_wf h_poly
  refine ⟨_, _, ρ, h_ht_post, h_wf_ρ, h_cae.1, h_cae.2.1, h_cae.2.2, ?_⟩
  -- output AliasEquiv
  rw [h_out_eq]
  show Lambda.AliasEquiv Env.context.aliases _ func.output
  exact h_ae_out

/-- `bodyTyped` for the original function: the unresolved body has the declared
    return type polymorphically in the formal-parameter context. Top-down: extract
    the instantiated judgment (with the rename `ρ` already folded in),
    then chain the two alias bridges (`talias` for the output alias,
    `HasType_context_aliasEquiv` for the context alias). -/
theorem Function.typeCheck_bodyTyped (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    -- TODO(preservation): no context alias is named `"arrow"` (so resolution distributes over the arrow spine).
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- TODO(preservation): ambient bindings' free tyvars are rigid.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): ambient bindings are monomorphic (`forAll []`), as `TContextAliasEquiv` requires.
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    -- TODO(preservation): aliases non-dropping; see `typeCheck_bodyTyped_instantiated`.
    (h_ali_nd : AliasesNonDropping Env.context.aliases)
    (h_arrow_wf : ArrowKnownBinary C) :
    ∀ body, func.body = some body →
      HasType C (funcContext Env.context func) body (.forAll [] func.output) := by
  intro body h_body
  obtain ⟨Γ_inst, output_inst, ρ, h_ht, h_wf_ρ, h_alias_eq, h_ctx_ae, h_fresh, h_out_ae⟩ :=
    Function.typeCheck_bodyTyped_instantiated C Env func func' Env' h h_wf h_fwf h_resolved h_ws h_aliases_not_known h_ambient_rigid h_ambient_mono h_ali_nd h_arrow_wf body h_body
  -- `h_ht` is already the post-ρ judgment (ρ folded into the resolve-core substitution).
  -- Bridge 1: alias-bridge the output type `subst ρ output_inst ↝ func.output`.
  have h_out_bridged : HasType C (TContext.subst Γ_inst ρ) body (.forAll [] func.output) := by
    rw [← h_alias_eq] at h_out_ae
    exact HasType.talias _ body _ _ h_out_ae h_ht
  -- Bridge 2: alias-bridge the context `Γ_inst.subst ρ ↝ funcContext Env.context func`.
  -- `HasType_context_aliasEquiv` moves a judgment from Γ (= Γ_inst.subst ρ) to Γ'
  -- (= funcContext …), needing `Γ'.aliases = Γ.aliases`, the equivalence over `Γ.aliases`,
  -- and the Γ'→Γ freshness reflection `h_fresh`. All come from the `_instantiated` result.
  exact HasType_context_aliasEquiv C (TContext.subst Γ_inst ρ) (funcContext Env.context func)
    body (.forAll [] func.output) h_out_bridged h_alias_eq.symm (h_alias_eq ▸ h_ctx_ae) h_fresh

/-- Measure analogue of `bodyComposite_pack`: folds `ρ ∘ Sm` (`Sm` = the measure's resolve
    substitution) into one absorbing, well-formed substitution acting as the composition on the
    measure-base context. The measure type is the ground `.int`, so no type-component is needed. -/
theorem Function.measureComposite_pack
    (v_measure : LExprT ({ Metadata := ExpressionMetadata, IDMeta := Unit } : LExprParams).mono × TEnv Unit)
    (ρ : Subst) (ρ₀ : SubstOne) (Γ_mbase : TContext Unit)
    -- `ρ` is single-scope.
    (h_ρ_single : ρ = [ρ₀])
    -- Every entry of the measure-base context is monomorphic (formals `forAll []`; ambient by
    -- `h_ambient_mono`). Drives the context-composition law and `polyKeysFresh`.
    (h_mono : ∀ ty ∈ Maps.values Γ_mbase.types, LTy.boundVars ty = [])
    -- `SubstWF` of the composite `S = compose ρ₀ Sm`. Supplied by `measureComposite_wf` at the call
    -- site (the measure analogue of `bodyComposite_wf`; the inner `Sm` need not be `SubstWF`).
    (h_wf_S : SubstWF (Subst.compose ρ₀ v_measure.snd.stateSubstInfo.subst) = true) :
    ∃ S : Subst,
        (Γ_mbase.subst v_measure.snd.stateSubstInfo.subst).subst ρ = Γ_mbase.subst S ∧
        S.absorbs v_measure.snd.stateSubstInfo.subst ∧
        SubstWF S = true ∧
        Subst.polyKeysFresh (T := CoreLParams) S Γ_mbase := by
  subst h_ρ_single
  refine ⟨Subst.compose ρ₀ v_measure.snd.stateSubstInfo.subst, ?_, ?_, ?_, ?_⟩
  · exact TContext.subst_compose_forAll_nil ρ₀ v_measure.snd.stateSubstInfo.subst Γ_mbase h_mono
  · intro a t h_find
    have h_self : LMonoTy.subst v_measure.snd.stateSubstInfo.subst t
        = LMonoTy.subst v_measure.snd.stateSubstInfo.subst (.ftvar a) :=
      Subst.absorbs_refl v_measure.snd.stateSubstInfo.subst
        v_measure.snd.stateSubstInfo.isWF a t h_find
    rw [← LMonoTy.subst_compose ρ₀ v_measure.snd.stateSubstInfo.subst t,
        ← LMonoTy.subst_compose ρ₀ v_measure.snd.stateSubstInfo.subst (.ftvar a), h_self]
  · exact h_wf_S
  · intro a _ x ty h_find h_bv
    exact absurd (h_mono ty (Maps.find?_mem_values Γ_mbase.types h_find)) h_bv

/-- `SubstWF` of the measure composite `ρ₀ ∘ Sm`. Simpler than `bodyComposite_wf`: no `renameMap`
    layer, so the inner factor is just the measure-resolve substitution `Sm` (itself `SubstWF`).
    `SubstWF_compose_of_cover` needs `Sm`'s keys to avoid `ρ₀`'s range (`hSmKeys`); the cover
    obligation is vacuous since `Sm` is `SubstWF`. -/
theorem Function.measureComposite_wf (func : Function) (ρ₀ : SubstOne) (Sm : SubstInfo)
    (h_wf_ρ : SubstWF [ρ₀] = true)
    (hC1 : ∀ v, v ∈ Subst.freeVars [ρ₀] → v ∈ func.typeArgs)
    (hSmKeys : ∀ k, k ∈ Maps.keys Sm.subst → k ∉ func.typeArgs) :
    SubstWF (Subst.compose ρ₀ Sm.subst) = true := by
  refine SubstWF_compose_of_cover ρ₀ Sm.subst h_wf_ρ ?hkeys ?hcover
  case hkeys =>
    intro k hk h_in_rho
    exact hSmKeys k hk (hC1 k h_in_rho)
  case hcover =>
    -- Vacuous: `Sm` is `SubstWF`, so no key of `Sm` is free in `Sm`.
    intro k hk h_fv
    exfalso
    have hwf := Sm.isWF
    simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at hwf
    exact hwf k hk h_fv

/-- **Instantiated measure judgment.** As `typeCheck_bodyTyped_instantiated`, but
    for a non-variable measure: the measure resolves at type `int` in the
    instantiated context, and the renaming `ρ` recovers `funcContext func`'s context
    up to type-alias equivalence. The output type is `.int`, which is alias-free and
    fixed by `ρ`, so only the *context* alias bridge is needed (no output bridge). -/
theorem Function.typeCheck_measureTyped_instantiated (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    -- TODO(preservation): no context alias is named `"arrow"` (so resolution distributes over the arrow spine).
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- TODO(preservation): ambient bindings' free tyvars are rigid.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): ambient bindings are monomorphic (`forAll []`), as `TContextAliasEquiv` requires.
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    -- TODO(preservation): the measure is well-scoped (needed by the resolve-based `HasType` route;
    -- not derivable from resolution alone). Parsed measures use no reserved `$__` names.
    (h_ws_measure : ∀ m, func.measure = some m → WellScoped m Env.context)
    -- TODO(preservation): aliases non-dropping; see `typeCheck_bodyTyped_instantiated`.
    (h_ali_nd : AliasesNonDropping Env.context.aliases)
    (h_arrow_wf : ArrowKnownBinary C) :
    ∀ m, func.measure = some m →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      ∃ (Γ_inst : TContext Unit) (ρ : Subst),
        HasType C (TContext.subst Γ_inst ρ) m (.forAll [] .int) ∧
        SubstWF ρ ∧
        (TContext.subst Γ_inst ρ).aliases = (funcContext Env.context func).aliases ∧
        TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
          (TContext.subst Γ_inst ρ) (funcContext Env.context func) ∧
        (∀ (x : CoreLParams.Identifier) (ty' : LTy),
          (funcContext Env.context func).types.find? x = some ty' →
          ∀ a, a ∈ LTy.freeVars ty' →
            ∃ ty0, (TContext.subst Γ_inst ρ).types.find? x = some ty0 ∧ a ∈ LTy.freeVars ty0) := by
  intro m h_measure h_nonfvar
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  -- A measure on a bodiless function is rejected, so `func.body = some body`.
  split at h
  · -- body = none: the measure guard rejects, contradiction with `func.measure = some m`.
    rename_i h_body_none
    split at h
    · simp only [reduceCtorEq] at h
    · rename_i h_measure_none
      rw [Option.not_isSome_iff_eq_none] at h_measure_none
      rw [h_measure] at h_measure_none
      simp only [reduceCtorEq] at h_measure_none
  · rename_i body h_body_some
    rw [h_body_some] at h
    simp only at h
    -- undeclared type-variable guard on the body
    split at h
    · simp only [reduceCtorEq] at h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    rename_i alphaMap h_alphaMap
    elim_err h
    rename_i bwdMap h_alpha
    -- Extract the rigid-typevar check (Region B of the context-alias conjunct).
    have h_rigid_fixed : ∀ v ∈ C.rigidTypeVars,
        LMonoTy.subst v_unify.subst (LMonoTy.ftvar v) = LMonoTy.ftvar v := by
      intro v hv
      cases h_find : List.find?
          (fun v => LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst
            (LMonoTy.ftvar v) != LMonoTy.ftvar v) C.rigidTypeVars with
      | some w => rw [h_find] at h; simp only [reduceCtorEq] at h
      | none =>
        have h_all := List.find?_eq_none.mp h_find v hv
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_all
        simpa only [TEnv.updateSubst] using h_all
    have h_rigid_none : List.find?
        (fun v => LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst
          (LMonoTy.ftvar v) != LMonoTy.ftvar v) C.rigidTypeVars = none := by
      cases hr : List.find?
          (fun v => LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst
            (LMonoTy.ftvar v) != LMonoTy.ftvar v) C.rigidTypeVars with
      | some w => rw [hr] at h; simp only [reduceCtorEq] at h
      | none => rfl
    rw [h_rigid_none] at h
    simp only [pure, Except.pure] at h
    have h_gen_none : List.find?
        (fun v => (TContext.types.knownTypeVars
          (TContext.types.subst Env.context.types
            (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst)).contains v)
        (LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst v_inst.fst).freeVars = none := by
      cases hg : List.find?
          (fun v => (TContext.types.knownTypeVars
            (TContext.types.subst Env.context.types
              (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst)).contains v)
          (LMonoTy.subst (v_resolve.snd.updateSubst v_unify).stateSubstInfo.subst v_inst.fst).freeVars with
      | some w => rw [hg] at h; simp only [reduceCtorEq] at h
      | none => rfl
    rw [h_gen_none] at h
    simp only [] at h
    -- Now peel the measure branch. Rewrite `func.measure` to `some m` so the
    -- outer match reduces to the `some` arm.
    rw [h_measure] at h
    simp only at h
    -- The measure resolves (`h_measure_resolve`); the int check and the new
    -- refine-guard both pass on the success path.
    elim_err h
    rename_i v_measure h_measure_resolve
    elim_err h
    rename_i h_measure_int
    elim_err h
    rename_i h_measure_norefine
    clear h
    -- The signature inputs inserted into the internal/measure-base env.
    let SIG : Map (Identifier CoreLParams.IDMeta) LMonoTy :=
      func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)
    -- The measure-base env: formals pushed, BEFORE the body's unification.
    -- `h_measure_resolve` resolves the measure here, under the rigidified `Cm`.
    let Cm : LContext CoreLParams :=
      { C with rigidTypeVars := v_inst.fst.freeVars.eraseDups ++ C.rigidTypeVars }
    let measureBaseEnv : TEnv Unit :=
      v_inst.snd.pushEmptyContext.addInNewestContext (LFunc.inputMonoSignature
        { name := func.name, typeArgs := v_inst.fst.freeVars.eraseDups, isConstr := func.isConstr,
          isRecursive := func.isRecursive, inputs := SIG,
          output := ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
          body := some body, attr := func.attr, concreteEval := func.concreteEval, axioms := func.axioms,
          preconditions := func.preconditions, measure := func.measure })
    let Sm : Subst := v_measure.snd.stateSubstInfo.subst
    -- The measure-base context = FORMALS :: Env.context.types.
    let FORMALS : Map (Identifier CoreLParams.IDMeta) LTy :=
      List.map (fun p => (p.fst, LTy.forAll [] p.snd)) SIG
    -- The input signature pairs inserted into the internal env.
    have h_pairs_sig : ∀ p ∈ func.inputs.keys.zip
        (List.take func.inputs.keys.length v_inst.fst.destructArrow),
        p.2 ∈ v_inst.fst.destructArrow := by
      intro p hp
      exact List.mem_of_mem_take (List.of_mem_zip hp).2
    -- Internal/measure-base env well-formedness.
    have h_internalwf : TEnvWF (T := CoreLParams) measureBaseEnv :=
      typeCheck_internalEnv_TEnvWF type C Env v_inst.fst v_inst.snd SIG
        (by rw [Prod.eta]; exact h_inst) h_wf h_pairs_sig
    have h_ctx_eq : v_inst.snd.context = Env.context :=
      LTy_instantiateWithCheck_context' type C Env v_inst.fst v_inst.snd
        (by rw [Prod.eta]; exact h_inst)
    -- The base context the measure resolves in is `FORMALS :: ambient`.
    have h_base_types : measureBaseEnv.context.types = FORMALS :: Env.context.types := by
      simp only [measureBaseEnv, FORMALS, SIG, TEnv.pushEmptyContext, TEnv.addInNewestContext,
        TEnv.updateContext, TEnv.context, Maps.addInNewest, Maps.newest, Maps.pop, Maps.push,
        LFunc.inputMonoSignature]
      exact congrArg (_ :: TContext.types ·) h_ctx_eq
    -- WellScoped of the measure on the measure-base env (knownVars only grows over ambient).
    -- Mirrors the body's `h_ws_internal`: `h_ws_measure`'s membership lifts via `List.mem_append`.
    have h_ws_measure_internal : WellScoped m measureBaseEnv.context := by
      intro x hx
      have h_amb : x.1 ∈ TContext.knownVars Env.context := h_ws_measure m h_measure x hx
      show x.1 ∈ TContext.knownVars _
      rw [TContext.knownVars, show measureBaseEnv.context.types = FORMALS :: Env.context.types
        from h_base_types]
      show x.1 ∈ _ ++ TContext.knownVars.go Env.context.types
      rw [List.mem_append]
      right
      exact h_amb
    -- The resolve-core typing judgment for the measure, under `Cm`.
    have h_core := resolve_HasType_core m v_measure.fst Cm _ v_measure.snd
      (by rw [Prod.eta]; exact h_measure_resolve) h_internalwf h_fwf h_ws_measure_internal
    -- `polyKeysFresh Sm`: every binding in the measure-base context is monomorphic
    -- (formals are `forAll []`; ambient by `h_ambient_mono`), so the guard never fires.
    have h_poly_fresh : Subst.polyKeysFresh (T := CoreLParams) Sm measureBaseEnv.context := by
      intro a _ x ty h_find h_bv
      rw [show measureBaseEnv.context.types = FORMALS :: Env.context.types from h_base_types] at h_find
      rw [Maps.find?] at h_find
      have h_mono : LTy.boundVars ty = [] := by
        cases h_fmls : Map.find? FORMALS x with
        | some tyF =>
          rw [h_fmls] at h_find
          simp only [Option.some.injEq] at h_find
          have h_mem := Map.find?_mem FORMALS x tyF h_fmls
          obtain ⟨p, _, hp_eq⟩ := List.mem_map.mp h_mem
          rw [← h_find]
          have h_tyF : tyF = LTy.forAll [] p.2 := (Prod.mk.injEq .. ▸ hp_eq).2.symm
          rw [h_tyF]; rfl
        | none =>
          rw [h_fmls] at h_find
          simp only at h_find
          exact h_ambient_mono ty (Maps.find?_mem_values _ h_find)
      exact absurd h_mono h_bv
    -- Instantiate the resolve-core judgment at `S := Sm` (absorbs reflexively).
    have h_sm_typed := h_core.1 Sm (Subst.absorbs_refl Sm v_measure.snd.stateSubstInfo.isWF)
      v_measure.snd.stateSubstInfo.isWF h_poly_fresh
    -- The measure type collapses to `int`: `subst Sm (toLMonoTy) = toLMonoTy` (idempotence)
    -- and `toLMonoTy = .int` (the int check `h_measure_int`).
    have h_int : v_measure.fst.toLMonoTy = .int := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_measure_int
      exact h_measure_int
    rw [h_core.2.1, h_int] at h_sm_typed
    -- L1b: `Sm` is the identity on every visible binding of the measure-base context
    -- (`h_measure_norefine`: `Sm` fixes every var in `v_inst.fst.freeVars.eraseDups ++
    -- C.rigidTypeVars`, ⊇ all free vars of the formals/ambient context).
    have h_find_eq : ∀ x,
        Maps.find? (measureBaseEnv.context.subst Sm).types x =
          Maps.find? (FORMALS :: Env.context.types) x := by
      intro x
      rw [TContext.subst]
      rw [show measureBaseEnv.context.types = FORMALS :: Env.context.types from h_base_types]
      cases h_base : Maps.find? (FORMALS :: Env.context.types) x with
      | none => rw [TContext_types_subst_find_none _ _ _ h_base]
      | some ty0 =>
        rw [TContext_types_subst_find _ Sm x ty0 h_base]
        rw [Maps.find?] at h_base
        have h_id : LTy.subst Sm ty0 = ty0 := by
          cases h_formals : Map.find? FORMALS x with
          | some tyF =>
            rw [h_formals] at h_base
            simp only [Option.some.injEq] at h_base
            subst h_base
            have h_mem := Map.find?_mem FORMALS x tyF h_formals
            obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp h_mem
            have h_tyF : tyF = LTy.forAll [] p.2 := (Prod.mk.injEq .. ▸ hp_eq).2.symm
            have hp_slice : p.2 ∈ List.take func.inputs.keys.length v_inst.fst.destructArrow :=
              (List.of_mem_zip hp_mem).2
            have h_fv : ∀ v ∈ LMonoTy.freeVars p.2, v ∈ v_inst.fst.freeVars.eraseDups := by
              intro v hv
              rw [List.mem_eraseDups]
              exact LMonoTy.mem_destructArrow_freeVars_subset v_inst.fst p.2
                (List.mem_of_mem_take hp_slice) hv
            have h_pm_id : LMonoTy.subst Sm p.2 = p.2 := by
              have h_eq := agree_on_freeVars_implies_subst_eq (S₁ := Sm) (S₂ := [])
                (ty := p.2) (fun v hv => by
                  have h_fix := List.find?_eq_none.mp h_measure_norefine v
                    (List.mem_append_left _ (h_fv v hv))
                  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_fix
                  rw [h_fix, LMonoTy.subst_emptyS (by rfl)])
              rw [h_eq, LMonoTy.subst_emptyS (by rfl)]
            rw [h_tyF, LTy.subst_forAll_nil, h_pm_id]
          | none =>
            rw [h_formals] at h_base
            simp only at h_base
            have h_bv : LTy.boundVars ty0 = [] := h_ambient_mono ty0 (Maps.find?_mem_values _ h_base)
            cases ty0 with
            | forAll xs mty0 =>
              simp only [LTy.boundVars] at h_bv
              subst h_bv
              have h_fv : ∀ v ∈ LMonoTy.freeVars mty0, v ∈ C.rigidTypeVars := by
                intro v hv
                have h_lv := h_ambient_rigid x (LTy.forAll [] mty0) h_base v
                rw [LTy.freeVars, List.removeAll_nil] at h_lv
                exact h_lv hv
              have h_m_id : LMonoTy.subst Sm mty0 = mty0 := by
                have h_eq := agree_on_freeVars_implies_subst_eq (S₁ := Sm) (S₂ := [])
                  (ty := mty0) (fun v hv => by
                    have h_fix := List.find?_eq_none.mp h_measure_norefine v
                      (List.mem_append_right _ (h_fv v hv))
                    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_fix
                    rw [h_fix, LMonoTy.subst_emptyS (by rfl)])
                rw [h_eq, LMonoTy.subst_emptyS (by rfl)]
              rw [LTy.subst_forAll_nil, h_m_id]
        rw [h_id]
    -- Obtain the renaming `ρ` (fresh → user, single scope) and per-component alias facts.
    obtain ⟨ρ₀, Env_r, h_wf_ρ, h_ra, h_ρ₀_keys, h_ρ₀_cover, h_ρ₀_range, h_ρ₀_ftvar⟩ :=
      LTy_instantiateWithCheck_inverse type C Env v_inst.fst v_inst.snd
        (by rw [Prod.eta]; exact h_inst) h_wf.aliasesWF (by simpa [bne_iff_ne] using h_undecl)
        (by
          have h_filter_nil : List.filter
              (fun ta => TState.tyPrefix.toList.isPrefixOf ta.toList) func.typeArgs = [] := by
            simpa [bne_iff_ne] using h_genprefix
          intro x hx h_pref
          rw [LFunc.type_boundVars_eq_typeArgs func type h_type] at hx
          have h_mem : x ∈ List.filter
              (fun ta => TState.tyPrefix.toList.isPrefixOf ta.toList) func.typeArgs := by
            rw [List.mem_filter]; exact ⟨hx, by simpa [TState.tyPrefix] using h_pref⟩
          rw [h_filter_nil] at h_mem; exact absurd h_mem (by simp))
    let ρ : Subst := [ρ₀]
    have hρ : ρ = [ρ₀] := rfl
    have h_ρ_keys : ∀ x ∈ Maps.keys ρ, TContext.isFresh (T := CoreLParams) x Env.context := by
      intro x hx
      apply h_ρ₀_keys x
      simpa only [hρ, Maps.keys, Map.keys, List.append_nil] using hx
    obtain ⟨_, h_ae_ins⟩ :=
      Function.typeCheck_inverse_components C Env func type v_inst ρ Env_r h_type h_ra
        h_wf.aliasesWF h_aliases_not_known
        (by intro mty hmty; apply h_ρ₀_ftvar mty; simpa [hρ, Maps.values, Map.values, List.append_nil] using hmty)
        h_arrow_wf
        (knownInstance_of_instantiateWithCheck type C Env v_inst h_inst)
    -- `measureBaseEnv.context.aliases = Env.context.aliases` (addInNewest touches only types).
    have h_aliases0 : measureBaseEnv.context.aliases = Env.context.aliases := by
      have e : measureBaseEnv.context.aliases = v_inst.snd.context.aliases := rfl
      rw [e, h_ctx_eq]
    -- The two shared context-alias conjuncts via the factored base lemma.
    have h_cae := Function.contextAliasEquiv_base Env func v_inst ρ
      (measureBaseEnv.context.subst Sm)
      (by rw [TContext.subst_aliases]; exact h_aliases0) h_ρ_keys h_ae_ins h_ambient_mono
      h_ali_nd h_find_eq
    -- The post-ρ measure judgment, from instantiating `resolve_HasType_core.1` at the composite of
    -- `Sm` with ρ. `subst ρ .int = .int` (int is ground).
    have h_sm_post : HasType C ((measureBaseEnv.context.subst Sm).subst ρ) m
        (.forAll [] .int) := by
      -- A single composite `S` folding `ρ ∘ Sm` (from `measureComposite_pack`). The measure type is
      -- the ground `.int`, so only the context needs the composite; `h_core.1` is under the
      -- rigidified `Cm`, bridged to `C` via `HasType.of_rigidTypeVars_irrel`.
      -- Measure-base context is monomorphic (FORMALS `forAll []` ++ ambient mono).
      have h_mono_mbase : ∀ ty ∈ Maps.values measureBaseEnv.context.types, LTy.boundVars ty = [] := by
        intro ty h_mem
        rw [h_base_types, Maps.values.eq_def, List.mem_append] at h_mem
        rcases h_mem with h_formals | h_ambient
        · exact mem_values_map_forAll_nil_boundVars _ ty h_formals
        · exact h_ambient_mono ty h_ambient
      -- ρ₀-range ⊆ user typeArgs (from `right✝` + `type.boundVars = typeArgs`).
      have h_type_bv : LTy.boundVars type = func.typeArgs :=
        LFunc.type_boundVars_eq_typeArgs (T := CoreLParams) func type h_type
      have hC1 : ∀ v, v ∈ Subst.freeVars [ρ₀] → v ∈ func.typeArgs := by
        intro v hv; rw [← h_type_bv]; exact h_ρ₀_range v hv
      -- Sm-keys avoid typeArgs: measure analogue of `vunify_avoids_typeArgs`, directly from
      -- `resolve_freeVars_pred`'s output-subst conjunct (no unify step for the measure resolve).
      -- Discharged in the same layer as `resolve_freeVars_pred` (+ its `h_gen` fix); the internal
      -- context/subst facts are the already-proven `h_ctx_avoids`/`h_subin_avoids` analogues.
      have hSmKeys : ∀ k, k ∈ Maps.keys Sm → k ∉ func.typeArgs := by
        have h_closed : LTy.freeVars type = [] := by simpa [bne_iff_ne] using h_undecl
        have h_ta_filter_nil : List.filter
            (fun ta => TState.tyPrefix.toList.isPrefixOf ta.toList) func.typeArgs = [] := by
          simpa [bne_iff_ne] using h_genprefix
        have h_gen_avoids : ∀ (j : Nat), (TState.tyPrefix ++ toString j) ∉ func.typeArgs := by
          intro j h_in
          have h_mem : (TState.tyPrefix ++ toString j) ∈ List.filter
              (fun ta => TState.tyPrefix.toList.isPrefixOf ta.toList) func.typeArgs := by
            rw [List.mem_filter]; exact ⟨h_in, by simp [TState.tyPrefix]⟩
          rw [h_ta_filter_nil] at h_mem; exact absurd h_mem (by simp)
        have h_inst_avoids : ∀ v, v ∈ LMonoTy.freeVars v_inst.fst → v ∉ func.typeArgs := by
          intro v hv
          obtain ⟨j, h_eq⟩ := instantiateWithCheck_freeVars_gen_prefixed type C Env
            v_inst.fst v_inst.snd (by rw [Prod.eta]; exact h_inst) h_closed h_wf.aliasesWF v hv
          rw [h_eq]; exact h_gen_avoids j
        have h_avoid_ambient : ∀ ta, ta ∈ func.typeArgs → ta ∉ Function.ambientTyVars Env :=
          Function.not_collidesWithAmbient_avoid Env func (by assumption)
        have h_resolved_m : TContext.AliasesResolved measureBaseEnv.context := by
          have h_vinst_res : TContext.AliasesResolved v_inst.snd.context := by
            rw [h_ctx_eq]; exact h_resolved
          exact TContext.AliasesResolved.of_addInNewestContext (T := CoreLParams) _ _
            (TContext.AliasesResolved.of_pushEmptyContext (T := CoreLParams) v_inst.snd h_vinst_res)
        have hpred := resolve_freeVars_pred m v_measure.fst Cm measureBaseEnv v_measure.snd
          (by rw [Prod.eta]; exact h_measure_resolve) h_internalwf h_fwf h_resolved_m
          (· ∉ func.typeArgs)
          (Function.internalContext_knownTypeVars_avoid_typeArgs Env func v_inst
            h_ctx_eq h_inst_avoids h_avoid_ambient)
          (Function.internalContext_subst_avoid_typeArgs type C Env func v_inst
            h_inst h_avoid_ambient)
          (fun v k h_eq => h_eq ▸ h_gen_avoids k)
        intro k hk
        exact hpred.2 k (Or.inl hk)
      have h_wf_S : SubstWF (Subst.compose ρ₀ Sm) = true :=
        Function.measureComposite_wf func ρ₀ v_measure.snd.stateSubstInfo h_wf_ρ hC1 hSmKeys
      obtain ⟨S, h_ctx, h_abs, h_wf, h_poly⟩ :=
        Function.measureComposite_pack v_measure ρ ρ₀ measureBaseEnv.context
          hρ h_mono_mbase h_wf_S
      rw [h_ctx]
      have h_typed := h_core.1 S h_abs h_wf h_poly
      rw [h_int] at h_typed
      simp only [LMonoTy.subst_unfold] at h_typed
      exact HasType.of_rigidTypeVars_irrel h_typed
    exact ⟨measureBaseEnv.context.subst Sm, ρ,
      h_sm_post, h_wf_ρ, h_cae.1, h_cae.2.1, h_cae.2.2⟩

/-- `measureTyped` for the original function: a non-variable measure has type `int`. -/
theorem Function.typeCheck_measureTyped (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    -- TODO(preservation): no context alias is named `"arrow"` (so resolution distributes over the arrow spine).
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- TODO(preservation): ambient bindings' free tyvars are rigid.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): ambient bindings are monomorphic (`forAll []`), as `TContextAliasEquiv` requires.
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    -- Measure well-scopedness; see `typeCheck_measureTyped_instantiated`.
    (h_ws_measure : ∀ m, func.measure = some m → WellScoped m Env.context)
    -- TODO(preservation): aliases non-dropping; see `typeCheck_bodyTyped_instantiated`.
    (h_ali_nd : AliasesNonDropping Env.context.aliases)
    (h_arrow_wf : ArrowKnownBinary C) :
    ∀ m, func.measure = some m →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      HasType C (funcContext Env.context func) m (.forAll [] .int) := by
  intro m h_measure h_nonfvar
  obtain ⟨Γ_inst, ρ, h_ht, h_wf_ρ, h_alias_eq, h_ctx_ae, h_fresh⟩ :=
    Function.typeCheck_measureTyped_instantiated C Env func func' Env' h h_wf h_fwf h_resolved h_aliases_not_known h_ambient_rigid h_ambient_mono h_ws_measure h_ali_nd h_arrow_wf m h_measure h_nonfvar
  -- `h_ht` is already the post-ρ judgment at output `.int`; no output bridge needed.
  -- Bridge: alias-bridge the context only (with the Γ'→Γ freshness reflection `h_fresh`).
  exact HasType_context_aliasEquiv C (TContext.subst Γ_inst ρ) (funcContext Env.context func)
    m (.forAll [] .int) h_ht h_alias_eq.symm (h_alias_eq ▸ h_ctx_ae) h_fresh

/--
Polymorphic soundness: if `Function.typeCheck` succeeds, the original function
satisfies `FuncHasType`.
-/
theorem Function.typeCheck_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    -- TODO(preservation): no context alias is named `"arrow"` (so resolution distributes over the arrow spine).
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- TODO(preservation): ambient bindings' free tyvars are rigid.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): ambient bindings are monomorphic (`forAll []`), as `TContextAliasEquiv` requires.
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    -- Measure well-scopedness; see `typeCheck_measureTyped_instantiated`.
    (h_ws_measure : ∀ m, func.measure = some m → WellScoped m Env.context)
    -- TODO(preservation): aliases non-dropping; see `typeCheck_bodyTyped_instantiated`.
    (h_ali_nd : AliasesNonDropping Env.context.aliases)
    (h_arrow_wf : ArrowKnownBinary C) :
    FuncHasType C Env.context func := by
  exact {
    inputsNodup := Function.typeCheck_inputsNodup_orig C Env func func' Env' h
    typeArgsNodup := Function.typeCheck_typeArgsNodup_orig C Env func func' Env' h
    noUndeclaredVars := Function.typeCheck_noUndeclaredVars_orig C Env func func' Env' h
    bodyTyped := Function.typeCheck_bodyTyped C Env func func' Env' h h_wf h_fwf h_resolved h_ws h_aliases_not_known h_ambient_rigid h_ambient_mono h_ali_nd h_arrow_wf
    measureTyped := Function.typeCheck_measureTyped C Env func func' Env' h h_wf h_fwf h_resolved h_aliases_not_known h_ambient_rigid h_ambient_mono h_ws_measure h_ali_nd h_arrow_wf
  }

/-- `Function.typeCheck` copies `concreteEval` and `isConstr` unchanged from the input
    `func` to the result `func'` in every successful branch. -/
theorem Function.typeCheck_concreteEval_isConstr_preserved
    (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func'.concreteEval = func.concreteEval ∧ func'.isConstr = func.isConstr := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  split at h
  · -- body = none
    split at h
    · simp at h
    · cases h; exact ⟨rfl, rfl⟩
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    rename_i alphaMap h_alphaMap
    elim_err h
    rename_i bwdMap h_alpha
    elim_err h
    elim_err h
    elim_err h
    elim_err h
    split at h
    · split at h
      · elim_err h; cases h; exact ⟨rfl, rfl⟩
      · elim_err h
        rename_i v_measure h_measure_resolve
        elim_err h
        rename_i h_measure_ty
        elim_err h; cases h; exact ⟨rfl, rfl⟩
    · elim_err h; cases h; exact ⟨rfl, rfl⟩

/-- The early guards in `Function.typeCheck` reject any function with a `concreteEval`
    or that is a constructor, so a successful check implies the *input* `func` has
    `concreteEval = none` and `isConstr = false`. -/
theorem Function.typeCheck_input_concreteEval_none_isConstr_false
    (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func.concreteEval = none ∧ func.isConstr = false := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h with h_ce
  elim_err h
  elim_err h with h_ic
  refine ⟨?_, ?_⟩
  · simpa using h_ce
  · simpa using h_ic

/-- Combining preservation with the guard extraction: every accepted `func'` has no
    `concreteEval` and is not a constructor. -/
theorem Function.typeCheck_concreteEval_none_isConstr_false
    (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func'.concreteEval = none ∧ func'.isConstr = false := by
  obtain ⟨h_ce, h_ic⟩ := Function.typeCheck_concreteEval_isConstr_preserved C Env func func' Env' h
  obtain ⟨h_ce', h_ic'⟩ := Function.typeCheck_input_concreteEval_none_isConstr_false C Env func func' Env' h
  exact ⟨h_ce.trans h_ce', h_ic.trans h_ic'⟩

/-- In every successful branch, `func'.typeArgs = map Prod.snd (_.zip func.typeArgs)`,
    a sublist of `func.typeArgs`; so every type arg of the result is a type arg of the
    input. -/
theorem Function.typeCheck_typeArgs_subset (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    ∀ ta, ta ∈ func'.typeArgs → ta ∈ func.typeArgs := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  have h_close : ∀ (vs : List TyIdentifier),
      ∀ ta, ta ∈ List.map (fun x => x.snd) (vs.zip func.typeArgs) → ta ∈ func.typeArgs := by
    intro vs ta hta
    exact (List.map_snd_zip_sublist vs func.typeArgs).subset hta
  split at h
  · -- body = none
    split at h
    · simp at h
    · cases h; exact h_close _
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    rename_i alphaMap h_alphaMap
    elim_err h
    rename_i bwdMap h_alpha
    elim_err h
    elim_err h
    elim_err h
    elim_err h
    split at h
    · split at h
      · elim_err h; cases h; exact h_close _
      · elim_err h
        rename_i v_measure h_measure_resolve
        elim_err h
        rename_i h_measure_ty
        elim_err h; cases h; exact h_close _
    · elim_err h; cases h; exact h_close _

/-- **Bridge: a successfully type-checked function is `LFuncWF`.**
    If `Function.typeCheck` succeeds, the resulting `func'` satisfies the structural
    well-formedness predicate `LFuncWF`. Lets downstream consumers obtain `LFuncWF func'`
    directly from a successful type-check, rather than re-establishing each field. -/
theorem Function.typeCheck_LFuncWF (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    Lambda.LFuncWF func' := by
  obtain ⟨h_ce_none, h_ic_false⟩ :=
    Function.typeCheck_concreteEval_none_isConstr_false C Env func func' Env' h
  refine { toFuncWF := ?_, constr_no_eval := ?_, typeArgs_no_gen_prefix := ?_,
           concreteEval_eraseMetadata := ?_ }
  · -- toFuncWF
    refine { arg_nodup := ?_, concreteEval_argmatch := ?_,
             body_or_concreteEval := ?_, typeArgs_nodup := ?_,
             inputs_typevars_in_typeArgs := ?_, output_typevars_in_typeArgs := ?_ }
    · -- arg_nodup: key-nodup ⟹ name-nodup (Identifier name is injective for Unit meta)
      have h_keys := Function.typeCheck_inputsNodup C Env func func' Env' h
      rw [ListMap.keys_eq_map_fst] at h_keys
      have h_eq : List.map (fun x : CoreLParams.Identifier × LMonoTy => x.fst.name) func'.inputs
          = List.map (fun i : CoreLParams.Identifier => i.name) (List.map Prod.fst func'.inputs) := by
        rw [List.map_map]; rfl
      rw [h_eq]
      refine List.Pairwise.map _ ?_ h_keys
      intro a b hab; cases a; cases b; simp_all
    · -- concreteEval_argmatch: vacuous (concreteEval = none)
      intro fn _ _ _ hfn; rw [h_ce_none] at hfn; exact absurd hfn (by simp)
    · -- body_or_concreteEval: concreteEval = none, so left conjunct false
      rw [h_ce_none]; simp
    · -- typeArgs_nodup
      exact Function.typeCheck_typeArgsNodup C Env func func' Env' h
    · -- inputs_typevars_in_typeArgs
      have h_undecl := Function.typeCheck_noUndeclaredVars C Env func func' Env' h h_wf
      intro ty hty v hv
      apply h_undecl v
      rw [LMonoTy.freeVars_mkArrow', List.mem_append]
      exact Or.inl (LMonoTys.freeVars_mem_subset hty hv)
    · -- output_typevars_in_typeArgs
      have h_undecl := Function.typeCheck_noUndeclaredVars C Env func func' Env' h h_wf
      intro v hv
      apply h_undecl v
      rw [LMonoTy.freeVars_mkArrow', List.mem_append]
      exact Or.inr hv
  · -- constr_no_eval: isConstr = false, premise false
    rw [h_ic_false]; simp
  · -- typeArgs_no_gen_prefix: func'.typeArgs ⊆ func.typeArgs, none of which has the prefix
    intro ta hta
    exact Function.typeCheck_input_typeArgs_no_gen_prefix C Env func func' Env' h ta
      (Function.typeCheck_typeArgs_subset C Env func func' Env' h ta hta)
  · -- concreteEval_eraseMetadata: vacuous (concreteEval = none)
    intro ceval hc; rw [h_ce_none] at hc; exact absurd hc (by simp)

end TypeSpec
end Core
