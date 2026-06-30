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

/-- **Region A parallel walk.** The formals scope `keys.zip slice` (mapped to `forAll []`)
    and the funcContext input scope `inputs` (mapped to `forAll []`) share the keys
    `keys = inputs.map fst`. For a key `x` found in the formals scope returning
    `forAll [] s` (so `s = slice[i]`), the funcContext scope returns `forAll [] (inputs.values[i])`,
    and the pointwise `AliasEquivList aliases (f <$> slice) inputs.values` gives
    `AliasEquiv aliases (f s) inputs.values[i]`. Stated over the underlying lists with an
    arbitrary post-map `f` (instantiated to `subst ρ` at the call site). -/
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

/-! ### New `renameSubst` (built directly from the instantiation variable list)

The checker (`FunctionType.lean`) builds the fresh→instantiation renaming directly
from `monoty.freeVars.eraseDups` as the *inverse* of the unifier `S` on those vars:
```
renameMap S vs = vs.filterMap (fun x => match subst S (ftvar x) with
  | .ftvar y => if x == y then none else some (y, .ftvar x) | _ => none)
```
The `alphaEquivMap` check (kept as a boolean guard) still guarantees `subst S` acts
as an injective variable renaming on `monoty`'s vars — that fact (irreducible) comes
from `alphaEquivMap_self_subst_bwd`/`_inverts`. These lemmas establish the lookup /
`SubstWF` / inverse properties of the new map, replacing the old `bwdMap`-shaped
plumbing. -/

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
    the composed substitution `subst userSubst (subst renameSubst (subst S bodyty))`
    equals `subst userSubst output_mty`. This captures the full type equality chain
    needed for bodyTyped. The `h_sub` precondition (output free vars ⊆ monoty free vars)
    is what lets `alphaEquivMap_renameSubst_inverse` apply to `output_mty`; it holds at the
    call site because `output_mty` is a component of `monoty.destructArrow`. -/
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

/-- The internal typing environment the body typechecker builds — push an empty
    scope, then insert the monomorphic input signature — is well-formed and
    aliases-resolved, given that each inserted input monotype is a component of
    `monoty.destructArrow` (which holds by construction: the inputs are
    `func.inputs.keys.zip (take n monoty.destructArrow)`). This packages the
    internal-env preservation chain so the three measure branches of `bodyTyped`
    can invoke `resolve_HasTypeA`/`resolve_AbsWF`. -/
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
    exact LMonoTy.freeVars_subst_closed (a :: rest) (tgts.take (a :: rest).length) h_len W
      h_closed hSNE v hv

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
        exact LMonoTy.freeVars_subst_closed (a :: rest) freshtvs h_flen body h_sub hSNE v hv
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
  -- The shared "closing" fact: any constructed `func'` of the branch shape has the property.
  -- `W` is the pre-rename signature monotype; its free vars are all in `monoty.freeVars`.
  -- `h_close` works on the *whole* `subst userSubst (mkArrow' RO ins)` term (RO = reconstructed
  -- output). Its free vars are all in `monoty.freeVars` (inputs are destructArrow slices, RO is
  -- the reconstructed output), so D1 applies.
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
      simp_all
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
      simp_all
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
          -- Resolve the measure and apply userSubst.
          -- The measure now resolves under the rigidified context `Cm` (signature
          -- type params rigid) and the *internal* env (formals pushed, pre-unify),
          -- not the post-body env. `Cm.functions = C.functions`, and the internal env
          -- is already proved WF + AliasesResolved (`h_envwf_internal`/
          -- `h_resolved_internal`); `HasTypeA` ignores the rigid field. Infer `C`/`Env`
          -- from `h_measure_resolve`.
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
  rename_i h_undecl
  have h_closed : LTy.freeVars type = [] := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_undecl
    exact h_undecl
  -- Decompose `func.type` to get `type = .forAll func.typeArgs sigBody` with an explicit `sigBody`
  -- determined by `func.inputs.values`.
  simp only [LFunc.type, bind, Except.bind, pure, Except.pure] at h_type
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

/-- **Shared per-component alias adapter.** Consumes the general structural inverse
    `LTy_instantiateWithCheck_inverse` (which gives a renaming `ρ` with
    `resolveAliases SIG = subst ρ v_inst.fst`, where `SIG = toMonoTypeUnsafe type` is the
    raw signature monotype) and produces the two *per-component* alias facts the
    `_instantiated` lemmas need, for BOTH `bodyTyped` and `measureTyped`:

    - **output:** `AliasEquiv aliases (subst ρ RO) func.output`, where `RO` is the
      reconstructed output (`mkArrow'` of the `drop n` destructArrow slice);
    - **inputs:** `AliasEquivList aliases (subst ρ (take n da)) func.inputs.values`.

    Both follow by peeling the `n = inputs.length` leading arrows of `SIG` (valid because
    no alias is named `"arrow"`, so `resolveAliases` distributes over the arrow spine),
    then `resolveAliases_aliasEquiv` on each raw component. The arrow-spine slicing is
    sound even for arrow-bodied aliases: inputs sit in atomic `t1` positions of
    `destructArrow`, so `take n` recovers exactly the `n` resolved inputs (verified). -/
theorem Function.typeCheck_inverse_components (C : LContext CoreLParams) (Env : TEnv Unit)
    (func : Function) (type : LTy) (v_inst : LMonoTy × TEnv Unit) (ρ : Subst) (Env_r : TEnv Unit)
    (h_type : LFunc.type func = .ok type)
    (h_ra : LMonoTy.resolveAliases (LTy.toMonoTypeUnsafe type) Env
      = .ok (LMonoTy.subst ρ v_inst.fst, Env_r))
    (h_aw : TContext.AliasesWF Env.context)
    (h_aliases_not_known : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow") :
    -- output component
    (Lambda.AliasEquiv Env.context.aliases
      (LMonoTy.subst ρ
        (((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
            (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
          (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast))
      func.output) ∧
    -- input components
    (Lambda.AliasEquivList Env.context.aliases
      (LMonoTy.subst ρ <$> (List.take func.inputs.keys.length v_inst.fst.destructArrow))
      func.inputs.values) := by
  sorry

/-- **Shared context-alias core.** The genuinely-common part of the body and measure
    context-alias proofs, parameterized over the resolution context `Γ0` by a single
    `find?`-agreement hypothesis `h_find_eq` against the base context `FORMALS :: ambient`.
    Given that agreement, the two conjuncts — `.aliases`-equality and `TContextAliasEquiv`
    against `funcContext Env.context func` — follow from the single renaming `ρ` alone:
    Region A (formals) via `region_a_input_lookup` + `h_ae_ins`; Region B (ambient) via
    `h_ambient_mono` + ρ-freshness. NONE of the inner-substitution machinery (`v_unify`,
    `renameSubst`, `bwdMap`, the alias/gen/rigid guards) appears here — each consumer
    establishes `h_find_eq` for its own inner layers (body: roundtrip + §10j/#1399 guards;
    measure: the L1b context-subst-identity) and then calls this. -/
theorem Function.contextAliasEquiv_base (Env : TEnv Unit)
    (func : Function) (v_inst : LMonoTy × TEnv Unit) (ρ : Subst)
    (Γ0 : TContext Unit)
    (h_aliases0 : Γ0.aliases = Env.context.aliases)
    (h_ρ_keys : ∀ x ∈ Maps.keys ρ, TContext.isFresh (T := CoreLParams) x Env.context)
    (h_ae_ins : AliasEquivList Env.context.aliases
      (LMonoTy.subst ρ <$> List.take func.inputs.keys.length v_inst.fst.destructArrow)
      func.inputs.values)
    (h_ambient_mono : ∀ x ty, Env.context.types.find? x = some ty →
      LTy.boundVars ty = [])
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
      (TContext.subst Γ0 ρ) (funcContext Env.context func) := by
  refine ⟨?_, ?_⟩
  · -- aliases equality: ρ preserves aliases; `funcContext` keeps `Env`'s aliases.
    rw [TContext.subst_aliases, h_aliases0]
    rfl
  · -- TContextAliasEquiv
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
      have h_bv : LTy.boundVars ty1 = [] := h_ambient_mono x ty1 h1
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

/-- **Shared context-alias facts.** Both `typeCheck_bodyTyped_instantiated` and
    `typeCheck_measureTyped_instantiated` resolve their subject (body / measure) in the
    SAME internal context `Γ_inst = ((FORMALS :: ambient).subst v_unify.subst).subst
    renameSubst` (the measure resolves in the post-unify env, whose context equals the
    body-resolution context; instantiating its `resolve_HasType_core` at `S := v_unify.subst`
    recovers the identical witness). So the two context-alias conjuncts — `.aliases`-equality
    and `TContextAliasEquiv` against `funcContext Env.context func` — are literally the same
    goals for both, factored here. Region A (formals) reuses the per-input `h_ae_ins`; Region B
    (ambient) uses the §10j rigid check + #1399 gen guard + ρ-freshness to show the triple
    substitution is the identity on ambient bindings. This wrapper proves the body's `h_find_eq`
    (its `v_unify`+`renameSubst` layers are the identity on visible bindings) and delegates the
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
    (h_ambient_mono : ∀ x ty, Env.context.types.find? x = some ty →
      LTy.boundVars ty = []) :
    let FORMALS : Map (Identifier CoreLParams.IDMeta) LTy :=
      List.map (fun p => (p.fst, LTy.forAll [] p.snd))
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
    let renameSubst : Subst := [renameMap v_unify.subst v_inst.fst.freeVars.eraseDups]
    let Γ_inst : TContext Unit :=
      ((v_inst.snd.pushEmptyContext.addInNewestContext FORMALS).context.subst v_unify.subst).subst renameSubst
    (TContext.subst Γ_inst ρ).aliases = (funcContext Env.context func).aliases ∧
    TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
      (TContext.subst Γ_inst ρ) (funcContext Env.context func) := by
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
  -- Region A (formals) uses the alpha-equiv roundtrip; Region B (ambient) uses the §10j
  -- rigid check + #1399 gen guard. The ρ-walk + funcContext matching is delegated to
  -- `contextAliasEquiv_base`.
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
          have h_bv : LTy.boundVars ty0 = [] := h_ambient_mono x ty0 h_base
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
    h_aliases0 h_ρ_keys h_ae_ins h_ambient_mono h_find_eq

/-- The internal body-resolution context `(FORMALS :: ambient)` is monomorphic: every
    value is `forAll [] _` (formals by construction; ambient by `h_ambient_mono`). Stated
    over `Maps.values` so it captures every physical entry (drives `TContext.subst`
    composition and `polyKeysFresh` in `bodyComposite_pack`). -/
theorem Function.internalContext_values_mono (C : LContext CoreLParams) (Env : TEnv Unit)
    (func : Function) (type : LTy) (v_inst : LMonoTy × TEnv Unit)
    (h_inst : type.instantiateWithCheck C Env = .ok v_inst)
    (h_ambient_mono : ∀ x ty, Env.context.types.find? x = some ty → LTy.boundVars ty = []) :
    ∀ ty ∈ Maps.values
      (v_inst.snd.pushEmptyContext.addInNewestContext
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.types,
      ty.boundVars = [] := by
  -- LAYER-3 LEAF — see ALPHAEQUIV_RENAMESUBST_PLAN.md §10k (mono-context obligation).
  sorry

/-- **`v_unify` avoids the user type arguments.** Every key and range variable of the
    body's return-type unification substitution `v_unify` is disjoint from `func.typeArgs`.
    This is the route-critical provenance fact behind `SubstWF` of the Route B composite:
    the offending `a ↦ a` entries (which would break `SubstWF`) cannot arise because no
    user type argument ever enters `v_unify`. Proved top-down from:
    `resolve_freeVars_pred` (body type + resolve subst avoid `typeArgs`, the deep leaf),
    `Constraints.unify_pred` (transfer through unification), and
    `LMonoTy.freeVars_reconstructedOutput_subset` (the reconstructed-output side of the
    constraint lies in `freeVars v_inst.fst`). The three remaining hypotheses are the
    instantiation-side closure facts (`hA`: instantiated signature vars avoid `typeArgs`;
    `h_ctx`/`h_subin`: the internal resolution context/substitution avoid `typeArgs`),
    discharged at the call site / by the `$__ty`-provenance leaves. -/
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
                      v ∈ Subst.freeVars Env_int.stateSubstInfo.subst) → v ∉ func.typeArgs) :
    (∀ k, k ∈ Maps.keys v_unify.subst → k ∉ func.typeArgs) ∧
    (∀ k, k ∈ Subst.freeVars v_unify.subst → k ∉ func.typeArgs) := by
  obtain ⟨hB, hC⟩ := resolve_freeVars_pred body v_resolve.fst C Env_int v_resolve.snd
    h_resolve h_envwf h_fwf h_resolved (· ∉ func.typeArgs) h_ctx h_subin
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
    proof consumes, so the call site obtains them in one step (no `sorry` in the main proof body):
    - `hC1`/`hC2`: the ρ₀-contract — ρ₀'s range is the user type arguments, and ρ₀'s keys cover the
      instantiation variables. From the (to-be-strengthened) `LTy_instantiateWithCheck_inverse`.
    - `hVU`/`hUT`: the v_unify provenance — `v_unify`'s keys and the unified type's variables avoid
      `func.typeArgs`. From `Function.vunify_avoids_typeArgs` (+ its `$__ty`-world chain).

    LAYER-3 LEAF (sorry body) — detailed proof plan in ALPHAEQUIV_RENAMESUBST_PLAN.md §10m. -/
theorem Function.bodyComposite_wf_hyps (C : LContext CoreLParams) (Env : TEnv Unit)
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

/-- **ROUTE B composite is `SubstWF` (body).** The full sequential composite
    `S = compose ρ₀ (compose rs₀ v_unify)` is well-formed. Proved via
    `SubstWF_compose_of_cover` (NOT factor-by-factor `SubstWF.compose`: the inner
    `compose rs₀ v_unify` is generally NOT itself `SubstWF` — it can carry a self-identity
    entry `(x, ftvar x)` when the unified type reuses an instantiation var `x`; `ρ₀` scrubs
    that entry because `x ∈ keys ρ₀`). `hkeys` (inner-composite keys avoid `ρ₀`'s range) and
    `hcover` (self-referential inner keys are covered by `ρ₀`) are proved here from the
    `bodyComposite_wf_hyps` bundle; only the inverse-pairing self-ref characterization (`hSelf`)
    remains a sub-leaf. -/
theorem Function.bodyComposite_wf (C : LContext CoreLParams) (Env : TEnv Unit)
    (func : Function) (type : LTy) (v_inst : LMonoTy × TEnv Unit)
    (v_unify : SubstInfo) (ρ₀ : SubstOne)
    (h_wf_ρ : SubstWF [ρ₀] = true)
    -- ρ₀-contract from (strengthened) `LTy_instantiateWithCheck_inverse`:
    -- C1: ρ₀'s range is the user type arguments; C2: ρ₀'s keys cover the instantiation vars.
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
    -- A key of the inner composite that is also in its range must be an instantiation var.
    -- `freeVars_compose_subset_scrub` splits the range into `freeVars[rs₀]` and the scrubbed
    -- `freeVars v_unify`; the latter is impossible for a key (it would violate `SubstWF v_unify`),
    -- so the var occurs in `rs₀`'s values, hence lies in `freeVars v_inst.fst.eraseDups`.
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

/-- **ROUTE B composite (body).** The single substitution `S` folding the threefold
    `ρ ∘ renameSubst ∘ v_unify.subst` into one absorbing, well-formed substitution
    (built sequentially via `Subst.apply`, NOT a flat scope merge — see plan §10c).
    `S` acts as the composition on the internal context and on `bodyty`, absorbs the
    resolve substitution, is `SubstWF`, and is `polyKeysFresh` over the (monomorphic)
    internal context. Instantiating `resolve_HasType_core.1` at `S` once yields the
    post-ρ body judgment, replacing the FALSE `HasType_TContext_subst` bridge.

    Layer-2 helper: its body is the genuinely-new content of Route B. The `SubstWF`
    conjunct needs `ρ`'s range disjoint from the unify/instantiation variables, which
    is exposed by (the to-be-strengthened) `LTy_instantiateWithCheck_inverse`. -/
theorem Function.bodyComposite_pack (C : LContext CoreLParams) (Env : TEnv Unit)
    (func : Function) (type : LTy) (v_inst : LMonoTy × TEnv Unit)
    (v_resolve : LExprT ({ Metadata := ExpressionMetadata, IDMeta := Unit } : LExprParams).mono × TEnv Unit)
    (v_unify : SubstInfo) (ρ : Subst) (ρ₀ : SubstOne)
    (bodyty : LMonoTy)
    -- `ρ` is single-scope (from the strengthened `LTy_instantiateWithCheck_inverse`).
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
    -- `bodyComposite_wf` (the route-critical leaf). NOT decomposed factor-by-factor: the inner
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
  · -- SubstWF: the full composite is well-formed (route-critical leaf `bodyComposite_wf`,
    -- via `SubstWF_compose_of_cover` — the inner factor need not be WF).
    show SubstWF (Subst.compose ρ₀ S₁) = true
    exact h_wf_S
  · -- polyKeysFresh: vacuous — every entry of `Γ_int` is mono (`h_mono`), so the
    -- `boundVars ty ≠ []` guard never fires.
    intro a _ x ty h_find h_bv
    exact absurd (h_mono ty (Maps.find?_mem_values Γ_int.types h_find)) h_bv

/-- **Instantiated body judgment.** The `typeCheck` pipeline resolves the body in
    an *instantiated* context `Γ_inst` (formals bound to fresh-tyvar, alias-resolved
    monotypes) at an instantiated output `output_inst`, and constructs a renaming
    `ρ` (fresh → user names). Applying `ρ` to the whole judgment recovers the
    user-facing context/output *up to type-alias equivalence* (the body is checked
    against alias-resolved types, but the spec uses the raw `func` signature). The
    top-level `typeCheck_bodyTyped` then chains three bridges: `HasType_TContext_subst`
    (rename `ρ`), `talias` (output alias), `HasType_context_aliasEquiv` (context alias). -/
theorem Function.typeCheck_bodyTyped_instantiated (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    -- TODO(preservation): every context alias name is a non-reserved (non-knownType) name.
    -- This is enforced by `TEnv.addTypeAlias` (LExprTypeEnv:1348, which rejects type decls whose
    -- name collides with `C.knownTypes`) but is not yet captured as a context invariant. It must
    -- be threaded as a property preserved by the type-decl / function typechecker and discharged at
    -- the call site. Needed to decompose the signature `AliasEquiv` along the arrow spine
    -- (`"arrow" ∈ C.knownTypes`, so no alias can restructure an arrow).
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- TODO(preservation): every free tyvar in an ambient binding is rigid (∈ C.rigidTypeVars).
    -- *Established* by ProcedureType.setupInputEnv: params are added using exactly the fresh
    -- vars registered as rigidTypeVars. *Preserved* by checkAnnotCompat (var-decls store the
    -- closed annotation and reject rigid-var refinement) and goBlock (empty scopes). *Vacuous*
    -- at top level (rigidTypeVars = []).
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): every ambient binding is monomorphic (`boundVars = []`).
    -- *Established* by ProcedureType.setupInputEnv (params/old-vars stored as `forAll [] _`)
    -- and the poly-init removal in CmdType (local `var` decls now store only `forAll [] _`).
    -- *Preserved* by checkAnnotCompat + goBlock. *Vacuous* at top level (types = []).
    -- Needed for Region B of the `TContextAliasEquiv` conjunct: a polymorphic ambient entry
    -- (e.g. `forAll [a] (a→a)`, closed yet poly) would break the `forAll []` shape the
    -- relation requires, and is exactly what the `var`-init fix rules out.
    (h_ambient_mono : ∀ x ty, Env.context.types.find? x = some ty →
      LTy.boundVars ty = []) :
    ∀ body, func.body = some body →
      ∃ (Γ_inst : TContext Unit) (output_inst : LMonoTy) (ρ : Subst),
        HasType C (TContext.subst Γ_inst ρ) body (.forAll [] (LMonoTy.subst ρ output_inst)) ∧
        SubstWF ρ ∧
        (TContext.subst Γ_inst ρ).aliases = (funcContext Env.context func).aliases ∧
        TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
          (TContext.subst Γ_inst ρ) (funcContext Env.context func) ∧
        _root_.Lambda.AliasEquiv (funcContext Env.context func).aliases
          (LMonoTy.subst ρ output_inst) func.output := by
  intro body h_body
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
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
  -- Extract the §10j rigid-typevar check from `h` before discarding it: the typechecker
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
  -- Extract the #1399 generalization guard from `h`: the typechecker only reaches `.ok` when
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
        exact h_ambient_mono x ty h_find
    exact absurd h_mono h_bv
  have h_unify_typed := h_core.1 v_unify.subst h_absorbs h_wf_unify h_poly_fresh
  -- `output_inst = subst renameSubst (subst v_unify.subst bodyty)` equals the reconstructed
  -- output RO (in fresh declaration-order instantiation vars); `renameSubst` inverts unify's
  -- renaming via `alphaEquivMap_renameSubst_inverse`. (Note: NO `userSubst`; see §10g.)
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
  obtain ⟨ρ₀, Env_r, h_wf_ρ, h_ra, h_ρ₀_keys, h_ρ₀_cover, h_ρ₀_range⟩ :=
    LTy_instantiateWithCheck_inverse type C Env v_inst.fst v_inst.snd
      (by rw [Prod.eta]; exact h_inst) h_wf.aliasesWF
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
  -- Assemble the existential. The two context-alias conjuncts are the shared facts.
  have h_cae := Function.contextAliasEquiv_facts C Env func type v_inst ρ v_unify alphaMap
    h_inst h_alphaMap h_gen_none h_rigid_fixed h_ρ_keys
    h_ae_ins h_ambient_rigid h_ambient_mono
  -- ROUTE B: the post-ρ body judgment, obtained by instantiating `resolve_HasType_core.1`
  -- at the composite of `v_unify.subst` with the (renameSubst ∘ ρ) renaming — NOT via the
  -- (false) `HasType_TContext_subst`. Stubbed here; discharged in step 3 below.
  have h_ht_post : HasType C
      (TContext.subst (((v_inst.snd.pushEmptyContext.addInNewestContext
          (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
            (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.subst
          v_unify.subst).subst renameSubst) ρ)
      body
      (.forAll [] (LMonoTy.subst ρ
        (LMonoTy.subst renameSubst (LMonoTy.subst v_unify.subst bodyty)))) := by
    -- ROUTE B: a single composite `S` folding the threefold substitution
    -- `ρ ∘ renameSubst ∘ v_unify.subst`, supplied by the layer-2 helper
    -- `bodyComposite_pack`. Instantiating `h_core.1` at `S` once yields the post-ρ
    -- judgment, since `S` acts as the composition on the internal context + `bodyty`
    -- and satisfies the resolve side-conditions.
    -- The internal context is monomorphic: every value is `forAll []` (formals) or
    -- ambient (`h_ambient_mono`). Reuses the reasoning from `h_poly_fresh`.
    have h_mono_ctx : ∀ ty ∈ Maps.values
        (v_inst.snd.pushEmptyContext.addInNewestContext
          (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
            (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.types,
        ty.boundVars = [] :=
      Function.internalContext_values_mono C Env func type v_inst h_inst h_ambient_mono
    -- The internal env resolve ran in: `Env_int = pushEmptyContext.addInNewestContext FORMALS`.
    -- `LFunc.inputMonoSignature {…}` reduces to the `forAll []`-map FORMALS, so the
    -- `h_core`/`h_resolve` env matches `bodyComposite_pack`'s `Γ_int`.
    -- Provenance facts that `func.typeArgs` (user names) never enter the instantiation /
    -- resolution / unification — required by `bodyComposite_wf` to scrub the inner 2-cycle.
    -- These rest on instantiation freshness (`$__ty`-prefix vars vs no-gen-prefix `typeArgs`).
    have h_inst_avoids : ∀ v, v ∈ LMonoTy.freeVars v_inst.fst → v ∉ func.typeArgs := by
      sorry
    have h_ctx_avoids : ∀ v, v ∈ TContext.knownTypeVars
        (v_inst.snd.pushEmptyContext.addInNewestContext
          (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
            (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context →
        v ∉ func.typeArgs := by
      sorry
    have h_subin_avoids : ∀ v, (v ∈ Maps.keys
          (v_inst.snd.pushEmptyContext.addInNewestContext
            (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
              (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).stateSubstInfo.subst ∨
        v ∈ Subst.freeVars
          (v_inst.snd.pushEmptyContext.addInNewestContext
            (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
              (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).stateSubstInfo.subst) →
        v ∉ func.typeArgs := by
      sorry
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
      h_inst_avoids h_ctx_avoids h_subin_avoids
    -- Provenance bundle for the composite `SubstWF`.
    obtain ⟨hC1, hC2, hVU', hUT⟩ := Function.bodyComposite_wf_hyps C Env func type v_inst v_unify ρ₀
      h_type h_ρ₀_range h_ρ₀_cover hVU hVUr h_inst_avoids
    -- The composite is `SubstWF` (via `SubstWF_compose_of_cover`; the inner 2-cycle is scrubbed).
    have h_wf_S := Function.bodyComposite_wf C Env func type v_inst v_unify ρ₀
      h_wf_ρ hC1 hC2 hVU' hUT
    -- Pack the threefold composite into a single `S` acting as `ρ ∘ rename ∘ v_unify`.
    obtain ⟨S, h_ctx, h_ty, h_abs, h_wf, h_poly⟩ := Function.bodyComposite_pack C Env func type
      v_inst v_resolve v_unify ρ ρ₀ bodyty hρ h_absorbs h_mono_ctx h_wf_S
    rw [h_ctx, h_ty]
    exact h_core.1 S h_abs h_wf h_poly
  refine ⟨_, _, ρ, h_ht_post, h_wf_ρ, h_cae.1, h_cae.2, ?_⟩
  · -- output AliasEquiv
    rw [h_out_eq]
    show Lambda.AliasEquiv Env.context.aliases _ func.output
    exact h_ae_out

/-- `bodyTyped` for the original function: the unresolved body has the declared
    return type polymorphically in the formal-parameter context. Top-down: extract
    the instantiated judgment + renaming, then chain the three bridges
    (`HasType_TContext_subst` for tyvars, `talias` for the output alias,
    `HasType_context_aliasEquiv` for the context alias). -/
theorem Function.typeCheck_bodyTyped (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    -- TODO(preservation): see `typeCheck_bodyTyped_instantiated`. Context alias names are
    -- non-reserved (enforced by `TEnv.addTypeAlias`); to be discharged as a preserved invariant.
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- Ambient-rigidity invariant; see `typeCheck_bodyTyped_instantiated`.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): every ambient binding is monomorphic (`boundVars = []`).
    -- *Established* by ProcedureType.setupInputEnv (params/old-vars stored as `forAll [] _`)
    -- and the poly-init removal in CmdType (local `var` decls now store only `forAll [] _`).
    -- *Preserved* by checkAnnotCompat + goBlock. *Vacuous* at top level (types = []).
    -- Needed for Region B of the `TContextAliasEquiv` conjunct: a polymorphic ambient entry
    -- (e.g. `forAll [a] (a→a)`, closed yet poly) would break the `forAll []` shape the
    -- relation requires, and is exactly what the `var`-init fix rules out.
    (h_ambient_mono : ∀ x ty, Env.context.types.find? x = some ty →
      LTy.boundVars ty = []) :
    ∀ body, func.body = some body →
      HasType C (funcContext Env.context func) body (.forAll [] func.output) := by
  intro body h_body
  obtain ⟨Γ_inst, output_inst, ρ, h_ht, h_wf_ρ, h_alias_eq, h_ctx_ae, h_out_ae⟩ :=
    Function.typeCheck_bodyTyped_instantiated C Env func func' Env' h h_wf h_fwf h_resolved h_ws h_aliases_not_known h_ambient_rigid h_ambient_mono body h_body
  -- `h_ht` is ALREADY the post-ρ judgment (ROUTE B: ρ folded into the resolve-core
  -- substitution, no `HasType_TContext_subst`).
  -- Bridge 1: alias-bridge the output type `subst ρ output_inst ↝ func.output`.
  have h_out_bridged : HasType C (TContext.subst Γ_inst ρ) body (.forAll [] func.output) := by
    rw [← h_alias_eq] at h_out_ae
    exact HasType.talias _ body _ _ h_out_ae h_ht
  -- Bridge 2: alias-bridge the context `Γ_inst.subst ρ ↝ funcContext Env.context func`.
  -- `HasType_context_aliasEquiv` moves a judgment from Γ (= Γ_inst.subst ρ) to Γ'
  -- (= funcContext …), needing `Γ'.aliases = Γ.aliases` and the equivalence stated
  -- over `Γ.aliases`. Both come from `h_alias_eq` / `h_ctx_ae` after orienting.
  refine HasType_context_aliasEquiv C (TContext.subst Γ_inst ρ) (funcContext Env.context func)
    body (.forAll [] func.output) h_out_bridged h_alias_eq.symm ?_
  rw [h_alias_eq]; exact h_ctx_ae

/-- **ROUTE B composite (measure).** The measure analogue of `bodyComposite_pack`,
    folding `ρ ∘ Sm` (`Sm = v_measure`'s resolve substitution) into one absorbing,
    well-formed substitution acting as the composition on the measure-base context.
    The measure type is the ground `.int`, so no type-component conjunct is needed.

    Layer-2 helper: shares the `SubstWF`-of-sequential-composite content with the
    body case (plan §10c). -/
theorem Function.measureComposite_pack (C : LContext CoreLParams) (Env : TEnv Unit)
    (func : Function) (v_inst : LMonoTy × TEnv Unit)
    (v_measure : LExprT ({ Metadata := ExpressionMetadata, IDMeta := Unit } : LExprParams).mono × TEnv Unit)
    (ρ : Subst) (Γ_mbase : TContext Unit) :
    ∃ S : Subst,
        (Γ_mbase.subst v_measure.snd.stateSubstInfo.subst).subst ρ = Γ_mbase.subst S ∧
        S.absorbs v_measure.snd.stateSubstInfo.subst ∧
        SubstWF S = true ∧
        Subst.polyKeysFresh (T := CoreLParams) S Γ_mbase := by
  sorry

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
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    -- TODO(preservation): see `typeCheck_bodyTyped_instantiated`. Context alias names are
    -- non-reserved (enforced by `TEnv.addTypeAlias`); to be discharged as a preserved invariant.
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- Ambient-rigidity invariant; see `typeCheck_bodyTyped_instantiated`.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): every ambient binding is monomorphic (`boundVars = []`).
    -- *Established* by ProcedureType.setupInputEnv (params/old-vars stored as `forAll [] _`)
    -- and the poly-init removal in CmdType (local `var` decls now store only `forAll [] _`).
    -- *Preserved* by checkAnnotCompat + goBlock. *Vacuous* at top level (types = []).
    -- Needed for Region B of the `TContextAliasEquiv` conjunct: a polymorphic ambient entry
    -- (e.g. `forAll [a] (a→a)`, closed yet poly) would break the `forAll []` shape the
    -- relation requires, and is exactly what the `var`-init fix rules out.
    (h_ambient_mono : ∀ x ty, Env.context.types.find? x = some ty →
      LTy.boundVars ty = [])
    -- A decreases clause is a parsed expression whose free variables are the
    -- function's parameters (in scope once the formals are pushed). Mirrors the
    -- body's `h_ws`: the resolve-based `HasType` route needs the subject to be
    -- well-scoped. NOT derivable from successful resolution — `genVar` only
    -- guarantees the binder is fresh for the *context*, not for the expression,
    -- so a captured `$__var`-prefixed fvar could resolve yet be ill-scoped.
    -- TODO(preservation): discharge as an invariant (parsed measures cannot use
    -- reserved `$__` names; their refs are exactly the declared parameters).
    (h_ws_measure : ∀ m, func.measure = some m → WellScoped m Env.context) :
    ∀ m, func.measure = some m →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      ∃ (Γ_inst : TContext Unit) (ρ : Subst),
        HasType C (TContext.subst Γ_inst ρ) m (.forAll [] .int) ∧
        SubstWF ρ ∧
        (TContext.subst Γ_inst ρ).aliases = (funcContext Env.context func).aliases ∧
        TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
          (TContext.subst Γ_inst ρ) (funcContext Env.context func) := by
  intro m h_measure h_nonfvar
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h with h_genprefix
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
    -- Extract the §10j rigid-typevar check (Region B of the context-alias conjunct).
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
    simp only [pure, Except.pure] at h
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
          exact h_ambient_mono x ty h_find
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
            have h_bv : LTy.boundVars ty0 = [] := h_ambient_mono x ty0 h_base
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
    obtain ⟨ρ₀, Env_r, h_wf_ρ, h_ra, h_ρ₀_keys, _, _⟩ :=
      LTy_instantiateWithCheck_inverse type C Env v_inst.fst v_inst.snd
        (by rw [Prod.eta]; exact h_inst) h_wf.aliasesWF
    let ρ : Subst := [ρ₀]
    have hρ : ρ = [ρ₀] := rfl
    have h_ρ_keys : ∀ x ∈ Maps.keys ρ, TContext.isFresh (T := CoreLParams) x Env.context := by
      intro x hx
      apply h_ρ₀_keys x
      simpa only [hρ, Maps.keys, Map.keys, List.append_nil] using hx
    obtain ⟨_, h_ae_ins⟩ :=
      Function.typeCheck_inverse_components C Env func type v_inst ρ Env_r h_type h_ra
        h_wf.aliasesWF h_aliases_not_known
    -- `measureBaseEnv.context.aliases = Env.context.aliases` (addInNewest touches only types).
    have h_aliases0 : measureBaseEnv.context.aliases = Env.context.aliases := by
      have e : measureBaseEnv.context.aliases = v_inst.snd.context.aliases := rfl
      rw [e, h_ctx_eq]
    -- The two shared context-alias conjuncts via the factored base lemma.
    have h_cae := Function.contextAliasEquiv_base Env func v_inst ρ
      (measureBaseEnv.context.subst Sm)
      (by rw [TContext.subst_aliases]; exact h_aliases0) h_ρ_keys h_ae_ins h_ambient_mono h_find_eq
    -- ROUTE B: the post-ρ measure judgment, obtained by instantiating `resolve_HasType_core.1`
    -- at the composite of `Sm` with ρ — NOT via the (false) `HasType_TContext_subst`. Stubbed
    -- here; discharged in step 3 (shared with the body). `subst ρ .int = .int` (int is ground).
    have h_sm_post : HasType C ((measureBaseEnv.context.subst Sm).subst ρ) m
        (.forAll [] .int) := by
      -- ROUTE B: a single composite `S` folding `ρ ∘ Sm`, from the layer-2 helper
      -- `measureComposite_pack`. The measure type is the ground `.int` (so
      -- `subst S .int = .int` is automatic); only the context needs the composite.
      -- `h_core.1` is under the rigidified `Cm`; bridge to `C` via
      -- `HasType.of_rigidTypeVars_irrel`.
      obtain ⟨S, h_ctx, h_abs, h_wf, h_poly⟩ :=
        Function.measureComposite_pack C Env func v_inst v_measure ρ measureBaseEnv.context
      rw [h_ctx]
      have h_typed := h_core.1 S h_abs h_wf h_poly
      rw [h_int] at h_typed
      simp only [LMonoTy.subst_unfold] at h_typed
      exact HasType.of_rigidTypeVars_irrel h_typed
    exact ⟨measureBaseEnv.context.subst Sm, ρ,
      h_sm_post, h_wf_ρ, h_cae.1, h_cae.2⟩

/-- `measureTyped` for the original function: a non-variable measure has type `int`. -/
theorem Function.typeCheck_measureTyped (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    -- TODO(preservation): see `typeCheck_bodyTyped_instantiated`. Context alias names are
    -- non-reserved (enforced by `TEnv.addTypeAlias`); to be discharged as a preserved invariant.
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- Ambient-rigidity invariant; see `typeCheck_bodyTyped_instantiated`.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): every ambient binding is monomorphic (`boundVars = []`).
    -- *Established* by ProcedureType.setupInputEnv (params/old-vars stored as `forAll [] _`)
    -- and the poly-init removal in CmdType (local `var` decls now store only `forAll [] _`).
    -- *Preserved* by checkAnnotCompat + goBlock. *Vacuous* at top level (types = []).
    -- Needed for Region B of the `TContextAliasEquiv` conjunct: a polymorphic ambient entry
    -- (e.g. `forAll [a] (a→a)`, closed yet poly) would break the `forAll []` shape the
    -- relation requires, and is exactly what the `var`-init fix rules out.
    (h_ambient_mono : ∀ x ty, Env.context.types.find? x = some ty →
      LTy.boundVars ty = [])
    -- Measure well-scopedness; see `typeCheck_measureTyped_instantiated`.
    (h_ws_measure : ∀ m, func.measure = some m → WellScoped m Env.context) :
    ∀ m, func.measure = some m →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      HasType C (funcContext Env.context func) m (.forAll [] .int) := by
  intro m h_measure h_nonfvar
  obtain ⟨Γ_inst, ρ, h_ht, h_wf_ρ, h_alias_eq, h_ctx_ae⟩ :=
    Function.typeCheck_measureTyped_instantiated C Env func func' Env' h h_wf h_fwf h_ws h_aliases_not_known h_ambient_rigid h_ambient_mono h_ws_measure m h_measure h_nonfvar
  -- `h_ht` is ALREADY the post-ρ judgment at output `.int` (ROUTE B); no output bridge needed.
  -- Bridge: alias-bridge the context only.
  refine HasType_context_aliasEquiv C (TContext.subst Γ_inst ρ) (funcContext Env.context func)
    m (.forAll [] .int) h_ht h_alias_eq.symm ?_
  rw [h_alias_eq]; exact h_ctx_ae

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
    -- TODO(preservation): see `typeCheck_bodyTyped_instantiated`. Context alias names are
    -- non-reserved (enforced by `TEnv.addTypeAlias`); to be discharged as a preserved invariant.
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- Ambient-rigidity invariant; see `typeCheck_bodyTyped_instantiated`.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    -- TODO(preservation): every ambient binding is monomorphic (`boundVars = []`).
    -- *Established* by ProcedureType.setupInputEnv (params/old-vars stored as `forAll [] _`)
    -- and the poly-init removal in CmdType (local `var` decls now store only `forAll [] _`).
    -- *Preserved* by checkAnnotCompat + goBlock. *Vacuous* at top level (types = []).
    -- Needed for Region B of the `TContextAliasEquiv` conjunct: a polymorphic ambient entry
    -- (e.g. `forAll [a] (a→a)`, closed yet poly) would break the `forAll []` shape the
    -- relation requires, and is exactly what the `var`-init fix rules out.
    (h_ambient_mono : ∀ x ty, Env.context.types.find? x = some ty →
      LTy.boundVars ty = [])
    -- Measure well-scopedness; see `typeCheck_measureTyped_instantiated`.
    (h_ws_measure : ∀ m, func.measure = some m → WellScoped m Env.context) :
    FuncHasType C Env.context func := by
  exact {
    inputsNodup := Function.typeCheck_inputsNodup_orig C Env func func' Env' h
    typeArgsNodup := Function.typeCheck_typeArgsNodup_orig C Env func func' Env' h
    noUndeclaredVars := Function.typeCheck_noUndeclaredVars_orig C Env func func' Env' h
    bodyTyped := Function.typeCheck_bodyTyped C Env func func' Env' h h_wf h_fwf h_resolved h_ws h_aliases_not_known h_ambient_rigid h_ambient_mono
    measureTyped := Function.typeCheck_measureTyped C Env func func' Env' h h_wf h_fwf h_ws h_aliases_not_known h_ambient_rigid h_ambient_mono h_ws_measure
  }

end TypeSpec
end Core
