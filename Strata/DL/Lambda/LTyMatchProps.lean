/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTyMatch
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LTyProps
import all Strata.DL.Lambda.LTyMatch
import Strata.DL.Lambda.LTyUnifyProps
import Strata.Util.HMaps

/-! # Properties of one-way type matching

Key results:
* `LMonoTy.matchTy?_subst_complete`: matching a pattern against one of its
  instances succeeds when every type variable of the pattern is a parameter,
  and binds each of them as the instance does.
* `LMonoTy.matchTy?_sound`, `LMonoTys.matchTys?_sound`: a successful match
  extends the starting map, binds only parameters, and instantiates the pattern
  to the target type.
* `LMonoTys.matchKnown?_sound`: a successful match of patterns with their known
  types binds only parameters and instantiates each pattern to its type.
* `LMonoTy.matchTy?_agrees_matchSubst`: matching with the pattern's own type
  variables as parameters succeeds exactly when `LMonoTy.matchSubst` does, with
  the same binding for every type variable of the pattern.
-/

namespace Lambda

public section

open Strata.Util (HMap HMaps)

/-- Matching a pattern against one of its instances succeeds when every type
    variable of the pattern is a parameter. Precisely: if the free type
    variables of `pat` are all in `params` and every binding in `S` agrees with
    `σ`, then matching `pat` against `pat.subst σ` from `S` succeeds. The
    result keeps the bindings of `S`, agrees with `σ`, and binds each type
    variable of `pat` as `σ` does. Proved by induction on `pat`. -/
theorem LMonoTy.matchTy?_subst_complete (params : List TyIdentifier)
    (σ : Subst) (pat : LMonoTy)
    (hpat : pat.freeVars ⊆ params) (S : SubstOne)
    (hS : ∀ a t, S.find? a = some t → t = LMonoTy.subst σ (.ftvar a)) :
    ∃ S', LMonoTy.matchTy? params S pat (pat.subst σ) = some S' ∧
      (∀ a t, S.find? a = some t → S'.find? a = some t) ∧
      (∀ a t, S'.find? a = some t → t = LMonoTy.subst σ (.ftvar a)) ∧
      (∀ a ∈ pat.freeVars, S'.find? a = some (LMonoTy.subst σ (.ftvar a))) := by
  induction pat generalizing S with
  | ftvar x =>
    have hxmem : x ∈ params := hpat (List.mem_singleton_self x)
    have hx : params.contains x = true := List.contains_iff_mem.mpr hxmem
    cases hf : S.find? x with
    | some bound =>
      have hb : bound = LMonoTy.subst σ (.ftvar x) := hS x bound hf
      refine ⟨S, ?_, fun _ _ h => h, hS, ?_⟩
      · simp only [LMonoTy.matchTy?, hx, ↓reduceIte, hf, hb, beq_self_eq_true]
      · intro a ha
        simp only [LMonoTy.freeVars, List.mem_singleton] at ha
        rw [ha, hf, hb]
    | none =>
      refine ⟨S.insert x (LMonoTy.subst σ (.ftvar x)), ?_, ?_, ?_, ?_⟩
      · simp only [LMonoTy.matchTy?, hx, ↓reduceIte, hf]
      · intro a t h
        by_cases hax : a = x
        · rw [hax, hf] at h
          cases h
        · rw [HMap.find?_insert_ne _ _ _ _ (bne_iff_ne.mpr hax)]
          exact h
      · intro a t h
        by_cases hax : a = x
        · rw [hax, HMap.find?_insert_self] at h
          rw [hax]
          exact (Option.some.inj h).symm
        · rw [HMap.find?_insert_ne _ _ _ _ (bne_iff_ne.mpr hax)] at h
          exact hS a t h
      · intro a ha
        simp only [LMonoTy.freeVars, List.mem_singleton] at ha
        rw [ha, HMap.find?_insert_self]
  | bitvec n =>
    refine ⟨S, ?_, fun _ _ h => h, hS, ?_⟩
    · rw [LMonoTy.subst_bitvec]
      simp only [LMonoTy.matchTy?, beq_self_eq_true, ↓reduceIte]
    · intro a ha
      simp only [LMonoTy.freeVars, List.not_mem_nil] at ha
  | tcons name args ih =>
    have hlist : ∀ l : List LMonoTy, (∀ t ∈ l, t ∈ args) → ∀ S : SubstOne,
        (∀ a t, S.find? a = some t → t = LMonoTy.subst σ (.ftvar a)) →
        ∃ S', LMonoTys.matchTys? params S l (l.map (LMonoTy.subst σ)) =
            some S' ∧
          (∀ a t, S.find? a = some t → S'.find? a = some t) ∧
          (∀ a t, S'.find? a = some t → t = LMonoTy.subst σ (.ftvar a)) ∧
          (∀ a ∈ LMonoTys.freeVars l,
            S'.find? a = some (LMonoTy.subst σ (.ftvar a))) := by
      intro l
      induction l with
      | nil =>
        intro _ S hS
        refine ⟨S, ?_, fun _ _ h => h, hS, ?_⟩
        · simp only [List.map_nil, LMonoTys.matchTys?]
        · intro a ha
          simp only [LMonoTys.freeVars, List.not_mem_nil] at ha
      | cons t rest ihl =>
        intro hsub S hS
        have htargs : t ∈ args := hsub t List.mem_cons_self
        have htpat : t.freeVars ⊆ params := fun v hv =>
          hpat (LMonoTys.freeVars_mem_subset htargs hv)
        obtain ⟨S1, hm1, hmono1, hag1, hb1⟩ := ih t htargs htpat S hS
        have hsubrest : ∀ u ∈ rest, u ∈ args := fun u hu =>
          hsub u (List.mem_cons_of_mem t hu)
        obtain ⟨S2, hm2, hmono2, hag2, hb2⟩ := ihl hsubrest S1 hag1
        refine ⟨S2, ?_, fun a u h => hmono2 a u (hmono1 a u h), hag2, ?_⟩
        · simp only [List.map_cons, LMonoTys.matchTys?, hm1,
            Option.bind_eq_bind, Option.bind_some, hm2]
        · intro a ha
          rw [LMonoTys.freeVars_of_cons, List.mem_append] at ha
          rcases ha with ha | ha
          · exact hmono2 _ _ (hb1 a ha)
          · exact hb2 a ha
    obtain ⟨S', hm, hmono, hag, hb⟩ := hlist args (fun _ h => h) S hS
    refine ⟨S', ?_, hmono, hag, hb⟩
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    simp only [LMonoTy.matchTy?, beq_self_eq_true, ↓reduceIte]
    exact hm

/-- Completing `σ` with the unbound parameters keeps every binding `σ` already
    has. -/
theorem SubstOne.completeParams_find?_of_find? (params : List TyIdentifier)
    (pfx : String)
    (σ : SubstOne) (a : TyIdentifier) (t : LMonoTy) (h : σ.find? a = some t) :
    (SubstOne.completeParams params pfx σ).find? a = some t := by
  unfold SubstOne.completeParams
  generalize params.zipIdx = l
  induction l generalizing σ with
  | nil => exact h
  | cons pi rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · rename_i hnone
      have hap : a ≠ pi.1 := by
        intro heq
        rw [← heq, h] at hnone
        exact hnone rfl
      rw [HMap.find?_insert_ne _ _ _ _ (bne_iff_ne.mpr hap)]
      exact h

/-- Soundness of one-way matching on lists, given soundness for each pattern
    in the list. -/
private theorem LMonoTys.matchTys?_sound_of (params : List TyIdentifier)
    (pats : LMonoTys)
    (ih : ∀ p ∈ pats, ∀ (S S' : SubstOne) (ty : LMonoTy),
      LMonoTy.matchTy? params S p ty = some S' →
      (∀ a t, S.find? a = some t → S'.find? a = some t) ∧
      (∀ a, S.find? a = none → S'.find? a ≠ none → a ∈ params) ∧
      (∀ a ∈ p.freeVars, a ∈ params → ∃ t, S'.find? a = some t) ∧
      ((∀ a ∈ p.freeVars, a ∉ params → S.find? a = none) →
        LMonoTy.subst [S'] p = ty))
    (S S' : SubstOne) (tys : LMonoTys)
    (h : LMonoTys.matchTys? params S pats tys = some S') :
    (∀ a t, S.find? a = some t → S'.find? a = some t) ∧
    (∀ a, S.find? a = none → S'.find? a ≠ none → a ∈ params) ∧
    (∀ a ∈ LMonoTys.freeVars pats, a ∈ params → ∃ t, S'.find? a = some t) ∧
    ((∀ a ∈ LMonoTys.freeVars pats, a ∉ params → S.find? a = none) →
      LMonoTys.subst [S'] pats = tys) := by
  induction pats generalizing S tys with
  | nil =>
    cases tys with
    | nil =>
      simp only [LMonoTys.matchTys?, Option.some.injEq] at h
      rw [← h]
      refine ⟨fun _ _ hf => hf, ?_, ?_, ?_⟩
      · intro a hn hs
        exact absurd hn hs
      · intro a ha
        simp only [LMonoTys.freeVars, List.not_mem_nil] at ha
      · intro _
        rw [LMonoTys.subst_nil]
    | cons t ts =>
      simp only [LMonoTys.matchTys?] at h
      cases h
  | cons p ps ihl =>
    cases tys with
    | nil =>
      simp only [LMonoTys.matchTys?] at h
      cases h
    | cons t ts =>
      cases hm1 : LMonoTy.matchTy? params S p t with
      | none =>
        simp only [LMonoTys.matchTys?, hm1, Option.bind_eq_bind,
          Option.bind_none] at h
        cases h
      | some S1 =>
        simp only [LMonoTys.matchTys?, hm1, Option.bind_eq_bind,
          Option.bind_some] at h
        obtain ⟨hext1, hnew1, hbound1, hsub1⟩ :=
          ih p List.mem_cons_self S S1 t hm1
        obtain ⟨hext2, hnew2, hbound2, hsub2⟩ :=
          ihl (fun q hq => ih q (List.mem_cons_of_mem p hq)) S1 ts h
        have hnewS : ∀ a, S.find? a = none → S'.find? a ≠ none →
            a ∈ params := by
          intro a hfa hs'
          cases hf1 : S1.find? a with
          | none => exact hnew2 a hf1 hs'
          | some v =>
            have hne : S1.find? a ≠ none := by
              rw [hf1]
              exact Option.some_ne_none v
            exact hnew1 a hfa hne
        refine ⟨fun a v hf => hext2 a v (hext1 a v hf), hnewS, ?_, ?_⟩
        · intro a ha hap
          rw [LMonoTys.freeVars_of_cons, List.mem_append] at ha
          rcases ha with ha | ha
          · obtain ⟨v, hv⟩ := hbound1 a ha hap
            exact ⟨v, hext2 a v hv⟩
          · exact hbound2 a ha hap
        · intro hfree
          have hfp : ∀ a ∈ p.freeVars, a ∉ params → S.find? a = none := by
            intro a ha hn
            apply hfree a _ hn
            rw [LMonoTys.freeVars_of_cons, List.mem_append]
            exact Or.inl ha
          have hfs : ∀ a ∈ LMonoTys.freeVars ps, a ∉ params →
              S1.find? a = none := by
            intro a ha hn
            cases hf1 : S1.find? a with
            | none => rfl
            | some v =>
              have hfa : S.find? a = none := by
                apply hfree a _ hn
                rw [LMonoTys.freeVars_of_cons, List.mem_append]
                exact Or.inr ha
              have hne : S1.find? a ≠ none := by
                rw [hf1]
                exact Option.some_ne_none v
              exact absurd (hnew1 a hfa hne) hn
          rw [LMonoTys.subst_eq_map, List.map_cons, ← LMonoTys.subst_eq_map]
          have hsame : LMonoTy.subst [S'] p = LMonoTy.subst [S1] p :=
            LMonoTy.subst_one_extend params S1 S' p hext2 hnew2 hbound1
          rw [hsame, hsub1 hfp, hsub2 hfs]

/-- A successful one-way match extends the starting map, binds only the given
    parameters, and instantiates the pattern to the target type. Precisely, if
    `matchTy? params S pat ty = some S'`, then: every binding of `S` is in `S'`;
    every key of `S'` that is not a key of `S` is a parameter; and every
    parameter occurring in `pat` is bound in `S'`. If moreover `S` binds no type
    variable of `pat` that is not a parameter, substituting `S'` into `pat`
    gives `ty`; only this last conclusion needs that assumption. Type variables
    of `pat` outside `params` are constants, so matching them requires equality
    with the target. Proved by induction on `pat`. -/
theorem LMonoTy.matchTy?_sound (params : List TyIdentifier)
    (S S' : SubstOne) (pat ty : LMonoTy)
    (h : LMonoTy.matchTy? params S pat ty = some S') :
    (∀ a t, S.find? a = some t → S'.find? a = some t) ∧
    (∀ a, S.find? a = none → S'.find? a ≠ none → a ∈ params) ∧
    (∀ a ∈ pat.freeVars, a ∈ params → ∃ t, S'.find? a = some t) ∧
    ((∀ a ∈ pat.freeVars, a ∉ params → S.find? a = none) →
      LMonoTy.subst [S'] pat = ty) := by
  induction pat generalizing S S' ty with
  | ftvar x =>
    by_cases hx : params.contains x = true
    · have hxmem : x ∈ params := List.contains_iff_mem.mp hx
      cases hf : S.find? x with
      | some bound =>
        simp only [LMonoTy.matchTy?, hx, ↓reduceIte, hf] at h
        by_cases hb : (bound == ty) = true
        · simp only [hb, ↓reduceIte, Option.some.injEq] at h
          have hbt : bound = ty := eq_of_beq hb
          rw [← h]
          refine ⟨fun _ _ hh => hh, ?_, ?_, ?_⟩
          · intro a hn hs
            exact absurd hn hs
          · intro a ha _
            simp only [LMonoTy.freeVars, List.mem_singleton] at ha
            rw [ha]
            exact ⟨bound, hf⟩
          · intro _
            rw [LMonoTy.subst_one_ftvar, hf]
            exact hbt
        · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
          cases h
      | none =>
        simp only [LMonoTy.matchTy?, hx, ↓reduceIte, hf, Option.some.injEq] at h
        rw [← h]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro a t hh
          have hax : a ≠ x := by
            intro hax
            rw [hax, hf] at hh
            cases hh
          rw [HMap.find?_insert_ne _ _ _ _ (bne_iff_ne.mpr hax)]
          exact hh
        · intro a hn hs
          by_cases hax : a = x
          · rw [hax]
            exact hxmem
          · rw [HMap.find?_insert_ne _ _ _ _ (bne_iff_ne.mpr hax), hn] at hs
            exact absurd rfl hs
        · intro a ha _
          simp only [LMonoTy.freeVars, List.mem_singleton] at ha
          rw [ha, HMap.find?_insert_self]
          exact ⟨ty, rfl⟩
        · intro _
          rw [LMonoTy.subst_one_ftvar, HMap.find?_insert_self]
    · have hxn : x ∉ params := fun hm => hx (List.contains_iff_mem.mpr hm)
      simp only [LMonoTy.matchTy?, hx, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hb : (LMonoTy.ftvar x == ty) = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at h
        have hbt : LMonoTy.ftvar x = ty := eq_of_beq hb
        rw [← h]
        refine ⟨fun _ _ hh => hh, ?_, ?_, ?_⟩
        · intro a hn hs
          exact absurd hn hs
        · intro a ha hap
          simp only [LMonoTy.freeVars, List.mem_singleton] at ha
          rw [ha] at hap
          exact absurd hap hxn
        · intro hfree
          have hxmem : x ∈ (LMonoTy.ftvar x).freeVars := by
            simp only [LMonoTy.freeVars, List.mem_singleton]
          have hxf : S.find? x = none := hfree x hxmem hxn
          rw [LMonoTy.subst_one_ftvar, hxf]
          exact hbt
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
        cases h
  | bitvec n =>
    cases ty with
    | bitvec m =>
      simp only [LMonoTy.matchTy?] at h
      by_cases hn : (n == m) = true
      · simp only [hn, ↓reduceIte, Option.some.injEq] at h
        have hnm : n = m := eq_of_beq hn
        rw [← h]
        refine ⟨fun _ _ hh => hh, ?_, ?_, ?_⟩
        · intro a hn' hs
          exact absurd hn' hs
        · intro a ha
          simp only [LMonoTy.freeVars, List.not_mem_nil] at ha
        · intro _
          rw [LMonoTy.subst_bitvec, hnm]
      · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | ftvar y => simp only [LMonoTy.matchTy?] at h; cases h
    | tcons y ys => simp only [LMonoTy.matchTy?] at h; cases h
  | tcons name args ih =>
    cases ty with
    | tcons m tys =>
      simp only [LMonoTy.matchTy?] at h
      by_cases hn : (name == m) = true
      · simp only [hn, ↓reduceIte] at h
        have hnm : name = m := eq_of_beq hn
        obtain ⟨h1, h2, h3, h4⟩ :=
          LMonoTys.matchTys?_sound_of params args ih S S' tys h
        refine ⟨h1, h2, h3, ?_⟩
        intro hfree
        rw [LMonoTy.subst_tcons, h4 hfree, hnm]
      · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | ftvar y => simp only [LMonoTy.matchTy?] at h; cases h
    | bitvec y => simp only [LMonoTy.matchTy?] at h; cases h

/-- Soundness of one-way matching on lists of types: a successful match of
    patterns against types, position by position, extends the starting map,
    binds only the given parameters, and instantiates each pattern to the type
    at its position. Only the last conclusion needs the starting map to bind no
    type variable of the patterns that is not a parameter. -/
theorem LMonoTys.matchTys?_sound (params : List TyIdentifier)
    (S S' : SubstOne) (pats tys : LMonoTys)
    (h : LMonoTys.matchTys? params S pats tys = some S') :
    (∀ a t, S.find? a = some t → S'.find? a = some t) ∧
    (∀ a, S.find? a = none → S'.find? a ≠ none → a ∈ params) ∧
    (∀ a ∈ LMonoTys.freeVars pats, a ∈ params → ∃ t, S'.find? a = some t) ∧
    ((∀ a ∈ LMonoTys.freeVars pats, a ∉ params → S.find? a = none) →
      LMonoTys.subst [S'] pats = tys) :=
  LMonoTys.matchTys?_sound_of params pats
    (fun p _ S0 S0' ty0 hm0 => LMonoTy.matchTy?_sound params S0 S0' p ty0 hm0)
    S S' tys h

/-- Matching each pattern with a known type, folding from a starting map whose
    keys are all parameters: the result keeps the starting bindings, has only
    parameter keys, and instantiates every pattern with a known type to it. -/
private theorem LMonoTys.matchKnown?_sound_from (params : List TyIdentifier)
    (pairs : List (LMonoTy × Option LMonoTy)) :
    ∀ (S S' : SubstOne),
    (∀ a, S.find? a ≠ none → a ∈ params) →
    pairs.foldlM (m := Option) (init := S) (fun S (pat, ty?) =>
      match ty? with
      | some ty => LMonoTy.matchTy? params S pat ty
      | none => some S) = some S' →
    (∀ a t, S.find? a = some t → S'.find? a = some t) ∧
    (∀ a, S'.find? a ≠ none → a ∈ params) ∧
    (∀ pat ty, (pat, some ty) ∈ pairs → LMonoTy.subst [S'] pat = ty) := by
  induction pairs with
  | nil =>
    intro S S' hS h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    rw [← h]
    refine ⟨fun _ _ hh => hh, hS, ?_⟩
    intro pat ty hmem
    cases hmem
  | cons pr rest ih =>
    intro S S' hS h
    obtain ⟨pat, ty?⟩ := pr
    cases ty? with
    | none =>
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨h1, h2, h3⟩ := ih S S' hS h
      refine ⟨h1, h2, ?_⟩
      intro p t hmem
      rcases List.mem_cons.mp hmem with hh | hh
      · cases hh
      · exact h3 p t hh
    | some ty =>
      cases hm : LMonoTy.matchTy? params S pat ty with
      | none =>
        simp only [List.foldlM_cons, hm, Option.bind_eq_bind,
          Option.bind_none] at h
        cases h
      | some S1 =>
        simp only [List.foldlM_cons, hm, Option.bind_eq_bind,
          Option.bind_some] at h
        have hfree : ∀ a ∈ pat.freeVars, a ∉ params → S.find? a = none := by
          intro a _ hn
          cases hf : S.find? a with
          | none => rfl
          | some v =>
            have hne : S.find? a ≠ none := by
              rw [hf]
              exact Option.some_ne_none v
            exact absurd (hS a hne) hn
        obtain ⟨hext1, hnew1, hbound1, hsub1⟩ :=
          LMonoTy.matchTy?_sound params S S1 pat ty hm
        have hS1 : ∀ a, S1.find? a ≠ none → a ∈ params := by
          intro a ha
          cases hf : S.find? a with
          | none => exact hnew1 a hf ha
          | some v =>
            have hne : S.find? a ≠ none := by
              rw [hf]
              exact Option.some_ne_none v
            exact hS a hne
        obtain ⟨h1, h2, h3⟩ := ih S1 S' hS1 h
        refine ⟨fun a t hh => h1 a t (hext1 a t hh), h2, ?_⟩
        intro p t hmem
        rcases List.mem_cons.mp hmem with hh | hh
        · have hpt : p = pat ∧ t = ty := by
            simp only [Prod.mk.injEq, Option.some.injEq] at hh
            exact hh
          rw [hpt.1, hpt.2]
          have hnew' : ∀ a, S1.find? a = none → S'.find? a ≠ none →
              a ∈ params := fun a _ ha => h2 a ha
          have hsame : LMonoTy.subst [S'] pat = LMonoTy.subst [S1] pat :=
            LMonoTy.subst_one_extend params S1 S' pat h1 hnew' hbound1
          rw [hsame, hsub1 hfree]
        · exact h3 p t hh

/-- A successful match of each pattern with its known type, starting from the
    empty map, binds only parameters and instantiates every pattern with a
    known type to that type. -/
theorem LMonoTys.matchKnown?_sound (params : List TyIdentifier)
    (pairs : List (LMonoTy × Option LMonoTy)) (S' : SubstOne)
    (h : LMonoTys.matchKnown? params pairs = some S') :
    (∀ a, S'.find? a ≠ none → a ∈ params) ∧
    (∀ pat ty, (pat, some ty) ∈ pairs → LMonoTy.subst [S'] pat = ty) := by
  have hempty : ∀ a, (Strata.Util.HMap.empty : SubstOne).find? a ≠ none →
      a ∈ params := by
    intro a ha
    exact absurd (HMap.find?_empty a) ha
  have hfold := LMonoTys.matchKnown?_sound_from params pairs
    Strata.Util.HMap.empty S' hempty h
  exact ⟨hfold.2.1, hfold.2.2⟩

/-- If a one-scope substitution binds every type variable of `pat`, the
    position-by-position bindings of `pat` against its instance exist, agree
    with the substitution, and mention every type variable of `pat`. -/
private theorem LMonoTy.matchBindings_of_subst (S' : SubstOne) (pat : LMonoTy)
    (hb : ∀ x ∈ pat.freeVars, ∃ t, S'.find? x = some t) :
    ∃ bs, LMonoTy.matchBindings pat (LMonoTy.subst [S'] pat) = some bs ∧
      (∀ b ∈ bs, S'.find? b.1 = some b.2) ∧
      (∀ x ∈ pat.freeVars, ∃ b ∈ bs, b.1 = x) := by
  induction pat with
  | ftvar x =>
    have hxmem : x ∈ (LMonoTy.ftvar x).freeVars := by
      simp only [LMonoTy.freeVars, List.mem_singleton]
    obtain ⟨t, ht⟩ := hb x hxmem
    refine ⟨[(x, t)], ?_, ?_, ?_⟩
    · rw [LMonoTy.subst_one_ftvar, ht]
      simp only [LMonoTy.matchBindings]
    · intro b hbm
      rw [List.mem_singleton] at hbm
      rw [hbm]
      exact ht
    · intro y hy
      rw [LMonoTy.freeVars, List.mem_singleton] at hy
      exact ⟨(x, t), List.mem_singleton_self _, hy.symm⟩
  | bitvec n =>
    refine ⟨[], ?_, ?_, ?_⟩
    · rw [LMonoTy.subst_bitvec]
      simp only [LMonoTy.matchBindings, ↓reduceIte]
    · intro b hbm
      cases hbm
    · intro y hy
      simp only [LMonoTy.freeVars, List.not_mem_nil] at hy
  | tcons name args ih =>
    have hlist : ∀ l : List LMonoTy, (∀ t ∈ l, t ∈ args) →
        (∀ x ∈ LMonoTys.freeVars l, ∃ t, S'.find? x = some t) →
        ∃ bs, LMonoTys.matchBindings l (l.map (LMonoTy.subst [S'])) = some bs ∧
          (∀ b ∈ bs, S'.find? b.1 = some b.2) ∧
          (∀ x ∈ LMonoTys.freeVars l, ∃ b ∈ bs, b.1 = x) := by
      intro l
      induction l with
      | nil =>
        intro _ _
        refine ⟨[], ?_, ?_, ?_⟩
        · simp only [List.map_nil, LMonoTys.matchBindings]
        · intro b hbm
          cases hbm
        · intro y hy
          simp only [LMonoTys.freeVars, List.not_mem_nil] at hy
      | cons t rest ihl =>
        intro hsub hbl
        have htargs : t ∈ args := hsub t List.mem_cons_self
        have hbt : ∀ x ∈ t.freeVars, ∃ v, S'.find? x = some v := by
          intro x hx
          apply hbl x
          rw [LMonoTys.freeVars_of_cons, List.mem_append]
          exact Or.inl hx
        have hbr : ∀ x ∈ LMonoTys.freeVars rest, ∃ v, S'.find? x = some v := by
          intro x hx
          apply hbl x
          rw [LMonoTys.freeVars_of_cons, List.mem_append]
          exact Or.inr hx
        obtain ⟨b1, hm1, hag1, hcov1⟩ := ih t htargs hbt
        obtain ⟨b2, hm2, hag2, hcov2⟩ :=
          ihl (fun u hu => hsub u (List.mem_cons_of_mem t hu)) hbr
        refine ⟨b1 ++ b2, ?_, ?_, ?_⟩
        · simp only [List.map_cons, LMonoTys.matchBindings, hm1, hm2]
        · intro b hbm
          rcases List.mem_append.mp hbm with hh | hh
          · exact hag1 b hh
          · exact hag2 b hh
        · intro x hx
          rw [LMonoTys.freeVars_of_cons, List.mem_append] at hx
          rcases hx with hx | hx
          · obtain ⟨b, hbm, hbx⟩ := hcov1 x hx
            exact ⟨b, List.mem_append_left _ hbm, hbx⟩
          · obtain ⟨b, hbm, hbx⟩ := hcov2 x hx
            exact ⟨b, List.mem_append_right _ hbm, hbx⟩
    obtain ⟨bs, hm, hag, hcov⟩ := hlist args (fun _ h => h) hb
    refine ⟨bs, ?_, hag, hcov⟩
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    simp only [LMonoTy.matchBindings, ↓reduceIte]
    exact hm

/-- If the target is an instance of the pattern according to `matchSubst`,
    matching with the pattern's own type variables as parameters from the empty
    map succeeds and binds each of them to the type `matchSubst` gives it. -/
private theorem LMonoTy.matchTy?_of_matchSubst (pat ty : LMonoTy) (S : Subst)
    (h : pat.matchSubst ty = some S) :
    ∃ S', LMonoTy.matchTy? pat.freeVars HMap.empty pat ty = some S' ∧
      ∀ x ∈ pat.freeVars, S'.find? x = some (LMonoTy.subst S (.ftvar x)) := by
  have hsub : pat.subst S = ty := LMonoTy.matchSubst_sound h
  have hsubset : pat.freeVars ⊆ pat.freeVars := fun _ hx => hx
  have hS : ∀ a t, (HMap.empty : SubstOne).find? a = some t →
      t = LMonoTy.subst S (.ftvar a) := by
    intro a t ht
    rw [HMap.find?_empty] at ht
    cases ht
  obtain ⟨S', hm, _, _, hbound⟩ :=
    LMonoTy.matchTy?_subst_complete pat.freeVars S pat hsubset HMap.empty hS
  rw [hsub] at hm
  exact ⟨S', hm, hbound⟩

/-- If matching with the pattern's own type variables as parameters from the
    empty map succeeds, `matchSubst` succeeds and gives each type variable of
    the pattern the type the match binds it to. -/
private theorem LMonoTy.matchSubst_of_matchTy? (pat ty : LMonoTy)
    (S' : SubstOne)
    (h : LMonoTy.matchTy? pat.freeVars HMap.empty pat ty = some S') :
    ∃ S, pat.matchSubst ty = some S ∧
      ∀ x ∈ pat.freeVars, S'.find? x = some (LMonoTy.subst S (.ftvar x)) := by
  have hnofree : ∀ a ∈ pat.freeVars, a ∉ pat.freeVars →
      (HMap.empty : SubstOne).find? a = none := by
    intro a ha hn
    exact absurd ha hn
  obtain ⟨_, _, hbound, hsubf⟩ :=
    LMonoTy.matchTy?_sound pat.freeVars HMap.empty S' pat ty h
  have hsub : LMonoTy.subst [S'] pat = ty := hsubf hnofree
  have hb : ∀ x ∈ pat.freeVars, ∃ t, S'.find? x = some t :=
    fun x hx => hbound x hx hx
  obtain ⟨bs, hmb, hag, hcov⟩ := LMonoTy.matchBindings_of_subst S' pat hb
  rw [hsub] at hmb
  have hne : ∀ x ∈ pat.freeVars, bs.isEmpty = false := by
    intro x hx
    obtain ⟨b, hbm, _⟩ := hcov x hx
    cases bs with
    | nil => cases hbm
    | cons _ _ => rfl
  have hfind : ∀ x ∈ pat.freeVars, ∃ t, S'.find? x = some t ∧
      (bs.foldl (fun m b => m.insert b.1 b.2) (∅ : SubstOne)).find? x
        = some t := by
    intro x hx
    obtain ⟨t, ht⟩ := hb x hx
    obtain ⟨b, hbm, hbx⟩ := hcov x hx
    exact ⟨t, ht, HMap.foldl_insert_find?_of_agree S' bs hag _ x t ht
      (Or.inl ⟨b, hbm, hbx⟩)⟩
  have hpt : pat.subst
      (if bs.isEmpty then Subst.empty
        else [bs.foldl (fun m b => m.insert b.1 b.2) (∅ : SubstOne)]) = ty := by
    rw [← hsub]
    apply LMonoTy.subst_ext
    intro x hx
    obtain ⟨t, ht, hft⟩ := hfind x hx
    rw [hne x hx, HMaps.find?_single_scope]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [HMaps.find?_single_scope, ht, hft]
  have hfinal : pat.matchSubst ty = some
      (if bs.isEmpty then Subst.empty
        else [bs.foldl (fun m b => m.insert b.1 b.2) (∅ : SubstOne)]) := by
    unfold LMonoTy.matchSubst
    rw [hmb]
    simp only [hpt, ↓reduceIte]
  refine ⟨_, hfinal, ?_⟩
  intro x hx
  obtain ⟨t, ht, hft⟩ := hfind x hx
  rw [hne x hx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [LMonoTy.subst_one_ftvar, hft]
  exact ht

/-- One-way matching with the pattern's own type variables as parameters,
    starting from the empty map, and `LMonoTy.matchSubst` agree: one succeeds
    exactly when the other does, and then both bind every type variable of the
    pattern to the same type. -/
theorem LMonoTy.matchTy?_agrees_matchSubst (pat ty : LMonoTy) :
    (∀ S, pat.matchSubst ty = some S →
      ∃ S', LMonoTy.matchTy? pat.freeVars HMap.empty pat ty = some S' ∧
        ∀ x ∈ pat.freeVars, S'.find? x = some (LMonoTy.subst S (.ftvar x))) ∧
    (∀ S', LMonoTy.matchTy? pat.freeVars HMap.empty pat ty = some S' →
      ∃ S, pat.matchSubst ty = some S ∧
        ∀ x ∈ pat.freeVars, S'.find? x = some (LMonoTy.subst S (.ftvar x))) :=
  ⟨LMonoTy.matchTy?_of_matchSubst pat ty,
    LMonoTy.matchSubst_of_matchTy? pat ty⟩

end -- public section

end Lambda
