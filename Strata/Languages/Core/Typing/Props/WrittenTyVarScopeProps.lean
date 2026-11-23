/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.WrittenTyVarScope
public import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import Strata.Languages.Core.Typing.Props.TypeSkolemProps
import Strata.Util.NameProofs
import all Strata.Languages.Core.WrittenTyVarScope
import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.DL.Lambda.LTyProps
import all Strata.DL.Lambda.LExprTypeEnv

/-! ## Properties of written-type-variable scoping

Key theorems: `bindVars_binds` (what `bindVars` binds), `freshName_admissible` and
`bindVars_admissible` (checker names are names a user may write), `renameCmd_scopeAdmissible`
(renaming keeps the scope admissible), `renameCmd_scopeAvoids` (renaming keeps checker names out
of the type parameters) and `subst_restrictTo_renameTy`. -/

public section

namespace Core

open Lambda Imperative
open TypeSpec
open WrittenTyVarScope

/-- Rename an expression annotation in scope `m`. -/
def WrittenTyVarScope.renameAnnot (m : ScopeMap) (ty : Option LMonoTy) : Option LMonoTy :=
  ty.map (renameTy (annotName m))

/-- No checker name the scope map `m` binds is in `ps`, and every name in `ps` is one a fresh name
    must avoid. -/
structure ScopeAvoids (ps : List TyIdentifier) (m : ScopeMap) (st : ScopeState) : Prop where
  names : ∀ p ∈ m, p.2 ∉ ps
  avoid : ∀ x ∈ ps, x ∈ st.avoid

/-! ### Renaming on each expression form -/

/-- Renaming a free variable renames its annotation. -/
theorem renameExpr_fvar (m : ScopeMap) (md : _) (x : CoreIdent)
    (ty : Option LMonoTy) : renameExpr m (.fvar md x ty) = .fvar md x (renameAnnot m ty) := by
  simp only [renameExpr, renameAnnot, LExpr.replaceUserProvidedType]

/-- Renaming an abstraction renames its annotation and body. -/
theorem renameExpr_abs (m : ScopeMap) (md : _) (name : String)
    (ty : Option LMonoTy) (b : Expression.Expr) :
    renameExpr m (.abs md name ty b) = .abs md name (renameAnnot m ty) (renameExpr m b) := by
  simp only [renameExpr, renameAnnot, LExpr.replaceUserProvidedType]

/-- Renaming a quantifier renames its annotation, trigger and body. -/
theorem renameExpr_quant (m : ScopeMap) (md : _) (k : QuantifierKind)
    (name : String) (ty : Option LMonoTy) (tr b : Expression.Expr) :
    renameExpr m (.quant md k name ty tr b) =
      .quant md k name (renameAnnot m ty) (renameExpr m tr) (renameExpr m b) := by
  simp only [renameExpr, renameAnnot, LExpr.replaceUserProvidedType]

/-- Renaming an application renames both parts. -/
theorem renameExpr_app (m : ScopeMap) (md : _) (f a : Expression.Expr) :
    renameExpr m (.app md f a) = .app md (renameExpr m f) (renameExpr m a) := by
  simp only [renameExpr, LExpr.replaceUserProvidedType]

/-- Renaming a conditional renames its three parts. -/
theorem renameExpr_ite (m : ScopeMap) (md : _) (c t e : Expression.Expr) :
    renameExpr m (.ite md c t e) = .ite md (renameExpr m c) (renameExpr m t) (renameExpr m e) := by
  simp only [renameExpr, LExpr.replaceUserProvidedType]

/-- Renaming an equality renames both sides. -/
theorem renameExpr_eq (m : ScopeMap) (md : _) (a b : Expression.Expr) :
    renameExpr m (.eq md a b) = .eq md (renameExpr m a) (renameExpr m b) := by
  simp only [renameExpr, LExpr.replaceUserProvidedType]

/-! ### Scope errors -/

/-- The scope error text is the first unbound annotation type variable of the list, wrapped in
    the message. -/
theorem unboundAnnotMsg?_eq (writable : Bool) (rigid : List TyIdentifier) (m : ScopeMap)
    (es : List Expression.Expr) :
    unboundAnnotMsg? writable rigid m es =
      (es.findSome? (unboundAnnotVar? writable rigid m)).map
        fun v => f!"type variable `{v}` is not in scope" := by
  unfold unboundAnnotMsg?
  rfl

/-! ### Renaming types -/

/-- Instantiating a written type by the `S`-instances of its checker names is substituting `S`
    into its renaming. -/
theorem subst_restrictTo_renameTy (S : Subst) (f : TyIdentifier → TyIdentifier) (ty : LMonoTy) :
    LMonoTy.subst [restrictTo (fun v => LMonoTy.subst S (.ftvar (f v))) ty] ty =
      LMonoTy.subst S (renameTy f ty) := by
  show _ = LMonoTy.subst S (LMonoTy.subst [restrictTo (fun v => .ftvar (f v)) ty] ty)
  refine (LMonoTy.subst_subst_of_pointwise [restrictTo (fun v => .ftvar (f v)) ty] S _ ty ?_).symm
  intro v hv
  rw [restrictTo_ftvar _ ty v hv, restrictTo_ftvar _ ty v hv]

/-- Every free type variable of the image of a free type variable of `t` is free in the image
    of `t`. -/
private theorem freeVars_subst_ftvar_subset (S : Subst) (t : LMonoTy) (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars t) :
    ∀ x ∈ LMonoTy.freeVars (LMonoTy.subst S (.ftvar v)),
      x ∈ LMonoTy.freeVars (LMonoTy.subst S t) := by
  induction t with
  | ftvar y =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv
    exact fun x hx => hx
  | bitvec n => simp only [LMonoTy.freeVars, List.not_mem_nil] at hv
  | tcons name args ih =>
    intro x hx
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map, LMonoTy.freeVars]
    simp only [LMonoTy.freeVars] at hv
    obtain ⟨a, ha, hva⟩ := LMonoTys.freeVars_exists hv
    exact LMonoTys.freeVars_mem_subset (List.mem_map_of_mem ha) (ih a ha hva x hx)

/-- If `v` is free in `t`, then `f v` is free in `renameTy f t`. -/
theorem mem_freeVars_renameTy (f : TyIdentifier → TyIdentifier) (t : LMonoTy) (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars t) : f v ∈ LMonoTy.freeVars (renameTy f t) := by
  have himg := freeVars_subst_ftvar_subset [restrictTo (fun v => .ftvar (f v)) t] t v hv (f v)
  rw [restrictTo_ftvar _ t v hv] at himg
  exact himg (by simp only [LMonoTy.freeVars, List.mem_singleton])

/-! ### Scope-map lookups and `bindVars` -/

/-- Looking up a key other than the newest binding's key skips that binding. -/
private theorem lookup_cons_ne {v u w : TyIdentifier} (m : ScopeMap) (h : u ≠ v) :
    ((v, w) :: m).lookup u = m.lookup u := by
  have hb : (u == v) = false := beq_false_of_ne h
  simp only [List.lookup, hb]

/-- `bindVars` keeps every binding it is given. -/
theorem bindVars_mono (rigid : List TyIdentifier) :
    ∀ (vs : List TyIdentifier) (m : ScopeMap) (st : ScopeState) (u w : TyIdentifier),
      m.lookup u = some w → (bindVars rigid vs m st).1.lookup u = some w
  | [], _, _, _, _, h => h
  | v :: vs, m, st, u, w, h => by
    simp only [bindVars]
    have hstep : ∀ w', (m.lookup v).isSome = false → ((v, w') :: m).lookup u = some w := by
      intro w' hnone
      have hne : u ≠ v := by
        rintro rfl
        rw [h] at hnone
        cases hnone
      rw [lookup_cons_ne m hne]
      exact h
    split
    · exact bindVars_mono rigid vs m st u w h
    · rename_i hcond
      have hnone : (m.lookup v).isSome = false := by
        cases hm : (m.lookup v).isSome
        · rfl
        · exact absurd (Or.inr hm) hcond
      split
      · exact bindVars_mono rigid vs _ _ u w (hstep _ hnone)
      · exact bindVars_mono rigid vs _ _ u w (hstep _ hnone)

/-- `bindVars` binds every non-rigid variable of its list. -/
theorem bindVars_binds (rigid : List TyIdentifier) :
    ∀ (vs : List TyIdentifier) (m : ScopeMap) (st : ScopeState) (u : TyIdentifier),
      u ∈ vs → u ∉ rigid → ∃ w, (bindVars rigid vs m st).1.lookup u = some w
  | [], _, _, _, hu, _ => absurd hu List.not_mem_nil
  | v :: vs, m, st, u, hu, hur => by
    simp only [bindVars]
    rcases List.mem_cons.mp hu with rfl | htail
    · split
      · rename_i hcond
        rcases hcond with hrig | hsome
        · exact absurd hrig hur
        · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
          exact ⟨w, bindVars_mono rigid vs m st u w hw⟩
      · split
        · exact ⟨_, bindVars_mono rigid vs _ _ u _ List.lookup_cons_self⟩
        · exact ⟨_, bindVars_mono rigid vs _ _ u _ List.lookup_cons_self⟩
    · split
      · exact bindVars_binds rigid vs m st u htail hur
      · split
        · exact bindVars_binds rigid vs _ _ u htail hur
        · exact bindVars_binds rigid vs _ _ u htail hur

/-- `bindVars` never binds a rigid variable. -/
theorem bindVars_noRigid (rigid : List TyIdentifier) :
    ∀ (vs : List TyIdentifier) (m : ScopeMap) (st : ScopeState),
      (∀ r ∈ rigid, m.lookup r = none) →
        ∀ r ∈ rigid, (bindVars rigid vs m st).1.lookup r = none
  | [], _, _, h => h
  | v :: vs, m, st, h => by
    simp only [bindVars]
    have hstep : ∀ w', v ∉ rigid → ∀ r ∈ rigid, ((v, w') :: m).lookup r = none := by
      intro w' hv r hr
      have hne : r ≠ v := by
        rintro rfl
        exact hv hr
      rw [lookup_cons_ne m hne]
      exact h r hr
    split
    · exact bindVars_noRigid rigid vs m st h
    · rename_i hcond
      have hv : v ∉ rigid := fun hr => hcond (Or.inl hr)
      split
      · exact bindVars_noRigid rigid vs _ _ (hstep _ hv)
      · exact bindVars_noRigid rigid vs _ _ (hstep _ hv)

/-- A name `bindVars` binds was bound before, or is a non-rigid member of its list that was
    unbound before. -/
theorem bindVars_lookup_cases (rigid : List TyIdentifier) :
    ∀ (vs : List TyIdentifier) (m : ScopeMap) (st : ScopeState) (u w : TyIdentifier),
      (bindVars rigid vs m st).1.lookup u = some w →
        m.lookup u = some w ∨ (u ∈ vs ∧ u ∉ rigid ∧ m.lookup u = none)
  | [], _, _, _, _, h => Or.inl h
  | v :: vs, m, st, u, w, h => by
    simp only [bindVars] at h
    have hcons : ∀ w', ((v, w') :: m).lookup u = some w → (m.lookup v).isSome = false →
        v ∉ rigid → m.lookup u = some w ∨ (u ∈ v :: vs ∧ u ∉ rigid ∧ m.lookup u = none) := by
      intro w' hl hnone hvr
      by_cases huv : u = v
      · subst huv
        refine Or.inr ⟨List.mem_cons_self .., hvr, ?_⟩
        cases hm : m.lookup u with
        | none => rfl
        | some _ =>
          rw [hm] at hnone
          cases hnone
      · rw [lookup_cons_ne m huv] at hl
        exact Or.inl hl
    have htail : ∀ (m' : ScopeMap) (st' : ScopeState) (w' : TyIdentifier),
        m' = (v, w') :: m → (m.lookup v).isSome = false → v ∉ rigid →
        (bindVars rigid vs m' st').1.lookup u = some w →
        m.lookup u = some w ∨ (u ∈ v :: vs ∧ u ∉ rigid ∧ m.lookup u = none) := by
      intro m' st' w' hm' hnone hvr hl
      subst hm'
      rcases bindVars_lookup_cases rigid vs _ st' u w hl with hl' | ⟨hmem, hr, hn⟩
      · exact hcons _ hl' hnone hvr
      · by_cases huv : u = v
        · subst huv
          rw [List.lookup_cons_self] at hn
          cases hn
        · rw [lookup_cons_ne m huv] at hn
          exact Or.inr ⟨List.mem_cons_of_mem _ hmem, hr, hn⟩
    split at h
    · rcases bindVars_lookup_cases rigid vs m st u w h with h | ⟨hm, hr, hn⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_cons_of_mem _ hm, hr, hn⟩
    · rename_i hcond
      have hnone : (m.lookup v).isSome = false := by
        cases hm : (m.lookup v).isSome
        · rfl
        · exact absurd (Or.inr hm) hcond
      have hvr : v ∉ rigid := fun hr => hcond (Or.inl hr)
      split at h
      · exact htail _ _ _ rfl hnone hvr h
      · exact htail _ _ _ rfl hnone hvr h

/-! ### Checker names of names a user may write -/

/-- Does no underscore in the list come directly before a decimal digit? -/
private def noUnderscoreDigit : List Char → Bool
  | [] => true
  | a :: rest => (a != '_' || !(rest.head?.any Char.isDigit)) && noUnderscoreDigit rest

/-- A prefix of `v_d…`, for a digit `d`, with no underscore directly before a digit is a prefix
    of `v_1`. -/
private theorem isPrefixOf_of_append_underscore_digit :
    ∀ (v p : List Char) (c : Char) (ds : List Char), noUnderscoreDigit p = true →
      c.isDigit = true → p.isPrefixOf (v ++ '_' :: c :: ds) = true →
      p.isPrefixOf (v ++ ['_', '1']) = true
  | [], [], _, _, _, _, _ => rfl
  | [], a :: p, c, ds, hp, hc, h => by
    simp only [List.nil_append, List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    cases p with
    | nil => rfl
    | cons b p =>
      simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [noUnderscoreDigit, bne_self_eq_false, List.head?_cons, Option.any_some, hc,
        Bool.not_true, Bool.or_false, Bool.false_and, Bool.false_eq_true] at hp
  | _ :: _, [], _, _, _, _, _ => rfl
  | a :: v, b :: p, c, ds, hp, hc, h => by
    simp only [List.cons_append, List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨h.1, isPrefixOf_of_append_underscore_digit v p c ds
      ((Bool.and_eq_true _ _).mp hp).2 hc h.2⟩

/-- The decimal representation of a number starts with a digit. -/
private theorem toString_toList_head_isDigit (k : Nat) :
    ∃ c ds, (toString k).toList = c :: ds ∧ c.isDigit = true := by
  have hrepr : (toString k).toList = Nat.toDigits 10 k := by
    rw [Nat.toString_eq_repr, Nat.toList_repr]
  rw [hrepr]
  cases hd : Nat.toDigits 10 k with
  | nil => exact absurd hd Nat.toDigits_ne_nil
  | cons c ds =>
    refine ⟨c, ds, rfl, Nat.isDigit_of_mem_toDigits (b := 10) (n := k) (by decide) (by decide) ?_⟩
    rw [hd]
    exact List.mem_cons_self

/-- A name `base_k` is one a user may write whenever `base_1` is. -/
private theorem notGeneratedOrRigid_append_underscore (base : TyIdentifier) (k : Nat)
    (h : TyVarAdmissibility.notGeneratedOrRigid (base ++ "_1") = true) :
    TyVarAdmissibility.notGeneratedOrRigid (base ++ "_" ++ toString k) = true := by
  obtain ⟨c, ds, hds, hc⟩ := toString_toList_head_isDigit k
  have hu : "_".toList = ['_'] := by decide
  have hu1 : "_1".toList = ['_', '1'] := by decide
  have hshape : (base ++ "_" ++ toString k).toList = base.toList ++ '_' :: c :: ds := by
    rw [String.toList_append, String.toList_append, hds, hu, List.append_assoc]
    rfl
  have hone : (base ++ "_1").toList = base.toList ++ ['_', '1'] := by
    rw [String.toList_append, hu1]
  have key : ∀ P : String, noUnderscoreDigit P.toList = true →
      P.toList.isPrefixOf (base ++ "_" ++ toString k).toList = true →
      P.toList.isPrefixOf (base ++ "_1").toList = true := by
    intro P hP hpre
    rw [hshape] at hpre
    rw [hone]
    exact isPrefixOf_of_append_underscore_digit _ _ c ds hP hc hpre
  have hgen : noUnderscoreDigit genTyPrefix.toList = true := by decide
  have hsk : noUnderscoreDigit skolemPrefix.toList = true := by decide
  simp only [TyVarAdmissibility.notGeneratedOrRigid, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  refine ⟨?_, ?_⟩
  · cases hp : genTyPrefix.toList.isPrefixOf (base ++ "_" ++ toString k).toList with
    | false => rfl
    | true =>
      rw [key _ hgen hp] at h
      exact absurd h.1 Bool.noConfusion
  · cases hp : skolemPrefix.toList.isPrefixOf (base ++ "_" ++ toString k).toList with
    | false => rfl
    | true =>
      rw [key _ hsk hp] at h
      exact absurd h.2 Bool.noConfusion

/-- `freshName` returns a name a user may write. -/
theorem freshName_admissible (v : TyIdentifier) (avoid : List TyIdentifier) :
    TyVarAdmissibility.notGeneratedOrRigid (freshName v avoid) = true := by
  simp only [freshName]
  by_cases hb : TyVarAdmissibility.notGeneratedOrRigid (v ++ "_1") = true
  · rw [ite_eq_left hb]
    have htaken : (fun n => n == v || avoid.contains n) v = true := by
      simp only [beq_self_eq_true, Bool.true_or]
    obtain ⟨j, hj⟩ := Strata.Name.freshNameBy_of_taken
      (fun n => n == v || avoid.contains n) (avoid.length + 1) v htaken
    rw [hj]
    exact notGeneratedOrRigid_append_underscore v j hb
  · rw [ite_eq_right hb]
    have htaken : (fun n => n == "t" || avoid.contains n) "t" = true := by
      simp only [beq_self_eq_true, Bool.true_or]
    obtain ⟨j, hj⟩ := Strata.Name.freshNameBy_of_taken
      (fun n => n == "t" || avoid.contains n) (avoid.length + 1) "t" htaken
    rw [hj]
    exact notGeneratedOrRigid_append_underscore "t" j (by decide)

/-- If a scope map gives every name a user may write a checker name a user may write, so does
    the map `bindVars` returns. -/
theorem bindVars_admissible (rigid : List TyIdentifier) :
    ∀ (vs : List TyIdentifier) (m : ScopeMap) (st : ScopeState),
      (∀ v w, m.lookup v = some w → TyVarAdmissibility.notGeneratedOrRigid v = true →
        TyVarAdmissibility.notGeneratedOrRigid w = true) →
      ∀ v w, (bindVars rigid vs m st).1.lookup v = some w →
        TyVarAdmissibility.notGeneratedOrRigid v = true →
        TyVarAdmissibility.notGeneratedOrRigid w = true
  | [], _, _, h => h
  | x :: vs, m, st, h => by
    have hcons : ∀ w', (TyVarAdmissibility.notGeneratedOrRigid x = true →
        TyVarAdmissibility.notGeneratedOrRigid w' = true) →
        ∀ v w, ((x, w') :: m).lookup v = some w →
          TyVarAdmissibility.notGeneratedOrRigid v = true →
          TyVarAdmissibility.notGeneratedOrRigid w = true := by
      intro w' hw' v w hl hv
      by_cases hvx : v = x
      · subst hvx
        rw [List.lookup_cons_self, Option.some.injEq] at hl
        subst hl
        exact hw' hv
      · rw [lookup_cons_ne m hvx] at hl
        exact h v w hl hv
    simp only [bindVars]
    split
    · exact bindVars_admissible rigid vs m st h
    · split
      · exact bindVars_admissible rigid vs _ _ (hcons _ (fun _ => freshName_admissible _ _))
      · exact bindVars_admissible rigid vs _ _ (hcons _ id)

/-! ### Written type variables the walk has met are admissible
Every written type variable the walk has bound or seen was a free variable of a declared type
the checker accepted, so a user may write it. -/

/-- The scope map binds no rigid name and only names a user may write, and every written type
    variable the walk has met is a name a user may write. -/
structure ScopeAdmissible (rigid : List TyIdentifier) (m : ScopeMap) (st : ScopeState) :
    Prop where
  noRigid : ∀ r ∈ rigid, m.lookup r = none
  keys : ∀ p ∈ m, TyVarAdmissibility.notGeneratedOrRigid p.1 = true
  seen : ∀ v ∈ st.seen, TyVarAdmissibility.notGeneratedOrRigid v = true

/-- Extending the walk's met type variables by admissible names keeps the scope admissible. -/
theorem ScopeAdmissible.of_seen {rigid : List TyIdentifier} {m : ScopeMap} {st st' : ScopeState}
    (hinv : ScopeAdmissible rigid m st)
    (h : ∀ v ∈ st'.seen, TyVarAdmissibility.notGeneratedOrRigid v = true) :
    ScopeAdmissible rigid m st' :=
  ⟨hinv.noRigid, hinv.keys, h⟩

/-- Binding the type variables of a declared type keeps the scope admissible, and each of those
    type variables is a name a user may write, provided each one's checker name is. -/
private theorem bindVars_scopeAdmissible (rigid : List TyIdentifier) :
    ∀ (vs : List TyIdentifier) (m : ScopeMap) (st : ScopeState),
      ScopeAdmissible rigid m st →
      (∀ v ∈ vs, TyVarAdmissibility.notGeneratedOrRigid
        (checkerName (bindVars rigid vs m st).1 v) = true) →
      ScopeAdmissible rigid (bindVars rigid vs m st).1 (bindVars rigid vs m st).2 ∧
        ∀ v ∈ vs, TyVarAdmissibility.notGeneratedOrRigid v = true
  | [], _, _, hinv, _ => ⟨hinv, fun _ hv => absurd hv List.not_mem_nil⟩
  | v :: vs, m, st, hinv, hw => by
    by_cases hcond : v ∈ rigid ∨ (m.lookup v).isSome
    · have hunf : bindVars rigid (v :: vs) m st = bindVars rigid vs m st := by
        simp only [bindVars, hcond, ↓reduceIte]
      rw [hunf] at hw ⊢
      obtain ⟨hinv', hall⟩ := bindVars_scopeAdmissible rigid vs m st hinv
        (fun u hu => hw u (List.mem_cons_of_mem _ hu))
      refine ⟨hinv', fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | hu'
      · rcases hcond with hrig | hsome
        · have hnone := bindVars_noRigid rigid vs m st hinv.noRigid u hrig
          have hu0 := hw u List.mem_cons_self
          simpa only [checkerName, hnone, Option.getD_none] using hu0
        · obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.mp hsome
          exact hinv.keys (u, w) (List.mem_of_lookup_eq_some hw')
      · exact hall u hu'
    · have hvr : v ∉ rigid := fun hr => hcond (Or.inl hr)
      have hnone : (m.lookup v).isSome = false := by
        cases hm : (m.lookup v).isSome
        · rfl
        · exact absurd (Or.inr hm) hcond
      have hnoRigid' : ∀ w', ∀ r ∈ rigid, ((v, w') :: m).lookup r = none := by
        intro w' r hr
        have hne : r ≠ v := fun h => hvr (h ▸ hr)
        rw [lookup_cons_ne m hne]
        exact hinv.noRigid r hr
      by_cases hseen : v ∈ st.seen
      · have hunf : bindVars rigid (v :: vs) m st =
            bindVars rigid vs ((v, freshName v st.avoid) :: m)
              { st with avoid := freshName v st.avoid :: st.avoid } := by
          simp only [bindVars, hcond, hseen, ↓reduceIte]
        rw [hunf] at hw ⊢
        have hadm : TyVarAdmissibility.notGeneratedOrRigid v = true := hinv.seen v hseen
        have hkeys : ∀ p ∈ (v, freshName v st.avoid) :: m,
            TyVarAdmissibility.notGeneratedOrRigid p.1 = true := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact hadm
          · exact hinv.keys p hp'
        obtain ⟨hinv', hall⟩ := bindVars_scopeAdmissible rigid vs _
          { st with avoid := freshName v st.avoid :: st.avoid }
          ⟨hnoRigid' _, hkeys, hinv.seen⟩
          (fun u hu => hw u (List.mem_cons_of_mem _ hu))
        refine ⟨hinv', fun u hu => ?_⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hadm
        · exact hall u hu'
      · have hunf : bindVars rigid (v :: vs) m st =
            bindVars rigid vs ((v, v) :: m) { seen := v :: st.seen, avoid := v :: st.avoid } := by
          simp only [bindVars, hcond, hseen, ↓reduceIte]
        rw [hunf] at hw ⊢
        have hfinal : (bindVars rigid vs ((v, v) :: m)
            { seen := v :: st.seen, avoid := v :: st.avoid }).1.lookup v = some v :=
          bindVars_mono rigid vs _ _ v v List.lookup_cons_self
        have hadm : TyVarAdmissibility.notGeneratedOrRigid v = true := by
          have hv0 := hw v List.mem_cons_self
          simpa only [checkerName, hfinal, Option.getD_some] using hv0
        have hkeys : ∀ p ∈ (v, v) :: m,
            TyVarAdmissibility.notGeneratedOrRigid p.1 = true := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact hadm
          · exact hinv.keys p hp'
        have hseenAdm : ∀ u ∈ (v :: st.seen),
            TyVarAdmissibility.notGeneratedOrRigid u = true := by
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact hadm
          · exact hinv.seen u hu'
        obtain ⟨hinv', hall⟩ := bindVars_scopeAdmissible rigid vs _ _
          ⟨hnoRigid' _, hkeys, hseenAdm⟩
          (fun u hu => hw u (List.mem_cons_of_mem _ hu))
        refine ⟨hinv', fun u hu => ?_⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hadm
        · exact hall u hu'

/-! ### Checker names avoid the type parameters
When no written type variable is a type parameter and the walk state avoids every type parameter,
no checker name is a type parameter. -/

/-- `freshName` returns a name outside the list it must avoid. -/
private theorem freshName_not_mem (v : TyIdentifier) (avoid : List TyIdentifier) :
    freshName v avoid ∉ avoid := by
  simp only [freshName]
  generalize (if TyVarAdmissibility.notGeneratedOrRigid (v ++ "_1") then v else "t") = base
  have hcover : ∀ n, (n == base || avoid.contains n) = true → n ∈ base :: avoid := by
    intro n hn
    rcases Bool.or_eq_true_iff.mp hn with h | h
    · exact (beq_iff_eq.mp h) ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.contains_iff_mem.mp h)
  have hlen : (base :: avoid).length ≤ avoid.length + 1 := by
    simp only [List.length_cons]; omega
  have hfree := Strata.Name.freshNameBy_not_taken (fun n => n == base || avoid.contains n)
    (avoid.length + 1) base (base :: avoid) hcover hlen
  intro hmem
  simp only [List.contains_iff_mem.mpr hmem, Bool.or_true] at hfree
  cases hfree

/-- `bindVars` keeps checker names out of `ps`, and `ps` among the names to avoid, when no
    non-rigid name of its list is in `ps`. -/
theorem bindVars_scopeAvoids {ps : List TyIdentifier} (rigid : List TyIdentifier) :
    ∀ (vs : List TyIdentifier) (m : ScopeMap) (st : ScopeState), (∀ v ∈ vs, v ∉ rigid → v ∉ ps) →
      ScopeAvoids ps m st →
      ScopeAvoids ps (bindVars rigid vs m st).1 (bindVars rigid vs m st).2
  | [], _, _, _, h => h
  | v :: vs, m, st, hvs, h => by
    have hrest : ∀ v' ∈ vs, v' ∉ rigid → v' ∉ ps :=
      fun v' hv' => hvs v' (List.mem_cons_of_mem v hv')
    simp only [bindVars]
    split
    · exact bindVars_scopeAvoids rigid vs m st hrest h
    · rename_i hcond
      split
      · refine bindVars_scopeAvoids rigid vs _ _ hrest ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact fun hmem => freshName_not_mem v st.avoid (h.avoid _ hmem)
          · exact h.names p hp
        · exact fun x hx => List.mem_cons_of_mem _ (h.avoid x hx)
      · refine bindVars_scopeAvoids rigid vs _ _ hrest ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hvs _ List.mem_cons_self (fun hr => hcond (Or.inl hr))
          · exact h.names p hp
        · exact fun x hx => List.mem_cons_of_mem _ (h.avoid x hx)

/-- `bindVars` only adds names a fresh name must avoid. -/
private theorem bindVars_avoid_mono (rigid : List TyIdentifier) :
    ∀ (vs : List TyIdentifier) (m : ScopeMap) (st : ScopeState),
      ∀ x ∈ st.avoid, x ∈ (bindVars rigid vs m st).2.avoid
  | [], _, _, _, hx => hx
  | v :: vs, m, st, x, hx => by
    simp only [bindVars]
    split
    · exact bindVars_avoid_mono rigid vs m st x hx
    · split
      · exact bindVars_avoid_mono rigid vs _ _ x (List.mem_cons_of_mem _ hx)
      · exact bindVars_avoid_mono rigid vs _ _ x (List.mem_cons_of_mem _ hx)

/-- Renaming a command only adds names a fresh name must avoid. -/
theorem renameCmd_avoid_mono (rigid : List TyIdentifier) (m : ScopeMap) (st : ScopeState)
    (c : Command) : ∀ x ∈ st.avoid, x ∈ (renameCmd rigid m st c).2.2.avoid := by
  cases c with
  | cmd cc =>
    cases cc with
    | init _ xty _ _ =>
      obtain ⟨vars, ty⟩ := xty
      cases vars with
      | nil => exact bindVars_avoid_mono rigid _ m st
      | cons _ _ => exact fun _ hx => hx
    | set | assert | assume | cover => exact fun _ hx => hx
  | call => exact fun _ hx => hx

/-- Renaming a command keeps checker names out of `ps`, and `ps` among the names to avoid, when
    every name in `ps` is rigid. -/
theorem renameCmd_scopeAvoids {ps : List TyIdentifier} (rigid : List TyIdentifier)
    (hps : ∀ x ∈ ps, x ∈ rigid) (m : ScopeMap) (st : ScopeState) (c : Command)
    (hsc : ScopeAvoids ps m st) :
    ScopeAvoids ps (renameCmd rigid m st c).2.1 (renameCmd rigid m st c).2.2 := by
  cases c with
  | cmd cc =>
    cases cc with
    | init _ xty _ _ =>
      obtain ⟨vars, ty⟩ := xty
      cases vars with
      | nil => exact bindVars_scopeAvoids rigid _ m st (fun v _ hvr hvp => hvr (hps v hvp)) hsc
      | cons _ _ => exact hsc
    | set | assert | assume | cover => exact hsc
  | call => exact hsc

/-- Renaming a command keeps the scope admissible, and every type variable of a declared type is
    a name a user may write, when the renamed declared type has only such type variables. -/
theorem renameCmd_scopeAdmissible (rigid : List TyIdentifier) (m : ScopeMap) (st : ScopeState)
    (c : Command) (hinv : ScopeAdmissible rigid m st)
    (hdecl : ∀ x ty e md, c = .cmd (.init x (.forAll [] ty) e md) →
      ∀ v ∈ LMonoTy.freeVars
          (renameTy (checkerName (bindVars rigid (LMonoTy.freeVars ty) m st).1) ty),
        TyVarAdmissibility.notGeneratedOrRigid v = true) :
    ScopeAdmissible rigid (renameCmd rigid m st c).2.1 (renameCmd rigid m st c).2.2 ∧
      ∀ x ty e md, c = .cmd (.init x (.forAll [] ty) e md) →
        ∀ v ∈ LMonoTy.freeVars ty, TyVarAdmissibility.notGeneratedOrRigid v = true := by
  cases c with
  | cmd cc =>
    cases cc with
    | init x xty e md =>
      obtain ⟨vars, ty⟩ := xty
      cases vars with
      | nil =>
        have hbind := bindVars_scopeAdmissible rigid (LMonoTy.freeVars ty) m st hinv
          (fun v hv => hdecl x ty e md rfl _
            (mem_freeVars_renameTy (checkerName (bindVars rigid (LMonoTy.freeVars ty) m st).1)
              ty v hv))
        refine ⟨hbind.1, ?_⟩
        intro x' ty' e' md' hc
        cases hc
        exact hbind.2
      | cons _ _ =>
        refine ⟨hinv, ?_⟩
        intro x' ty' e' md' hc
        cases hc
    | set | assert | assume | cover =>
      exact ⟨hinv, fun _ _ _ _ hc => by cases hc⟩
  | call => exact ⟨hinv, fun _ _ _ _ hc => by cases hc⟩

/-- The checker name of a variable outside `ps` is outside `ps` when the scope map's names are. -/
theorem checkerName_not_mem {ps : List TyIdentifier} {m : ScopeMap}
    (hm : ∀ p ∈ m, p.2 ∉ ps) {v : TyIdentifier} (hv : v ∉ ps) : checkerName m v ∉ ps := by
  unfold checkerName
  cases hl : m.lookup v with
  | none => exact hv
  | some w =>
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp hl
    exact hm (v, w) (List.mem_append_right _ List.mem_cons_self)

/-- Renaming the variables of a type through a map that keeps names outside `ps` outside `ps`
    gives a type avoiding `ps` when the type does. -/
theorem freeVars_renameTy_not_mem {ps : List TyIdentifier} (f : TyIdentifier → TyIdentifier)
    (hf : ∀ v, v ∉ ps → f v ∉ ps) (t : LMonoTy) (ht : ∀ v ∈ LMonoTy.freeVars t, v ∉ ps) :
    ∀ w ∈ LMonoTy.freeVars (renameTy f t), w ∉ ps := by
  have key : ∀ u : LMonoTy, (∀ v ∈ LMonoTy.freeVars u, v ∈ LMonoTy.freeVars t) →
      ∀ w ∈ LMonoTy.freeVars (LMonoTy.subst [restrictTo (fun v => .ftvar (f v)) t] u),
        w ∉ ps := by
    intro u
    induction u with
    | ftvar y =>
      intro hsub w hw
      have hy : y ∈ LMonoTy.freeVars t := hsub y (List.mem_singleton.mpr rfl)
      rw [restrictTo_ftvar _ t y hy] at hw
      simp only [LMonoTy.freeVars, List.mem_singleton] at hw
      subst hw
      exact hf y (ht y hy)
    | bitvec n =>
      intro _ w hw
      rw [LMonoTy.subst_bitvec] at hw
      simp only [LMonoTy.freeVars, List.not_mem_nil] at hw
    | tcons name args ih =>
      intro hsub w hw
      rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map, LMonoTy.freeVars] at hw
      obtain ⟨a', ha', hwa⟩ := LMonoTys.freeVars_exists hw
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
      exact ih a ha (fun v hv => hsub v (LMonoTys.freeVars_mem_subset ha hv)) w hwa
  exact key t (fun v hv => hv)

end Core

end -- public section
