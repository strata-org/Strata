/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Denote
import all Strata.DL.SMT.Denote

public section


/-!
# Rewriting lemmas for the SMT denotation

`denoteQuery` and its helpers are not exposed, so a module that imports
`Strata.DL.SMT.Denote` cannot reduce them in the kernel. The lemmas below
characterize them one constructor at a time. A proof-producing translation
(see `Strata.MetaVerifier`) chains these lemmas to prove
`denoteQuery ctx assums conc = some P` for a concrete query, so the kernel only
has to instantiate lemmas instead of evaluating the denotation.

Lemmas are stated in "hypothesis style": the denotation of each subterm is a
hypothesis, and the conclusion builds the denotation of the parent from the
children's semantic functions. Conclusions only mention constants whose bodies
are visible to importers (structure literals, projections, `denoteSort`,
`denoteFunSort`, `Option.get` and casts), so a semantic function produced by
chaining them reduces to the expected Lean proposition by definitional
unfolding of sort-level definitions alone.

## Key results

- `denoteQuery_of` and `denoteBoolTermFromContext_of` close a whole query: the
  former reduces `denoteQuery` to `denoteBoolTermFromContext` on an empty
  datatype context, the latter peels the interpreted-function, uninterpreted-
  function and uninterpreted-sort binders and evaluates in the empty
  environment.
- The per-construct `den_*` lemmas (e.g. `den_var`, `den_uf`, `den_forall`,
  `den_exists`, `den_eq`, the bitvector/array/option families) characterize
  `denoteTerm` one term constructor at a time.
- The `bind*`, `buildForall`/`buildExists` and `buildIFBody`/`bindIF_eq`
  lemmas drive the binder-closing helpers of `denoteBoolTermFromContext`.
- `substitute*_nil` show synonym substitution in the empty context is the
  identity; the `findIdx_*` and `argTypesAlign_*` lemmas discharge the lookup
  side conditions without evaluating unexposed `DecidableEq` instances.
-/

open Strata.SMT

namespace Strata.SMT.DenoteProps

/-! ## Environment helpers -/

/-- If `uf` is found at index `i` in the context, that index is within the
realized UF environment. -/
theorem ufs_findIdx_lt {ctx : Context} {uf : UF} {i : Nat}
    (hi : ctx.tctx.ufs.findIdx? (· == uf) = some i) (tdi : TermDenoteInput ctx) :
    i < tdi.tΓ.ufs.length :=
  tdi.htΓ.huf.h ▸ (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).left

/-- The function sort of `uf` equals the function sort of the environment entry
found at the same index, so their realizations have the same type. -/
theorem ufs_findIdx_ty {ctx : Context} {uf : UF} {i : Nat}
    (hi : ctx.tctx.ufs.findIdx? (· == uf) = some i) (tdi : TermDenoteInput ctx) :
    denoteFunSort ctx.sctx uf.args uf.out =
      denoteFunSort ctx.sctx (tdi.tΓ.ufs[i]'(ufs_findIdx_lt hi tdi)).uf.args
        (tdi.tΓ.ufs[i]'(ufs_findIdx_lt hi tdi)).uf.out :=
  have hi' := (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).left
  have hiuf : ctx.tctx.ufs[i] = uf := of_decide_eq_true (List.getElem_of_findIdx?_eq_some hi)
  by rw [← tdi.htΓ.huf.ha i hi', hiuf]

/-- If variable `v` is found at index `i` in the context, that index is within
the realized variable environment. -/
theorem vs_findIdx_lt {ctx : Context} {v : TermVar} {i : Nat}
    (hi : ctx.tctx.vs.findIdx? (· == v) = some i) (tdi : TermDenoteInput ctx) :
    i < tdi.tΓ.vs.length :=
  tdi.htΓ.hv.h ▸ (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).left

/-- The sort of `v` equals the sort of the environment entry found at the same
index, so their realizations have the same type. -/
theorem vs_findIdx_ty {ctx : Context} {v : TermVar} {i : Nat}
    (hi : ctx.tctx.vs.findIdx? (· == v) = some i) (tdi : TermDenoteInput ctx) :
    denoteSort ctx.sctx v.ty = denoteSort ctx.sctx (tdi.tΓ.vs[i]'(vs_findIdx_lt hi tdi)).var.ty :=
  have hi' := (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).left
  have hiv : ctx.tctx.vs[i] = v := of_decide_eq_true (List.getElem_of_findIdx?_eq_some hi)
  by rw [← tdi.htΓ.hv.ha i hi', hiv]

/-- Look up the semantic value of a UF symbol in an environment. -/
abbrev lookupUF {ctx : Context} {uf : UF} {i : Nat} {h : (denoteFunSort ctx.sctx uf.args uf.out).isSome}
    (hi : ctx.tctx.ufs.findIdx? (· == uf) = some i) (tdi : TermDenoteInput ctx) :
    (denoteFunSort ctx.sctx uf.args uf.out).get h ⟨tdi.sΓ, tdi.hsΓ⟩ :=
  Option.get_congr (ufs_findIdx_ty hi tdi) ▸ (tdi.tΓ.ufs[i]'(ufs_findIdx_lt hi tdi)).ufΓ

/-- Look up the semantic value of a bound variable in an environment. -/
abbrev lookupVar {ctx : Context} {v : TermVar} {i : Nat} {h : (denoteSort ctx.sctx v.ty).isSome}
    (hi : ctx.tctx.vs.findIdx? (· == v) = some i) (tdi : TermDenoteInput ctx) :
    (denoteSort ctx.sctx v.ty).get h ⟨tdi.sΓ, tdi.hsΓ⟩ :=
  Option.get_congr (vs_findIdx_ty hi tdi) ▸ (tdi.tΓ.vs[i]'(vs_findIdx_lt hi tdi)).varΓ

/-- The empty sort environment is well-formed for the empty sort context. -/
theorem sortEnv_nil_wf (iss : ISContext) : SortEnvironment.WF ⟨[], iss⟩ [] :=
  { h := rfl, ha := fun _ hi => nomatch hi }

/-- The empty term environment is well-formed for the empty term context. -/
theorem termEnv_nil_wf (sΓ : SortDenoteInput sctx) :
    ({ vs := [], ufs := [] } : TermEnvironment sΓ).WF { vs := [], ufs := [] } :=
  { hv := { h := rfl, ha := fun _ hi => nomatch hi },
    huf := { h := rfl, ha := fun _ hi => nomatch hi } }

/-- Extending both a UF context and its environment by the same symbol
preserves well-formedness. -/
theorem ufEnv_cons_wf {sΓ : SortDenoteInput sctx} {ufs : UFContext} {Γ : UFEnvironment sΓ}
    (h : UFEnvironment.WF ufs Γ) (d : UFDenote sΓ) : UFEnvironment.WF (d.uf :: ufs) (d :: Γ) :=
  { h := by simp [h.h]
    ha := fun i hi => match i with
      | 0 => rfl
      | i + 1 => by simpa using h.ha i (Nat.lt_of_succ_lt_succ hi) }

/-- Extending both a variable context and its environment by the same variable
preserves well-formedness. -/
theorem varEnv_cons_wf {sΓ : SortDenoteInput sctx} {vs : TermVarContext} {Γ : TermVarEnvironment sΓ}
    (h : TermVarEnvironment.WF vs Γ) (d : TermVarDenote sΓ) : TermVarEnvironment.WF (d.var :: vs) (d :: Γ) :=
  { h := by simp [h.h]
    ha := fun i hi => match i with
      | 0 => rfl
      | i + 1 => by simpa using h.ha i (Nat.lt_of_succ_lt_succ hi) }

/-- The empty term environment, as used by `denoteBoolTermFromContext`. -/
abbrev emptyInput : TermDenoteInput ⟨{}, ⟨[], []⟩⟩ :=
  { sΓ := [], hsΓ := sortEnv_nil_wf ∅, tΓ := { vs := [], ufs := [] },
    htΓ := termEnv_nil_wf _ }

/-- Extend a term environment with the realization of a UF symbol. -/
abbrev pushUF {ctx : Context} (tdi : TermDenoteInput ctx) (uf : UF)
    (h : (denoteFunSort ctx.sctx uf.args uf.out).isSome)
    (f : (denoteFunSort ctx.sctx uf.args uf.out).get h ⟨tdi.sΓ, tdi.hsΓ⟩) :
    TermDenoteInput ⟨ctx.sctx, ⟨ctx.tctx.vs, uf :: ctx.tctx.ufs⟩⟩ :=
  { sΓ := tdi.sΓ, hsΓ := tdi.hsΓ,
    tΓ := { vs := tdi.tΓ.vs, ufs := ⟨uf, h, f⟩ :: tdi.tΓ.ufs },
    htΓ := { hv := tdi.htΓ.hv, huf := ufEnv_cons_wf tdi.htΓ.huf ⟨uf, h, f⟩ } }

/-- Extend a term environment with the value of a bound variable. -/
abbrev pushVar {ctx : Context} (tdi : TermDenoteInput ctx) (v : TermVar)
    (h : (denoteSort ctx.sctx v.ty).isSome)
    (x : (denoteSort ctx.sctx v.ty).get h ⟨tdi.sΓ, tdi.hsΓ⟩) :
    TermDenoteInput ⟨ctx.sctx, ⟨v :: ctx.tctx.vs, ctx.tctx.ufs⟩⟩ :=
  { sΓ := tdi.sΓ, hsΓ := tdi.hsΓ,
    tΓ := { vs := ⟨v, h, x⟩ :: tdi.tΓ.vs, ufs := tdi.tΓ.ufs },
    htΓ := { hv := varEnv_cons_wf tdi.htΓ.hv ⟨v, h, x⟩, huf := tdi.htΓ.huf } }


/-! ## Type-synonym substitution is the identity for the empty context -/

mutual
/-- Substituting type synonyms under the empty synonym context leaves a type
unchanged. -/
theorem substituteIS_nil : (ty : TermType) → substituteIS (∅ : ISContext) ty = ty
  | .prim _ => by simp [substituteIS]
  | .option ty => by simp [substituteIS, substituteIS_nil ty]
  | .constr id args => by
    simp [substituteIS, substituteISs_nil args, show Map.find? (∅ : ISContext) id = none from rfl]
/-- Substituting type synonyms under the empty synonym context leaves a list of
types unchanged. -/
theorem substituteISs_nil : (tys : List TermType) → substituteISs (∅ : ISContext) tys = tys
  | [] => by simp [substituteISs]
  | ty :: tys => by simp [substituteISs, substituteIS_nil ty, substituteISs_nil tys]
end

/-- Substituting type synonyms under the empty synonym context leaves a term
variable unchanged. -/
theorem substituteTermVarIS_nil (v : TermVar) : substituteTermVarIS (∅ : ISContext) v = v := by
  simp [substituteTermVarIS, substituteIS_nil]

/-- Substituting type synonyms under the empty synonym context leaves a UF
symbol unchanged. -/
theorem substituteUFIS_nil (uf : UF) : substituteUFIS (∅ : ISContext) uf = uf := by
  have : ∀ l : List TermType, l.map (substituteIS (∅ : ISContext)) = l := fun l => by
    simp [funext substituteIS_nil]
  simp [substituteUFIS, substituteIS_nil, this]

mutual
/-- Substituting type synonyms under the empty synonym context leaves a term
unchanged. -/
theorem substituteTermIS_nil : (t : Term) → substituteTermIS (∅ : ISContext) t = t
  | .prim _ => by simp [substituteTermIS]
  | .var v => by simp [substituteTermIS, substituteTermVarIS_nil]
  | .none ty => by simp [substituteTermIS, substituteIS_nil]
  | .some t => by simp [substituteTermIS, substituteTermIS_nil t]
  | .app op as ty => by
    have hs := substituteTermISs_nil as
    by_cases h : ∃ f, op = .core (.uf f)
    · obtain ⟨f, rfl⟩ := h
      simp [substituteTermIS, hs, substituteIS_nil, substituteUFIS_nil]
    · simp only [not_exists] at h
      simp [substituteTermIS, hs, substituteIS_nil]
  | .quant q vs tr b => by
    have : vs.map (substituteTermVarIS (∅ : ISContext)) = vs := by simp [funext substituteTermVarIS_nil]
    simp [substituteTermIS, this, substituteTermISss_nil tr, substituteTermIS_nil b]
/-- Substituting type synonyms under the empty synonym context leaves a list of
terms unchanged. -/
theorem substituteTermISs_nil : (ts : List Term) → substituteTermISs (∅ : ISContext) ts = ts
  | [] => by simp [substituteTermISs]
  | t :: ts => by simp [substituteTermISs, substituteTermIS_nil t, substituteTermISs_nil ts]
/-- Substituting type synonyms under the empty synonym context leaves a list of
lists of terms (quantifier triggers) unchanged. -/
theorem substituteTermISss_nil : (tss : List (List Term)) → substituteTermISss (∅ : ISContext) tss = tss
  | [] => by simp [substituteTermISss]
  | ts :: tss => by simp [substituteTermISss, substituteTermISs_nil ts, substituteTermISss_nil tss]
end

/-! ## Closing the context -/

/-- Reduce `denoteQuery` to `denoteBoolTermFromContext` on the implication of
the axioms and assumptions over the conclusion, given that the datatype
machinery of the context is empty. -/
theorem denoteQuery_of (ctx : Core.SMT.Context) (assums : List Term) (conc : Term) (P : Prop)
    (hdt : ctx.datatypes.factory.isEmpty = true) (hs : ctx.seenDatatypes.isEmpty = true)
    (hf : ctx.datatypeFuns.isEmpty = true)
    (h : denoteBoolTermFromContext ctx.sorts.toList.reverse (mkISContext ctx.tySubst).reverse
          ctx.ufs.toList.reverse ctx.ifs.toList.reverse
          (ctx.axms.toList.foldr (.app .implies [·, ·] (.prim .bool))
            (assums.foldr (.app .implies [·, ·] (.prim .bool)) conc)) = some (PLift.up P)) :
    denoteQuery ctx assums conc = some P := by
  simp only [denoteQuery, hdt, hs, hf, Bool.not_true, Bool.or_false]
  rw [h]
  rfl

/-- The synonym context built from the empty substitution is empty. -/
theorem mkISContext_nil : mkISContext [] = ∅ := by simp [mkISContext, mkISContext.go]

/--
Close a boolean term: substitute sort synonyms, then eliminate the
interpreted-function, uninterpreted-function and uninterpreted-sort binders,
and evaluate in the empty environment. The substituted declarations and term
(`ufs'`, `ifs'`, `t'`) are supplied by the caller.
-/
theorem denoteBoolTermFromContext_of (uss : USContext) (iss : ISContext) (ufs : UFContext)
    (ifs : List IF) (t : Term) (ufs' : UFContext) (ifs' : List IF) (t' : Term)
    (h : (denoteSort ⟨uss, iss⟩ (.prim .bool)).isSome)
    (ft : TermDenoteInput ⟨⟨uss, iss⟩, ⟨[], ifs'.map IF.toUF ++ ufs'⟩⟩ → Prop)
    (ft₁ : TermDenoteInput ⟨⟨uss, iss⟩, ⟨[], ufs'⟩⟩ → Prop)
    (ft₂ : TermDenoteInput ⟨⟨uss, iss⟩, ⟨[], []⟩⟩ → Prop)
    (ft₃ : SortDenoteInput ⟨[], []⟩ → Prop)
    (hufs : (if iss.isEmpty then ufs else ufs.map (substituteUFIS iss)) = ufs')
    (hifs : (if iss.isEmpty then ifs else ifs.map (substituteIFIS iss)) = ifs')
    (htt : substituteTermIS iss t = t')
    (ht : denoteTerm ⟨⟨uss, iss⟩, ⟨[], ifs'.map IF.toUF ++ ufs'⟩⟩ t' = some ⟨.prim .bool, h, ft⟩)
    (hif : denoteBoolTermFromContext.bindIFs ⟨uss, iss⟩ [] ufs' ifs' ft = some ft₁)
    (huf : denoteBoolTermFromContext.bindUFs ⟨uss, iss⟩ [] ufs' ft₁ = some ft₂)
    (hus : denoteBoolTermFromContext.bindUSs uss []
      (fun sdi => ft₂ ⟨sdi.sΓ, sdi.hsΓ, ⟨[], []⟩, termEnv_nil_wf _⟩) = some ft₃) :
    denoteBoolTermFromContext uss iss ufs ifs t = some (PLift.up (ft₃ ⟨[], sortEnv_nil_wf []⟩)) := by
  subst hufs hifs htt
  rw [denoteBoolTermFromContext]
  show Option.bind (denoteTerm ⟨⟨uss, iss⟩, ⟨[], _⟩⟩ _) _ = _
  rw [ht, Option.bind_some]
  show Option.bind (denoteBoolTermFromContext.bindIFs ⟨uss, iss⟩ [] _ _ ft) _ = _
  rw [hif, Option.bind_some]
  show Option.bind (denoteBoolTermFromContext.bindUFs ⟨uss, iss⟩ [] _ ft₁) _ = _
  rw [huf, Option.bind_some]
  show Option.bind (denoteBoolTermFromContext.bindISs uss iss _) _ = _
  rw [denoteBoolTermFromContext.bindISs, Option.pure_def, Option.bind_some]
  show Option.bind (denoteBoolTermFromContext.bindUSs uss []
    (fun sdi => ft₂ ⟨sdi.sΓ, sdi.hsΓ, ⟨[], []⟩, termEnv_nil_wf _⟩)) _ = _
  rw [hus, Option.bind_some]
  rfl

/-- Extending both an uninterpreted-sort context and its environment by the same
sort preserves well-formedness. -/
theorem usEnv_cons_wf {uss : USContext} {Γ : USEnvironment} (h : USEnvironment.WF uss Γ)
    (d : USDenote) : USEnvironment.WF (d.us :: uss) (d :: Γ) :=
  { h := by simp [h.h]
    ha := fun i hi => match i with
      | 0 => rfl
      | i + 1 => by simpa using h.ha i (Nat.lt_of_succ_lt_succ hi) }

/-- Closing over an empty list of uninterpreted sorts leaves the predicate
unchanged. -/
theorem bindUSs_nil (iss : ISContext) (ft : SortDenoteInput ⟨[], iss⟩ → Prop) :
    denoteBoolTermFromContext.bindUSs [] iss ft = some ft := by
  simp [denoteBoolTermFromContext.bindUSs]

section
-- Mirrors `bindUS`'s non-class `[inst : mkNonemptyPred α]` binder (Denote.lean).
set_option checkBinderAnnotations false
/-- Closing over `us :: uss` universally quantifies the realization of `us`
(and its nonemptiness witness) before closing over the rest. -/
theorem bindUSs_cons (us : Strata.DL.SMT.Sort) (uss : USContext) (iss : ISContext)
    (ft : SortDenoteInput ⟨us :: uss, iss⟩ → Prop) (ft' : SortDenoteInput ⟨[], iss⟩ → Prop)
    (h : denoteBoolTermFromContext.bindUSs uss iss
      (fun sdi => ∀ (α : mkTypeFunType us.arity) [inst : mkNonemptyPred α],
        ft ⟨⟨us, α, inst⟩ :: sdi.sΓ, usEnv_cons_wf sdi.hsΓ ⟨us, α, inst⟩⟩) = some ft') :
    denoteBoolTermFromContext.bindUSs (us :: uss) iss ft = some ft' := by
  simp only [denoteBoolTermFromContext.bindUSs, bindUS]
  exact h
end

/-- Closing over an empty list of uninterpreted functions leaves the predicate
unchanged. -/
theorem bindUFs_nil (sctx : SortContext) (vs : TermVarContext)
    (ft : TermDenoteInput ⟨sctx, ⟨vs, []⟩⟩ → Prop) :
    denoteBoolTermFromContext.bindUFs sctx vs [] ft = some ft := by
  simp [denoteBoolTermFromContext.bindUFs]

/-- Closing over `uf :: ufs` universally quantifies the realization of `uf`
before closing over the rest. -/
theorem bindUFs_cons (sctx : SortContext) (vs : TermVarContext) (uf : UF) (ufs : UFContext)
    (ft : TermDenoteInput ⟨sctx, ⟨vs, uf :: ufs⟩⟩ → Prop)
    (hTys : (denoteFunSort sctx uf.args uf.out).isSome)
    (ft' : TermDenoteInput ⟨sctx, ⟨vs, []⟩⟩ → Prop)
    (h : denoteBoolTermFromContext.bindUFs sctx vs ufs
          (fun tdi => ∀ f, ft (pushUF (ctx := ⟨sctx, ⟨vs, ufs⟩⟩) tdi uf hTys f)) = some ft') :
    denoteBoolTermFromContext.bindUFs sctx vs (uf :: ufs) ft = some ft' := by
  simp only [denoteBoolTermFromContext.bindUFs, bindUF, hTys, ↓reduceDIte]
  exact h

/-- Closing over an empty list of interpreted functions leaves the predicate
unchanged. -/
theorem bindIFs_nil (sctx : SortContext) (vs : TermVarContext) (ufs : UFContext)
    (ft : TermDenoteInput ⟨sctx, ⟨vs, ufs⟩⟩ → Prop) :
    denoteBoolTermFromContext.bindIFs sctx vs ufs [] ft = some ft := by
  simp [denoteBoolTermFromContext.bindIFs]

/-! ## Terms -/

/-- Denoting the empty argument list yields the empty list of results. -/
theorem denoteTerms_nil (ctx : Context) : denoteTerms ctx [] = some [] := by
  simp [denoteTerms]

/-- Denoting `a :: as` conses the denotation of the head onto the denotations
of the tail. -/
theorem denoteTerms_cons (ctx : Context) (a : Term) (as : List Term)
    (r : TermDenoteResult ctx) (rs : List (TermDenoteResult ctx))
    (ha : denoteTerm ctx a = some r) (has : denoteTerms ctx as = some rs) :
    denoteTerms ctx (a :: as) = some (r :: rs) := by
  simp [denoteTerms, ha, has]

/-- The boolean literal `true` denotes the always-true predicate. -/
theorem den_true (ctx : Context) :
    denoteTerm ctx (.prim (.bool true)) = some ⟨.prim .bool, rfl, fun _ => True⟩ := by
  simp [denoteTerm]

/-- The boolean literal `false` denotes the always-false predicate. -/
theorem den_false (ctx : Context) :
    denoteTerm ctx (.prim (.bool false)) = some ⟨.prim .bool, rfl, fun _ => False⟩ := by
  simp [denoteTerm]

/-- The integer literal `x` denotes the constant function returning `x`. -/
theorem den_int (ctx : Context) (x : Int) :
    denoteTerm ctx (.prim (.int x)) = some ⟨.prim .int, rfl, fun _ => x⟩ := by
  simp [denoteTerm]

/-- Negation denotes the logical negation of its argument's denotation. -/
theorem den_not (ctx : Context) (a : Term) (rt : TermType) (h : (denoteSort ctx.sctx (.prim .bool)).isSome)
    (fa : (tdi : TermDenoteInput ctx) → (denoteSort ctx.sctx (.prim .bool)).get h ⟨tdi.sΓ, tdi.hsΓ⟩)
    (ha : denoteTerm ctx a = some ⟨.prim .bool, h, fa⟩) :
    denoteTerm ctx (.app .not [a] rt) = some ⟨.prim .bool, h, fun Γ => ¬ fa Γ⟩ := by
  simp [denoteTerm, ha]

/-- Shorthand for the type of a semantic function of sort `ty`. -/
abbrev SemFun (ctx : Context) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome) :=
  (tdi : TermDenoteInput ctx) → (denoteSort ctx.sctx ty).get h ⟨tdi.sΓ, tdi.hsΓ⟩

/-- `ite` denotes the classical if-then-else over its condition's denotation. -/
theorem den_ite (ctx : Context) (c a b : Term) (rt ty : TermType)
    (hc : (denoteSort ctx.sctx (.prim .bool)).isSome) (fc : SemFun ctx (.prim .bool) hc)
    (h₁ h₂ : (denoteSort ctx.sctx ty).isSome) (fa : SemFun ctx ty h₁) (fb : SemFun ctx ty h₂)
    (hc' : denoteTerm ctx c = some ⟨.prim .bool, hc, fc⟩)
    (ha : denoteTerm ctx a = some ⟨ty, h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨ty, h₂, fb⟩) :
    denoteTerm ctx (.app .ite [c, a, b] rt) =
      some ⟨ty, h₁, fun Γ => @ite _ (fc Γ) (Classical.propDecidable (fc Γ)) (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, hc', ha, hb]

/-- Two-argument instances of `chainable` (`=`, `<=`, `<`, `>=`, `>`). -/
theorem den_chain2 (ctx : Context) (op : Op) (a b : Term) (rt ty : TermType)
    (h : (denoteSort ctx.sctx ty).isSome) (h₁ h₂ : (denoteSort ctx.sctx ty).isSome)
    (rel : (sdi : SortDenoteInput ctx.sctx) → (denoteSort ctx.sctx ty).get h sdi →
      (denoteSort ctx.sctx ty).get h sdi → Prop)
    (fa : SemFun ctx ty h₁) (fb : SemFun ctx ty h₂)
    (hop : ∀ (as : List Term), denoteTerm ctx (.app op as rt) =
      (denoteTerms ctx as).bind (chainable ctx ty h rel))
    (ha : denoteTerm ctx a = some ⟨ty, h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨ty, h₂, fb⟩) :
    denoteTerm ctx (.app op [a, b] rt) =
      some ⟨.prim .bool, rfl, fun Γ => rel ⟨Γ.sΓ, Γ.hsΓ⟩ (fa Γ) (fb Γ)⟩ := by
  rw [hop]
  simp [denoteTerms, ha, hb, chainable, chainable.go]

/-- Unfold `<=` to a `chainable` over integer operands. -/
theorem den_le_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .le as rt) =
      (denoteTerms ctx as).bind (chainable ctx (.prim .int) rfl (fun _ => @LE.le Int _)) := by
  simp [denoteTerm]
/-- Unfold `<` to a `chainable` over integer operands. -/
theorem den_lt_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .lt as rt) =
      (denoteTerms ctx as).bind (chainable ctx (.prim .int) rfl (fun _ => @LT.lt Int _)) := by
  simp [denoteTerm]
/-- Unfold `>=` to a `chainable` over integer operands. -/
theorem den_ge_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .ge as rt) =
      (denoteTerms ctx as).bind (chainable ctx (.prim .int) rfl (fun _ => @GE.ge Int _)) := by
  simp [denoteTerm]
/-- Unfold `>` to a `chainable` over integer operands. -/
theorem den_gt_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .gt as rt) =
      (denoteTerms ctx as).bind (chainable ctx (.prim .int) rfl (fun _ => @GT.gt Int _)) := by
  simp [denoteTerm]

/-- Equality of two operands denotes propositional equality of their
denotations. -/
theorem den_eq (ctx : Context) (a b : Term) (rt ty : TermType)
    (h₁ h₂ : (denoteSort ctx.sctx ty).isSome) (fa : SemFun ctx ty h₁) (fb : SemFun ctx ty h₂)
    (ha : denoteTerm ctx a = some ⟨ty, h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨ty, h₂, fb⟩) :
    denoteTerm ctx (.app .eq [a, b] rt) =
      some ⟨.prim .bool, rfl, fun Γ => @Eq ((denoteSort ctx.sctx ty).get h₁ ⟨Γ.sΓ, Γ.hsΓ⟩) (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, denoteTerms, ha, hb, chainable, chainable.go]

/-! ### Left-associative operators -/

/-- The left-fold over no further operands returns the accumulated function. -/
theorem leftAssoc_go_nil (ctx : Context) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome) op
    (ft : SemFun ctx ty h) :
    leftAssoc.go ctx ty h op ft [] = some ⟨ty, h, ft⟩ := by
  simp [leftAssoc.go]

/-- The left-fold combines the accumulator with the next operand, then recurses. -/
theorem leftAssoc_go_cons (ctx : Context) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome) op
    (ft : SemFun ctx ty h) (h' : (denoteSort ctx.sctx ty).isSome) (f : SemFun ctx ty h')
    (ts : List (TermDenoteResult ctx)) (r : TermDenoteResult ctx)
    (hg : leftAssoc.go ctx ty h op (fun tdi => op ⟨tdi.sΓ, tdi.hsΓ⟩ (ft tdi) (f tdi)) ts = some r) :
    leftAssoc.go ctx ty h op ft (⟨ty, h', f⟩ :: ts) = some r := by
  simpa [leftAssoc.go] using hg

/-- `leftAssoc` over at least two operands seeds the fold with the first two. -/
theorem leftAssoc_cons2 (ctx : Context) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome) op
    (h₁ h₂ : (denoteSort ctx.sctx ty).isSome) (f₁ : SemFun ctx ty h₁) (f₂ : SemFun ctx ty h₂)
    (ts : List (TermDenoteResult ctx)) (r : TermDenoteResult ctx)
    (hg : leftAssoc.go ctx ty h op (fun tdi => op ⟨tdi.sΓ, tdi.hsΓ⟩ (f₁ tdi) (f₂ tdi)) ts = some r) :
    leftAssoc ctx ty h op (⟨ty, h₁, f₁⟩ :: ⟨ty, h₂, f₂⟩ :: ts) = some r := by
  simpa [leftAssoc] using hg

/-- Left-associative operators whose denotation is `leftAssoc` over the operands. -/
theorem den_leftAssoc (ctx : Context) (op : Op) (as : List Term) (rt ty : TermType)
    (h : (denoteSort ctx.sctx ty).isSome) opF (rs : List (TermDenoteResult ctx))
    (r : TermDenoteResult ctx)
    (hop : denoteTerm ctx (.app op as rt) = (denoteTerms ctx as).bind (leftAssoc ctx ty h opF))
    (has : denoteTerms ctx as = some rs) (hl : leftAssoc ctx ty h opF rs = some r) :
    denoteTerm ctx (.app op as rt) = some r := by
  rw [hop, has, Option.bind_some, hl]

/-- Unfold `and` to a left-fold of `∧` over its operands. -/
theorem den_and_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .and as rt) =
      (denoteTerms ctx as).bind (leftAssoc ctx (.prim .bool) rfl (fun _ => And)) := by
  simp [denoteTerm]
/-- Unfold `or` to a left-fold of `∨` over its operands. -/
theorem den_or_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .or as rt) =
      (denoteTerms ctx as).bind (leftAssoc ctx (.prim .bool) rfl (fun _ => Or)) := by
  simp [denoteTerm]
/-- Unfold integer `+` to a left-fold of addition over its operands. -/
theorem den_add_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .add as rt) =
      (denoteTerms ctx as).bind (leftAssoc ctx (.prim .int) rfl (fun _ => @HAdd.hAdd Int Int Int _)) := by
  simp [denoteTerm]
/-- Unfold integer `-` to a left-fold of subtraction over its operands. -/
theorem den_sub_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .sub as rt) =
      (denoteTerms ctx as).bind (leftAssoc ctx (.prim .int) rfl (fun _ => @HSub.hSub Int Int Int _)) := by
  simp [denoteTerm]
/-- Unfold integer `*` to a left-fold of multiplication over its operands. -/
theorem den_mul_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .mul as rt) =
      (denoteTerms ctx as).bind (leftAssoc ctx (.prim .int) rfl (fun _ => @HMul.hMul Int Int Int _)) := by
  simp [denoteTerm]
/-- Unfold integer `/` to a left-fold of division over its operands. -/
theorem den_div_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .div as rt) =
      (denoteTerms ctx as).bind (leftAssoc ctx (.prim .int) rfl (fun _ => @HDiv.hDiv Int Int Int _)) := by
  simp [denoteTerm]

/-- Integer negation denotes `-` of its argument's denotation. -/
theorem den_neg (ctx : Context) (a : Term) (rt : TermType) (h : (denoteSort ctx.sctx (.prim .int)).isSome)
    (fa : SemFun ctx (.prim .int) h) (ha : denoteTerm ctx a = some ⟨.prim .int, h, fa⟩) :
    denoteTerm ctx (.app .neg [a] rt) = some ⟨.prim .int, rfl, fun Γ => @Neg.neg Int _ (fa Γ)⟩ := by
  simp [denoteTerm, ha]

/-- Integer modulo denotes `%` of its two arguments' denotations. -/
theorem den_mod (ctx : Context) (a b : Term) (rt : TermType)
    (h₁ h₂ : (denoteSort ctx.sctx (.prim .int)).isSome)
    (fa : SemFun ctx (.prim .int) h₁) (fb : SemFun ctx (.prim .int) h₂)
    (ha : denoteTerm ctx a = some ⟨.prim .int, h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨.prim .int, h₂, fb⟩) :
    denoteTerm ctx (.app .mod [a, b] rt) =
      some ⟨.prim .int, rfl, fun Γ => @HMod.hMod Int Int Int _ (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-! ### Implication (right-associative) -/

/-- The right-fold over exactly two operands applies the operator once. -/
theorem rightAssoc_go_two (ctx : Context) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome) op
    (h₁ h₂ : (denoteSort ctx.sctx ty).isSome) (f₁ : SemFun ctx ty h₁) (f₂ : SemFun ctx ty h₂) :
    rightAssoc.go ctx ty h op [⟨ty, h₁, f₁⟩, ⟨ty, h₂, f₂⟩] =
      some (fun tdi => op ⟨tdi.sΓ, tdi.hsΓ⟩ (f₁ tdi) (f₂ tdi)) := by
  simp [rightAssoc.go]

/-- The right-fold applies the operator to the head and the fold of the tail. -/
theorem rightAssoc_go_cons (ctx : Context) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome) op
    (h₁ : (denoteSort ctx.sctx ty).isSome) (f₁ : SemFun ctx ty h₁)
    (t₂ t₃ : TermDenoteResult ctx) (ts : List (TermDenoteResult ctx)) (g : SemFun ctx ty h)
    (hg : rightAssoc.go ctx ty h op (t₂ :: t₃ :: ts) = some g) :
    rightAssoc.go ctx ty h op (⟨ty, h₁, f₁⟩ :: t₂ :: t₃ :: ts) =
      some (fun tdi => op ⟨tdi.sΓ, tdi.hsΓ⟩ (f₁ tdi) (g tdi)) := by
  simp [rightAssoc.go, hg]

/-- Implication denotes the right-associative chain of `→` over its operands. -/
theorem den_implies (ctx : Context) (as : List Term) (rt : TermType)
    (rs : List (TermDenoteResult ctx)) (g : SemFun ctx (.prim .bool) rfl)
    (has : denoteTerms ctx as = some rs)
    (hg : rightAssoc.go ctx (.prim .bool) rfl (fun _ p q => p → q) rs = some g) :
    denoteTerm ctx (.app .implies as rt) = some ⟨.prim .bool, rfl, g⟩ := by
  simp [denoteTerm, has, rightAssoc, hg]

/-! ### Bitvectors, strings, arrays and options -/

/-- Bitvector negation denotes two's-complement negation. -/
theorem den_bvneg (ctx : Context) (a : Term) (rt : TermType) (n : Nat)
    (h : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (fa : SemFun ctx (.prim (.bitvec n)) h)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h, fa⟩) :
    denoteTerm ctx (.app .bvneg [a] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => @Neg.neg (BitVec n) _ (fa Γ)⟩ := by
  simp [denoteTerm, ha]

/-- Bitvector `bvnot` denotes bitwise complement. -/
theorem den_bvnot (ctx : Context) (a : Term) (rt : TermType) (n : Nat)
    (h : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (fa : SemFun ctx (.prim (.bitvec n)) h)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h, fa⟩) :
    denoteTerm ctx (.app .bvnot [a] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => @Complement.complement (BitVec n) _ (fa Γ)⟩ := by
  simp [denoteTerm, ha]

/-- Bitvector `bvnego` denotes the negation-overflow predicate. -/
theorem den_bvnego (ctx : Context) (a : Term) (rt : TermType) (n : Nat)
    (h : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (fa : SemFun ctx (.prim (.bitvec n)) h)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h, fa⟩) :
    denoteTerm ctx (.app .bvnego [a] rt) = some ⟨(.prim .bool), rfl, fun Γ => BitVec.negOverflow (fa Γ) = true⟩ := by
  simp [denoteTerm, ha]

/-- Zero-extension by `i` bits denotes `BitVec.zeroExtend`. -/
theorem den_zero_extend (ctx : Context) (a : Term) (rt : TermType) (i : Nat) (n : Nat)
    (h : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (fa : SemFun ctx (.prim (.bitvec n)) h)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h, fa⟩) :
    denoteTerm ctx (.app (.zero_extend i) [a] rt) = some ⟨(.prim (.bitvec (n + i))), rfl, fun Γ => BitVec.zeroExtend (n + i) (fa Γ)⟩ := by
  simp [denoteTerm, ha]

/-- Unsigned bitvector-to-integer denotes `Int.ofNat ∘ BitVec.toNat`. -/
theorem den_ubv_to_int (ctx : Context) (a : Term) (rt : TermType) (n : Nat)
    (h : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (fa : SemFun ctx (.prim (.bitvec n)) h)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h, fa⟩) :
    denoteTerm ctx (.app .ubv_to_int [a] rt) = some ⟨(.prim .int), rfl, fun Γ => Int.ofNat (fa Γ).toNat⟩ := by
  simp [denoteTerm, ha]

/-- Signed bitvector-to-integer denotes `BitVec.toInt`. -/
theorem den_sbv_to_int (ctx : Context) (a : Term) (rt : TermType) (n : Nat)
    (h : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (fa : SemFun ctx (.prim (.bitvec n)) h)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h, fa⟩) :
    denoteTerm ctx (.app .sbv_to_int [a] rt) = some ⟨(.prim .int), rfl, fun Γ => (fa Γ).toInt⟩ := by
  simp [denoteTerm, ha]

/-- Integer-to-bitvector of width `n` denotes `BitVec.ofInt n`. -/
theorem den_int_to_bv (ctx : Context) (a : Term) (rt : TermType) (n : Nat)
    (h : (denoteSort ctx.sctx (.prim .int)).isSome) (fa : SemFun ctx (.prim .int) h)
    (ha : denoteTerm ctx a = some ⟨(.prim .int), h, fa⟩) :
    denoteTerm ctx (.app (.int_to_bv n) [a] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => BitVec.ofInt n (fa Γ)⟩ := by
  simp [denoteTerm, ha]

/-- String length denotes `Int.ofNat ∘ String.length`. -/
theorem den_str_length (ctx : Context) (a : Term) (rt : TermType)
    (h : (denoteSort ctx.sctx (.prim .string)).isSome) (fa : SemFun ctx (.prim .string) h)
    (ha : denoteTerm ctx a = some ⟨(.prim .string), h, fa⟩) :
    denoteTerm ctx (.app .str_length [a] rt) = some ⟨(.prim .int), rfl, fun Γ => Int.ofNat (fa Γ).length⟩ := by
  simp [denoteTerm, ha]

/-- Integer absolute value denotes the if-then-else over `< 0` matching
`denoteTerm`'s decidability instance. -/
theorem den_abs (ctx : Context) (a : Term) (rt : TermType)
    (h : (denoteSort ctx.sctx (.prim .int)).isSome) (fa : SemFun ctx (.prim .int) h)
    (ha : denoteTerm ctx a = some ⟨(.prim .int), h, fa⟩) :
    denoteTerm ctx (.app .abs [a] rt) = some ⟨(.prim .int), rfl, fun Γ => @ite Int (@LT.lt Int _ (fa Γ) 0) (Int.decLt (fa Γ) 0) (@Neg.neg Int _ (fa Γ)) (fa Γ)⟩ := by
  simp [denoteTerm, ha] <;> rfl

/-- Bitvector left shift denotes `<<<`. -/
theorem den_bvshl (ctx : Context) (a b : Term) (rt : TermType) (n : Nat) (m : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec m))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec m)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec m)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvshl [a, b] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => @HShiftLeft.hShiftLeft (BitVec n) (BitVec m) (BitVec n) _ (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Bitvector logical right shift denotes `>>>`. -/
theorem den_bvlshr (ctx : Context) (a b : Term) (rt : TermType) (n : Nat) (m : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec m))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec m)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec m)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvlshr [a, b] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => @HShiftRight.hShiftRight (BitVec n) (BitVec m) (BitVec n) _ (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Bitvector arithmetic right shift denotes `BitVec.sshiftRight'`. -/
theorem den_bvashr (ctx : Context) (a b : Term) (rt : TermType) (n : Nat) (m : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec m))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec m)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec m)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvashr [a, b] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => BitVec.sshiftRight' (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Bitvector concatenation denotes `++` on bitvectors. -/
theorem den_bvconcat (ctx : Context) (a b : Term) (rt : TermType) (n : Nat) (m : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec m))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec m)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec m)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvconcat [a, b] rt) = some ⟨(.prim (.bitvec (n + m))), rfl, fun Γ => @HAppend.hAppend (BitVec n) (BitVec m) (BitVec (n + m)) _ (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Signed bitvector `<` denotes `BitVec.slt`. -/
theorem den_bvslt (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvslt [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => BitVec.slt (fa Γ) (fb Γ) = true⟩ := by
  simp [denoteTerm, ha, hb]

/-- Signed bitvector `<=` denotes `BitVec.sle`. -/
theorem den_bvsle (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvsle [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => BitVec.sle (fa Γ) (fb Γ) = true⟩ := by
  simp [denoteTerm, ha, hb]

/-- Unsigned bitvector `<` denotes `LT.lt` on bitvectors. -/
theorem den_bvult (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvult [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => @LT.lt (BitVec n) _ (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Signed bitvector `>=` denotes `BitVec.sle` with operands swapped. -/
theorem den_bvsge (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvsge [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => BitVec.sle (fb Γ) (fa Γ) = true⟩ := by
  simp [denoteTerm, ha, hb]

/-- Signed bitvector `>` denotes `BitVec.slt` with operands swapped. -/
theorem den_bvsgt (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvsgt [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => BitVec.slt (fb Γ) (fa Γ) = true⟩ := by
  simp [denoteTerm, ha, hb]

/-- Unsigned bitvector `<=` denotes `LE.le` on bitvectors. -/
theorem den_bvule (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvule [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => @LE.le (BitVec n) _ (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Unsigned bitvector `>` denotes `GT.gt` on bitvectors. -/
theorem den_bvugt (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvugt [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => @GT.gt (BitVec n) _ (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Unsigned bitvector `>=` denotes `GE.ge` on bitvectors. -/
theorem den_bvuge (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvuge [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => @GE.ge (BitVec n) _ (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Unsigned bitvector division denotes `BitVec.smtUDiv`. -/
theorem den_bvudiv (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvudiv [a, b] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => BitVec.smtUDiv (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Unsigned bitvector remainder denotes `%` on bitvectors. -/
theorem den_bvurem (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvurem [a, b] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => @HMod.hMod (BitVec n) (BitVec n) (BitVec n) _ (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Signed bitvector division denotes `BitVec.smtSDiv`. -/
theorem den_bvsdiv (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvsdiv [a, b] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => BitVec.smtSDiv (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Signed bitvector remainder denotes `BitVec.srem`. -/
theorem den_bvsrem (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvsrem [a, b] rt) = some ⟨(.prim (.bitvec n)), rfl, fun Γ => BitVec.srem (fa Γ) (fb Γ)⟩ := by
  simp [denoteTerm, ha, hb]

/-- Signed add-overflow denotes `BitVec.saddOverflow`. -/
theorem den_bvsaddo (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvsaddo [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => BitVec.saddOverflow (fa Γ) (fb Γ) = true⟩ := by
  simp [denoteTerm, ha, hb]

/-- Signed sub-overflow denotes `BitVec.ssubOverflow`. -/
theorem den_bvssubo (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvssubo [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => BitVec.ssubOverflow (fa Γ) (fb Γ) = true⟩ := by
  simp [denoteTerm, ha, hb]

/-- Signed mul-overflow denotes `BitVec.smulOverflow`. -/
theorem den_bvsmulo (ctx : Context) (a b : Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (h₂ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome)
    (fa : SemFun ctx (.prim (.bitvec n)) h₁) (fb : SemFun ctx (.prim (.bitvec n)) h₂)
    (ha : denoteTerm ctx a = some ⟨(.prim (.bitvec n)), h₁, fa⟩) (hb : denoteTerm ctx b = some ⟨(.prim (.bitvec n)), h₂, fb⟩) :
    denoteTerm ctx (.app .bvsmulo [a, b] rt) = some ⟨(.prim .bool), rfl, fun Γ => BitVec.smulOverflow (fa Γ) (fb Γ) = true⟩ := by
  simp [denoteTerm, ha, hb]

/-- Bitvector `bvadd` denotes a left-fold of addition over its operands. -/
theorem den_bvadd (ctx : Context) (as : List Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (f₁ : SemFun ctx (.prim (.bitvec n)) h₁)
    (rs : List (TermDenoteResult ctx)) (r : TermDenoteResult ctx)
    (has : denoteTerms ctx as = some (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs))
    (hl : leftAssoc ctx (.prim (.bitvec n)) rfl (fun _ => @HAdd.hAdd (BitVec n) (BitVec n) (BitVec n) _)
      (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs) = some r) :
    denoteTerm ctx (.app .bvadd as rt) = some r := by
  simp [denoteTerm, has, hl]

/-- Bitvector `bvsub` denotes a left-fold of subtraction over its operands. -/
theorem den_bvsub (ctx : Context) (as : List Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (f₁ : SemFun ctx (.prim (.bitvec n)) h₁)
    (rs : List (TermDenoteResult ctx)) (r : TermDenoteResult ctx)
    (has : denoteTerms ctx as = some (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs))
    (hl : leftAssoc ctx (.prim (.bitvec n)) rfl (fun _ => @HSub.hSub (BitVec n) (BitVec n) (BitVec n) _)
      (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs) = some r) :
    denoteTerm ctx (.app .bvsub as rt) = some r := by
  simp [denoteTerm, has, hl]

/-- Bitvector `bvmul` denotes a left-fold of multiplication over its operands. -/
theorem den_bvmul (ctx : Context) (as : List Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (f₁ : SemFun ctx (.prim (.bitvec n)) h₁)
    (rs : List (TermDenoteResult ctx)) (r : TermDenoteResult ctx)
    (has : denoteTerms ctx as = some (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs))
    (hl : leftAssoc ctx (.prim (.bitvec n)) rfl (fun _ => @HMul.hMul (BitVec n) (BitVec n) (BitVec n) _)
      (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs) = some r) :
    denoteTerm ctx (.app .bvmul as rt) = some r := by
  simp [denoteTerm, has, hl]

/-- Bitvector `bvand` denotes a left-fold of bitwise-and over its operands. -/
theorem den_bvand (ctx : Context) (as : List Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (f₁ : SemFun ctx (.prim (.bitvec n)) h₁)
    (rs : List (TermDenoteResult ctx)) (r : TermDenoteResult ctx)
    (has : denoteTerms ctx as = some (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs))
    (hl : leftAssoc ctx (.prim (.bitvec n)) rfl (fun _ => @HAnd.hAnd (BitVec n) (BitVec n) (BitVec n) _)
      (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs) = some r) :
    denoteTerm ctx (.app .bvand as rt) = some r := by
  simp [denoteTerm, has, hl]

/-- Bitvector `bvor` denotes a left-fold of bitwise-or over its operands. -/
theorem den_bvor (ctx : Context) (as : List Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (f₁ : SemFun ctx (.prim (.bitvec n)) h₁)
    (rs : List (TermDenoteResult ctx)) (r : TermDenoteResult ctx)
    (has : denoteTerms ctx as = some (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs))
    (hl : leftAssoc ctx (.prim (.bitvec n)) rfl (fun _ => @HOr.hOr (BitVec n) (BitVec n) (BitVec n) _)
      (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs) = some r) :
    denoteTerm ctx (.app .bvor as rt) = some r := by
  simp [denoteTerm, has, hl]

/-- Bitvector `bvxor` denotes a left-fold of bitwise-xor over its operands. -/
theorem den_bvxor (ctx : Context) (as : List Term) (rt : TermType) (n : Nat)
    (h₁ : (denoteSort ctx.sctx (.prim (.bitvec n))).isSome) (f₁ : SemFun ctx (.prim (.bitvec n)) h₁)
    (rs : List (TermDenoteResult ctx)) (r : TermDenoteResult ctx)
    (has : denoteTerms ctx as = some (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs))
    (hl : leftAssoc ctx (.prim (.bitvec n)) rfl (fun _ => @HXor.hXor (BitVec n) (BitVec n) (BitVec n) _)
      (⟨(.prim (.bitvec n)), h₁, f₁⟩ :: rs) = some r) :
    denoteTerm ctx (.app .bvxor as rt) = some r := by
  simp [denoteTerm, has, hl]

/-- A bitvector literal denotes the constant function returning it. -/
theorem den_bitvec (ctx : Context) (n : Nat) (bv : BitVec n) :
    denoteTerm ctx (.prim (.bitvec bv)) = some ⟨.prim (.bitvec n), rfl, fun _ => bv⟩ := by
  simp [denoteTerm]

/-- A string literal denotes the constant function returning it. -/
theorem den_string (ctx : Context) (s : String) :
    denoteTerm ctx (.prim (.string s)) = some ⟨.prim .string, rfl, fun _ => s⟩ := by
  simp [denoteTerm]

/-- String concatenation denotes a left-fold of `++` over its operands. -/
theorem den_str_concat_op (ctx : Context) (rt : TermType) (as : List Term) :
    denoteTerm ctx (.app .str_concat as rt) =
      (denoteTerms ctx as).bind (leftAssoc ctx (.prim .string) rfl (fun _ => @HAppend.hAppend String String String _)) := by
  simp [denoteTerm]

/-- Array `select` denotes `SmtArray.select` of the array and index denotations. -/
theorem den_select (ctx : Context) (x i : Term) (rt kTy vTy : TermType)
    (h : (denoteSort ctx.sctx (.constr "Array" [kTy, vTy])).isSome) (hk : (denoteSort ctx.sctx kTy).isSome)
    (fx : SemFun ctx (.constr "Array" [kTy, vTy]) h) (fi : SemFun ctx kTy hk)
    (hx : denoteTerm ctx x = some ⟨.constr "Array" [kTy, vTy], h, fx⟩)
    (hi : denoteTerm ctx i = some ⟨kTy, hk, fi⟩) :
    denoteTerm ctx (.app .select [x, i] rt) =
      some ⟨vTy, denoteSortArray_isSome_val h, fun Γ => (denoteSortArray_Some ▸ fx Γ).select (fi Γ)⟩ := by
  simp [denoteTerm, hx, hi]

/-- Array `store` denotes `SmtArray.store` of the array, index and value denotations. -/
theorem den_store (ctx : Context) (x i v : Term) (rt kTy vTy : TermType)
    (h : (denoteSort ctx.sctx (.constr "Array" [kTy, vTy])).isSome) (hk : (denoteSort ctx.sctx kTy).isSome)
    (hv : (denoteSort ctx.sctx vTy).isSome)
    (fx : SemFun ctx (.constr "Array" [kTy, vTy]) h) (fi : SemFun ctx kTy hk) (fv : SemFun ctx vTy hv)
    (hx : denoteTerm ctx x = some ⟨.constr "Array" [kTy, vTy], h, fx⟩)
    (hi : denoteTerm ctx i = some ⟨kTy, hk, fi⟩) (hv' : denoteTerm ctx v = some ⟨vTy, hv, fv⟩) :
    denoteTerm ctx (.app .store [x, i, v] rt) =
      some ⟨.constr "Array" [kTy, vTy], h, fun Γ => denoteSortArray_Some ▸
        @SmtArray.store _ _ (Classical.typeDecidableEq _) (denoteSortArray_Some ▸ fx Γ) (fi Γ) (fv Γ)⟩ := by
  simp [denoteTerm, hx, hi, hv']

/-- `none` of type `ty` denotes the `none` of the option sort. -/
theorem den_none (ctx : Context) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome) :
    denoteTerm ctx (.none ty) =
      some ⟨.option ty, isSome_denoteSortOption h, fun _ => denoteSortOption_Some ▸ none⟩ := by
  simp [denoteTerm, h]

/-- `some a` denotes the `some` of the argument's denotation in the option sort. -/
theorem den_some (ctx : Context) (a : Term) (ty : TermType) (h : (denoteSort ctx.sctx ty).isSome)
    (fa : SemFun ctx ty h) (ha : denoteTerm ctx a = some ⟨ty, h, fa⟩) :
    denoteTerm ctx (.some a) =
      some ⟨.option ty, isSome_denoteSortOption h, fun Γ => denoteSortOption_Some ▸ some (fa Γ)⟩ := by
  simp [denoteTerm, ha]

/-! ### Variables and uninterpreted functions -/

/-- A variable denotes the value looked up at its context index in the environment. -/
theorem den_var (ctx : Context) (v : TermVar) (i : Nat) (hTy : (denoteSort ctx.sctx v.ty).isSome)
    (hi : ctx.tctx.vs.findIdx? (· == v) = some i) :
    denoteTerm ctx (.var v) = some ⟨v.ty, hTy, fun tdi => lookupVar (h := hTy) hi tdi⟩ := by
  obtain ⟨n, ty⟩ := v
  simp only [denoteTerm, hTy, ↓reduceDIte]
  split
  · next i' hi' =>
    have : i = i' := Option.some.inj (hi.symm.trans hi')
    subst this
    rfl
  · next hn => simp_all

/-- Applying a UF to aligned arguments equals the length-indexed `applyUFAux` application. -/
theorem applyUF_eq (ctx : Context) (args : List TermType) (out : TermType)
    (h : (denoteFunSort ctx.sctx args out).isSome) (tdi : TermDenoteInput ctx)
    (uf : (denoteFunSort ctx.sctx args out).get h ⟨tdi.sΓ, tdi.hsΓ⟩)
    (as : List (TermDenoteResult ctx)) (hal : argTypesAlign as args) :
    applyUF tdi uf as hal =
      applyUFAux tdi uf as (argTypesAlign_length_eq hal).symm (argTypesAlign_arg_types hal) := by
  simp [applyUF]

/-- Applying a nullary UF returns its realization unchanged. -/
theorem applyUFAux_nil (ctx : Context) (out : TermType)
    (h : (denoteFunSort ctx.sctx [] out).isSome) (tdi : TermDenoteInput ctx)
    (uf : (denoteFunSort ctx.sctx [] out).get h ⟨tdi.sΓ, tdi.hsΓ⟩) hl has :
    applyUFAux tdi uf [] hl has = uf := by
  simp [applyUFAux] <;> rfl

/-- Applying a UF to a non-empty argument list feeds the head's denotation and recurses on the tail. -/
theorem applyUFAux_cons (ctx : Context) (arg : TermType) (args : List TermType) (out : TermType)
    (h : (denoteFunSort ctx.sctx (arg :: args) out).isSome) (tdi : TermDenoteInput ctx)
    (uf : (denoteFunSort ctx.sctx (arg :: args) out).get h ⟨tdi.sΓ, tdi.hsΓ⟩)
    (a : TermDenoteResult ctx) (as : List (TermDenoteResult ctx)) hl has :
    applyUFAux tdi uf (a :: as) hl has =
      have ha : denoteSort ctx.sctx arg = denoteSort ctx.sctx a.ty := has 0 (Nat.zero_lt_succ _) ▸ rfl
      applyUFAux tdi ((arrow_of_denoteFunSortCons_isSome h ▸ uf) (Option.get_congr ha ▸ a.res tdi)) as
        (Nat.succ.inj hl) (fun i hi => (has (i + 1) (Nat.succ_lt_succ hi))) := by
  simp [applyUFAux]

/-- A UF application denotes the realization found at the UF's context index, applied to the argument denotations. -/
theorem den_uf (ctx : Context) (uf : UF) (as : List Term) (ty : TermType) (i : Nat)
    (hTys : (denoteFunSort ctx.sctx uf.args uf.out).isSome)
    (hi : ctx.tctx.ufs.findIdx? (· == uf) = some i)
    (rs : List (TermDenoteResult ctx)) (hal : argTypesAlign rs uf.args = true)
    (F : SemFun ctx uf.out (denoteSortOut_isSome_of_denoteFunSort_isSome hTys))
    (has : denoteTerms ctx as = some rs)
    (hF : ∀ tdi, applyUF tdi (lookupUF (h := hTys) hi tdi) rs hal = F tdi) :
    denoteTerm ctx (.app (.uf uf) as ty) =
      some ⟨uf.out, denoteSortOut_isSome_of_denoteFunSort_isSome hTys, F⟩ := by
  have hF' := funext hF
  subst hF'
  simp only [denoteTerm, hTys, ↓reduceDIte]
  split
  · next i' hi' =>
    have : i = i' := Option.some.inj (hi.symm.trans hi')
    subst this
    simp [has, hal]
  · next hn => simp_all

/-! ### Quantifiers -/

/-- Reassociate the quantifier-variable context: `(v :: vs).reverse ++ Γ = vs.reverse ++ (v :: Γ)`. -/
theorem quant_vs_eq (ctx : Context) (v : TermVar) (vs : List TermVar) :
    (v :: vs).reverse ++ ctx.tctx.vs = vs.reverse ++ (v :: ctx.tctx.vs) := by simp

/-- Building a universal over no variables returns the body predicate unchanged. -/
theorem buildForall_nil (ctx : Context)
    (hTys : (denoteFunSort ctx.sctx (List.map TermVar.ty []) (.prim .bool)).isSome)
    (fb : TermDenoteInput ⟨ctx.sctx, ⟨([] : List TermVar).reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop) :
    buildForall ctx [] hTys fb = fb := by
  funext tdi; simp [buildForall, buildQuant]

/-- Building a universal over `v :: vs` quantifies `v`'s realization around the rest. -/
theorem buildForall_cons (ctx : Context) (v : TermVar) (vs : List TermVar)
    (hTys : (denoteFunSort ctx.sctx ((v :: vs).map (·.ty)) (.prim .bool)).isSome)
    (fb : TermDenoteInput ⟨ctx.sctx, ⟨(v :: vs).reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop)
    (G : TermDenoteInput ⟨ctx.sctx, ⟨v :: ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop)
    (hrest : buildForall ⟨ctx.sctx, ⟨v :: ctx.tctx.vs, ctx.tctx.ufs⟩⟩ vs
      (denoteFunSortCons_isSome hTys).right (quant_vs_eq ctx v vs ▸ fb) = G) :
    buildForall ctx (v :: vs) hTys fb =
      fun tdi => ∀ x, G (pushVar tdi v (denoteFunSortCons_isSome hTys).left x) := by
  subst hrest
  funext tdi
  simp [buildForall, buildQuant]

/-- Building an existential over no variables returns the body predicate unchanged. -/
theorem buildExists_nil (ctx : Context)
    (hTys : (denoteFunSort ctx.sctx (List.map TermVar.ty []) (.prim .bool)).isSome)
    (fb : TermDenoteInput ⟨ctx.sctx, ⟨([] : List TermVar).reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop) :
    buildExists ctx [] hTys fb = fb := by
  funext tdi; simp [buildExists, buildQuant]

/-- Building an existential over `v :: vs` quantifies `v`'s realization around the rest. -/
theorem buildExists_cons (ctx : Context) (v : TermVar) (vs : List TermVar)
    (hTys : (denoteFunSort ctx.sctx ((v :: vs).map (·.ty)) (.prim .bool)).isSome)
    (fb : TermDenoteInput ⟨ctx.sctx, ⟨(v :: vs).reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop)
    (G : TermDenoteInput ⟨ctx.sctx, ⟨v :: ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop)
    (hrest : buildExists ⟨ctx.sctx, ⟨v :: ctx.tctx.vs, ctx.tctx.ufs⟩⟩ vs
      (denoteFunSortCons_isSome hTys).right (quant_vs_eq ctx v vs ▸ fb) = G) :
    buildExists ctx (v :: vs) hTys fb =
      fun tdi => ∃ x, G (pushVar tdi v (denoteFunSortCons_isSome hTys).left x) := by
  subst hrest
  funext tdi
  simp [buildExists, buildQuant]

/-- A universally quantified term denotes `buildForall` over its body's denotation. -/
theorem den_forall (ctx : Context) (vs : List TermVar) (tr : List (List Term)) (b : Term)
    (hTys : (denoteFunSort ctx.sctx (vs.map (·.ty)) (.prim .bool)).isSome)
    (h : (denoteSort ctx.sctx (.prim .bool)).isSome)
    (fb : TermDenoteInput ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop)
    (F : TermDenoteInput ctx → Prop)
    (hb : denoteTerm ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ b = some ⟨.prim .bool, h, fb⟩)
    (hF : buildForall ctx vs hTys fb = F) :
    denoteTerm ctx (.quant .all vs tr b) = some ⟨.prim .bool, rfl, F⟩ := by
  subst hF
  simp [denoteTerm, hTys, hb]

/-- An existentially quantified term denotes `buildExists` over its body's denotation. -/
theorem den_exists (ctx : Context) (vs : List TermVar) (tr : List (List Term)) (b : Term)
    (hTys : (denoteFunSort ctx.sctx (vs.map (·.ty)) (.prim .bool)).isSome)
    (h : (denoteSort ctx.sctx (.prim .bool)).isSome)
    (fb : TermDenoteInput ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ → Prop)
    (F : TermDenoteInput ctx → Prop)
    (hb : denoteTerm ⟨ctx.sctx, ⟨vs.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ b = some ⟨.prim .bool, h, fb⟩)
    (hF : buildExists ctx vs hTys fb = F) :
    denoteTerm ctx (.quant .exist vs tr b) = some ⟨.prim .bool, rfl, F⟩ := by
  subst hF
  simp [denoteTerm, hTys, hb]

/-! ## Side conditions

Derived `DecidableEq` instances are not exposed, so importers cannot evaluate
`==` on `UF`, `TermVar` or `TermType` by reduction. These lemmas discharge the
lookups performed by `denoteTerm` using only `String` comparisons on names and
syntactic equality of literals.
-/

/-- A UF equal to the head is found at index 0. -/
theorem findIdx_uf_head (x : UF) (rest : List UF) (uf : UF) (h : x = uf) :
    (x :: rest).findIdx? (· == uf) = some 0 := by
  subst h; simp [List.findIdx?_cons]

/-- Skip a UF with a different name: the lookup index shifts by one into the tail. -/
theorem findIdx_uf_tail (x : UF) (rest : List UF) (uf : UF) (i : Nat)
    (h : decide (x.id = uf.id) = false) (hr : rest.findIdx? (· == uf) = some i) :
    (x :: rest).findIdx? (· == uf) = some (i + 1) := by
  have hne : (x == uf) = false := by
    have h' : x.id ≠ uf.id := of_decide_eq_false h
    exact beq_false_of_ne (fun hx => h' (hx ▸ rfl))
  simp [List.findIdx?_cons, hne, hr]

/-- Skip a UF with the same name but a different signature. -/
theorem findIdx_uf_tail_sig (x : UF) (rest : List UF) (uf : UF) (i : Nat)
    (h : (TermType.beq.go x.args uf.args && TermType.beq x.out uf.out) = false)
    (hr : rest.findIdx? (· == uf) = some i) :
    (x :: rest).findIdx? (· == uf) = some (i + 1) := by
  have hne : (x == uf) = false := by
    refine beq_false_of_ne fun hx => ?_
    subst hx
    have hgo : ∀ ts : List TermType, TermType.beq.go ts ts = true := by
      intro ts; induction ts <;> simp_all [TermType.beq.go]
    simp [hgo, TermType.beq_refl] at h
  simp [List.findIdx?_cons, hne, hr]

/-- A variable equal to the head is found at index 0. -/
theorem findIdx_var_head (x : TermVar) (rest : List TermVar) (v : TermVar) (h : x = v) :
    (x :: rest).findIdx? (· == v) = some 0 := by
  subst h; simp [List.findIdx?_cons]

/-- Skip a variable with a different name: the lookup index shifts by one into the tail. -/
theorem findIdx_var_tail (x : TermVar) (rest : List TermVar) (v : TermVar) (i : Nat)
    (h : decide (x.id = v.id) = false) (hr : rest.findIdx? (· == v) = some i) :
    (x :: rest).findIdx? (· == v) = some (i + 1) := by
  have hne : (x == v) = false := by
    have h' : x.id ≠ v.id := of_decide_eq_false h
    exact beq_false_of_ne (fun hx => h' (hx ▸ rfl))
  simp [List.findIdx?_cons, hne, hr]

/-- Skip a variable with the same name but a different type. -/
theorem findIdx_var_tail_ty (x : TermVar) (rest : List TermVar) (v : TermVar) (i : Nat)
    (h : TermType.beq x.ty v.ty = false) (hr : rest.findIdx? (· == v) = some i) :
    (x :: rest).findIdx? (· == v) = some (i + 1) := by
  have hne : (x == v) = false := by
    refine beq_false_of_ne fun hx => ?_
    subst hx
    simp [TermType.beq_refl] at h
  simp [List.findIdx?_cons, hne, hr]

/-- Empty arguments align with the empty parameter-type list. -/
theorem argTypesAlign_nil (ctx : Context) :
    argTypesAlign ([] : List (TermDenoteResult ctx)) [] = true := by
  simp [argTypesAlign]

/-- Arguments align with a cons when the head types match and the tails align. -/
theorem argTypesAlign_cons (ctx : Context) (a : TermDenoteResult ctx) (as : List (TermDenoteResult ctx))
    (v : TermType) (vs : List TermType) (h : a.ty = v) (hr : argTypesAlign as vs = true) :
    argTypesAlign (a :: as) (v :: vs) = true := by
  simp [argTypesAlign, h, hr]

/-! ## Interpreted functions -/

/-- Closing over `iF :: ifs` binds `iF` then closes over the rest. -/
theorem bindIFs_cons (sctx : SortContext) (vs : TermVarContext) (ufs : UFContext) (iF : IF)
    (ifs : List IF) (ft : TermDenoteInput ⟨sctx, ⟨vs, (iF :: ifs).map IF.toUF ++ ufs⟩⟩ → Prop)
    (ft' : TermDenoteInput ⟨sctx, ⟨vs, ifs.map IF.toUF ++ ufs⟩⟩ → Prop)
    (ft'' : TermDenoteInput ⟨sctx, ⟨vs, ufs⟩⟩ → Prop)
    (h₁ : bindIF iF ⟨sctx, ⟨vs, ifs.map IF.toUF ++ ufs⟩⟩ ft = some ft')
    (h₂ : denoteBoolTermFromContext.bindIFs sctx vs ufs ifs ft' = some ft'') :
    denoteBoolTermFromContext.bindIFs sctx vs ufs (iF :: ifs) ft = some ft'' := by
  simp only [denoteBoolTermFromContext.bindIFs]
  rw [h₁]
  exact h₂

/-- The body of a nullary interpreted function is the body denotation itself. -/
theorem buildIFBody_nil (ctx : Context) (out : TermType)
    (hTys : (denoteFunSort ctx.sctx (List.map TermVar.ty []) out).isSome)
    (hTy : (denoteSort ctx.sctx out).isSome)
    (bodyFt : (tdi : TermDenoteInput ⟨ctx.sctx, ⟨([] : List TermVar).reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩) →
      (denoteSort ctx.sctx out).get hTy ⟨tdi.sΓ, tdi.hsΓ⟩)
    (tdi : TermDenoteInput ctx) :
    buildIFBody ctx [] (hTys := hTys) (hTy := hTy) bodyFt tdi = bodyFt tdi := by
  simp [buildIFBody] <;> rfl

/-- The body of an interpreted function over `v :: vs` lambda-abstracts `v`'s realization. -/
theorem buildIFBody_cons (ctx : Context) (v : TermVar) (vs : List TermVar) (out : TermType)
    (hTys : (denoteFunSort ctx.sctx ((v :: vs).map (·.ty)) out).isSome)
    (hTy : (denoteSort ctx.sctx out).isSome)
    (bodyFt : (tdi : TermDenoteInput ⟨ctx.sctx, ⟨(v :: vs).reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩) →
      (denoteSort ctx.sctx out).get hTy ⟨tdi.sΓ, tdi.hsΓ⟩)
    (G : (tdi : TermDenoteInput ⟨ctx.sctx, ⟨v :: ctx.tctx.vs, ctx.tctx.ufs⟩⟩) →
      (denoteFunSort ctx.sctx (vs.map (·.ty)) out).get (denoteFunSortCons_isSome hTys).right
        ⟨tdi.sΓ, tdi.hsΓ⟩)
    (hrest : ∀ tdi, buildIFBody ⟨ctx.sctx, ⟨v :: ctx.tctx.vs, ctx.tctx.ufs⟩⟩ vs
      (hTys := (denoteFunSortCons_isSome hTys).right) (hTy := hTy) (quant_vs_eq ctx v vs ▸ bodyFt) tdi
        = G tdi)
    (tdi : TermDenoteInput ctx) :
    buildIFBody ctx (v :: vs) (hTys := hTys) (hTy := hTy) bodyFt tdi =
      (arrow_of_denoteFunSortCons_isSome hTys ▸
        fun x => G (pushVar tdi v (denoteFunSortCons_isSome hTys).left x)) := by
  have hG := funext hrest
  subst hG
  simp [buildIFBody, bindIFVar] <;> rfl

/-- Binding an interpreted function closes the predicate over the realization built from its body. -/
theorem bindIF_eq (iF : IF) (ctx : Context)
    (ft' : TermDenoteInput ⟨ctx.sctx, ⟨ctx.tctx.vs, iF.toUF :: ctx.tctx.ufs⟩⟩ → Prop)
    (hTys : (denoteFunSort ctx.sctx iF.toUF.args iF.toUF.out).isSome)
    (h : (denoteSort ctx.sctx iF.out).isSome)
    (bodyFt : (tdi : TermDenoteInput ⟨ctx.sctx, ⟨iF.args.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩) →
      (denoteSort ctx.sctx iF.out).get h ⟨tdi.sΓ, tdi.hsΓ⟩)
    (F : (tdi : TermDenoteInput ctx) →
      (denoteFunSort ctx.sctx iF.toUF.args iF.toUF.out).get hTys ⟨tdi.sΓ, tdi.hsΓ⟩)
    (hb : denoteTerm ⟨ctx.sctx, ⟨iF.args.reverse ++ ctx.tctx.vs, ctx.tctx.ufs⟩⟩ iF.body =
      some ⟨iF.out, h, bodyFt⟩)
    (hF : ∀ tdi, buildIFBody ctx iF.args (hTys := hTys)
      (hTy := denoteSortOut_isSome_of_denoteFunSort_isSome hTys) bodyFt tdi = F tdi) :
    bindIF iF ctx ft' = some (fun tdi => ft' (pushUF tdi iF.toUF hTys (F tdi))) := by
  have hF' := funext hF
  subst hF'
  simp only [bindIF, hTys, ↓reduceDIte]
  erw [hb]
  simp
  rfl

end Strata.SMT.DenoteProps

end
