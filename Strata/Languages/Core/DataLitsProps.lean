/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.DataLits
public import Strata.DL.Lambda.Denote.LExprDenote
public import Strata.DL.Lambda.FactoryWF
import all Strata.Languages.Core.DataLits
import all Strata.DL.Lambda.LConstData
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LConstDataProps
import Strata.DL.Lambda.Denote.LExprDenoteConsts
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.LTyProps
import Strata.Util.ListMapProps
import all Strata.DL.Lambda.Denote.Assumptions
public import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent

/-! # Models and well-formedness of the factory extended to datatype values

`extendDataLits F` (`Strata.Languages.Core.DataLits`) wraps the `Map` and `Sequence` evaluators
of `F` so that they compute on datatype values. The wrapped evaluators keep denotations in every
interpretation whose constructors are disjoint and injective (`ConstrInterpConsistent`): an
argument passed as the constant it stands for denotes what it denotes, and a result transformed
by `dataLitsPost` keeps its type and denotation. So the models of `F` and of `extendDataLits F`
are the same interpretations. The extension keeps a well-formed factory well-formed, and keeps the
conditions under which evaluation preserves denotation (`Factory.EvalSoundWF`).

Key theorems: `dataLitsResult_denote`, `dataLitsPost_denote`, `dataLitsPost_hasTypeA`,
`interpConsistentEval_dataLitsEval`, `dataLitsFunc_wf`, `extendDataLits_wf`,
`extendDataLits_evalSoundWF`.
Key definitions: `Interp.extendDataLits`, `Interp.ofExtendDataLits`. -/

namespace Core
open Lambda

public section

variable {F : @Lambda.Factory CoreLParams} {tc : TyConstrInterp} {op : OpInterp tc}

/-! ## Denotations of the transformed arguments and results -/

/-- The value of a constant at the sort of the type of a constant expression holding it is the
    expression's denotation. -/
private theorem constVal_denote {m : CoreExprMetadata} {c : LConst} {τ : LMonoTy}
    (h : LExpr.HasTypeA [] (.const m c : LExpr CoreLParams.mono) τ) (fv : FreeVarVal CoreLParams tc)
    (vt : TyVarVal) :
    constVal tc op (τ.substTyVars vt) c =
      some (LExpr.denote tc op fv vt .nil (.const m c) τ h) := by
  obtain rfl := HasTypeA.const_inv h
  exact constVal_denoteConst vt (HasTypeA.const_wt h)

/-- The arguments passed as the constants they stand for (`dataLitsArg`) keep their types and
    denotations. -/
private theorem dataLitsArg_denote : ∀ {args : List (LExpr CoreLParams.mono)} {tys : List LMonoTy}
    (h : List.Rel₂ (LExpr.HasTypeA []) args tys),
    ∃ h' : List.Rel₂ (LExpr.HasTypeA []) (args.map (dataLitsArg F)) tys,
      ∀ (fv : FreeVarVal CoreLParams tc) vt,
        denoteArgs tc op fv vt .nil (args.map (dataLitsArg F)) tys h' =
          denoteArgs tc op fv vt .nil args tys h
  | [], [], .nil => ⟨.nil, fun _ _ => rfl⟩
  | a :: args, ty :: tys, .cons ha hs => by
    obtain ⟨hs', hd⟩ := dataLitsArg_denote hs
    obtain ⟨ha', hda⟩ : ∃ ha' : LExpr.HasTypeA [] (dataLitsArg F a) ty,
        ∀ (fv : FreeVarVal CoreLParams tc) vt,
          LExpr.denote tc op fv vt .nil (dataLitsArg F a) ty ha' =
          LExpr.denote tc op fv vt .nil a ty ha := by
      unfold dataLitsArg
      split
      · rename_i c hc
        obtain ⟨hw, hty, hden⟩ := LExpr.toConst?_sound hc ha
        have hc' : LExpr.HasTypeA [] (.const a.metadata c : LExpr CoreLParams.mono) ty :=
          hty ▸ .const hw
        exact ⟨hc', fun fv vt => hden tc op fv vt _ hc'⟩
      · exact ⟨ha, fun _ _ => rfl⟩
    refine ⟨.cons ha' hs', fun fv vt => ?_⟩
    show HList.cons _ _ = HList.cons _ _
    rw [hda fv vt, hd fv vt]

/-- `dataLitsConst` keeps the type and denotation of a constant expression. -/
private theorem dataLitsConst_denote {m : CoreExprMetadata} {c : LConst} {τ : LMonoTy}
    (h : LExpr.HasTypeA [] (.const m c : LExpr CoreLParams.mono) τ) (fv : FreeVarVal CoreLParams tc)
    (vt : TyVarVal) :
    ∃ h' : LExpr.HasTypeA [] (dataLitsConst F m c) τ,
      LExpr.denote tc op fv vt .nil (dataLitsConst F m c) τ h' =
        LExpr.denote tc op fv vt .nil (.const m c) τ h := by
  unfold dataLitsConst
  split
  · split
    · obtain rfl := HasTypeA.const_inv h
      exact LConst.denote_toLExpr tc op fv vt m _ (HasTypeA.const_wt h)
    · exact ⟨h, rfl⟩
  · exact ⟨h, rfl⟩

open Classical in
/-- Dropping the entries whose keys `LConst.eqlIn F` decides equal to the key `a` leaves the
    values of a map at every key other than the value of `a` unchanged, in an interpretation
    consistent with the constructors of `F`. -/
private theorem constValEntries_filter_eqlIn (hF : ConstrInterpConsistent tc op F) {k v : LSort}
    {a : LConst} {xa : SortDenote tc k} (ha : constVal tc op k a = some xa) (dv : SortDenote tc v) :
    ∀ {es : List (LConst × LConst)} {kvs : List (SortDenote tc k × SortDenote tc v)},
      constValEntries tc op k v es = some kvs →
      ∃ kvs', constValEntries tc op k v (es.filter fun e => LConst.eqlIn F a e.1 != some true) =
        some kvs' ∧ ∀ z, z ≠ xa → SortDenote.mapOf dv kvs' z = SortDenote.mapOf dv kvs z
  | [], kvs, h => by
    simp only [constValEntries, Option.some.injEq] at h; subst h
    exact ⟨[], rfl, fun _ _ => rfl⟩
  | (c, e) :: es, kvs, h => by
    simp only [constValEntries] at h
    split at h
    · rename_i xc xe r hc he hr
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨r', hr', hz⟩ := constValEntries_filter_eqlIn hF ha dv hr
      by_cases hq : LConst.eqlIn F a c = some true
      · obtain rfl : xa = xc := (LConst.eqlIn_sound hF a c ha hc hq).2 rfl
        refine ⟨r', by simpa [List.filter_cons, hq] using hr', fun z hne => ?_⟩
        simp only [SortDenote.mapOf_cons, Ne.symm hne, ↓reduceIte, hz z hne]
      · refine ⟨(xc, xe) :: r', by simp [hq, constValEntries, hc, he, hr'],
          fun z hne => ?_⟩
        rw [SortDenote.mapOf_cons, SortDenote.mapOf_cons, hz z hne]
    · cases h

/-- The entries of a map literal well typed at key sort `k` and value sort `v` stay well typed
    after filtering. -/
private theorem wtEntries_filter {k v : LSort} (p : LConst × LConst → Bool) :
    ∀ {es : List (LConst × LConst)}, LConst.wtEntries k v es = true →
      LConst.wtEntries k v (es.filter p) = true
  | [], _ => rfl
  | (a, b) :: es, h => by
    simp only [LConst.wtEntries, Bool.and_eq_true] at h
    rw [List.filter_cons]
    split
    · simp only [LConst.wtEntries, Bool.and_eq_true]
      exact ⟨h.1, wtEntries_filter p h.2⟩
    · exact wtEntries_filter p h.2

open Classical in
/-- A map literal with the entries `dedupeFront F` keeps has the value of the literal, in an
    interpretation consistent with the constructors of `F`. -/
private theorem constVal_dedupeFront (hF : ConstrInterpConsistent tc op F) {s k v : LSort}
    {d : LConst} {es : List (LConst × LConst)} {x : SortDenote tc s}
    (h : constVal tc op s (.mapConst k v d ⟨es⟩) = some x) :
    constVal tc op s (.mapConst k v d ⟨dedupeFront F es⟩) = some x := by
  obtain rfl : LSort.map k v = s := constVal_sort h
  rw [constVal_mapConst] at h ⊢
  split at h
  · rename_i dv kvs hd hkvs
    obtain ⟨kvs', hkvs', heq⟩ : ∃ kvs', constValEntries tc op k v (dedupeFront F es) = some kvs' ∧
        SortDenote.mapOf dv kvs' = SortDenote.mapOf dv kvs := by
      match es, hkvs with
      | [], hkvs => exact ⟨kvs, hkvs, rfl⟩
      | (a, b) :: es, hkvs =>
        simp only [constValEntries] at hkvs
        split at hkvs
        · rename_i xa xb r ha hb hr
          simp only [Option.some.injEq] at hkvs; subst hkvs
          obtain ⟨r', hr', hz⟩ := constValEntries_filter_eqlIn hF ha dv hr
          refine ⟨(xa, xb) :: r', by simp [dedupeFront, constValEntries, ha, hb, hr'], ?_⟩
          funext z
          rw [SortDenote.mapOf_cons, SortDenote.mapOf_cons]
          by_cases hxz : xa = z
          · simp [hxz]
          · simp only [hxz, ↓reduceIte, hz z (Ne.symm hxz)]
        · cases hkvs
    rw [hd, hkvs']
    exact (congrArg some heq).trans h
  · cases h

/-- The branch `decideChain F` selects in an `ite` chain has the chain's type and denotation, in
    an interpretation consistent with the constructors of `F`. -/
private theorem decideChain_denote (hF : ConstrInterpConsistent tc op F)
    (e : LExpr CoreLParams.mono) :
    ∀ {r : LExpr CoreLParams.mono}, decideChain F e = some r → ∀ {τ : LMonoTy}
      (h : LExpr.HasTypeA [] e τ) (fv : FreeVarVal CoreLParams tc) (vt : TyVarVal),
      ∃ h' : LExpr.HasTypeA [] r τ,
        LExpr.denote tc op fv vt .nil r τ h' = LExpr.denote tc op fv vt .nil e τ h := by
  fun_induction decideChain F e with
  | case1 m m' mk key mk' k t f hq ih | case2 m m' mk key mk' k t f hq ih =>
    intro r hr τ h fv vt
    obtain ⟨hc, ht, hf⟩ := HasTypeA.ite_inv h
    obtain ⟨h', hd⟩ := ih hr (by assumption) fv vt
    refine ⟨h', hd.trans ?_⟩
    rw [denote_ite .nil hc ht hf h]
    cases hc with
    | eq hkey hk =>
      have hiff :=
        LConst.eqlIn_sound hF key k (constVal_denote hkey fv vt) (constVal_denote hk fv vt) hq
      first
        | rw [denote_eq_true .nil hkey hk _ (hiff.2 rfl)]; rfl
        | rw [denote_eq_false .nil hkey hk _ (fun he => nomatch hiff.1 he)]; rfl
  | case3 => intro _ h; cases h
  | case4 m c =>
    intro r hr τ h fv vt
    cases hr
    exact dataLitsConst_denote h fv vt
  | case5 => intro _ h; cases h

/-- `dedupeFront F` keeps the type of a map literal. -/
private theorem hasTypeA_dedupeFront {m : CoreExprMetadata} {k v : LSort} {d : LConst}
    {es : List (LConst × LConst)} {τ : LMonoTy}
    (h : LExpr.HasTypeA [] (.const m (.mapConst k v d ⟨es⟩) : LExpr CoreLParams.mono) τ) :
    LExpr.HasTypeA [] (.const m (.mapConst k v d ⟨dedupeFront F es⟩) :
      LExpr CoreLParams.mono) τ := by
  have hw := HasTypeA.const_wt h
  have hw' : (LConst.mapConst k v d ⟨dedupeFront F es⟩).wt = true := by
    simp only [LConst.wt, Bool.and_eq_true] at hw ⊢
    refine ⟨hw.1, ?_⟩
    cases es with
    | nil => exact hw.2
    | cons p es =>
      simp only [dedupeFront, LConst.wtEntries, Bool.and_eq_true] at hw ⊢
      exact ⟨hw.2.1, wtEntries_filter _ hw.2.2⟩
  have hty : (LConst.mapConst k v d ⟨dedupeFront F es⟩).ty = τ := by
    rw [HasTypeA.const_inv h, LConst.ty_of_wt hw', LConst.ty_of_wt hw]; rfl
  exact hty ▸ .const hw'

/-- **The transformed result keeps its type and denotation.** In an interpretation consistent
    with the constructors of `F`, `dataLitsResult F upd r` has every type `r` has, and there the
    denotation of `r`. -/
theorem dataLitsResult_denote (hF : ConstrInterpConsistent tc op F) (upd : Bool)
    {r : LExpr CoreLParams.mono} {τ : LMonoTy} (h : LExpr.HasTypeA [] r τ)
    (fv : FreeVarVal CoreLParams tc) (vt : TyVarVal) :
    ∃ h' : LExpr.HasTypeA [] (dataLitsResult F upd r) τ,
      LExpr.denote tc op fv vt .nil (dataLitsResult F upd r) τ h' =
        LExpr.denote tc op fv vt .nil r τ h := by
  have hite : ∀ {e : LExpr CoreLParams.mono} (h : LExpr.HasTypeA [] e τ),
      ∃ h' : LExpr.HasTypeA [] ((decideChain F e).getD e) τ,
        LExpr.denote tc op fv vt .nil ((decideChain F e).getD e) τ h' =
          LExpr.denote tc op fv vt .nil e τ h := by
    intro e h
    cases hd : decideChain F e with
    | none => exact ⟨h, rfl⟩
    | some r' => exact decideChain_denote hF e hd h fv vt
  unfold dataLitsResult
  split
  · rename_i m k v d es
    split
    · have h' := hasTypeA_dedupeFront (F := F) h
      exact ⟨h', Option.some.inj ((constVal_denote h' fv vt).symm.trans
        (constVal_dedupeFront hF (constVal_denote h fv vt)))⟩
    · exact ⟨h, rfl⟩
  · exact dataLitsConst_denote h fv vt
  · exact hite h
  · exact ⟨h, rfl⟩

/-- **`dataLitsPost` keeps the type and denotation of a result**, in an interpretation consistent
    with the constructors of `F`. -/
theorem dataLitsPost_denote (hF : ConstrInterpConsistent tc op F) (upd : Bool)
    (ty : Option LMonoTy) (n : Nat) {r : LExpr CoreLParams.mono} {τ : LMonoTy}
    (h : LExpr.HasTypeA [] r τ) (fv : FreeVarVal CoreLParams tc) (vt : TyVarVal) :
    ∃ h' : LExpr.HasTypeA [] (dataLitsPost F upd ty n r) τ,
      LExpr.denote tc op fv vt .nil (dataLitsPost F upd ty n r) τ h' =
        LExpr.denote tc op fv vt .nil r τ h := by
  unfold dataLitsPost
  split
  · exact dataLitsResult_denote hF upd h fv vt
  · exact ⟨h, rfl⟩

/-- A result whose image under `dataLitsPost` has the result type `τ` of the annotation `ty`
    after `n` arguments has type `τ`. -/
private theorem hasTypeA_of_dataLitsPost {upd : Bool} {ty : LMonoTy} {n : Nat}
    {r : LExpr CoreLParams.mono} {τ : LMonoTy} (hτ : ty.arrowResult n = τ)
    (h : LExpr.HasTypeA [] (dataLitsPost F upd (some ty) n r) τ) : LExpr.HasTypeA [] r τ := by
  unfold dataLitsPost at h
  split at h
  · rename_i hg
    simp only [Option.isSome_some, Option.map_some, Bool.true_and, beq_iff_eq] at hg
    exact hτ ▸ LExpr.typeCheck_to_HasTypeA hg
  · exact h

/-- The result type of the instantiated type of a function after its inputs is its instantiated
    output type. -/
private theorem arrowResult_instTy (f : LFunc CoreLParams) (S : Subst) :
    (f.instTy S).arrowResult f.inputs.length = LMonoTy.subst S f.output := by
  have h := LMonoTy.arrowResult_mkArrow' (LMonoTy.subst S f.output)
    ((f.inputs.map Prod.snd).map (LMonoTy.subst S))
  have hl : ((f.inputs.map Prod.snd).map (LMonoTy.subst S)).length = f.inputs.length :=
    (List.length_map ..).trans (List.length_map ..)
  exact hl ▸ h

/-- **The evaluator extended to datatype values is consistent** with every interpretation
    consistent with the original evaluator and with the constructors of `F`. -/
theorem interpConsistentEval_dataLitsEval (hF : ConstrInterpConsistent tc op F) (upd : Bool)
    {f : LFunc CoreLParams} {ce : ConcreteEval CoreLParams}
    (h : LFunc.InterpConsistentEval tc op f ce) :
    LFunc.InterpConsistentEval tc op f (dataLitsEval F upd f.inputs.length ce) := by
  intro vt fv md S args r' _ _ hr _ _ _ h_args h_res
  obtain ⟨r, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
  have hr := hasTypeA_of_dataLitsPost (arrowResult_instTy f S) h_res
  obtain ⟨h', hd⟩ := dataLitsPost_denote hF upd _ _ hr fv vt
  refine hd.trans ?_
  cases hc : ce md (some (f.instTy S)) args with
  | some r0 =>
    simp only [hc, Option.orElse_some, Option.some.injEq] at hr0
    subst hr0
    exact h vt fv md S args _ hc h_args hr
  | none =>
    simp only [hc, Option.orElse_none] at hr0
    obtain ⟨h_args', hda⟩ := dataLitsArg_denote (F := F) (tc := tc) (op := op) h_args
    rw [h vt fv md S _ _ hr0 h_args' hr, hda fv vt]

/-! ### Types of the transformed arguments and results -/

/-- The interpretation of every type constructor by `Unit`. -/
private def unitTc : TyConstrInterp := fun _ _ => Unit

/-- An interpretation of every name, at every sort, by a value of that sort under `unitTc`. -/
private def unitVal : IdentInterp CoreLParams unitTc :=
  fun _ s => (SortDenote.inhabited unitTc (fun _ _ => ⟨()⟩) s).default

/-- The arguments passed as the constants they stand for (`dataLitsArg`) keep their types. -/
private theorem dataLitsArg_hasTypeA {args : List (LExpr CoreLParams.mono)} {tys : List LMonoTy}
    (h : List.Rel₂ (LExpr.HasTypeA []) args tys) :
    List.Rel₂ (LExpr.HasTypeA []) (args.map (dataLitsArg F)) tys :=
  (dataLitsArg_denote (tc := unitTc) (op := fun n => unitVal ⟨n, ()⟩) h).1

/-- The branch `decideChain F` selects in an `ite` chain has the chain's type. -/
private theorem decideChain_hasTypeA (e : LExpr CoreLParams.mono) :
    ∀ {r : LExpr CoreLParams.mono}, decideChain F e = some r → ∀ {τ : LMonoTy},
      LExpr.HasTypeA [] e τ → LExpr.HasTypeA [] r τ := by
  fun_induction decideChain F e with
  | case1 _ _ _ _ _ _ t f _ ih | case2 _ _ _ _ _ _ t f _ ih =>
    intro r hr τ h
    obtain ⟨-, ht, hf⟩ := HasTypeA.ite_inv h
    first | exact ih hr ht | exact ih hr hf
  | case3 => intro _ h; cases h
  | case4 m c =>
    intro r hr τ h
    cases hr
    exact (dataLitsConst_denote (op := fun n => unitVal ⟨n, ()⟩) h unitVal fun _ => .int).1
  | case5 => intro _ h; cases h

/-- `dataLitsResult F upd r` has every type `r` has. -/
private theorem dataLitsResult_hasTypeA (upd : Bool) {r : LExpr CoreLParams.mono} {τ : LMonoTy}
    (h : LExpr.HasTypeA [] r τ) : LExpr.HasTypeA [] (dataLitsResult F upd r) τ := by
  unfold dataLitsResult
  split
  · split
    · exact hasTypeA_dedupeFront h
    · exact h
  · exact (dataLitsConst_denote (op := fun n => unitVal ⟨n, ()⟩) h unitVal fun _ => .int).1
  · cases hd : decideChain F _ with
    | none => exact h
    | some r' => exact decideChain_hasTypeA _ hd h
  · exact h

/-- `dataLitsPost F upd ty n r` has every type `r` has. -/
theorem dataLitsPost_hasTypeA (upd : Bool) (ty : Option LMonoTy) (n : Nat)
    {r : LExpr CoreLParams.mono} {τ : LMonoTy} (h : LExpr.HasTypeA [] r τ) :
    LExpr.HasTypeA [] (dataLitsPost F upd ty n r) τ := by
  unfold dataLitsPost
  split
  · exact dataLitsResult_hasTypeA upd h
  · exact h

/-! ## Models of `extendDataLits F` -/

/-- `dataLitsFunc F f` differs from `f` in its concrete evaluator only. -/
private theorem dataLitsFunc_eq (f : LFunc CoreLParams) :
    dataLitsFunc F f = { f with concreteEval := (dataLitsFunc F f).concreteEval } := by
  unfold dataLitsFunc; split <;> (try split) <;> rfl

/-- The concrete evaluator of `dataLitsFunc F f`: `f`'s, extended by `dataLitsEval` when `f` is
    a `Map` or `Sequence` operation that is neither a constructor nor short-circuit. -/
private theorem dataLitsFunc_concreteEval (f : LFunc CoreLParams) :
    (dataLitsFunc F f).concreteEval = f.concreteEval.map fun ce =>
      if isCollOp f ∧ f.isConstr = false ∧
          Strata.DL.Util.FuncAttr.hasShortCircuit f.attr = false then
        dataLitsEval F (isUpdateOp f) f.inputs.length ce
      else ce := by
  unfold dataLitsFunc; split <;> (try split) <;> simp_all

/-- `dataLitsFunc F` keeps whether a function is a constructor. -/
private theorem dataLitsFunc_isConstr (f : LFunc CoreLParams) :
    (dataLitsFunc F f).isConstr = f.isConstr := by
  rw [dataLitsFunc_eq]

/-- `dataLitsFunc F` keeps a constructor as it is. -/
private theorem dataLitsFunc_of_isConstr {f : LFunc CoreLParams} (h : f.isConstr = true) :
    dataLitsFunc F f = f := by
  unfold dataLitsFunc; split <;> (try split) <;> simp_all

/-- Under each name, `extendDataLits F` holds `dataLitsFunc F` of the function `F` holds. -/
private theorem getElem_extendDataLits {n : String} (h : n ∈ extendDataLits F) :
    (extendDataLits F)[n]'h = dataLitsFunc F (F[n]'h) :=
  Array.getElem_map ..

/-- The datatype sorts of `extendDataLits F` are those of `F`. -/
private theorem isDatatypeSort_extendDataLits {s : LSort} :
    (extendDataLits F).IsDatatypeSort s ↔ F.IsDatatypeSort s := by
  simp only [Factory.IsDatatypeSort, extendDataLits, Factory.map, Array.mem_map]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, hc, vt, hs⟩
    rw [dataLitsFunc_isConstr] at hc
    exact ⟨g, hg, hc, vt, dataLitsFunc_of_isConstr hc ▸ hs⟩
  · rintro ⟨g, hg, hc, vt, hs⟩
    exact ⟨g, ⟨g, hg, dataLitsFunc_of_isConstr hc⟩, hc, vt, hs⟩

/-- The constructors of `extendDataLits F` are those of `F`. -/
private theorem constr_mem_extendDataLits {f : LFunc CoreLParams} (hc : f.isConstr = true) :
    f ∈ (extendDataLits F).toArray ↔ f ∈ F.toArray := by
  simp only [extendDataLits, Factory.map, Array.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rwa [dataLitsFunc_of_isConstr (dataLitsFunc_isConstr g ▸ hc)]
  · exact fun h => ⟨f, h, dataLitsFunc_of_isConstr hc⟩

/-- An interpretation consistent with the constructors of one of `F` and `extendDataLits F` is
    consistent with those of the other. -/
private theorem constrInterpConsistent_extendDataLits :
    ConstrInterpConsistent tc op (extendDataLits F) ↔ ConstrInterpConsistent tc op F := by
  have hmem : ∀ f : LFunc CoreLParams, f.isConstr = true →
      (f ∈ (extendDataLits F).toArray ↔ f ∈ F.toArray) := fun _ => constr_mem_extendDataLits
  constructor
  · intro h
    refine ⟨fun f1 f2 h1 h2 hc1 hc2 => h.constr_disjoint f1 f2 ((hmem _ hc1).2 h1)
      ((hmem _ hc2).2 h2) hc1 hc2, fun f hf hc => h.constr_injective f ((hmem _ hc).2 hf) hc,
      fun P hstep s v hs => h.constr_induction P (fun f hf hc vt args hall =>
        hstep f ((hmem _ hc).1 hf) hc vt args (HList.All.imp
          (fun _ _ hx hs' => hx (isDatatypeSort_extendDataLits (F := F).2 hs')) hall))
        s v (isDatatypeSort_extendDataLits.2 hs)⟩
  · intro h
    refine ⟨fun f1 f2 h1 h2 hc1 hc2 => h.constr_disjoint f1 f2 ((hmem _ hc1).1 h1)
      ((hmem _ hc2).1 h2) hc1 hc2, fun f hf hc => h.constr_injective f ((hmem _ hc).1 hf) hc,
      fun P hstep s v hs => h.constr_induction P (fun f hf hc vt args hall =>
        hstep f ((hmem _ hc).2 hf) hc vt args (HList.All.imp
          (fun _ _ hx hs' => hx (isDatatypeSort_extendDataLits (F := F).1 hs')) hall))
        s v (isDatatypeSort_extendDataLits.1 hs)⟩

/-- An interpretation satisfies the axioms of `extendDataLits F` exactly when it satisfies those
    of `F`. -/
private theorem axiomsSatisfied_extendDataLits :
    Factory.AxiomsSatisfied tc op (extendDataLits F) ↔ Factory.AxiomsSatisfied tc op F := by
  refine ⟨fun h n hn => ?_, fun h n hn => ?_⟩
  · have hax := h n hn
    rwa [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq] at hax
  · rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq]
    exact h n hn

/-- An interpretation consistent with the function bodies and concrete evaluators of `F` and
    with its constructors is consistent with the function bodies and concrete evaluators of
    `extendDataLits F`. -/
private theorem interpConsistent_extendDataLits (h : Factory.InterpConsistent tc op F)
    (hF : ConstrInterpConsistent tc op F) :
    Factory.InterpConsistent tc op (extendDataLits F) := by
  refine ⟨fun n hn body hb => ?_, fun n hn ce' hce' => ?_⟩
  · rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq] at hb ⊢
    exact h.1 n hn body hb
  · rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_concreteEval] at hce'
    obtain ⟨ce, hce, rfl⟩ := Option.map_eq_some_iff.1 hce'
    rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq]
    split
    · exact interpConsistentEval_dataLitsEval hF _ (h.2 n hn ce hce)
    · exact h.2 n hn ce hce

/-- An interpretation consistent with the function bodies, concrete evaluators and constructors
    of `extendDataLits F` is consistent with the function bodies and concrete evaluators of
    `F`. -/
private theorem interpConsistent_of_extendDataLits
    (h : Factory.InterpConsistent tc op (extendDataLits F))
    (hF : ConstrInterpConsistent tc op F) : Factory.InterpConsistent tc op F := by
  refine ⟨fun n hn body hb => ?_, fun n hn ce hce => ?_⟩
  · have hc := h.1 n hn body
      (by rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq]; exact hb)
    rwa [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq] at hc
  · have hc := h.2 n hn _ (by
      rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_concreteEval, hce]
      rfl)
    rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq] at hc
    split at hc
    · intro vt fv md S args r _ _ hr _ _ _ h_args h_res
      obtain ⟨h', hd⟩ := dataLitsPost_denote hF (isUpdateOp (F[n]'hn)) (some ((F[n]'hn).instTy S))
        (F[n]'hn).inputs.length h_res fv vt
      refine hd.symm.trans (hc vt fv md S args _ ?_ h_args h')
      show Option.map _ ((ce md (some ((F[n]'hn).instTy S)) args).orElse _) = _
      rw [hr]
      rfl
    · exact hc

/-- **A model of `F` is a model of `extendDataLits F`**, with the same interpretation: the
    evaluators extended to datatype values are consistent with every model of `F`, and the
    function bodies, axioms and constructors are those of `F`. -/
def Interp.extendDataLits (M : Interp F) : Interp (extendDataLits F) where
  tcInterp := M.tcInterp
  opInterp := M.opInterp
  allInhabited := M.allInhabited
  interpConsistent := interpConsistent_extendDataLits M.interpConsistent M.constrConsistent
  axiomsSatisfied := axiomsSatisfied_extendDataLits.2 M.axiomsSatisfied
  constrConsistent := constrInterpConsistent_extendDataLits.2 M.constrConsistent

/-- **A model of `extendDataLits F` is a model of `F`**, with the same interpretation: where an
    evaluator of `F` gives a result, the extended evaluator gives its image under
    `dataLitsPost`, which has the result's type and denotation. -/
def Interp.ofExtendDataLits (M : Interp (Core.extendDataLits F)) : Interp F where
  tcInterp := M.tcInterp
  opInterp := M.opInterp
  allInhabited := M.allInhabited
  interpConsistent := interpConsistent_of_extendDataLits M.interpConsistent
    (constrInterpConsistent_extendDataLits.1 M.constrConsistent)
  axiomsSatisfied := axiomsSatisfied_extendDataLits.1 M.axiomsSatisfied
  constrConsistent := constrInterpConsistent_extendDataLits.1 M.constrConsistent

/-! ## Well-formedness of `extendDataLits F` -/

/-- `LExpr.toConstAux F` gives the same result on expressions equal up to metadata. -/
private theorem toConstAux_eraseMetadata :
    ∀ {e₁ e₂ : LExpr CoreLParams.mono}, e₁.eraseMetadata = e₂.eraseMetadata →
      LExpr.toConstAux F e₁ = LExpr.toConstAux F e₂ := by
  intro e₁
  induction e₁ with
  | app m f a ihf iha =>
    intro e₂ h
    cases e₂ <;> simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, reduceCtorEq] at h
    simp only [LExpr.app.injEq, true_and] at h
    simp only [LExpr.toConstAux, ihf h.1, iha h.2]
  | op m o ty =>
    intro e₂ h
    cases e₂ <;> simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, reduceCtorEq] at h
    simp only [LExpr.op.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := h
    cases ty <;> rfl
  | _ =>
    intro e₂ h
    cases e₂ <;> simp_all [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.toConstAux]

mutual
/-- The expression of a constant does not depend on its metadata, up to metadata. -/
private theorem eraseMetadata_toLExpr (m₁ m₂ : CoreExprMetadata) :
    ∀ c : LConst, (c.toLExpr m₁ : LExpr CoreLParams.mono).eraseMetadata =
      (c.toLExpr m₂ : LExpr CoreLParams.mono).eraseMetadata
  | .dataConst _ _ _ ⟨es⟩ => eraseMetadata_toLExprApp m₁ m₂ es _ _ rfl
  | .intConst _ | .strConst _ | .rationalConst _ | .bitvecConst _ _ | .boolConst _
  | .mapConst .. | .sequenceConst .. => rfl
/-- `LConst.toLExprApp` keeps the equality of expressions up to metadata. -/
private theorem eraseMetadata_toLExprApp (m₁ m₂ : CoreExprMetadata) :
    ∀ (es : List LConst) (f₁ f₂ : LExpr CoreLParams.mono), f₁.eraseMetadata = f₂.eraseMetadata →
      (LConst.toLExprApp m₁ f₁ es).eraseMetadata = (LConst.toLExprApp m₂ f₂ es).eraseMetadata
  | [], _, _, h => h
  | e :: es, f₁, f₂, h => eraseMetadata_toLExprApp m₁ m₂ es _ _ (by
      show LExpr.app () f₁.eraseMetadata (e.toLExpr m₁ : LExpr CoreLParams.mono).eraseMetadata =
        LExpr.app () f₂.eraseMetadata (e.toLExpr m₂ : LExpr CoreLParams.mono).eraseMetadata
      rw [h, eraseMetadata_toLExpr m₁ m₂ e])
end

mutual
/-- The expression of a constant has no free variables. -/
private theorem getVars_toLExpr (m : CoreExprMetadata) :
    ∀ c : LConst, LExpr.LExpr.getVars (c.toLExpr m : LExpr CoreLParams.mono) = []
  | .dataConst _ _ _ ⟨es⟩ => getVars_toLExprApp m es _ rfl
  | .intConst _ | .strConst _ | .rationalConst _ | .bitvecConst _ _ | .boolConst _
  | .mapConst .. | .sequenceConst .. => rfl
/-- `LConst.toLExprApp` adds no free variables. -/
private theorem getVars_toLExprApp (m : CoreExprMetadata) :
    ∀ (es : List LConst) (f : LExpr CoreLParams.mono), LExpr.LExpr.getVars f = [] →
      LExpr.LExpr.getVars (LConst.toLExprApp m f es) = []
  | [], _, h => h
  | e :: es, f, h => getVars_toLExprApp m es _ (by
      show LExpr.LExpr.getVars f ++ LExpr.LExpr.getVars (e.toLExpr m : LExpr CoreLParams.mono) = []
      rw [h, getVars_toLExpr m e]; rfl)
end

/-- `dataLitsConst F` does not depend on its metadata, up to metadata. -/
private theorem eraseMetadata_dataLitsConst (m₁ m₂ : CoreExprMetadata) (c : LConst) :
    (dataLitsConst F m₁ c).eraseMetadata = (dataLitsConst F m₂ c).eraseMetadata := by
  unfold dataLitsConst
  split
  · split
    · exact eraseMetadata_toLExpr m₁ m₂ _
    · rfl
  · rfl

/-- `decideChain F` decides expressions equal up to metadata alike, with results equal up to
    metadata. -/
private theorem decideChain_eraseMetadata (e₁ : LExpr CoreLParams.mono) :
    ∀ {e₂ : LExpr CoreLParams.mono}, e₁.eraseMetadata = e₂.eraseMetadata →
      ∀ {r₁}, decideChain F e₁ = some r₁ →
        ∃ r₂, decideChain F e₂ = some r₂ ∧ r₁.eraseMetadata = r₂.eraseMetadata := by
  fun_induction decideChain F e₁ with
  | case1 m m' mk key mk' k t f hq ih | case2 m m' mk key mk' k t f hq ih =>
    intro e₂ h r₁ hr
    cases e₂ <;> simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, reduceCtorEq] at h
    rename_i c₂ t₂ f₂
    simp only [LExpr.ite.injEq, true_and] at h
    obtain ⟨hc, ht, hf⟩ := h
    cases c₂ <;> simp only [LExpr.replaceMetadata, reduceCtorEq] at hc
    rename_i a b
    simp only [LExpr.eq.injEq, true_and] at hc
    obtain ⟨ha, hb⟩ := hc
    cases a <;> simp only [LExpr.replaceMetadata, reduceCtorEq] at ha
    cases b <;> simp only [LExpr.replaceMetadata, reduceCtorEq] at hb
    simp only [LExpr.const.injEq, true_and] at ha hb
    subst ha hb
    simp only [decideChain, hq]
    first | exact ih ht hr | exact ih hf hr
  | case3 => intro _ _ _ h; cases h
  | case4 m c =>
    intro e₂ h r₁ hr
    cases hr
    cases e₂ <;> simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, reduceCtorEq] at h
    simp only [LExpr.const.injEq, true_and] at h
    subst h
    exact ⟨_, rfl, eraseMetadata_dataLitsConst _ _ c⟩
  | case5 => intro _ _ _ h; cases h

/-- `dataLitsResult F upd` keeps the equality of results up to metadata. -/
private theorem eraseMetadata_dataLitsResult (upd : Bool) {r₁ r₂ : LExpr CoreLParams.mono}
    (h : r₁.eraseMetadata = r₂.eraseMetadata) :
    (dataLitsResult F upd r₁).eraseMetadata = (dataLitsResult F upd r₂).eraseMetadata := by
  have h₀ := h
  cases r₁ <;> cases r₂ <;>
    simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, reduceCtorEq] at h
  case const.const m₁ c₁ m₂ c₂ =>
    simp only [LExpr.const.injEq, true_and] at h
    subst h
    cases c₁ <;> simp only [dataLitsResult] <;>
      first | (split <;> rfl) | exact eraseMetadata_dataLitsConst _ _ _
  case ite.ite m₁ c₁ t₁ f₁ m₂ c₂ t₂ f₂ =>
    simp only [dataLitsResult]
    cases hd : decideChain F (.ite m₁ c₁ t₁ f₁) with
    | some r =>
      obtain ⟨r', hr', he⟩ := decideChain_eraseMetadata _ h₀ hd
      rw [hr']
      exact he
    | none =>
      cases hd' : decideChain F (.ite m₂ c₂ t₂ f₂) with
      | none => exact h₀
      | some r =>
        obtain ⟨_, h₁, -⟩ := decideChain_eraseMetadata _ h₀.symm hd'
        rw [hd] at h₁
        cases h₁
  all_goals
    simp only [dataLitsResult]
    exact h₀

/-- `dataLitsPost F upd ty n` keeps the equality of results up to metadata. -/
private theorem eraseMetadata_dataLitsPost (upd : Bool) (ty : Option LMonoTy) (n : Nat)
    {r₁ r₂ : LExpr CoreLParams.mono} (h : r₁.eraseMetadata = r₂.eraseMetadata) :
    (dataLitsPost F upd ty n r₁).eraseMetadata = (dataLitsPost F upd ty n r₂).eraseMetadata := by
  have ht : LExpr.typeCheck [] r₁ = LExpr.typeCheck [] r₂ := by
    rw [replaceMetadata_typeCheck (e := r₁) fun _ => (),
      replaceMetadata_typeCheck (e := r₂) fun _ => ()]
    exact congrArg (LExpr.typeCheck []) h
  simp only [dataLitsPost, ht]
  split
  · exact eraseMetadata_dataLitsResult upd h
  · exact h

/-- `dataLitsArg F` keeps the equality of arguments up to metadata. -/
private theorem eraseMetadata_dataLitsArg :
    ∀ {args₁ args₂ : List (LExpr CoreLParams.mono)},
      args₁.map LExpr.eraseMetadata = args₂.map LExpr.eraseMetadata →
      (args₁.map (dataLitsArg F)).map LExpr.eraseMetadata =
        (args₂.map (dataLitsArg F)).map LExpr.eraseMetadata
  | [], [], _ => rfl
  | a₁ :: args₁, a₂ :: args₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    refine ⟨?_, eraseMetadata_dataLitsArg h.2⟩
    have hc : a₁.toConst? F = a₂.toConst? F := by
      simp only [LExpr.toConst?, toConstAux_eraseMetadata h.1]
    simp only [dataLitsArg, hc]
    split
    · rfl
    · exact h.1
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- The free variables of `decideChain F e` are free in `e`. -/
private theorem getVars_decideChain (e : LExpr CoreLParams.mono) :
    ∀ {r}, decideChain F e = some r → ∀ z ∈ LExpr.LExpr.getVars r, z ∈ LExpr.LExpr.getVars e := by
  fun_induction decideChain F e with
  | case1 m m' mk key mk' k t f hq ih | case2 m m' mk key mk' k t f hq ih =>
    intro r hr z hz
    simp only [LExpr.LExpr.getVars, List.mem_append]
    first | exact .inl (.inr (ih hr z hz)) | exact .inr (ih hr z hz)
  | case3 => intro _ h; cases h
  | case4 m c =>
    intro r hr z hz
    cases hr
    unfold dataLitsConst at hz
    split at hz
    · split at hz
      · simp [getVars_toLExpr] at hz
      · exact hz
    · exact hz
  | case5 => intro _ h; cases h

/-- The free variables of `dataLitsPost F upd ty n r` are free in `r`. -/
private theorem getVars_dataLitsPost (upd : Bool) (ty : Option LMonoTy) (n : Nat)
    (r : LExpr CoreLParams.mono) :
    ∀ z ∈ LExpr.LExpr.getVars (dataLitsPost F upd ty n r), z ∈ LExpr.LExpr.getVars r := by
  intro z hz
  unfold dataLitsPost dataLitsResult at hz
  split at hz
  · split at hz
    · split at hz
      · simp [LExpr.LExpr.getVars] at hz
      · exact hz
    · exact getVars_decideChain _ rfl z hz
    · simp only [Option.getD] at hz
      split at hz
      · rename_i hd
        exact getVars_decideChain _ hd z hz
      · exact hz
    · exact hz
  · exact hz

/-- **`dataLitsFunc F` keeps a function well-formed**: the extended evaluator matches the
    arity, is insensitive to metadata (`LExpr.toConst?` and `LExpr.typeCheck` ignore metadata)
    and adds no free variables. -/
theorem dataLitsFunc_wf {f : LFunc CoreLParams} (h : LFuncWF f) : LFuncWF (dataLitsFunc F f) := by
  unfold dataLitsFunc
  split
  · rename_i ce hce
    split
    · rename_i hc
      obtain ⟨-, hcon, hsc⟩ := hc
      exact {
        toFuncWF := h.toFuncWF
        constr_no_eval := by simp [hcon]
        typeArgs_no_gen_prefix := h.typeArgs_no_gen_prefix
        concreteEval_argmatch := by
          intro fn md opTy args res hfn hres
          cases hfn
          obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.1 hres
          cases hc : ce md opTy args with
          | some r' => exact h.concreteEval_argmatch ce md opTy args r' hce hc
          | none =>
            simp only [hc, Option.orElse_none] at hr
            exact (List.length_map ..).symm.trans (h.concreteEval_argmatch ce md opTy _ r hce hr)
        body_or_concreteEval := by
          have hb := h.body_or_concreteEval
          simp_all
        concreteEval_eraseMetadata := by
          intro fn hfn md1 md2 opTy args1 args2 res1 he hres
          cases hfn
          obtain ⟨r1, hr1, rfl⟩ := Option.map_eq_some_iff.1 hres
          suffices hs : ∃ r2, ((ce md2 opTy args2).orElse fun _ =>
              ce md2 opTy (args2.map (dataLitsArg F))) = some r2 ∧
              r1.eraseMetadata = r2.eraseMetadata by
            obtain ⟨r2, hr2, heq⟩ := hs
            exact ⟨_, by simp only [dataLitsEval, hr2, Option.map_some],
              eraseMetadata_dataLitsPost _ _ _ heq⟩
          cases hc1 : ce md1 opTy args1 with
          | some r =>
            simp only [hc1, Option.orElse_some, Option.some.injEq] at hr1
            subst hr1
            obtain ⟨r2, hr2, heq⟩ :=
              h.concreteEval_eraseMetadata ce hce md1 md2 opTy args1 args2 _ he hc1
            exact ⟨r2, by simp [hr2], heq⟩
          | none =>
            simp only [hc1, Option.orElse_none] at hr1
            cases hc2 : ce md2 opTy args2 with
            | some r =>
              obtain ⟨r', hr', -⟩ :=
                h.concreteEval_eraseMetadata ce hce md2 md1 opTy args2 args1 r he.symm hc2
              simp [hr'] at hc1
            | none =>
              obtain ⟨r2, hr2, heq⟩ := h.concreteEval_eraseMetadata ce hce md1 md2 opTy _ _ _
                (eraseMetadata_dataLitsArg he) hr1
              exact ⟨r2, by simp [hr2], heq⟩
        concreteEval_freeVars := by
          intro fn hfn md opTy args res hres z hz
          cases hfn
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hres
          have hz' := getVars_dataLitsPost _ _ _ r z hz
          cases hc : ce md opTy args with
          | some r' =>
            simp only [hc, Option.orElse_some, Option.some.injEq] at hr
            subst hr
            exact h.concreteEval_freeVars ce hce md opTy args _ hc z hz'
          | none =>
            simp only [hc, Option.orElse_none] at hr
            obtain ⟨a, ha, hza⟩ := h.concreteEval_freeVars ce hce md opTy _ r hr z hz'
            obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
            refine ⟨a₀, ha₀, ?_⟩
            unfold dataLitsArg at hza
            split at hza
            · simp [LExpr.LExpr.getVars] at hza
            · exact hza
        shortCircuit_substFvars := by intro hs; simp [hsc] at hs }
    · exact h
  · exact h

/-- **Extending a well-formed factory to datatype values keeps it well-formed.** -/
theorem extendDataLits_wf (h : FactoryWF F) : FactoryWF (extendDataLits F) :=
  ⟨fun lf hlf => by
    simp only [extendDataLits, Factory.map] at hlf
    obtain ⟨g, hg, rfl⟩ := Array.mem_map.1 hlf
    exact dataLitsFunc_wf (h.lfuncs_wf g hg)⟩


/-! ## Evaluation soundness conditions of `extendDataLits F` -/

/-- Looking a name up in `extendDataLits F` gives `dataLitsFunc F` of the function `F` holds
    under it. -/
private theorem getElem?_extendDataLits (n : String) :
    (extendDataLits F)[n]? = (F[n]?).map (dataLitsFunc F) := by
  by_cases hn : n ∈ F
  · rw [Factory.getElem?_of_mem (F := extendDataLits F) hn, Factory.getElem?_of_mem hn]
    exact congrArg some (getElem_extendDataLits (F := F) hn)
  · have h₁ : ¬ ((extendDataLits F)[n]?).isSome = true :=
      fun h => hn ((Factory.mem_iff_getElem?_isSome (extendDataLits F) n).2 h)
    have h₂ : ¬ (F[n]?).isSome = true := fun h => hn ((Factory.mem_iff_getElem?_isSome _ n).2 h)
    simp only [Option.not_isSome_iff_eq_none] at h₁ h₂
    rw [h₁, h₂]
    rfl

/-- The operator annotations of an expression are consistent with `extendDataLits F` exactly
    when they are consistent with `F`. -/
private theorem opsConsistent_extendDataLits (e : LExpr CoreLParams.mono) :
    OpsConsistent (extendDataLits F) e ↔ OpsConsistent F e := by
  induction e with
  | op m o ty =>
    unfold OpsConsistent
    rw [getElem?_extendDataLits]
    cases F[o.name]? with
    | none => exact Iff.rfl
    | some fn =>
      show (match LFunc.opTypeSubst (dataLitsFunc F fn) _ with
        | some S => _ | none => False) ↔ _
      rw [dataLitsFunc_eq]
      exact Iff.rfl
  | _ => simp_all only [OpsConsistent]

/-- A ground constructor of a factory whose constructors come from a type factory
    (`Factory.ConstrWellFormed`) has no type arguments, and its signature is the ground one. -/
private theorem isGroundConstr_mono {tf : @TypeFactory CoreLParams.IDMeta}
    (hc : F.ConstrWellFormed tf) {n : String} {as : List LSort} {s : LSort}
    (h : F.isGroundConstr n as s = true) :
    ∃ fn, F[n]? = some fn ∧ fn.typeArgs = [] ∧ fn.output = s.toMonoTy ∧
      fn.inputs.map Prod.snd = as.map (·.toMonoTy) := by
  unfold Factory.isGroundConstr at h
  split at h
  · rename_i fn hfn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hcon, hout⟩, hin⟩ := h
    obtain ⟨d, -, c, -, rfl⟩ := hc fn (Factory.getElem?_is_some_implies_mem hfn) hcon
    refine ⟨_, hfn, ?_, hout, (ListMap.values_eq_map_snd _).symm.trans hin⟩
    simp only [constrFunc, dataDefault, data] at hout ⊢
    cases s with
    | bitvec => simp [LSort.toMonoTy] at hout
    | tcons name args =>
      simp only [LSort.toMonoTy, LMonoTy.tcons.injEq] at hout
      cases hd : d.typeArgs with
      | nil => rfl
      | cons a _ =>
        rw [hd] at hout
        cases args with
        | nil => simp [LSort.toMonoTy.map] at hout
        | cons b _ =>
          simp only [List.map_cons, LSort.toMonoTy.map, List.cons.injEq] at hout
          cases b <;> simp [LSort.toMonoTy] at hout
  · cases h

mutual
/-- The expression of a constant whose datatype values name ground constructors of `F`
    (`LConst.ctorsIn`) has operator annotations consistent with `F`, when the constructors of `F`
    come from a type factory. -/
private theorem opsConsistent_toLExpr {tf : @TypeFactory CoreLParams.IDMeta}
    (hc : F.ConstrWellFormed tf) (m : CoreExprMetadata) :
    ∀ c : LConst, c.ctorsIn F = true → OpsConsistent F (c.toLExpr m : LExpr CoreLParams.mono)
  | .dataConst _ _ _ ⟨es⟩, h => by
    simp only [LConst.ctorsIn, Bool.and_eq_true] at h
    obtain ⟨fn, hfn, hta, hout, hin⟩ := isGroundConstr_mono hc h.1
    refine opsConsistent_toLExprApp hc m es _ h.2
      (OpsConsistent.op_in (tySubst := Subst.empty) hfn ?_ ?_)
    · simp [LFunc.opTypeSubst, hta]
    · rw [hout, hin]
      rfl
  | .intConst _, _ | .strConst _, _ | .rationalConst _, _ | .bitvecConst _ _, _
  | .boolConst _, _ | .mapConst .., _ | .sequenceConst .., _ => OpsConsistent.const
/-- `LConst.toLExprApp` keeps operator annotations consistent with `F`. -/
private theorem opsConsistent_toLExprApp {tf : @TypeFactory CoreLParams.IDMeta}
    (hc : F.ConstrWellFormed tf) (m : CoreExprMetadata) :
    ∀ (es : List LConst) (f : LExpr CoreLParams.mono), LConst.ctorsInElems F es = true →
      OpsConsistent F f → OpsConsistent F (LConst.toLExprApp m f es)
  | [], _, _, h => h
  | e :: es, _, he, h => by
    simp only [LConst.ctorsInElems, Bool.and_eq_true] at he
    exact opsConsistent_toLExprApp hc m es _ he.2
      (OpsConsistent.app h (opsConsistent_toLExpr hc m e he.1))
end

/-- `dataLitsPost F upd ty n` keeps operator annotations consistent with `F`, when the
    constructors of `F` come from a type factory. -/
private theorem opsConsistent_dataLitsPost {tf : @TypeFactory CoreLParams.IDMeta}
    (hc : F.ConstrWellFormed tf) (upd : Bool) (ty : Option LMonoTy) (n : Nat)
    {r : LExpr CoreLParams.mono} (h : OpsConsistent F r) :
    OpsConsistent F (dataLitsPost F upd ty n r) := by
  have hconst : ∀ m c, OpsConsistent F (dataLitsConst F m c) := by
    intro m c
    unfold dataLitsConst
    split
    · split
      · rename_i hw
        exact opsConsistent_toLExpr hc m _ (Bool.and_eq_true _ _ ▸ hw).2
      · exact OpsConsistent.const
    · exact OpsConsistent.const
  have hchain : ∀ e r, decideChain F e = some r → OpsConsistent F e → OpsConsistent F r := by
    intro e
    fun_induction decideChain F e with
    | case1 _ _ _ _ _ _ t f _ ih | case2 _ _ _ _ _ _ t f _ ih =>
      intro r hr he
      simp only [OpsConsistent] at he
      first | exact ih r hr he.2.1 | exact ih r hr he.2.2
    | case3 => intro _ h; cases h
    | case4 m c =>
      intro r hr _
      cases hr
      exact hconst m c
    | case5 => intro _ h; cases h
  unfold dataLitsPost dataLitsResult
  split
  · split
    · split
      · exact OpsConsistent.const
      · exact h
    · exact hconst _ _
    · cases hd : decideChain F _ with
      | none => exact h
      | some r' => exact hchain _ _ hd h
    · exact h
  · exact h

/-- An expression without free variables has its free variables annotated by every map. -/
private theorem fvars_annotated_by_of_getVars (tyMap : Map CoreLParams.Identifier LMonoTy) :
    ∀ e : LExpr CoreLParams.mono, LExpr.LExpr.getVars e = [] → fvars_annotated_by tyMap e := by
  intro e
  induction e <;> simp_all [LExpr.LExpr.getVars, fvars_annotated_by]

/-- `dataLitsPost F upd ty n` keeps free variables annotated by `tyMap`. -/
private theorem fvars_annotated_by_dataLitsPost (tyMap : Map CoreLParams.Identifier LMonoTy)
    (upd : Bool) (ty : Option LMonoTy) (n : Nat) {r : LExpr CoreLParams.mono}
    (h : fvars_annotated_by tyMap r) : fvars_annotated_by tyMap (dataLitsPost F upd ty n r) := by
  have hconst : ∀ m c, fvars_annotated_by tyMap (dataLitsConst F m c) := fun m c =>
    fvars_annotated_by_of_getVars tyMap _ (List.eq_nil_iff_forall_not_mem.2 fun z hz =>
      by simpa [LExpr.LExpr.getVars] using getVars_decideChain (F := F) (.const m c) rfl z hz)
  have hchain : ∀ e r, decideChain F e = some r → fvars_annotated_by tyMap e →
      fvars_annotated_by tyMap r := by
    intro e
    fun_induction decideChain F e with
    | case1 _ _ _ _ _ _ t f _ ih | case2 _ _ _ _ _ _ t f _ ih =>
      intro r hr he
      simp only [fvars_annotated_by] at he
      first | exact ih r hr he.2.1 | exact ih r hr he.2.2
    | case3 => intro _ h; cases h
    | case4 m c =>
      intro r hr _
      cases hr
      exact hconst m c
    | case5 => intro _ h; cases h
  unfold dataLitsPost dataLitsResult
  split
  · split
    · split
      · trivial
      · exact h
    · exact hconst _ _
    · cases hd : decideChain F _ with
      | none => exact h
      | some r' => exact hchain _ _ hd h
    · exact h
  · exact h

/-- **Extending a factory to datatype values keeps the conditions under which evaluation
    preserves denotation** (`Factory.EvalSoundWF`): the extended evaluators return results well
    typed at the instantiated output type, with operator annotations consistent with the factory
    (the constructor applications they build name ground constructors of `F`, which have no type
    arguments since the constructors of `F` come from a type factory) and without new free
    variables. -/
theorem extendDataLits_evalSoundWF (h : Factory.EvalSoundWF F) :
    Factory.EvalSoundWF (extendDataLits F) := by
  obtain ⟨⟨tf, hwf⟩, hstep⟩ : Lambda.Factory.EvalSoundWFS F := h
  refine ⟨⟨tf, extendDataLits_wf hwf.factoryWF,
    fun f hf hc => hwf.constrWF f ((constr_mem_extendDataLits hc).1 hf) hc, hwf.tfWF⟩,
    fun tyMap => ?_⟩
  obtain ⟨hwt, hewt, hbops, heops, hbann, heann⟩ := hstep tyMap
  have hargs : ∀ {P : LExpr CoreLParams.mono → Prop}, (∀ m c, P (.const m c)) →
      ∀ {args : List (LExpr CoreLParams.mono)}, (∀ a ∈ args, P a) →
        ∀ a ∈ args.map (dataLitsArg F), P a := by
    intro P hP args ha a hm
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 hm
    unfold dataLitsArg
    split
    · exact hP _ _
    · exact ha a₀ ha₀
  refine ⟨fun n hn body hb => ?_, fun n hn ce' hce' md args r' S hr ha => ?_,
    fun n hn body callee args S hb hS => ?_, fun n hn ce' md opTy args r' hce' hr ha => ?_,
    fun n hn body S args hb hlen ha => ?_, fun n hn ce' md opTy args r' hce' hr ha => ?_⟩
  · rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq] at hb ⊢
    exact hwt n hn body hb
  · rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_concreteEval] at hce'
    obtain ⟨ce, hce, rfl⟩ := Option.map_eq_some_iff.1 hce'
    rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq] at hr ha ⊢
    split at hr
    · obtain ⟨r, hr0, rfl⟩ := Option.map_eq_some_iff.1 hr
      apply dataLitsPost_hasTypeA
      have hr1 : ((ce md (some ((F[n]'hn).instTy S)) args).orElse fun _ =>
          ce md (some ((F[n]'hn).instTy S)) (args.map (dataLitsArg F))) = some r := hr0
      cases hc : ce md (some ((F[n]'hn).instTy S)) args with
      | some r₀ =>
        simp only [hc, Option.orElse_some, Option.some.injEq] at hr1
        subst hr1
        exact hewt n hn ce hce md args _ S hc ha
      | none =>
        simp only [hc, Option.orElse_none] at hr1
        exact hewt n hn ce hce md _ r S hr1 (dataLitsArg_hasTypeA ha)
    · exact hewt n hn ce hce md args r' S hr ha
  · rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq] at hb hS
    exact (opsConsistent_extendDataLits _).2 (hbops n hn body callee args S hb hS)
  · rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_concreteEval] at hce'
    obtain ⟨ce, hce, rfl⟩ := Option.map_eq_some_iff.1 hce'
    have haF : ∀ a ∈ args, OpsConsistent F a :=
      fun a h => (opsConsistent_extendDataLits a).1 (ha a h)
    refine (opsConsistent_extendDataLits _).2 ?_
    split at hr
    · obtain ⟨r, hr0, hr'⟩ := Option.map_eq_some_iff.1 hr.symm
      subst hr'
      apply opsConsistent_dataLitsPost hwf.constrWF
      cases hc : ce md opTy args with
      | some r₀ =>
        simp only [hc, Option.orElse_some, Option.some.injEq] at hr0
        subst hr0
        exact heops n hn ce md opTy args _ hce hc.symm haF
      | none =>
        simp only [hc, Option.orElse_none] at hr0
        exact heops n hn ce md opTy _ r hce hr0.symm (hargs (fun _ _ => OpsConsistent.const) haF)
    · exact heops n hn ce md opTy args r' hce hr haF
  · rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_eq] at hb hlen ⊢
    exact hbann n hn body S args hb hlen ha
  · rw [getElem_extendDataLits (F := F) hn, dataLitsFunc_concreteEval] at hce'
    obtain ⟨ce, hce, rfl⟩ := Option.map_eq_some_iff.1 hce'
    split at hr
    · obtain ⟨r, hr0, hr'⟩ := Option.map_eq_some_iff.1 hr.symm
      subst hr'
      apply fvars_annotated_by_dataLitsPost
      cases hc : ce md opTy args with
      | some r₀ =>
        simp only [hc, Option.orElse_some, Option.some.injEq] at hr0
        subst hr0
        exact heann n hn ce md opTy args _ hce hc.symm ha
      | none =>
        simp only [hc, Option.orElse_none] at hr0
        exact heann n hn ce md opTy _ r hce hr0.symm (hargs (fun _ _ => trivial) ha)
    · exact heann n hn ce md opTy args r' hce hr ha


end -- public section
end Core
