/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.VerifiedSMTGen.CoreCtx
import all Strata.Languages.Core.VerifiedSMTGen.CoreCtx
public import Strata.DL.SMT.DenoteTypedSMTQuery
import all Strata.DL.SMT.DenoteTypedSMTQuery
-- The production encoder: provides `translate`/`translateQuery`/`tyToTermType`/`corePredefinedOpToSMTOp`/
-- `TranslateEnv`/`CoreCtx.toTranslateEnv`/`sigToSMT`/`fnDefSmtParams`/… — the real functions these proofs
-- reason about (it in turn imports the language files above, so `SMTQuery`/`CoreCtx`/… stay single-source).
public import Strata.Languages.Core.VerifiedSMTGen.SMTEncoder
import all Strata.Languages.Core.VerifiedSMTGen.SMTEncoder
public import Strata.Languages.Core.VerifiedSMTGen.SharedWF
import all Strata.Languages.Core.VerifiedSMTGen.SharedWF
public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.CoreOp
import all Strata.Languages.Core.CoreOp
public import Strata.Languages.Core.NameMangling
import all Strata.Languages.Core.NameMangling
public import Strata.DL.SMT.Factory
import all Strata.DL.SMT.Factory
public import Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.TypeFactory
public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
public import Strata.DL.Imperative.EvalContext
import all Strata.DL.Imperative.EvalContext
public import Strata.Util.Name
import all Strata.Util.Name
public import StrataDDM.Util.DecimalRat
import all StrataDDM.Util.DecimalRat
public import Strata.DL.SMT.DenoteTypedFactoryCorrect
import all Strata.DL.SMT.DenoteTypedFactoryCorrect
public import Strata.DL.SMT.DenoteTyped
import all Strata.DL.SMT.DenoteTyped
public import Strata.DL.SMT.DenoteTypedProps
import all Strata.DL.SMT.DenoteTypedProps
public import Strata.Util.NameProofs
import all Strata.Util.NameProofs

/-!
# Refactored SMT encoder — translate soundness (CoreCtx ⟶ SMTQuery)

Statements A and B: `translateQuery_WF` — under `CoreCtx.WF` + `CoreCtx.NamesWF`, the emitted query is
`SMTQuery.WF`; `query_valid_of_unsatWithNegObl` — if it is further `UnsatWithNegObl`, the source `CoreCtx` is
`Valid`. This is where cross-language contact happens (CoreCtx meets SMTQuery): the correspondence
relations, `mkUFInterp`, HList/BVarVal bridges, `tyToTermType`, and a source-side weakening
(`HasSimpType.weaken_fvar` in `CollectSound`) reconciling the order-threaded `FnDefsWF` /
`VarDefsWF` prefix typing with `translate_sound`/`IF.UFConsistent` at the full `toΦ`/`toΨ` ↔ `q.ufs`.
-/

open Core Lambda Imperative Strata.SMT Std
open Strata.SMT.DenoteTyped

namespace Core.Refactor

/-! ## Typing-side soundness proofs -/

/-! ## Substrate: UF lookup, base-type facts, base-type encoding -/

theorem lookupUF_mem {ufs : UFCtx} {name : String} {uf : UF}
    (h : lookupUF ufs name = some uf) : uf ∈ ufs :=
  List.mem_of_find?_eq_some h

theorem lookupUF_id {ufs : UFCtx} {name : String} {uf : UF}
    (h : lookupUF ufs name = some uf) : uf.id = name := by
  have := List.find?_some h; simpa using this

/-- `real` (`.tcons "real" []`) is not a base monotype (base = bool/int/string/bitvec). -/
theorem not_MonoTyIsBase_real : ¬ LExpr.MonoTyIsBase (.tcons "real" []) := by
  intro h
  generalize hg : (LMonoTy.tcons "real" []) = t at h
  cases h <;> simp_all

mutual
theorem HasSimpType_base {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {τ : LMonoTy} (he : LExpr.HasSimpType Φ Ψ Δ e τ) : LExpr.MonoTyIsBase τ := by
  match he with
  | .const c hbase => exact hbase
  | .bvar i _ hlook hbase => exact hbase
  | .app fn arg rty hspine => exact AppSpine_base hspine
  | .fvarNullary f τ rty hspine => exact AppSpine_base hspine
  | .ite c t _ e_ hc ht hee => exact HasSimpType_base ht
  | .eq e1 e2 τ hbase he1 he2 => exact .bool
  | .quant qty qbody qk qname qtr qτtr hbase htr hbody => exact .bool
theorem AppSpine_base {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {e : Expression.Expr}
    {acc : List LMonoTy} {rty : LMonoTy} (hspine : LExpr.AppSpine Φ Ψ Δ e acc rty) :
    LExpr.MonoTyIsBase rty := by
  match hspine with
  | .app fn arg aty acc' rty harg hrest => exact AppSpine_base hrest
  | .fvar f τ acc' rty hmem hcollect hbase => exact hbase
  | .op o oty acc' rty hop hcollect =>
    generalize CoreOp.ofString (Core.NameMangling.demangledBaseName o.name) = cop at hop
    cases hop <;> first | exact .int | exact .bool
  | .fnOp o oty acc' rty hmem hnpre hcollect hbase => exact hbase
termination_by structural hspine
end

/- `tyToTermType uAT` produces WFSort-valid primitive sorts on base types. -/
theorem tyToTermType_wfSort {uss : USCtx} {uAT : Bool} {τ : LMonoTy}
    (hbase : LExpr.MonoTyIsBase τ) : TermType.WFSort uss (tyToTermType uAT τ) = true := by
  cases hbase with
  | bool => simp [tyToTermType, TermType.WFSort, TermType.isBase]
  | int => simp [tyToTermType, TermType.WFSort, TermType.isBase]
  | string => simp [tyToTermType, TermType.WFSort, TermType.isBase]
  | bitvec => simp [tyToTermType, TermType.WFSort, TermType.isBase]

theorem tyToTermTypes_wfSort {uss : USCtx} {uAT : Bool} {tys : List LMonoTy}
    (h : ∀ t ∈ tys, LExpr.MonoTyIsBase t) :
    (tys.map (tyToTermType uAT)).all (TermType.WFSort uss) = true := by
  induction tys with
  | nil => simp
  | cons t rest ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true]
    exact ⟨tyToTermType_wfSort (h t (List.mem_cons.mpr (Or.inl rfl))),
      ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))⟩

/-- `tyToTermType uAT` produces a base SMT sort on a base monotype (constituent-part lemma,
    mirroring `tyToTermType_wfSort`). -/
theorem tyToTermType_isBase {uAT : Bool} {τ : LMonoTy}
    (hbase : LExpr.MonoTyIsBase τ) : TermType.isBase (tyToTermType uAT τ) = true := by
  cases hbase <;> simp [tyToTermType, TermType.isBase]

/-! ## `typeCheckArgs` inversion lemmas -/

/-- `typeCheckArgs` forces the argument list and the expected-type list to have equal length. -/
private theorem typeCheckArgs_length {ufs : UFCtx} {Γ : List TermVar}
    {smtArgs : List Term} {smtTys : List TermType}
    (h : Term.typeCheckArgs ⟨[], ufs, Γ⟩ smtArgs smtTys = true) : smtArgs.length = smtTys.length := by
  induction smtArgs generalizing smtTys with
  | nil => cases smtTys with
    | nil => rfl
    | cons _ _ => simp [Term.typeCheckArgs] at h
  | cons t ts ih => cases smtTys with
    | nil => simp [Term.typeCheckArgs] at h
    | cons ty tys =>
      simp only [Term.typeCheckArgs] at h
      split at h
      · rename_i hty
        simp only [Bool.and_eq_true] at h
        simp only [List.length_cons, Nat.add_right_cancel_iff]
        exact ih h.2
      · exact absurd h (by simp)

/-- Inversion for a two-element expected-type list. -/
private theorem typeCheckArgs_two_inv {ufs : UFCtx} {Γ : List TermVar}
    {smtArgs : List Term} {ty1 ty2 : TermType}
    (h : Term.typeCheckArgs ⟨[], ufs, Γ⟩ smtArgs [ty1, ty2] = true) :
    ∃ t1 t2, smtArgs = [t1, t2] ∧
      Term.typeCheck ⟨[], ufs, Γ⟩ t1 = .ok ty1 ∧ Term.typeCheck ⟨[], ufs, Γ⟩ t2 = .ok ty2 := by
  have hlen := typeCheckArgs_length h
  match smtArgs, hlen with
  | [t1, t2], _ =>
    refine ⟨t1, t2, rfl, ?_, ?_⟩
    · simp only [Term.typeCheckArgs] at h
      split at h <;> rename_i hty <;> simp_all [BEq.beq, decide_eq_true_eq]
    · simp only [Term.typeCheckArgs] at h
      split at h <;> rename_i hty1
      · simp only [Bool.and_eq_true] at h
        obtain ⟨_, h2⟩ := h
        revert h2; split <;> rename_i hty2 <;>
          simp_all [BEq.beq, decide_eq_true_eq]
      · exact absurd h (by simp)

/-- Inversion for a one-element expected-type list. -/
private theorem typeCheckArgs_one_inv {ufs : UFCtx} {Γ : List TermVar}
    {smtArgs : List Term} {ty1 : TermType}
    (h : Term.typeCheckArgs ⟨[], ufs, Γ⟩ smtArgs [ty1] = true) :
    ∃ t1, smtArgs = [t1] ∧ Term.typeCheck ⟨[], ufs, Γ⟩ t1 = .ok ty1 := by
  have hlen := typeCheckArgs_length h
  match smtArgs, hlen with
  | [t1], _ =>
    refine ⟨t1, rfl, ?_⟩
    simp only [Term.typeCheckArgs] at h
    split at h <;> rename_i hty <;> simp_all [BEq.beq, decide_eq_true_eq]

/-! ## Well-formedness / correspondence layer -/

/-- **Free-var / function-name context ↔ UF-context correspondence.** -/
structure FNameCtxCorresponds (uAT : Bool) (Φ : FNameCtx) (ufs : UFCtx) : Prop where
  /-- Every declared name resolves to a UF. -/
  fvar_resolves : ∀ (name : String) (τ : LMonoTy), (name, τ) ∈ Φ →
    (lookupUF ufs name).isSome = true
  /-- The resolved UF's argument types are the SMT encoding of the collected argument types.
      Source side: the collected argument types are base; correspondence: they encode to `uf.args`. -/
  args_eq : ∀ (name : String) (τ : LMonoTy) (uf : UF), (name, τ) ∈ Φ →
    lookupUF ufs name = some uf →
    (∀ t ∈ (collectArrowTy τ).1, LExpr.MonoTyIsBase t)
      ∧ (collectArrowTy τ).1.map (tyToTermType uAT) = uf.args
  /-- The resolved UF's return type is the SMT encoding of the collected return type.
      Source side: the collected return type is base; correspondence: it encodes to `uf.out`. -/
  out_eq : ∀ (name : String) (τ : LMonoTy) (uf : UF), (name, τ) ∈ Φ →
    lookupUF ufs name = some uf →
    LExpr.MonoTyIsBase (collectArrowTy τ).2 ∧ tyToTermType uAT (collectArrowTy τ).2 = uf.out

/-- Existential-shape view of `FNameCtxCorresponds`. -/
theorem FNameCtxCorresponds.fvar_has_uf {uAT : Bool} {Φ : FVarCtx} {ufs : UFCtx}
    (hwf : FNameCtxCorresponds uAT Φ ufs)
    (name : String) (ty : LMonoTy) (hmem : (name, ty) ∈ Φ) :
    let (argTys, rty) := collectArrowTy ty
    ∃ smtArgTys smtRty,
      ((∀ t ∈ argTys, LExpr.MonoTyIsBase t) ∧ argTys.map (tyToTermType uAT) = smtArgTys) ∧
      (LExpr.MonoTyIsBase rty ∧ tyToTermType uAT rty = smtRty) ∧
      (⟨name, smtArgTys, smtRty⟩ : UF) ∈ ufs := by
  obtain ⟨uf, hlk⟩ := Option.isSome_iff_exists.mp (hwf.fvar_resolves name ty hmem)
  have hargs := hwf.args_eq name ty uf hmem hlk
  have hout := hwf.out_eq name ty uf hmem hlk
  have hid : uf.id = name := lookupUF_id hlk
  have hmem_uf : uf ∈ ufs := lookupUF_mem hlk
  obtain ⟨argTys, rty, hcol⟩ : ∃ a r, collectArrowTy ty = (a, r) := ⟨_, _, rfl⟩
  rw [hcol] at hargs hout ⊢
  simp only at hargs hout ⊢
  refine ⟨uf.args, uf.out, hargs, hout, ?_⟩
  have huf_eq : (⟨name, uf.args, uf.out⟩ : UF) = uf := by rw [← hid]
  rw [huf_eq]; exact hmem_uf

/-- **Source typing contexts** bundled for the expression-level lemmas. -/
structure SimpTyCtx where
  Ψ : FnCtx     -- interpreted-function context
  Φ : FVarCtx   -- free-variable context

/-- The static (non-binder) names `translate` avoids when choosing a fresh quantifier binder. -/
def staticUsedNames (tenv : TranslateEnv) : Std.HashSet String := quantUsedNames tenv []

/-- **Anchor / validity check** — for a real collected `CoreCtx`, the `hused` freshness hypothesis is
    dischargeable: every `toΦ`/`toΨ` name is listed by `toTranslateEnv.usedNames`. -/
theorem coreCtx_names_used {cctx : CoreCtx} {nm : String}
    (h : nm ∈ (cctx.toΦ ++ cctx.toΨ).map Prod.fst) :
    (staticUsedNames cctx.toTranslateEnv).contains nm := by
  simp only [staticUsedNames, quantUsedNames, CoreCtx.toTranslateEnv, CoreCtx.declaredNames,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem, decide_eq_true_eq, List.map_nil, List.nil_append, List.mem_append]
  simp only [List.map_append, List.mem_append, CoreCtx.toΦ, CoreCtx.toΨ, List.map_map] at h
  rcases h with (h | h) | (h | h)
  · simp [h]   -- varDecls (free vars + nondet vars)
  · have hΦv : nm ∈ cctx.varDefs.map (·.name) := by
      simpa [Function.comp] using h
    simp [hΦv]
  · simp [h]   -- fnDecls (uninterpreted factory decls)
  · have hΨ : nm ∈ cctx.fnDefs.map (·.name) := by
      simpa [Function.comp] using h
    simp [hΨ]

/-- **Binder-context correspondence** — the `Δ`↔`bvs` resolution bridge. -/
structure BVarCtxCorresponds (uAT : Bool) (Δ : BVarCtx) (bvs : TermVarCtx) : Prop where
  len_eq : Δ.length = bvs.length
  ty_eq : ∀ i (hi : i < Δ.length),
    LExpr.MonoTyIsBase Δ[i] ∧ tyToTermType uAT Δ[i] = (bvs[i]'(by omega)).ty
  nodup : (bvs.map (·.id)).Nodup

/-- A resolved source name is not a binder id — direct from the scoped capture-freedom hypothesis. -/
theorem toΦ_not_captured {Γ : SimpTyCtx} {bvs : TermVarCtx}
    (havoid : ∀ v ∈ bvs, v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst)
    {nm : String} (h : nm ∈ (Γ.Φ ++ Γ.Ψ).map Prod.fst) : nm ∉ bvs.map (·.id) := by
  intro hbv
  obtain ⟨v, hv_mem, hv_id⟩ := List.mem_map.mp hbv
  exact havoid v hv_mem (hv_id ▸ h)

/-- `find?_id_self` for `BVarCtxCorresponds`: from `nodup`. -/
theorem BVarCtxCorresponds.find?_id_self {uAT : Bool} {Δ : BVarCtx} {bvs : TermVarCtx}
    (hbwf : BVarCtxCorresponds uAT Δ bvs) (i : Nat) (hi : i < bvs.length) :
    bvs.find? (fun w => w.id == (bvs[i]'hi).id) = some (bvs[i]'hi) := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, i, hi, rfl, ?_⟩
  intro j hj
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
  intro hcontra
  have hnd := hbwf.nodup
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd
  have hjm : j < (bvs.map (·.id)).length := by simpa using Nat.lt_trans hj hi
  have him : i < (bvs.map (·.id)).length := by simpa using hi
  refine hnd j i hjm him hj ?_
  simp only [List.getElem_map]; exact hcontra

/-! ## Leaf typing lemmas (fvar / predefined-op / user-fn heads) -/

/-- **A free-var head (applied to any number of args) produces a well-sorted term.** -/
theorem fvarHead_typeChecks
    {Γ : SimpTyCtx} {tenv : TranslateEnv} {useArrayTheory : Bool} {Δ : BVarCtx}
    {f : CoreLParams.Identifier} {τ_head : LMonoTy} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Γ.Φ Γ.Ψ Δ (.fvar () f (some τ_head)) acc rty)
    (haccbase : ∀ t ∈ acc, LExpr.MonoTyIsBase t) (hrtybase : LExpr.MonoTyIsBase rty)
    {ufs : UFCtx} {bvs : TermVarCtx} {accSmt : List TermType} {accTms : List Term}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (h_ok : appTranslate useArrayTheory tenv bvs (.fvar () f (some τ_head)) accTms = .ok tm)
    (haccenc : acc.map (tyToTermType useArrayTheory) = accSmt)
    (hrtyenc : tyToTermType useArrayTheory rty = smtRty)
    (hfvar : FNameCtxCorresponds useArrayTheory Γ.Φ ufs)
    (havoid : ∀ v ∈ bvs, v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst)
    : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty := by
  match acc, rty, hspine, haccbase, haccenc, hrtybase, hrtyenc, h_ok with
  | _, _, .fvar f τ acc' rty' hmem hcollect hbase, haccbase, haccenc, hrtybase, hrtyenc, h_ok =>
    have huwf_info := hfvar.fvar_has_uf f.name τ hmem
    rw [hcollect] at huwf_info
    obtain ⟨smtArgTys, smtRty', h_smtArgTys, h_smtRty', h_uf_mem⟩ := huwf_info
    have hacc_eq : accSmt = smtArgTys := haccenc.symm.trans h_smtArgTys.2
    subst hacc_eq
    have hrty_eq0 : smtRty = smtRty' := hrtyenc.symm.trans h_smtRty'.2
    subst hrty_eq0
    have hargs_eq : acc'.map (tyToTermType useArrayTheory) = accSmt := h_smtArgTys.2
    have hrty_eq : tyToTermType useArrayTheory rty' = smtRty := h_smtRty'.2
    simp only [appTranslate, translateAppHead] at h_ok
    have htm := (Except.ok.inj h_ok).symm
    have h_no_capture : f.name ∉ bvs.map (·.id) :=
      toΦ_not_captured (Γ := Γ) havoid
        (by rw [List.map_append]; exact List.mem_append_left _ (List.mem_map_of_mem (f := Prod.fst) hmem))
    subst htm
    rw [hcollect]
    rw [hargs_eq, hrty_eq]
    simp only [Term.typeCheck, h_uf_mem, h_no_capture, h_acc_tc,
      h_smtArgTys.2 ▸ tyToTermTypes_wfSort h_smtArgTys.1,
      h_smtRty'.2 ▸ tyToTermType_wfSort h_smtRty'.1,
      beq_self_eq_true, Bool.and_true, true_and, not_false_iff, if_true]

/-- **Predefined-op head produces a well-sorted term.** -/
theorem predefinedOp_typeChecks
    {tenv : TranslateEnv} {useArrayTheory : Bool}
    {o : CoreLParams.Identifier} {oty : LMonoTy} {acc : List LMonoTy} {rty : LMonoTy}
    (hopty : LExpr.CoreOpHasType (CoreOp.ofString (Core.NameMangling.demangledBaseName o.name)) acc rty)
    (hcol : collectArrowTy oty = (acc, rty))
    (haccbase : ∀ t ∈ acc, LExpr.MonoTyIsBase t) (hrtybase : LExpr.MonoTyIsBase rty)
    {ufs : UFCtx} {bvs : TermVarCtx} {accTms : List Term} {accSmt : List TermType}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (h_ok : appTranslate useArrayTheory tenv bvs (.op () o (some oty)) accTms = .ok tm)
    (haccenc : acc.map (tyToTermType useArrayTheory) = accSmt)
    (hrtyenc : tyToTermType useArrayTheory rty = smtRty)
    : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty := by
  have hacc : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType useArrayTheory) = accSmt :=
    ⟨haccbase, haccenc⟩
  have hrty : LExpr.MonoTyIsBase rty ∧ tyToTermType useArrayTheory rty = smtRty := ⟨hrtybase, hrtyenc⟩
  generalize hcop : CoreOp.ofString (Core.NameMangling.demangledBaseName o.name) = cop at hopty
  have hne : ∀ s, cop ≠ CoreOp.other s := by intro s h; rw [h] at hopty; nomatch hopty
  have hbeq : (Core.NameMangling.demangledBaseName o.name == "Re.Loop") = false := by
    rw [beq_eq_false_iff_ne]; intro hloop
    have hre : CoreOp.ofString "Re.Loop" = CoreOp.re .Loop := by native_decide
    rw [hloop, hre] at hcop; rw [← hcop] at hopty; nomatch hopty
  cases hopty with
  | intNeg =>
    have haccEq : accSmt = [.int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .int := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, hst, h1⟩ := typeCheckArgs_one_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with htm; subst htm
    simp [Term.typeCheck, bind, Except.bind, h1]
  | boolNot =>
    have haccEq : accSmt = [.bool] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, hst, h1⟩ := typeCheckArgs_one_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with htm; subst htm
    simp [Term.typeCheck, bind, Except.bind, h1]
  | intAdd | intSub | intMul | intDiv | intMod =>
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .int := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with htm; subst htm
    simp [Term.typeCheck, bind, Except.bind, h1, h2]
  | intLt | intLe | intGt | intGe =>
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with htm; subst htm
    simp [Term.typeCheck, bind, Except.bind, h1, h2]
  | boolAnd | boolOr | boolImplies | boolEquiv =>
    have haccEq : accSmt = [.bool, .bool] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with htm; subst htm
    simp [Term.typeCheck, bind, Except.bind, h1, h2]

/-- **A name missing the predefined-op table is not `Re.Loop`.** -/
theorem ne_reLoop_of_corePredefinedOpToSMTOp_none {uAT : Bool} {nm : String}
    (h : corePredefinedOpToSMTOp uAT (CoreOp.ofString nm) = none) : nm ≠ "Re.Loop" := by
  intro hloop
  subst hloop
  have hre : CoreOp.ofString "Re.Loop" = CoreOp.re .Loop := by native_decide
  rw [hre] at h
  simp [corePredefinedOpToSMTOp] at h

/-- **User-fn (`.fnOp`) head produces a well-sorted term.** -/
theorem userFnOp_typeChecks
    {Γ : SimpTyCtx} {tenv : TranslateEnv} {useArrayTheory : Bool}
    {o : CoreLParams.Identifier} {oty : LMonoTy} {acc : List LMonoTy} {rty : LMonoTy}
    (hmem : (o.name, oty) ∈ Γ.Ψ)
    (hcollect : collectArrowTy oty = (acc, rty))
    (haccbase : ∀ t ∈ acc, LExpr.MonoTyIsBase t) (hrtybase : LExpr.MonoTyIsBase rty)
    {ufs : UFCtx} {bvs : TermVarCtx} {accSmt : List TermType} {accTms : List Term}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (h_pre_none : corePredefinedOpToSMTOp useArrayTheory
      (CoreOp.ofString (Core.NameMangling.demangledBaseName o.name)) = none)
    (h_dt_none : tenv.datatypeFuns.find? (Core.NameMangling.demangledBaseName o.name) = none)
    (h_ok : appTranslate useArrayTheory tenv bvs (.op () o (some oty)) accTms = .ok tm)
    (haccenc : acc.map (tyToTermType useArrayTheory) = accSmt)
    (hrtyenc : tyToTermType useArrayTheory rty = smtRty)
    (hfn : FNameCtxCorresponds useArrayTheory Γ.Ψ ufs)
    (havoid : ∀ v ∈ bvs, v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst)
    : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty := by
  have hacc : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType useArrayTheory) = accSmt :=
    ⟨haccbase, haccenc⟩
  have hrty : LExpr.MonoTyIsBase rty ∧ tyToTermType useArrayTheory rty = smtRty := ⟨hrtybase, hrtyenc⟩
  have huwf_info := hfn.fvar_has_uf o.name oty hmem
  rw [hcollect] at huwf_info
  obtain ⟨smtArgTys, smtRty', h_smtArgTys, h_smtRty', h_uf_mem⟩ := huwf_info
  have hacc_eq : accSmt = smtArgTys := hacc.2.symm.trans h_smtArgTys.2
  subst hacc_eq
  have hrty_eq0 : smtRty = smtRty' := hrty.2.symm.trans h_smtRty'.2
  subst hrty_eq0
  have hargs_eq : acc.map (tyToTermType useArrayTheory) = accSmt := h_smtArgTys.2
  have hrty_eq : tyToTermType useArrayTheory rty = smtRty := h_smtRty'.2
  have hbeq_loop : (Core.NameMangling.demangledBaseName o.name == "Re.Loop") = false := by
    rw [beq_eq_false_iff_ne]; exact ne_reLoop_of_corePredefinedOpToSMTOp_none h_pre_none
  simp only [appTranslate, translateAppHead, hbeq_loop, Bool.false_eq_true, if_false,
    h_pre_none, h_dt_none] at h_ok
  have htm := (Except.ok.inj h_ok).symm
  have h_no_capture : o.name ∉ bvs.map (·.id) :=
    toΦ_not_captured (Γ := Γ) havoid
      (by rw [List.map_append]; exact List.mem_append_right _ (List.mem_map_of_mem (f := Prod.fst) hmem))
  subst htm
  rw [hcollect]
  rw [hargs_eq, hrty_eq]
  simp only [Term.typeCheck, h_uf_mem, h_no_capture, h_acc_tc,
    h_smtArgTys.2 ▸ tyToTermTypes_wfSort h_smtArgTys.1,
    h_smtRty'.2 ▸ tyToTermType_wfSort h_smtRty'.1,
    beq_self_eq_true, Bool.and_true, true_and, not_false_iff, if_true]

/-! ## Quantifier-case support -/

/-- The SMT quantifier kind emitted by `translate` for a source (Lambda) quantifier kind `k`. -/
def coreQK : Lambda.QuantifierKind → Strata.SMT.QuantifierKind
  | .all => .all
  | .exist => .exist

/-- **`findUnique` postcondition** (`¬ ·.contains` form): the returned name is not in `usedNames`. -/
theorem findUnique_not_mem (base : String) (startSuffix : Nat) (used : Std.HashSet String) :
    ¬ used.contains (Strata.Name.findUnique base startSuffix used) := by
  simp only [Std.HashSet.contains_eq_false_iff_not_mem.mpr
    (Strata.Name.findUnique_not_mem base startSuffix used), Bool.false_eq_true, not_false_eq_true]

/-- `quantUsedNames tenv bvs` contains a name iff it is a binder id OR a static context name. -/
theorem mem_quantUsedNames_iff (tenv : TranslateEnv) (bvs : TermVarCtx) (nm : String) :
    (quantUsedNames tenv bvs).contains nm
      ↔ nm ∈ bvs.map (·.id) ∨ (staticUsedNames tenv).contains nm := by
  simp only [quantUsedNames, staticUsedNames, Std.HashSet.contains_ofList, List.contains_eq_mem,
    decide_eq_true_eq, List.map_nil, List.nil_append, List.mem_append]

/-- The `findUnique`-chosen binder name is fresh for BOTH `bvs` and the static context. -/
theorem findUnique_quant_fresh (tenv : TranslateEnv) (bvs : TermVarCtx) (base : String) (start : Nat) :
    (Strata.Name.findUnique base start (quantUsedNames tenv bvs)) ∉ bvs.map (·.id)
      ∧ ¬ (staticUsedNames tenv).contains (Strata.Name.findUnique base start (quantUsedNames tenv bvs)) := by
  have hfresh := findUnique_not_mem base start (quantUsedNames tenv bvs)
  rw [mem_quantUsedNames_iff] at hfresh
  exact ⟨fun hbv => hfresh (Or.inl hbv), fun hst => hfresh (Or.inr hst)⟩

/-- **`translate` on `.quant`, inverted.** -/
theorem translate_quant_inv {useArrayTheory : Bool} {tenv : TranslateEnv}
    {bvs : TermVarCtx} {qk : Lambda.QuantifierKind} {qname : String} {qty : LMonoTy}
    {qtr qbody : Expression.Expr} {tm : Term}
    (h_ok : translate useArrayTheory tenv bvs (.quant () qk qname (some qty) qtr qbody) = .ok tm) :
    ∃ (base : String) (start : Nat) (trGroups : List (List Term)) (bodyTm : Term),
      let v : TermVar := ⟨Strata.Name.findUnique base start (quantUsedNames tenv bvs),
                          tyToTermType useArrayTheory qty⟩
      translate useArrayTheory tenv (v :: bvs) qbody = .ok bodyTm
      ∧ ((isCoreTriggerListExpr qtr = true
            ∧ translateTriggerGroups useArrayTheory tenv (v :: bvs) qtr [] = .ok trGroups)
         ∨ (∃ tt, isCoreTriggerListExpr qtr = false
            ∧ translate useArrayTheory tenv (v :: bvs) qtr = .ok tt ∧ trGroups = [[tt]]))
      ∧ tm = Strata.SMT.Factory.quant (coreQK qk) v.id v.ty trGroups bodyTm := by
  unfold translate at h_ok
  obtain ⟨base, start, hbs⟩ :
      ∃ base start, (if qname.isEmpty = true then (s!"$__bv{bvs.length}", 1)
        else match Strata.Name.breakDisambiguated qname with | (b, s) => (sanitizeSmtName b, s))
          = (base, start) := ⟨_, _, rfl⟩
  rw [hbs] at h_ok
  simp only at h_ok
  generalize hv : (⟨Strata.Name.findUnique base start (quantUsedNames tenv bvs),
    tyToTermType useArrayTheory qty⟩ : TermVar) = v at *
  split at h_ok
  · rename_i hcond
    cases htg : translateTriggerGroups useArrayTheory tenv (v :: bvs) qtr [] with
    | error e => rw [htg] at h_ok; simp [bind, Except.bind] at h_ok
    | ok trGroups =>
      rw [htg] at h_ok
      simp only [bind, Except.bind] at h_ok
      cases hbodyt : translate useArrayTheory tenv (v :: bvs) qbody with
      | error e => rw [hbodyt] at h_ok; simp at h_ok
      | ok bodyTm =>
        rw [hbodyt] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst hv
        exact ⟨base, start, trGroups, bodyTm, hbodyt, Or.inl ⟨hcond, htg⟩, h_ok.symm⟩
  · rename_i hcond
    cases httr : translate useArrayTheory tenv (v :: bvs) qtr with
    | error e => rw [httr] at h_ok; simp [bind, Except.bind] at h_ok
    | ok tt =>
      rw [httr] at h_ok
      simp only [bind, Except.bind] at h_ok
      cases hbodyt : translate useArrayTheory tenv (v :: bvs) qbody with
      | error e => rw [hbodyt] at h_ok; simp at h_ok
      | ok bodyTm =>
        rw [hbodyt] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst hv
        exact ⟨base, start, [[tt]], bodyTm, hbodyt,
          Or.inr ⟨tt, by simpa using hcond, httr, rfl⟩, h_ok.symm⟩

/-- **Extend the `Δ`↔`bvs` correspondence with a fresh binder.** -/
theorem BVarCtxCorresponds_cons {uAT : Bool} {Δ : BVarCtx} {bvs : TermVarCtx}
    {qty : LMonoTy} {v : TermVar}
    (hbwf : BVarCtxCorresponds uAT Δ bvs)
    (hqbase : LExpr.MonoTyIsBase qty)
    (hty : tyToTermType uAT qty = v.ty)
    (hfresh : v.id ∉ bvs.map (·.id))
    : BVarCtxCorresponds uAT (qty :: Δ) (v :: bvs) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_cons, hbwf.len_eq]
  · intro i hi
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      exact ⟨hqbase, hty⟩
    | succ j =>
      simp only [List.length_cons] at hi
      simp only [List.getElem_cons_succ]
      exact hbwf.ty_eq j (by omega)
  · simp only [List.map_cons, List.nodup_cons]
    exact ⟨hfresh, hbwf.nodup⟩

/-- **A `HasSimpType`-typed trigger expression is never a *structured* trigger spine.** -/
theorem hasSimpType_trigger_bvar
    {Φ : FVarCtx} {Ψ : FnCtx} {Δ : BVarCtx} {uAT : Bool}
    {qtr : Expression.Expr} {τ_tr : LMonoTy}
    (htr : LExpr.HasSimpType Φ Ψ Δ qtr τ_tr)
    (hfnwf : FnNamesNotPredefined Ψ uAT)
    (hics : isCoreTriggerListExpr qtr = true) :
    ∃ i, qtr = .bvar () i := by
  cases htr with
  | bvar i τ hlook hbase => exact ⟨i, rfl⟩
  | const c hbase => simp [isCoreTriggerListExpr] at hics
  | fvarNullary f τ rty hspine => simp [isCoreTriggerListExpr] at hics
  | ite c t τ e hc ht hee => simp [isCoreTriggerListExpr] at hics
  | eq e1 e2 τ hb he1 he2 => simp [isCoreTriggerListExpr] at hics
  | quant qty body k name tr τtr hb htr' hbody => simp [isCoreTriggerListExpr] at hics
  | app fn arg rty hspine =>
    exfalso
    cases hspine with
    | app fn' arg' aty acc rty' harg hrest =>
      cases hrest with
      | fvar f τ acc2 rty2 hmem hcollect hbase => simp [isCoreTriggerListExpr] at hics
      | op o oty acc2 rty2 hcop hcollect => simp [isCoreTriggerListExpr] at hics
      | fnOp o oty acc2 rty2 hmem hnpre hcollect hbase => simp [isCoreTriggerListExpr] at hics
      | app fn'' arg'' aty2 acc2 rty2 harg2 hrest2 =>
        cases hrest2 with
        | app fn3 arg3 aty3 acc3 rty3 harg3 hrest3 => simp [isCoreTriggerListExpr] at hics
        | fvar f τ acc3 rty3 hmem hcollect hbase => simp [isCoreTriggerListExpr] at hics
        | op o oty acc3 rty3 hcop hcollect =>
          generalize hc : CoreOp.ofString (Core.NameMangling.demangledBaseName o.name) = cop at hcop
          cases hcop <;> simp [isCoreTriggerListExpr, hc] at hics
        | fnOp o oty acc3 rty3 hmem hnpre hcollect hbase =>
          have hnone := hfnwf o.name (List.mem_map_of_mem (f := Prod.fst) hmem)
          simp only [isCoreTriggerListExpr] at hics
          cases hd : CoreOp.ofString (Core.NameMangling.demangledBaseName o.name) <;>
            simp_all [corePredefinedOpToSMTOp]

/-- **Reconstruct the naive single-binder quantifier's type-check.** -/
theorem quant_naive_typeCheck {uAT : Bool} {qty : LMonoTy}
    {ufs : UFCtx} {bvs : TermVarCtx} {v : TermVar} {trGroups : List (List Term)} {bodyTm : Term}
    {qk : Strata.SMT.QuantifierKind}
    (hbase : LExpr.MonoTyIsBase qty) (hvty : v.ty = tyToTermType uAT qty)
    (hbodyTm_tc : Term.typeCheck ⟨[], ufs, v :: bvs⟩ bodyTm = .ok .bool)
    (hwftr : Term.wfTriggers ⟨[], ufs, v :: bvs⟩ trGroups = true) :
    Term.typeCheck ⟨[], ufs, bvs⟩ (.quant qk [v] trGroups bodyTm) = .ok .bool := by
  refine Term.typeCheck_quant_ok_iff.mpr ⟨hbodyTm_tc, ?_, hwftr, rfl⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, hvty, tyToTermType_wfSort hbase]

/-! ## Headline mutual TYPING block: `translate` / `appSpine` sort-correctness -/

mutual
/-- **`translate` sort-correctness.** A well-typed source expression translates to a term that SMT-type-
    checks at the encoded sort. Mutually recursive with `appSpine_typeChecks`. -/
theorem translate_typeChecks
    -- ── LExpr (source) side ──
    {Γ : SimpTyCtx} {tenv : TranslateEnv} {useArrayTheory : Bool} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Γ.Φ Γ.Ψ Δ e τ)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx} {smtTy : TermType} {tm : Term}
    (huf : UFCtxWF ufs)
    -- ── correspondence (source ↔ target) ──
    (h_ok : translate useArrayTheory tenv bvs e = .ok tm)
    (hτenc : tyToTermType useArrayTheory τ = smtTy)
    (hfvar : FNameCtxCorresponds useArrayTheory Γ.Φ ufs)
    (hfn : FNameCtxCorresponds useArrayTheory Γ.Ψ ufs)
    (hbwf : BVarCtxCorresponds useArrayTheory Δ bvs)
    (hused : ∀ nm ∈ (Γ.Φ ++ Γ.Ψ).map Prod.fst, (staticUsedNames tenv).contains nm)
    (havoid : ∀ v ∈ bvs, v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst)
    (hfnwf : FnNamesNotPredefined Γ.Ψ useArrayTheory)
    (hdtfree : tenv.datatypeFuns = ∅)
    : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtTy := by
  match e, τ, he, hτenc, h_ok with
  | _, _, .const cst hbase, hτenc, h_ok =>
    have hτbase := hbase
    have hτ : LExpr.MonoTyIsBase _ ∧ tyToTermType useArrayTheory _ = smtTy := ⟨hτbase, hτenc⟩
    cases cst with
    | boolConst b =>
      have htm : tm = .prim (.bool b) := by simp [translate] at h_ok; exact h_ok.symm
      have hsmt : smtTy = .bool := by
        have h2 := hτ.2; simp only [LConst.ty, LMonoTy.bool, tyToTermType] at h2; exact h2.symm
      subst htm; subst hsmt
      simp [Term.typeCheck, TermPrim.typeOf, TermType.isBase]
    | intConst i =>
      have htm : tm = .prim (.int i) := by simp [translate] at h_ok; exact h_ok.symm
      have hsmt : smtTy = .int := by
        have h2 := hτ.2; simp only [LConst.ty, LMonoTy.int, tyToTermType] at h2; exact h2.symm
      subst htm; subst hsmt
      simp [Term.typeCheck, TermPrim.typeOf, TermType.isBase]
    | strConst s =>
      have htm : tm = .prim (.string s) := by simp [translate] at h_ok; exact h_ok.symm
      have hsmt : smtTy = .string := by
        have h2 := hτ.2; simp only [LConst.ty, LMonoTy.string, tyToTermType] at h2; exact h2.symm
      subst htm; subst hsmt
      simp [Term.typeCheck, TermPrim.typeOf, TermType.isBase]
    | bitvecConst n bv =>
      have htm : tm = .prim (.bitvec bv) := by simp [translate] at h_ok; exact h_ok.symm
      have hsmt : smtTy = .bitvec n := by
        have h2 := hτ.2; simp only [LConst.ty, tyToTermType] at h2; exact h2.symm
      subst htm; subst hsmt
      simp [Term.typeCheck, TermPrim.typeOf, TermType.isBase]
    | realConst _ =>
      simp only [LConst.ty, LMonoTy.real] at hbase
      exact absurd hbase not_MonoTyIsBase_real
  | _, _, .bvar i τ' hlook hbase, hτenc, h_ok =>
    have hτbase := hbase
    have hτ : LExpr.MonoTyIsBase _ ∧ tyToTermType useArrayTheory _ = smtTy := ⟨hτbase, hτenc⟩
    unfold translate at h_ok
    split at h_ok <;> simp at h_ok
    rename_i hi; subst h_ok
    simp only [Term.typeCheck]
    split
    · rename_i hmem
      congr 1
      have hi_Δ : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
      have hΔi_eq : Δ[i] = τ' := (List.getElem?_eq_some_iff.mp hlook).2
      have hty_eq := hbwf.ty_eq i hi_Δ
      rw [hΔi_eq] at hty_eq
      exact hty_eq.2.symm.trans hτ.2
    · rename_i hnotmem
      exfalso
      have hi_Δ : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
      have hΔi_eq : Δ[i] = τ' := (List.getElem?_eq_some_iff.mp hlook).2
      have hty_eq := hbwf.ty_eq i hi_Δ
      rw [hΔi_eq] at hty_eq
      exact hnotmem ⟨hbwf.find?_id_self i hi, hty_eq.2 ▸ tyToTermType_wfSort hty_eq.1⟩
  | _, _, .app fn arg rty hspine, hτenc, h_ok =>
    have h_ok' : appTranslate useArrayTheory tenv bvs (.app () fn arg) [] = .ok tm := by
      rw [appTranslate]; rw [translate] at h_ok; exact h_ok
    exact appSpine_typeChecks (hspine := hspine)
      (haccbase := (by simp))
      (huf := huf) (h_ok := h_ok') (h_acc_tc := by simp [Term.typeCheckArgs])
      (haccenc := rfl) (hrtyenc := hτenc)
      (hfvar := hfvar) (hfn := hfn) (hbwf := hbwf) (hused := hused)
      (havoid := havoid) (hfnwf := hfnwf) (hdtfree := hdtfree)
  | _, _, .fvarNullary f τ_f rty hspine, hτenc, h_ok =>
    have h_ok' : appTranslate useArrayTheory tenv bvs (.fvar () f (some τ_f)) [] = .ok tm := by
      rw [translate] at h_ok; exact h_ok
    exact appSpine_typeChecks (hspine := hspine)
      (haccbase := (by simp))
      (huf := huf) (h_ok := h_ok') (h_acc_tc := by simp [Term.typeCheckArgs])
      (haccenc := rfl) (hrtyenc := hτenc)
      (hfvar := hfvar) (hfn := hfn) (hbwf := hbwf) (hused := hused)
      (havoid := havoid) (hfnwf := hfnwf) (hdtfree := hdtfree)
  | _, _, .ite c t τ' e_ hc ht hee, hτenc, h_ok =>
    have hτbase := HasSimpType_base (LExpr.HasSimpType.ite c t τ' e_ hc ht hee)
    have hτ : LExpr.MonoTyIsBase _ ∧ tyToTermType useArrayTheory _ = smtTy := ⟨hτbase, hτenc⟩
    cases hc_ok : translate useArrayTheory tenv bvs c with
    | error _ => rw [translate] at h_ok; rw [hc_ok] at h_ok; simp [bind, Except.bind] at h_ok
    | ok ct =>
      cases ht_ok : translate useArrayTheory tenv bvs t with
      | error _ => rw [translate] at h_ok; rw [hc_ok, ht_ok] at h_ok; simp [bind, Except.bind] at h_ok
      | ok tt =>
        cases he_ok : translate useArrayTheory tenv bvs e_ with
        | error _ => rw [translate] at h_ok; rw [hc_ok, ht_ok, he_ok] at h_ok; simp [bind, Except.bind] at h_ok
        | ok et =>
          have htm : tm = Factory.ite ct tt et := by
            rw [translate] at h_ok
            simp only [hc_ok, ht_ok, he_ok, bind, Except.bind, Except.ok.injEq] at h_ok
            exact h_ok.symm
          subst htm
          have hc_enc : LExpr.MonoTyIsBase (.tcons "bool" []) ∧
              tyToTermType useArrayTheory (.tcons "bool" []) = .bool := ⟨.bool, by simp only [tyToTermType]⟩
          have hctc := translate_typeChecks hc huf hc_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
            (hτenc := hc_enc.2)
          have httc := translate_typeChecks ht huf ht_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
            (hτenc := hτ.2)
          have hetc := translate_typeChecks hee huf he_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
            (hτenc := hτ.2)
          exact Factory_ite_typeCheck (hτ.2 ▸ tyToTermType_isBase hτ.1) hctc httc hetc
  | _, _, .eq e1 e2 τ' hbase he1 he2, hτenc, h_ok =>
    have hsmt : smtTy = .bool := by have h2 := hτenc; simp only [tyToTermType] at h2; exact h2.symm
    subst hsmt
    cases h1_ok : translate useArrayTheory tenv bvs e1 with
    | error _ => rw [translate] at h_ok; rw [h1_ok] at h_ok; simp [bind, Except.bind] at h_ok
    | ok t1 =>
      cases h2_ok : translate useArrayTheory tenv bvs e2 with
      | error _ => rw [translate] at h_ok; rw [h1_ok, h2_ok] at h_ok; simp [bind, Except.bind] at h_ok
      | ok t2 =>
        have htm : tm = Factory.eq t1 t2 := by
          rw [translate] at h_ok
          simp only [h1_ok, h2_ok, bind, Except.bind, Except.ok.injEq] at h_ok
          exact h_ok.symm
        subst htm
        have h1 := translate_typeChecks he1 huf h1_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
          (hτenc := rfl)
        have h2 := translate_typeChecks he2 huf h2_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
          (hτenc := rfl)
        exact Factory_eq_typeCheck (tyToTermType_isBase hbase) h1 h2
  | _, _, .quant qty qbody qk qname qtr qτtr hbase htr hbody, hτenc, h_ok =>
    have hτ_bool : smtTy = .bool := by simp only [tyToTermType] at hτenc; exact hτenc.symm
    subst hτ_bool
    obtain ⟨base, start, trGroups, bodyTm, hbody_ok', htrig, htm⟩ := translate_quant_inv h_ok
    obtain ⟨hv_bvs, hv_static⟩ := findUnique_quant_fresh tenv bvs base start
    have hbwf' : BVarCtxCorresponds useArrayTheory (qty :: Δ)
        (⟨Strata.Name.findUnique base start (quantUsedNames tenv bvs), tyToTermType useArrayTheory qty⟩ :: bvs) :=
      BVarCtxCorresponds_cons hbwf hbase rfl hv_bvs
    have hv_ctx : (Strata.Name.findUnique base start (quantUsedNames tenv bvs))
        ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst := fun hmem => hv_static (hused _ hmem)
    have havoid' : ∀ v ∈ (⟨Strata.Name.findUnique base start (quantUsedNames tenv bvs),
        tyToTermType useArrayTheory qty⟩ : TermVar) :: bvs,
        v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hv_ctx
      · exact havoid w hw
    have hbool_enc : LExpr.MonoTyIsBase (.tcons "bool" []) ∧
        tyToTermType useArrayTheory (.tcons "bool" []) = .bool := ⟨.bool, by simp only [tyToTermType]⟩
    have hbodyTm_tc := translate_typeChecks hbody huf hbody_ok'
      hfvar hfn hbwf' hused havoid' hfnwf hdtfree (hτenc := hbool_enc.2)
    have hwftr : Term.wfTriggers ⟨[], ufs,
        ⟨Strata.Name.findUnique base start (quantUsedNames tenv bvs), tyToTermType useArrayTheory qty⟩ :: bvs⟩
        trGroups = true := by
      rcases htrig with ⟨hics, hgroups⟩ | ⟨tt, hics, httt, hgeq⟩
      · obtain ⟨i, hbv⟩ := hasSimpType_trigger_bvar htr hfnwf hics
        rw [hbv] at hgroups
        simp only [translateTriggerGroups, Except.ok.injEq] at hgroups
        subst hgroups
        rfl
      · subst hgeq
        have htt_tc := translate_typeChecks htr huf httt
          hfvar hfn hbwf' hused havoid' hfnwf hdtfree
          (hτenc := rfl)
        simp [Term.wfTriggers, Term.typeCheckAll, htt_tc, Except.toOption]
    rw [htm]
    exact (Factory.quant_typeCheck (coreQK qk) _ _ trGroups bodyTm).mpr
      (quant_naive_typeCheck (qk := coreQK qk) (uAT := useArrayTheory) hbase rfl hbodyTm_tc hwftr)
  termination_by structural he

/-- **App-spine sort-correctness** (companion to `translate_typeChecks`). -/
theorem appSpine_typeChecks
    -- ── LExpr (source) side ──
    {Γ : SimpTyCtx} {tenv : TranslateEnv} {useArrayTheory : Bool} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Γ.Φ Γ.Ψ Δ e acc rty)
    (haccbase : ∀ t ∈ acc, LExpr.MonoTyIsBase t)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx} {accSmt : List TermType} {accTms : List Term}
    {smtRty : TermType} {tm : Term}
    (huf : UFCtxWF ufs)
    (h_ok : appTranslate useArrayTheory tenv bvs e accTms = .ok tm)
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    -- ── correspondence (source ↔ target) ──
    (haccenc : acc.map (tyToTermType useArrayTheory) = accSmt)
    (hrtyenc : tyToTermType useArrayTheory rty = smtRty)
    (hfvar : FNameCtxCorresponds useArrayTheory Γ.Φ ufs)
    (hfn : FNameCtxCorresponds useArrayTheory Γ.Ψ ufs)
    (hbwf : BVarCtxCorresponds useArrayTheory Δ bvs)
    (hused : ∀ nm ∈ (Γ.Φ ++ Γ.Ψ).map Prod.fst, (staticUsedNames tenv).contains nm)
    (havoid : ∀ v ∈ bvs, v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst)
    (hfnwf : FnNamesNotPredefined Γ.Ψ useArrayTheory)
    (hdtfree : tenv.datatypeFuns = ∅)
    : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty := by
  match e, acc, rty, hspine, haccbase, haccenc, hrtyenc, h_ok with
  | _, _, _, .app fn arg aty acc' rty' harg hrest, haccbase, haccenc, hrtyenc, h_ok =>
    have hrtybase := AppSpine_base (LExpr.AppSpine.app fn arg aty acc' rty' harg hrest)
    rw [appTranslate] at h_ok
    cases h_arg_ok : translate useArrayTheory tenv bvs arg with
    | error e => rw [h_arg_ok] at h_ok; simp [bind, Except.bind] at h_ok
    | ok argt =>
      rw [h_arg_ok] at h_ok; simp only [bind, Except.bind] at h_ok
      have hbase_arg : LExpr.MonoTyIsBase aty := HasSimpType_base harg
      have h_argt := translate_typeChecks harg huf h_arg_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
        (hτenc := rfl)
      have hacc'base : ∀ t ∈ (aty :: acc'), LExpr.MonoTyIsBase t := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact hbase_arg
        · exact haccbase t ht'
      have hacc'enc : (aty :: acc').map (tyToTermType useArrayTheory)
          = tyToTermType useArrayTheory aty :: accSmt := by simp only [List.map_cons, haccenc]
      have h_acc_tc' : Term.typeCheckArgs ⟨[], ufs, bvs⟩ (argt :: accTms) (tyToTermType useArrayTheory aty :: accSmt) = true := by
        simp only [Term.typeCheckArgs, h_argt]
        simp [h_acc_tc, BEq.beq]
      exact appSpine_typeChecks (hspine := hrest)
        (haccbase := hacc'base)
        (huf := huf) (h_ok := h_ok) (h_acc_tc := h_acc_tc')
        (haccenc := hacc'enc) (hrtyenc := hrtyenc)
        (hfvar := hfvar) (hfn := hfn) (hbwf := hbwf) (hused := hused)
        (havoid := havoid) (hfnwf := hfnwf) (hdtfree := hdtfree)
  | _, _, _, .fvar f τ acc' rty' hmem hcollect hbase, haccbase, haccenc, hrtyenc, h_ok =>
    have hrtybase := hbase
    exact fvarHead_typeChecks (Δ := Δ) (LExpr.AppSpine.fvar f τ acc' rty' hmem hcollect hbase)
      h_acc_tc h_ok hfvar havoid
      (haccbase := haccbase) (haccenc := haccenc) (hrtybase := hrtybase) (hrtyenc := hrtyenc)
  | _, _, _, .op o oty acc' rty' hopc hcollect, haccbase, haccenc, hrtyenc, h_ok =>
    have hrtybase := AppSpine_base (@LExpr.AppSpine.op Γ.Φ Γ.Ψ Δ o oty acc' rty' hopc hcollect)
    exact predefinedOp_typeChecks hopc hcollect h_acc_tc h_ok
      (haccbase := haccbase) (haccenc := haccenc) (hrtybase := hrtybase) (hrtyenc := hrtyenc)
  | _, _, _, .fnOp o oty acc' rty' hmem hnpre hcollect hbase, haccbase, haccenc, hrtyenc, h_ok =>
    have hrtybase := hbase
    have hmem_name : o.name ∈ Γ.Ψ.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hmem
    exact userFnOp_typeChecks hmem hcollect h_acc_tc (hfnwf o.name hmem_name) (by rw [hdtfree]; rfl)
      h_ok hfn havoid
      (haccbase := haccbase) (haccenc := haccenc) (hrtybase := hrtybase) (hrtyenc := hrtyenc)
  termination_by structural hspine
end

/-! ## STATEMENT-A well-formedness preservation: `translateQuery` on a well-formed,
hygiene-satisfying `CoreCtx` yields a well-formed `SMTQuery` (`SMTQuery.WF`).
-/

/-! ## `Except`-bind and `mapM` support (API-agnostic) -/

theorem bind_ok_inv {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {z : β}
    (h : (x >>= f) = .ok z) : ∃ y, x = .ok y ∧ f y = .ok z := by
  cases hx : x with
  | error e => rw [hx] at h; simp [bind, Except.bind] at h
  | ok y => rw [hx] at h; simp only [bind, Except.bind] at h; exact ⟨y, rfl, h⟩

theorem mapM_mem {ε α β : Type} [Inhabited ε] (l : List α) (f : α → Except ε β)
    {bs : List β} (h : l.mapM f = .ok bs) :
    ∀ b ∈ bs, ∃ e ∈ l, f e = .ok b := by
  induction l generalizing bs with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; intro b hb; simp at hb
  | cons hd tl ih =>
    rw [List.mapM_cons] at h
    obtain ⟨b0, hb0, h⟩ := bind_ok_inv h
    obtain ⟨bs', hbs', h⟩ := bind_ok_inv h
    have hbs : bs = b0 :: bs' := by
      simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm
    subst hbs
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hd, by simp, hb0⟩
    · obtain ⟨e, he, hfe⟩ := ih hbs' b hb; exact ⟨e, by simp [he], hfe⟩

/-- Positional map-transfer through a successful `mapM`: if every successful `F a = .ok b` maps a
    result under `g` to the same thing `h` maps the input to, the whole result list maps under `g` to
    the input list mapped under `h`. Used to reconstruct the emitted UF chunks from the source lists. -/
theorem mapM_map_eq {ε α β γ : Type} [Inhabited ε] {F : α → Except ε β} {g : β → γ} {h : α → γ} :
    ∀ {l : List α} {bs : List β}, l.mapM F = .ok bs →
      (∀ a b, F a = .ok b → g b = h a) → bs.map g = l.map h := by
  intro l
  induction l with
  | nil => intro bs hmap _; simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmap; subst hmap; simp
  | cons a as ih =>
    intro bs hmap hstep
    rw [List.mapM_cons] at hmap
    obtain ⟨b, hb, hmap⟩ := bind_ok_inv hmap
    obtain ⟨bs', hbs', hmap⟩ := bind_ok_inv hmap
    simp only [pure, Except.pure, Except.ok.injEq] at hmap
    subst hmap
    simp only [List.map_cons]
    rw [hstep a b hb, ih hbs' hstep]

theorem translateList_mem {uAT : Bool} {tenv : TranslateEnv}
    {es : List Expression.Expr} {ts : List Term}
    (h : translateList uAT tenv es = .ok ts) :
    ∀ t ∈ ts, ∃ e ∈ es, translate uAT tenv [] e = .ok t := by
  unfold translateList at h
  exact mapM_mem es (fun e => translate uAT tenv [] e) h

theorem translateList_cons {uAT : Bool} {tenv : TranslateEnv}
    {hd : Expression.Expr} {tl : List Expression.Expr} {ts : List Term}
    (h : translateList uAT tenv (hd :: tl) = .ok ts) :
    ∃ t1 rest, translate uAT tenv [] hd = .ok t1 ∧
      translateList uAT tenv tl = .ok rest ∧ ts = t1 :: rest := by
  unfold translateList at h ⊢
  rw [List.mapM_cons] at h
  obtain ⟨t1, ht1, h⟩ := bind_ok_inv h
  obtain ⟨rest, hrest, h⟩ := bind_ok_inv h
  refine ⟨t1, rest, ht1, hrest, ?_⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm

theorem translateList_len {uAT : Bool} {tenv : TranslateEnv} :
    ∀ {es : List Expression.Expr} {ts : List Term},
      translateList uAT tenv es = .ok ts → ts.length = es.length := by
  intro es
  induction es with
  | nil =>
    intro ts h
    unfold translateList at h; simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [← h]
  | cons hd tl ih =>
    intro ts h
    obtain ⟨t1, rest, _, hrest, hts⟩ := translateList_cons h
    rw [hts]; simp only [List.length_cons]; rw [ih hrest]

theorem translateList_getElem {uAT : Bool} {tenv : TranslateEnv} :
    ∀ (es : List Expression.Expr) (ts : List Term),
      translateList uAT tenv es = .ok ts →
      ∀ (i : Nat) (hie : i < es.length) (hit : i < ts.length),
        translate uAT tenv [] (es.get ⟨i, hie⟩) = .ok (ts.get ⟨i, hit⟩) := by
  intro es
  induction es with
  | nil => intro ts _ i hie _; simp at hie
  | cons hd tl ih =>
    intro ts h i hie hit
    obtain ⟨t1, rest, ht1, hrest, hts⟩ := translateList_cons h
    subst hts
    cases i with
    | zero => exact ht1
    | succ j =>
      simp only [List.get_cons_succ]
      have hje : j < tl.length := by simp only [List.length_cons] at hie; omega
      have hjt : j < rest.length := by simp only [List.length_cons] at hit; omega
      exact ih rest hrest j hje hjt

theorem distinctFold_mem {uAT : Bool} {tenv : TranslateEnv}
    {ds : List (List Expression.Expr)} {dts : List Term}
    (h : ds.mapM (fun es => do
        let ts ← translateList uAT tenv es
        .ok (Term.app (Op.core Op.Core.distinct) ts TermType.bool)) = .ok dts) :
    ∀ t ∈ dts, ∃ es ∈ ds, ∃ ts,
      translateList uAT tenv es = .ok ts ∧
      t = Term.app (Op.core Op.Core.distinct) ts TermType.bool := by
  intro t ht
  obtain ⟨es, hes, hstep⟩ := mapM_mem ds _ h t ht
  obtain ⟨ts, hts, hstep⟩ := bind_ok_inv hstep
  refine ⟨es, hes, ts, hts, ?_⟩
  simp only [Except.ok.injEq] at hstep; exact hstep.symm

/-! ## Arrow / encoding lemmas -/

/-- `mkArrow'` is the right-fold of `arrow`. -/
theorem mkArrow'_eq_foldr (r : LMonoTy) (as : List LMonoTy) :
    LMonoTy.mkArrow' r as = List.foldr LMonoTy.arrow r as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [LMonoTy.mkArrow', List.foldr_cons, ih]

/-- `collectArrowTy` inverts `mkArrow'` at a base return type. -/
theorem collectArrowTy_mkArrow' {r : LMonoTy} {as : List LMonoTy}
    (hr : LExpr.MonoTyIsBase r) : collectArrowTy (LMonoTy.mkArrow' r as) = (as, r) := by
  rw [mkArrow'_eq_foldr]
  induction as with
  | nil => cases hr <;> rfl
  | cons a as ih =>
    rw [List.foldr_cons]
    rw [show collectArrowTy (LMonoTy.arrow a (List.foldr LMonoTy.arrow r as))
          = (a :: (collectArrowTy (List.foldr LMonoTy.arrow r as)).1,
             (collectArrowTy (List.foldr LMonoTy.arrow r as)).2) from rfl, ih]

/-- `collectArrowTy` of a base type is `([], τ)`. -/
theorem collectArrowTy_base {τ : LMonoTy} (h : LExpr.MonoTyIsBase τ) :
    collectArrowTy τ = ([], τ) := by cases h <;> rfl

/-- The UF signature a source `(name, type)` pair encodes to under `tyToTermType uAT`. -/
def encodeUF (uAT : Bool) (p : String × LMonoTy) : UF :=
  ⟨p.1, (collectArrowTy p.2).1.map (tyToTermType uAT), tyToTermType uAT (collectArrowTy p.2).2⟩

/-! ## `lookupUF` on appends -/

theorem lookupUF_append_left' {ufs extra : UFCtx} {name : String}
    (h : (lookupUF ufs name).isSome) : lookupUF (ufs ++ extra) name = lookupUF ufs name := by
  simp only [lookupUF, List.find?_append]
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
  simp only [lookupUF] at hu
  rw [hu]; rfl

theorem lookupUF_append_fresh {ufs : UFCtx} {uf : UF} {name : String}
    (hfresh : name ∉ ufs.map (·.id)) (hid : uf.id = name) :
    lookupUF (ufs ++ [uf]) name = some uf := by
  simp only [lookupUF, List.find?_append]
  have hnone : ufs.find? (·.id == name) = none := by
    rw [List.find?_eq_none]
    intro x hx heq
    rw [beq_iff_eq] at heq
    exact hfresh (heq ▸ List.mem_map_of_mem (f := (·.id)) hx)
  rw [hnone, Option.none_or]
  simp only [List.find?_cons, hid, beq_self_eq_true]

/-! ## `FNameCtxCorresponds` construction / weakening -/

theorem FNameCtxCorresponds_nil {uAT : Bool} {ufs : UFCtx} : FNameCtxCorresponds uAT [] ufs :=
  ⟨fun name τ h => by simp at h, fun name τ uf h => by simp at h, fun name τ uf h => by simp at h⟩

/-- Downward monotone in the source context: restrict to a sub-context. -/
theorem FNameCtxCorresponds.mono_sub {uAT : Bool} {Φ Φ' : FNameCtx} {ufs : UFCtx}
    (h : FNameCtxCorresponds uAT Φ' ufs) (hsub : Φ ⊆ Φ') : FNameCtxCorresponds uAT Φ ufs :=
  ⟨fun name τ hmem => h.fvar_resolves name τ (hsub hmem),
   fun name τ uf hmem hlk => h.args_eq name τ uf (hsub hmem) hlk,
   fun name τ uf hmem hlk => h.out_eq name τ uf (hsub hmem) hlk⟩

/-- Appending UFs on the right preserves a correspondence: every source name already resolves inside the
    left part, so the append never changes the first match. -/
theorem FNameCtxCorresponds.append_rightList {uAT : Bool} {Φ : FNameCtx} {ufs extra : UFCtx}
    (h : FNameCtxCorresponds uAT Φ ufs) : FNameCtxCorresponds uAT Φ (ufs ++ extra) := by
  refine ⟨?_, ?_, ?_⟩
  · intro name τ hmem
    rw [lookupUF_append_left' (h.fvar_resolves name τ hmem)]
    exact h.fvar_resolves name τ hmem
  · intro name τ uf hmem hlk
    rw [lookupUF_append_left' (h.fvar_resolves name τ hmem)] at hlk
    exact h.args_eq name τ uf hmem hlk
  · intro name τ uf hmem hlk
    rw [lookupUF_append_left' (h.fvar_resolves name τ hmem)] at hlk
    exact h.out_eq name τ uf hmem hlk

/-- Extend a correspondence by one aligned entry appended on the right (`nm` must be fresh in `ufs`). -/
theorem FNameCtxCorresponds.snoc_eq {uAT : Bool} {Ψ : FNameCtx} {ufs : UFCtx}
    (h : FNameCtxCorresponds uAT Ψ ufs) {nm : String} {τ : LMonoTy} {uf : UF}
    (hid : uf.id = nm)
    (hargs : (∀ t ∈ (collectArrowTy τ).1, LExpr.MonoTyIsBase t)
      ∧ (collectArrowTy τ).1.map (tyToTermType uAT) = uf.args)
    (hout : LExpr.MonoTyIsBase (collectArrowTy τ).2 ∧ tyToTermType uAT (collectArrowTy τ).2 = uf.out)
    (hfresh : nm ∉ ufs.map (·.id)) :
    FNameCtxCorresponds uAT (Ψ ++ [(nm, τ)]) (ufs ++ [uf]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro name τ0 hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · rw [lookupUF_append_left' (h.fvar_resolves name τ0 hmem)]
      exact h.fvar_resolves name τ0 hmem
    · rw [List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
      rw [lookupUF_append_fresh hfresh hid]; rfl
  · intro name τ0 uf' hmem hlk
    rcases List.mem_append.mp hmem with hmem | hmem
    · rw [lookupUF_append_left' (h.fvar_resolves name τ0 hmem)] at hlk
      exact h.args_eq name τ0 uf' hmem hlk
    · rw [List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
      rw [lookupUF_append_fresh hfresh hid] at hlk
      obtain rfl := Option.some.inj hlk
      exact hargs
  · intro name τ0 uf' hmem hlk
    rcases List.mem_append.mp hmem with hmem | hmem
    · rw [lookupUF_append_left' (h.fvar_resolves name τ0 hmem)] at hlk
      exact h.out_eq name τ0 uf' hmem hlk
    · rw [List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hmem
      rw [lookupUF_append_fresh hfresh hid] at hlk
      obtain rfl := Option.some.inj hlk
      exact hout

/-- With nodup ids and pointwise-aligned names, `lookupUF` at the `i`-th name returns the `i`-th UF. -/
theorem lookupUF_of_pointwise {ufs : UFCtx} {Ψ : FNameCtx}
    (hids : ufs.map (·.id) = Ψ.map Prod.fst) (hnd : (ufs.map (·.id)).Nodup)
    {i : Nat} (hiΨ : i < Ψ.length) (hiu : i < ufs.length) :
    lookupUF ufs (Ψ[i]'hiΨ).1 = some (ufs[i]'hiu) := by
  have hname : (ufs[i]'hiu).id = (Ψ[i]'hiΨ).1 := by
    have h : (ufs.map (·.id))[i]? = (Ψ.map Prod.fst)[i]? := by rw [hids]
    rw [List.getElem?_eq_getElem (by simpa using hiu), List.getElem?_eq_getElem (by simpa using hiΨ)] at h
    rw [List.getElem_map, List.getElem_map] at h
    exact Option.some.inj h
  unfold lookupUF
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by rw [hname]; exact beq_self_eq_true _, i, hiu, rfl, ?_⟩
  intro j hj
  have hju : j < ufs.length := Nat.lt_trans hj hiu
  have hnd2 := hnd
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd2
  have hjm : j < (ufs.map (·.id)).length := by simpa using hju
  have him : i < (ufs.map (·.id)).length := by simpa using hiu
  have hne := hnd2 j i hjm him hj
  rw [List.getElem_map, List.getElem_map] at hne
  show (!((ufs[j]'hju).id == (Ψ[i]'hiΨ).1)) = true
  rw [Bool.not_eq_true', beq_eq_false_iff_ne]
  exact hname ▸ hne

/-- Build a correspondence from pointwise-aligned ids and per-index signature encodings. -/
theorem FNameCtxCorresponds.of_pointwise {uAT : Bool} {Ψ : FNameCtx} {ufs : UFCtx}
    (hids : ufs.map (·.id) = Ψ.map Prod.fst) (hnd : (ufs.map (·.id)).Nodup)
    (hsig : ∀ i (hiΨ : i < Ψ.length) (hiu : i < ufs.length),
        ((∀ t ∈ (collectArrowTy (Ψ[i]'hiΨ).2).1, LExpr.MonoTyIsBase t)
          ∧ (collectArrowTy (Ψ[i]'hiΨ).2).1.map (tyToTermType uAT) = (ufs[i]'hiu).args) ∧
        (LExpr.MonoTyIsBase (collectArrowTy (Ψ[i]'hiΨ).2).2
          ∧ tyToTermType uAT (collectArrowTy (Ψ[i]'hiΨ).2).2 = (ufs[i]'hiu).out)) :
    FNameCtxCorresponds uAT Ψ ufs := by
  have hlen : ufs.length = Ψ.length := by
    have := congrArg List.length hids; simpa only [List.length_map] using this
  refine ⟨?_, ?_, ?_⟩
  · intro name τ hmem
    obtain ⟨i, hiΨ, hget⟩ := List.getElem_of_mem hmem
    have hiu : i < ufs.length := by rw [hlen]; exact hiΨ
    have hlk := lookupUF_of_pointwise hids hnd hiΨ hiu
    have hname : (Ψ[i]'hiΨ).1 = name := by rw [hget]
    rw [hname] at hlk; rw [hlk]; rfl
  · intro name τ uf hmem hlk
    obtain ⟨i, hiΨ, hget⟩ := List.getElem_of_mem hmem
    have hiu : i < ufs.length := by rw [hlen]; exact hiΨ
    have hlk0 := lookupUF_of_pointwise hids hnd hiΨ hiu
    have hname : (Ψ[i]'hiΨ).1 = name := by rw [hget]
    have hτ : (Ψ[i]'hiΨ).2 = τ := by rw [hget]
    rw [hname] at hlk0; rw [hlk0] at hlk
    obtain rfl := Option.some.inj hlk
    have := (hsig i hiΨ hiu).1; rw [hτ] at this; exact this
  · intro name τ uf hmem hlk
    obtain ⟨i, hiΨ, hget⟩ := List.getElem_of_mem hmem
    have hiu : i < ufs.length := by rw [hlen]; exact hiΨ
    have hlk0 := lookupUF_of_pointwise hids hnd hiΨ hiu
    have hname : (Ψ[i]'hiΨ).1 = name := by rw [hget]
    have hτ : (Ψ[i]'hiΨ).2 = τ := by rw [hget]
    rw [hname] at hlk0; rw [hlk0] at hlk
    obtain rfl := Option.some.inj hlk
    have := (hsig i hiΨ hiu).2; rw [hτ] at this; exact this

/-- A source context mapped to its `encodeUF` images corresponds to itself. -/
theorem FNameCtxCorresponds.of_map_encode {uAT : Bool} {Γ : FNameCtx}
    (hbase : ∀ p ∈ Γ, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2)
    (hnd : (Γ.map Prod.fst).Nodup) :
    FNameCtxCorresponds uAT Γ (Γ.map (encodeUF uAT)) := by
  have hids : (Γ.map (encodeUF uAT)).map (·.id) = Γ.map Prod.fst := by
    rw [List.map_map]; exact List.map_congr_left (fun p _ => rfl)
  apply FNameCtxCorresponds.of_pointwise hids (by rw [hids]; exact hnd)
  intro i hiΓ hiu
  have hb := hbase (Γ[i]'hiΓ) (List.getElem_mem hiΓ)
  rw [List.getElem_map]
  exact ⟨⟨hb.1, rfl⟩, ⟨hb.2, rfl⟩⟩

/-! ## `UFCtxWF` on prefixes + distinct type-checking -/

theorem UFCtxWF.of_append_left {a b : UFCtx} (h : UFCtxWF (a ++ b)) : UFCtxWF a := by
  refine ⟨?_, ?_⟩
  · have := h.uf_nodup; rw [List.map_append] at this; exact (List.nodup_append.mp this).1
  · intro n
    have := h.no_reserved n; rw [List.map_append] at this
    exact fun hmem => this (List.mem_append_left _ hmem)

/-! ## Base-typedness of definition signatures, from `CoreCtx.WF`'s order-threaded typings -/

theorem FnDefsWF.mem_retBase {Ψ : FnCtx} {fds : List FnDef} (h : FnDefsWF Ψ fds) :
    ∀ d ∈ fds, LExpr.MonoTyIsBase d.retTy := by
  induction h with
  | nil => intro d hd; simp at hd
  | @cons Ψ d rest hty _ _ _ _ ih =>
    intro d' hd'
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact HasSimpType_base hty
    · exact ih d' hd'

/-- Each `fnDef`'s argument types are base — extracted from the per-`cons` `args_base` field. -/
theorem FnDefsWF.mem_argsBase {Ψ : FnCtx} {fds : List FnDef} (h : FnDefsWF Ψ fds) :
    ∀ d ∈ fds, ∀ t ∈ d.argTys, LExpr.MonoTyIsBase t := by
  induction h with
  | nil => intro d hd; simp at hd
  | @cons Ψ d rest _ hargs _ _ _ ih =>
    intro d' hd'
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact hargs
    · exact ih d' hd'

theorem VarDefsWF.mem_tyBase {Ψ : FnCtx} {Φ : FVarCtx} {vds : List VarDef} (h : VarDefsWF Ψ Φ vds) :
    ∀ v ∈ vds, LExpr.MonoTyIsBase v.ty := by
  induction h with
  | nil => intro v hv; simp at hv
  | @cons Φ v rest hty _ ih =>
    intro v' hv'
    rcases List.mem_cons.mp hv' with rfl | hv'
    · exact HasSimpType_base hty
    · exact ih v' hv'

/-- The SMT parameter types of a `define-fun` are the encodings of its source arg types. -/
theorem fnDefSmtParams_map_ty (uAT : Bool) (d : FnDef) :
    (fnDefSmtParams uAT d).map (·.ty) = d.argTys.map (tyToTermType uAT) := by
  simp only [fnDefSmtParams, FnDef.argTys, List.map_map]
  exact List.map_congr_left (fun p _ => rfl)

/-! ## `translateQuery` structural inversion -/

theorem translateQuery_inv {uAT : Bool}
    {cctx : CoreCtx} {goal : Expression.Expr} {q : SMTQuery}
    (henc : translateQuery uAT cctx goal = .ok q) :
    q.fnDecls = cctx.fnDecls.map (encodeUF uAT) ∧
    q.varDecls = cctx.varDecls.map (encodeUF uAT) ∧
    cctx.fnDefs.mapM (fun d => do
        let bodyTm ← translate uAT cctx.toTranslateEnv (fnDefSmtParams uAT d) d.body
        .ok ({ id := d.name, args := fnDefSmtParams uAT d, out := tyToTermType uAT d.retTy, body := bodyTm } : IF))
      = .ok q.fnDefs ∧
    cctx.varDefs.mapM (fun v => do
        let bodyTm ← translate uAT cctx.toTranslateEnv [] v.body
        .ok ({ id := v.name, args := [], out := tyToTermType uAT v.ty, body := bodyTm } : IF))
      = .ok q.varDefs ∧
    translateList uAT cctx.toTranslateEnv cctx.fnAxioms = .ok q.fnAxioms ∧
    translate uAT cctx.toTranslateEnv [] goal = .ok q.obl := by
  unfold translateQuery at henc
  obtain ⟨r1, h1, henc⟩ := bind_ok_inv henc
  obtain ⟨r2, h2, henc⟩ := bind_ok_inv henc
  obtain ⟨r3, h3, henc⟩ := bind_ok_inv henc
  obtain ⟨r4, h4, henc⟩ := bind_ok_inv henc
  obtain ⟨r5, h5, henc⟩ := bind_ok_inv henc
  obtain ⟨r6, h6, henc⟩ := bind_ok_inv henc
  have hq := Except.ok.inj henc
  subst hq
  refine ⟨?_, ?_, h1, h2, h3, h6⟩
  · exact List.map_congr_left (fun p _ => rfl)
  · exact List.map_congr_left (fun p _ => rfl)

/-- The `Ψ`-half of `q.ufs` is exactly the `encodeUF`-image of `cctx.toΨ`. -/
theorem tq_toΨ_map {uAT : Bool}
    {cctx : CoreCtx} {goal : Expression.Expr} {q : SMTQuery}
    (henc : translateQuery uAT cctx goal = .ok q)
    (hretBase : ∀ d ∈ cctx.fnDefs, LExpr.MonoTyIsBase d.retTy) :
    cctx.toΨ.map (encodeUF uAT) = q.fnDecls ++ q.fnDefs.map IF.toUF := by
  obtain ⟨hfnDecls, _, hfnDefsMap, _⟩ := translateQuery_inv henc
  rw [CoreCtx.toΨ, List.map_append, ← hfnDecls]
  congr 1
  rw [List.map_map,
    mapM_map_eq hfnDefsMap (g := IF.toUF)
      (h := fun d => (⟨d.name, (fnDefSmtParams uAT d).map (·.ty), tyToTermType uAT d.retTy⟩ : UF))
      (by
        intro d b hb
        obtain ⟨bodyTm, _, heq⟩ := bind_ok_inv hb
        obtain rfl := Except.ok.inj heq
        rfl)]
  apply List.map_congr_left
  intro d hd
  show encodeUF uAT (d.name, LMonoTy.mkArrow' d.retTy d.argTys)
      = ⟨d.name, (fnDefSmtParams uAT d).map (·.ty), tyToTermType uAT d.retTy⟩
  unfold encodeUF
  rw [collectArrowTy_mkArrow' (hretBase d hd), fnDefSmtParams_map_ty]

/-- The `Φ`-half of `q.ufs` is exactly the `encodeUF`-image of `cctx.toΦ`. -/
theorem tq_toΦ_map {uAT : Bool}
    {cctx : CoreCtx} {goal : Expression.Expr} {q : SMTQuery}
    (henc : translateQuery uAT cctx goal = .ok q)
    (hvarBase : ∀ v ∈ cctx.varDefs, LExpr.MonoTyIsBase v.ty) :
    cctx.toΦ.map (encodeUF uAT) = q.varDecls ++ q.varDefs.map IF.toUF := by
  obtain ⟨_, hvarDecls, _, hvarDefsMap, _⟩ := translateQuery_inv henc
  rw [CoreCtx.toΦ, List.map_append, ← hvarDecls]
  congr 1
  rw [List.map_map,
    mapM_map_eq hvarDefsMap (g := IF.toUF)
      (h := fun v => (⟨v.name, [], tyToTermType uAT v.ty⟩ : UF))
      (by
        intro v b hb
        obtain ⟨bodyTm, _, heq⟩ := bind_ok_inv hb
        obtain rfl := Except.ok.inj heq
        rfl)]
  apply List.map_congr_left
  intro v hv
  show encodeUF uAT (v.name, v.ty) = ⟨v.name, [], tyToTermType uAT v.ty⟩
  unfold encodeUF
  rw [collectArrowTy_base (hvarBase v hv)]
  rfl

/-- `q.ufs` is the `encodeUF`-image of the full source name context `toΨ ++ toΦ`. -/
theorem tq_ufs_eq {uAT : Bool}
    {cctx : CoreCtx} {goal : Expression.Expr} {q : SMTQuery}
    (henc : translateQuery uAT cctx goal = .ok q)
    (hretBase : ∀ d ∈ cctx.fnDefs, LExpr.MonoTyIsBase d.retTy)
    (hvarBase : ∀ v ∈ cctx.varDefs, LExpr.MonoTyIsBase v.ty) :
    q.ufs = (cctx.toΨ ++ cctx.toΦ).map (encodeUF uAT) := by
  rw [List.map_append, tq_toΨ_map henc hretBase, tq_toΦ_map henc hvarBase, SMTQuery.ufs]
  simp only [List.append_assoc]

/-! ## Empty-binder correspondences + `define-fun` parameter hygiene -/

theorem bwf_nil {uAT : Bool} : BVarCtxCorresponds uAT [] [] where
  len_eq := rfl
  ty_eq := by intro i hi; simp at hi
  nodup := by simp

theorem havoid_nil {Γ : SimpTyCtx} :
    ∀ v ∈ ([] : TermVarCtx), v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst := by
  intro v hv; simp at hv

theorem fnDefParams_bvarCorresponds {uAT : Bool} {d : FnDef}
    (hargsBase : ∀ t ∈ d.argTys, LExpr.MonoTyIsBase t)
    (hpNodup : (d.params.map Prod.fst).Nodup) :
    BVarCtxCorresponds uAT d.argTys (fnDefSmtParams uAT d) where
  len_eq := by simp only [FnDef.argTys, fnDefSmtParams, List.length_map]
  ty_eq := by
    intro i hi
    refine ⟨hargsBase _ (List.getElem_mem hi), ?_⟩
    simp only [FnDef.argTys, fnDefSmtParams, List.getElem_map]
  nodup := by
    have hnd : (fnDefSmtParams uAT d).map (·.id) = d.params.map Prod.fst := by
      simp only [fnDefSmtParams, List.map_map]; exact List.map_congr_left (fun p _ => rfl)
    rw [hnd]; exact hpNodup

/-- Adapter: from a per-`fnDef` params-fresh field `∀ p ∈ d.params, p.1 ∉ Ψ.map .fst`, produce the
    scoped `havoid` shape expected by `translate_typeChecks` at `Γ := ⟨Ψ, []⟩`. -/
theorem fnDefParams_havoid {uAT : Bool} {Ψ : FnCtx} {d : FnDef}
    (hpFresh : ∀ p ∈ d.params, p.1 ∉ Ψ.map Prod.fst) :
    ∀ v ∈ fnDefSmtParams uAT d, v.id ∉ (([] : FVarCtx) ++ Ψ).map Prod.fst := by
  intro v hv
  simp only [fnDefSmtParams, List.mem_map] at hv
  obtain ⟨p, hp_mem, hp⟩ := hv
  have hvid : v.id = p.1 := by rw [← hp]
  simp only [List.nil_append, hvid]
  exact hpFresh p hp_mem

/-! ## Order-threaded `IFsWF` for the `fnDef` preamble (Step 5) -/

/-- The `fnDef` preamble is order-well-typed as an `IFsWF` fold, provided the source `FnDefsWF`
    typing, the base UF-context correspondence, nodup, and the parameter hygiene. -/
theorem IFsWF_of_FnDefsWF {uAT : Bool} {cctx : CoreCtx} {Ψbase : FnCtx} {fds : List FnDef}
    (hwf : FnDefsWF Ψbase fds) :
    ∀ {ufsBase : UFCtx} {ifs : List IF},
      FNameCtxCorresponds uAT Ψbase ufsBase →
      UFCtxWF (ufsBase ++ ifs.map IF.toUF) →
      fds.mapM (fun d => do
          let bodyTm ← translate uAT cctx.toTranslateEnv (fnDefSmtParams uAT d) d.body
          .ok ({ id := d.name, args := fnDefSmtParams uAT d, out := tyToTermType uAT d.retTy, body := bodyTm } : IF))
        = .ok ifs →
      (∀ nm ∈ Ψbase.map Prod.fst, (staticUsedNames cctx.toTranslateEnv).contains nm) →
      (∀ d ∈ fds, (staticUsedNames cctx.toTranslateEnv).contains d.name) →
      FnNamesNotPredefined Ψbase uAT →
      (∀ d ∈ fds, corePredefinedOpToSMTOp uAT (CoreOp.ofString (Core.NameMangling.demangledBaseName d.name)) = none) →
      cctx.toTranslateEnv.datatypeFuns = ∅ →
      IFsWF ufsBase ifs := by
  induction hwf with
  | nil =>
    intro ufsBase ifs _ _ hmap _ _ _ _ _
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmap
    subst hmap; exact IFsWF.nil
  | @cons Ψ d rest hhead hargsBase_d hpNodup_d hpFresh_d htail ih =>
    intro ufsBase ifs hcorr hufwf hmap hused hfdsUsed hnpreBase hfdsNpre hdt
    rw [List.mapM_cons] at hmap
    obtain ⟨f, hf, hmap⟩ := bind_ok_inv hmap
    obtain ⟨ifsRest, hifsRest, hmap⟩ := bind_ok_inv hmap
    simp only [pure, Except.pure, Except.ok.injEq] at hmap
    subst hmap
    obtain ⟨bodyTm, hbody, hfeq⟩ := bind_ok_inv hf
    obtain rfl := Except.ok.inj hfeq
    have hretBaseD := HasSimpType_base hhead
    -- head: `IF.WF`
    have hIFwf : IF.WF ufsBase ⟨d.name, fnDefSmtParams uAT d, tyToTermType uAT d.retTy, bodyTm⟩ := by
      show Term.typeCheck ⟨[], ufsBase, fnDefSmtParams uAT d⟩ bodyTm = .ok (tyToTermType uAT d.retTy)
      exact translate_typeChecks (Γ := ⟨Ψ, []⟩) (tenv := cctx.toTranslateEnv) (useArrayTheory := uAT) (Δ := d.argTys)
        hhead (UFCtxWF.of_append_left hufwf) hbody rfl
        FNameCtxCorresponds_nil hcorr
        (fnDefParams_bvarCorresponds hargsBase_d hpNodup_d)
        (by intro nm hnm; apply hused; simpa using hnm)
        (fnDefParams_havoid (Ψ := Ψ) hpFresh_d)
        hnpreBase hdt
    -- freshness of `d.name` in `ufsBase`
    have hfresh : d.name ∉ ufsBase.map (·.id) := by
      have hnd := hufwf.uf_nodup
      simp only [List.map_append, List.map_cons] at hnd
      exact fun hmem => (List.nodup_append.mp hnd).2.2 d.name hmem d.name List.mem_cons_self rfl
    -- extended correspondence
    have hcorr' : FNameCtxCorresponds uAT (Ψ ++ [(d.name, LMonoTy.mkArrow' d.retTy d.argTys)])
        (ufsBase ++ [(⟨d.name, fnDefSmtParams uAT d, tyToTermType uAT d.retTy, bodyTm⟩ : IF).toUF]) := by
      refine hcorr.snoc_eq rfl ?_ ?_ hfresh
      · rw [collectArrowTy_mkArrow' hretBaseD]
        exact ⟨hargsBase_d, (fnDefSmtParams_map_ty uAT d).symm⟩
      · rw [collectArrowTy_mkArrow' hretBaseD]
        exact ⟨hretBaseD, rfl⟩
    have hIH := ih hcorr'
      (by simpa only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using hufwf)
      hifsRest
      (by
        intro nm hnm
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hnm
        rcases hnm with hnm | hnm
        · exact hused nm hnm
        · subst hnm; exact hfdsUsed d List.mem_cons_self)
      (fun d' hd' => hfdsUsed d' (List.mem_cons_of_mem _ hd'))
      (by
        intro nm hnm
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hnm
        rcases hnm with hnm | hnm
        · exact hnpreBase nm hnm
        · subst hnm; exact hfdsNpre d List.mem_cons_self)
      (fun d' hd' => hfdsNpre d' (List.mem_cons_of_mem _ hd'))
      hdt
    exact IFsWF.cons hIFwf hIH

/-! ## Order-threaded `IFsWF` for the `varDef` preamble (Step 6) -/

/-- The `varDef` preamble is order-well-typed as an `IFsWF` fold. The function context `Ψfull` is fixed;
    the free-var context `Φ` is threaded. -/
theorem IFsWF_of_VarDefsWF {uAT : Bool} {tenv : TranslateEnv} {Ψfull : FnCtx} {Φbase : FVarCtx}
    {vds : List VarDef} (hwf : VarDefsWF Ψfull Φbase vds) :
    ∀ {ufsBase : UFCtx} {ifs : List IF},
      FNameCtxCorresponds uAT Φbase ufsBase →
      FNameCtxCorresponds uAT Ψfull ufsBase →
      UFCtxWF (ufsBase ++ ifs.map IF.toUF) →
      vds.mapM (fun v => do
          let bodyTm ← translate uAT tenv [] v.body
          .ok ({ id := v.name, args := [], out := tyToTermType uAT v.ty, body := bodyTm } : IF))
        = .ok ifs →
      (∀ v ∈ vds, LExpr.MonoTyIsBase v.ty) →
      (∀ nm ∈ (Φbase ++ Ψfull).map Prod.fst, (staticUsedNames tenv).contains nm) →
      (∀ v ∈ vds, (staticUsedNames tenv).contains v.name) →
      FnNamesNotPredefined Ψfull uAT →
      tenv.datatypeFuns = ∅ →
      IFsWF ufsBase ifs := by
  induction hwf with
  | nil =>
    intro ufsBase ifs _ _ _ hmap _ _ _ _ _
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmap
    subst hmap; exact IFsWF.nil
  | @cons Φ v rest hhead htail ih =>
    intro ufsBase ifs hcorrΦ hcorrΨ hufwf hmap hvarTyBase hused hvdsUsed hfnwf hdt
    rw [List.mapM_cons] at hmap
    obtain ⟨f, hf, hmap⟩ := bind_ok_inv hmap
    obtain ⟨ifsRest, hifsRest, hmap⟩ := bind_ok_inv hmap
    simp only [pure, Except.pure, Except.ok.injEq] at hmap
    subst hmap
    obtain ⟨bodyTm, hbody, hfeq⟩ := bind_ok_inv hf
    obtain rfl := Except.ok.inj hfeq
    have hvTyBase := hvarTyBase v List.mem_cons_self
    -- head: `IF.WF`
    have hIFwf : IF.WF ufsBase ⟨v.name, [], tyToTermType uAT v.ty, bodyTm⟩ := by
      show Term.typeCheck ⟨[], ufsBase, []⟩ bodyTm = .ok (tyToTermType uAT v.ty)
      exact translate_typeChecks (Γ := ⟨Ψfull, Φ⟩) (tenv := tenv) (useArrayTheory := uAT) (Δ := [])
        hhead (UFCtxWF.of_append_left hufwf) hbody rfl
        hcorrΦ hcorrΨ bwf_nil hused havoid_nil hfnwf hdt
    -- freshness of `v.name` in `ufsBase`
    have hfresh : v.name ∉ ufsBase.map (·.id) := by
      have hnd := hufwf.uf_nodup
      simp only [List.map_append, List.map_cons] at hnd
      exact fun hmem => (List.nodup_append.mp hnd).2.2 v.name hmem v.name List.mem_cons_self rfl
    -- extended Φ-correspondence
    have hcorrΦ' : FNameCtxCorresponds uAT (Φ ++ [(v.name, v.ty)])
        (ufsBase ++ [(⟨v.name, [], tyToTermType uAT v.ty, bodyTm⟩ : IF).toUF]) := by
      refine hcorrΦ.snoc_eq rfl ?_ ?_ hfresh
      · rw [collectArrowTy_base hvTyBase]; exact ⟨by simp, rfl⟩
      · rw [collectArrowTy_base hvTyBase]; exact ⟨hvTyBase, rfl⟩
    have hIH := ih hcorrΦ' hcorrΨ.append_rightList
      (by simpa only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using hufwf)
      hifsRest
      (fun v' hv' => hvarTyBase v' (List.mem_cons_of_mem _ hv'))
      (by
        intro nm hnm
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hnm ⊢
        rcases hnm with (hnm | hnm) | hnm
        · exact hused nm (by simp only [List.map_append, List.mem_append]; exact Or.inl hnm)
        · subst hnm; exact hvdsUsed v List.mem_cons_self
        · exact hused nm (by simp only [List.map_append, List.mem_append]; exact Or.inr hnm))
      (fun v' hv' => hvdsUsed v' (List.mem_cons_of_mem _ hv'))
      hfnwf hdt
    exact IFsWF.cons hIFwf hIH

/-! ## Left-append of UFs (prefix disjoint from the source names) preserves a correspondence -/

theorem lookupUF_append_left_none {prefixUfs ufs : UFCtx} {name : String}
    (hfresh : name ∉ prefixUfs.map (·.id)) :
    lookupUF (prefixUfs ++ ufs) name = lookupUF ufs name := by
  simp only [lookupUF, List.find?_append]
  have hnone : prefixUfs.find? (·.id == name) = none := by
    rw [List.find?_eq_none]
    intro x hx heq; rw [beq_iff_eq] at heq
    exact hfresh (heq ▸ List.mem_map_of_mem (f := (·.id)) hx)
  rw [hnone, Option.none_or]

theorem FNameCtxCorresponds.append_left {uAT : Bool} {Φ : FNameCtx} {prefixUfs ufs : UFCtx}
    (h : FNameCtxCorresponds uAT Φ ufs)
    (hdisj : ∀ nm ∈ Φ.map Prod.fst, nm ∉ prefixUfs.map (·.id)) :
    FNameCtxCorresponds uAT Φ (prefixUfs ++ ufs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro name τ hmem
    rw [lookupUF_append_left_none (hdisj name (List.mem_map_of_mem (f := Prod.fst) hmem))]
    exact h.fvar_resolves name τ hmem
  · intro name τ uf hmem hlk
    rw [lookupUF_append_left_none (hdisj name (List.mem_map_of_mem (f := Prod.fst) hmem))] at hlk
    exact h.args_eq name τ uf hmem hlk
  · intro name τ uf hmem hlk
    rw [lookupUF_append_left_none (hdisj name (List.mem_map_of_mem (f := Prod.fst) hmem))] at hlk
    exact h.out_eq name τ uf hmem hlk

/-! ## Assertion-membership inversion of `translateQuery` (for `assertsWF`) -/

theorem translateQuery_asserts_mem {uAT : Bool}
    {cctx : CoreCtx} {goal : Expression.Expr} {q : SMTQuery}
    (henc : translateQuery uAT cctx goal = .ok q) :
    ∀ t ∈ q.asserts,
      (∃ e ∈ cctx.fnAxioms, translate uAT cctx.toTranslateEnv [] e = .ok t) ∨
      (∃ e ∈ cctx.assumptions, translate uAT cctx.toTranslateEnv [] e = .ok t) ∨
      (∃ es ∈ cctx.distincts, ∃ ts,
        translateList uAT cctx.toTranslateEnv es = .ok ts ∧
        t = Term.app (Op.core Op.Core.distinct) ts TermType.bool) := by
  unfold translateQuery at henc
  obtain ⟨r1, h1, henc⟩ := bind_ok_inv henc
  obtain ⟨r2, h2, henc⟩ := bind_ok_inv henc
  obtain ⟨r3, h3, henc⟩ := bind_ok_inv henc
  obtain ⟨r4, h4, henc⟩ := bind_ok_inv henc
  obtain ⟨r5, h5, henc⟩ := bind_ok_inv henc
  obtain ⟨r6, h6, henc⟩ := bind_ok_inv henc
  have hq := Except.ok.inj henc
  intro t ht
  rw [SMTQuery.asserts, ← hq] at ht
  simp only [] at ht
  rw [List.mem_append] at ht
  rcases ht with ht | ht
  · exact Or.inl (translateList_mem h3 t ht)
  · rw [List.mem_append] at ht
    rcases ht with ht | ht
    · exact Or.inr (Or.inl (translateList_mem h4 t ht))
    · exact Or.inr (Or.inr (distinctFold_mem h5 t ht))

/-! ## Headline: `translateQuery` preserves well-formedness (`CoreCtx` ⟶ `SMTQuery`) -/

/-- **Statement A.** `translateQuery` on a well-formed, name-hygienic, datatype-free `CoreCtx`
    produces an order-aware well-formed `SMTQuery`. -/
theorem translateQuery_WF
    -- ── source side ──
    {cctx : CoreCtx} {goal : Expression.Expr}
    (hwf : CoreCtx.WF cctx goal)
    -- ── target side ──
    {q : SMTQuery}
    -- ── correspondence ──
    {useArrayTheory : Bool}
    (hnames : CoreCtx.NamesWF cctx useArrayTheory)
    (hq : translateQuery useArrayTheory cctx goal = .ok q) :
    SMTQuery.WF q := by
  -- Abbreviations and shared facts.
  let uAT := useArrayTheory
  have hnpre : FnNamesNotPredefined cctx.toΨ useArrayTheory := hnames.fnNamesNotPredefined
  have hretBase := hwf.fnDefsWF.mem_retBase
  have hvarBase := hwf.varDefsWF.mem_tyBase
  have hargsBase := hwf.fnDefsWF.mem_argsBase
  obtain ⟨hfnDecls, hvarDecls, hfnDefsMap, hvarDefsMap, hfnAxioms, hobl⟩ := translateQuery_inv hq
  have hufs_eq : q.ufs = (cctx.toΨ ++ cctx.toΦ).map (encodeUF uAT) := tq_ufs_eq hq hretBase hvarBase
  have hdtfree : cctx.toTranslateEnv.datatypeFuns = ∅ := hwf.datatypeFunsEmpty
  have hnd_full : ((cctx.toΨ ++ cctx.toΦ).map Prod.fst).Nodup := hnames.names_nodup
  -- ids-of-encoded chunks collapse to the source names.
  have hids_eq : q.ufs.map (·.id) = (cctx.toΨ ++ cctx.toΦ).map Prod.fst := by
    rw [hufs_eq, List.map_map]; exact List.map_congr_left (fun p _ => rfl)
  have hids_Ψ : (q.fnDecls ++ q.fnDefs.map IF.toUF).map (·.id) = cctx.toΨ.map Prod.fst := by
    rw [← tq_toΨ_map hq hretBase, List.map_map]; exact List.map_congr_left (fun p _ => rfl)
  -- Nodups of the sub-contexts.
  have hnd_toΨ : (cctx.toΨ.map Prod.fst).Nodup := by
    have := hnd_full; rw [List.map_append] at this; exact (List.nodup_append.mp this).1
  have hnd_toΦ : (cctx.toΦ.map Prod.fst).Nodup := by
    have := hnd_full; rw [List.map_append] at this; exact (List.nodup_append.mp this).2.1
  have hnd_fnDecls : (cctx.fnDecls.map Prod.fst).Nodup := by
    have := hnd_toΨ; rw [CoreCtx.toΨ, List.map_append] at this; exact (List.nodup_append.mp this).1
  have hnd_varDecls : (cctx.varDecls.map Prod.fst).Nodup := by
    have := hnd_toΦ; rw [CoreCtx.toΦ, List.map_append] at this; exact (List.nodup_append.mp this).1
  -- Name-membership helpers.
  have hfnDecl_toΨ : ∀ nm ∈ cctx.fnDecls.map Prod.fst, nm ∈ cctx.toΨ.map Prod.fst := by
    intro nm h; rw [CoreCtx.toΨ, List.map_append, List.mem_append]; exact Or.inl h
  have hfnDef_name_toΨ : ∀ d ∈ cctx.fnDefs, d.name ∈ cctx.toΨ.map Prod.fst := by
    intro d hd; rw [CoreCtx.toΨ, List.map_append, List.mem_append]; right
    exact List.mem_map_of_mem (f := Prod.fst)
      (List.mem_map_of_mem (f := fun d => (d.name, LMonoTy.mkArrow' d.retTy d.argTys)) hd)
  have hcoreUsed_Ψ : ∀ nm ∈ cctx.toΨ.map Prod.fst, (staticUsedNames cctx.toTranslateEnv).contains nm := by
    intro nm h; exact coreCtx_names_used (by rw [List.map_append, List.mem_append]; exact Or.inr h)
  -- Per-entry SigBase for the declared/defined signatures.
  have hbase_fnDecls : ∀ p ∈ cctx.fnDecls, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 :=
    fun p hp => hwf.fnDeclsSigBase p.1 p.2 hp
  have hbase_varDecls : ∀ p ∈ cctx.varDecls, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 :=
    fun p hp => hwf.varDeclsSigBase p.1 p.2 hp
  have hbase_toΨ : ∀ p ∈ cctx.toΨ, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 := by
    intro p hp
    rw [CoreCtx.toΨ, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hbase_fnDecls p hp
    · obtain ⟨d, hd_mem, hd_eq⟩ := List.mem_map.mp hp
      have hp2 : p.2 = LMonoTy.mkArrow' d.retTy d.argTys := by rw [← hd_eq]
      rw [hp2, collectArrowTy_mkArrow' (hretBase d hd_mem)]
      exact ⟨hargsBase d hd_mem, hretBase d hd_mem⟩
  have hbase_toΦ : ∀ p ∈ cctx.toΦ, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 := by
    intro p hp
    rw [CoreCtx.toΦ, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hbase_varDecls p hp
    · obtain ⟨v, hv_mem, hv_eq⟩ := List.mem_map.mp hp
      have hp2 : p.2 = v.ty := by rw [← hv_eq]
      rw [hp2, collectArrowTy_base (hvarBase v hv_mem)]
      exact ⟨by intro a ha; simp at ha, hvarBase v hv_mem⟩
  have hbase_full : ∀ p ∈ cctx.toΨ ++ cctx.toΦ, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hbase_toΨ p hp
    · exact hbase_toΦ p hp
  -- The four correspondences.
  have hc_full : FNameCtxCorresponds uAT (cctx.toΨ ++ cctx.toΦ) q.ufs := by
    rw [hufs_eq]
    exact FNameCtxCorresponds.of_map_encode hbase_full hnd_full
  have hcΨ : FNameCtxCorresponds uAT cctx.toΨ q.ufs := hc_full.mono_sub (List.subset_append_left _ _)
  have hcΦ : FNameCtxCorresponds uAT cctx.toΦ q.ufs := hc_full.mono_sub (List.subset_append_right _ _)
  -- `ufsWF`.
  have hufsWF : UFCtxWF q.ufs :=
    ⟨by rw [hids_eq]; exact hnd_full, fun n => by rw [hids_eq]; exact hnames.names_no_reserved n⟩
  -- `oblWF`.
  have hoblWF : Term.typeCheck ⟨[], q.ufs, []⟩ q.obl = .ok .bool :=
    translate_typeChecks (Γ := ⟨cctx.toΨ, cctx.toΦ⟩) (tenv := cctx.toTranslateEnv) (useArrayTheory := uAT) (Δ := [])
      hwf.goalWF hufsWF hobl (by simp only [tyToTermType]) hcΦ hcΨ bwf_nil
      (fun nm hnm => coreCtx_names_used hnm) havoid_nil hnpre hdtfree
  -- `assertsWF`.
  have hassertsWF : ∀ t ∈ q.asserts, Term.typeCheck ⟨[], q.ufs, []⟩ t = .ok .bool := by
    intro t ht
    rcases translateQuery_asserts_mem hq t ht with ⟨e, he, htr⟩ | ⟨e, he, htr⟩ | ⟨es, hes, ts, htls, hteq⟩
    · exact translate_typeChecks (Γ := ⟨cctx.toΨ, cctx.toΦ⟩) (tenv := cctx.toTranslateEnv) (useArrayTheory := uAT) (Δ := [])
        (hwf.fnAxiomsWF e he) hufsWF htr (by simp only [tyToTermType]) hcΦ hcΨ bwf_nil
        (fun nm hnm => coreCtx_names_used hnm) havoid_nil hnpre hdtfree
    · exact translate_typeChecks (Γ := ⟨cctx.toΨ, cctx.toΦ⟩) (tenv := cctx.toTranslateEnv) (useArrayTheory := uAT) (Δ := [])
        (hwf.assumptionsWF e he) hufsWF htr (by simp only [tyToTermType]) hcΦ hcΨ bwf_nil
        (fun nm hnm => coreCtx_names_used hnm) havoid_nil hnpre hdtfree
    · subst hteq
      obtain ⟨hge2_es, τ, hτbase, hall⟩ := hwf.distinctsWF es hes
      have hlen : ts.length = es.length := translateList_len htls
      have hge2 : 2 ≤ ts.length := by rw [hlen]; exact hge2_es
      obtain ⟨t1, t2, rest, htseq⟩ : ∃ a b r, ts = a :: b :: r := by
        rcases ts with _ | ⟨a, _ | ⟨b, r⟩⟩
        · exact absurd hge2 (by simp only [List.length_nil]; omega)
        · exact absurd hge2 (by simp only [List.length_cons, List.length_nil]; omega)
        · exact ⟨a, b, r, rfl⟩
      apply distinct_typeCheck htseq
      intro i hi
      have hie : i < es.length := hlen ▸ hi
      exact translate_typeChecks (Γ := ⟨cctx.toΨ, cctx.toΦ⟩) (tenv := cctx.toTranslateEnv) (useArrayTheory := uAT) (Δ := [])
        (hall _ (es.get_mem ⟨i, hie⟩)) hufsWF (translateList_getElem es ts htls i hie hi) rfl hcΦ hcΨ bwf_nil
        (fun nm hnm => coreCtx_names_used hnm) havoid_nil hnpre hdtfree
  -- `fnDefsWF`.
  have hcorr_fnDecls : FNameCtxCorresponds uAT cctx.fnDecls q.fnDecls := by
    rw [hfnDecls]; exact FNameCtxCorresponds.of_map_encode hbase_fnDecls hnd_fnDecls
  have hufwf_fnDefs : UFCtxWF (q.fnDecls ++ q.fnDefs.map IF.toUF) := by
    have h1 := hufsWF; rw [SMTQuery.ufs] at h1
    exact UFCtxWF.of_append_left (UFCtxWF.of_append_left h1)
  have hfnDefsWF : IFsWF q.fnDecls q.fnDefs :=
    IFsWF_of_FnDefsWF (cctx := cctx) hwf.fnDefsWF hcorr_fnDecls hufwf_fnDefs hfnDefsMap
      (fun nm h => hcoreUsed_Ψ nm (hfnDecl_toΨ nm h))
      (fun d hd => hcoreUsed_Ψ d.name (hfnDef_name_toΨ d hd))
      (fun nm h => hnpre nm (hfnDecl_toΨ nm h))
      (fun d hd => hnpre d.name (hfnDef_name_toΨ d hd))
      hdtfree
  -- `varDefsWF`.
  have hcorrΨ_pre : FNameCtxCorresponds uAT cctx.toΨ (q.fnDecls ++ q.fnDefs.map IF.toUF) := by
    rw [← tq_toΨ_map hq hretBase]; exact FNameCtxCorresponds.of_map_encode hbase_toΨ hnd_toΨ
  have hcorrΨ : FNameCtxCorresponds uAT cctx.toΨ (q.fnDecls ++ q.fnDefs.map IF.toUF ++ q.varDecls) :=
    hcorrΨ_pre.append_rightList
  have hdisj_varDecls : ∀ nm ∈ cctx.varDecls.map Prod.fst, nm ∉ (q.fnDecls ++ q.fnDefs.map IF.toUF).map (·.id) := by
    intro nm hnm hcontra
    rw [hids_Ψ] at hcontra
    have hΦ : nm ∈ cctx.toΦ.map Prod.fst := by
      rw [CoreCtx.toΦ, List.map_append, List.mem_append]; exact Or.inl hnm
    have hnd := hnd_full; rw [List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 nm hcontra nm hΦ rfl
  have hcorrΦ_pre : FNameCtxCorresponds uAT cctx.varDecls q.varDecls := by
    rw [hvarDecls]; exact FNameCtxCorresponds.of_map_encode hbase_varDecls hnd_varDecls
  have hcorrΦ : FNameCtxCorresponds uAT cctx.varDecls (q.fnDecls ++ q.fnDefs.map IF.toUF ++ q.varDecls) :=
    hcorrΦ_pre.append_left hdisj_varDecls
  have hufwf_varDefs : UFCtxWF ((q.fnDecls ++ q.fnDefs.map IF.toUF ++ q.varDecls) ++ q.varDefs.map IF.toUF) := by
    have h1 := hufsWF; rw [SMTQuery.ufs] at h1; exact h1
  have hused_var : ∀ nm ∈ (cctx.varDecls ++ cctx.toΨ).map Prod.fst, (staticUsedNames cctx.toTranslateEnv).contains nm := by
    intro nm hnm
    rw [List.map_append, List.mem_append] at hnm
    apply coreCtx_names_used
    rw [List.map_append, List.mem_append]
    rcases hnm with hnm | hnm
    · left; rw [CoreCtx.toΦ, List.map_append, List.mem_append]; exact Or.inl hnm
    · right; exact hnm
  have hvdsUsed : ∀ v ∈ cctx.varDefs, (staticUsedNames cctx.toTranslateEnv).contains v.name := by
    intro v hv
    apply coreCtx_names_used
    rw [List.map_append, List.mem_append]; left
    have hmem : (v.name, v.ty) ∈ cctx.toΦ := by
      rw [CoreCtx.toΦ, List.mem_append]; exact Or.inr (List.mem_map_of_mem (f := fun v => (v.name, v.ty)) hv)
    exact List.mem_map_of_mem (f := Prod.fst) hmem
  have hvarDefsWF : IFsWF (q.fnDecls ++ q.fnDefs.map IF.toUF ++ q.varDecls) q.varDefs :=
    IFsWF_of_VarDefsWF (tenv := cctx.toTranslateEnv) hwf.varDefsWF hcorrΦ hcorrΨ hufwf_varDefs hvarDefsMap
      hvarBase hused_var hvdsUsed hnpre hdtfree
  exact ⟨hufsWF, hfnDefsWF, hvarDefsWF, hassertsWF, hoblWF⟩


/-! ## Denotation-side soundness proofs -/

variable {σ : SortInterp}

/-! ## Cast bridges -/
theorem tyDenote_eq_smtTyDenote {uAT : Bool} {τ : LMonoTy} {smtTy : TermType}
    (h : LExpr.MonoTyIsBase τ ∧ tyToTermType uAT τ = smtTy) :
    Lambda.TyDenote simpTcInterp simpTyVarVal τ = TermType.denoteTyped σ SmtArrayTheory smtTy := by
  obtain ⟨hbase, heq⟩ := h
  cases hbase <;> (subst heq; first | rfl | (simp only [tyToTermType]; rfl))

/-- The curried LExpr denotation of a right-nested arrow type equals the SMT-side
    `UF.denoteTyped'` at the corresponding SMT types. -/
theorem tyDenote_arrow_eq_UFDenote' {uAT : Bool}
    {acc : List LMonoTy} {accSmt : List TermType} {rty : LMonoTy} {smtRty : TermType}
    (hacc : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType uAT) = accSmt)
    (hrty : LExpr.MonoTyIsBase rty ∧ tyToTermType uAT rty = smtRty) :
    Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow rty acc)
      = UF.denoteTyped' σ SmtArrayTheory accSmt smtRty := by
  obtain ⟨haccBase, haccEq⟩ := hacc
  subst haccEq
  induction acc with
  | nil =>
    simp only [List.map_nil, UF.denoteTyped', List.foldr]
    exact tyDenote_eq_smtTyDenote (σ := σ) hrty
  | cons aty rest ih =>
    simp only [List.map_cons, List.foldr, UF.denoteTyped']
    have hatyBase : LExpr.MonoTyIsBase aty := haccBase aty (List.mem_cons.mpr (Or.inl rfl))
    have hrestBase : ∀ t ∈ rest, LExpr.MonoTyIsBase t :=
      fun t ht => haccBase t (List.mem_cons.mpr (Or.inr ht))
    have harrow : Lambda.TyDenote simpTcInterp simpTyVarVal
          (LMonoTy.arrow aty (List.foldr LMonoTy.arrow rty rest))
        = (Lambda.TyDenote simpTcInterp simpTyVarVal aty →
           Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow rty rest)) := rfl
    have h_aty : Lambda.TyDenote simpTcInterp simpTyVarVal aty
        = TermType.denoteTyped σ SmtArrayTheory (tyToTermType uAT aty) :=
      tyDenote_eq_smtTyDenote (σ := σ) ⟨hatyBase, rfl⟩
    have h_rest : Lambda.TyDenote simpTcInterp simpTyVarVal
          (List.foldr LMonoTy.arrow rty rest)
        = UF.denoteTyped' σ SmtArrayTheory (rest.map (tyToTermType uAT)) smtRty :=
      ih hrestBase
    rw [harrow, h_aty, h_rest]

/-! ## Cast / HEq plumbing + SMT denotation unfolding -/
theorem subst_heq {α : Sort u} {P : α → Sort v} {a b : α}
    (h : a = b) (x : P b) : HEq (h ▸ x) x := by subst h; exact HEq.rfl

/-- Casting a function and its argument along matching type equalities commutes
    with application. -/
theorem cast_arrow_app {A A' B B' : Type} (hA : A = A') (hB : B = B')
    (hAB : (A → B) = (A' → B')) (f : A → B) (x : A) :
    (cast hAB f) (cast hA x) = cast hB (f x) := by
  subst hA; subst hB; rfl

/-- Unfolding lemma for `Term.denoteTyped` on a UF application. -/
noncomputable def SMTTerm_denote_uf_unfold {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) {divByZero modByZero : Int → Int}
    (uf : UF) (args : List Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck ⟨[], ufs, Γ⟩ (.app (.core (.uf uf)) args rty) = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero (.app (.core (.uf uf)) args rty) τ htc =
      cast (by rw [(tc_uf_inv htc).2])
        (UF.applyDenoteTyped' σ SmtArrayTheory uf.args uf.out (ufInterp uf)
          (Term.denoteTypedArgs ufInterp env divByZero modByZero args uf.args (tc_uf_inv htc).1)) := by
  simp only [Term.denoteTyped]


private noncomputable def SMTTerm_denote_eq_unfold {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) {divByZero modByZero : Int → Int}
    (t1 t2 : Term) (rty : TermType) (τ : TermType)
    (htc : Term.typeCheck ⟨[], ufs, Γ⟩ (.app (.core .eq) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero (.app (.core .eq) [t1, t2] rty) τ htc =
      cast (by rw [(Term.typeCheck_eq_inv htc).2.2.2]) (@decide
        (Term.denoteTyped ufInterp env divByZero modByZero t1 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.1
         = Term.denoteTyped ufInterp env divByZero modByZero t2 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.2.1)
        (Classical.propDecidable _)) := by
  simp only [Term.denoteTyped]
  obtain ⟨τ', h1, h2, heq⟩ := Term.typeCheck_eq_inv htc
  rfl

/-- `Term.denoteTyped` is invariant (up to `HEq`) under a provably-equal change of the type index. -/
private theorem SMTTerm_denote_cast {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) {divByZero modByZero : Int → Int}
    (tm : Term) (τ τ' : TermType)
    (h : Term.typeCheck ⟨[], ufs, Γ⟩ tm = .ok τ) (h' : Term.typeCheck ⟨[], ufs, Γ⟩ tm = .ok τ')
    (heq : τ = τ') :
    HEq (Term.denoteTyped ufInterp env divByZero modByZero tm τ h) (Term.denoteTyped ufInterp env divByZero modByZero tm τ' h') := by
  subst heq; exact heq_of_eq (congrArg (Term.denoteTyped ufInterp env divByZero modByZero tm τ) (proof_irrel h h'))

/-- LHS reduction for a **unary** operator head, re-keyed onto the arg/return base-ness facts
    and their correspondence equations. -/
private theorem applyUF1_of_cons {uAT : Bool} {Δ : BVarCtx}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    {o : CoreLParams.Identifier} {a r : LMonoTy} {sa sr : TermType}
    {g : TermType.denoteTyped σ SmtArrayTheory sa → TermType.denoteTyped σ SmtArrayTheory sr}
    (htA : LExpr.HasTypeA Δ (.op () o (some (.tcons "arrow" [a, r])))
      (List.foldr LMonoTy.arrow r [a]))
    (hacc : (∀ t ∈ [a], LExpr.MonoTyIsBase t) ∧ [a].map (tyToTermType uAT) = [sa])
    (hrty : LExpr.MonoTyIsBase r ∧ tyToTermType uAT r = sr)
    (hcons : HEq (opInterp o.name ((LMonoTy.tcons "arrow" [a, r]).substTyVars simpTyVarVal)) g)
    (v : TermType.denoteTyped σ SmtArrayTheory sa) :
    UF.applyDenoteTyped' σ SmtArrayTheory [sa] sr (cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal (.op () o (some (.tcons "arrow" [a, r])))
        (List.foldr LMonoTy.arrow r [a]) htA)) (.cons v .nil) = g v := by
  have h_head : cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal (.op () o (some (.tcons "arrow" [a, r])))
        (List.foldr LMonoTy.arrow r [a]) htA) = g := by
    simp only [simpDenote,
      Lambda.denote_op simpTcInterp opInterp fvarVal simpTyVarVal bvarVal htA]
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans (subst_heq (P := fun x => Lambda.TyDenote simpTcInterp simpTyVarVal x)
      (HasTypeA.op_inv htA)
      (opInterp o.name ((LMonoTy.tcons "arrow" [a, r]).substTyVars simpTyVarVal))) ?_
    exact hcons
  rw [h_head]; rfl

/-- LHS reduction for a **binary** operator head, re-keyed onto the arg/return base-ness facts
    and their correspondence equations. -/
private theorem applyUF2_of_cons {uAT : Bool} {Δ : BVarCtx}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    {o : CoreLParams.Identifier} {a1 a2 r : LMonoTy} {sa1 sa2 sr : TermType}
    {g : TermType.denoteTyped σ SmtArrayTheory sa1 → TermType.denoteTyped σ SmtArrayTheory sa2 → TermType.denoteTyped σ SmtArrayTheory sr}
    (htA : LExpr.HasTypeA Δ (.op () o (some (.tcons "arrow" [a1, .tcons "arrow" [a2, r]])))
      (List.foldr LMonoTy.arrow r [a1, a2]))
    (hacc : (∀ t ∈ [a1, a2], LExpr.MonoTyIsBase t) ∧ [a1, a2].map (tyToTermType uAT) = [sa1, sa2])
    (hrty : LExpr.MonoTyIsBase r ∧ tyToTermType uAT r = sr)
    (hcons : HEq (opInterp o.name
      ((LMonoTy.tcons "arrow" [a1, .tcons "arrow" [a2, r]]).substTyVars simpTyVarVal)) g)
    (v1 : TermType.denoteTyped σ SmtArrayTheory sa1) (v2 : TermType.denoteTyped σ SmtArrayTheory sa2) :
    UF.applyDenoteTyped' σ SmtArrayTheory [sa1, sa2] sr (cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal
        (.op () o (some (.tcons "arrow" [a1, .tcons "arrow" [a2, r]])))
        (List.foldr LMonoTy.arrow r [a1, a2]) htA)) (.cons v1 (.cons v2 .nil)) = g v1 v2 := by
  have h_head : cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal
        (.op () o (some (.tcons "arrow" [a1, .tcons "arrow" [a2, r]])))
        (List.foldr LMonoTy.arrow r [a1, a2]) htA) = g := by
    simp only [simpDenote,
      Lambda.denote_op simpTcInterp opInterp fvarVal simpTyVarVal bvarVal htA]
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans (subst_heq (P := fun x => Lambda.TyDenote simpTcInterp simpTyVarVal x)
      (HasTypeA.op_inv htA)
      (opInterp o.name
        ((LMonoTy.tcons "arrow" [a1, .tcons "arrow" [a2, r]]).substTyVars simpTyVarVal))) ?_
    exact hcons
  rw [h_head]; rfl

theorem bif_heq_of_cond_branches {α β : Type} {b1 b2 : Bool}
    {t1 e1 : α} {t2 e2 : β} (h_ty : α = β)
    (hb : b1 = b2) (ht : HEq t1 t2) (he : HEq e1 e2) :
    cast h_ty (bif b1 then t1 else e1) = (bif b2 then t2 else e2) := by
  subst h_ty; subst hb; cases ht; cases he; cases b1 <;> rfl

/-- Injectivity of `cast` on a single fixed type equality (fresh copy). -/
theorem cast_inj_of_eq {α β : Type} (h : α = β) (a b : α)
    (hcast : cast h a = cast h b) : a = b := by cases h; exact hcast

/-- Splitter for a `decide … || decide …` guard (fresh copy of the FactoryCorrect helper). -/
theorem or_decide_true {p q : Prop} [Decidable p] [Decidable q]
    (h : (decide p || decide q) = true) : p ∨ q := by
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h; exact h

private noncomputable def SMTTerm_denote_ite_unfold {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) {divByZero modByZero : Int → Int}
    (c t e : Term) (rty τ : TermType)
    (htc : Term.typeCheck ⟨[], ufs, Γ⟩ (.app (.core .ite) [c, t, e] rty) = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero (.app (.core .ite) [c, t, e] rty) τ htc =
      bif Term.denoteTyped ufInterp env divByZero modByZero c .bool (Term.typeCheck_ite_inv htc).1
        then Term.denoteTyped ufInterp env divByZero modByZero t τ (Term.typeCheck_ite_inv htc).2.1
        else Term.denoteTyped ufInterp env divByZero modByZero e τ (Term.typeCheck_ite_inv htc).2.2 := by
  simp only [Term.denoteTyped]; obtain ⟨hc, ht, he⟩ := Term.typeCheck_ite_inv htc; rfl

/-! ## Primitive-literal denotation value lemmas -/
theorem prim_of_isLiteral_base {ufs : UFCtx} {bvs : TermVarCtx} {t : Term} {smtτ' : TermType}
    (hb : TermType.isBase smtτ' = true) (hlit : t.isLiteral = true)
    (h : Term.typeCheck ⟨[], ufs, bvs⟩ t = .ok smtτ') : ∃ p, t = .prim p := by
  cases t with
  | prim p => exact ⟨p, rfl⟩
  | none ty =>
    have heq := Term.typeCheck_none_inv h
    rcases isBase_cases hb with rfl | rfl | rfl | ⟨n, rfl⟩ <;> simp_all
  | some t' =>
    obtain ⟨τ', _, heq⟩ := Term.typeCheck_some_inv h
    rcases isBase_cases hb with rfl | rfl | rfl | ⟨n, rfl⟩ <;> simp_all
  | var v => simp [Term.isLiteral] at hlit
  | app o a r => simp [Term.isLiteral] at hlit
  | quant k vs tr b => simp [Term.isLiteral] at hlit

/-! ## Factory.eq / Factory.ite denotation characterization -/
theorem Factory_eq_denote_true {ufs : UFCtx} {bvs : TermVarCtx}
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory) {dz mz : Int → Int}
    {t1 t2 : Term} {smtτ' : TermType}
    (hb : TermType.isBase smtτ' = true)
    (h1 : Term.typeCheck ⟨[], ufs, bvs⟩ t1 = .ok smtτ')
    (h2 : Term.typeCheck ⟨[], ufs, bvs⟩ t2 = .ok smtτ')
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ (Factory.eq t1 t2) = .ok .bool)
    (hvals : Term.denoteTyped ufInterp smtEnv dz mz t1 smtτ' h1
             = Term.denoteTyped ufInterp smtEnv dz mz t2 smtτ' h2) :
    Term.denoteTyped ufInterp smtEnv dz mz (Factory.eq t1 t2) .bool htc = true := by
  have hns1 := not_someNone_of_base hb h1
  have hns2 := not_someNone_of_base hb h2
  by_cases hc : t1 = t2
  · have hform := Factory_eq_true_form hc
    have htc' : Term.typeCheck ⟨[], ufs, bvs⟩ (Term.prim (.bool true)) = .ok .bool := hform ▸ htc
    rw [Term.denoteTyped_congr hform htc htc', denote_prim_bool]
  · by_cases hlit : (t1.isLiteral && t2.isLiteral) = true
    · -- distinct literals with equal denotations is impossible (injectivity)
      exfalso
      rw [Bool.and_eq_true] at hlit
      obtain ⟨hl1, hl2⟩ := hlit
      obtain ⟨p1, rfl⟩ := prim_of_isLiteral_base hb hl1 h1
      obtain ⟨p2, rfl⟩ := prim_of_isLiteral_base hb hl2 h2
      exact denote_prim_inj ufInterp smtEnv hb h1 h2 hc hvals
    · have hform := Factory_eq_app_form hc hlit hns1 hns2
      have htc' : Term.typeCheck ⟨[], ufs, bvs⟩ (Term.app (.core .eq) [t1, t2] .bool) = .ok .bool := hform ▸ htc
      rw [Term.denoteTyped_congr hform htc htc', SMTTerm_denote_eq_unfold,
        eq_of_heq (cast_heq _ _)]
      have hd1 := SMTTerm_denote_cast ufInterp smtEnv (divByZero := dz) (modByZero := mz) t1 (Term.typeCheck_eq_inv htc').1 smtτ'
        (Term.typeCheck_eq_inv htc').2.1 h1 (Except.ok.inj ((Term.typeCheck_eq_inv htc').2.1.symm.trans h1))
      have hd2 := SMTTerm_denote_cast ufInterp smtEnv (divByZero := dz) (modByZero := mz) t2 (Term.typeCheck_eq_inv htc').1 smtτ'
        (Term.typeCheck_eq_inv htc').2.2.1 h2 (Except.ok.inj ((Term.typeCheck_eq_inv htc').2.2.1.symm.trans h2))
      simp only [decide_eq_true_eq]
      exact eq_of_heq (hd1.trans ((heq_of_eq hvals).trans hd2.symm))

/-- `Factory.eq` denotes `false` when the operand denotations differ. -/
theorem Factory_eq_denote_false {ufs : UFCtx} {bvs : TermVarCtx}
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory) {dz mz : Int → Int}
    {t1 t2 : Term} {smtτ' : TermType}
    (hb : TermType.isBase smtτ' = true)
    (h1 : Term.typeCheck ⟨[], ufs, bvs⟩ t1 = .ok smtτ')
    (h2 : Term.typeCheck ⟨[], ufs, bvs⟩ t2 = .ok smtτ')
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ (Factory.eq t1 t2) = .ok .bool)
    (hvals : Term.denoteTyped ufInterp smtEnv dz mz t1 smtτ' h1
             ≠ Term.denoteTyped ufInterp smtEnv dz mz t2 smtτ' h2) :
    Term.denoteTyped ufInterp smtEnv dz mz (Factory.eq t1 t2) .bool htc = false := by
  have hns1 := not_someNone_of_base hb h1
  have hns2 := not_someNone_of_base hb h2
  by_cases hc : t1 = t2
  · -- equal terms cannot have distinct denotations
    exfalso; apply hvals; subst hc; rw [proof_irrel h1 h2]
  · by_cases hlit : (t1.isLiteral && t2.isLiteral) = true
    · have hform := Factory_eq_false_form hc hlit
      have htc' : Term.typeCheck ⟨[], ufs, bvs⟩ (Term.prim (.bool false)) = .ok .bool := hform ▸ htc
      rw [Term.denoteTyped_congr hform htc htc', denote_prim_bool]
    · have hform := Factory_eq_app_form hc hlit hns1 hns2
      have htc' : Term.typeCheck ⟨[], ufs, bvs⟩ (Term.app (.core .eq) [t1, t2] .bool) = .ok .bool := hform ▸ htc
      rw [Term.denoteTyped_congr hform htc htc', SMTTerm_denote_eq_unfold,
        eq_of_heq (cast_heq _ _)]
      have hd1 := SMTTerm_denote_cast ufInterp smtEnv (divByZero := dz) (modByZero := mz) t1 (Term.typeCheck_eq_inv htc').1 smtτ'
        (Term.typeCheck_eq_inv htc').2.1 h1 (Except.ok.inj ((Term.typeCheck_eq_inv htc').2.1.symm.trans h1))
      have hd2 := SMTTerm_denote_cast ufInterp smtEnv (divByZero := dz) (modByZero := mz) t2 (Term.typeCheck_eq_inv htc').1 smtτ'
        (Term.typeCheck_eq_inv htc').2.2.1 h2 (Except.ok.inj ((Term.typeCheck_eq_inv htc').2.2.1.symm.trans h2))
      simp only [decide_eq_false_iff_not]
      intro hp
      exact hvals (eq_of_heq (hd1.symm.trans ((heq_of_eq hp).trans hd2)))

theorem Factory_ite_denoteTyped {ufs : UFCtx} {bvs : TermVarCtx}
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory) {dz mz : Int → Int}
    {t1 t2 t3 : Term} {smtτ' : TermType}
    (hb : TermType.isBase smtτ' = true)
    (h1 : Term.typeCheck ⟨[], ufs, bvs⟩ t1 = .ok .bool)
    (h2 : Term.typeCheck ⟨[], ufs, bvs⟩ t2 = .ok smtτ')
    (h3 : Term.typeCheck ⟨[], ufs, bvs⟩ t3 = .ok smtτ')
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ (Factory.ite t1 t2 t3) = .ok smtτ') :
    Term.denoteTyped ufInterp smtEnv dz mz (Factory.ite t1 t2 t3) smtτ' htc
      = bif Term.denoteTyped ufInterp smtEnv dz mz t1 .bool h1
        then Term.denoteTyped ufInterp smtEnv dz mz t2 smtτ' h2
        else Term.denoteTyped ufInterp smtEnv dz mz t3 smtτ' h3 := by
  have hns2 := not_someNone_of_base hb h2
  by_cases hcond : (decide (t1 = (true : Term)) || decide (t2 = t3)) = true
  · rw [Term.denoteTyped_congr (Factory_ite_t2_form hcond) htc h2]
    rcases or_decide_true hcond with ht1 | ht23
    · have hcv : Term.denoteTyped ufInterp smtEnv dz mz t1 .bool h1 = true := by
        have h1' : Term.typeCheck ⟨[], ufs, bvs⟩ (Term.prim (.bool true)) = .ok .bool := ht1 ▸ h1
        rw [Term.denoteTyped_congr ht1 h1 h1', denote_prim_bool]
      rw [hcv]; rfl
    · have hb23 : Term.denoteTyped ufInterp smtEnv dz mz t2 smtτ' h2
                = Term.denoteTyped ufInterp smtEnv dz mz t3 smtτ' h3 :=
        Term.denoteTyped_congr ht23 h2 h3
      rw [show Term.denoteTyped ufInterp smtEnv dz mz t3 smtτ' h3
            = Term.denoteTyped ufInterp smtEnv dz mz t2 smtτ' h2 from hb23.symm]
      cases Term.denoteTyped ufInterp smtEnv dz mz t1 .bool h1 <;> rfl
  · by_cases hf : t1 = (false : Term)
    · rw [Term.denoteTyped_congr (Factory_ite_t3_form hcond hf) htc h3]
      have hcv : Term.denoteTyped ufInterp smtEnv dz mz t1 .bool h1 = false := by
        have h1' : Term.typeCheck ⟨[], ufs, bvs⟩ (Term.prim (.bool false)) = .ok .bool := hf ▸ h1
        rw [Term.denoteTyped_congr hf h1 h1', denote_prim_bool]
      rw [hcv]; rfl
    · have hform := Factory_ite_app_form hcond hf hns2
      have htc' : Term.typeCheck ⟨[], ufs, bvs⟩ (Term.app (.core .ite) [t1, t2, t3] t2.typeOf) = .ok smtτ' := hform ▸ htc
      rw [Term.denoteTyped_congr hform htc htc', SMTTerm_denote_ite_unfold,
        proof_irrel (Term.typeCheck_ite_inv htc').1 h1,
        proof_irrel (Term.typeCheck_ite_inv htc').2.1 h2,
        proof_irrel (Term.typeCheck_ite_inv htc').2.2 h3]

/-! ## Environment correspondences -/
def FVarEnvCorresponds
    {uAT : Bool} {Φ : FVarCtx} {ufs : UFCtx}
    (hwf : FNameCtxCorresponds uAT Φ ufs)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (ufInterp : UFInterp σ SmtArrayTheory) : Prop :=
  ∀ (name : String) (τ : LMonoTy) (hmem : (name, τ) ∈ Φ),
    let uf : UF := (lookupUF ufs name).get (hwf.fvar_resolves name τ hmem)
    let hlk : lookupUF ufs name = some uf := (Option.some_get _).symm
    cast (by
          have hargs := hwf.args_eq name τ uf hmem hlk
          have hout := hwf.out_eq name τ uf hmem hlk
          have h1 : τ = List.foldr LMonoTy.arrow (collectArrowTy τ).2 (collectArrowTy τ).1 := by
            have hf := collectArrowTy_foldr τ
            obtain ⟨argTys, rty, hcol⟩ : ∃ a r, collectArrowTy τ = (a, r) := ⟨_, _, rfl⟩
            rw [hcol] at hf ⊢; exact hf
          rw [h1]; exact tyDenote_arrow_eq_UFDenote' hargs hout)
         (fvarVal ⟨name, ()⟩ (τ.substTyVars simpTyVarVal))
      = ufInterp uf

def FnEnvCorresponds
    {uAT : Bool} {Ψ : FnCtx} {ufs : UFCtx}
    (hwf : FNameCtxCorresponds uAT Ψ ufs)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (ufInterp : UFInterp σ SmtArrayTheory) : Prop :=
  ∀ (name : String) (τ : LMonoTy) (hmem : (name, τ) ∈ Ψ),
    let uf : UF := (lookupUF ufs name).get (hwf.fvar_resolves name τ hmem)
    let hlk : lookupUF ufs name = some uf := (Option.some_get _).symm
    cast (by
          have hargs := hwf.args_eq name τ uf hmem hlk
          have hout := hwf.out_eq name τ uf hmem hlk
          have h1 : τ = List.foldr LMonoTy.arrow (collectArrowTy τ).2 (collectArrowTy τ).1 := by
            have hf := collectArrowTy_foldr τ
            obtain ⟨argTys, rty, hcol⟩ : ∃ a r, collectArrowTy τ = (a, r) := ⟨_, _, rfl⟩
            rw [hcol] at hf ⊢; exact hf
          rw [h1]; exact tyDenote_arrow_eq_UFDenote' hargs hout)
         (opInterp name (τ.substTyVars simpTyVarVal))
      = ufInterp uf

def BVarEnvCorresponds {uAT : Bool} {Δ : BVarCtx} {bvs : TermVarCtx} (hwf : BVarCtxCorresponds uAT Δ bvs)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ) (smtEnv : VarEnv σ SmtArrayTheory) : Prop :=
  ∀ i (τ : LMonoTy) (hbase : LExpr.MonoTyIsBase τ) (hlook : Δ[i]? = some τ),
    let hi : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
    let hbvs : i < bvs.length := hwf.len_eq ▸ hi
    let hty : LExpr.MonoTyIsBase τ ∧ tyToTermType uAT τ = (bvs[i]'hbvs).ty := by
      have := hwf.ty_eq i hi
      rw [(List.getElem?_eq_some_iff.mp hlook).2] at this
      exact this
    cast (tyDenote_eq_smtTyDenote (σ := σ) hty) (bvarVal.get i hlook)
      = smtEnv (bvs[i]'hbvs)

theorem BVarEnvCorresponds_cons {uAT : Bool} {Δ : BVarCtx} {bvs : TermVarCtx}
    {hbwf : BVarCtxCorresponds uAT Δ bvs}
    {bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ}
    {smtEnv : VarEnv σ SmtArrayTheory}
    (henv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    {qty : LMonoTy} {v : TermVar}
    (hty : LExpr.MonoTyIsBase qty ∧ tyToTermType uAT qty = v.ty)
    (x : Lambda.TyDenote simpTcInterp simpTyVarVal qty)
    {smtEnv' : VarEnv σ SmtArrayTheory}
    (hnew : smtEnv' v = cast (tyDenote_eq_smtTyDenote (σ := σ) hty) x)
    (hold : ∀ w, w ≠ v → smtEnv' w = smtEnv w)
    (hbwf' : BVarCtxCorresponds uAT (qty :: Δ) (v :: bvs))
    : BVarEnvCorresponds hbwf' (.cons x bvarVal) smtEnv' := by
  intro i τ hbase_i hlook
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hlook
    subst hlook
    simp only [HList.get_cons_zero, List.getElem_cons_zero]
    rw [hnew]
  | succ j =>
    simp only [List.getElem?_cons_succ] at hlook
    have hj_lt : j < bvs.length := by
      have := (List.getElem?_eq_some_iff.mp hlook).1
      rw [hbwf.len_eq] at this; exact this
    have henv_j := henv j τ hbase_i hlook
    simp only [HList.get_cons_succ, List.getElem_cons_succ]
    have hfresh : v.id ∉ bvs.map (·.id) := by
      have hnd := hbwf'.nodup
      simp only [List.map_cons, List.nodup_cons] at hnd
      exact hnd.1
    have hvne : (bvs[j]'hj_lt) ≠ v := by
      intro hcontra
      apply hfresh
      rw [List.mem_map]
      exact ⟨bvs[j]'hj_lt, List.getElem_mem hj_lt, by rw [hcontra]⟩
    rw [hold _ hvne]
    refine Eq.trans ?_ henv_j
    exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-! ## Leaf _sound lemmas -/
private theorem uf_app_sound_tail
    -- ── LExpr (source) side ──
    {useArrayTheory : Bool} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (htA : LExpr.HasTypeA Δ e (List.foldr LMonoTy.arrow rty acc))
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    -- ── SMT (target) side ──
    {divByZero modByZero : Int → Int}
    {ufs : UFCtx} {bvs : TermVarCtx} {accTms : List Term}
    {name : String} {ufargs : List TermType} {ufout : TermType}
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ (.app (.core (.uf ⟨name, ufargs, ufout⟩)) accTms ufout) = .ok ufout)
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory)
    (accArgVals : HList (TermType.denoteTyped σ SmtArrayTheory) ufargs)
    -- ── correspondence (source ↔ target) ──
    (hacc : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType useArrayTheory) = ufargs)
    (hrty : LExpr.MonoTyIsBase rty ∧ tyToTermType useArrayTheory rty = ufout)
    (h_head_eq : cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal e (List.foldr LMonoTy.arrow rty acc) htA)
        = ufInterp ⟨name, ufargs, ufout⟩)
    (h_denoteArgs : Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero accTms
      (⟨name, ufargs, ufout⟩ : UF).args (tc_uf_inv htc).1 = accArgVals) :
    Term.denoteTyped ufInterp smtEnv divByZero modByZero
        (.app (.core (.uf ⟨name, ufargs, ufout⟩)) accTms ufout) ufout htc
      = UF.applyDenoteTyped' σ SmtArrayTheory ufargs ufout
          (cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
            (simpDenote opInterp fvarVal bvarVal e (List.foldr LMonoTy.arrow rty acc) htA))
          accArgVals := by
  rw [SMTTerm_denote_uf_unfold]
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) ?_
  apply heq_of_eq
  rw [h_denoteArgs, h_head_eq]

theorem fvarHead_sound
    {Γ : SimpTyCtx} {tenv : TranslateEnv} {useArrayTheory : Bool} {Δ : BVarCtx}
    {f : CoreLParams.Identifier} {τ_head : LMonoTy} {acc : List LMonoTy} {rty : LMonoTy}
    -- ── LExpr (source) side ──
    (hspine : LExpr.AppSpine Γ.Φ Γ.Ψ Δ (.fvar () f (some τ_head)) acc rty)
    (haccbase : ∀ t ∈ acc, LExpr.MonoTyIsBase t) (hrtybase : LExpr.MonoTyIsBase rty)
    (htA : LExpr.HasTypeA Δ (.fvar () f (some τ_head)) (List.foldr LMonoTy.arrow rty acc))
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    -- ── SMT (target) side ──
    {divByZero modByZero : Int → Int}
    {ufs : UFCtx} {bvs : TermVarCtx} {accTms : List Term} {accSmt : List TermType}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty)
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory)
    (accArgVals : HList (TermType.denoteTyped σ SmtArrayTheory) accSmt)
    (h_acc_denote : Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero accTms accSmt h_acc_tc = accArgVals)
    -- ── correspondence (source ↔ target) ──
    (h_ok : appTranslate useArrayTheory tenv bvs (.fvar () f (some τ_head)) accTms = .ok tm)
    (haccenc : acc.map (tyToTermType useArrayTheory) = accSmt)
    (hrtyenc : tyToTermType useArrayTheory rty = smtRty)
    (hfvar : FNameCtxCorresponds useArrayTheory Γ.Φ ufs)
    (hfenv : FVarEnvCorresponds hfvar fvarVal ufInterp)
    : Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtRty htc
        = UF.applyDenoteTyped' σ SmtArrayTheory accSmt smtRty
            (cast (tyDenote_arrow_eq_UFDenote'
                (⟨haccbase, haccenc⟩ : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType useArrayTheory) = accSmt)
                (⟨hrtybase, hrtyenc⟩ : LExpr.MonoTyIsBase rty ∧ tyToTermType useArrayTheory rty = smtRty))
              (simpDenote opInterp fvarVal bvarVal (.fvar () f (some τ_head))
                (List.foldr LMonoTy.arrow rty acc) htA))
            accArgVals := by
  match acc, rty, hspine, haccbase, haccenc, h_acc_tc, accArgVals, h_acc_denote, hrtybase, hrtyenc, htA, h_ok, htc with
  | _, _, .fvar f τ_f acc' rty' hmem hcol hb,
      haccbase, haccenc, h_acc_tc, accArgVals, h_acc_denote, hrtybase, hrtyenc, htA, h_ok, htc =>
    have hacc : (∀ t ∈ acc', LExpr.MonoTyIsBase t) ∧ acc'.map (tyToTermType useArrayTheory) = accSmt := ⟨haccbase, haccenc⟩
    have hrty : LExpr.MonoTyIsBase rty' ∧ tyToTermType useArrayTheory rty' = smtRty := ⟨hrtybase, hrtyenc⟩
    have hbridge := hfvar
    have hresolve := hbridge.fvar_resolves f.name τ_f hmem
    obtain ⟨uf, hlk⟩ := Option.isSome_iff_exists.mp hresolve
    obtain ⟨ufid, ufargs, ufout⟩ := uf
    have hid : ufid = f.name := lookupUF_id hlk
    subst hid
    have hargs_uf := hbridge.args_eq f.name τ_f _ hmem hlk
    have hout_uf := hbridge.out_eq f.name τ_f _ hmem hlk
    rw [hcol] at hargs_uf hout_uf
    simp only at hargs_uf hout_uf
    have hacc_eq : ufargs = accSmt := hargs_uf.2.symm.trans hacc.2
    subst hacc_eq
    have hrty_eqU : ufout = smtRty := hout_uf.2.symm.trans hrty.2
    subst hrty_eqU
    have hmem_uf : (⟨f.name, ufargs, ufout⟩ : UF) ∈ ufs := lookupUF_mem hlk
    have hargs_eq : acc'.map (tyToTermType useArrayTheory) = ufargs := hargs_uf.2
    have hrty_eq2 : tyToTermType useArrayTheory rty' = ufout := hout_uf.2
    have htm : tm = .app (.core (.uf ⟨f.name, ufargs, ufout⟩)) accTms ufout := by
      simp only [appTranslate, translateAppHead, hcol,
        hargs_eq, hrty_eq2] at h_ok
      exact (Except.ok.inj h_ok).symm
    subst htm
    have hfe := hfenv f.name τ_f hmem
    have hlk_uf : (lookupUF ufs f.name).get (hbridge.fvar_resolves f.name τ_f hmem)
        = ⟨f.name, ufargs, ufout⟩ := by
      have hsome := hbridge.fvar_resolves f.name τ_f hmem
      change (lookupUF ufs f.name).get hsome = _
      simp only [show lookupUF ufs f.name = some ⟨f.name, ufargs, ufout⟩ from hlk, Option.get_some]
    have h_ufi_heq : HEq (ufInterp ((lookupUF ufs f.name).get (hbridge.fvar_resolves f.name τ_f hmem)))
        (ufInterp ⟨f.name, ufargs, ufout⟩) := by rw [hlk_uf]
    have h_head_eq : cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
        (simpDenote opInterp fvarVal bvarVal (.fvar () f (some τ_f))
          (List.foldr LMonoTy.arrow rty' acc') htA) = ufInterp ⟨f.name, ufargs, ufout⟩ := by
      simp only [simpDenote, LExpr.denote]
      apply eq_of_heq
      refine HEq.trans ?_ (h_ufi_heq)
      refine HEq.trans ?_ (heq_of_eq hfe)
      refine HEq.trans (cast_heq _ _) ?_
      refine HEq.trans
        (subst_heq (P := fun x => Lambda.TyDenote simpTcInterp simpTyVarVal x)
          (HasTypeA.fvar_inv htA) (fvarVal f (τ_f.substTyVars simpTyVarVal))) ?_
      exact (cast_heq _ _).symm
    exact uf_app_sound_tail htA opInterp fvarVal bvarVal htc ufInterp smtEnv accArgVals hacc hrty
      h_head_eq (by rw [← h_acc_denote])

theorem predefinedOp_sound
    -- ── LExpr (source) side ──
    {tenv : TranslateEnv} {useArrayTheory : Bool} {Δ : BVarCtx}
    {o : CoreLParams.Identifier} {oty : LMonoTy} {acc : List LMonoTy} {rty : LMonoTy}
    (hopty : LExpr.CoreOpHasType (CoreOp.ofString (Core.NameMangling.demangledBaseName o.name)) acc rty)
    (hcol : collectArrowTy oty = (acc, rty))
    (haccbase : ∀ t ∈ acc, LExpr.MonoTyIsBase t) (hrtybase : LExpr.MonoTyIsBase rty)
    (htA : LExpr.HasTypeA Δ (.op () o (some oty)) (List.foldr LMonoTy.arrow rty acc))
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    -- ── SMT (target) side ──
    {ufs : UFCtx} {bvs : TermVarCtx} {accTms : List Term} {accSmt : List TermType}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty)
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory)
    (accArgVals : HList (TermType.denoteTyped σ SmtArrayTheory) accSmt)
    -- ── correspondence (source ↔ target) ──
    (h_ok : appTranslate useArrayTheory tenv bvs (.op () o (some oty)) accTms = .ok tm)
    (h_acc_denote : Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero accTms accSmt h_acc_tc = accArgVals)
    (haccenc : acc.map (tyToTermType useArrayTheory) = accSmt)
    (hrtyenc : tyToTermType useArrayTheory rty = smtRty)
    : Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtRty htc
        = UF.applyDenoteTyped' σ SmtArrayTheory accSmt smtRty
            (cast (tyDenote_arrow_eq_UFDenote'
                (⟨haccbase, haccenc⟩ : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType useArrayTheory) = accSmt)
                (⟨hrtybase, hrtyenc⟩ : LExpr.MonoTyIsBase rty ∧ tyToTermType useArrayTheory rty = smtRty))
              (simpDenote opInterp fvarVal bvarVal (.op () o (some oty))
                (List.foldr LMonoTy.arrow rty acc) htA))
            accArgVals := by
  have hacc : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType useArrayTheory) = accSmt := ⟨haccbase, haccenc⟩
  have hrty : LExpr.MonoTyIsBase rty ∧ tyToTermType useArrayTheory rty = smtRty := ⟨hrtybase, hrtyenc⟩
  generalize hcop : CoreOp.ofString (Core.NameMangling.demangledBaseName o.name) = cop at hopty
  have hne : ∀ s, cop ≠ CoreOp.other s := by intro s h; rw [h] at hopty; nomatch hopty
  have hbeq : (Core.NameMangling.demangledBaseName o.name == "Re.Loop") = false := by
    rw [beq_eq_false_iff_ne]; intro hloop
    have hre : CoreOp.ofString "Re.Loop" = CoreOp.re .Loop := by native_decide
    rw [hloop, hre] at hcop; rw [← hcop] at hopty; nomatch hopty
  cases hopty with
  | intNeg =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "int" []] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .int := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, hst, h1⟩ := typeCheckArgs_one_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) .nil := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF1_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.neg o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.neg [t1] .int) .int htc
        = cast (by rw [(Term.typeCheck_intUn_inv htc).2])
            (-(Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intUn_inv htc).1)) := by
      simp only [Term.denoteTyped]; obtain ⟨ht, heq⟩ := Term.typeCheck_intUn_inv htc; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intUn_inv htc).1 h1]; simp only [cast_eq]
  | boolNot =>
    have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "bool" []] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.bool] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, hst, h1⟩ := typeCheckArgs_one_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1) .nil := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF1_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.not o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app (.core .not) [t1] .bool) .bool htc
        = cast (by rw [(Term.typeCheck_not_inv htc).2])
            (!(Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool (Term.typeCheck_not_inv htc).1)) := by
      simp only [Term.denoteTyped]; obtain ⟨ht, heq⟩ := Term.typeCheck_not_inv htc; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_not_inv htc).1 h1]; simp only [cast_eq]
  | intAdd =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .int := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.add o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.add [t1, t2] .int) .int htc
        = cast (by rw [(Term.typeCheck_intBin_inv htc (.inl rfl)).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).1) + (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).2.1)) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inl rfl)).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inl rfl)).2.1 h2]
    simp only [cast_eq]
  | intSub =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .int := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.sub o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.sub [t1, t2] .int) .int htc
        = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).1) - (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.1)) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.1 h2]
    simp only [cast_eq]
  | intMul =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .int := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.mul o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.mul [t1, t2] .int) .int htc
        = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).1) * (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1)) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1 h2]
    simp only [cast_eq]
  | intDiv =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .int := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.div o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.div [t1, t2] .int) .int htc
        = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2])
            (if (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1) = 0
             then divByZero (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1)
             else (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1) / (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1)) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1 h2]
    simp only [cast_eq]
  | intMod =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "int" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .int := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.mod_ o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.mod [t1, t2] .int) .int htc
        = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2])
            (if (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1) = 0
             then modByZero (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1)
             else (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1) % (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1)) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1 h1, proof_irrel (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1 h2]
    simp only [cast_eq]
  | intLt =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.lt o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.lt [t1, t2] .bool) .bool htc
        = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.2]) (decide ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).1) < (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.1))) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).1 h1, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.1 h2]
    simp only [cast_eq]
  | intLe =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.le o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.le [t1, t2] .bool) .bool htc
        = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inl rfl)).2.2]) (decide ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).1) ≤ (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.1))) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intCmp_inv htc (.inl rfl)).1 h1, proof_irrel (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.1 h2]
    simp only [cast_eq]
  | intGt =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.gt o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.gt [t1, t2] .bool) .bool htc
        = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.2]) (decide ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).1) > (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1))) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).1 h1, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1 h2]
    simp only [cast_eq]
  | intGe =>
    have hoty : oty = .tcons "arrow" [.tcons "int" [], .tcons "arrow" [.tcons "int" [], .tcons "bool" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.int, .int] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.ge o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.ge [t1, t2] .bool) .bool htc
        = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.2]) (decide ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).1) ≥ (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1))) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).1 h1, proof_irrel (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1 h2]
    simp only [cast_eq]
  | boolAnd =>
    have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.bool, .bool] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.and_ o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.and [t1, t2] .bool) .bool htc
        = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inl rfl)).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).1) && (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).2.1)) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_boolBin_inv htc (.inl rfl)).1 h1, proof_irrel (Term.typeCheck_boolBin_inv htc (.inl rfl)).2.1 h2]
    simp only [cast_eq]
  | boolOr =>
    have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.bool, .bool] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.or_ o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.or [t1, t2] .bool) .bool htc
        = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.2]) ((Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).1) || (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.1)) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).1 h1, proof_irrel (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.1 h2]
    simp only [cast_eq]
  | boolImplies =>
    have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.bool, .bool] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.implies o.name hcop))]
    have hrhs : Term.denoteTyped ufInterp smtEnv divByZero modByZero (.app Op.implies [t1, t2] .bool) .bool htc
        = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.2]) ((!(Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).1)) || (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.1)) := by
      simp only [Term.denoteTyped]; split; rfl
    rw [hrhs, proof_irrel (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).1 h1, proof_irrel (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.1 h2]
    simp only [cast_eq]
  | boolEquiv =>
    have hoty : oty = .tcons "arrow" [.tcons "bool" [], .tcons "arrow" [.tcons "bool" [], .tcons "bool" []]] := by
      have := collectArrowTy_foldr oty; rw [hcol] at this; simpa [List.foldr, LMonoTy.arrow] using this
    subst hoty
    have haccEq : accSmt = [.bool, .bool] := by
      have h := hacc.2; simp only [List.map_cons, List.map_nil, tyToTermType] at h; exact h.symm
    subst haccEq
    have hrtyEq : smtRty = .bool := by
      have h := hrty.2; simp only [tyToTermType] at h; exact h.symm
    subst hrtyEq
    obtain ⟨t1, t2, hst, h1, h2⟩ := typeCheckArgs_two_inv h_acc_tc; subst hst
    simp only [appTranslate, translateAppHead, hcol, hbeq, Bool.false_eq_true, if_false,
      hcop, corePredefinedOpToSMTOp, tyToTermType] at h_ok
    injection h_ok with h_ok; subst h_ok
    have h_av : accArgVals = .cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t1 .bool h1) (.cons (Term.denoteTyped ufInterp smtEnv divByZero modByZero t2 .bool h2) .nil) := by
      rw [← h_acc_denote]; rfl
    subst h_av
    rw [applyUF2_of_cons opInterp fvarVal bvarVal htA hacc hrty (heq_of_eq (hop.equiv o.name hcop))]
    -- SMT `.eq` denotes via `Classical.propDecidable` at the operand type; bridge to the LExpr `decide`
    -- at `.bool` via `SMTTerm_denote_cast` and reconcile the two decidability instances.
    rw [SMTTerm_denote_eq_unfold]
    simp only [cast_eq]
    have hτ' : (Term.typeCheck_eq_inv htc).1 = .bool :=
      Except.ok.inj ((Term.typeCheck_eq_inv htc).2.1.symm.trans h1)
    have hd1 := SMTTerm_denote_cast ufInterp smtEnv (divByZero := divByZero) (modByZero := modByZero)
      t1 .bool (Term.typeCheck_eq_inv htc).1 h1 (Term.typeCheck_eq_inv htc).2.1 hτ'.symm
    have hd2 := SMTTerm_denote_cast ufInterp smtEnv (divByZero := divByZero) (modByZero := modByZero)
      t2 .bool (Term.typeCheck_eq_inv htc).1 h2 (Term.typeCheck_eq_inv htc).2.2.1 hτ'.symm
    congr 1; apply propext; constructor
    · intro heq'; exact eq_of_heq (hd1.trans ((heq_of_eq heq').trans hd2.symm))
    · intro heq'; exact eq_of_heq (hd1.symm.trans ((heq_of_eq heq').trans hd2))

theorem userFnOp_sound
    {Γ : SimpTyCtx} {tenv : TranslateEnv} {useArrayTheory : Bool} {Δ : BVarCtx}
    {o : CoreLParams.Identifier} {oty : LMonoTy} {acc : List LMonoTy} {rty : LMonoTy}
    -- ── LExpr (source) side ──
    (hmem : (o.name, oty) ∈ Γ.Ψ)
    (hcol : collectArrowTy oty = (acc, rty))
    (haccbase : ∀ t ∈ acc, LExpr.MonoTyIsBase t) (hrtybase : LExpr.MonoTyIsBase rty)
    (htA : LExpr.HasTypeA Δ (.op () o (some oty)) (List.foldr LMonoTy.arrow rty acc))
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    -- ── SMT (target) side ──
    {divByZero modByZero : Int → Int}
    {ufs : UFCtx} {bvs : TermVarCtx} {accTms : List Term} {accSmt : List TermType}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty)
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory)
    (accArgVals : HList (TermType.denoteTyped σ SmtArrayTheory) accSmt)
    (h_acc_denote : Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero accTms accSmt h_acc_tc = accArgVals)
    -- ── disjointness (user-fn name misses predefined-op / datatype-op tables) ──
    (h_pre_none : corePredefinedOpToSMTOp useArrayTheory
      (CoreOp.ofString (Core.NameMangling.demangledBaseName o.name)) = none)
    (h_dt_none : tenv.datatypeFuns.find? (Core.NameMangling.demangledBaseName o.name) = none)
    -- ── correspondence (source ↔ target) ──
    (h_ok : appTranslate useArrayTheory tenv bvs (.op () o (some oty)) accTms = .ok tm)
    (haccenc : acc.map (tyToTermType useArrayTheory) = accSmt)
    (hrtyenc : tyToTermType useArrayTheory rty = smtRty)
    (hfn : FNameCtxCorresponds useArrayTheory Γ.Ψ ufs)
    (hopenv : FnEnvCorresponds hfn opInterp ufInterp)
    : Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtRty htc
        = UF.applyDenoteTyped' σ SmtArrayTheory accSmt smtRty
            (cast (tyDenote_arrow_eq_UFDenote'
                (⟨haccbase, haccenc⟩ : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType useArrayTheory) = accSmt)
                (⟨hrtybase, hrtyenc⟩ : LExpr.MonoTyIsBase rty ∧ tyToTermType useArrayTheory rty = smtRty))
              (simpDenote opInterp fvarVal bvarVal (.op () o (some oty))
                (List.foldr LMonoTy.arrow rty acc) htA))
            accArgVals := by
  have hacc : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType useArrayTheory) = accSmt := ⟨haccbase, haccenc⟩
  have hrty : LExpr.MonoTyIsBase rty ∧ tyToTermType useArrayTheory rty = smtRty := ⟨hrtybase, hrtyenc⟩
  have hresolve := hfn.fvar_resolves o.name oty hmem
  obtain ⟨uf, hlk⟩ := Option.isSome_iff_exists.mp hresolve
  obtain ⟨ufid, ufargs, ufout⟩ := uf
  have hid : ufid = o.name := lookupUF_id hlk
  subst hid
  have hargs_uf := hfn.args_eq o.name oty _ hmem hlk
  have hout_uf := hfn.out_eq o.name oty _ hmem hlk
  rw [hcol] at hargs_uf hout_uf
  simp only at hargs_uf hout_uf
  have hacc_eq : ufargs = accSmt := hargs_uf.2.symm.trans hacc.2
  subst hacc_eq
  have hrty_eqU : ufout = smtRty := hout_uf.2.symm.trans hrty.2
  subst hrty_eqU
  have hmem_uf : (⟨o.name, ufargs, ufout⟩ : UF) ∈ ufs := lookupUF_mem hlk
  have hargs_eq : acc.map (tyToTermType useArrayTheory) = ufargs := hargs_uf.2
  have hrty_eq2 : tyToTermType useArrayTheory rty = ufout := hout_uf.2
  have hbeq_loop : (Core.NameMangling.demangledBaseName o.name == "Re.Loop") = false := by
    rw [beq_eq_false_iff_ne]; exact ne_reLoop_of_corePredefinedOpToSMTOp_none h_pre_none
  have htm : tm = .app (.core (.uf ⟨o.name, ufargs, ufout⟩)) accTms ufout := by
    simp only [appTranslate, translateAppHead, hbeq_loop, Bool.false_eq_true, if_false,
      h_pre_none, h_dt_none, hcol, hargs_eq, hrty_eq2] at h_ok
    exact (Except.ok.inj h_ok).symm
  subst htm
  have hoe := hopenv o.name oty hmem
  have hlk_uf : (lookupUF ufs o.name).get (hfn.fvar_resolves o.name oty hmem)
      = ⟨o.name, ufargs, ufout⟩ := by
    have hsome := hfn.fvar_resolves o.name oty hmem
    change (lookupUF ufs o.name).get hsome = _
    simp only [show lookupUF ufs o.name = some ⟨o.name, ufargs, ufout⟩ from hlk, Option.get_some]
  have h_ufi_heq : HEq (ufInterp ((lookupUF ufs o.name).get (hfn.fvar_resolves o.name oty hmem)))
      (ufInterp ⟨o.name, ufargs, ufout⟩) := by rw [hlk_uf]
  have h_head_eq : cast (tyDenote_arrow_eq_UFDenote' hacc hrty)
      (simpDenote opInterp fvarVal bvarVal (.op () o (some oty))
        (List.foldr LMonoTy.arrow rty acc) htA) = ufInterp ⟨o.name, ufargs, ufout⟩ := by
    simp only [simpDenote, LExpr.denote]
    apply eq_of_heq
    refine HEq.trans ?_ (h_ufi_heq)
    refine HEq.trans ?_ (heq_of_eq hoe)
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans
      (subst_heq (P := fun x => Lambda.TyDenote simpTcInterp simpTyVarVal x)
        (HasTypeA.op_inv htA) (opInterp o.name (oty.substTyVars simpTyVarVal))) ?_
    exact (cast_heq _ _).symm
  exact uf_app_sound_tail htA opInterp fvarVal bvarVal htc ufInterp smtEnv accArgVals hacc hrty
    h_head_eq (by rw [← h_acc_denote])

theorem quant_step_sound
    {uAT : Bool} {Δ : BVarCtx} {bvs : TermVarCtx}
    {qty : LMonoTy} {v : TermVar} {name : String}
    {k : Lambda.QuantifierKind} {tr body : Expression.Expr}
    {divByZero modByZero : Int → Int}
    {ufs : UFCtx} {trGroups : List (List Term)} {bodyTm : Term}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    (hbwf : BVarCtxCorresponds uAT Δ bvs)
    (hbwf' : BVarCtxCorresponds uAT (qty :: Δ) (v :: bvs))
    (hty : LExpr.MonoTyIsBase qty ∧ tyToTermType uAT qty = v.ty)
    (htA : LExpr.HasTypeA Δ (.quant () k name (some qty) tr body) (.tcons "bool" []))
    (hbodyA : LExpr.HasTypeA (qty :: Δ) body (.tcons "bool" []))
    (hbodyTm_tc : Term.typeCheck ⟨[], ufs, v :: bvs⟩ bodyTm = .ok .bool)
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ (Strata.SMT.Factory.quant (coreQK k) v.id v.ty trGroups bodyTm) = .ok .bool)
    (hN_tc : Term.typeCheck ⟨[], ufs, bvs⟩ (.quant (coreQK k) [v] trGroups bodyTm) = .ok .bool)
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    (hbody_sound : ∀ (y : Lambda.TyDenote simpTcInterp simpTyVarVal qty) (smtEnv' : VarEnv σ SmtArrayTheory),
      BVarEnvCorresponds hbwf' (.cons y bvarVal) smtEnv' →
      (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal (.cons y bvarVal) body
        (.tcons "bool" []) hbodyA : Bool)
        = Term.denoteTyped ufInterp smtEnv' divByZero modByZero bodyTm .bool hbodyTm_tc)
    : cast (tyDenote_eq_smtTyDenote (σ := σ) (show LExpr.MonoTyIsBase (.tcons "bool" []) ∧ tyToTermType uAT (.tcons "bool" []) = .bool from ⟨.bool, by simp only [tyToTermType]⟩))
        (simpDenote opInterp fvarVal bvarVal (.quant () k name (some qty) tr body) (.tcons "bool" []) htA)
      = Term.denoteTyped ufInterp smtEnv divByZero modByZero
          (Strata.SMT.Factory.quant (coreQK k) v.id v.ty trGroups bodyTm) .bool htc := by
  rw [Factory.quant_correct ufInterp smtEnv divByZero modByZero (coreQK k) v.id v.ty trGroups bodyTm htc hN_tc]
  have h_ty_eq := tyDenote_eq_smtTyDenote (σ := σ) hty
  simp only [simpDenote]
  apply eq_of_heq
  apply HEq.trans (cast_heq _ _)
  unfold LExpr.denote Term.denoteTyped
  dsimp only []
  obtain ⟨_, _, _, h_body_inv⟩ := HasTypeA.quant_inv htA
  obtain ⟨hbody_inv, heq_inv⟩ := Term.typeCheck_quant_inv hN_tc
  dsimp only []
  apply HEq.trans _ (cast_heq _ _).symm
  apply heq_of_eq
  congr 1
  apply propext
  have h_pi1 : h_body_inv = hbodyA := proof_irrel _ _
  have h_pi2 : hbody_inv = hbodyTm_tc := proof_irrel _ _
  rw [h_pi1, h_pi2]
  have bridge : ∀ (y : Lambda.TyDenote simpTcInterp simpTyVarVal qty) (ext : VarEnv σ SmtArrayTheory)
      (hxy : ext v = cast h_ty_eq y),
      (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal (.cons y bvarVal) body
        (.tcons "bool" []) hbodyA : Bool) = true ↔
      Term.denoteTyped ufInterp (fun w => if _hv : w ∈ [v] then ext w else smtEnv w)
        divByZero modByZero bodyTm .bool hbodyTm_tc = true := by
    intro y ext hxy
    let smtEnv' : VarEnv σ SmtArrayTheory := fun w => if _hv : w ∈ [v] then ext w else smtEnv w
    have hcorr : BVarEnvCorresponds hbwf' (.cons y bvarVal) smtEnv' :=
      BVarEnvCorresponds_cons hbenv hty y
        (show smtEnv' v = cast h_ty_eq y by
          simp only [smtEnv', List.mem_singleton, dif_pos rfl]; exact hxy)
        (show ∀ w, w ≠ v → smtEnv' w = smtEnv w by
          intro w hwne
          simp only [smtEnv', List.mem_singleton, dif_neg hwne])
        hbwf'
    have hbe := hbody_sound y smtEnv' hcorr
    exact ⟨fun h => hbe ▸ h, fun h => hbe ▸ h⟩
  cases k with
  | all =>
    simp only [coreQK]
    constructor
    · intro hx ext
      let z := ext v
      exact (bridge (cast h_ty_eq.symm z) ext (by simp [z, cast_cast])).mp (hx _)
    · intro hext y
      let ext : VarEnv σ SmtArrayTheory := fun w =>
        if hw : w = v then cast (by rw [hw]; exact h_ty_eq) y else smtEnv w
      have hextv : ext v = cast h_ty_eq y := by simp [ext]
      exact (bridge y ext hextv).mpr (hext ext)
  | exist =>
    simp only [coreQK]
    constructor
    · intro ⟨y, hy⟩
      let ext : VarEnv σ SmtArrayTheory := fun w =>
        if hw : w = v then cast (by rw [hw]; exact h_ty_eq) y else smtEnv w
      have hextv : ext v = cast h_ty_eq y := by simp [ext]
      exact ⟨ext, (bridge y ext hextv).mp hy⟩
    · intro ⟨ext, hext⟩
      let z := ext v
      exact ⟨cast h_ty_eq.symm z,
        (bridge (cast h_ty_eq.symm z) ext (by simp [z, cast_cast])).mpr hext⟩

/-! ## Headline mutual denotation block -/
mutual
/-- **`translate` denotational soundness.** The Core denotation (`simpDenote`) equals — under the
    sort-coercion cast — the SMT denotation of the translated term. Mutually recursive with
    `appTranslate_sound`. -/
theorem translate_sound
    -- ── LExpr (source) side ──
    {Γ : SimpTyCtx} {tenv : TranslateEnv} {useArrayTheory : Bool} {Δ : BVarCtx}
    {e : Expression.Expr} {τ : LMonoTy}
    (he : LExpr.HasSimpType Γ.Φ Γ.Ψ Δ e τ) (htA : LExpr.HasTypeA Δ e τ)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    -- ── SMT (target) side ──
    {divByZero modByZero : Int → Int}
    {ufs : UFCtx} {bvs : TermVarCtx} {smtTy : TermType} {tm : Term}
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtTy)
    (huf : UFCtxWF ufs)
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory)
    -- ── correspondence (source ↔ target) ──
    (h_ok : translate useArrayTheory tenv bvs e = .ok tm)
    (hτenc : tyToTermType useArrayTheory τ = smtTy)
    (hfvar : FNameCtxCorresponds useArrayTheory Γ.Φ ufs)
    (hfn : FNameCtxCorresponds useArrayTheory Γ.Ψ ufs)
    (hbwf : BVarCtxCorresponds useArrayTheory Δ bvs)
    (hused : ∀ nm ∈ (Γ.Φ ++ Γ.Ψ).map Prod.fst, (staticUsedNames tenv).contains nm)
    (havoid : ∀ v ∈ bvs, v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst)
    (hfenv : FVarEnvCorresponds hfvar fvarVal ufInterp)
    (hopenv : FnEnvCorresponds hfn opInterp ufInterp)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    (hop : OpInterpConsistent divByZero modByZero opInterp)
    (hfnwf : FnNamesNotPredefined Γ.Ψ useArrayTheory)
    (hdtfree : tenv.datatypeFuns = ∅)
    : cast (tyDenote_eq_smtTyDenote (σ := σ) (⟨HasSimpType_base he, hτenc⟩ : LExpr.MonoTyIsBase τ ∧ tyToTermType useArrayTheory τ = smtTy))
        (simpDenote opInterp fvarVal bvarVal e τ htA)
      = Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtTy htc := by
  match e, τ, he, hτenc, htA, h_ok, htc with
  | _, _, .const c hb, hτenc, htA, h_ok, htc =>
    cases c with
    | boolConst b =>
      have htm : tm = .prim (.bool b) := by simp [translate] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, Term.denoteTyped, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ b).trans
        (@subst_heq _ (TermType.denoteTyped σ SmtArrayTheory) _ _ (Term.typeCheck_prim_inv htc) b).symm)
    | intConst i =>
      have htm : tm = .prim (.int i) := by simp [translate] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, Term.denoteTyped, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ i).trans
        (@subst_heq _ (TermType.denoteTyped σ SmtArrayTheory) _ _ (Term.typeCheck_prim_inv htc) i).symm)
    | strConst s =>
      have htm : tm = .prim (.string s) := by simp [translate] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, Term.denoteTyped, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ s).trans
        (@subst_heq _ (TermType.denoteTyped σ SmtArrayTheory) _ _ (Term.typeCheck_prim_inv htc) s).symm)
    | bitvecConst n bv =>
      have htm : tm = .prim (.bitvec bv) := by simp [translate] at h_ok; exact h_ok.symm
      subst htm
      simp only [simpDenote, LExpr.denote, Lambda.denoteConst, Term.denoteTyped, TermPrim.typeOf]
      exact eq_of_heq ((cast_heq _ bv).trans
        (@subst_heq _ (TermType.denoteTyped σ SmtArrayTheory) _ _ (Term.typeCheck_prim_inv htc) bv).symm)
    | realConst _ =>
      simp only [LConst.ty, LMonoTy.real] at hb
      exact absurd hb not_MonoTyIsBase_real
  | _, _, .bvar i τ' hlook hb, hτenc, htA, h_ok, htc =>
    have hi : i < bvs.length := by
      have hi_Δ : i < Δ.length := (List.getElem?_eq_some_iff.mp hlook).1
      exact hbwf.len_eq ▸ hi_Δ
    have htm : tm = .var (bvs[i]) := by
      unfold translate at h_ok; rw [dif_pos hi] at h_ok
      simp at h_ok; exact h_ok.symm
    subst htm
    simp only [simpDenote, LExpr.denote]
    have hcorr := hbenv i τ' hb hlook
    apply eq_of_heq
    refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans ?_ (SMTTerm_denote_var_heq ufInterp smtEnv _ _ htc).symm
    exact (cast_heq _ _).symm.trans (heq_of_eq hcorr)
  | _, _, .app fn arg rty hspine, hτenc, htA, h_ok, htc =>
    -- fvar-headed application: fold into `appTranslate (.app fn arg) []`, delegate to the spine lemma.
    have h_ok' : appTranslate useArrayTheory tenv bvs (.app () fn arg) [] = .ok tm := by
      rw [appTranslate]; rw [translate] at h_ok; exact h_ok
    have hres := appTranslate_sound hspine htA opInterp fvarVal bvarVal
      (show Term.typeCheckArgs ⟨[], ufs, bvs⟩ [] [] = true from rfl) htc huf ufInterp smtEnv
      HList.nil (show Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero [] [] rfl = HList.nil from rfl)
      h_ok' hfvar hfn hbwf hused havoid hfenv hopenv hbenv hop hfnwf hdtfree
      (haccbase := (by simp)) (haccenc := rfl)
      (hrtyenc := hτenc)
    rw [hres]; rfl
  | _, _, .fvarNullary f τ_f rty hspine, hτenc, htA, h_ok, htc =>
    have h_ok' : appTranslate useArrayTheory tenv bvs (.fvar () f (some τ_f)) [] = .ok tm := by
      rw [translate] at h_ok; exact h_ok
    have hres := appTranslate_sound hspine
      htA opInterp fvarVal bvarVal
      (show Term.typeCheckArgs ⟨[], ufs, bvs⟩ [] [] = true from rfl) htc huf ufInterp smtEnv
      HList.nil (show Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero [] [] rfl = HList.nil from rfl)
      h_ok' hfvar hfn hbwf hused havoid hfenv hopenv hbenv hop hfnwf hdtfree
      (haccbase := (by simp)) (haccenc := rfl)
      (hrtyenc := hτenc)
    rw [hres]; rfl
  | _, _, .ite c t τ' e_ hc ht hee, hτenc, htA, h_ok, htc =>
    have hbase := HasSimpType_base (LExpr.HasSimpType.ite c t τ' e_ hc ht hee)
    have hτ : LExpr.MonoTyIsBase _ ∧ tyToTermType useArrayTheory _ = smtTy := ⟨hbase, hτenc⟩
    cases hc_ok : translate useArrayTheory tenv bvs c with
    | error _ => rw [translate] at h_ok; rw [hc_ok] at h_ok; simp [bind, Except.bind] at h_ok
    | ok ct =>
      cases ht_ok : translate useArrayTheory tenv bvs t with
      | error _ => rw [translate] at h_ok; rw [hc_ok, ht_ok] at h_ok; simp [bind, Except.bind] at h_ok
      | ok tt =>
        cases he_ok : translate useArrayTheory tenv bvs e_ with
        | error _ => rw [translate] at h_ok; rw [hc_ok, ht_ok, he_ok] at h_ok; simp [bind, Except.bind] at h_ok
        | ok et =>
          have htm : tm = Factory.ite ct tt et := by
            rw [translate] at h_ok
            simp only [hc_ok, ht_ok, he_ok, bind, Except.bind, Except.ok.injEq] at h_ok
            exact h_ok.symm
          subst htm
          have hc_enc : LExpr.MonoTyIsBase (.tcons "bool" []) ∧
              tyToTermType useArrayTheory (.tcons "bool" []) = .bool := ⟨.bool, by simp only [tyToTermType]⟩
          have hctc := translate_typeChecks hc huf hc_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
            (hτenc := hc_enc.2)
          have httc := translate_typeChecks ht huf ht_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
            (hτenc := hτ.2)
          have hetc := translate_typeChecks hee huf he_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
            (hτenc := hτ.2)
          rw [Factory_ite_denoteTyped ufInterp smtEnv (hτ.2 ▸ tyToTermType_isBase hτ.1) hctc httc hetc]
          have ihc := translate_sound hc (HasSimpType_implies_HasTypeA hc)
            opInterp fvarVal bvarVal hctc huf ufInterp smtEnv hc_ok hc_enc.2 hfvar hfn hbwf hused havoid hfenv hopenv hbenv hop hfnwf hdtfree
          have iht := translate_sound ht (HasSimpType_implies_HasTypeA ht)
            opInterp fvarVal bvarVal httc huf ufInterp smtEnv ht_ok hτ.2 hfvar hfn hbwf hused havoid hfenv hopenv hbenv hop hfnwf hdtfree
          have ihe := translate_sound hee (HasSimpType_implies_HasTypeA hee)
            opInterp fvarVal bvarVal hetc huf ufInterp smtEnv he_ok hτ.2 hfvar hfn hbwf hused havoid hfenv hopenv hbenv hop hfnwf hdtfree
          have h_ite_unfold := Lambda.denote_ite (T := CoreLParams) (tcInterp := simpTcInterp)
            (opInterp := opInterp) (fvarVal := fvarVal) (vt := simpTyVarVal) bvarVal
            (HasSimpType_implies_HasTypeA hc) (HasSimpType_implies_HasTypeA ht)
            (HasSimpType_implies_HasTypeA hee) htA
          simp only [simpDenote] at ihc iht ihe ⊢
          rw [h_ite_unfold]
          apply bif_heq_of_cond_branches (tyDenote_eq_smtTyDenote (σ := σ) hτ)
          · exact eq_of_heq ((cast_heq _ _).symm.trans (heq_of_eq ihc))
          · exact (cast_heq _ _).symm.trans (heq_of_eq iht)
          · exact (cast_heq _ _).symm.trans (heq_of_eq ihe)
  | _, _, .eq e1 e2 τ' hb he1 he2, hτenc, htA, h_ok, htc =>
    have hsmt : smtTy = .bool := by have h2 := hτenc; simp only [tyToTermType] at h2; exact h2.symm
    subst hsmt
    cases h1_ok : translate useArrayTheory tenv bvs e1 with
    | error _ => rw [translate] at h_ok; rw [h1_ok] at h_ok; simp [bind, Except.bind] at h_ok
    | ok t1 =>
      cases h2_ok : translate useArrayTheory tenv bvs e2 with
      | error _ => rw [translate] at h_ok; rw [h1_ok, h2_ok] at h_ok; simp [bind, Except.bind] at h_ok
      | ok t2 =>
        have htm : tm = Factory.eq t1 t2 := by
          rw [translate] at h_ok
          simp only [h1_ok, h2_ok, bind, Except.bind, Except.ok.injEq] at h_ok
          exact h_ok.symm
        subst htm
        have hτ'enc : LExpr.MonoTyIsBase τ' ∧ tyToTermType useArrayTheory τ' = tyToTermType useArrayTheory τ' := ⟨hb, rfl⟩
        have htc1 := translate_typeChecks he1 huf h1_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
          (hτenc := hτ'enc.2)
        have htc2 := translate_typeChecks he2 huf h2_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
          (hτenc := hτ'enc.2)
        have ih1 := translate_sound he1 (HasSimpType_implies_HasTypeA he1)
          opInterp fvarVal bvarVal htc1 huf ufInterp smtEnv h1_ok hτ'enc.2 hfvar hfn hbwf hused havoid hfenv hopenv hbenv hop hfnwf hdtfree
        have ih2 := translate_sound he2 (HasSimpType_implies_HasTypeA he2)
          opInterp fvarVal bvarVal htc2 huf ufInterp smtEnv h2_ok hτ'enc.2 hfvar hfn hbwf hused havoid hfenv hopenv hbenv hop hfnwf hdtfree
        simp only [simpDenote] at ih1 ih2 ⊢
        by_cases heq_vals : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal e1 τ'
            (HasSimpType_implies_HasTypeA he1)
          = LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal e2 τ'
            (HasSimpType_implies_HasTypeA he2)
        · have h_lhs : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
              (.eq () e1 e2) (.tcons "bool" []) htA = true :=
            Lambda.denote_eq_true bvarVal (HasSimpType_implies_HasTypeA he1)
              (HasSimpType_implies_HasTypeA he2) htA heq_vals
          rw [h_lhs]
          have hvals_smt : Term.denoteTyped ufInterp smtEnv divByZero modByZero t1
              (tyToTermType useArrayTheory τ') htc1
            = Term.denoteTyped ufInterp smtEnv divByZero modByZero t2
              (tyToTermType useArrayTheory τ') htc2 := by rw [← ih1, ← ih2, heq_vals]
          rw [Factory_eq_denote_true ufInterp smtEnv (hτ'enc.2 ▸ tyToTermType_isBase hτ'enc.1) htc1 htc2 htc hvals_smt]
          exact eq_of_heq (cast_heq _ _)
        · have h_lhs : LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal
              (.eq () e1 e2) (.tcons "bool" []) htA = false :=
            Lambda.denote_eq_false bvarVal (HasSimpType_implies_HasTypeA he1)
              (HasSimpType_implies_HasTypeA he2) htA heq_vals
          rw [h_lhs]
          have hvals_smt : Term.denoteTyped ufInterp smtEnv divByZero modByZero t1
              (tyToTermType useArrayTheory τ') htc1
            ≠ Term.denoteTyped ufInterp smtEnv divByZero modByZero t2
              (tyToTermType useArrayTheory τ') htc2 := by
            intro hw
            apply heq_vals
            have hc : cast (tyDenote_eq_smtTyDenote (σ := σ) hτ'enc)
                (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal e1 τ'
                  (HasSimpType_implies_HasTypeA he1))
              = cast (tyDenote_eq_smtTyDenote (σ := σ) hτ'enc)
                (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal bvarVal e2 τ'
                  (HasSimpType_implies_HasTypeA he2)) := by rw [ih1, ih2]; exact hw
            exact cast_inj_of_eq _ _ _ hc
          rw [Factory_eq_denote_false ufInterp smtEnv (hτ'enc.2 ▸ tyToTermType_isBase hτ'enc.1) htc1 htc2 htc hvals_smt]
          exact eq_of_heq (cast_heq _ _)
  | _, _, .quant qty qbody qk qname qtr qτtr hb htr hbody, hτenc, htA, h_ok, htc =>
    -- `.quant` arm. `translate` emits `Factory.quant (coreQK qk) v.id v.ty trTm bodyTm`; `quant_step_sound`
    -- strips the coalescing (`Factory.quant_correct`) and bridges each quantifier witness
    -- (`BVarEnvCorresponds_cons`) using the body-soundness IH.
    have hτ_bool : smtTy = .bool := by simp only [tyToTermType] at hτenc; exact hτenc.symm
    subst hτ_bool
    obtain ⟨base, start, trGroups, bodyTm, hbody_ok', htrig, htm⟩ := translate_quant_inv h_ok
    subst htm
    obtain ⟨hv_bvs, hv_static⟩ := findUnique_quant_fresh tenv bvs base start
    have hbwf' : BVarCtxCorresponds useArrayTheory (qty :: Δ)
        (⟨Strata.Name.findUnique base start (quantUsedNames tenv bvs), tyToTermType useArrayTheory qty⟩ :: bvs) :=
      BVarCtxCorresponds_cons hbwf hb rfl hv_bvs
    have hv_ctx : (Strata.Name.findUnique base start (quantUsedNames tenv bvs))
        ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst := fun hmem => hv_static (hused _ hmem)
    have havoid' : ∀ v ∈ (⟨Strata.Name.findUnique base start (quantUsedNames tenv bvs),
        tyToTermType useArrayTheory qty⟩ : TermVar) :: bvs,
        v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hv_ctx
      · exact havoid w hw
    have hbool_enc : LExpr.MonoTyIsBase (.tcons "bool" []) ∧
        tyToTermType useArrayTheory (.tcons "bool" []) = .bool := ⟨.bool, by simp only [tyToTermType]⟩
    have hbodyTm_tc := translate_typeChecks hbody huf hbody_ok'
      hfvar hfn hbwf' hused havoid' hfnwf hdtfree (hτenc := hbool_enc.2)
    -- Naive single-binder type-check (feeding `Factory.quant_correct` in `quant_step_sound`). Same
    -- trigger/bound-sort well-formedness reasoning as the sort-correctness arm.
    have hwftr : Term.wfTriggers ⟨[], ufs,
        ⟨Strata.Name.findUnique base start (quantUsedNames tenv bvs), tyToTermType useArrayTheory qty⟩ :: bvs⟩
        trGroups = true := by
      rcases htrig with ⟨hics, hgroups⟩ | ⟨tt, hics, httt, hgeq⟩
      · obtain ⟨i, hbv⟩ := hasSimpType_trigger_bvar htr hfnwf hics
        rw [hbv] at hgroups
        simp only [translateTriggerGroups, Except.ok.injEq] at hgroups
        subst hgroups
        rfl
      · subst hgeq
        have htt_tc := translate_typeChecks htr huf httt
          hfvar hfn hbwf' hused havoid' hfnwf hdtfree
          (hτenc := rfl)
        simp [Term.wfTriggers, Term.typeCheckAll, htt_tc, Except.toOption]
    have hN_tc := quant_naive_typeCheck (qk := coreQK qk) (uAT := useArrayTheory) hb rfl hbodyTm_tc hwftr
    have hbodyA : LExpr.HasTypeA (qty :: Δ) qbody (.tcons "bool" []) := HasSimpType_implies_HasTypeA hbody
    have hbody_sound : ∀ (y : Lambda.TyDenote simpTcInterp simpTyVarVal qty) (smtEnv' : VarEnv σ SmtArrayTheory),
        BVarEnvCorresponds hbwf' (.cons y bvarVal) smtEnv' →
        (LExpr.denote simpTcInterp opInterp fvarVal simpTyVarVal (.cons y bvarVal) qbody
          (.tcons "bool" []) hbodyA : Bool)
          = Term.denoteTyped ufInterp smtEnv' divByZero modByZero bodyTm .bool hbodyTm_tc := by
      intro y smtEnv' henv'
      have ih := translate_sound hbody hbodyA
        opInterp fvarVal (.cons y bvarVal) hbodyTm_tc huf ufInterp smtEnv'
        hbody_ok' hbool_enc.2 hfvar hfn hbwf' hused havoid' hfenv hopenv henv' hop hfnwf hdtfree
      simp only [simpDenote] at ih
      exact eq_of_heq ((cast_heq _ _).symm.trans (heq_of_eq ih))
    exact quant_step_sound opInterp fvarVal bvarVal hbwf hbwf' ⟨hb, rfl⟩ htA hbodyA
      hbodyTm_tc htc hN_tc ufInterp smtEnv hbenv hbody_sound
  termination_by structural he

/-- **App-spine soundness** (companion to `translate_sound`). The fvar-, predefined-op-,
    or user-fn-headed spine's curried denotation, cast to a UF/op denotation and applied to the
    accumulator's argument values, equals the SMT denotation of `appTranslate … e accTms`. The `.op` arm
    delegates to `predefinedOp_sound` (via `hop : OpInterpConsistent`); the `.fnOp` arm to `userFnOp_sound`
    (via `hopenv : FnEnvCorresponds`). Domain is exactly the `AppSpine`-derivable heads. -/
theorem appTranslate_sound
    -- ── LExpr (source) side ──
    {Γ : SimpTyCtx} {tenv : TranslateEnv} {useArrayTheory : Bool} {Δ : BVarCtx}
    {e : Expression.Expr} {acc : List LMonoTy} {rty : LMonoTy}
    (hspine : LExpr.AppSpine Γ.Φ Γ.Ψ Δ e acc rty)
    (haccbase : ∀ t ∈ acc, LExpr.MonoTyIsBase t)
    (htA : LExpr.HasTypeA Δ e (List.foldr LMonoTy.arrow rty acc))
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal Δ)
    -- ── SMT (target) side ──
    {divByZero modByZero : Int → Int}
    {ufs : UFCtx} {bvs : TermVarCtx} {accTms : List Term} {accSmt : List TermType}
    {smtRty : TermType} {tm : Term}
    (h_acc_tc : Term.typeCheckArgs ⟨[], ufs, bvs⟩ accTms accSmt = true)
    (htc : Term.typeCheck ⟨[], ufs, bvs⟩ tm = .ok smtRty)
    (huf : UFCtxWF ufs)
    (ufInterp : UFInterp σ SmtArrayTheory) (smtEnv : VarEnv σ SmtArrayTheory)
    (accArgVals : HList (TermType.denoteTyped σ SmtArrayTheory) accSmt)
    (h_acc_denote : Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero accTms accSmt h_acc_tc = accArgVals)
    -- ── correspondence (source ↔ target) ──
    (h_ok : appTranslate useArrayTheory tenv bvs e accTms = .ok tm)
    (haccenc : acc.map (tyToTermType useArrayTheory) = accSmt)
    (hrtyenc : tyToTermType useArrayTheory rty = smtRty)
    (hfvar : FNameCtxCorresponds useArrayTheory Γ.Φ ufs)
    (hfn : FNameCtxCorresponds useArrayTheory Γ.Ψ ufs)
    (hbwf : BVarCtxCorresponds useArrayTheory Δ bvs)
    (hused : ∀ nm ∈ (Γ.Φ ++ Γ.Ψ).map Prod.fst, (staticUsedNames tenv).contains nm)
    (havoid : ∀ v ∈ bvs, v.id ∉ (Γ.Φ ++ Γ.Ψ).map Prod.fst)
    (hfenv : FVarEnvCorresponds hfvar fvarVal ufInterp)
    (hopenv : FnEnvCorresponds hfn opInterp ufInterp)
    (hbenv : BVarEnvCorresponds hbwf bvarVal smtEnv)
    (hop : OpInterpConsistent divByZero modByZero opInterp)
    (hfnwf : FnNamesNotPredefined Γ.Ψ useArrayTheory)
    (hdtfree : tenv.datatypeFuns = ∅)
    : Term.denoteTyped ufInterp smtEnv divByZero modByZero tm smtRty htc
        = UF.applyDenoteTyped' σ SmtArrayTheory accSmt smtRty
            (cast (tyDenote_arrow_eq_UFDenote'
                (⟨haccbase, haccenc⟩ : (∀ t ∈ acc, LExpr.MonoTyIsBase t) ∧ acc.map (tyToTermType useArrayTheory) = accSmt)
                (⟨AppSpine_base hspine, hrtyenc⟩ : LExpr.MonoTyIsBase rty ∧ tyToTermType useArrayTheory rty = smtRty))
              (simpDenote opInterp fvarVal bvarVal e
                (List.foldr LMonoTy.arrow rty acc) htA))
            accArgVals := by
  match e, acc, rty, hspine, haccbase, haccenc, h_acc_tc, accArgVals, h_acc_denote, hrtyenc, htA, h_ok, htc with
  | _, _, _, .app fn arg aty acc' rty' harg hrest,
      haccbase, haccenc, h_acc_tc, accArgVals, h_acc_denote, hrtyenc, htA, h_ok, htc =>
    have hrtybase := AppSpine_base (LExpr.AppSpine.app fn arg aty acc' rty' harg hrest)
    have hacc : (∀ t ∈ acc', LExpr.MonoTyIsBase t) ∧ acc'.map (tyToTermType useArrayTheory) = accSmt := ⟨haccbase, haccenc⟩
    have hrty : LExpr.MonoTyIsBase rty' ∧ tyToTermType useArrayTheory rty' = smtRty := ⟨hrtybase, hrtyenc⟩
    rw [appTranslate] at h_ok
    cases h_arg_ok : translate useArrayTheory tenv bvs arg with
    | error e => rw [h_arg_ok] at h_ok; simp [bind, Except.bind] at h_ok
    | ok argt =>
      rw [h_arg_ok] at h_ok; simp only [bind, Except.bind] at h_ok
      have hbase_arg : LExpr.MonoTyIsBase aty := HasSimpType_base harg
      have h_saty : LExpr.MonoTyIsBase aty ∧ tyToTermType useArrayTheory aty = tyToTermType useArrayTheory aty := ⟨hbase_arg, rfl⟩
      have h_argt := translate_typeChecks harg huf h_arg_ok hfvar hfn hbwf hused havoid hfnwf hdtfree
        (hτenc := h_saty.2)
      have hacc' : (∀ t ∈ (aty :: acc'), LExpr.MonoTyIsBase t) ∧ (aty :: acc').map (tyToTermType useArrayTheory) = tyToTermType useArrayTheory aty :: accSmt := by
        refine ⟨fun t ht => ?_, ?_⟩
        · rcases List.mem_cons.mp ht with rfl | ht'
          · exact hbase_arg
          · exact hacc.1 t ht'
        · simp only [List.map_cons, hacc.2]
      have h_acc_tc' : Term.typeCheckArgs ⟨[], ufs, bvs⟩ (argt :: accTms) (tyToTermType useArrayTheory aty :: accSmt) = true := by
        simp only [Term.typeCheckArgs, h_argt]; simp [h_acc_tc, BEq.beq]
      have htA_arg : LExpr.HasTypeA Δ arg aty := HasSimpType_implies_HasTypeA harg
      have htA_fn : LExpr.HasTypeA Δ fn (List.foldr LMonoTy.arrow rty' (aty :: acc')) :=
        AppSpine_implies_HasTypeA hrest
      let vArg : TermType.denoteTyped σ SmtArrayTheory (tyToTermType useArrayTheory aty) := Term.denoteTyped ufInterp smtEnv divByZero modByZero argt (tyToTermType useArrayTheory aty) h_argt
      have h_acc_denote' :
          Term.denoteTypedArgs ufInterp smtEnv divByZero modByZero (argt :: accTms) (tyToTermType useArrayTheory aty :: accSmt) h_acc_tc'
            = .cons vArg accArgVals := by
        rw [← h_acc_denote]; rfl
      have h_arg_sound : cast (tyDenote_eq_smtTyDenote (σ := σ) h_saty)
          (simpDenote opInterp fvarVal bvarVal arg aty htA_arg) = vArg :=
        translate_sound harg htA_arg
          opInterp fvarVal bvarVal h_argt huf ufInterp smtEnv h_arg_ok h_saty.2 hfvar hfn hbwf hused havoid
          hfenv hopenv hbenv hop hfnwf hdtfree
      have ih := appTranslate_sound hrest htA_fn opInterp fvarVal bvarVal
        h_acc_tc' htc huf ufInterp smtEnv (.cons vArg accArgVals) h_acc_denote'
        h_ok hfvar hfn hbwf hused havoid hfenv hopenv hbenv hop hfnwf hdtfree
        (haccbase := hacc'.1) (haccenc := hacc'.2) (hrtyenc := hrty.2)
      rw [ih]
      show UF.applyDenoteTyped' σ SmtArrayTheory accSmt smtRty _ accArgVals = UF.applyDenoteTyped' σ SmtArrayTheory accSmt smtRty _ accArgVals
      apply congrArg (fun w => UF.applyDenoteTyped' σ SmtArrayTheory accSmt smtRty w accArgVals)
      rw [← h_arg_sound]
      have happ : simpDenote opInterp fvarVal bvarVal (.app () fn arg)
          (List.foldr LMonoTy.arrow rty' acc') htA
          = (simpDenote opInterp fvarVal bvarVal fn
              (List.foldr LMonoTy.arrow rty' (aty :: acc')) htA_fn)
            (simpDenote opInterp fvarVal bvarVal arg aty htA_arg) := by
        simp only [simpDenote]
        exact Lambda.denote_app (T := CoreLParams) (tcInterp := simpTcInterp)
          (opInterp := opInterp) (fvarVal := fvarVal) (vt := simpTyVarVal)
          bvarVal htA_fn htA_arg htA
      rw [happ]
      exact cast_arrow_app (tyDenote_eq_smtTyDenote (σ := σ) h_saty)
        (tyDenote_arrow_eq_UFDenote' hacc hrty) (tyDenote_arrow_eq_UFDenote' hacc' hrty)
        (simpDenote opInterp fvarVal bvarVal fn (List.foldr LMonoTy.arrow rty' (aty :: acc')) htA_fn)
        (simpDenote opInterp fvarVal bvarVal arg aty htA_arg)
  | _, _, _, .fvar f τ_f acc' rty' hmem hcol hb,
      haccbase, haccenc, h_acc_tc, accArgVals, h_acc_denote, hrtyenc, htA, h_ok, htc =>
    exact fvarHead_sound (Δ := Δ) (LExpr.AppSpine.fvar f τ_f acc' rty' hmem hcol hb)
      htA opInterp fvarVal bvarVal h_acc_tc htc ufInterp smtEnv accArgVals h_acc_denote
      h_ok hfvar hfenv
      (haccbase := haccbase) (haccenc := haccenc) (hrtybase := hb) (hrtyenc := hrtyenc)
  | _, _, _, .op o oty acc' rty' hopc hcol,
      haccbase, haccenc, h_acc_tc, accArgVals, h_acc_denote, hrtyenc, htA, h_ok, htc =>
    -- Predefined-op head: delegate to the standalone `.op`-core soundness lemma.
    have hrtybase := AppSpine_base (@LExpr.AppSpine.op Γ.Φ Γ.Ψ Δ o oty acc' rty' hopc hcol)
    exact predefinedOp_sound hopc hcol htA opInterp hop fvarVal bvarVal h_acc_tc htc
      ufInterp smtEnv accArgVals h_ok h_acc_denote
      (haccbase := haccbase) (haccenc := haccenc) (hrtybase := hrtybase) (hrtyenc := hrtyenc)
  | _, _, _, .fnOp o oty acc' rty' hmem hnpre hcol hb,
      haccbase, haccenc, h_acc_tc, accArgVals, h_acc_denote, hrtyenc, htA, h_ok, htc =>
    -- User-fn head: delegates to `userFnOp_sound`.
    have hmem_name : o.name ∈ Γ.Ψ.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hmem
    exact userFnOp_sound hmem hcol htA opInterp fvarVal bvarVal h_acc_tc htc ufInterp smtEnv
      accArgVals h_acc_denote (hfnwf o.name hmem_name) (by rw [hdtfree]; rfl)
      h_ok hfn hopenv
      (haccbase := haccbase) (haccenc := haccenc) (hrtybase := hb) (hrtyenc := hrtyenc)
  termination_by structural hspine
end


/-! ## Statement B — whole-query denotational soundness (`UnsatWithNegObl ⟹ CoreCtx.Valid`)
Because `CoreCtx.WF` is prefix-threaded, each `fnDef`/`varDef` body is typed at its emission
prefix; the per-IF consistency bridges run `translate_sound` at that prefix, restricting the full
`mkUFInterp` correspondences via `FVarEnvCorresponds.mono_sub` / `FnEnvCorresponds.mono_sub`.
-/

/-- The source-context bundle the Tier-A/denotation lemmas take (`Ψ` first, then `Φ`). -/
def toSimpTyCtx (cctx : CoreCtx) : SimpTyCtx := ⟨cctx.toΨ, cctx.toΦ⟩

/-! ## The HList↔BVarVal bridge machinery. The binder-type correspondence is threaded as its two
constituent parts: the source-side base-ness fact `∀ t ∈ Δ, MonoTyIsBase t` and the
correspondence equation `Δ.map (tyToTermType uAT) = bvs.map (·.ty)`.
-/

/-- `BVarCtxCorresponds` yields the two constituent parts of the binder-type encoding: the
    source-side base-ness fact and the correspondence equation. -/
theorem BVarCtxCorresponds.baseAndEnc {uAT : Bool} {Δ : BVarCtx} {bvs : TermVarCtx}
    (h : BVarCtxCorresponds uAT Δ bvs) :
    (∀ t ∈ Δ, LExpr.MonoTyIsBase t) ∧ Δ.map (tyToTermType uAT) = bvs.map (·.ty) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi, hie⟩ := List.getElem_of_mem ht
    have := (h.ty_eq i (hi)).1
    rw [hie] at this; exact this
  · apply List.ext_getElem
    · simp only [List.length_map]; exact h.len_eq
    · intro i hi1 hi2
      have hiΔ : i < Δ.length := by simpa using hi1
      have := (h.ty_eq i hiΔ).2
      simp only [List.getElem_map]
      exact this

/-- Build a `Lambda.BVarVal` over `Δ` from an HList of SMT values over `bvs`, using the binder
    correspondence's per-index base encoding. -/
noncomputable def hlToBVarVal {uAT : Bool} :
    (Δ : List LMonoTy) → (bvs : TermVarCtx) →
    ((∀ t ∈ Δ, LExpr.MonoTyIsBase t) ∧ Δ.map (tyToTermType uAT) = bvs.map (·.ty)) →
    HList (TermType.denoteTyped σ SmtArrayTheory) (bvs.map (·.ty)) →
    Lambda.BVarVal simpTcInterp simpTyVarVal Δ
  | [], [], _, _ => .nil
  | [], b :: bs, henc, _ => absurd henc.2 (by simp)
  | a :: as, [], henc, _ => absurd henc.2 (by simp)
  | a :: as, b :: bs, henc, .cons x xs =>
    have hh : LExpr.MonoTyIsBase a ∧ tyToTermType uAT a = b.ty :=
      ⟨henc.1 a (by simp), by
        have he := henc.2; simp only [List.map_cons, List.cons.injEq] at he; exact he.1⟩
    have htail : (∀ t ∈ as, LExpr.MonoTyIsBase t) ∧ as.map (tyToTermType uAT) = bs.map (·.ty) :=
      ⟨fun t ht => henc.1 t (by simp [ht]), by
        have he := henc.2; simp only [List.map_cons, List.cons.injEq] at he; exact he.2⟩
    .cons (cast (tyDenote_eq_smtTyDenote (σ := σ) hh).symm x)
          (hlToBVarVal as bs htail xs)

/-- **The `applyBVarVal ↔ UF.applyDenoteTyped'` bridge**, threading the binder-type base-ness fact
    and correspondence equation (plus the return-type base-ness fact and its equation) separately. -/
theorem applyBVarVal_eq_applyDenoteTyped' {uAT : Bool} :
    (Δ : List LMonoTy) → (bvs : TermVarCtx) → {rty : LMonoTy} → {smtRty : TermType} →
    (henc : (∀ t ∈ Δ, LExpr.MonoTyIsBase t) ∧ Δ.map (tyToTermType uAT) = bvs.map (·.ty)) →
    (hrty : LExpr.MonoTyIsBase rty ∧ tyToTermType uAT rty = smtRty) →
    (hd : Lambda.TyDenote simpTcInterp simpTyVarVal (List.foldr LMonoTy.arrow rty Δ)) →
    (hl : HList (TermType.denoteTyped σ SmtArrayTheory) (bvs.map (·.ty))) →
    UF.applyDenoteTyped' σ SmtArrayTheory (bvs.map (·.ty)) smtRty
        (cast (tyDenote_arrow_eq_UFDenote' henc hrty) hd) hl
      = cast (tyDenote_eq_smtTyDenote (σ := σ) hrty)
          (applyBVarVal Δ rty hd (hlToBVarVal (σ := σ) Δ bvs henc hl))
  | [], [], rty, smtRty, henc, hrty, hd, .nil => by
    simp only [hlToBVarVal, applyBVarVal, List.map_nil, UF.applyDenoteTyped']
    rfl
  | [], b :: bs, _, _, henc, _, _, _ => absurd henc.2 (by simp)
  | a :: as, [], _, _, henc, _, _, _ => absurd henc.2 (by simp)
  | a :: as, v :: rest, rty, smtRty, henc, hrty, hd, .cons x xs => by
    have hah : LExpr.MonoTyIsBase a ∧ tyToTermType uAT a = v.ty :=
      ⟨henc.1 a (by simp), by
        have he := henc.2; simp only [List.map_cons, List.cons.injEq] at he; exact he.1⟩
    have hrest : (∀ t ∈ as, LExpr.MonoTyIsBase t) ∧ as.map (tyToTermType uAT) = rest.map (·.ty) :=
      ⟨fun t ht => henc.1 t (by simp [ht]), by
        have he := henc.2; simp only [List.map_cons, List.cons.injEq] at he; exact he.2⟩
    let AC : Lambda.TyDenote simpTcInterp simpTyVarVal a = TermType.denoteTyped σ SmtArrayTheory v.ty :=
      tyDenote_eq_smtTyDenote (σ := σ) hah
    have hcaa := cast_arrow_app AC (tyDenote_arrow_eq_UFDenote' hrest hrty)
          (tyDenote_arrow_eq_UFDenote' henc hrty) hd (cast AC.symm x)
    rw [cast_cast, cast_eq] at hcaa
    have hhead : (cast (tyDenote_arrow_eq_UFDenote' henc hrty) hd) x
        = cast (tyDenote_arrow_eq_UFDenote' hrest hrty) (hd (cast AC.symm x)) := hcaa
    show UF.applyDenoteTyped' σ SmtArrayTheory (rest.map (·.ty)) smtRty
          ((cast (tyDenote_arrow_eq_UFDenote' henc hrty) hd) x) xs
        = cast (tyDenote_eq_smtTyDenote (σ := σ) hrty)
            (applyBVarVal as rty (hd (cast AC.symm x)) (hlToBVarVal (σ := σ) as rest hrest xs))
    rw [hhead]
    rw [applyBVarVal_eq_applyDenoteTyped' as rest hrest hrty (hd (cast AC.symm x)) xs]

/-- The environment bridge: `hlToBVarVal` and `hlToEnv` from the same HList correspond under
    `BVarEnvCorresponds`. -/
theorem hlToBVarVal_hlToEnv_corresponds {uAT : Bool} [SortInterp.AllInhabited σ] :
    (Δ : List LMonoTy) → (bvs : TermVarCtx) →
    (hbwf : BVarCtxCorresponds uAT Δ bvs) →
    (henc : (∀ t ∈ Δ, LExpr.MonoTyIsBase t) ∧ Δ.map (tyToTermType uAT) = bvs.map (·.ty)) →
    (hl : HList (TermType.denoteTyped σ SmtArrayTheory) (bvs.map (·.ty))) →
    BVarEnvCorresponds hbwf (hlToBVarVal (σ := σ) Δ bvs henc hl) (hlToEnv (σ := σ) bvs hl)
  | [], [], hbwf, henc, _ => by
    intro i τ hbase hlook; exact absurd hlook (by simp)
  | [], b :: bs, _, henc, _ => absurd henc.2 (by simp)
  | a :: as, [], _, henc, _ => absurd henc.2 (by simp)
  | a :: as, v :: rest, hbwf, henc, .cons x xs => by
    have hah : LExpr.MonoTyIsBase a ∧ tyToTermType uAT a = v.ty :=
      ⟨henc.1 a (by simp), by
        have he := henc.2; simp only [List.map_cons, List.cons.injEq] at he; exact he.1⟩
    have hrest_enc : (∀ t ∈ as, LExpr.MonoTyIsBase t) ∧ as.map (tyToTermType uAT) = rest.map (·.ty) :=
      ⟨fun t ht => henc.1 t (by simp [ht]), by
        have he := henc.2; simp only [List.map_cons, List.cons.injEq] at he; exact he.2⟩
    have hbwf_tail : BVarCtxCorresponds uAT as rest := by
      refine ⟨?_, ?_, ?_⟩
      · have := hbwf.len_eq; simp only [List.length_cons] at this; omega
      · intro i hi
        have := hbwf.ty_eq (i+1) (by simp only [List.length_cons]; omega)
        simpa using this
      · have := hbwf.nodup; simp only [List.map_cons, List.nodup_cons] at this; exact this.2
    have ih := hlToBVarVal_hlToEnv_corresponds as rest hbwf_tail hrest_enc xs
    have hbv_eq : hlToBVarVal (σ := σ) (a :: as) (v :: rest) henc (.cons x xs)
        = .cons (cast (tyDenote_eq_smtTyDenote (σ := σ) hah).symm x)
                (hlToBVarVal (σ := σ) as rest hrest_enc xs) := by
      simp only [hlToBVarVal]
    have henv_eq : hlToEnv (σ := σ) (v :: rest) (.cons x xs)
        = fun w => if h : w = v then cast (by rw [h]) x else hlToEnv (σ := σ) rest xs w := by
      simp only [hlToEnv]
    rw [hbv_eq, henv_eq]
    refine BVarEnvCorresponds_cons ih hah
      (cast (tyDenote_eq_smtTyDenote (σ := σ) hah).symm x) ?_ ?_ hbwf
    · simp only [dif_pos]; rw [cast_cast, cast_eq]
    · intro w hwne; simp only [dif_neg hwne]

/-! ## `mkUFInterp` — the constructed UF interpretation (over `defaultσ`) -/

/-- Boolean base-type checker, matching `LExpr.MonoTyIsBase`. -/
def isBaseTyB : LMonoTy → Bool
  | .tcons "bool" [] => true
  | .tcons "int" [] => true
  | .tcons "string" [] => true
  | .bitvec _ => true
  | _ => false

theorem isBaseTyB_iff {τ : LMonoTy} : isBaseTyB τ = true ↔ LExpr.MonoTyIsBase τ := by
  constructor
  · intro h
    unfold isBaseTyB at h
    split at h <;>
      first
        | exact .bool
        | exact .int
        | exact .string
        | exact .bitvec
        | simp at h
  · intro h; cases h <;> rfl

theorem isBaseTyB_all_iff {tys : List LMonoTy} :
    tys.all isBaseTyB = true ↔ ∀ t ∈ tys, LExpr.MonoTyIsBase t := by
  rw [List.all_eq_true]
  constructor
  · intro h t ht; exact isBaseTyB_iff.mp (h t ht)
  · intro h t ht; exact isBaseTyB_iff.mpr (h t ht)

/-- A default UF denotation. -/
noncomputable def UFDenote'.default : (args : List TermType) → (out : TermType) → UF.denoteTyped' defaultσ SmtArrayTheory args out
  | [], out => (TermType.denoteTyped.instInhabited (σ := defaultσ) (𝒜 := SmtArrayTheory) out).default
  | _ :: rest, out => fun _ => UFDenote'.default rest out

/-- The type-equality cast carrying an fvar/op value of arrow type `τ` to `uf`'s UF denotation. -/
theorem uf_cast_eq (uAT : Bool) {τ : LMonoTy} {uf : UF}
    (hargsBase : ∀ t ∈ (collectArrowTy τ).1, LExpr.MonoTyIsBase t)
    (hargs : (collectArrowTy τ).1.map (tyToTermType uAT) = uf.args)
    (houtBase : LExpr.MonoTyIsBase (collectArrowTy τ).2)
    (hout : tyToTermType uAT (collectArrowTy τ).2 = uf.out) :
    Lambda.TyDenote simpTcInterp simpTyVarVal τ = UF.denoteTyped defaultσ SmtArrayTheory uf := by
  have h1 : τ = List.foldr LMonoTy.arrow (collectArrowTy τ).2 (collectArrowTy τ).1 := by
    have hf := collectArrowTy_foldr τ
    obtain ⟨argTys, rty, hcol⟩ : ∃ a r, collectArrowTy τ = (a, r) := ⟨_, _, rfl⟩
    rw [hcol] at hf ⊢; exact hf
  rw [h1]
  have := tyDenote_arrow_eq_UFDenote' (σ := defaultσ) (uAT := uAT)
    (⟨hargsBase, hargs⟩ : (∀ t ∈ (collectArrowTy τ).1, LExpr.MonoTyIsBase t) ∧ (collectArrowTy τ).1.map (tyToTermType uAT) = uf.args)
    (⟨houtBase, hout⟩ : LExpr.MonoTyIsBase (collectArrowTy τ).2 ∧ tyToTermType uAT (collectArrowTy τ).2 = uf.out)
  simpa only [UF.denoteTyped] using this

/-- The decidable predicate "source entry `x` RESOLVES to UF signature `uf`". -/
def resolvesTo (uAT : Bool) (ufs : UFCtx) (uf : UF) (x : String × LMonoTy) : Bool :=
  decide (lookupUF ufs x.1 = some uf)
    && ((collectArrowTy x.2).1.map (tyToTermType uAT) == uf.args)
    && (tyToTermType uAT (collectArrowTy x.2).2 == uf.out)
    && (collectArrowTy x.2).1.all isBaseTyB
    && isBaseTyB (collectArrowTy x.2).2

theorem resolvesTo_iff {uAT : Bool} {ufs : UFCtx} {uf : UF} {x : String × LMonoTy} :
    resolvesTo uAT ufs uf x = true ↔
      lookupUF ufs x.1 = some uf ∧
      (collectArrowTy x.2).1.map (tyToTermType uAT) = uf.args ∧
      tyToTermType uAT (collectArrowTy x.2).2 = uf.out ∧
      (∀ t ∈ (collectArrowTy x.2).1, LExpr.MonoTyIsBase t) ∧
      LExpr.MonoTyIsBase (collectArrowTy x.2).2 := by
  simp only [resolvesTo, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, isBaseTyB_all_iff,
    isBaseTyB_iff]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- **Construct `ufInterp`.** Dispatch by `List.find?` on the resolution predicate. -/
noncomputable def mkUFInterp (uAT : Bool)
    (Φ : FVarCtx) (Ψ : FnCtx) (ufs : UFCtx)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : UFInterp defaultσ SmtArrayTheory :=
  fun uf =>
    match hΦ : Φ.find? (resolvesTo uAT ufs uf) with
    | some x =>
        have hx := resolvesTo_iff.mp (List.find?_some hΦ)
        cast (uf_cast_eq uAT hx.2.2.2.1 hx.2.1 hx.2.2.2.2 hx.2.2.1) (fvarVal ⟨x.1, ()⟩ (x.2.substTyVars simpTyVarVal))
    | none =>
        match hΨ : Ψ.find? (resolvesTo uAT ufs uf) with
        | some x =>
            have hx := resolvesTo_iff.mp (List.find?_some hΨ)
            cast (uf_cast_eq uAT hx.2.2.2.1 hx.2.1 hx.2.2.2.2 hx.2.2.1) (opInterp x.1 (x.2.substTyVars simpTyVarVal))
        | none => UFDenote'.default uf.args uf.out

private theorem entry_unique {Γ : List (String × LMonoTy)} (hnd : (Γ.map Prod.fst).Nodup)
    {a b : String × LMonoTy} (ha : a ∈ Γ) (hb : b ∈ Γ) (hkey : a.1 = b.1) : a = b := by
  induction Γ with
  | nil => simp at ha
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (hkey ▸ List.mem_map_of_mem (f := Prod.fst) hb) hnd.1
    · exact absurd (hkey.symm ▸ List.mem_map_of_mem (f := Prod.fst) ha) hnd.1
    · exact ih hnd.2 ha hb

private theorem find?_isSome_of_mem {α} {l : List α} {p : α → Bool} {a : α}
    (ha : a ∈ l) (hpa : p a = true) : (l.find? p).isSome := by
  rcases h : l.find? p with _ | b
  · exact absurd hpa (by have := List.find?_eq_none.mp h a ha; simp [this])
  · rfl

/-- The resolution facts backing a correspondence: the collected arrow types encode `uf`. -/
private theorem resolves_of_bridge (uAT : Bool) {ufs : UFCtx} {name : String} {τ : LMonoTy} {uf : UF}
    (hlk : lookupUF ufs name = some uf)
    (hargs : (∀ t ∈ (collectArrowTy τ).1, LExpr.MonoTyIsBase t) ∧ (collectArrowTy τ).1.map (tyToTermType uAT) = uf.args)
    (hout : LExpr.MonoTyIsBase (collectArrowTy τ).2 ∧ tyToTermType uAT (collectArrowTy τ).2 = uf.out) :
    resolvesTo uAT ufs uf (name, τ) = true := by
  rw [resolvesTo_iff]
  exact ⟨hlk, hargs.2, hout.2, hargs.1, hout.1⟩

theorem mkUFInterp_fvar_eq (uAT : Bool)
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (hnd : (Φ.map Prod.fst).Nodup)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {name : String} {τ : LMonoTy} {uf : UF} (hmem : (name, τ) ∈ Φ)
    (hlk : lookupUF ufs name = some uf)
    (hargs : (∀ t ∈ (collectArrowTy τ).1, LExpr.MonoTyIsBase t) ∧ (collectArrowTy τ).1.map (tyToTermType uAT) = uf.args)
    (hout : LExpr.MonoTyIsBase (collectArrowTy τ).2 ∧ tyToTermType uAT (collectArrowTy τ).2 = uf.out)
    (hcast : Lambda.TyDenote simpTcInterp simpTyVarVal τ = UF.denoteTyped defaultσ SmtArrayTheory uf) :
    mkUFInterp uAT Φ Ψ ufs opInterp fvarVal uf
      = cast hcast (fvarVal ⟨name, ()⟩ (τ.substTyVars simpTyVarVal)) := by
  have hres : resolvesTo uAT ufs uf (name, τ) = true := resolves_of_bridge uAT hlk hargs hout
  have hsome := find?_isSome_of_mem hmem hres
  unfold mkUFInterp
  split
  · rename_i x' hx'
    have hxres := resolvesTo_iff.mp (List.find?_some hx')
    have hxname : x'.1 = name := by
      have h1 := lookupUF_id hxres.1; have h2 := lookupUF_id hlk; rw [h1] at h2; exact h2
    have hxeq : x' = (name, τ) := entry_unique hnd (List.mem_of_find?_eq_some hx') hmem hxname
    subst hxeq; rfl
  · rename_i hnone; rw [hnone] at hsome; simp at hsome

theorem mkUFInterp_fvarCorresponds (uAT : Bool)
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (huwf : FNameCtxCorresponds uAT Φ ufs)
    (hnd : (Φ.map Prod.fst).Nodup)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) :
    FVarEnvCorresponds (σ := defaultσ) huwf fvarVal (mkUFInterp uAT Φ Ψ ufs opInterp fvarVal) := by
  intro name τ hmem
  have hlk : lookupUF ufs name = some ((lookupUF ufs name).get (huwf.fvar_resolves name τ hmem)) :=
    (Option.some_get _).symm
  exact (mkUFInterp_fvar_eq uAT hnd opInterp fvarVal hmem hlk
    (huwf.args_eq name τ _ hmem hlk) (huwf.out_eq name τ _ hmem hlk) _).symm

theorem mkUFInterp_fn_eq (uAT : Bool)
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (hndΨ : (Ψ.map Prod.fst).Nodup)
    (hdisj : ∀ x ∈ Φ, x.1 ∉ Ψ.map Prod.fst)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {name : String} {τ : LMonoTy} {uf : UF} (hmem : (name, τ) ∈ Ψ)
    (hlk : lookupUF ufs name = some uf)
    (hargs : (∀ t ∈ (collectArrowTy τ).1, LExpr.MonoTyIsBase t) ∧ (collectArrowTy τ).1.map (tyToTermType uAT) = uf.args)
    (hout : LExpr.MonoTyIsBase (collectArrowTy τ).2 ∧ tyToTermType uAT (collectArrowTy τ).2 = uf.out)
    (hcast : Lambda.TyDenote simpTcInterp simpTyVarVal τ = UF.denoteTyped defaultσ SmtArrayTheory uf) :
    mkUFInterp uAT Φ Ψ ufs opInterp fvarVal uf
      = cast hcast (opInterp name (τ.substTyVars simpTyVarVal)) := by
  have hΦnone : Φ.find? (resolvesTo uAT ufs uf) = none := by
    rw [List.find?_eq_none]
    intro x hxΦ hxres
    have hxname : x.1 = name := by
      have h1 := lookupUF_id (resolvesTo_iff.mp hxres).1
      have h2 := lookupUF_id hlk; rw [h1] at h2; exact h2
    exact hdisj x hxΦ (hxname ▸ List.mem_map_of_mem (f := Prod.fst) hmem)
  have hres : resolvesTo uAT ufs uf (name, τ) = true := resolves_of_bridge uAT hlk hargs hout
  have hsome := find?_isSome_of_mem hmem hres
  unfold mkUFInterp
  split
  · rename_i x' hx'; rw [hΦnone] at hx'; simp at hx'
  · split
    · rename_i x' hx'
      have hxres := resolvesTo_iff.mp (List.find?_some hx')
      have hxname : x'.1 = name := by
        have h1 := lookupUF_id hxres.1; have h2 := lookupUF_id hlk; rw [h1] at h2; exact h2
      have hxeq : x' = (name, τ) := entry_unique hndΨ (List.mem_of_find?_eq_some hx') hmem hxname
      subst hxeq; rfl
    · rename_i hnone; rw [hnone] at hsome; simp at hsome

theorem mkUFInterp_fnCorresponds (uAT : Bool)
    {Φ : FVarCtx} {Ψ : FnCtx} {ufs : UFCtx} (hψwf : FNameCtxCorresponds uAT Ψ ufs)
    (hndΨ : (Ψ.map Prod.fst).Nodup) (hdisj : ∀ x ∈ Φ, x.1 ∉ Ψ.map Prod.fst)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) :
    FnEnvCorresponds (σ := defaultσ) hψwf opInterp (mkUFInterp uAT Φ Ψ ufs opInterp fvarVal) := by
  intro name τ hmem
  have hlk : lookupUF ufs name = some ((lookupUF ufs name).get (hψwf.fvar_resolves name τ hmem)) :=
    (Option.some_get _).symm
  exact (mkUFInterp_fn_eq uAT hndΨ hdisj opInterp fvarVal hmem hlk
    (hψwf.args_eq name τ _ hmem hlk) (hψwf.out_eq name τ _ hmem hlk) _).symm

/-! ## Env-correspondence monotonicity (restrict to a sub-context) + nil -/

theorem FVarEnvCorresponds.mono_sub {uAT : Bool} {Φ Φ' : FVarCtx} {ufs : UFCtx}
    {hwf : FNameCtxCorresponds uAT Φ' ufs} (hsub : Φ ⊆ Φ')
    {fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp} {ufInterp : UFInterp σ SmtArrayTheory}
    (henv : FVarEnvCorresponds hwf fvarVal ufInterp) :
    FVarEnvCorresponds (hwf.mono_sub hsub) fvarVal ufInterp := by
  intro name τ hmem
  exact henv name τ (hsub hmem)

theorem FnEnvCorresponds.mono_sub {uAT : Bool} {Ψ Ψ' : FnCtx} {ufs : UFCtx}
    {hwf : FNameCtxCorresponds uAT Ψ' ufs} (hsub : Ψ ⊆ Ψ')
    {opInterp : Lambda.OpInterp simpTcInterp} {ufInterp : UFInterp σ SmtArrayTheory}
    (henv : FnEnvCorresponds hwf opInterp ufInterp) :
    FnEnvCorresponds (hwf.mono_sub hsub) opInterp ufInterp := by
  intro name τ hmem
  exact henv name τ (hsub hmem)

theorem FVarEnvCorresponds_nil {uAT : Bool} {ufs : UFCtx}
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) (ufInterp : UFInterp σ SmtArrayTheory) :
    FVarEnvCorresponds (σ := σ) (FNameCtxCorresponds_nil (uAT := uAT) (ufs := ufs)) fvarVal ufInterp := by
  intro name τ hmem; simp at hmem

/-! ## HList / distinct transfer helpers -/

/-- Source-side satisfaction of a distinctness group (pairwise-distinct member denotations). -/
noncomputable def DistinctSat (Φ Ψ : FNameCtx)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (es : List Expression.Expr) (τ : LMonoTy)
    (hall : ∀ e ∈ es, LExpr.HasSimpType Φ Ψ [] e τ) : Prop :=
  (es.attach.map (fun x => simpDenote opInterp fvarVal .nil x.1 τ
    (HasSimpType_implies_HasTypeA (hall x.1 x.2)))).Pairwise (· ≠ ·)

/-- `collectArrowTy` inverts `foldr arrow` at a base return type. -/
theorem collectArrowTy_foldr_base {argTys : List LMonoTy} {rty : LMonoTy}
    (hret : LExpr.MonoTyIsBase rty) :
    collectArrowTy (List.foldr LMonoTy.arrow rty argTys) = (argTys, rty) := by
  induction argTys with
  | nil => cases hret <;> rfl
  | cons a as ih =>
    rw [List.foldr_cons]
    rw [show collectArrowTy (LMonoTy.arrow a (List.foldr LMonoTy.arrow rty as))
          = (a :: (collectArrowTy (List.foldr LMonoTy.arrow rty as)).1,
             (collectArrowTy (List.foldr LMonoTy.arrow rty as)).2) from rfl, ih]

/-! ## `translateQuery` structural inversions for the define-fun preamble + goal -/

theorem fnDefsFold_mem {uAT : Bool} {tenv : TranslateEnv}
    {fds : List FnDef} {ifs : List IF}
    (h : fds.mapM (fun d => do
        let bodyTm ← translate uAT tenv (fnDefSmtParams uAT d) d.body
        .ok ({ id := d.name, args := fnDefSmtParams uAT d, out := tyToTermType uAT d.retTy, body := bodyTm } : IF)) = .ok ifs) :
    ∀ f ∈ ifs, ∃ d ∈ fds, ∃ bodyTm,
      translate uAT tenv (fnDefSmtParams uAT d) d.body = .ok bodyTm ∧
      f = ⟨d.name, fnDefSmtParams uAT d, tyToTermType uAT d.retTy, bodyTm⟩ := by
  intro f hf
  obtain ⟨d, hd, hstep⟩ := mapM_mem fds _ h f hf
  obtain ⟨bodyTm, hbody, hstep⟩ := bind_ok_inv hstep
  refine ⟨d, hd, bodyTm, hbody, ?_⟩
  simp only [Except.ok.injEq] at hstep; exact hstep.symm

theorem varDefsFold_mem {uAT : Bool} {tenv : TranslateEnv}
    {vds : List VarDef} {ifs : List IF}
    (h : vds.mapM (fun v => do
        let bodyTm ← translate uAT tenv [] v.body
        .ok ({ id := v.name, args := [], out := tyToTermType uAT v.ty, body := bodyTm } : IF)) = .ok ifs) :
    ∀ f ∈ ifs, ∃ v ∈ vds, ∃ bodyTm,
      translate uAT tenv [] v.body = .ok bodyTm ∧
      f = ⟨v.name, [], tyToTermType uAT v.ty, bodyTm⟩ := by
  intro f hf
  obtain ⟨v, hv, hstep⟩ := mapM_mem vds _ h f hf
  obtain ⟨bodyTm, hbody, hstep⟩ := bind_ok_inv hstep
  refine ⟨v, hv, bodyTm, hbody, ?_⟩
  simp only [Except.ok.injEq] at hstep; exact hstep.symm

theorem translateQuery_defs_mem {uAT : Bool}
    {cctx : CoreCtx} {goal : Expression.Expr} {q : SMTQuery}
    (henc : translateQuery uAT cctx goal = .ok q) :
    ∀ f ∈ q.fs,
      (∃ d ∈ cctx.fnDefs, ∃ bodyTm,
        translate uAT cctx.toTranslateEnv (fnDefSmtParams uAT d) d.body = .ok bodyTm ∧
        f = ⟨d.name, fnDefSmtParams uAT d, tyToTermType uAT d.retTy, bodyTm⟩) ∨
      (∃ v ∈ cctx.varDefs, ∃ bodyTm,
        translate uAT cctx.toTranslateEnv [] v.body = .ok bodyTm ∧
        f = ⟨v.name, [], tyToTermType uAT v.ty, bodyTm⟩) := by
  obtain ⟨_, _, hfnDefsMap, hvarDefsMap, _, _⟩ := translateQuery_inv henc
  intro f hf
  rw [SMTQuery.fs, List.mem_append] at hf
  rcases hf with hf | hf
  · exact Or.inl (fnDefsFold_mem hfnDefsMap f hf)
  · exact Or.inr (varDefsFold_mem hvarDefsMap f hf)

/-! ## Prefix-typing extractors from the order-threaded `CoreCtx.WF` inductives -/

/-- Each `fnDef`'s parameter names are `Nodup`. -/
theorem FnDefsWF.mem_paramsNodup {Ψ : FnCtx} {fds : List FnDef} (h : FnDefsWF Ψ fds) :
    ∀ d ∈ fds, (d.params.map Prod.fst).Nodup := by
  induction h with
  | nil => intro d hd; simp at hd
  | @cons Ψ d rest _ _ hpNodup _ _ ih =>
    intro d' hd'
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact hpNodup
    · exact ih d' hd'

/-- Each `fnDef` body is typed against its EMISSION PREFIX `Ψpre` (⊆ the full fold), with its params
    fresh for that prefix — exactly what `translate_sound` needs at `Γ := ⟨Ψpre, []⟩`. -/
theorem FnDefsWF.mem_typing {Ψbase : FnCtx} {fds : List FnDef} (h : FnDefsWF Ψbase fds) :
    ∀ d ∈ fds, ∃ Ψpre : FnCtx,
      Ψpre ⊆ Ψbase ++ fds.map (fun d => (d.name, LMonoTy.mkArrow' d.retTy d.argTys)) ∧
      LExpr.HasSimpType [] Ψpre d.argTys d.body d.retTy ∧
      (∀ p ∈ d.params, p.1 ∉ Ψpre.map Prod.fst) := by
  induction h with
  | nil => intro d hd; simp at hd
  | @cons Ψ d rest hhead _ _ hpFresh htail ih =>
    intro d' hd'
    rcases List.mem_cons.mp hd' with rfl | hd'
    · refine ⟨Ψ, ?_, hhead, hpFresh⟩
      intro x hx; exact List.mem_append_left _ hx
    · obtain ⟨Ψpre, hsub, hty, hfr⟩ := ih d' hd'
      refine ⟨Ψpre, ?_, hty, hfr⟩
      intro x hx
      have h2 := hsub hx
      simpa only [List.map_cons, List.cons_append, List.append_assoc, List.singleton_append] using h2

/-- Each `varDef` body is typed against its emission prefix `Φpre` (⊆ the full fold) + the FULL
    function context `Ψ`. -/
theorem VarDefsWF.mem_typing {Ψ : FnCtx} {Φbase : FVarCtx} {vds : List VarDef}
    (h : VarDefsWF Ψ Φbase vds) :
    ∀ v ∈ vds, ∃ Φpre : FVarCtx,
      Φpre ⊆ Φbase ++ vds.map (fun v => (v.name, v.ty)) ∧
      LExpr.HasSimpType Φpre Ψ [] v.body v.ty := by
  induction h with
  | nil => intro v hv; simp at hv
  | @cons Φ v rest hhead htail ih =>
    intro v' hv'
    rcases List.mem_cons.mp hv' with rfl | hv'
    · refine ⟨Φ, ?_, hhead⟩
      intro x hx; exact List.mem_append_left _ hx
    · obtain ⟨Φpre, hsub, hty⟩ := ih v' hv'
      refine ⟨Φpre, ?_, hty⟩
      intro x hx
      have h2 := hsub hx
      simpa only [List.map_cons, List.cons_append, List.append_assoc, List.singleton_append] using h2

/-! ## Obligation-denotation transfer (closed bool source, via `translate_sound`) — full context -/

theorem mkModel_denote_obligation_refactor {uAT : Bool} {cctx : CoreCtx} {ufs : UFCtx}
    (hfvar : FNameCtxCorresponds uAT cctx.toΦ ufs) (hfn : FNameCtxCorresponds uAT cctx.toΨ ufs)
    (huf : UFCtxWF ufs) (hfnwf : FnNamesNotPredefined cctx.toΨ uAT)
    (hdtfree : cctx.toTranslateEnv.datatypeFuns = ∅)
    (hndΦ : (cctx.toΦ.map Prod.fst).Nodup) (hndΨ : (cctx.toΨ.map Prod.fst).Nodup)
    (hdisj : ∀ x ∈ cctx.toΦ, x.1 ∉ cctx.toΨ.map Prod.fst)
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {e : Expression.Expr} (he : LExpr.HasSimpType cctx.toΦ cctx.toΨ [] e (.tcons "bool" []))
    {tm : Term} (htc : Term.typeCheck ⟨[], ufs, []⟩ tm = .ok .bool)
    (h_ok : translate uAT cctx.toTranslateEnv [] e = .ok tm) :
    (Term.denoteTyped (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal) mkVarEnv divByZero modByZero tm .bool htc : Bool)
      = (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
          (HasSimpType_implies_HasTypeA he) : Bool) := by
  have hfenv := mkUFInterp_fvarCorresponds uAT (Ψ := cctx.toΨ) hfvar hndΦ opInterp fvarVal
  have hopenv := mkUFInterp_fnCorresponds uAT (Φ := cctx.toΦ) hfn hndΨ hdisj opInterp fvarVal
  have hbenv : BVarEnvCorresponds (σ := defaultσ) (uAT := uAT) bwf_nil (bvarVal := .nil) mkVarEnv := by
    intro i τ _ hlook; simp at hlook
  have hbool : LExpr.MonoTyIsBase (.tcons "bool" []) ∧ tyToTermType uAT (.tcons "bool" []) = .bool := ⟨.bool, by simp only [tyToTermType]⟩
  have hsound := translate_sound (Γ := toSimpTyCtx cctx) (tenv := cctx.toTranslateEnv)
    (useArrayTheory := uAT) (σ := defaultσ)
    he (HasSimpType_implies_HasTypeA he) opInterp fvarVal .nil
    htc huf (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal) mkVarEnv
    h_ok hbool.2 hfvar hfn bwf_nil
    (fun nm h => coreCtx_names_used h) havoid_nil
    hfenv hopenv hbenv hop hfnwf hdtfree
  simpa using hsound.symm

theorem mkModel_translate_distinct {uAT : Bool} {cctx : CoreCtx} {ufs : UFCtx}
    (hfvar : FNameCtxCorresponds uAT cctx.toΦ ufs) (hfn : FNameCtxCorresponds uAT cctx.toΨ ufs)
    (huf : UFCtxWF ufs) (hfnwf : FnNamesNotPredefined cctx.toΨ uAT)
    (hdtfree : cctx.toTranslateEnv.datatypeFuns = ∅)
    (hndΦ : (cctx.toΦ.map Prod.fst).Nodup) (hndΨ : (cctx.toΨ.map Prod.fst).Nodup)
    (hdisj : ∀ x ∈ cctx.toΦ, x.1 ∉ cctx.toΨ.map Prod.fst)
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    {es : List Expression.Expr} {τ : LMonoTy} (hbase : LExpr.MonoTyIsBase τ)
    (hall : ∀ e ∈ es, LExpr.HasSimpType cctx.toΦ cctx.toΨ [] e τ)
    (hsat : DistinctSat cctx.toΦ cctx.toΨ opInterp fvarVal es τ hall)
    {ts : List Term}
    (htc : Term.typeCheck ⟨[], ufs, []⟩ (.app (.core .distinct) ts .bool) = .ok .bool)
    (h_ok : translateList uAT cctx.toTranslateEnv es = .ok ts) :
    (Term.denoteTyped (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal)
      mkVarEnv divByZero modByZero (.app (.core .distinct) ts .bool) .bool htc : Bool) = true := by
  have hτ : LExpr.MonoTyIsBase τ ∧ tyToTermType uAT τ = tyToTermType uAT τ := ⟨hbase, rfl⟩
  have htlen : ts.length = es.length := translateList_len h_ok
  have hfenv := mkUFInterp_fvarCorresponds uAT (Ψ := cctx.toΨ) hfvar hndΦ opInterp fvarVal
  have hopenv := mkUFInterp_fnCorresponds uAT (Φ := cctx.toΦ) hfn hndΨ hdisj opInterp fvarVal
  have hbenv : BVarEnvCorresponds (σ := defaultσ) (uAT := uAT) bwf_nil (bvarVal := .nil) mkVarEnv := by
    intro i τ' _ hlook; simp at hlook
  have hused : ∀ nm ∈ ((toSimpTyCtx cctx).Φ ++ (toSimpTyCtx cctx).Ψ).map Prod.fst,
      (staticUsedNames cctx.toTranslateEnv).contains nm := fun nm h => coreCtx_names_used h
  have htci : ∀ i (hit : i < ts.length), Term.typeCheck ⟨[], ufs, []⟩ ts[i] = .ok (tyToTermType uAT τ) := by
    intro i hit
    have hie : i < es.length := htlen ▸ hit
    have hi_ok := translateList_getElem es ts h_ok i hie hit
    have := translate_typeChecks (Γ := toSimpTyCtx cctx) (tenv := cctx.toTranslateEnv)
      (useArrayTheory := uAT)
      (hall _ (es.get_mem ⟨i, hie⟩)) huf
      (by simpa using hi_ok) rfl hfvar hfn bwf_nil hused havoid_nil hfnwf hdtfree
    simpa using this
  have hsound : ∀ i (hit : i < ts.length) (hie : i < es.length),
      Term.denoteTyped (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal)
        mkVarEnv divByZero modByZero ts[i] (tyToTermType uAT τ) (htci i hit)
      = cast (tyDenote_eq_smtTyDenote (σ := defaultσ) hτ)
          (simpDenote opInterp fvarVal .nil (es.get ⟨i, hie⟩) τ
            (HasSimpType_implies_HasTypeA (hall _ (es.get_mem ⟨i, hie⟩)))) := by
    intro i hit hie
    have hi_ok := translateList_getElem es ts h_ok i hie hit
    have hs := translate_sound (Γ := toSimpTyCtx cctx) (tenv := cctx.toTranslateEnv)
      (useArrayTheory := uAT) (σ := defaultσ)
      (hall _ (es.get_mem ⟨i, hie⟩)) (HasSimpType_implies_HasTypeA (hall _ (es.get_mem ⟨i, hie⟩)))
      opInterp fvarVal .nil
      (htci i hit) huf (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal) mkVarEnv
      (by simpa using hi_ok) rfl hfvar hfn bwf_nil hused havoid_nil hfenv hopenv hbenv hop hfnwf hdtfree
    simpa using hs.symm
  obtain ⟨t1, t2, restts, htseq⟩ : ∃ a b r, ts = a :: b :: r := by
    match ts, htc with
    | [], htc => simp [Term.typeCheck] at htc
    | [_], htc => simp [Term.typeCheck] at htc
    | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩
  subst htseq
  unfold Term.denoteTyped
  rcases htdi : Term.typeCheck_distinct_inv htc with ⟨ty, ht1, hargs, heq⟩
  dsimp only
  rw [cast_eq]
  have htyeq : ty = tyToTermType uAT τ := by
    have h0 := htci 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [ht1] at h0; exact Except.ok.inj h0
  subst htyeq
  simp only [decide_eq_true_iff]
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [hlist_len] at hi hj
  have hfullargs : Term.typeCheckArgs ⟨[], ufs, []⟩ (t1::t2::restts)
      (List.replicate (t1::t2::restts).length (tyToTermType uAT τ)) = true := by
    show Term.typeCheckArgs ⟨[], ufs, []⟩ (t1::t2::restts) ((tyToTermType uAT τ) :: List.replicate (t2::restts).length (tyToTermType uAT τ)) = true
    simp only [Term.typeCheckArgs, ht1, hargs, BEq.beq, decide_eq_true_eq, Bool.and_true]
  rw [hlist_getElem (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal) mkVarEnv (tyToTermType uAT τ) (t1::t2::restts) hfullargs
        i hi (htci i hi),
      hlist_getElem (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal) mkVarEnv (tyToTermType uAT τ) (t1::t2::restts) hfullargs
        j hj (htci j hj)]
  rw [hsound i hi (htlen ▸ hi), hsound j hj (htlen ▸ hj)]
  have hpw := hsat
  rw [DistinctSat, List.pairwise_iff_getElem] at hpw
  have hij' := hpw i j
    (by simp only [List.length_map, List.length_attach]; exact htlen ▸ hi)
    (by simp only [List.length_map, List.length_attach]; exact htlen ▸ hj) hij
  simp only [List.getElem_map, List.getElem_attach] at hij'
  revert hij'
  generalize simpDenote opInterp fvarVal .nil (es.get ⟨i, htlen ▸ hi⟩) τ
      (HasSimpType_implies_HasTypeA (hall _ (es.get_mem ⟨i, htlen ▸ hi⟩))) = vi
  generalize simpDenote opInterp fvarVal .nil (es.get ⟨j, htlen ▸ hj⟩) τ
      (HasSimpType_implies_HasTypeA (hall _ (es.get_mem ⟨j, htlen ▸ hj⟩))) = vj
  intro hij' hcontra
  revert hcontra
  generalize tyDenote_eq_smtTyDenote (σ := defaultσ) hτ = C
  generalize TermType.denoteTyped defaultσ SmtArrayTheory (tyToTermType uAT τ) = B at C
  subst C
  simp only [cast_eq]
  exact hij'

/-! ## Per-IF preamble consistency bridges (op-side fnDef / fvar-side varDef), PREFIX-threaded -/

theorem UFConsistent_of_DefConsistent_op {uAT : Bool} {cctx : CoreCtx} {ufs : UFCtx}
    (d : FnDef)
    {Ψpre : FnCtx} (hsub : Ψpre ⊆ cctx.toΨ)
    (hbody : LExpr.HasSimpType [] Ψpre d.argTys d.body d.retTy)
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hndΨ : (cctx.toΨ.map Prod.fst).Nodup)
    (hdisj : ∀ x ∈ cctx.toΦ, x.1 ∉ cctx.toΨ.map Prod.fst)
    (hcons : ∀ (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal d.argTys),
      applyBVarVal d.argTys d.retTy
        (opInterp d.name ((List.foldr LMonoTy.arrow d.retTy d.argTys).substTyVars simpTyVarVal)) bvarVal
      = simpDenote opInterp fvarVal bvarVal d.body d.retTy (HasSimpType_implies_HasTypeA hbody))
    (hfn : FNameCtxCorresponds uAT cctx.toΨ ufs)
    (huf : UFCtxWF ufs) (hfnwf : FnNamesNotPredefined cctx.toΨ uAT)
    (hdtfree : cctx.toTranslateEnv.datatypeFuns = ∅)
    (hmem : (d.name, List.foldr LMonoTy.arrow d.retTy d.argTys) ∈ cctx.toΨ)
    {smtRet : TermType} {ifbody : Term} {params : List TermVar}
    (hbwf : BVarCtxCorresponds uAT d.argTys params)
    (hpFresh : ∀ v ∈ params, v.id ∉ (([] : FVarCtx) ++ Ψpre).map Prod.fst)
    (htc : Term.typeCheck ⟨[], ufs, params⟩ ifbody = .ok smtRet)
    (h_ok : translate uAT cctx.toTranslateEnv params d.body = .ok ifbody)
    (hrty : LExpr.MonoTyIsBase d.retTy ∧ tyToTermType uAT d.retTy = smtRet)
    (hretbase : LExpr.MonoTyIsBase d.retTy) :
    IF.UFConsistent ⟨d.name, params, smtRet, ifbody⟩ htc
      (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal) divByZero modByZero := by
  unfold IF.UFConsistent
  intro hl
  have henc : (∀ t ∈ d.argTys, LExpr.MonoTyIsBase t) ∧ d.argTys.map (tyToTermType uAT) = params.map (·.ty) := BVarCtxCorresponds.baseAndEnc hbwf
  have hopenv_full := mkUFInterp_fnCorresponds uAT (Φ := cctx.toΦ) hfn hndΨ hdisj opInterp fvarVal
  have hused : ∀ nm ∈ (([] : FVarCtx) ++ Ψpre).map Prod.fst,
      (staticUsedNames cctx.toTranslateEnv).contains nm := by
    intro nm hnm
    simp only [List.nil_append, List.mem_map] at hnm
    obtain ⟨p, hp_mem, hp⟩ := hnm
    apply coreCtx_names_used
    rw [List.map_append, List.mem_append]
    exact Or.inr (hp ▸ List.mem_map_of_mem (f := Prod.fst) (hsub hp_mem))
  have hfnwf_pre : FnNamesNotPredefined Ψpre uAT := by
    intro nm hnm
    simp only [List.mem_map] at hnm
    obtain ⟨p, hp_mem, hp⟩ := hnm
    exact hfnwf nm (hp ▸ List.mem_map_of_mem (f := Prod.fst) (hsub hp_mem))
  simp only [IF.toUF, UF.applyDenoteTyped]
  have hcol := collectArrowTy_foldr_base (argTys := d.argTys) hretbase
  have hlk : lookupUF ufs d.name = some ⟨d.name, params.map (·.ty), smtRet⟩ := by
    obtain ⟨uf, huf'⟩ := Option.isSome_iff_exists.mp (hfn.fvar_resolves d.name _ hmem)
    have hid := lookupUF_id huf'
    have hargs := hfn.args_eq d.name _ uf hmem huf'
    have hout := hfn.out_eq d.name _ uf hmem huf'
    rw [hcol] at hargs hout; simp only at hargs hout
    have hargs_eq : uf.args = params.map (·.ty) := hargs.2.symm.trans henc.2
    have hout_eq : uf.out = smtRet := hout.2.symm.trans hrty.2
    rw [huf']; cases uf; simp_all
  have hcorr := (mkUFInterp_fn_eq uAT (Φ := cctx.toΦ) hndΨ hdisj opInterp fvarVal hmem hlk
    (by rw [hcol]; exact henc) (by rw [hcol]; exact hrty)
    (tyDenote_arrow_eq_UFDenote' henc hrty)).symm
  rw [← hcorr]
  have hbenv : BVarEnvCorresponds hbwf (hlToBVarVal (σ := defaultσ) d.argTys params henc hl) (hlToEnv (σ := defaultσ) params hl) :=
    hlToBVarVal_hlToEnv_corresponds d.argTys params hbwf henc hl
  have h_sound := translate_sound (Γ := ⟨Ψpre, []⟩) (tenv := cctx.toTranslateEnv)
    (useArrayTheory := uAT) (σ := defaultσ)
    hbody (HasSimpType_implies_HasTypeA hbody) opInterp fvarVal
    (hlToBVarVal (σ := defaultσ) d.argTys params henc hl) htc huf
    (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal) (hlToEnv (σ := defaultσ) params hl)
    h_ok hrty.2 FNameCtxCorresponds_nil (hfn.mono_sub hsub) hbwf hused hpFresh
    (FVarEnvCorresponds_nil _ _) (hopenv_full.mono_sub hsub) hbenv hop hfnwf_pre hdtfree
  exact (applyBVarVal_eq_applyDenoteTyped' d.argTys params henc hrty
      (opInterp d.name ((List.foldr LMonoTy.arrow d.retTy d.argTys).substTyVars simpTyVarVal)) hl).trans
    ((congrArg (cast (tyDenote_eq_smtTyDenote (σ := defaultσ) hrty))
      (hcons (hlToBVarVal (σ := defaultσ) d.argTys params henc hl))).trans h_sound)

theorem UFConsistent_of_DefConsistent_var {uAT : Bool} {cctx : CoreCtx} {ufs : UFCtx}
    (v : VarDef)
    (hbase : LExpr.MonoTyIsBase v.ty)
    {Φpre : FVarCtx} (hsub : Φpre ⊆ cctx.toΦ)
    (hbody : LExpr.HasSimpType Φpre cctx.toΨ [] v.body v.ty)
    {divByZero modByZero : Int → Int}
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hndΦ : (cctx.toΦ.map Prod.fst).Nodup) (hndΨ : (cctx.toΨ.map Prod.fst).Nodup)
    (hdisj : ∀ x ∈ cctx.toΦ, x.1 ∉ cctx.toΨ.map Prod.fst)
    (hcons : fvarVal ⟨v.name, ()⟩ (v.ty.substTyVars simpTyVarVal)
      = simpDenote opInterp fvarVal .nil v.body v.ty (HasSimpType_implies_HasTypeA hbody))
    (hfvar : FNameCtxCorresponds uAT cctx.toΦ ufs) (hfn : FNameCtxCorresponds uAT cctx.toΨ ufs)
    (huf : UFCtxWF ufs) (hfnwf : FnNamesNotPredefined cctx.toΨ uAT)
    (hdtfree : cctx.toTranslateEnv.datatypeFuns = ∅)
    (hΦ : (v.name, v.ty) ∈ cctx.toΦ)
    {smtτ : TermType} {ifbody : Term}
    (htc : Term.typeCheck ⟨[], ufs, []⟩ ifbody = .ok smtτ)
    (h_ok : translate uAT cctx.toTranslateEnv [] v.body = .ok ifbody)
    (hτ : LExpr.MonoTyIsBase v.ty ∧ tyToTermType uAT v.ty = smtτ) :
    IF.UFConsistent ⟨v.name, [], smtτ, ifbody⟩ htc
      (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal) divByZero modByZero := by
  unfold IF.UFConsistent
  intro hl
  have hnil : hl = .nil := by cases hl; rfl
  subst hnil
  have hfenv_full := mkUFInterp_fvarCorresponds uAT (Ψ := cctx.toΨ) hfvar hndΦ opInterp fvarVal
  have hopenv := mkUFInterp_fnCorresponds uAT (Φ := cctx.toΦ) hfn hndΨ hdisj opInterp fvarVal
  have hused : ∀ nm ∈ (Φpre ++ cctx.toΨ).map Prod.fst,
      (staticUsedNames cctx.toTranslateEnv).contains nm := by
    intro nm hnm
    rw [List.map_append, List.mem_append] at hnm
    apply coreCtx_names_used
    rw [List.map_append, List.mem_append]
    rcases hnm with hnm | hnm
    · left
      obtain ⟨p, hp_mem, hp⟩ := List.mem_map.mp hnm
      exact hp ▸ List.mem_map_of_mem (f := Prod.fst) (hsub hp_mem)
    · right; exact hnm
  simp only [IF.toUF, UF.applyDenoteTyped, UF.applyDenoteTyped', List.map_nil]
  have hcol : collectArrowTy v.ty = ([], v.ty) := collectArrowTy_base hbase
  have hlk : lookupUF ufs v.name = some ⟨v.name, [], smtτ⟩ := by
    obtain ⟨uf, huf'⟩ := Option.isSome_iff_exists.mp (hfvar.fvar_resolves v.name _ hΦ)
    have hid := lookupUF_id huf'
    have hargs := hfvar.args_eq v.name _ uf hΦ huf'
    have hout := hfvar.out_eq v.name _ uf hΦ huf'
    rw [hcol] at hargs hout; simp only at hargs hout
    have hout_eq : uf.out = smtτ := hout.2.symm.trans hτ.2
    have hargs_eq : uf.args = [] := by
      have := hargs.2; simp only [List.map_nil] at this; exact this.symm
    rw [huf']; cases uf; simp_all
  have hcorr := (mkUFInterp_fvar_eq uAT (Ψ := cctx.toΨ) hndΦ opInterp fvarVal hΦ hlk
    (by rw [hcol]; exact ⟨by simp, rfl⟩) (by rw [hcol]; exact hτ)
    (tyDenote_eq_smtTyDenote (σ := defaultσ) hτ)).symm
  rw [← hcorr, hcons]
  have hbenv : BVarEnvCorresponds (σ := defaultσ) (uAT := uAT) bwf_nil (bvarVal := .nil) (hlToEnv (σ := defaultσ) [] .nil) := by
    intro i τ' _ hlook; simp at hlook
  exact translate_sound (Γ := ⟨cctx.toΨ, Φpre⟩) (tenv := cctx.toTranslateEnv)
    (useArrayTheory := uAT) (σ := defaultσ)
    hbody (HasSimpType_implies_HasTypeA hbody) opInterp fvarVal .nil
    htc huf (mkUFInterp uAT cctx.toΦ cctx.toΨ ufs opInterp fvarVal) (hlToEnv (σ := defaultσ) [] .nil)
    h_ok hτ.2 (hfvar.mono_sub hsub) hfn bwf_nil hused havoid_nil
    (hfenv_full.mono_sub hsub) hopenv hbenv hop hfnwf hdtfree

/-! ## The two `translateQuery` correspondences, and the whole-query soundness headline -/

/-- `q.ufs` corresponds to the source `toΨ`/`toΦ` — the two `translate_sound` bridges,
    reusing the `translateQuery_WF` derivation. -/
theorem translateQuery_corr {uAT : Bool}
    {cctx : CoreCtx} {goal : Expression.Expr} {q : SMTQuery}
    (henc : translateQuery uAT cctx goal = .ok q)
    (hwf : CoreCtx.WF cctx goal) (hnames : CoreCtx.NamesWF cctx uAT) :
    FNameCtxCorresponds uAT cctx.toΨ q.ufs ∧ FNameCtxCorresponds uAT cctx.toΦ q.ufs := by
  have hretBase := hwf.fnDefsWF.mem_retBase
  have hvarBase := hwf.varDefsWF.mem_tyBase
  have hargsBase := hwf.fnDefsWF.mem_argsBase
  have hufs_eq : q.ufs = (cctx.toΨ ++ cctx.toΦ).map (encodeUF uAT) := tq_ufs_eq henc hretBase hvarBase
  have hnd_full : ((cctx.toΨ ++ cctx.toΦ).map Prod.fst).Nodup := hnames.names_nodup
  have hbase_fnDecls : ∀ p ∈ cctx.fnDecls, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 :=
    fun p hp => hwf.fnDeclsSigBase p.1 p.2 hp
  have hbase_varDecls : ∀ p ∈ cctx.varDecls, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 :=
    fun p hp => hwf.varDeclsSigBase p.1 p.2 hp
  have hbase_toΨ : ∀ p ∈ cctx.toΨ, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 := by
    intro p hp
    rw [CoreCtx.toΨ, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hbase_fnDecls p hp
    · obtain ⟨d, hd_mem, hd_eq⟩ := List.mem_map.mp hp
      have hp2 : p.2 = LMonoTy.mkArrow' d.retTy d.argTys := by rw [← hd_eq]
      rw [hp2, collectArrowTy_mkArrow' (hretBase d hd_mem)]
      exact ⟨hargsBase d hd_mem, hretBase d hd_mem⟩
  have hbase_toΦ : ∀ p ∈ cctx.toΦ, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 := by
    intro p hp
    rw [CoreCtx.toΦ, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hbase_varDecls p hp
    · obtain ⟨v, hv_mem, hv_eq⟩ := List.mem_map.mp hp
      have hp2 : p.2 = v.ty := by rw [← hv_eq]
      rw [hp2, collectArrowTy_base (hvarBase v hv_mem)]
      exact ⟨by intro a ha; simp at ha, hvarBase v hv_mem⟩
  have hbase_full : ∀ p ∈ cctx.toΨ ++ cctx.toΦ, (∀ a ∈ (collectArrowTy p.2).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy p.2).2 := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hbase_toΨ p hp
    · exact hbase_toΦ p hp
  have hc_full : FNameCtxCorresponds uAT (cctx.toΨ ++ cctx.toΦ) q.ufs := by
    rw [hufs_eq]
    exact FNameCtxCorresponds.of_map_encode hbase_full hnd_full
  exact ⟨hc_full.mono_sub (List.subset_append_left _ _), hc_full.mono_sub (List.subset_append_right _ _)⟩

/-- **Shared model-transfer core** for both verdicts. Given a source model consistent with `cctx`
    (definitions, asserts, distincts), it equates the SMT goal-term denotation with the source goal
    denotation, and builds a `checkSat` witness for ANY well-typed boolean literal the constructed
    model satisfies. Direction-agnostic — the caller picks the literal (`¬goal` for validity, `goal`
    for unsatisfiability). -/
theorem query_checkSat_of_coreModel
    {cctx : CoreCtx} {goal : Expression.Expr}
    (hwf : CoreCtx.WF cctx goal)
    {q : SMTQuery}
    {useArrayTheory : Bool}
    (henc : translateQuery useArrayTheory cctx goal = .ok q)
    (hnames : CoreCtx.NamesWF cctx useArrayTheory)
    (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) (hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (hdefcons : CoreCtx.DefConsistent cctx goal hwf opInterp fvarVal)
    (hasserts : CoreCtx.ModelSatisfiesAsserts cctx goal hwf opInterp fvarVal)
    (hdistincts : CoreCtx.ModelSatisfiesDistincts cctx goal hwf opInterp fvarVal) :
    ((Term.denoteTyped (mkUFInterp useArrayTheory cctx.toΦ cctx.toΨ q.ufs opInterp fvarVal)
          mkVarEnv divByZero modByZero q.obl .bool (translateQuery_WF hwf hnames henc).oblWF : Bool)
        = (simpDenote opInterp fvarVal .nil goal (.tcons "bool" [])
            (HasSimpType_implies_HasTypeA hwf.goalWF) : Bool))
      ∧ (∀ (lit : Term) (hltc : Term.typeCheck ⟨[], q.ufs, []⟩ lit = .ok .bool),
          (Term.denoteTyped (mkUFInterp useArrayTheory cctx.toΦ cctx.toΨ q.ufs opInterp fvarVal)
              mkVarEnv divByZero modByZero lit .bool hltc : Bool) = true →
          q.checkSat (translateQuery_WF hwf hnames henc) [lit]
            (fun t ht => by rw [List.mem_singleton] at ht; subst ht; exact hltc)) := by
  have hwfq : SMTQuery.WF q := translateQuery_WF hwf hnames henc
  have huf : UFCtxWF q.ufs := hwfq.ufsWF
  obtain ⟨hcΨ, hcΦ⟩ := translateQuery_corr henc hwf hnames
  have hfnwf : FnNamesNotPredefined cctx.toΨ useArrayTheory := hnames.fnNamesNotPredefined
  have hdtfree : cctx.toTranslateEnv.datatypeFuns = ∅ := hwf.datatypeFunsEmpty
  have fnDefArgsBase := hwf.fnDefsWF.mem_argsBase
  have fnDefRetBase := hwf.fnDefsWF.mem_retBase
  have varDefTyBase := hwf.varDefsWF.mem_tyBase
  have fnDefParamsNodup := hwf.fnDefsWF.mem_paramsNodup
  -- Nodup / disjointness of the two source name-halves.
  have hnd_full : ((cctx.toΨ ++ cctx.toΦ).map Prod.fst).Nodup := hnames.names_nodup
  rw [List.map_append, List.nodup_append] at hnd_full
  have hndΨ : (cctx.toΨ.map Prod.fst).Nodup := hnd_full.1
  have hndΦ : (cctx.toΦ.map Prod.fst).Nodup := hnd_full.2.1
  have hdisj : ∀ x ∈ cctx.toΦ, x.1 ∉ cctx.toΨ.map Prod.fst := by
    intro x hx hmem
    exact hnd_full.2.2 x.1 hmem x.1 (List.mem_map_of_mem (f := Prod.fst) hx) rfl
  have varDefsΦ : ∀ v ∈ cctx.varDefs, (v.name, v.ty) ∈ cctx.toΦ := by
    intro v hv
    rw [CoreCtx.toΦ, List.mem_append]
    exact Or.inr (List.mem_map_of_mem (f := fun v => (v.name, v.ty)) hv)
  -- Membership of a `fnDef`'s reconstructed arrow signature in `toΨ`.
  have fnDefMem : ∀ d ∈ cctx.fnDefs, (d.name, List.foldr LMonoTy.arrow d.retTy d.argTys) ∈ cctx.toΨ := by
    intro d hd
    have hmk : LMonoTy.mkArrow' d.retTy d.argTys = List.foldr LMonoTy.arrow d.retTy d.argTys := by
      induction d.argTys with
      | nil => rfl
      | cons a as ih => simp only [LMonoTy.mkArrow', List.foldr_cons, ih]
    rw [CoreCtx.toΨ, List.mem_append]
    exact Or.inr (by rw [← hmk]; exact List.mem_map_of_mem (f := fun d => (d.name, LMonoTy.mkArrow' d.retTy d.argTys)) hd)
  -- `toΨ`-fold identity (for `mem_typing` subset targets).
  have htoΨeq : cctx.toΨ = cctx.fnDecls ++ cctx.fnDefs.map (fun d => (d.name, LMonoTy.mkArrow' d.retTy d.argTys)) := rfl
  have htoΦeq : cctx.toΦ = cctx.varDecls ++ cctx.varDefs.map (fun v => (v.name, v.ty)) := rfl
  let U := mkUFInterp useArrayTheory cctx.toΦ cctx.toΨ q.ufs opInterp fvarVal
  obtain ⟨_, _, _, _, _, hgoal_ok⟩ := translateQuery_inv henc
  have hgtc : Term.typeCheck ⟨[], q.ufs, []⟩ q.obl = .ok .bool := hwfq.oblWF
  have hgoal_denote : (Term.denoteTyped U mkVarEnv divByZero modByZero q.obl .bool hgtc : Bool)
      = (simpDenote opInterp fvarVal .nil goal (.tcons "bool" [])
          (HasSimpType_implies_HasTypeA hwf.goalWF) : Bool) :=
    mkModel_denote_obligation_refactor hcΦ hcΨ huf hfnwf hdtfree hndΦ hndΨ hdisj opInterp hop fvarVal
      hwf.goalWF hgtc hgoal_ok
  have hpreamble : IFs.UFConsistent q.fs hwfq.fsTypeCheck U divByZero modByZero := by
    intro f hf
    rcases translateQuery_defs_mem henc f hf with ⟨d, hd, bodyTm, h_ok, hfeq⟩ | ⟨v, hv, bodyTm, h_ok, hfeq⟩
    · subst hfeq
      obtain ⟨Ψpre, hsubpre, hbodypre, hpFreshpre⟩ := hwf.fnDefsWF.mem_typing d hd
      have hsub : Ψpre ⊆ cctx.toΨ := by rw [htoΨeq]; exact hsubpre
      have hbwf := fnDefParams_bvarCorresponds (uAT := useArrayTheory) (fnDefArgsBase d hd) (fnDefParamsNodup d hd)
      have hrty : LExpr.MonoTyIsBase d.retTy ∧ tyToTermType useArrayTheory d.retTy = tyToTermType useArrayTheory d.retTy := ⟨fnDefRetBase d hd, rfl⟩
      have hcons : ∀ (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal d.argTys),
          applyBVarVal d.argTys d.retTy
            (opInterp d.name ((List.foldr LMonoTy.arrow d.retTy d.argTys).substTyVars simpTyVarVal)) bvarVal
          = simpDenote opInterp fvarVal bvarVal d.body d.retTy (HasSimpType_implies_HasTypeA hbodypre) :=
        fun bvarVal => hdefcons.1 d hd bvarVal
      exact UFConsistent_of_DefConsistent_op d hsub hbodypre opInterp hop fvarVal hndΨ hdisj
        hcons hcΨ huf hfnwf hdtfree (fnDefMem d hd)
        hbwf (fnDefParams_havoid (Ψ := Ψpre) hpFreshpre) (hwfq.fsTypeCheck _ hf) h_ok hrty (fnDefRetBase d hd)
    · subst hfeq
      obtain ⟨Φpre, hsubpre, hbodypre⟩ := hwf.varDefsWF.mem_typing v hv
      have hsub : Φpre ⊆ cctx.toΦ := by rw [htoΦeq]; exact hsubpre
      have hτ : LExpr.MonoTyIsBase v.ty ∧ tyToTermType useArrayTheory v.ty = tyToTermType useArrayTheory v.ty := ⟨varDefTyBase v hv, rfl⟩
      have hcons : fvarVal ⟨v.name, ()⟩ (v.ty.substTyVars simpTyVarVal)
          = simpDenote opInterp fvarVal .nil v.body v.ty (HasSimpType_implies_HasTypeA hbodypre) :=
        hdefcons.2 v hv
      exact UFConsistent_of_DefConsistent_var v (varDefTyBase v hv) hsub hbodypre opInterp hop fvarVal
        hndΦ hndΨ hdisj hcons hcΦ hcΨ huf hfnwf hdtfree (varDefsΦ v hv) (hwfq.fsTypeCheck _ hf) h_ok hτ
  -- Every persistent assertion is satisfied by the constructed model.
  have hassert_sat : ∀ t ∈ q.asserts, ∀ (hatc : Term.typeCheck ⟨[], q.ufs, []⟩ t = .ok .bool),
      (Term.denoteTyped U mkVarEnv divByZero modByZero t .bool hatc : Bool) = true := by
    intro t ht hatc
    rcases translateQuery_asserts_mem henc t ht with ⟨e, he, h_ok⟩ | ⟨e, he, h_ok⟩ | ⟨es, hes, ts, htls, hteq⟩
    · rw [mkModel_denote_obligation_refactor hcΦ hcΨ huf hfnwf hdtfree hndΦ hndΨ hdisj opInterp hop fvarVal
        (hwf.fnAxiomsWF e he) hatc h_ok]
      exact hasserts.2 e he
    · rw [mkModel_denote_obligation_refactor hcΦ hcΨ huf hfnwf hdtfree hndΦ hndΨ hdisj opInterp hop fvarVal
        (hwf.assumptionsWF e he) hatc h_ok]
      exact hasserts.1 e he
    · subst hteq
      obtain ⟨hbase, hall⟩ := (hwf.distinctsWF es hes).2.choose_spec
      have hsat_es : DistinctSat cctx.toΦ cctx.toΨ opInterp fvarVal es (hwf.distinctsWF es hes).2.choose hall :=
        hdistincts es hes
      exact mkModel_translate_distinct hcΦ hcΨ huf hfnwf hdtfree hndΦ hndΨ hdisj opInterp hop fvarVal
        hbase hall hsat_es hatc htls
  refine ⟨hgoal_denote, ?_⟩
  intro lit hltc hsat
  refine ⟨defaultσ, inferInstance, SmtArrayTheory, U, mkVarEnv, divByZero, modByZero, hpreamble, ?_⟩
  intro t ht
  rw [List.mem_append] at ht
  rcases ht with ht | ht
  · exact hassert_sat t ht _
  · rw [List.mem_singleton] at ht
    subst ht
    exact hsat

/-- **Statement B.** If the emitted query is `UnsatWithNegObl` (its SMT-LIB rendering refutes the negated
    goal), the source `CoreCtx` is denotationally valid. -/
theorem query_valid_of_unsatWithNegObl
    -- ── source side ──
    {cctx : CoreCtx} {goal : Expression.Expr}
    (hwf : CoreCtx.WF cctx goal)
    -- ── target side ──
    {q : SMTQuery}
    -- ── correspondence ──
    {useArrayTheory : Bool}
    (henc : translateQuery useArrayTheory cctx goal = .ok q)
    (hnames : CoreCtx.NamesWF cctx useArrayTheory)
    (hprove : q.UnsatWithNegObl (translateQuery_WF hwf hnames henc)) :
    CoreCtx.Valid cctx goal hwf := by
  intro divByZero modByZero opInterp hop fvarVal hdefcons hasserts hdistincts
  obtain ⟨hgoal_denote, mkWitness⟩ :=
    query_checkSat_of_coreModel hwf henc hnames divByZero modByZero opInterp hop fvarVal
      hdefcons hasserts hdistincts
  let U := mkUFInterp useArrayTheory cctx.toΦ cctx.toΨ q.ufs opInterp fvarVal
  cases hobl : (simpDenote opInterp fvarVal .nil goal (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.goalWF) : Bool) with
  | true => rfl
  | false =>
    exfalso
    have hwfq : SMTQuery.WF q := translateQuery_WF hwf hnames henc
    have hgtc : Term.typeCheck ⟨[], q.ufs, []⟩ q.obl = .ok .bool := hwfq.oblWF
    have hntc : Term.typeCheck ⟨[], q.ufs, []⟩ (Term.app (.core .not) [q.obl] .bool) = .ok .bool :=
      hwfq.notOblTypeCheck
    have hodenote : (Term.denoteTyped U mkVarEnv divByZero modByZero q.obl .bool hgtc : Bool) = false :=
      hgoal_denote.trans hobl
    have hnot_sat : (Term.denoteTyped U mkVarEnv divByZero modByZero
        (Term.app (.core .not) [q.obl] .bool) .bool hntc : Bool) = true := by
      unfold Term.denoteTyped
      rcases htni : Term.typeCheck_not_inv hntc with ⟨ht', heq⟩
      dsimp only; rw [cast_eq]
      have hpi : Term.denoteTyped U mkVarEnv divByZero modByZero q.obl .bool ht'
          = Term.denoteTyped U mkVarEnv divByZero modByZero q.obl .bool hgtc := rfl
      rw [hpi, hodenote]; rfl
    exact hprove (mkWitness (Term.app (.core .not) [q.obl] .bool) hntc hnot_sat)

/-- **Statement B, dual.** If the emitted query is `UnsatWithObl` (its SMT-LIB rendering refutes the goal
    asserted positively — no model satisfies the asserts together with the goal), the source `CoreCtx`
    is denotationally unsatisfiable (the asserts entail `¬goal`). -/
theorem query_unsat_of_unsatWithObl
    -- ── source side ──
    {cctx : CoreCtx} {goal : Expression.Expr}
    (hwf : CoreCtx.WF cctx goal)
    -- ── target side ──
    {q : SMTQuery}
    -- ── correspondence ──
    {useArrayTheory : Bool}
    (henc : translateQuery useArrayTheory cctx goal = .ok q)
    (hnames : CoreCtx.NamesWF cctx useArrayTheory)
    (hrefute : q.UnsatWithObl (translateQuery_WF hwf hnames henc)) :
    CoreCtx.Unsat cctx goal hwf := by
  intro divByZero modByZero opInterp hop fvarVal hdefcons hasserts hdistincts
  obtain ⟨hgoal_denote, mkWitness⟩ :=
    query_checkSat_of_coreModel hwf henc hnames divByZero modByZero opInterp hop fvarVal
      hdefcons hasserts hdistincts
  let U := mkUFInterp useArrayTheory cctx.toΦ cctx.toΨ q.ufs opInterp fvarVal
  cases hobl : (simpDenote opInterp fvarVal .nil goal (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.goalWF) : Bool) with
  | false => rfl
  | true =>
    exfalso
    have hwfq : SMTQuery.WF q := translateQuery_WF hwf hnames henc
    have hgtc : Term.typeCheck ⟨[], q.ufs, []⟩ q.obl = .ok .bool := hwfq.oblWF
    have hobl_sat : (Term.denoteTyped U mkVarEnv divByZero modByZero q.obl .bool hgtc : Bool) = true :=
      hgoal_denote.trans hobl
    exact hrefute (mkWitness q.obl hgtc hobl_sat)

end Core.Refactor
