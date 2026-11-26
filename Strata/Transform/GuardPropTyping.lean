/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardPropProps
public import Strata.Transform.GuardFwdTyping
public import Strata.Transform.Passive.WellTyped
import all Strata.Transform.GuardPropProps
import all Strata.Transform.GuardFwdTyping

/-! # Guard propagation keeps conditions typed

Guard propagation replaces a variable only by a Boolean literal, for a guard known in the guard
map, or by a candidate of the name (`GuardFwd.cand`), which has the type the typing `Γ` gives
the name when the recorded right-hand sides do.  The guards of the map are Boolean variables:
those of the facts have the declared type `bool`, and those the contextual simplification adds
are rewritten conditions of conditionals.  So, under the typing laws `TypedOpLaws` and when the
literals `true` and `false` have the Boolean type, the contextual simplification keeps the type
of an expression whose annotations agree with `Γ` (`rwG_typed`), and guard propagation keeps the
conditions of the `assume`s, `assert`s and `cover`s of a list in passive form typed
(`guardProp_condsTyped`).

Key theorems: `rwG_typed`, `guardProp_condsTyped`. -/

namespace Imperative
namespace GuardProp

open WP BigStep GuardFwd

public section

variable {P : PureExpr} [BEq P.Ident] [Hashable P.Ident] [LawfulBEq P.Ident] [HasFvar P]
  [HasFvars P] [DecidableEq P.Ident] [HasBool P] [HasSubstFvar P] [WPLang P] [HasOps P]
  [GuardOps P] {Typ : P.Expr → P.Ty → Prop} {oe : WPOps.OpEnv P}

omit [LawfulBEq P.Ident] in
/-- **The replacement of a variable has the variable's type**, when the recorded right-hand sides
    pass the checks and have the types `Γ` gives their names, the guards of the map are Boolean
    under `Γ`, and the Boolean literals have the Boolean type. -/
theorem look_typed [LawfulHasFvars P] (hS : GuardFwdSynLaws P) (hP : GuardPropSynLaws P)
    (hL : TypedOpLaws Typ oe) (hB : ∀ b, Typ (boolE (P := P) b) HasBool.boolTy)
    {dv df : P.Ident → Bool} {Γ : VarTyping P} {sc : Scope P} (hs : ScopeOK dv df Γ sc)
    (hst : ScopeTyped Typ Γ sc) (K : Guards P)
    (hK : ∀ g b, K[g]? = some b → Γ g = some HasBool.boolTy) :
    ∀ (n : Nat) (y : P.Ident) (r : P.Expr), look sc K n y = some r →
      ∀ T, Γ y = some T → Typ r T
  | n, y, r, h, T, hT => by
    unfold look at h
    split at h
    · rename_i b hb
      cases h
      obtain rfl := Option.some.inj (hT.symm.trans (hK y b hb))
      exact hB b
    split at h <;> try cases h
    rename_i r0 hr0
    have hc := (Option.filter_eq_some_iff.1 hr0).1
    obtain ⟨T0, hT0, hr0T⟩ := cand_typed hL hst hc
    obtain rfl := Option.some.inj (hT.symm.trans hT0)
    split at h
    · rename_i n z hz
      cases h
      cases hl : look sc K n z with
      | none => exact hr0T
      | some r' =>
        exact look_typed hS hP hL hB hs hst K hK n z r' hl T
          ((cand_ok hS hs hc).2.1 z T (hL.getFvar hz hr0T))
    · exact Option.some.inj h ▸ hr0T

/-- **The contextual simplification keeps the type** of an expression whose annotations agree
    with `Γ` and whose free variables are defined, when the recorded right-hand sides pass the
    checks and have the types `Γ` gives their names, the guards of the map are Boolean under
    `Γ`, and the Boolean literals have the Boolean type. -/
theorem rwG_typed [LawfulHasFvars P] (hS : GuardFwdSynLaws P) (hP : GuardPropSynLaws P)
    (hL : TypedOpLaws Typ oe) (hB : ∀ b, Typ (boolE (P := P) b) HasBool.boolTy)
    {dv df : P.Ident → Bool} {Γ : VarTyping P} {sc : Scope P} (hs : ScopeOK dv df Γ sc)
    (hst : ScopeTyped Typ Γ sc) (fuel : Nat) (K : Guards P) (e : P.Expr) :
    (∀ g b, K[g]? = some b → Γ g = some HasBool.boolTy) → ExprOK dv df Γ e →
      ∀ {ty}, Typ e ty → Typ (rwG sc fuel K e) ty := by
  fun_induction rwG sc fuel K e with
  | case1 K e c t f hv c' g hg ihc iht ihf =>
    intro hK he ty hT
    have hp := (ExprOK.iteView_iff hS hv).1 he
    have ht := (hL.iteView hv).1 hT
    have hc := ihc hK hp.1 ht.1
    have hgΓ := (rwG_ok hS hP hs fuel K c hp.1).2.1 g _ (hL.getFvar hg hc)
    have hK' : ∀ b, ∀ g' b', (K.insert g b)[g']? = some b' → Γ g' = some HasBool.boolTy :=
      fun b g' b' h => by
        rw [Std.HashMap.getElem?_insert] at h
        split at h
        · exact beq_iff_eq.1 ‹_› ▸ hgΓ
        · exact hK g' b' h
    exact hL.ite.2 ⟨hc, iht (hK' true) hp.2.1 ht.2.1, ihf (hK' false) hp.2.2 ht.2.2⟩
  | case2 K e c t f hv c' hg ihc iht ihf =>
    intro hK he ty hT
    have hp := (ExprOK.iteView_iff hS hv).1 he
    have ht := (hL.iteView hv).1 hT
    exact hL.ite.2 ⟨ihc hK hp.1 ht.1, iht hK hp.2.1 ht.2.1, ihf hK hp.2.2 ht.2.2⟩
  | case3 K e hv =>
    intro hK he ty hT
    exact hL.substFn _ hT fun p hp v hv =>
      look_typed hS hP hL hB hs hst K hK fuel p.1 v hv p.2 (he.2.1 p.1 p.2 hp)

/-- The declared types of the walk's state are those `Γ` gives the names, which `dv` defines,
    and the guards of its facts have the declared type `bool`. -/
@[expose] def TysOK (dv : P.Ident → Bool) (Γ : VarTyping P) (st : PSt P) : Prop :=
  (∀ (y : P.Ident) (T : P.Ty), st.tys[y]? = some T → Γ y = some T ∧ dv y = true) ∧
    ∀ (g : P.Ident) (b : Bool), st.facts[g]? = some b → st.tys[g]? = some HasBool.boolTy

omit [LawfulBEq P.Ident] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasBool P]
  [HasSubstFvar P] [WPLang P] [HasOps P] [GuardOps P] in
/-- The types of the recorded right-hand sides after an `init` of `x` at type `ty`: the typing
    grows by `x`, recorded with a right-hand side of type `ty`, if any. -/
private theorem scopeTyped_insert [LawfulBEq P.Ident] {Γ : VarTyping P} {sc : Scope P}
    (hs : ScopeTyped Typ Γ sc) {x : P.Ident} {ty : P.Ty} {val : Option P.Expr}
    (hv : ∀ d, val = some d → Typ d ty) :
    ScopeTyped Typ (Γ.extend [(x, ty)]) (sc.insert x val) := by
  intro y d hy
  simp only [Std.HashMap.getElem?_insert] at hy
  split at hy <;> rename_i hxy
  · obtain rfl : x = y := beq_iff_eq.1 hxy
    exact ⟨ty, by simp [VarTyping.extend_singleton], hv d (Option.some.inj hy)⟩
  · obtain ⟨T, hT, hdT⟩ := hs y d hy
    exact ⟨T, by simp [VarTyping.extend_singleton, hT, Ne.symm (mt beq_iff_eq.2 hxy)], hdT⟩

omit [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P] [HasOps P] [GuardOps P] in
/-- The declared types after an `init` of `x` at type `ty`, `x` undefined before it. -/
private theorem tysOK_insert {dv dv' : P.Ident → Bool} {Γ : VarTyping P} {st : PSt P}
    (h : TysOK dv Γ st) {x : P.Ident} {ty : P.Ty} {v : Option P.Expr} (hx : dv x = false)
    (hd : ∀ z, dv z = true → dv' z = true) (hdx : dv' x = true) :
    TysOK dv' (Γ.extend [(x, ty)])
      ({ st with scope := st.scope.insert x v, tys := st.tys.insert x ty } : PSt P) := by
  refine ⟨fun y T hy => ?_, fun g b hg => ?_⟩
  · simp only [Std.HashMap.getElem?_insert] at hy
    split at hy <;> rename_i hxy
    · obtain rfl : x = y := beq_iff_eq.1 hxy
      exact ⟨by simp [VarTyping.extend_singleton, Option.some.inj hy], hdx⟩
    · obtain ⟨h1, h2⟩ := h.1 y T hy
      exact ⟨by simp [VarTyping.extend_singleton, h1, Ne.symm (mt beq_iff_eq.2 hxy)], hd y h2⟩
  · have hgb := h.2 g b hg
    have hgx : x ≠ g := fun hxg => by
      subst hxg
      simp [(h.1 x _ hgb).2] at hx
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq, hgx, ↓reduceIte, hgb]

omit [HasOps P] [GuardOps P] in
/-- The facts after an assumption keep their guards of the declared type `bool`. -/
private theorem tysOK_addFact {dv : P.Ident → Bool} {Γ : VarTyping P} {st : PSt P}
    (h : TysOK dv Γ st) (ini : Std.HashSet P.Ident) (e : P.Expr) :
    TysOK dv Γ { st with facts := addFact ini st e } := by
  refine ⟨h.1, fun g b hg => ?_⟩
  simp only [addFact] at hg
  split at hg
  · rename_i g' b' _
    split at hg
    · rename_i hbv
      rw [Std.HashMap.getElem?_insert] at hg
      split at hg
      · obtain rfl : g' = g := beq_iff_eq.1 ‹_›
        simp only [boolVar, Bool.and_eq_true] at hbv
        cases ht : st.tys[g']? with
        | none => simp [ht] at hbv
        | some T =>
          simp only [ht, Option.map_some, Option.getD_some] at hbv
          rw [WPLang.tyBEq_eq hbv.2]
      · exact h.2 g b hg
    · exact h.2 g b hg
  · exact h.2 g b hg

omit [LawfulBEq P.Ident] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasSubstFvar P]
  [WPLang P] [HasOps P] [GuardOps P] in
/-- `TysOK` survives the growth of the defined names, under a typing that agrees on them. -/
private theorem TysOK.mono {dv dv' : P.Ident → Bool} {Γ Γ' : VarTyping P} {st : PSt P}
    (h : TysOK dv Γ st) (hd : ∀ z, dv z = true → dv' z = true)
    (hΓ : ∀ z, dv z = true → Γ' z = Γ z) : TysOK dv' Γ' st :=
  ⟨fun y T hy => (h.1 y T hy).elim fun h1 h2 => ⟨(hΓ y h2).trans h1, hd y h2⟩, h.2⟩

/-- **The walk keeps the conditions typed** on a list in passive form that is def-use well formed
    and whose annotations agree with `Γ`, with typed `init`s, when the recorded right-hand sides
    of the scope pass the checks and have the types `Γ` gives their names, the declared types of
    the state are those of `Γ` and the guards of its facts are Boolean (`TysOK`). -/
theorem walk_condsTyped [LawfulHasFvars P] (hS : GuardFwdSynLaws P) (hP : GuardPropSynLaws P)
    (hL : TypedOpLaws Typ oe) (hB : ∀ b, Typ (boolE (P := P) b) HasBool.boolTy)
    (ini : Std.HashSet P.Ident) (df : P.Ident → Bool) (ss : PStmts P)
    (hp : Block.passiveForm ss = true) :
    ∀ (st : PSt P) (dv : P.Ident → Bool) (Γ : VarTyping P),
    Block.defUseWellFormed dv df ss = true → Block.fvarTypesWellAnnotated Γ ss →
    ScopeOK dv df Γ st.scope → ScopeTyped Typ Γ st.scope → TysOK dv Γ st →
    Block.initsTyped Typ ss → Block.condsTyped Typ ss →
      Block.condsTyped Typ (walk ini st ss).1 := by
  induction ss using Block.passiveForm.induct <;> intro st dv Γ hd hf hs hst htys hT hc <;>
    (try cases ‹ExprOrNondet P›) <;>
    simp only [Block.passiveForm, walk, walkS, Block.defUseWellFormed, Stmt.defUseWellFormed,
      Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated, HasVarsImp.readVars,
      CmdExt.readVars, ExprOrNondet.getVars, HasVarsImp.modifiedVars, CmdExt.modifiedVars,
      Cmd.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
      HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps, ExprOrNondet.getOps, Stmt.definedVars,
      HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Stmt.typedDefinedVars,
      HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars, Bool.and_eq_true, List.all_eq_true,
      List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq, Bool.false_eq_true,
      Block.initsTyped, Stmt.initsTyped, CmdExt.initsTyped, Block.condsTyped, Stmt.condsTyped,
      CmdExt.condsTyped] at hp hd hf hT hc ⊢
  case case2.det x ty md rest ih e =>
    obtain ⟨⟨⟨hfv, hx⟩, hops⟩, hrest⟩ := hd
    refine ⟨trivial, ih hp _ _ _ hrest hf.2 ?_ ?_ ?_ hT.2 hc.2⟩
    · refine scopeOK_insert hs (Bool.eq_false_iff.2 hx) (fun d h => ?_) fun z hz => by simp [hz]
      split at h <;> cases h
      exact ⟨hfv, hf.1, hops⟩
    · exact scopeTyped_insert hst fun d h => by split at h <;> cases h; exact hT.1
    · exact tysOK_insert htys (Bool.eq_false_iff.2 hx) (fun z hz => by simp [hz]) (by simp)
  case case2.nondet x ty md rest ih =>
    refine ⟨trivial, ih hp _ _ _ hd.2 hf.2 ?_ ?_ ?_ hT.2 hc.2⟩
    · exact scopeOK_insert hs (Bool.eq_false_iff.2 hd.1.2) (fun _ h => by cases h)
        fun z hz => by simp [hz]
    · exact scopeTyped_insert hst fun _ h => by cases h
    · exact tysOK_insert htys (Bool.eq_false_iff.2 hd.1.2) (fun z hz => by simp [hz]) (by simp)
  case case3 l e md rest ih | case4 l e md rest ih | case5 l e md rest ih =>
    obtain ⟨⟨hfv, hops⟩, hrest⟩ := hd
    have hK : ∀ g b, st.facts[g]? = some b → Γ g = some HasBool.boolTy :=
      fun g b h => (htys.1 g _ (htys.2 g b h)).1
    refine ⟨rwG_typed hS hP hL hB hs hst _ _ e hK ⟨hfv, hf.1, hops⟩ hc.1, ih hp _ _ _ hrest hf.2
      (hs.mono (fun z hz => by simp [hz]) fun _ _ => rfl) hst ?_ hT.2 hc.2⟩
    first
      | exact (tysOK_addFact htys ini _).mono (fun z hz => by simp [hz]) fun _ _ => rfl
      | exact htys.mono (fun z hz => by simp [hz]) fun _ _ => rfl
  case case6 t e md rest iht ihe ihr =>
    obtain ⟨⟨hpt, hpe⟩, hpr⟩ := hp
    obtain ⟨⟨⟨-, hdt⟩, hde⟩, hdr⟩ := hd
    obtain ⟨⟨-, hft, hfe⟩, hfr⟩ := hf
    exact ⟨⟨iht hpt st dv Γ hdt hft hs hst htys hT.1.1 hc.1.1,
      ihe hpe st dv Γ hde hfe hs hst htys hT.1.2 hc.1.2⟩,
      ihr hpr st _ _ hdr hfr (hs.mono (fun z hz => by simp [hz]) fun _ _ => rfl) hst
        (htys.mono (fun z hz => by simp [hz]) fun _ _ => rfl) hT.2 hc.2⟩


/-- **Guard propagation keeps the conditions typed.**  Under the typing laws `TypedOpLaws`, when
    the Boolean literals have the Boolean type, on a list in passive form that is def-use well
    formed (from the defined-names predicate `dv` and the declared-functions predicate `df`),
    whose annotations agree with a typing `Γ` and whose `init`s are typed, the conditions of the
    `assume`s, `assert`s and `cover`s of `guardProp ss` have the Boolean type when those of `ss`
    have. -/
theorem guardProp_condsTyped [LawfulHasFvars P] (hS : GuardFwdSynLaws P)
    (hP : GuardPropSynLaws P) (hL : TypedOpLaws Typ oe)
    (hB : ∀ b, Typ (boolE (P := P) b) HasBool.boolTy) {ss : PStmts P}
    (hp : Block.passiveForm ss = true) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    (hd : Block.defUseWellFormed dv df ss = true) (hf : Block.fvarTypesWellAnnotated Γ ss)
    (hT : Block.initsTyped Typ ss) (hc : Block.condsTyped Typ ss) :
    Block.condsTyped Typ (guardProp ss) :=
  walk_condsTyped hS hP hL hB _ df ss hp {} dv Γ hd hf (fun _ _ h => by simp at h)
    (fun _ _ h => by simp at h) ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩ hT hc

end -- public section

end GuardProp
end Imperative
