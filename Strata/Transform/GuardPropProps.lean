/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardProp
public import Strata.Transform.GuardFwdProps

/-! # Properties of guard propagation

On a list in passive form the output has the shape of the input: it is in passive form, defines
the same names with the same types, and is in tree form when the input is (`walk_shape`).  Every
expression of the output has its free variables, annotated occurrences and operators among those
of the input and of the recorded right-hand sides it reads (`rwG_ok`), so the output passes the
def-use and annotation checks of the initial-environment gate wherever the input does
(`walk_gate`).

Key theorems: `walk_shape`, `rwG_ok`, `walk_gate`. -/

namespace Imperative
namespace GuardProp

open WP BigStep GuardFwd

public section

variable {P : PureExpr} [BEq P.Ident] [Hashable P.Ident]

/-! ## The shape of the output -/

section Walk

variable [HasBool P] [HasFvar P] [HasFvars P] [WPOps P]

/-- The walk keeps an empty list empty and a nonempty one nonempty. -/
private theorem walk_isEmpty (ini : Std.HashSet P.Ident) (st : PSt P) (ss : PStmts P) :
    (walk ini st ss).1.isEmpty = ss.isEmpty := by
  cases ss <;> rfl

/-- **The shape of the output.**  On a list in passive form, the output of the walk is in
    passive form, defines the same names with the same declared types, and is in tree form when
    the input is. -/
theorem walk_shape (ini : Std.HashSet P.Ident) (ss : PStmts P) (hp : Block.passiveForm ss = true) :
    ∀ st : PSt P, Block.passiveForm (walk ini st ss).1 = true ∧
      (∀ b, Block.definedVars (walk ini st ss).1 b = Block.definedVars ss b) ∧
      Block.initTypes (walk ini st ss).1 = Block.initTypes ss ∧
      Block.treeForm (walk ini st ss).1 = Block.treeForm ss := by
  induction ss using Block.passiveForm.induct <;> (try cases ‹ExprOrNondet P›) <;>
    simp_all [walk, walkS, Block.passiveForm, Block.treeForm, Block.initTypes, Stmt.initTypes,
      HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars, HasInitTypesImp.initTypes,
      CmdExt.initTypes, Cmd.initTypes, walk_isEmpty]

end Walk

/-! ## Free variables, annotations and operators of the output -/

section Gate

variable [LawfulBEq P.Ident] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasBool P]
  [HasSubstFvar P] [WPLang P] [HasOps P] [GuardOps P]

/-- The laws of the syntax of expressions that the gate of guard propagation's output needs,
    beyond those of guard forwarding: an operator of a substitution is one of the expression or of
    an image, and the literal `false` has no operator. -/
structure GuardPropSynLaws (P : PureExpr) [DecidableEq P.Ident] [HasBool P] [HasFvar P]
    [HasFvars P] [HasSubstFvar P] [WPLang P] [HasOps P] : Prop where
  ops_substFn_mem : ∀ (e : P.Expr) (g : P.Ident → Option P.Expr) o,
    o ∈ HasOps.getOps (WPOps.substFn e g) →
      o ∈ HasOps.getOps e ∨ ∃ x r, g x = some r ∧ o ∈ HasOps.getOps r
  ops_ff : HasOps.getOps (HasBool.ff (P := P)) = []

omit [LawfulBEq P.Ident] in
/-- A candidate passes the checks when the scope does. -/
private theorem cand_ok (hS : GuardFwdSynLaws P) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {sc : Scope P} (hs : ScopeOK dv df Γ sc) {K : Guards P} {y : P.Ident} {r : P.Expr}
    (h : cand sc K y = some r) : ExprOK dv df Γ r := by
  unfold cand at h
  split at h <;> try cases h
  rename_i d hd
  split at h
  · exact Option.some.inj h ▸ hs y _ hd
  split at h <;> try cases h
  rename_i c a b hcab
  have hok := (ExprOK.iteView_iff hS hcab).1 (hs y d hd)
  split at h <;> try cases h
  split at h <;> cases h
  · exact hok.2.1
  · exact hok.2.2

omit [LawfulBEq P.Ident] in
/-- **The replacement of a variable passes the checks** when the scope does. -/
theorem look_ok [LawfulHasFvars P] (hS : GuardFwdSynLaws P) (hP : GuardPropSynLaws P)
    {dv df : P.Ident → Bool} {Γ : VarTyping P} {sc : Scope P} (hs : ScopeOK dv df Γ sc)
    (K : Guards P) :
    ∀ (n : Nat) (y : P.Ident) (r : P.Expr), look sc K n y = some r → ExprOK dv df Γ r
  | n, y, r, h => by
    unfold look at h
    split at h
    · rename_i b _
      cases h
      cases b
      · refine ⟨fun z hz => by simp [boolE, WPLang.getFvars_ff] at hz, fun x ty hx => ?_,
          fun o ho => by simp [boolE, hP.ops_ff] at ho⟩
        have hx' := LawfulHasFvars.mem_getFvars_of_typed _ x ty hx
        simp [boolE, WPLang.getFvars_ff] at hx'
      · exact ⟨fun z hz => by simp [boolE, WPLang.getFvars_tt] at hz,
          fun x ty hx => by simp [boolE, hS.typed_tt] at hx,
          fun o ho => by simp [boolE, hS.ops_tt] at ho⟩
    split at h <;> try cases h
    rename_i r0 hr0
    have h0 : ExprOK dv df Γ r0 := cand_ok hS hs (Option.filter_eq_some_iff.1 hr0).1
    split at h
    · rename_i n z _
      cases h
      cases hl : look sc K n z with
      | none => exact h0
      | some r' => exact look_ok hS hP hs K n z r' hl
    · exact Option.some.inj h ▸ h0

omit [LawfulBEq P.Ident] [BEq P.Ident] [Hashable P.Ident] [GuardOps P] in
/-- A substitution whose images pass the checks passes them when its input does. -/
private theorem substFn_ok (hP : GuardPropSynLaws P) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {lk : P.Ident → Option P.Expr} (hlook : ∀ {k r}, lk k = some r → ExprOK dv df Γ r)
    (e : P.Expr) (he : ExprOK dv df Γ e) : ExprOK dv df Γ (WPOps.substFn e lk) := by
  let sm := (HasFvars.getFvars e).filterMap fun y => (lk y).map (y, ·)
  have hfind : ∀ x ∈ HasFvars.getFvars e, lk x = Map.find? sm x :=
    fun x hx => (find?_filterMap lk _ x (.inl hx)).symm
  refine ⟨fun z hz => ?_, fun x ty hx => ?_, fun o ho => ?_⟩
  · rw [WPLang.substFn_eq e lk sm hfind] at hz
    rcases WPLang.getFvars_substFvars e sm z hz with ⟨hz, -⟩ | ⟨x, v, hx, hv, hz⟩
    · exact he.1 z hz
    · exact (hlook ((hfind x hx).trans hv)).1 z hz
  · rcases WPLang.getTypedFvars_substFn e lk (x, ty) hx with ⟨hx, -⟩ | ⟨z, v, -, hv, hx⟩
    · exact he.2.1 x ty hx
    · exact (hlook hv).2.1 x ty hx
  · rcases hP.ops_substFn_mem e lk o ho with ho | ⟨x, r, hr, ho⟩
    · exact he.2.2 o ho
    · exact (hlook hr).2.2 o ho

omit [LawfulBEq P.Ident] in
/-- **The contextual simplification passes the checks** when its input and the recorded
    right-hand sides do. -/
theorem rwG_ok [LawfulHasFvars P] (hS : GuardFwdSynLaws P) (hP : GuardPropSynLaws P)
    {dv df : P.Ident → Bool}
    {Γ : VarTyping P} {sc : Scope P} (hs : ScopeOK dv df Γ sc) (fuel : Nat) (K : Guards P)
    (e : P.Expr) : ExprOK dv df Γ e → ExprOK dv df Γ (rwG sc fuel K e) := by
  fun_induction rwG sc fuel K e with
  | case1 K e c t f hv c' g hg ihc iht ihf | case2 K e c t f hv c' hg ihc iht ihf =>
    intro he
    have hp := (ExprOK.iteView_iff hS hv).1 he
    exact (ExprOK.ite_iff hS).2 ⟨ihc hp.1, iht hp.2.1, ihf hp.2.2⟩
  | case3 K e hv =>
    exact substFn_ok hP (fun h => look_ok hS hP hs K fuel _ _ h) e

omit [HasBool P] [HasSubstFvar P] [WPLang P] [GuardOps P] in
/-- The checks of the recorded right-hand sides after an `init`: the defined names and the
    typing grow by the variable, which the position before does not define. -/
private theorem scopeOK_insert [LawfulHasFvars P] {dv dv' df : P.Ident → Bool}
    {Γ : VarTyping P} {sc : Scope P} (hs : ScopeOK dv df Γ sc) {x : P.Ident} {ty : P.Ty}
    {val : Option P.Expr} (hx : dv x = false) (hv : ∀ d, val = some d → ExprOK dv df Γ d)
    (hd : ∀ z, dv z = true → dv' z = true) :
    ScopeOK dv' df (Γ.extend [(x, ty)]) (sc.insert x val) := by
  have hΓ : ∀ z, dv z = true → Γ.extend [(x, ty)] z = Γ z := fun z hz => by
    have hxz : z ≠ x := fun h => Bool.false_ne_true (hx.symm.trans (h ▸ hz))
    simp [VarTyping.extend_singleton, hxz]
  intro y d hy
  simp only [Std.HashMap.getElem?_insert] at hy
  split at hy
  · exact (hv d (Option.some.inj hy)).mono hd hΓ
  · exact (hs y d hy).mono hd hΓ

/-- **The output passes the def-use and annotation checks** of the gate wherever the input does,
    when the recorded right-hand sides of the scope pass the checks. -/
theorem walk_gate [LawfulHasFvars P] (hS : GuardFwdSynLaws P) (hP : GuardPropSynLaws P)
    (ini : Std.HashSet P.Ident)
    (df : P.Ident → Bool) (ss : PStmts P) (hp : Block.passiveForm ss = true) :
    ∀ (st : PSt P) (dv : P.Ident → Bool) (Γ : VarTyping P),
    Block.defUseWellFormed dv df ss = true → Block.fvarTypesWellAnnotated Γ ss →
    ScopeOK dv df Γ st.scope →
    Block.defUseWellFormed dv df (walk ini st ss).1 = true ∧
      Block.fvarTypesWellAnnotated Γ (walk ini st ss).1 := by
  induction ss using Block.passiveForm.induct <;> intro st dv Γ hd hf hs <;>
    (try cases ‹ExprOrNondet P›) <;>
    simp only [Block.passiveForm, walk, walkS, Block.defUseWellFormed, Stmt.defUseWellFormed,
      Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated, HasVarsImp.readVars,
      CmdExt.readVars, ExprOrNondet.getVars, HasVarsImp.modifiedVars, CmdExt.modifiedVars,
      Cmd.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
      HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps, ExprOrNondet.getOps, Stmt.definedVars,
      HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Stmt.typedDefinedVars,
      HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars, Bool.and_eq_true, List.all_eq_true,
      List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq, and_self, Bool.false_eq_true]
      at hp hd hf ⊢
  case case2.det x ty md rest ih e =>
    obtain ⟨⟨⟨hfv, hx⟩, hops⟩, hrest⟩ := hd
    refine (ih hp _ _ _ hrest hf.2 ?_).imp (⟨⟨⟨hfv, hx⟩, hops⟩, ·⟩) (⟨hf.1, ·⟩)
    refine scopeOK_insert hs (Bool.eq_false_iff.2 hx) (fun d h => ?_) fun z hz => by simp [hz]
    split at h <;> cases h
    exact ⟨hfv, hf.1, hops⟩
  case case2.nondet x ty md rest ih =>
    refine (ih hp _ _ _ hd.2 hf.2 ?_).imp (⟨hd.1, ·⟩) (⟨hf.1, ·⟩)
    exact scopeOK_insert hs (Bool.eq_false_iff.2 hd.1.2) (fun _ h => by cases h)
      fun z hz => by simp [hz]
  case case3 l e md rest ih | case4 l e md rest ih | case5 l e md rest ih =>
    obtain ⟨⟨hfv, hops⟩, hrest⟩ := hd
    have he' := rwG_ok hS hP hs st.scope.size st.facts e ⟨hfv, hf.1, hops⟩
    refine (ih hp _ _ _ hrest hf.2 ?_).imp (⟨⟨he'.1, he'.2.2⟩, ·⟩) (⟨he'.2.1, ·⟩)
    exact hs.mono (fun z hz => by simp [hz]) fun _ _ => rfl
  case case6 t e md rest iht ihe ihr =>
    obtain ⟨⟨hpt, hpe⟩, hpr⟩ := hp
    obtain ⟨⟨⟨-, hdt⟩, hde⟩, hdr⟩ := hd
    obtain ⟨⟨-, hft, hfe⟩, hfr⟩ := hf
    obtain ⟨ht1, ht2⟩ := iht hpt st dv Γ hdt hft hs
    obtain ⟨he1, he2⟩ := ihe hpe st dv Γ hde hfe hs
    obtain ⟨hr1, hr2⟩ := ihr hpr st _ _ hdr hfr (hs.mono (fun z hz => by simp [hz]) fun _ _ => rfl)
    exact ⟨⟨⟨⟨trivial, ht1⟩, he1⟩, hr1⟩, ⟨nofun, ht2, he2⟩, hr2⟩

end Gate

end -- public section

end GuardProp
end Imperative
