/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SSA.SSAProps
public import Strata.Transform.Passive.Typed
public import Strata.Transform.Passive.WellTypedProps
import Strata.DL.Imperative.CmdSemanticsProps

/-! # The SSA phase keeps right-hand sides typed

When the right-hand sides of a guarded program have the types of their variables
(`Block.rhsTyped`, under a typing `Γ` its annotations agree with) and the types `tys` the phase
reads for the free variables are those of `Γ`, every `init` of the obligation program the SSA
phase produces has a right-hand side of its declared type (`ssaEntry_initsTyped`).  The phase
replaces each name by its current value: a variable annotated with the type of the name, or a
literal or function value of that type; under the laws `TypedOpLaws`, folding keeps the type.

Key theorems: `ssaEntry_initsTyped`, `ssaEntry_condsTyped`, `ssaEntry_initsTyped_renamed`,
`ssaEntry_condsTyped_renamed`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLId : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P] [iW : WPLang P]
  [iLFvs : LawfulHasFvars P] {Typ : P.Expr → P.Ty → Prop} {oe : WPOps.OpEnv P}

/-- The value `v` of a name of type `T` has that type: a variable annotated with `T`, or a
    literal or function value of type `T` (under the typing predicate `Typ`). -/
@[expose] def SValTyped (Typ : P.Expr → P.Ty → Prop) (T : P.Ty) : SVal P → Prop
  | .name _ ty => ty = some T
  | .lit e ty _ => ty = T ∧ Typ e T

omit iLB iHI iLId iLFvs in
/-- Renaming the names of an expression of type `ty` to their current values (`renM`) keeps the
    type, under `TypedOpLaws`, when the current value of the variable of each annotated
    free-variable occurrence has the annotated type. -/
private theorem renM_typed (hL : TypedOpLaws Typ oe) (ρ : Std.HashMap P.Ident (SVal P))
    (e : P.Expr) {ty : P.Ty} (he : Typ e ty)
    (hA : ∀ p ∈ HasFvars.getTypedFvars e, ∀ v, ρ[p.1]? = some v → SValTyped Typ p.2 v) :
    Typ (renM ρ e) ty := hL.substFn _ he fun p hp w hw => by
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 hw
  have ht := hA p hp _ hv
  cases v with
  | name y yty => exact (show yty = some p.2 from ht) ▸ hL.var y he hp
  | lit e' ty' m =>
    obtain ⟨rfl, ht⟩ := ht
    cases m <;> simp only [substVal, SVal.expr] <;> (try split) <;>
      first | exact ht | exact hL.var _ he hp

omit iLB iHI iLId iLFvs in
/-- **Folding keeps the type.**  Under `TypedOpLaws`, the fold of an expression of type `ty` has
    type `ty` when the current value of the variable of each annotated free-variable occurrence
    has the annotated type. -/
private theorem foldE_typed (hL : TypedOpLaws Typ oe) (ρ : Std.HashMap P.Ident (SVal P))
    (e : P.Expr) :
    ∀ {ty}, Typ e ty →
    (∀ p ∈ HasFvars.getTypedFvars e, ∀ v, ρ[p.1]? = some v → SValTyped Typ p.2 v) →
    Typ (foldE oe ρ e) ty := by
  have parts : ∀ {e c t f : P.Expr}, WPOps.iteView? e = some (c, t, f) →
      (∀ p ∈ HasFvars.getTypedFvars e, ∀ v, ρ[p.1]? = some v → SValTyped Typ p.2 v) →
      (∀ p ∈ HasFvars.getTypedFvars c, ∀ v, ρ[p.1]? = some v → SValTyped Typ p.2 v) ∧
      (∀ p ∈ HasFvars.getTypedFvars t, ∀ v, ρ[p.1]? = some v → SValTyped Typ p.2 v) ∧
      (∀ p ∈ HasFvars.getTypedFvars f, ∀ v, ρ[p.1]? = some v → SValTyped Typ p.2 v) :=
    fun hv hA => by
      have m := fun {p} h => hA p ((WPLang.typedFvars_iteView p hv).2 (hL.typedFvars_ite h))
      exact ⟨fun _ hp => m (.inl hp), fun _ hp => m (.inr (.inl hp)),
        fun _ hp => m (.inr (.inr hp))⟩
  fun_induction foldE oe ρ e
  case case1 e c t f hv c' hb ih2 ih1 | case2 e c t f hv c' hb ih2 ih1 =>
    intro ty he hA
    obtain ⟨-, ht, hf⟩ := (hL.iteView hv).1 he
    first | exact ih1 ht (parts hv hA).2.1 | exact ih1 hf (parts hv hA).2.2
  case case3 e c t f hv c' hb t' f' hs ih3 ih2 ih1 =>
    intro ty he hA
    exact ih2 ((hL.iteView hv).1 he).2.1 (parts hv hA).2.1
  case case4 e c t f hv c' hb t' f' hs ih3 ih2 ih1 =>
    intro ty he hA
    obtain ⟨hc, ht, hf⟩ := (hL.iteView hv).1 he
    obtain ⟨Ac, At, Af⟩ := parts hv hA
    exact hL.ite.2 ⟨ih3 hc Ac, ih2 ht At, ih1 hf Af⟩
  case case5 e hv =>
    intro ty he hA
    have hr := renM_typed hL ρ e he hA
    simp only [evalM]
    cases ho : WPOps.evalOp? oe (renM ρ e) <;> first | exact hr | exact hL.evalOp ho hr

omit iHB iHF iSF iHI iLId iHFs iW iLFvs in
/-- Binding `x` to a value of the type `ty` keeps the current values of the names of `V` of the
    types `Γ` extended with `(x, ty)` gives them, when the names of `V` other than `x` had them. -/
private theorem SValTyped.assign {Γ : VarTyping P} {V : List P.Ident} {x : P.Ident} {ty : P.Ty}
    {v : SVal P} {ρ : Std.HashMap P.Ident (SVal P)} (hv : SValTyped Typ ty v)
    (hold : ∀ z ∈ V, z ≠ x → ∀ T, Γ z = some T → ∀ w, ρ[z]? = some w → SValTyped Typ T w)
    (d : List (P.Ident × P.Ty)) (hd : ∀ z, z ≠ x → Γ.extend d z = Γ z)
    (hx : ∀ T, Γ.extend d x = some T → T = ty) :
    ∀ z ∈ V, ∀ T, Γ.extend d z = some T → ∀ w, (ρ.insert x v)[z]? = some w →
      SValTyped Typ T w := fun z hz T hT w hw => by
  by_cases h : x = z
  · subst h
    obtain rfl := hx T hT
    exact Option.some.inj (Std.HashMap.getElem?_insert_self.symm.trans hw) ▸ hv
  · exact hold z hz (Ne.symm h) T (hd z (Ne.symm h) ▸ hT) w
      (by simpa [Std.HashMap.getElem?_insert, h] using hw)

/-- **The traversal keeps right-hand sides typed.**  Under `TypedOpLaws`, from a state whose
    current value of every free variable of the list has the type `Γ` gives the variable, the
    output of a list whose annotations agree with `Γ` and whose right-hand sides have the types
    of their variables under `Γ` has every `init` of its declared type. -/
private theorem ssaList_initsTyped (hL : TypedOpLaws Typ oe) (ss : PStmts P) :
    ∀ {s s' : SSt P} {out : PStmts P}, ssaList oe ss s = .ok (out, s') →
    ∀ {Γ : VarTyping P}, Block.fvarTypesWellAnnotated Γ ss → Block.rhsTyped Typ Γ ss →
    (∀ x ∈ Block.freeVars ss, ∀ T, Γ x = some T → ∀ v, s.ρ[x]? = some v → SValTyped Typ T v) →
    Block.initsTyped Typ out := by
  intro s s' out h
  have hav : ∀ {x ty e s o v s1} {Γ : VarTyping P} {V : List P.Ident},
      assignVal oe x ty e s = .ok ((o, v), s1) → Typ e ty →
      Γ.annotates (HasFvars.getTypedFvars e) → (∀ x ∈ HasFvars.getFvars e, x ∈ V) →
      (∀ x ∈ V, ∀ T, Γ x = some T → ∀ v, s.ρ[x]? = some v → SValTyped Typ T v) →
      Block.initsTyped Typ o ∧ SValTyped Typ ty v := fun h1 he hW hV hA => by
    have hfe := foldE_typed hL _ _ he fun p hp =>
      hA p.1 (hV _ (LawfulHasFvars.mem_getFvars_of_typed _ _ _ hp)) p.2 (hW _ _ hp)
    rcases assignVal_ok h1 with ⟨_, -, -, rfl, rfl⟩ | ⟨_, -, -, rfl, rfl, -⟩ | ⟨_, -, rfl, rfl⟩
    · exact ⟨⟨hfe, trivial⟩, rfl, hfe⟩
    · exact ⟨trivial, rfl⟩
    · exact ⟨⟨hfe, trivial⟩, rfl⟩
  refine no_implicit_lambda% (ssaList_ind (fun _ _ _ _ _ => trivial)
    ?initDet ?initNondet ?setDet ?setNondet ?_ ?_ ?_ ?_ h)
  case' initDet =>
    intro x ty e _ rest s o v s1 out s' h1 ih Γ hW hR hA
    obtain ⟨ho, hv⟩ := hav h1 hR.1
      (fun z T hz => hW.1 z T (by simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
        Cmd.getTypedVars, ExprOrNondet.getTypedVars] using hz))
      (fun z hz => by simp [Block.freeVars, mem_exprFV, hz]) hA
    have hρ := (assignVal_facts h1).1
    refine (Block.initsTyped_append _ _).2 ⟨ho, ih hW.2 hR.2 ?_⟩
  case' initNondet =>
    intro x ty _ rest s x' s1 out s' h1 ih Γ hW hR hA
    obtain ⟨hv, hρ⟩ : SValTyped Typ ty (.name x' (some ty)) ∧ s1.ρ = s.ρ :=
      ⟨rfl, by obtain ⟨_, -, -, -, rfl⟩ := sFresh_ok h1; rfl⟩
    refine ⟨trivial, ih hW.2 hR.2 ?_⟩
  case initDet | initNondet =>
    exact SValTyped.assign hv (fun z hz hzx => hρ ▸ hA z (by simp [Block.freeVars, hz, hzx]))
      [(x, ty)] (fun z hzx => by simp [VarTyping.extend_singleton, hzx])
      fun T hT => by simpa [VarTyping.extend_singleton, eq_comm] using hT
  case' setDet => intro x e _ rest s ty o v s1 out s' hT h1 ih Γ hW hR hA
  case' setNondet => intro x _ rest s ty x' s1 out s' hT h1 ih Γ hW hR hA
  case' setDet | setNondet =>
    have hxT : ∀ T, Γ x = some T → T = ty := fun T hT' => by
      have hc := (curTy_ok hT).2
      rcases hw : s.ρ[x]? with _ | (_ | _) <;>
        simp only [hw, Option.getD, SVal.ty?, reduceCtorEq] at hc
      all_goals have hS := hA x (by simp [Block.freeVars, Stmt.freeVars]) T hT' _ hw
      · exact Option.some.inj (hS.symm.trans hc)
      · exact hS.1.symm.trans (Option.some.inj hc)
    have hold : ∀ z ∈ Block.freeVars rest, z ≠ x → ∀ T, Γ z = some T → ∀ w, s.ρ[z]? = some w →
        SValTyped Typ T w := fun z hz _ => hA z (by simp [Block.freeVars, Stmt.freeVars, hz])
  case setDet =>
    obtain ⟨T, hΓ, hRe⟩ := hR.1
    obtain rfl := hxT T hΓ
    obtain ⟨ho, hv⟩ := hav h1 hRe
      (fun z T hz => hW.1 z T (by simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
        Cmd.getTypedVars, ExprOrNondet.getTypedVars] using hz))
      (fun z hz => by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hz]) hA
    exact (Block.initsTyped_append _ _).2 ⟨ho, ih hW.2 hR.2 (SValTyped.assign hv
      (fun z hz hzx => (assignVal_facts h1).1 ▸ hold z hz hzx) [] (fun _ _ => rfl) hxT)⟩
  case setNondet =>
    obtain ⟨_, -, -, -, rfl⟩ := sFresh_ok h1
    exact ⟨trivial, ih hW.2 hR.2 (SValTyped.assign (v := .name x' (some ty)) rfl hold []
      (fun _ _ => rfl) hxT)⟩
  · intro l a md rest s out s' ih Γ hW hR hA
    have hr := ih hW.2 hR.2 fun z hz => hA z (by simp [Block.freeVars, Stmt.freeVars, hz])
    split <;> first | exact hr | exact ⟨trivial, hr⟩
  · intro mk b l e md rest s out s' hmk _ ih Γ hW hR hA
    rcases hmk with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      exact ⟨trivial, ih hW.2 hR.2 fun z hz => hA z (by simp [Block.freeVars, Stmt.freeVars, hz])⟩
  · intro tss ess md s t sT sU e out s' hT ihT hU _ ihE h1 h2 h3 Γ hW hR hA
    have hρ := (undoTo_frame (ssaList_frame _ hT) hU).2
    have rT := ihT hW.1.2.1 hR.1.2.1 fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy])
    have rE := ihE hW.1.2.2 hR.1.2.2 fun y hy T hT w hw => hA y
      (by simp [Block.freeVars, Stmt.freeVars, hy]) T hT w (hρ y ▸ hw)
    exact if ht : t = [] then h1 ht ▸ rE else if he : e = [] then h2 ht he ▸ rT
      else h3 ht he ▸ ⟨⟨rT, rE⟩, trivial⟩
  · intro tc md rest s out s' ih Γ hW hR hA
    exact ih hW.2 hR.2 fun z hz => hA z (by simp [Block.freeVars, Stmt.freeVars, hz])

omit iHI iLId iLFvs in
/-- **The condition of an obligation keeps the type.**  Under `TypedOpLaws`, the condition
    `oblCond` emits for an expression of type `ty` has type `ty` when the current value of the
    variable of each annotated free-variable occurrence has the annotated type. -/
private theorem oblCond_typed (hL : TypedOpLaws Typ oe) (b : Bool)
    (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) {ty : P.Ty} (he : Typ e ty)
    (hA : ∀ p ∈ HasFvars.getTypedFvars e, ∀ v, ρ[p.1]? = some v → SValTyped Typ p.2 v) :
    Typ (oblCond oe b ρ e) ty := by
  have hr := renM_typed hL ρ e he hA
  simp only [oblCond, evalM]
  rcases Bool.eq_false_or_eq_true ((exprFV e).any (litValued ρ) &&
      WPOps.boolLit? ((WPOps.evalOp? oe (renM ρ e)).getD (renM ρ e)) == some b) with hc | hc <;>
    simp only [hc, ↓reduceIte, Bool.false_eq_true]
  · cases ho : WPOps.evalOp? oe (renM ρ e) <;> first | exact hr | exact hL.evalOp ho hr
  · refine hL.substFn _ he fun p hp w hw => ?_
    obtain ⟨⟨y, yty⟩, hy, rfl⟩ := Option.map_eq_some_iff.1 hw
    simp only [oblVar] at hy
    split at hy
    · rename_i hv
      split at hy
      · cases hy
      · cases hy
        exact (show yty = some p.2 from hA p hp _ hv) ▸ hL.var y he hp
    · rename_i hv
      cases hy
      exact (hA p hp _ hv).1 ▸ hL.var y he hp
    · cases hy

/-- **The traversal keeps conditions typed.**  Under `TypedOpLaws`, from a state whose current
    value of every free variable of the list has the type `Γ` gives the variable, the output of a
    list whose annotations agree with `Γ`, whose right-hand sides have the types of their
    variables under `Γ` and whose `assume`, `assert` and `cover` conditions are Boolean has
    Boolean `assume`, `assert` and `cover` conditions. -/
private theorem ssaList_condsTyped (hL : TypedOpLaws Typ oe) (ss : PStmts P) :
    ∀ {s s' : SSt P} {out : PStmts P}, ssaList oe ss s = .ok (out, s') →
    ∀ {Γ : VarTyping P}, Block.fvarTypesWellAnnotated Γ ss → Block.rhsTyped Typ Γ ss →
    Block.condsTyped Typ ss →
    (∀ x ∈ Block.freeVars ss, ∀ T, Γ x = some T → ∀ v, s.ρ[x]? = some v → SValTyped Typ T v) →
    Block.condsTyped Typ out := by
  intro s s' out h
  have hav : ∀ {x ty e s o v s1} {Γ : VarTyping P} {V : List P.Ident},
      assignVal oe x ty e s = .ok ((o, v), s1) → Typ e ty →
      Γ.annotates (HasFvars.getTypedFvars e) → (∀ x ∈ HasFvars.getFvars e, x ∈ V) →
      (∀ x ∈ V, ∀ T, Γ x = some T → ∀ v, s.ρ[x]? = some v → SValTyped Typ T v) →
      Block.condsTyped Typ o ∧ SValTyped Typ ty v := fun h1 he hW hV hA => by
    have hfe := foldE_typed hL _ _ he fun p hp =>
      hA p.1 (hV _ (LawfulHasFvars.mem_getFvars_of_typed _ _ _ hp)) p.2 (hW _ _ hp)
    rcases assignVal_ok h1 with ⟨_, -, -, rfl, rfl⟩ | ⟨_, -, -, rfl, rfl, -⟩ | ⟨_, -, rfl, rfl⟩
    · exact ⟨⟨trivial, trivial⟩, rfl, hfe⟩
    · exact ⟨trivial, rfl⟩
    · exact ⟨⟨trivial, trivial⟩, rfl⟩
  refine no_implicit_lambda% (ssaList_ind (fun _ _ _ _ _ _ => trivial)
    ?initDet ?initNondet ?setDet ?setNondet ?_ ?_ ?_ ?_ h)
  case' initDet =>
    intro x ty e _ rest s o v s1 out s' h1 ih Γ hW hR hC hA
    obtain ⟨ho, hv⟩ := hav h1 hR.1
      (fun z T hz => hW.1 z T (by simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
        Cmd.getTypedVars, ExprOrNondet.getTypedVars] using hz))
      (fun z hz => by simp [Block.freeVars, mem_exprFV, hz]) hA
    have hρ := (assignVal_facts h1).1
    refine (Block.condsTyped_append _ _).2 ⟨ho, ih hW.2 hR.2 hC.2 ?_⟩
  case' initNondet =>
    intro x ty _ rest s x' s1 out s' h1 ih Γ hW hR hC hA
    obtain ⟨hv, hρ⟩ : SValTyped Typ ty (.name x' (some ty)) ∧ s1.ρ = s.ρ :=
      ⟨rfl, by obtain ⟨_, -, -, -, rfl⟩ := sFresh_ok h1; rfl⟩
    refine ⟨trivial, ih hW.2 hR.2 hC.2 ?_⟩
  case initDet | initNondet =>
    exact SValTyped.assign hv (fun z hz hzx => hρ ▸ hA z (by simp [Block.freeVars, hz, hzx]))
      [(x, ty)] (fun z hzx => by simp [VarTyping.extend_singleton, hzx])
      fun T hT => by simpa [VarTyping.extend_singleton, eq_comm] using hT
  case' setDet => intro x e _ rest s ty o v s1 out s' hT h1 ih Γ hW hR hC hA
  case' setNondet => intro x _ rest s ty x' s1 out s' hT h1 ih Γ hW hR hC hA
  case' setDet | setNondet =>
    have hxT : ∀ T, Γ x = some T → T = ty := fun T hT' => by
      have hc := (curTy_ok hT).2
      rcases hw : s.ρ[x]? with _ | (_ | _) <;>
        simp only [hw, Option.getD, SVal.ty?, reduceCtorEq] at hc
      all_goals have hS := hA x (by simp [Block.freeVars, Stmt.freeVars]) T hT' _ hw
      · exact Option.some.inj (hS.symm.trans hc)
      · exact hS.1.symm.trans (Option.some.inj hc)
    have hold : ∀ z ∈ Block.freeVars rest, z ≠ x → ∀ T, Γ z = some T → ∀ w, s.ρ[z]? = some w →
        SValTyped Typ T w := fun z hz _ => hA z (by simp [Block.freeVars, Stmt.freeVars, hz])
  case setDet =>
    obtain ⟨T, hΓ, hRe⟩ := hR.1
    obtain rfl := hxT T hΓ
    obtain ⟨ho, hv⟩ := hav h1 hRe
      (fun z T hz => hW.1 z T (by simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
        Cmd.getTypedVars, ExprOrNondet.getTypedVars] using hz))
      (fun z hz => by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hz]) hA
    exact (Block.condsTyped_append _ _).2 ⟨ho, ih hW.2 hR.2 hC.2 (SValTyped.assign hv
      (fun z hz hzx => (assignVal_facts h1).1 ▸ hold z hz hzx) [] (fun _ _ => rfl) hxT)⟩
  case setNondet =>
    obtain ⟨_, -, -, -, rfl⟩ := sFresh_ok h1
    exact ⟨trivial, ih hW.2 hR.2 hC.2 (SValTyped.assign (v := .name x' (some ty)) rfl hold []
      (fun _ _ => rfl) hxT)⟩
  · intro l a md rest s out s' ih Γ hW hR hC hA
    have hr := ih hW.2 hR.2 hC.2 fun z hz => hA z (by simp [Block.freeVars, Stmt.freeVars, hz])
    have ht := foldE_typed hL _ _ hC.1 fun p hp => hA p.1
      (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV,
        LawfulHasFvars.mem_getFvars_of_typed _ _ _ hp]) p.2
      (hW.1 _ _ (by simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
        Cmd.getTypedVars] using hp))
    split
    · exact hr
    · exact ⟨ht, hr⟩
  · intro mk b l e md rest s out s' hmk _ ih Γ hW hR hC hA
    rcases hmk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨oblCond_typed hL _ _ _ hC.1 fun p hp => hA p.1 (by
        simp [Block.freeVars, Stmt.freeVars, mem_exprFV,
          LawfulHasFvars.mem_getFvars_of_typed _ _ _ hp]) p.2 (hW.1 _ _ (by
        simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars] using hp)),
        ih hW.2 hR.2 hC.2 fun z hz => hA z (by simp [Block.freeVars, Stmt.freeVars, hz])⟩
  · intro tss ess md s t sT sU e out s' hT ihT hU _ ihE h1 h2 h3 Γ hW hR hC hA
    have hρ := (undoTo_frame (ssaList_frame _ hT) hU).2
    have rT := ihT hW.1.2.1 hR.1.2.1 hC.1.1 fun y hy =>
      hA y (by simp [Block.freeVars, Stmt.freeVars, hy])
    have rE := ihE hW.1.2.2 hR.1.2.2 hC.1.2 fun y hy T hT w hw => hA y
      (by simp [Block.freeVars, Stmt.freeVars, hy]) T hT w (hρ y ▸ hw)
    exact if ht : t = [] then h1 ht ▸ rE else if he : e = [] then h2 ht he ▸ rT
      else h3 ht he ▸ ⟨⟨rT, rE⟩, trivial⟩
  · intro tc md rest s out s' ih Γ hW hR hC hA
    exact ih hW.2 hR.2 hC.2 fun z hz => hA z (by simp [Block.freeVars, Stmt.freeVars, hz])

/-- **The SSA phase keeps right-hand sides typed, from the types of the renamed free
    variables.**  Under the typing laws `TypedOpLaws` of the typing predicate `Typ`, when the
    annotations of a guarded program `lay` agree with a typing `Γ`, its right-hand sides have the
    types of their variables under `Γ` (`Block.rhsTyped`), and the types `tys` records for the
    free variables the entry renaming `ρ0` renames are those `Γ` gives them, every `init` of the
    obligation program `ssaEntry` produces has a right-hand side of its declared type.  A free
    variable the entry renaming leaves alone is read with its own annotation. -/
theorem ssaEntry_initsTyped_renamed (hL : TypedOpLaws Typ oe) {G : IdSet P} {tys : Tys P}
    {xs : List P.Ident} {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P}
    {so : SOut P} (h : ssaEntry oe G tys xs al lay = .ok (ρ0, so)) {Γ : VarTyping P}
    (hW : Block.fvarTypesWellAnnotated Γ lay) (hR : Block.rhsTyped Typ Γ lay)
    (hty : ∀ x ∈ Block.freeVars lay, ∀ T, Γ x = some T → x ∈ ρ0.map (·.1) →
      tys.get? x = some T) :
    Block.initsTyped Typ so.out := by
  obtain ⟨-, hb⟩ := ssaEntry_ok h
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hb
  exact ssaList_initsTyped hL _ h1 hW hR fun x hx T hT v hv =>
    (Option.map_eq_some_iff.1 ((entryMap_lookup _ _ x).symm.trans hv)).elim fun p ⟨hp, he⟩ =>
      he ▸ hty x hx T hT (List.mem_map.2 ⟨p, List.mem_of_find?_eq_some hp,
        by simpa using List.find?_some hp⟩)

/-- **The SSA phase keeps right-hand sides typed.**  Under the typing laws `TypedOpLaws` of the
    typing predicate `Typ`, when the annotations of a guarded program `lay` agree with a typing
    `Γ`, its right-hand sides have the types of their variables under `Γ` (`Block.rhsTyped`),
    and the types `tys` records for its free variables are those `Γ` gives them, every `init`
    of the obligation program `ssaEntry` produces has a right-hand side of its declared type. -/
theorem ssaEntry_initsTyped (hL : TypedOpLaws Typ oe) {G : IdSet P} {tys : Tys P}
    {xs : List P.Ident} {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P}
    {so : SOut P} (h : ssaEntry oe G tys xs al lay = .ok (ρ0, so)) {Γ : VarTyping P}
    (hW : Block.fvarTypesWellAnnotated Γ lay) (hR : Block.rhsTyped Typ Γ lay)
    (hty : ∀ x ∈ Block.freeVars lay, ∀ T, Γ x = some T → tys.get? x = some T) :
    Block.initsTyped Typ so.out :=
  ssaEntry_initsTyped_renamed hL h hW hR fun x hx T hT _ => hty x hx T hT

/-- **The SSA phase keeps conditions typed, from the types of the renamed free variables.**
    Under the typing laws `TypedOpLaws` of the typing predicate `Typ`, when the annotations of a
    guarded program `lay` agree with a typing `Γ`, its right-hand sides have the types of their
    variables under `Γ` (`Block.rhsTyped`), its `assume`, `assert` and `cover` conditions are
    Boolean (`Block.condsTyped`), and the types `tys` records for the free variables the entry
    renaming `ρ0` renames are those `Γ` gives them, every `assume`, `assert` and `cover` condition
    of the obligation program `ssaEntry` produces is Boolean. -/
theorem ssaEntry_condsTyped_renamed (hL : TypedOpLaws Typ oe) {G : IdSet P} {tys : Tys P}
    {xs : List P.Ident} {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P}
    {so : SOut P} (h : ssaEntry oe G tys xs al lay = .ok (ρ0, so)) {Γ : VarTyping P}
    (hW : Block.fvarTypesWellAnnotated Γ lay) (hR : Block.rhsTyped Typ Γ lay)
    (hC : Block.condsTyped Typ lay)
    (hty : ∀ x ∈ Block.freeVars lay, ∀ T, Γ x = some T → x ∈ ρ0.map (·.1) →
      tys.get? x = some T) :
    Block.condsTyped Typ so.out := by
  obtain ⟨-, hb⟩ := ssaEntry_ok h
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hb
  exact ssaList_condsTyped hL _ h1 hW hR hC fun x hx T hT v hv =>
    (Option.map_eq_some_iff.1 ((entryMap_lookup _ _ x).symm.trans hv)).elim fun p ⟨hp, he⟩ =>
      he ▸ hty x hx T hT (List.mem_map.2 ⟨p, List.mem_of_find?_eq_some hp,
        by simpa using List.find?_some hp⟩)

/-- **The SSA phase keeps conditions typed.**  Under the typing laws `TypedOpLaws` of the typing
    predicate `Typ`, when the annotations of a guarded program `lay` agree with a typing `Γ`, its
    right-hand sides have the types of their variables under `Γ` (`Block.rhsTyped`), its
    `assume`, `assert` and `cover` conditions are Boolean (`Block.condsTyped`), and the types
    `tys` records for its free variables are those `Γ` gives them, every `assume`, `assert` and
    `cover` condition of the obligation program `ssaEntry` produces is Boolean. -/
theorem ssaEntry_condsTyped (hL : TypedOpLaws Typ oe) {G : IdSet P} {tys : Tys P}
    {xs : List P.Ident} {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P}
    {so : SOut P} (h : ssaEntry oe G tys xs al lay = .ok (ρ0, so)) {Γ : VarTyping P}
    (hW : Block.fvarTypesWellAnnotated Γ lay) (hR : Block.rhsTyped Typ Γ lay)
    (hC : Block.condsTyped Typ lay)
    (hty : ∀ x ∈ Block.freeVars lay, ∀ T, Γ x = some T → tys.get? x = some T) :
    Block.condsTyped Typ so.out :=
  ssaEntry_condsTyped_renamed hL h hW hR hC fun x hx T hT _ => hty x hx T hT

end -- public section

end WP
end Imperative
