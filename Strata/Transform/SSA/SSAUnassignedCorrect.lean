/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SSA.SSACoreCorrect
public import Strata.Transform.Passive.Typed
import Strata.Transform.Passive.CoreTyped
import all Strata.Transform.SSA.SSAProps
import all Strata.Transform.SSA.SSAOver
import all Strata.Transform.SSA.SSACoreProgramProps
import all Strata.Transform.SSA.SSACoreCorrect
import Strata.DL.Imperative.Logic.TraceRelationsProps
import Strata.DL.Imperative.BigStep.Adequacy
import Strata.Languages.Core.ProcedureProps
import all Strata.Languages.Core.Verifier
import all Strata.Transform.SSA.SSACoreProgram
import Strata.Languages.Core.InstExprTyping

/-! # The SSA phase on lists whose other free variables are unassigned

`ssa_overapproximatesTraces` asks every free variable of the guarded list to be a parameter or an
alias.  The free variables of an obligation unit, those of a lemma's obligation, are neither: the
entry renaming does not rename them, and, as the list never assigns or defines them, the phase
reads them under their own names.  This module states the trace over-approximation of the SSA
phase on a list each of whose free variables is a parameter, an alias, or neither assigned nor
defined in the list (`ssa_overapproximatesTraces_unassigned`).

The proofs follow those of `ssa_overapproximatesTraces`.  The output reads an unassigned free
variable with the annotations it has in the input, so the output's annotations agree with the
typing of the entry names extended by a typing of the input's free variables at the unassigned
ones (`ssaEntry_fvarTypesWellAnnotated_unassigned`).

Key theorems: `ssa_overapproximatesTraces_unassigned`,
`ssaEntry_fvarTypesWellAnnotated_unassigned`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLId : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P] [iW : WPLang P]
  [iLFvs : LawfulHasFvars P]
variable {ρ : Std.HashMap P.Ident (SVal P)} {oe : WPOps.OpEnv P}

/-! ## Annotations -/

/-- The current value `ρ[x]?` of the name `x` agrees with the typing `Γ` (`STyped`), or `x` is
    unmapped and one of the names `U` read under their own names. -/
@[expose] def SAnn (Γ : VarTyping P) (U : List P.Ident) (ρ : Std.HashMap P.Ident (SVal P))
    (x : P.Ident) : Prop :=
  (∃ v, ρ[x]? = some v ∧ STyped Γ x v) ∨ (ρ[x]? = none ∧ x ∈ U)

omit iLB iHI iLId in
/-- The annotations of `e` with every name replaced by its current value agree with `Γ`, when the
    current value of each mapped free variable of `e` does and `Γ` gives each annotated
    occurrence of an unmapped variable its annotation. -/
private theorem renM_typedU {Γ : VarTyping P} (e : P.Expr)
    (hA : ∀ x ∈ HasFvars.getFvars e, ∀ v, ρ[x]? = some v → STyped Γ x v)
    (hU : ∀ p ∈ HasFvars.getTypedFvars e, ρ[p.1]? = none → Γ p.1 = some p.2) :
    ∀ p ∈ HasFvars.getTypedFvars (renM ρ e), Γ p.1 = some p.2 := by
  intro p hp
  rcases WPLang.getTypedFvars_substFn e _ p hp with ⟨hp, hg⟩ | ⟨z, w, hz, hg, hw⟩
  · exact hU p hp (Option.map_eq_none_iff.1 hg)
  · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 hg
    have ht := hA z hz v hv
    cases v with
    | name y ty =>
      obtain ⟨h1, h2⟩ := typed_var hw
      exact h1 ▸ ht.2 _ h2
    | lit e' ty m =>
      obtain ⟨⟨y, rfl, hy⟩, ht⟩ := ht
      simp only [substVal] at hw
      split at hw
      · obtain ⟨h1, h2⟩ := typed_var hw
        exact h1 ▸ Option.some.inj h2 ▸ hy
      · exact ht p hw

omit iLB iHI iLId in
/-- The annotations of the folded `e` agree with `Γ` under the hypotheses of `renM_typedU`, when
    the annotated occurrences of the parts of a conditional are the conditional's (`hite`). -/
private theorem foldE_typedU {Γ : VarTyping P} (ρ : Std.HashMap P.Ident (SVal P))
    (hite : ∀ {c t f : P.Expr} {p : P.Ident × P.Ty}, (p ∈ HasFvars.getTypedFvars c ∨
      p ∈ HasFvars.getTypedFvars t ∨ p ∈ HasFvars.getTypedFvars f) →
      p ∈ HasFvars.getTypedFvars (WPOps.ite c t f)) (e : P.Expr) :
    (∀ x ∈ HasFvars.getFvars e, ∀ v, ρ[x]? = some v → STyped Γ x v) →
    (∀ p ∈ HasFvars.getTypedFvars e, ρ[p.1]? = none → Γ p.1 = some p.2) →
      ∀ p ∈ HasFvars.getTypedFvars (foldE oe ρ e), Γ p.1 = some p.2 := by
  have parts : ∀ {e c t f : P.Expr}, WPOps.iteView? e = some (c, t, f) →
      (∀ x ∈ HasFvars.getFvars e, ∀ v, ρ[x]? = some v → STyped Γ x v) →
      (∀ p ∈ HasFvars.getTypedFvars e, ρ[p.1]? = none → Γ p.1 = some p.2) →
      ∀ g ∈ [c, t, f], (∀ x ∈ HasFvars.getFvars g, ∀ v, ρ[x]? = some v → STyped Γ x v) ∧
        (∀ p ∈ HasFvars.getTypedFvars g, ρ[p.1]? = none → Γ p.1 = some p.2) := by
    intro e c t f hv hA hU g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    refine ⟨fun x hx => hA x ((WPLang.iteView?_getFvars x hv).2
      ((WPLang.getFvars_ite _ _ _ x).2 ?_)), fun p hp => hU p ((WPLang.typedFvars_iteView p hv).2
      (hite ?_))⟩ <;> rcases hg with rfl | rfl | rfl <;>
      first | exact .inl ‹_› | exact .inr (.inl ‹_›) | exact .inr (.inr ‹_›)
  fun_induction foldE oe ρ e
  case case1 e c t f hv c' hb ih2 ih1 | case2 e c t f hv c' hb ih2 ih1 =>
    intro hA hU
    have ht := parts hv hA hU t (by simp)
    have hf := parts hv hA hU f (by simp)
    first | exact ih1 ht.1 ht.2 | exact ih1 hf.1 hf.2 | exact ih2 ht.1 ht.2 | exact ih2 hf.1 hf.2
  case case3 e c t f hv c' hb t' f' hs ih3 ih2 ih1 =>
    intro hA hU
    exact ih2 (parts hv hA hU t (by simp)).1 (parts hv hA hU t (by simp)).2
  case case4 e c t f hv c' hb t' f' hs ih3 ih2 ih1 =>
    intro hA hU p hp
    have hc := parts hv hA hU c (by simp)
    have ht := parts hv hA hU t (by simp)
    have hf := parts hv hA hU f (by simp)
    rcases WPLang.getTypedFvars_ite _ _ _ p hp with hp | hp | hp
    · exact ih3 hc.1 hc.2 p hp
    · exact ih2 ht.1 ht.2 p hp
    · exact ih1 hf.1 hf.2 p hp
  case case5 e hv =>
    exact fun hA hU p hp => renM_typedU e hA hU p (evalM_sub _ WPLang.getTypedFvars_evalOp? hp)

omit iHI iLId in
/-- The annotations of an emitted obligation condition agree with `Γ` under the hypotheses of
    `renM_typedU`. -/
private theorem renM'_typedU {Γ : VarTyping P} (e : P.Expr)
    (hA : ∀ x ∈ HasFvars.getFvars e, ∀ v, ρ[x]? = some v → STyped Γ x v)
    (hU : ∀ p ∈ HasFvars.getTypedFvars e, ρ[p.1]? = none → Γ p.1 = some p.2) :
    ∀ p ∈ HasFvars.getTypedFvars (renM' ρ e), Γ p.1 = some p.2 := by
  intro p hp
  rcases WPLang.getTypedFvars_substFn e _ p hp with ⟨hp, hg⟩ | ⟨z, w, hz, hg, hw⟩
  · rcases hv : ρ[p.1]? with _ | v
    · exact hU p hp hv
    have ht := hA p.1 (LawfulHasFvars.mem_getFvars_of_typed _ _ _ hp) v hv
    cases v with
    | name y ty => simp [oblVar, hv, ht.1] at hg
    | lit e' ty m =>
      obtain ⟨⟨y, rfl, -⟩, -⟩ := ht
      simp [oblVar, hv] at hg
  · rcases hv : ρ[z]? with _ | v
    · simp [oblVar, hv] at hg
    have ht := hA z hz v hv
    cases v with
    | name y ty =>
      simp only [oblVar, hv, beq_iff_eq, ht.1, ite_false, Option.map_some,
        Option.some.injEq] at hg
      subst hg
      obtain ⟨h1, h2⟩ := typed_var hw
      exact h1 ▸ ht.2 _ h2
    | lit e' ty m =>
      obtain ⟨⟨y, rfl, hy⟩, -⟩ := ht
      simp only [oblVar, hv, Option.map_some, Option.some.injEq] at hg
      subst hg
      obtain ⟨h1, h2⟩ := typed_var hw
      rw [h1, ← Option.some.inj h2]
      exact hy

omit iHB iHF iSF iHI iW iLFvs in
/-- `SAnn` on the names of `V` after binding `x`: on `x` from the new value, on the other names
    of `V` from before. -/
private theorem SAnn.assign {Γ : VarTyping P} {U V : List P.Ident} {x : P.Ident} {v : SVal P}
    (hx : STyped Γ x v) (hold : ∀ y ∈ V, y ≠ x → SAnn Γ U ρ y) :
    ∀ y ∈ V, SAnn Γ U (ρ.insert x v) y := fun y hy => by
  by_cases h : x = y
  · subst h
    exact .inl ⟨v, by simp, hx⟩
  · simpa only [SAnn, Std.HashMap.getElem?_insert, beq_iff_eq, h, ite_false] using
      hold y hy (Ne.symm h)

omit iDE iLB iHB iHF iSF iHI iW iLFvs in
/-- `SAnn` survives extending the typing at a name outside the names `Dd ++ U` it types. -/
private theorem SAnn.extend {Γ : VarTyping P} {Dd U : List P.Ident} {x' : P.Ident} {T : P.Ty}
    (hΓ : ∀ y, (Γ y).isSome → y ∈ Dd ∨ y ∈ U) (hx' : x' ∉ Dd ++ U) {z : P.Ident}
    (h : SAnn Γ U ρ z) : SAnn (Γ.extend [(x', T)]) U ρ z :=
  h.imp_left fun ⟨w, hw, ht⟩ => ⟨w, hw, STyped.extend (Dd := Dd ++ U)
    (fun y hy => List.mem_append.2 (hΓ y hy)) hx' ht⟩

omit iDE iBE iLB iHB iHF iSF iHI iLId iHa iHFs iW iLFvs in
/-- A typing `Γ'` agreeing with `Γ` on the names of `U` gives each of them the type a typing `Γs`
    extended outside `U` gives it, when `Γ` gives each the type `Γs` gives it. -/
private theorem ext_agree {Γ Γ' Γs : VarTyping P} {U : List P.Ident} {d : List (P.Ident × P.Ty)}
    (hc : ∀ u ∈ U, ∀ T, Γs u = some T → Γ u = some T) (hd : ∀ u ∈ U, u ∉ d.map Prod.fst)
    (hΓ' : ∀ u ∈ U, Γ' u = Γ u) : ∀ u ∈ U, ∀ T, Γs.extend d u = some T → Γ' u = some T :=
  fun u hu T hT =>
    (hΓ' u hu).trans (hc u hu T ((VarTyping.extend_of_not_mem (hd u hu)).symm.trans hT))

omit iDE iBE iLB iHB iSF iHI iLId iHa iW iLFvs in
/-- A name the list `s :: rest` neither assigns nor defines, `rest` neither assigns nor
    defines. -/
private theorem not_mem_modOrDef_tail {s : Stmt P (CmdExt P)} {rest : PStmts P} {u : P.Ident}
    (h : u ∉ Block.modifiedOrDefinedVars (s :: rest) false) :
    u ∉ Block.modifiedOrDefinedVars rest false := fun hm => h (by
  simp only [Block.modifiedOrDefinedVars, Block.modifiedVars, Block.definedVars,
    List.mem_append] at hm ⊢
  exact hm.elim (fun h => .inl (.inr h)) fun h => .inr (.inr h))

omit iDE iBE iLB iHB iSF iHI iLId iHa iW iLFvs in
/-- A name an `ite *` neither assigns nor defines, neither of its arms assigns or defines. -/
private theorem not_mem_modOrDef_ite {tss ess : PStmts P} {md : MetaData P} {u : P.Ident}
    (h : u ∉ Block.modifiedOrDefinedVars [.ite .nondet tss ess md] false) :
    u ∉ Block.modifiedOrDefinedVars tss false ∧ u ∉ Block.modifiedOrDefinedVars ess false := by
  simp only [Block.modifiedOrDefinedVars, Block.modifiedVars, Block.definedVars, Stmt.modifiedVars,
    Stmt.definedVars, Bool.false_eq_true, ite_false, List.append_nil, List.mem_append,
    not_or] at h ⊢
  exact ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩

include iLId iLFvs in
/-- **The traversal's output passes the annotation check** against a typing `Γ` of names of `Dd`
    and of the names `U` the list reads under their own names, when the names of `Dd` are not
    avoided, the names of `U` and the identifiers of the list are, the list neither assigns nor
    defines a name of `U`, the current value of every free variable of the list agrees with `Γ`
    or the variable is an unmapped name of `U`, and `Γ` gives each name of `U` the type a typing
    `Γs` the list's annotations agree with gives it. -/
private theorem ssaList_fvarTypesWellAnnotatedU
    (hite : ∀ {c t f : P.Expr} {p : P.Ident × P.Ty}, (p ∈ HasFvars.getTypedFvars c ∨
      p ∈ HasFvars.getTypedFvars t ∨ p ∈ HasFvars.getTypedFvars f) →
      p ∈ HasFvars.getTypedFvars (WPOps.ite c t f)) (ss : PStmts P) :
    ∀ {s s' : SSt P} {out : PStmts P}, ssaList oe ss s = .ok (out, s') →
    ∀ {Γ Γs : VarTyping P} {Dd U : List P.Ident}, NamesOK s.avoid.toList Dd s.next →
    (∀ y, (Γ y).isSome → y ∈ Dd ∨ y ∈ U) → (∀ y ∈ Dd, y ∉ s.avoid.toList) →
    (∀ u ∈ U, u ∈ s.avoid.toList) → (∀ u ∈ U, u ∉ Block.modifiedOrDefinedVars ss false) →
    (∀ x ∈ Block.idents ss, x ∈ s.avoid.toList) →
    Block.fvarTypesWellAnnotated Γs ss → (∀ u ∈ U, ∀ T, Γs u = some T → Γ u = some T) →
    (∀ x ∈ Block.freeVars ss, SAnn Γ U s.ρ x) →
    Block.fvarTypesWellAnnotated Γ out := by
  have exprHyps : ∀ {Γ Γs : VarTyping P} {U : List P.Ident} {ρ : Std.HashMap P.Ident (SVal P)}
      {e : P.Expr} {V : List P.Ident}, (∀ x ∈ HasFvars.getFvars e, x ∈ V) →
      (∀ x ∈ V, SAnn Γ U ρ x) → Γs.annotates (HasFvars.getTypedFvars e) →
      (∀ u ∈ U, ∀ T, Γs u = some T → Γ u = some T) →
      (∀ x ∈ HasFvars.getFvars e, ∀ v, ρ[x]? = some v → STyped Γ x v) ∧
      (∀ p ∈ HasFvars.getTypedFvars e, ρ[p.1]? = none → Γ p.1 = some p.2) := by
    intro Γ Γs U ρ e V hV hA hW hc
    refine ⟨fun x hx v hv => ?_, fun p hp hn => ?_⟩
    · rcases hA x (hV x hx) with ⟨w, hw, ht⟩ | ⟨hn, -⟩
      · exact Option.some.inj (hw.symm.trans hv) ▸ ht
      · exact absurd (hn.symm.trans hv) nofun
    · rcases hA p.1 (hV _ (LawfulHasFvars.mem_getFvars_of_typed _ _ _ hp)) with
        ⟨w, hw, -⟩ | ⟨-, hu⟩
      · exact absurd (hn.symm.trans hw) nofun
      · exact hc p.1 hu p.2 (hW p.1 p.2 hp)
  intro s s' out h
  refine no_implicit_lambda% (ssaList_ind (fun _ => by intros; trivial)
    ?initDet ?initNondet ?setDet ?setNondet ?_ ?_ ?_ ?_ h)
  case' initDet => intro x ty e _ rest s _ _ _ _ _ h1 ih Γ Γs Dd U hN hΓ hDd hUA hUm hid hWs hc hA
  case' setDet =>
    intro x e _ rest s ty _ _ _ _ _ _ h1 ih Γ Γs Dd U hN hΓ hDd hUA hUm hid hWs hc hA
  case initDet | setDet =>
    obtain ⟨hfe, hUe⟩ := exprHyps (e := e) (V := Block.freeVars (_ :: rest))
      (fun y hy => by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hy]) hA
      (fun z T hz => hWs.1 z T (by simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
        Cmd.getTypedVars, ExprOrNondet.getTypedVars] using hz)) hc
    have hold : ∀ y ∈ Block.freeVars rest, y ≠ x → SAnn Γ U s.ρ y :=
      fun y hy hne => hA y (by simp [Block.freeVars, Stmt.freeVars, hy, hne])
    have hx : x ∈ s.avoid.toList := hid x (by simp [Block.idents, Stmt.idents])
    have hxU : x ∉ U := fun hu => hUm x hu (by simp [Block.modifiedOrDefinedVars,
      HasVarsImp.definedVars, HasVarsImp.modifiedVars, CmdExt.definedVars, CmdExt.modifiedVars,
      Cmd.definedVars, Cmd.modifiedVars])
    have hidr : ∀ z ∈ Block.idents rest, z ∈ s.avoid.toList := fun z hz =>
      hid z (by simp [Block.idents, hz])
    have hUmr : ∀ u ∈ U, u ∉ Block.modifiedOrDefinedVars rest false := fun u hu =>
      not_mem_modOrDef_tail (hUm u hu)
    have hdx : ∀ u ∈ U, u ≠ x := fun u hu he => hxU (he ▸ hu)
    rcases assignVal_ok h1 with ⟨_, -, hf, rfl, rfl⟩ | ⟨y, hy, hcp, rfl, rfl, rfl⟩ |
      ⟨_, hf, rfl, rfl⟩
    case inr.inl =>
      obtain ⟨p, hp, hpe⟩ := List.any_eq_true.1 hcp
      simp only [Bool.and_eq_true, beq_iff_eq] at hpe
      obtain ⟨rfl, hpt⟩ := hpe
      have hΓy : Γ p.1 = some ty := WPLang.tyBEq_eq hpt ▸ foldE_typedU _ hite e hfe hUe p hp
      have hne : p.1 ≠ x := fun he => (hΓ p.1 (by simp [hΓy])).elim
        (fun hd => hDd p.1 hd (he ▸ hx)) fun hu => hxU (he ▸ hu)
      exact ih hN hΓ hDd hUA hUmr hidr hWs.2 (ext_agree hc (fun u hu => by
        simp [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
          Cmd.typedDefinedVars, hdx u hu]) fun _ _ => rfl)
        (SAnn.assign ⟨hne, fun T hT => by cases hT; exact hΓy⟩ hold)
    all_goals
      obtain ⟨j, hj, rfl, hy, rfl⟩ := sFresh_ok hf
      have hfr : freshName (baseOf x) j ∉ Dd ++ U := fun hm => (List.mem_append.1 hm).elim
        (hN.fresh_not_mem hj hy) fun hu => hy (hUA _ hu)
      have hΓ' : ∀ z, ((Γ.extend [(freshName (baseOf x) j, ty)]) z).isSome →
          z ∈ freshName (baseOf x) j :: Dd ∨ z ∈ U := fun z hz => by
        by_cases hzx : z = freshName (baseOf x) j
        · exact .inl (hzx ▸ .head _)
        · rw [VarTyping.extend_of_not_mem (by simpa using hzx)] at hz
          exact (hΓ z hz).imp_left (.tail _)
      have hxe : ∀ u ∈ U, (Γ.extend [(freshName (baseOf x) j, ty)]) u = Γ u := fun u hu =>
        VarTyping.extend_of_not_mem (by
        simp only [List.map_cons, List.map_nil, List.mem_singleton]
        rintro rfl
        exact hy (hUA _ hu))
      have hfe' := foldE_typedU (oe := oe) _ hite e hfe hUe
      refine init_out (fun p hp => hfe' p (by simpa [ExprOrNondet.getTypedVars] using hp))
        (ih (hN.add_fresh _ hj) hΓ' (fun z hz => (List.mem_cons.1 hz).elim (· ▸ hy) (hDd z))
          hUA hUmr hidr hWs.2 (ext_agree hc (fun u hu => by
            simp [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
              Cmd.typedDefinedVars, hdx u hu]) hxe)
          (SAnn.assign ?_ fun z hz hzx => SAnn.extend hΓ hfr (hold z hz hzx)))
    · refine ⟨⟨_, rfl, by simp [VarTyping.extend]⟩, fun p hp => ?_⟩
      have hne : p.1 ≠ freshName (baseOf x) j := fun he => hfr (he ▸ List.mem_append.2
        (hΓ p.1 (by simp [hfe' p hp])))
      exact (VarTyping.extend_of_not_mem (by simpa [eq_comm] using hne)).trans (hfe' p hp)
    · exact ⟨fun he => hy (by rw [he]; exact hx), fun T hT => by cases hT; simp [VarTyping.extend]⟩
  case' initNondet => intro x ty _ rest s _ _ _ _ h1 ih Γ Γs Dd U hN hΓ hDd hUA hUm hid hWs hc hA
  case' setNondet => intro x _ rest s ty _ _ _ _ _ h1 ih Γ Γs Dd U hN hΓ hDd hUA hUm hid hWs hc hA
  case initNondet | setNondet =>
    have hx : x ∈ s.avoid.toList := hid x (by simp [Block.idents, Stmt.idents])
    have hxU : x ∉ U := fun hu => hUm x hu (by simp [Block.modifiedOrDefinedVars,
      HasVarsImp.definedVars, HasVarsImp.modifiedVars, CmdExt.definedVars, CmdExt.modifiedVars,
      Cmd.definedVars, Cmd.modifiedVars])
    have hdx : ∀ u ∈ U, u ≠ x := fun u hu he => hxU (he ▸ hu)
    obtain ⟨j, hj, rfl, hy, rfl⟩ := sFresh_ok h1
    have hfr : freshName (baseOf x) j ∉ Dd ++ U := fun hm => (List.mem_append.1 hm).elim
      (hN.fresh_not_mem hj hy) fun hu => hy (hUA _ hu)
    have hΓ' : ∀ z, ((Γ.extend [(freshName (baseOf x) j, ty)]) z).isSome →
        z ∈ freshName (baseOf x) j :: Dd ∨ z ∈ U := fun z hz => by
      by_cases hzx : z = freshName (baseOf x) j
      · exact .inl (hzx ▸ .head _)
      · rw [VarTyping.extend_of_not_mem (by simpa using hzx)] at hz
        exact (hΓ z hz).imp_left (.tail _)
    have hxe : ∀ u ∈ U, (Γ.extend [(freshName (baseOf x) j, ty)]) u = Γ u := fun u hu =>
      VarTyping.extend_of_not_mem (by
        simp only [List.map_cons, List.map_nil, List.mem_singleton]
        rintro rfl
        exact hy (hUA _ hu))
    exact init_out (fun p hp => by simp [ExprOrNondet.getTypedVars] at hp)
      (ih (hN.add_fresh _ hj) hΓ' (fun z hz => (List.mem_cons.1 hz).elim (· ▸ hy) (hDd z)) hUA
        (fun u hu => not_mem_modOrDef_tail (hUm u hu))
        (fun z hz => hid z (by simp [Block.idents, hz])) hWs.2
        (ext_agree hc (fun u hu => by
          simp [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
            Cmd.typedDefinedVars, hdx u hu]) hxe)
        (SAnn.assign ⟨fun he => hy (by rw [he]; exact hx),
          fun T hT => by cases hT; simp [VarTyping.extend]⟩
          fun z hz hzx => SAnn.extend hΓ hfr (hA z (by simp [Block.freeVars, Stmt.freeVars, hz,
            hzx]))))
  · intro l a md rest s out s' ih Γ Γs Dd U hN hΓ hDd hUA hUm hid hWs hc hA
    have hr := ih hN hΓ hDd hUA (fun u hu => not_mem_modOrDef_tail (hUm u hu))
      (fun z hz => hid z (by simp [Block.idents, hz])) hWs.2 (ext_agree hc (fun _ _ => by
        simp [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
          Cmd.typedDefinedVars]) fun _ _ => rfl)
      fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy])
    obtain ⟨hfa, hUa⟩ := exprHyps (e := a) (V := Block.freeVars (_ :: rest))
      (fun y hy => by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hy]) hA
      (fun z T hz => hWs.1 z T (by simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
        Cmd.getTypedVars] using hz)) hc
    have hf := foldE_typedU (oe := oe) s.ρ hite a hfa hUa
    split
    · exact hr
    · exact ⟨fun z T hz => hf (z, T) (by simpa [HasTypedVarsImp.typedReadVars,
        CmdExt.typedReadVars, Cmd.getTypedVars] using hz),
        by simp only [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
          CmdExt.typedDefinedVars, Cmd.typedDefinedVars]; exact hr⟩
  · intro mk b l e md rest s out s' hmk _ ih Γ Γs Dd U hN hΓ hDd hUA hUm hid hWs hc hA
    rcases hmk with ⟨rfl, -⟩ | ⟨rfl, -⟩
    all_goals
      have hr := ih hN hΓ hDd hUA
        (fun u hu => not_mem_modOrDef_tail (hUm u hu))
        (fun z hz => hid z (by simp [Block.idents, hz])) hWs.2 (ext_agree hc (fun _ _ => by
        simp [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
          Cmd.typedDefinedVars]) fun _ _ => rfl)
        fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy])
      obtain ⟨hfe, hUe⟩ := exprHyps (e := e) (V := Block.freeVars (_ :: rest))
        (fun y hy => by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hy]) hA
        (fun z T hz => hWs.1 z T (by simpa [HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars,
          Cmd.getTypedVars] using hz)) hc
      have hf : ∀ p ∈ HasFvars.getTypedFvars (oblCond oe b s.ρ e), Γ p.1 = some p.2 := by
        rcases oblCond_eq b s.ρ e with h | ⟨-, h⟩ <;> rw [h]
        · exact renM'_typedU e hfe hUe
        · exact fun p hp => renM_typedU e hfe hUe p (evalM_sub _ WPLang.getTypedFvars_evalOp? hp)
      exact ⟨fun z T hz => hf (z, T) (by simpa [HasTypedVarsImp.typedReadVars,
        CmdExt.typedReadVars, Cmd.getTypedVars] using hz),
        by simp only [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
          CmdExt.typedDefinedVars, Cmd.typedDefinedVars]; exact hr⟩
  · intro tss ess md s t sT sU e out s' hT ihT hU _ ihE h1 h2 h3 Γ Γs Dd U hN hΓ hDd hUA hUm hid
      hWs hc hA
    obtain ⟨⟨ha, hn, -⟩, hρ⟩ := undoTo_frame (ssaList_frame _ hT) hU
    have hUmT : ∀ u ∈ U, u ∉ Block.modifiedOrDefinedVars tss false := fun u hu =>
      (not_mem_modOrDef_ite (hUm u hu)).1
    have hUmE : ∀ u ∈ U, u ∉ Block.modifiedOrDefinedVars ess false := fun u hu =>
      (not_mem_modOrDef_ite (hUm u hu)).2
    have rT := ihT hN hΓ hDd hUA hUmT
      (fun z hz => hid z (by simp [Block.idents, Stmt.idents, hz])) hWs.1.2.1 hc
      fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy])
    have rE := ihE (fun y hy b j hj he => ha ▸ hN y hy b j (Nat.le_trans hn hj) he) hΓ
      (fun z hz => ha ▸ hDd z hz) (fun z hz => ha ▸ hUA z hz) hUmE
      (fun z hz => ha ▸ hid z (by simp [Block.idents, Stmt.idents, hz])) hWs.1.2.2 hc
      fun y hy => by
        simpa only [SAnn, hρ y] using hA y (by simp [Block.freeVars, Stmt.freeVars, hy])
    exact if ht : t = [] then h1 ht ▸ rE else if he : e = [] then h2 ht he ▸ rT
      else h3 ht he ▸ ⟨⟨fun _ _ hz => by simp [ExprOrNondet.getTypedVars] at hz, rT, rE⟩, trivial⟩
  · intro tc md rest s out s' ih Γ Γs Dd U hN hΓ hDd hUA hUm hid hWs hc hA
    exact ih hN hΓ hDd hUA (fun u hu => not_mem_modOrDef_tail (hUm u hu))
      (fun z hz => hid z (by simp [Block.idents, hz])) hWs.2
      (ext_agree hc (fun _ _ => by simp [Stmt.typedDefinedVars]) fun _ _ => rfl)
      fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy])

/-! ## The entry renaming on every free variable -/

omit iDE iHB iHF iSF iHI iHa iHFs iW iLFvs in
/-- A name the renaming `ρ0` renames has the target of one of its pairs with that name as key;
    any other name is its own current name. -/
theorem Ren.get_cases (ρ0 : Ren P) (x : P.Ident) :
    (∃ q ∈ ρ0, q.1 = x ∧ ρ0.get x = q.2) ∨ (x ∉ ρ0.map (·.1) ∧ ρ0.get x = x) := by
  cases hf : ρ0.find? (·.1 == x) with
  | some q => exact .inl ⟨q, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf,
      by simp [Ren.get, hf]⟩
  | none => exact .inr ⟨fun hm => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
      simpa using List.find?_eq_none.1 hf q hq, by simp [Ren.get, hf]⟩

omit iLFvs in
include iLId in
/-- Every entry name of a free variable of `lay` of the form of a fresh name the traversal may
    introduce after the entry renaming is avoided: a renamed free variable's entry name has a
    smaller counter, and an unrenamed one is an identifier of `lay`. -/
theorem ssaEntryRen_namesOK_freeVars {G : IdSet P} {tys : Tys P} {xs : List P.Ident}
    {al : List (P.Ident × P.Ident)} (hal : ∀ q ∈ al, q.2 ∈ xs) (lay : PStmts P) :
    NamesOK (inputAvoid G tys lay).toList
      ((Block.freeVars lay).map (ssaEntryRen (inputAvoid G tys lay) xs al 0).1.get)
      (ssaEntryRen (inputAvoid G tys lay) xs al 0).2 := by
  intro y hy b j hj he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  rcases Ren.get_cases (ssaEntryRen (inputAvoid G tys lay) xs al 0).1 x with
    ⟨q, hq, -, hg⟩ | ⟨-, hg⟩
  · obtain ⟨⟨b', j', -, hj', hb, -⟩, -⟩ := (ssaEntryRen_spec _ xs al 0 hal).2.1 q hq
    exact absurd (freshName_counter_inj (hb.symm.trans (hg.symm.trans he))) (by omega)
  · rw [hg]
    simp [inputAvoid, AvoidSet.toList, IdSet.ofList, Block.mem_idents_of_mem_freeVars lay hx]

include iLId iLFvs in
/-- **Well-scopedness of the SSA output from the entry names of the free variables**, for any
    free variables: a renamed one is read under its entry name, an unrenamed one under its own
    name. -/
theorem ssaEntry_wellScopedFV_freeVars {G : IdSet P} {tys : Tys P} {xs : List P.Ident}
    {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P} {so : SOut P}
    (h : ssaEntry oe G tys xs al lay = .ok (ρ0, so)) (hal : ∀ q ∈ al, q.2 ∈ xs) :
    Block.readsDefined ((Block.freeVars lay).map ρ0.get) so.out = true := by
  obtain ⟨rfl, hb⟩ := ssaEntry_ok h
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hb
  refine ssaList_wellScoped _ h1 (ssaEntryRen_namesOK_freeVars hal lay) fun x hx => ?_
  rw [entryMap_lookup]
  rcases Ren.get_cases (ssaEntryRen (inputAvoid G tys lay) xs al 0).1 x with
    ⟨q, hq, hqx, hg⟩ | ⟨hn, hg⟩
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
      ((List.find?_isSome (p := (·.1 == x))).2 ⟨q, hq, by simp [hqx]⟩)
    rw [hp]
    exact List.mem_map.2 ⟨x, hx, by simp [Ren.get, hp]⟩
  · rw [List.find?_eq_none.2 fun q hq he => hn (List.mem_map.2 ⟨q, hq, by simpa using he⟩)]
    exact List.mem_map.2 ⟨x, hx, hg⟩

include iLId iLFvs in
/-- **The SSA output passes the annotation check** on a guarded program each of whose free
    variables is a name of `xs`, the name of an alias of `al`, or neither assigned nor defined
    in the program, against a typing `Γ` that gives the entry name of every renamed free variable
    the type `tys` records for it, gives every other free variable the type a typing `Γs` the
    program's annotations agree with gives it, and types only those names. -/
theorem ssaEntry_fvarTypesWellAnnotated_unassigned
    (hite : ∀ {c t f : P.Expr} {p : P.Ident × P.Ty}, (p ∈ HasFvars.getTypedFvars c ∨
      p ∈ HasFvars.getTypedFvars t ∨ p ∈ HasFvars.getTypedFvars f) →
      p ∈ HasFvars.getTypedFvars (WPOps.ite c t f))
    {G : IdSet P} {tys : Tys P} {xs : List P.Ident}
    {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P} {so : SOut P}
    (h : ssaEntry oe G tys xs al lay = .ok (ρ0, so)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (hfv : ∀ x ∈ Block.freeVars lay,
      x ∈ xs ∨ x ∈ al.map (·.1) ∨ x ∉ Block.modifiedOrDefinedVars lay false)
    {Γ Γs : VarTyping P} (hWs : Block.fvarTypesWellAnnotated Γs lay)
    (hty : ∀ x ∈ Block.freeVars lay, x ∈ xs ∨ x ∈ al.map (·.1) →
      ∀ T, tys.get? x = some T → Γ (ρ0.get x) = some T)
    (hU : ∀ x ∈ Block.freeVars lay, x ∉ xs → x ∉ al.map (·.1) →
      ∀ T, Γs x = some T → Γ x = some T)
    (hdom : ∀ y, (Γ y).isSome → ∃ x ∈ Block.freeVars lay, y = ρ0.get x) :
    Block.fvarTypesWellAnnotated Γ so.out := by
  obtain ⟨rfl, hb⟩ := ssaEntry_ok h
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hb
  have hspec := ssaEntryRen_spec (inputAvoid G tys lay) xs al 0 hal
  have hidA : ∀ x ∈ Block.idents lay, x ∈ (inputAvoid G tys lay).toList := fun x hx => by
    simp [inputAvoid, AvoidSet.toList, IdSet.ofList, hx]
  have hkey : ∀ x, x ∈ (ssaEntryRen (inputAvoid G tys lay) xs al 0).1.map (·.1) ↔
      x ∈ xs ∨ x ∈ al.map (·.1) := fun x => ⟨fun hm => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
    exact (hspec.2.1 q hq).2, hspec.2.2 x⟩
  let U := (Block.freeVars lay).filter
    fun x => !decide (x ∈ (ssaEntryRen (inputAvoid G tys lay) xs al 0).1.map (·.1))
  have hUm : ∀ u, u ∈ U ↔ u ∈ Block.freeVars lay ∧
      u ∉ (ssaEntryRen (inputAvoid G tys lay) xs al 0).1.map (·.1) := fun u => by simp [U]
  refine ssaList_fvarTypesWellAnnotatedU hite _ h1 (Γs := Γs) (U := U)
    (Dd := (ssaEntryRen (inputAvoid G tys lay) xs al 0).1.map (·.2))
    (ssaEntryRen_namesOK _ _ _ hal fun y hy => .inl hy) (fun y hy => ?_) (fun y hy => ?_)
    (fun u hu => hidA u (Block.mem_idents_of_mem_freeVars lay ((hUm u).1 hu).1)) (fun u hu => ?_)
    hidA hWs (fun u hu T hT => ?_) fun x hx => ?_
  · obtain ⟨x, hx, rfl⟩ := hdom y hy
    rcases Ren.get_cases (ssaEntryRen (inputAvoid G tys lay) xs al 0).1 x with
      ⟨q, hq, -, hg⟩ | ⟨hn, hg⟩
    · exact .inl (hg ▸ List.mem_map_of_mem hq)
    · rw [hg]
      exact .inr ((hUm _).2 ⟨hx, hn⟩)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    exact (hspec.2.1 q hq).1.elim fun _ ⟨_, _, _, _, hn⟩ => hn
  · obtain ⟨hx, hn⟩ := (hUm u).1 hu
    exact ((hfv u hx).resolve_left fun h => hn ((hkey u).2 (.inl h))).resolve_left
      fun h => hn ((hkey u).2 (.inr h))
  · obtain ⟨hx, hn⟩ := (hUm u).1 hu
    exact hU u hx (fun h => hn ((hkey u).2 (.inl h))) (fun h => hn ((hkey u).2 (.inr h))) T hT
  · dsimp only
    unfold SAnn
    rw [entryMap_lookup]
    rcases Ren.get_cases (ssaEntryRen (inputAvoid G tys lay) xs al 0).1 x with
      ⟨q, hq, hqx, hg⟩ | ⟨hn, hg⟩
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
        ((List.find?_isSome (p := (·.1 == x))).2 ⟨q, hq, by simp [hqx]⟩)
      rw [hp]
      have hp2 : p.2 = (ssaEntryRen (inputAvoid G tys lay) xs al 0).1.get x := by
        simp [Ren.get, hp]
      have hpn := ((hspec.2.1 p (List.mem_of_find?_eq_some hp)).1).elim
        fun _ ⟨_, _, _, _, hn⟩ => hn
      refine .inl ⟨_, rfl, fun hpx => hpn (hpx ▸ hidA x (Block.mem_idents_of_mem_freeVars lay hx)),
        fun T hT => hp2 ▸ hty x hx ((hkey x).1 (hqx ▸ List.mem_map_of_mem hq)) T hT⟩
    · rw [List.find?_eq_none.2 fun q hq he => hn (List.mem_map.2 ⟨q, hq, by simpa using he⟩)]
      exact .inr ⟨rfl, (hUm x).2 ⟨hx, hn⟩⟩

omit iDE iHB iSF iHI iLId iHa iW iLFvs in
/-- A passive statement list in tree form that reads only names defined before it from the names
    `D` (`Block.readsDefined D`) defines no name of `D`. -/
theorem Block.readsDefined_definedVars_not_mem (ss : Block P (CmdExt P)) :
    ∀ {D : List P.Ident}, Block.readsDefined D ss = true → Block.treeForm ss = true →
      Block.passiveForm ss = true → ∀ n ∈ Block.definedVars ss false, n ∉ D := by
  induction ss using Block.passiveForm.induct
  case case1 => simp
  case case2 x ty e md rest ih =>
    intro D hr hT hP n hn hnD
    rcases e with e | _ <;>
      simp only [Block.readsDefined, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hr
    all_goals
      simp only [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars,
        Cmd.definedVars, List.cons_append, List.nil_append, List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact absurd hr.1 (by simp [hnD])
      · exact ih hr.2 (by simpa [Block.treeForm] using hT) (by simpa [Block.passiveForm] using hP)
          n hn (.tail _ hnD)
  case case3 l e md rest ih | case4 l e md rest ih | case5 l e md rest ih =>
    intro D hr hT hP n hn
    simp only [Block.readsDefined, Bool.and_eq_true] at hr
    exact ih hr.2 (by simpa [Block.treeForm] using hT) (by simpa [Block.passiveForm] using hP) n
      (by simpa [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars,
        Cmd.definedVars] using hn)
  case case6 t e md rest ihT ihE _ =>
    intro D hr hT hP n hn
    simp only [Block.treeForm, List.isEmpty_iff, Bool.and_eq_true] at hT
    obtain ⟨⟨rfl, hT1⟩, hT2⟩ := hT
    simp only [Block.passiveForm, Bool.and_eq_true] at hP
    simp only [Block.readsDefined, Bool.and_eq_true] at hr
    simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ite_false,
      List.append_nil, List.mem_append] at hn
    exact hn.elim (ihT hr.1 hT1 hP.1.1 n) (ihE hr.2 hT2 hP.1.2 n)
  case case7 =>
    intro D hr hT hP
    simp_all [Block.passiveForm]

end -- public section

end WP
end Imperative

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Imperative.Specification.Transform Core.Logic
  Strata.Logic Imperative.DeadDefElim Core.DeadDefElim

public section

/-- **The SSA output agrees with a typing of the target store**, on a list each of whose free
    variables is a parameter, an alias, or neither assigned nor defined in the list.  Let the
    environments be related by the entry renaming (`SSAEntryRel`), every alias rename to a
    parameter, and the source store conform to a typing `Γs` the list's annotations agree with.
    If `ssaEntry` succeeds, the target store conforms to a typing its output's annotations agree
    with: the typing of the entry names by `tys` (`entryTyping`), and `Γs` at the free variables
    the entry renaming does not rename. -/
private theorem ssa_outAnnotated_unassigned {fac : Lambda.Factory CoreLParams}
    {G : IdSet Expression} {tys : Tys Expression} {xs : List Expression.Ident}
    {al : List (Expression.Ident × Expression.Ident)} {ss₀ : Statements}
    {ρ ρ' : Imperative.Env Expression} (hrel : SSAEntryRel fac G tys xs al ss₀ ρ ρ')
    (hal : ∀ q ∈ al, q.2 ∈ xs)
    (hfv : ∀ x ∈ Block.freeVars ss₀,
      x ∈ xs ∨ x ∈ al.map (·.1) ∨ x ∉ Block.modifiedOrDefinedVars ss₀ false)
    {ρ0 : Ren Expression} {so : SOut Expression} (hss : ssaEntry fac G tys xs al ss₀ = .ok (ρ0, so))
    {Γs : VarTyping Expression} (hΓs : StoreHasTyping ρ.factory ρ.store Γs)
    (hWs : Block.fvarTypesWellAnnotated Γs ss₀) :
    ∃ Γ, StoreHasTyping ρ'.factory ρ'.store Γ ∧ Block.fvarTypesWellAnnotated Γ so.out := by
  obtain ⟨rfl, -⟩ := ssaEntry_ok hss
  have hspec := ssaEntryRen_spec (inputAvoid G tys ss₀) xs al 0 hal
  have hkey : ∀ x, x ∈ (ssaEntryRenOf G tys xs al ss₀).map (·.1) ↔ x ∈ xs ∨ x ∈ al.map (·.1) :=
    fun x => ⟨fun hm => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
      exact (hspec.2.1 q hq).2, hspec.2.2 x⟩
  have hidA : ∀ x ∈ Block.freeVars ss₀, x ∈ (inputAvoid G tys ss₀).toList := fun x hx => by
    simp [inputAvoid, AvoidSet.toList, IdSet.ofList, Block.mem_idents_of_mem_freeVars ss₀ hx]
  have hfind : ∀ y T, entryTyping (ssaEntryRenOf G tys xs al ss₀) tys ss₀ y = some T →
      ∃ x ∈ Block.freeVars ss₀, (ssaEntryRenOf G tys xs al ss₀).get x = y ∧
        tys.get? x = some T := by
    intro y T h
    cases hf : (Block.freeVars ss₀).find?
        (fun x => (ssaEntryRenOf G tys xs al ss₀).get x == y && (tys.get? x).isSome) with
    | none => simp [entryTyping, hf] at h
    | some x =>
      simp only [entryTyping, hf, Option.bind_some] at h
      have hx := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      exact ⟨x, List.mem_of_find?_eq_some hf, hx.1, h⟩
  have hval : ∀ x ∈ Block.freeVars ss₀, ∀ T, tys.get? x = some T →
      ∃ v, ρ'.store ((ssaEntryRenOf G tys xs al ss₀).get x) = some v ∧
        HasVal.valueOfTy ρ'.factory v T := fun x hx T hT => by
    obtain ⟨he, hs⟩ := hrel.entry x hx
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨v, he ▸ hv, hrel.factory ▸ hrel.tyOK x hx hx T hT v hv⟩
  let Γ : VarTyping Expression := fun y =>
    if y ∈ Block.freeVars ss₀ ∧ y ∉ (ssaEntryRenOf G tys xs al ss₀).map (·.1) then Γs y
    else entryTyping (ssaEntryRenOf G tys xs al ss₀) tys ss₀ y
  refine ⟨Γ, fun y T hy => ?_, ssaEntry_fvarTypesWellAnnotated_unassigned
    (fun h => (Core.typedOpLaws fac).typedFvars_ite h) hss hal hfv hWs
    (fun x hx hk T hT => ?_) (fun x hx h1 h2 T hT => ?_) fun y hy => ?_⟩
  · simp only [Γ] at hy
    split at hy
    · rename_i hu
      obtain ⟨v, hv, hvT⟩ := hΓs y T hy
      have hg : (ssaEntryRenOf G tys xs al ss₀).get y = y :=
        ((Ren.get_cases _ y).resolve_left fun ⟨q, hq, hqy, _⟩ =>
          hu.2 (hqy ▸ List.mem_map_of_mem hq)).2
      exact ⟨v, hg ▸ ((hrel.entry y hu.1).1 ▸ hv), hrel.factory ▸ hvT⟩
    · obtain ⟨x, hx, rfl, hT⟩ := hfind y T hy
      exact hval x hx T hT
  · obtain ⟨q, hq, he⟩ := Ren.get_mem ((hkey x).2 hk)
    have hn : ¬ ((ssaEntryRenOf G tys xs al ss₀).get x ∈ Block.freeVars ss₀ ∧
        (ssaEntryRenOf G tys xs al ss₀).get x ∉ (ssaEntryRenOf G tys xs al ss₀).map (·.1)) :=
      fun ⟨h, _⟩ => ((hspec.2.1 q hq).1.elim fun _ ⟨_, _, _, _, hn⟩ => hn) (he ▸ hidA _ h)
    show Γ ((ssaEntryRenOf G tys xs al ss₀).get x) = some T
    simp only [Γ, hn, ite_false]
    have hsome : ((Block.freeVars ss₀).find? fun z =>
        (ssaEntryRenOf G tys xs al ss₀).get z == (ssaEntryRenOf G tys xs al ss₀).get x &&
          (tys.get? z).isSome).isSome :=
      List.find?_isSome.2 ⟨x, hx, by simp [hT]⟩
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hsome
    have hzp := List.find?_some hz
    simp only [Bool.and_eq_true, beq_iff_eq] at hzp
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 hzp.2
    obtain ⟨v, hv, hvT⟩ := hval x hx T hT
    obtain ⟨w, hw, hwU⟩ := hval z (List.mem_of_find?_eq_some hz) U hU
    rw [hzp.1, hv] at hw
    cases hw
    change ((Block.freeVars ss₀).find? fun z =>
        (ssaEntryRenOf G tys xs al ss₀).get z == (ssaEntryRenOf G tys xs al ss₀).get x &&
          (tys.get? z).isSome).bind tys.get? = some T
    rw [hz, Option.bind_some, hU]
    exact congrArg some (Core.valueOfTy_unique hwU hvT)
  · have hn : x ∉ (ssaEntryRenOf G tys xs al ss₀).map (·.1) := fun hm =>
      ((hkey x).1 hm).elim h1 h2
    simpa only [Γ, hx, hn, not_false_eq_true, and_self, ite_true] using hT
  · simp only [Γ] at hy
    split at hy
    · rename_i hu
      exact ⟨y, hu.1, (((Ren.get_cases _ y).resolve_left fun ⟨q, hq, hqy, _⟩ =>
        hu.2 (hqy ▸ List.mem_map_of_mem hq)).2).symm⟩
    · obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 hy
      obtain ⟨x, hx, rfl, -⟩ := hfind y T hT
      exact ⟨x, hx, rfl⟩

/-- **The SSA phase keeps the initial-environment gate**, for any free variables.  For a Core
    statement list `ss₀` in tree form on which `ssaEntry fac G tys xs al` succeeds with the entry
    renaming `ρ0` and the output `so.out`, every reserved prefix of `params` being free of `@` and
    every alias of `al` denoting a parameter of `xs`: when the environment `ρ` of `ss₀` satisfies
    `BlockInitEnvWF params ss₀`, and `ρ'` has the factory of `ρ`, holds under the entry name of
    each free variable of `ss₀` (the name itself when the entry renaming leaves it alone) its
    (defined) value in `ρ`, typed by `tys`, and binds nothing else, while every parameter is
    defined in `ρ`, then `ρ'` satisfies `BlockInitEnvWF params so.out`, provided the type
    annotations of `so.out` agree with a typing of `ρ'` (`hty`). -/
theorem ssaEntry_blockInitEnvWF_freeVars {params : InitEnvWFParams}
    {fac : Lambda.Factory CoreLParams}
    (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList) {G : IdSet Expression}
    {tys : Tys Expression} {xs : List Expression.Ident}
    {al : List (Expression.Ident × Expression.Ident)} (hal : ∀ q ∈ al, q.2 ∈ xs)
    {ss₀ : Statements} {ρ0 : Ren Expression} {so : SOut Expression}
    (h : ssaEntry fac G tys xs al ss₀ = .ok (ρ0, so)) (hTF : Block.treeForm ss₀ = true)
    {ρ ρ' : Imperative.Env Expression} (hF : ρ'.factory = ρ.factory)
    (hval : ∀ x ∈ Block.freeVars ss₀, ρ.store x =
      ρ'.store ((ssaEntryRen (inputAvoid G tys ss₀) xs al 0).1.get x) ∧ (ρ.store x).isSome)
    (hparams : ∀ x ∈ xs, (ρ.store x).isSome)
    (htyOK : TyOK ρ.factory tys (Block.freeVars ss₀) (Block.freeVars ss₀) ρ.store)
    (hdomS : ∀ y, (ρ'.store y).isSome →
      ∃ x ∈ Block.freeVars ss₀, y = (ssaEntryRen (inputAvoid G tys ss₀) xs al 0).1.get x)
    (hwf : BlockInitEnvWF params ss₀ ρ)
    (hty : ∃ Γ, StoreHasTyping ρ'.factory ρ'.store Γ ∧ Block.fvarTypesWellAnnotated Γ so.out) :
    BlockInitEnvWF params so.out ρ' := by
  have hrd := ssaEntry_wellScopedFV_freeVars h hal
  obtain ⟨rfl, hb⟩ := ssaEntry_ok h
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hb
  have hdom (y : Expression.Ident) : (ρ'.store y).isSome = true ↔
      y ∈ (Block.freeVars ss₀).map ((ssaEntryRen (inputAvoid G tys ss₀) xs al 0).1).get := by
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hdomS y hy
      exact List.mem_map_of_mem hx
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (hval x hx).1 ▸ (hval x hx).2
  obtain ⟨o1, o2, o3, o4, o5⟩ := ssaList_outFacts (fun ty => ∃ v, HasVal.valueOfTy ρ'.factory v ty)
    ⟨_, (HasBool.boolIsValOfTy _).1⟩ (Block.getOps ss₀) ss₀ h1 hTF (hF ▸ hwf.initTypesInhabited)
    (fun x hx ty hty => by
      rw [entryMap_lookup tys _ x] at hty
      rcases hf : (ssaEntryRen (inputAvoid G tys ss₀) xs al 0).1.find? (·.1 == x) with _ | q <;>
        simp only [hf, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
          SVal.ty?, reduceCtorEq] at hty
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hval x hx).2
      exact ⟨w, hF ▸ htyOK x hx hx ty hty w hw⟩) (fun _ h => h)
    fun (y : Expression.Ident) (w : SVal Expression) hw o ho => by
      obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 ((entryMap_lookup tys _ y).symm.trans hw)
      simp [SVal.expr, var_ops] at ho
  obtain ⟨d1, d2, d3, d4⟩ :=
    Block.defUseWellFormed_of_readsDefined (df := params.declaredFuncs) so.out hrd o1 o2
    hdom fun o ho => Block.getOps_declared_of_defUseWellFormed ss₀ hTF hwf.defUseOk o (o5 o ho)
  refine { toWellFormedSemanticEval := hF ▸ hwf.toWellFormedSemanticEval
           storeWellDefined := ?_
           readWritesDefined := ?_
           defsUndefined := ?_
           definedVarsNotReserved := ?_
           reservedFresh := ?_
           exitsNotReserved := by simp [Imperative.Block.labels_of_treeForm o1]
           defUseOk := d1
           factoryDeclared := hwf.factoryDeclared
           runtimeFactoryDeclared := hF ▸ hwf.runtimeFactoryDeclared
           initTypesInhabited := o4
           fvarTypesOk := hty
           measuresTyped := by simp [Imperative.Block.measures_of_treeForm o1] }
  · intro y v hy
    obtain ⟨x, hx, rfl⟩ := hdomS y (by simp [hy])
    exact hF ▸ hwf.storeWellDefined x v ((hval x hx).1.trans hy)
  · intro n hn hnd
    simp only [Block.touchedVars, Block.modifiedOrDefinedVars, d2, List.nil_append,
      List.mem_append] at hn
    rcases hn with hn | hn
    · exact absurd (d3 n hn) hnd
    · exact (hdom n).2 ((d4 n hn).resolve_right hnd)
  · intro n hn
    refine Option.isNone_iff_eq_none.2 (Option.eq_none_iff_forall_ne_some.2 fun v hv => ?_)
    exact Imperative.WP.Block.readsDefined_definedVars_not_mem so.out hrd o1 o2 n hn
      ((hdom n).1 (by simp [hv]))
  · intro n hn name hname p hpm
    obtain rfl : name = n.name := by rw [hname]; rfl
    obtain ⟨x, hx, j, -, rfl⟩ := o3 n hn
    refine fresh_notReserved j (hp p hpm) (baseOf_prefix x) ?_
    by_cases hxd : x ∈ Block.definedVars ss₀ false
    · exact hwf.definedVarsNotReservedCore x hxd p hpm
    · refine hwf.reservedFreshCore x (hwf.readWritesDefined x ?_ hxd) p hpm
      simp [Block.touchedVars, Block.modifiedOrDefinedVars, hx.resolve_left hxd]
  · intro n hn name hname p hpm
    obtain rfl : name = n.name := by rw [hname]; rfl
    obtain ⟨x, hx, rfl⟩ := hdomS n hn
    rcases Ren.get_cases (ssaEntryRen (inputAvoid G tys ss₀) xs al 0).1 x with
      ⟨q, hq, -, hg⟩ | ⟨-, hg⟩
    · rw [hg]
      obtain ⟨w, hw, k, hk⟩ := ssaEntryRen_base _ xs al 0 hal q hq
      exact hk ▸ fresh_notReserved k (hp p hpm) (List.prefix_refl _)
        (hwf.reservedFreshCore w (hparams w hw) p hpm)
    · rw [hg]
      exact hwf.reservedFreshCore x (hval x hx).2 p hpm

/-- **The SSA phase over-approximates the traces of a guarded statement list whose free
    variables are parameters, aliases or unassigned.**  For a Core statement list `ss₀` in tree
    form, with an assertion or a cover in every arm of every `ite *` and each of its free
    variables among the parameters `xs`, the aliases of `al`, or neither assigned nor defined in
    `ss₀`, on which `ssaEntry fac G tys xs al` succeeds with the output `out`, every reserved
    prefix of `params` being free of `@`, every alias of `al` denoting a parameter of `xs`, and all
    initial environments `ρ₀` of `ss₀` and `ρ₀'` of `out` related by `SSAEntryRel fac` with `ρ₀`
    satisfying `BlockInitEnvWF params ss₀`:
    * every finite trace of `ss₀` from `ρ₀` has a trace of `out` from `ρ₀'` whose assumptions are
      weakened (`Trace.WeakensAssumes evalInterp`);
    * every terminating run of `ss₀` from `ρ₀` has a terminating run of `out` from `ρ₀'` with
      such a trace and the same factory (`ss₀` has no exiting run);
    * `out` satisfies `BlockInitEnvWF params` at `ρ₀'`. -/
theorem ssa_overapproximatesTraces_unassigned (π : String → Option Procedure)
    (params : InitEnvWFParams) (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList)
    (fac : Lambda.Factory CoreLParams) (G : IdSet Expression) (tys : Tys Expression)
    (xs : List Expression.Ident) (al : List (Expression.Ident × Expression.Ident))
    (hal : ∀ q ∈ al, q.2 ∈ xs) (ss₀ : Statements) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes evalInterp)
      (SSAEntryRel fac G tys xs al ss₀) (fun ρ ρ' => ρ'.factory = ρ.factory)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => (ssaEntry fac G tys xs al ss).toOption.map (·.2.out))
      (fun ss => ss = ss₀ ∧ Block.treeForm ss = true ∧ Block.armsHaveChecks ss = true ∧
        ∀ x ∈ Block.freeVars ss,
          x ∈ xs ∨ x ∈ al.map (·.1) ∨ x ∉ Block.modifiedOrDefinedVars ss false) params params := by
  intro ss out hT ⟨rfl, htf, harm, hfv⟩ ρ₀ ρ₀' hrel hwf
  obtain ⟨⟨ρ0, so⟩, hss, rfl⟩ : ∃ r, ssaEntry fac G tys xs al ss = .ok r ∧ r.2.out = out := by
    cases h : ssaEntry fac G tys xs al ss <;>
      simp only [h, Except.toOption, Option.map, reduceCtorEq] at hT
    exact ⟨_, rfl, Option.some.inj hT⟩
  obtain ⟨Γs, hΓs, hWs⟩ := hwf.fvarTypesOk
  have hgate := ssaEntry_blockInitEnvWF_freeVars hp hal hss htf hrel.factory hrel.entry
    hrel.params hrel.tyOK hrel.dom hwf (ssa_outAnnotated_unassigned hrel hal hfv hss hΓs hWs)
  obtain ⟨rfl, hs⟩ := ssaEntry_ok hss
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hs
  obtain ⟨σ₀, F⟩ := ρ₀
  obtain ⟨σ₀', F'⟩ := ρ₀'
  obtain rfl : F = F' := hrel.factory.symm
  have hC : WellFormedStore σ₀ F := hwf.storeWellDefined
  have hWB := hwf.bool
  have hnc : Statements.noCalls ss = true :=
    Block.treeForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) htf
  have hsim := ssaList_sim ⟨hwf.var, hwf.val, coreEvaluator_WellFormedSemanticEvalSubstExprs F,
      hwf.mono, coreEvaluator_WellFormedSemanticEvalOp F fac hrel.factoryIs hwf.bool⟩ _
    ((Block.freeVars ss).map (ssaEntryRenOf G tys xs al ss).get) _ ss h1 rfl (Nat.le_refl _)
    (σL := σ₀) (σS := σ₀') (entryMap_agree hrel.entry hrel.tyOK) hC
    (fun y v hy => by
      obtain ⟨x, hx, rfl⟩ := hrel.dom y (by simp [hy])
      exact hC x v ((hrel.entry x hx).1.trans hy))
    ⟨_, ssaEntryRen_namesOK_freeVars hal ss,
      fun y hy => (hrel.dom y hy).elim fun x ⟨hx, he⟩ => he ▸ List.mem_map_of_mem hx,
      fun z hz => .inl hz⟩
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_, hgate⟩
  · have h' := star_evalE h hnc
    by_cases htr : trace = []
    · subst htr
      exact ⟨_, [], .refl _, .nil⟩
    obtain ⟨tr', hw, rfl | hb⟩ := hsim.1 (star_breach h' htr)
    · exact ⟨_, [], .refl _, hw⟩
    obtain ⟨cfg', hc⟩ := breach_star hWB hb
    exact ⟨cfg', tr', star_core π hc, hw⟩
  · have h' := star_evalE h hnc
    obtain ⟨σL', -, tr', σS', hb, hw⟩ := hsim.2 harm (star_brun.1 h')
    exact ⟨_, tr', star_core π (brun_star hWB hb), starE_preserves_factory h', hw⟩
  · obtain ⟨σL', ho, -⟩ := hsim.2 harm (star_brun.2 (star_evalE h hnc))
    cases ho

end -- public section

end WP
end Core
