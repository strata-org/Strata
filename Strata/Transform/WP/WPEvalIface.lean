/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BigStep.StoreAgree
public import Strata.Transform.Passive.Shadow

/-! # The evaluator interface of the WP prefix proof

The facts about the evaluator that the proof that the WP phase over-approximates failing
prefixes uses beyond the mainline factory laws, over the evaluation relation `EvalsTo` of
`DL/Imperative/CmdSemantics.lean`: its invariance under stores agreeing on the free variables
(`evalsTo_congr`), and the replay of a command step from a wider store (`cmd_widen`, over the
store agreement `Wide`).  Every other part of the proof reaches the evaluator only through these
and the mainline laws.

Key definitions: `Wide`.

Key theorems: `evalsTo_congr`, `cmd_widen`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [HasBool P] [HasFvar P] [HasFvars P]
variable {F : P.Factory}

omit [HasFvar P] in
/-- Value-valued stores agreeing on the free variables of `e` evaluate it alike. -/
theorem evalsTo_congr (hE : EvCongr F) {σ σ' : SemanticStore P} (hC : WellFormedStore σ F)
    (hC' : WellFormedStore σ' F) {e : P.Expr} {v : P.Val}
    (hA : ∀ y ∈ HasFvars.getFvars e, σ' y = σ y) (h : EvalsTo F σ e v) : EvalsTo F σ' e v :=
  (hE hC hC' e hA).trans h

/-- The value-valued stores `σ` and `σ'` agree on `N`. -/
@[expose] def Wide (F : P.Factory) (N : List P.Ident) (σ σ' : SemanticStore P) : Prop :=
  (∀ y ∈ N, σ' y = σ y) ∧ WellFormedStore σ F ∧ WellFormedStore σ' F

section
omit [HasFvar P] [HasFvars P]

/-- Agreement on `N` gives agreement on any subset of `N`. -/
theorem Wide.mono {N N' : List P.Ident} {σ σ' : SemanticStore P} (h : Wide F N σ σ')
    (hN : ∀ y ∈ N', y ∈ N) : Wide F N' σ σ' :=
  ⟨fun y hy => h.1 y (hN y hy), h.2⟩

/-- Defining `x` as the value `v` in both stores keeps agreement. -/
private theorem wide_def [DecidableEq P.Ident] {N : List P.Ident} {σ σ1 σ' : SemanticStore P}
    {x : P.Ident} {v : P.Val} (hW : Wide F (x :: N) σ σ') (hv : HasVal.value F v)
    (h1 : σ1 x = some v) (hfr : ∀ y, x ≠ y → σ1 y = σ y) :
    Wide F N σ1 (SemanticStore.update σ' x v) := by
  grind [Wide, SemanticStore.update, WellFormedStore]

end

/-- **A command step, replayed** from a value-valued store agreeing with the value-valued `σ` on
    the identifiers of the command and on `N`: a step of the same command, observed alike, to a
    store agreeing on `N` with the result. -/
theorem cmd_widen [DecidableEq P.Ident] [LawfulHasVal P] (hE : EvCongr F) {c : Cmd P}
    {σ σ1 σ' : SemanticStore P} {evs : List (Event P)} {N : List P.Ident}
    (h : EvalE F σ (.cmd c) σ1 evs)
    (hW : Wide F (Stmt.idents (.cmd (.cmd c) : PStmt P) ++ N) σ σ') :
    ∃ σ1' evs', EvalE F σ' (.cmd c) σ1' evs' ∧ evs'.map Event.obs = evs.map Event.obs ∧
      Wide F N σ1 σ1' := by
  have hev : ∀ e, (∀ y ∈ HasFvars.getFvars e, y ∈ Stmt.idents (.cmd (.cmd c) : PStmt P)) →
      ∀ v, EvalsTo F σ e v → EvalsTo F σ' e v := fun e he _ =>
    evalsTo_congr hE hW.2.1 hW.2.2 fun y hy => hW.1 y (List.mem_append_left _ (he y hy))
  have hobs : ∀ e, (∀ y ∈ HasFvars.getFvars e, y ∈ Stmt.idents (.cmd (.cmd c) : PStmt P)) →
      P.eval F σ' e = P.eval F σ e := fun e he =>
    hE hW.2.1 hW.2.2 e fun y hy => hW.1 y (List.mem_append_left _ (he y hy))
  have hN : Wide F N σ σ' := hW.mono fun y hy => List.mem_append_right _ hy
  cases c with
  | init x ty e md =>
    have hW' : Wide F (x :: N) σ σ' := hW.mono fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · cases e <;> simp [Stmt.idents]
      · exact List.mem_append_right _ hy
    have hx : σ' x = σ x := hW'.1 x List.mem_cons_self
    cases e with
    | det e =>
      match h with
      | .eval_init (v := v) hv (.init h0 h1 hfr) hty hwf =>
        obtain ⟨hU1, hU2⟩ := update_facts σ' x v
        exact ⟨_, [], .eval_init (hev e (fun y hy => by simp [Stmt.idents, hy]) _ hv)
          (.init (hx.trans h0) hU1 hU2) hty hwf, rfl,
          wide_def hW' (LawfulHasVal.valueOfTy_isVal _ _ _ hty) h1 hfr⟩
    | nondet =>
      match h with
      | .eval_init_unconstrained (v := v) (.init h0 h1 hfr) hty hwf =>
        obtain ⟨hU1, hU2⟩ := update_facts σ' x v
        exact ⟨_, [], .eval_init_unconstrained (.init (hx.trans h0) hU1 hU2) hty hwf, rfl,
          wide_def hW' (LawfulHasVal.valueOfTy_isVal _ _ _ hty) h1 hfr⟩
  | set x e md =>
    have hW' : Wide F (x :: N) σ σ' := hW.mono fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · cases e <;> simp [Stmt.idents]
      · exact List.mem_append_right _ hy
    have hx : σ' x = σ x := hW'.1 x List.mem_cons_self
    cases e with
    | det e =>
      match h with
      | .eval_set (v := v) hv (.update h0 h1 hfr) ⟨p, ty, hp, hpt, hvt⟩ hwf =>
        obtain ⟨hU1, hU2⟩ := update_facts σ' x v
        exact ⟨_, [], .eval_set (hev e (fun y hy => by simp [Stmt.idents, hy]) _ hv)
          (.update (hx.trans h0) hU1 hU2) ⟨p, ty, hx.trans hp, hpt, hvt⟩ hwf, rfl,
          wide_def hW' (LawfulHasVal.valueOfTy_isVal _ _ _ hvt) h1 hfr⟩
    | nondet =>
      match h with
      | .eval_set_nondet (v := v) (.update h0 h1 hfr) ⟨p, ty, hp, hpt, hvt⟩ hwf =>
        obtain ⟨hU1, hU2⟩ := update_facts σ' x v
        exact ⟨_, [], .eval_set_nondet (.update (hx.trans h0) hU1 hU2)
          ⟨p, ty, hx.trans hp, hpt, hvt⟩ hwf, rfl,
          wide_def hW' (LawfulHasVal.valueOfTy_isVal _ _ _ hvt) h1 hfr⟩
  | assert l e md =>
    obtain ⟨rfl, rfl⟩ := evalE_assert_inv h
    exact ⟨σ', _, .eval_assert, by simp [Event.obs, hobs e fun y hy => by simpa [Stmt.idents]], hN⟩
  | assume l e md =>
    obtain ⟨rfl, rfl⟩ := evalE_assume_inv h
    exact ⟨σ', _, .eval_assume, by simp [Event.obs, hobs e fun y hy => by simpa [Stmt.idents]], hN⟩
  | cover l e md =>
    obtain ⟨rfl, rfl⟩ := evalE_cover_inv h
    exact ⟨σ', _, .eval_cover, by simp [Event.obs, hobs e fun y hy => by simpa [Stmt.idents]], hN⟩


end -- public section

end WP
end Imperative
