/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WP
public import Strata.Transform.Passive.Shadow
public import Strata.Transform.Passive.WellTyped
import Strata.Transform.WP.WPOverSim
import Strata.Transform.WP.WPOverEmit
import Strata.Util.ExceptProps

/-! # The WP phase over-approximates

A failing occurrence of a target that a loop-free list reaches on a feasible path, along a run
whose off-path runs exist (`FailsD`), is also reached by its guarded program from the same store:
an occurrence of the same target whose condition is the list's under the WP renaming of its free
variables (`substObl wsub`), and the skeleton has a slot for its label (`wpEntry_over`); the
failing occurrence of the guarded program is of the same kind, an assertion or a cover, as that
of the list (`wpEntry_overK`).

Key theorems: `wpEntry_overK`, `wpEntry_over`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P]
  [HasFvar P] [HasSubstFvar P] [HasIdent P] [LawfulHasIdent P] [Hashable P.Ident] [HasFvars P]
  [WPLang P] [iIL : WPIteLang P] [HasOps P] [LawfulHasFvar P] [LawfulHasFvars P] [LawfulHasVal P]
omit iIL

include iIL in
/-- **The WP phase over-approximates, keeping the kind of the failing check.**  If the loop-free
    list `ss`, well scoped from `S`, has a reach from the store `σ` whose off-path runs exist
    (`DReach`) and whose trace `tr` fails the target `t` on a feasible path at an event of kind `k`
    with the condition `e` (`ClaimK`: a cover when `k` is `true`, an assertion when `k` is
    `false`), then its guarded program `w.lay` (`wpEntry`, with the free-variable types `tys`) has
    a reach from the same store whose trace fails `t`, at an event of kind `k`, with the condition
    `e` with its free variables renamed by `wsub` (each pair of `wsub` a free variable of `e` and
    the WP name of a renamed local, `w.back` mapping it back), and the skeleton has a slot for the
    label.  Hypotheses on the list:
    every variable of `S` of the form of a fresh name is a free variable with a type in `tys`, and
    the expressions of the list are typed under the types `tys` of its free variables
    (`Block.ExprsTyped`, for the typing predicate of `tE`).
    Hypotheses on the store: the variables of `S` the list reads are defined, the locals outside
    `S` are not, the store binds only variables of `S` the list reads, holds values, and those
    have their types in `tys` (`TyOK`).  Hypotheses on the factory: the mainline evaluator laws
    for variables, values, agreement on free variables and renaming. -/
theorem wpEntry_overK {F : P.Factory} (hVar : WellFormedSemanticEvalVar (P := P) F)
    (hVal : WellFormedSemanticEvalVal (P := P) F)
    (hCongr : WellFormedSemanticEvalExprCongr (P := P) F)
    (hRen : WellFormedSemanticEvalRename (P := P) F) {G : IdSet P} {tys : Tys P}
    {ss : PStmts P} {w : WOut P} (h : wpEntry G tys ss = .ok w) {Lc S : List P.Ident}
    (hwf : Block.WellScoped Lc S ss)
    (hSI : ∀ x ∈ S, ∀ b k, x = freshName b k → x ∈ tys.map (·.1))
    {σ : SemanticStore P} (hdef : ∀ x ∈ S, x ∈ contFV [ss] → (σ x).isSome)
    (hundef : ∀ x ∈ Lc, x ∉ S → σ x = none)
    (hdom : SemanticStore.DomIn σ (S.filter fun x => (contFV [ss]).contains x))
    (hC : WellFormedStore σ F)
    (hty : TyOK F tys S (contFV [ss]) σ) {tE : TypedEval P}
    (htyp : Block.ExprsTyped tE.Typ (fun x => tys.get? x) ss)
    {tr : List (Event P)} (hR : DReach F ss σ tr)
    {t : AssertId P} {e : P.Expr} {k : Bool} (hc : ClaimK k t e tr) :
    ∃ wsub : List (P.Ident × P.Ident × Option P.Ty),
      (∀ q ∈ wsub, w.back.lookup q.2.1 = some q.1 ∧ q.1 ∈ exprFV e) ∧ SkObl t.label w.sk ∧
      ∃ tr', BReach F w.lay σ tr' ∧ ClaimK k t (substObl wsub e) tr' := by
  have hF : WellFormedSemanticEvalBase F := ⟨hVar, hVal, hCongr, hRen⟩
  have hav : ∀ x ∈ S ++ Block.idents ss, ∀ b k, x = freshName b k →
      (inputAvoid G tys ss).contains x = true := fun x hx b k hb => by
    grind [inputAvoid, AvoidSet.contains, IdSet.ofList]
  simp only [wpEntry, wpBody, Except.bind_is_ok, Except.pure_is_ok] at h
  obtain ⟨⟨r, st1⟩, h1, lay, h2, rfl⟩ := h
  obtain ⟨items, hr, -⟩ := (Except.bind_is_ok _ _ _).1 h2
  obtain ⟨hcur, hav1, htys⟩ := wpList_top_facts hwf ⟨rfl, rfl, rfl, rfl⟩
    (fun x hx => hav x (List.mem_append_left _ hx)) h1
  have htn := wpList_top_tyOfName hwf ⟨rfl, rfl, rfl, rfl⟩
    (fun x hx => hav x (List.mem_append_left _ hx)) h1
  have hS : ∀ x, (σ x).isSome → x ∈ S ∧ x ∈ contFV [ss] := fun x hx => by simpa using hdom x hx
  have hcx : ∀ x ∈ S, ∀ n, curName st1 x = some n → n = x :=
    fun x hx n hn => Option.some.inj (hn.symm.trans (hcur x hx).1)
  have hOn : OnInv F st1.tys st1.tyOf Lc (fun _ => False) st1 .top S (contFV [ss]) σ σ := by
    refine ⟨⟨fun x hx _ n hn _ => hcx x hx n hn ▸ rfl,
      fun x hx hv => ⟨hdef x hx hv, fun n hn => hcx x hx n hn ▸ hdef x hx hv⟩,
      fun x hx _ n hn _ w w' h1 h2 _ => (by grind), hundef, hC, hC, fun n w hw _ ty hn => ?_,
      fun x hx hv n hn w hw ty ht => ?_, fun y hy => by grind⟩, trivial⟩
    · have hn' := hS n (by simp [hw])
      exact hty n hn'.1 hn'.2 ty (htys n hn'.1 ty hn) w hw
    · exact hty x hx hv ty (htys x hx ty (hcx x hx n hn ▸ ht)) w hw
  obtain ⟨-, hsk, wsub, hq, tr, hh, hc⟩ := (listSpec_all hF Lc ss .top 0 false (fun _ => rfl) _ _ _
    (by constructor
        case tys_keys =>
          grind [TyKey, inputAvoid, AvoidSet.contains, IdSet.ofList, → foldr_insert_key]
        all_goals simp) h1 _ _
    ⟨fun _ _ => .inl, fun _ _ => id, fun _ => .inl⟩ items hr S hwf (fun x => tys.get? x)
    (fun _ x hx ty hty n hn => hcx x hx n hn ▸ htn x hx ty hty) htyp hav (fun _ => False) nofun []
    (fun _ => []) (by simp) (by simp [RE.vars]) (fun _ _ h => by simp at h) (liveKeys_empty rfl)
    (by simp)).1 σ σ _ _ _ _ hOn hR hc
  refine ⟨wsub, fun q hq' => ⟨?_, (hq q hq').2⟩, hsk, fails_of_emitK h2 hr hh hc⟩
  have hd := st1.back.distinct_keys_toList
  obtain ⟨l1, l2, he⟩ := List.append_of_mem
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.2 (hq q hq').1)
  rw [he] at hd ⊢
  grind [List.lookup_eq_some_iff]

include iIL in
/-- **The WP phase over-approximates.**  If the loop-free list `ss`, well scoped from `S`, fails the
    target `t` from the store `σ` along a run whose off-path runs exist, at an occurrence whose
    condition is `e` (`FailsD`), then its guarded program `w.lay` (`wpEntry`, with the
    free-variable types `tys`) fails `t`, from the same store, at an occurrence whose condition is
    `e` with its free variables renamed by `wsub` (each pair of `wsub` a free variable of `e` and
    the WP name of a renamed local, `w.back` mapping it back), and the skeleton has a slot for the
    label.  Hypotheses: those of `wpEntry_overK`. -/
theorem wpEntry_over {F : P.Factory} (hVar : WellFormedSemanticEvalVar (P := P) F)
    (hVal : WellFormedSemanticEvalVal (P := P) F)
    (hCongr : WellFormedSemanticEvalExprCongr (P := P) F)
    (hRen : WellFormedSemanticEvalRename (P := P) F) {G : IdSet P} {tys : Tys P}
    {ss : PStmts P} {w : WOut P} (h : wpEntry G tys ss = .ok w) {Lc S : List P.Ident}
    (hwf : Block.WellScoped Lc S ss)
    (hSI : ∀ x ∈ S, ∀ b k, x = freshName b k → x ∈ tys.map (·.1))
    {σ : SemanticStore P} (hdef : ∀ x ∈ S, x ∈ contFV [ss] → (σ x).isSome)
    (hundef : ∀ x ∈ Lc, x ∉ S → σ x = none)
    (hdom : SemanticStore.DomIn σ (S.filter fun x => (contFV [ss]).contains x))
    (hC : WellFormedStore σ F)
    (hty : TyOK F tys S (contFV [ss]) σ) {tE : TypedEval P}
    (htyp : Block.ExprsTyped tE.Typ (fun x => tys.get? x) ss) {t : AssertId P} {e : P.Expr}
    (hfail : FailsD F ss σ t e) :
    ∃ wsub : List (P.Ident × P.Ident × Option P.Ty),
      (∀ q ∈ wsub, w.back.lookup q.2.1 = some q.1 ∧ q.1 ∈ exprFV e) ∧
      SkObl t.label w.sk ∧ Fails F w.lay σ t (substObl wsub e) := by
  obtain ⟨evs, ev, hR, hA, hFe, -⟩ := hfail
  obtain ⟨_, hk⟩ := Claim.kind ⟨evs, ev, rfl, hA, hFe⟩
  obtain ⟨wsub, hq, hsk, _, hb, hc⟩ :=
    wpEntry_overK hVar hVal hCongr hRen h hwf hSI hdef hundef hdom hC hty htyp hR hk
  obtain ⟨evs', _, rfl, hf, hfe⟩ := hc.claim
  exact ⟨wsub, hq, hsk, evs', _, hb, hf, hfe⟩

end -- public section

end WP
end Imperative
