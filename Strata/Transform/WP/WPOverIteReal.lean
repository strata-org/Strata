/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
import Strata.Transform.WP.WPOverEmit
import Strata.Transform.WP.WPOverEval
import Strata.Transform.WP.WPOverFacts
import Strata.Util.ExceptProps

/-! The simulation through real branches

The walk of an `ite` after which no obligation follows (a real branch, each arm at top level)
has the simulation property (`Spec`) when the walks of its arms have it.

Key theorems: `iteRealSpec`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P]
  [iWL : WPLang P] [iIL : WPIteLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iIL
variable {F : P.Factory} {Tm : Std.HashMap P.Ident P.Ty} {Ym : Std.HashMap P.Ident P.Ident}
  {Lc S V V' : List P.Ident} {Ex : P.Ident → Prop} {sa : WSt P} {κ : RE P} {σ σL : SemanticStore P}
variable {tE : TypedEval P}

/-- The state after the arms of a real branch: the state after the then arm with the label
    depths and pending exits of the state before the walk and the union of the live sets. -/
private def joinSt (st s2 s4 : WSt P) : WSt P :=
  { s4 with labelDepth := st.labelDepth, pending := st.pending,
            live := unionLive (unionLive s4.live s2.live) st.live }

/-- The new renamings and back-map entries of a run of `wRen e` from `st` to `st'` are fresh
    names with counters from `st.next` up to `st'.next`, not avoided: a renaming of `st'` is one
    of `st` or such a name, and the back map is unchanged at the other names. -/
private def RenFresh (st s : WSt P) : Prop :=
  s = { st with next := s.next, nm := s.nm, back := s.back } ∧ st.next ≤ s.next ∧
  (∀ x y : P.Ident, s.nm[x]? = some y →
    st.nm[x]? = some y ∨ ∃ b j, y = freshName b j ∧ st.next ≤ j ∧ j < s.next) ∧
  ∀ m : P.Ident, (∀ b j, m = freshName b j → st.avoid.contains m = false → j < st.next) →
    s.back[m]? = st.back[m]?

omit iLV iOp iLF iLFs in
/-- A run of `wRen e` keeps `RenFresh`. -/
private theorem wRen_fresh {e : P.Expr} {st st' : WSt P} {x : WExpr P × List P.Ident}
    (h : (wRen e).run st = .ok (x, st')) : RenFresh st st' := by
  unfold wRen at h
  obtain ⟨r, s1, hl, h⟩ := wm_run_bind_ok h
  cases h
  refine wm_forIn_inv (fun _ _ s => RenFresh st s) _ ?_ _ [] _ st r st'
    ⟨rfl, Nat.le_refl _, fun _ _ h => .inl h, fun _ _ => rfl⟩ hl
  intro _ y b s b' s' ⟨h1, h2, h3, h4⟩ hb
  obtain ⟨n, s2, hn, hb⟩ := wm_run_bind_ok hb
  have hs2 : RenFresh st s2 := by
    rcases wName_cases hn with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hn', rfl⟩
    iterate 2 exact ⟨h1, h2, h3, h4⟩
    obtain ⟨k, hk, hle, hav⟩ := freshIn_spec s.avoid (baseOf y) s.next
    rw [hk] at hn' ⊢
    subst hn'
    refine ⟨by rw [h1], show st.next ≤ k + 1 by omega, fun x z hz => by grind, fun m hm => ?_⟩
    grind [h4 m hm]
  split at hb <;> cases hb <;> exact ⟨_, rfl, hs2⟩
omit iLV iOp iLF iLFs in
/-- `OnInv` at the point after an arm of a real branch (walk output state `sa`, top level) from
    `OnInv` at the point after the branch (walk output state `so`), when the current names of
    the variables in scope, the live set and the recorded declarations of `sa` are kept in `so`,
    the renamings of `so` are renamings of `sa` or fresh names from `sa.next` on, and the
    counter and the avoided names agree. -/
private theorem onInv_arm {so : WSt P} (h : OnInv F Tm Ym Lc Ex so κ S V σ σL) (hV : V' ⊆ V)
    (hcur : ∀ x ∈ S, ∀ n, curName sa x = some n → curName so x = some n)
    (hlive : ∀ n, sa.live.contains n = true → so.live.contains n = true)
    (htaken : ∀ y, sa.taken.contains y = true → so.taken.contains y = true)
    (hnm : ∀ x y : P.Ident, so.nm[x]? = some y → (∃ z : P.Ident, sa.nm[z]? = some y) ∨
      ∃ b j, y = freshName b j ∧ sa.next ≤ j) (hnext : sa.next ≤ so.next)
    (havoid : sa.avoid = so.avoid) : OnInv F Tm Ym Lc Ex sa .top S V' σ σL := by
  obtain ⟨⟨ha, hd, hal, hu, hc, hcl, hg, hlt, hf⟩, -⟩ := h
  refine ⟨⟨fun x hx hv n hn hl => ha x hx (hV hv) n (hcur x hx n hn) (hlive n hl),
    fun x hx hv => ⟨(hd x hx (hV hv)).1, fun n hn => (hd x hx (hV hv)).2 n (hcur x hx n hn)⟩,
    fun x hx hv n hn => hal x hx (hV hv) n (hcur x hx n hn), hu, hc, hcl, hg,
    fun x hx hv n hn => hlt x hx (hV hv) n (hcur x hx n hn), fun y hy => ?_⟩, trivial⟩
  grind [FreshInv, freshName_counter_inj]

omit iLI iOp iLF iLFs in
/-- `OnInv` at top level survives binding the guard `g`, unbound before, to a Boolean `v` of
    every final declared type of `g`, when `g` is a fresh name that is not avoided, from the
    counter on, a renaming or excepted. -/
private theorem onInv_guard (h : OnInv F Tm Ym Lc Ex sa .top S V σ σL) {g : P.Ident} {v : P.Val}
    (hg0 : σL g = none) (hv : v = HasBool.ttVal F ∨ v = HasBool.ffVal F)
    (hgty : ∀ ty, tyOfName Tm Ym g = .ok ty → HasVal.valueOfTy F v ty)
    (hga : ∃ b j, g = freshName b j ∧ sa.avoid.contains g = false)
    (hgf : ∀ b j, g = freshName b j → sa.avoid.contains g = false →
      sa.next ≤ j ∨ (∃ x : P.Ident, sa.nm[x]? = some g) ∨ Ex g) :
    OnInv F Tm Ym Lc Ex sa .top S V σ (σL.update g v) := by
  obtain ⟨⟨hag, hde, hal, hun, hca, hcL, hgt, hlt, hfr⟩, -⟩ := h
  obtain ⟨u1, u2⟩ := update_facts σL g v
  have hne : ∀ x ∈ S, x ∈ V → ∀ n, curName sa x = some n → σL.update g v n = σL n :=
    fun x hx hv n hn => u2 n fun he => by simpa [← he, hg0] using (hde x hx hv).2 n hn
  refine ⟨⟨fun x hx hv n hn hl => (hne x hx hv n hn).trans (hag x hx hv n hn hl),
    fun x hx hv => ⟨(hde x hx hv).1, fun n hn => hne x hx hv n hn ▸ (hde x hx hv).2 n hn⟩,
    fun x hx hv n hn hty w w' hw hw' => hal x hx hv n hn hty w w' hw (hne x hx hv n hn ▸ hw'),
    hun, hca, wfStore_update_bool hcL g hv, ?_, hlt, ?_⟩, trivial⟩
  all_goals grind [SemanticStore.update, FreshInv]

omit iLV iLB iHI iLI iOp iLF iLFs in
/-- A resolved real branch is the branch of the resolved arms. -/
private theorem resolveItem_branch_inv {t e : List (WItem P)} {it : Item P}
    (h : resolveItem Tm Ym (.branch t e) = .ok it) :
    ∃ it' ie, resolveItems Tm Ym t = .ok it' ∧ resolveItems Tm Ym e = .ok ie ∧
      it = .branch it' ie := by grind [resolveItem, Except.bind_is_ok, Except.pure_is_ok]

omit iLFs in
include iIL in
/-- The walk of an `ite` after which no obligation follows (a real branch) has the simulation
    property when the walks of its arms (at the same depth, at top level, no obligation following
    them) have it. -/
theorem iteRealSpec {F : P.Factory} (hF : WellFormedSemanticEvalBase F) {Lc : List P.Ident}
    {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P} (md : MetaData P)
    (hT : ListSpec F tE Lc .top d false tss) (hE : ListSpec F tE Lc .top d false ess) :
    Spec F tE Lc κ d (wpIteReal κ d c tss ess) [.ite (.det c) tss ess md]
      (fun S => Stmt.WellScoped Lc S (.ite (.det c) tss ess md)) false
      (DReachS F (.ite (.det c) tss ess md))
      (fun X => DRunS F X (.ite (.det c) tss ess md)) (ShS F (.ite (.det c) tss ess md)) := by
  rintro st r st' hwf hrun Tm Ym hfin items hres S ⟨hSc, hwT, hwE⟩
    Γ hΓ hwt hav Ex hEx k Lab _ _ hD _ hhigh
  refine ⟨fun σ σL t cnd b tr hOn hreach hclaim => ?_, nofun, nofun⟩
  simp only [wpIteReal, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_modify,
    pure_bind, Except.bind_is_ok] at hrun
  obtain ⟨⟨E, s2⟩, hE', ⟨T, s4⟩, hT', h⟩ := hrun
  have wE := wpList_walkOK hE'
  have wT := wpList_walkOK hT'
  have hD1 : DeadBelow { st with live := {}, labelDepth := {}, pending := {} } := hD
  have hD3 : DeadBelow { s2 with live := {} } := (wpList_deadBelow hE' hD1 :)
  have hmem : ∀ x, x ∈ S ++ Block.idents tss ∨ x ∈ S ++ Block.idents ess →
      x ∈ S ++ Block.idents [.ite (.det c) tss ess md] := fun x hx => by
    grind [Block.idents, Stmt.idents]
  have hwf1 : WFSt { st with live := {}, labelDepth := {}, pending := {} } :=
    { hwf with pending_fresh := fun l e h => by simp at h, live_stamp := fun n s h => by simp at h }
  have hwf2 := wE.wf hwf1 fun x hx b j hxj =>
    hav x (hmem x (.inr (List.mem_append_right _ (wfl_inits_scope ess hwE hx).2.1))) b j hxj
  have hwf3 : WFSt { s2 with live := {} } := { hwf2 with live_stamp := fun n s h => by simp at h }
  have hwf4 := wT.wf hwf3 fun x hx b j hxj => wE.avoid ▸
    hav x (hmem x (.inl (List.mem_append_right _ (wfl_inits_scope tss hwT hx).2.1))) b j hxj
  have hobl : T.hasObl = true ∨ E.hasObl = true := by
    cases hreach with
    | ite_true _ hd => exact .inl (wpList_hit_hasObl hT' hD3 hd hclaim.claim)
    | ite_false _ hd _ => exact .inr (wpList_hit_hasObl hE' hD1 hd hclaim.claim)
  split at h
  · next hc => exact absurd hobl (by simpa using hc)
  simp only [StateT.run_bind, StateT.run_pure, Except.bind_is_ok, wFreshBool_run,
    Except.ok.injEq] at h
  obtain ⟨⟨⟨wc, rdc⟩, s6⟩, h6, _, rfl, ⟨_, s8⟩, h8, h9⟩ := h
  obtain ⟨live, clock, hlr, hl, -⟩ := liveAdd_run (rdc ++ RE.vars κ) _
  cases hlr.symm.trans h8
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h9
  obtain ⟨rfl, hst'⟩ := h9
  generalize hg : (freshIn s6.avoid "g" s6.next).1 = g at *
  obtain ⟨⟨ren, hwc, hren1, hren2, -⟩, -, -, hkeep⟩ := wRen_run h6
  obtain ⟨hs6, hn6, hnm6, hb6⟩ := wRen_fresh h6
  obtain ⟨kg, hk, hle, hav6⟩ := freshIn_spec s6.avoid "g" s6.next
  have hgk : g = freshName "g" kg := by rw [← hg, hk]
  have ha6 : s6.avoid = s4.avoid := by rw [hs6]
  have hgav : s4.avoid.contains g = false := by rw [hgk, ← ha6]; exact hav6
  have hlt : s4.next ≤ kg := Nat.le_trans hn6 hle
  have post : (∀ x n, curName (joinSt st s2 s4) x = some n → curName st' x = some n) ∧
      (∀ n, (joinSt st s2 s4).live.contains n = true → st'.live.contains n = true) ∧
      st'.taken = s4.taken ∧
      (∀ x y : P.Ident, st'.nm[x]? = some y →
        s4.nm[x]? = some y ∨ ∃ b j, y = freshName b j ∧ s4.next ≤ j) ∧
      s4.next ≤ st'.next ∧ st'.avoid = s4.avoid ∧
      (∀ m y : P.Ident, s4.back[m]? = some y → st'.back[m]? = some y) ∧
      (∀ (n : P.Ident) ty, s4.tys[n]? = some ty → st'.tys[n]? = some ty ∨
        ∃ b j, n = freshName b j ∧ s4.next ≤ j ∧ s4.avoid.contains n = false) ∧
      st'.tyOf = s4.tyOf := by
    subst hst'
    refine ⟨fun x n h => hkeep x n h, fun n h => (hl n).2 (.inl (by rw [hs6]; exact h)),
      by rw [hs6], fun x y h => (hnm6 x y h).imp_right fun ⟨b, j, hj, hj1, _⟩ => ⟨b, j, hj, hj1⟩,
      hk ▸ Nat.le_succ_of_le hlt, ha6, fun m y h => ?_, fun n ty h => ?_, by rw [hs6]⟩
    · obtain ⟨b', j', hm', hj'⟩ := hwf4.back_fresh m y h
      exact (hb6 m fun b j hm _ => freshName_counter_inj (hm.symm.trans hm') ▸ hj').trans h
    · have ht6 : s6.tys = s4.tys := by rw [hs6]
      exact (Classical.em (n = g)).elim (fun he => .inr ⟨"g", kg, he ▸ hgk, hlt, he ▸ hgav⟩)
        fun hn => .inl (by simp [Std.HashMap.getElem?_insert, Ne.symm hn, ht6, h])
  obtain ⟨pcur, plive, ptaken, pnm, pnext, pavoid, pback, ptys, ptyOf⟩ := post
  have hfT : FinalOK Lc s4 Tm Ym := by
    have hl : ∀ n : P.Ident, (∃ b j, n = freshName b j ∧ st'.next ≤ j ∧
        st'.avoid.contains n = false) →
        ∃ b j, n = freshName b j ∧ s4.next ≤ j ∧ s4.avoid.contains n = false :=
      fun _ ⟨b, j, h1, h2, h3⟩ => ⟨b, j, h1, Nat.le_trans pnext h2, pavoid ▸ h3⟩
    exact ⟨fun n ty h => (ptys n ty h).elim (fun h => (hfin.1 n ty h).imp_right
        (.imp (fun ⟨h1, h2, h3⟩ => ⟨h1, pavoid ▸ h2, ptaken ▸ h3⟩) (hl n))) (.inr ∘ .inr),
      fun n x h => hfin.2.1 n x (ptyOf ▸ h), fun n h => (hfin.2.2 n h).imp (ptyOf ▸ ·) (hl n)⟩
  subst hst'
  have hn2 : st.next ≤ s2.next := wE.next
  have hn4 : s2.next ≤ s4.next := wT.next
  have hfE : FinalOK Lc s2 Tm Ym :=
    ⟨fun n ty h => wT.tys_final hwf3 (fun x hx => ⟨(wfl_inits_scope tss hwT hx).1,
      fun b j hxj => wE.avoid ▸ hav x (hmem x (.inl (List.mem_append_right _
        (wfl_inits_scope tss hwT hx).2.1))) b j hxj⟩) hfT.1 h,
      fun n x h => hfT.2.1 n x (wT.tyOf_keep hwf3 h), fun n h => (hfT.2.2 n h).elim
        (fun h => (Classical.em (s4.tyOf[n]? = s2.tyOf[n]?)).elim (.inl <| · ▸ h) fun he =>
          (wT.tyOf n he).elim fun b ⟨j, h4, h5, h6⟩ => .inr ⟨b, j, h4, h6, h5⟩)
        fun ⟨b, j, h4, h5, h6⟩ => .inr ⟨b, j, h4, Nat.le_trans hn4 h5, wT.avoid ▸ h6⟩⟩
  have hOnT : OnInv F Tm Ym Lc Ex s4 .top S (contFV (tss :: k)) σ σL :=
    onInv_arm hOn (fun x hx => mem_contFV_cons.2 ((mem_contFV_cons.1 hx).imp_left
      fun h => by simp [Block.freeVars, Stmt.freeVars, h]))
      (fun x _ n h => pcur x n h)
      (fun n h => plive n (unionLive_contains.2 (.inl (unionLive_contains.2 (.inl h)))))
      (fun y h => ptaken ▸ h) (fun x y h => (pnm x y h).imp (fun h => ⟨x, h⟩) id) pnext
      pavoid.symm
  have hOnE : OnInv F Tm Ym Lc Ex s2 .top S (contFV (ess :: k)) σ σL :=
    onInv_arm hOn (fun x hx => mem_contFV_cons.2 ((mem_contFV_cons.1 hx).imp_left
      fun h => by simp [Block.freeVars, Stmt.freeVars, h]))
      (fun x hx n h => pcur x n (wT.names x n (fun hd => (wfl_inits_scope tss hwT hd).2.2 hx) h))
      (fun n h => plive n (unionLive_contains.2 (.inl (unionLive_contains.2 (.inr h)))))
      (fun y h => ptaken ▸ wT.taken y h)
      (fun x y h => (pnm x y h).elim (fun h => (wT.nm x y h).imp (⟨x, ·⟩)
        fun ⟨b, j, hj, _, hj'⟩ => ⟨b, j, hj, hj'⟩) fun ⟨b, j, hj, hj'⟩ => .inr ⟨b, j, hj, by omega⟩)
      (by omega) (by rw [pavoid, wT.avoid])
  have hg0 : σL g = none := Option.eq_none_iff_forall_ne_some.2 fun w hσg => by
    obtain ⟨-, h2⟩ := hOn.fresh g (by simp [hσg])
    rcases h2 "g" kg hgk (by rw [pavoid]; exact hgav) with h | ⟨x, hx⟩ | hx
    · exact Nat.not_succ_le_self kg (by simpa only [hk] using h)
    · obtain ⟨-, b, j, hj, hl, -⟩ | ⟨b, j, hj, -, hl⟩ := (hnm6 x g hx).imp_left (hwf4.nm_fresh x g)
      all_goals exact absurd (freshName_counter_inj (hgk.symm.trans hj)) (by omega)
    · exact absurd ((hEx g hx).1 "g" kg hgk) (by omega)
  have hTg : Tm[g]? = some HasBool.boolTy :=
    (hfin.1 g _ (by show (s6.tys.insert g HasBool.boolTy)[g]? = _; simp)).resolve_right
      (by grind [→ freshName_counter_inj])
  have hgty : ∀ v, v = HasBool.ttVal F ∨ v = HasBool.ffVal F → ∀ ty, tyOfName Tm Ym g = .ok ty →
      HasVal.valueOfTy F v ty := fun v hv ty h =>
    Except.ok.inj (by simpa only [tyOfName, hTg, pure, Except.pure] using h) ▸ bool_valueOfTy hv
  have hcev : ∀ v, P.eval F σ c = some v → ∀ a', resolveE Tm Ym wc = .ok a' →
      P.eval F σL a' = some v := fun v hv a' ha' => by
    rw [hwc] at ha'
    have hag := fun y hy n hn (hnr : n ∈ rdc) => hOn.agree y (hSc y hy) (ite_cond_fv y hy) n hn
      ((hl n).2 (.inr (List.mem_append_left _ hnr)))
    refine (ev_resolveE_user hF hOn.canon hOn.canonL ha' ?_ ?_).trans hv
    · intro p hp
      obtain ⟨hp1, hp2, -⟩ := hren1 p hp
      obtain ⟨n, hn, hnr, -⟩ := hren2 p.1 hp1
      cases Option.some.inj (hn.symm.trans hp2)
      exact ⟨hag p.1 hp1 _ hp2 hnr, (hOn.defd p.1 (hSc p.1 hp1) (ite_cond_fv p.1 hp1)).1⟩
    · intro y hy hne
      obtain ⟨n, hn, hnr, h⟩ := hren2 y hy
      exact h.elim (· ▸ hag y hy _ hn hnr) fun hny => absurd rfl (hne _ hny)
  cases hreach
  case' ite_true hc hd =>
    have hAo := wpList_hit_hasObl hT' hD3 hd hclaim.claim
    have hOnA := onInv_guard hOnT hg0 (.inl rfl) (hgty _ (.inl rfl)) ⟨"g", kg, hgk, hgav⟩
      (fun b j hj _ => .inl (freshName_counter_inj (hgk.symm.trans hj) ▸ hlt))
    have hitA := fun itemsA hr => ((hT fun _ => rfl) _ _ _ hwf3 hT' Tm Ym hfT itemsA hr S hwT Γ
      (fun _ => (hΓ (.inr (by simp))).back fun x _ n h => pcur x n h) hwt.ite.2.2.1
      (fun x hx b j hxj => wE.avoid ▸ hav x (hmem x (.inl hx)) b j hxj)
      Ex (fun y hy => ⟨fun b j hj => Nat.lt_of_lt_of_le ((hEx y hy).1 b j hj) hn2,
        Option.eq_none_iff_forall_ne_some.2 fun v h =>
          nomatch (pback y v h).symm.trans (hEx y hy).2⟩)
      k Lab (fun l t' hl => by simp [wE.labelDepth] at hl) (fun _ h => by simp [RE.vars] at h)
      hD3 (liveKeys_empty rfl) (fun k hk => List.eq_nil_iff_forall_not_mem.2 fun q hm => by
        simpa [hhigh k hk] using wpList_carries_high hE' (fun l t h => by simp at h) k hk q hm)).1
    have hbA := pback
    obtain ⟨u1, u2⟩ := update_facts σL g (HasBool.ttVal F)
    generalize σL.update g (HasBool.ttVal F) = σg at hOnA u1 u2
    cases hEo : E.hasObl <;>
      simp only [hAo, hEo, Bool.and_false, Bool.and_self, Bool.false_eq_true, ite_false,
        ite_true] at hres
  case' ite_false hc _ hd =>
    have hAo := wpList_hit_hasObl hE' hD1 hd hclaim.claim
    have hOnA := onInv_guard hOnE hg0 (.inr rfl) (hgty _ (.inr rfl))
      ⟨"g", kg, hgk, by rw [← wT.avoid]; exact hgav⟩
      (fun b j hj _ => .inl (freshName_counter_inj (hgk.symm.trans hj) ▸ Nat.le_trans hn4 hlt))
    have hitA := fun itemsA hr => ((hE fun _ => rfl) _ _ _ hwf1 hE' Tm Ym hfE itemsA hr S hwE Γ
      (fun _ => (hΓ (.inr (by simp))).back fun x hx n h =>
        pcur x n (wT.names x n (fun hd => (wfl_inits_scope tss hwT hd).2.2 hx) h))
      hwt.ite.2.2.2 (fun x hx b j hxj => hav x (hmem x (.inr hx)) b j hxj)
      Ex (fun y hy => ⟨(hEx y hy).1, Option.eq_none_iff_forall_ne_some.2 fun v h =>
        nomatch (pback y v (wT.back_keep hwf3 h)).symm.trans (hEx y hy).2⟩)
      k Lab (fun l t' hl => by simp at hl) (fun _ h => by simp [RE.vars] at h)
      hD1 (liveKeys_empty rfl) hhigh).1
    have hbA := fun m y (h : s2.back[m]? = some y) => pback m y (wT.back_keep hwf3 h)
    obtain ⟨u1, u2⟩ := update_facts σL g (HasBool.ffVal F)
    have hκ' : κ.Holds F (σL.update g (HasBool.ffVal F)) := RE.Holds.mono hOn.reach fun x w h =>
      (u2 x (by rintro rfl; cases hg0.symm.trans h)).trans h
    generalize σL.update g (HasBool.ffVal F) = σg at hOnA u1 u2 hκ'
    cases hTo : T.hasObl <;>
      simp only [hAo, hTo, Bool.false_and, Bool.and_self, Bool.false_eq_true, ite_false,
        ite_true] at hres
  all_goals
    simp only [Rope.toList_app, Rope.toList_one, List.cons_append, List.nil_append] at hres
    obtain ⟨iG, l1, hiG, hl1, rfl⟩ := resolveItems_cons_ok hres
  case' ite_true.true | ite_false.true =>
    obtain ⟨iB, l2, hiB, hl2, rfl⟩ := resolveItems_cons_ok hl1
    simp only [resolveItems, pure, Except.pure, Except.ok.injEq] at hl2
    subst hl2
    clear hl1
  case' ite_true.true => obtain ⟨l1, be, hl1, -, rfl⟩ := resolveItem_branch_inv hiB
  case' ite_false.true => obtain ⟨bt, l1, -, hl1, rfl⟩ := resolveItem_branch_inv hiB
  all_goals
    obtain ⟨iA, itemsA, hiA, hiAs, rfl⟩ := resolveItems_cons_ok hl1
    obtain ⟨ge, hge, rfl⟩ := resolveItem_init_det hiG
    obtain ⟨ae, hae, rfl⟩ := resolveItem_assume hiA
    have hgev := ev_kAnd_holds hF hOn.canonL hOn.reach hge (hcev _ hc)
      (by first | exact .inl rfl | exact .inr rfl | (split <;> simp))
    have haev : P.eval F σg ae = some (HasBool.ttVal F) := by
      first
        | obtain ⟨ty, rfl⟩ := resolveE_var hae
          exact ev_var hF.var hOnA.canonL u1
        | refine ev_kAnd_holds hF hOnA.canonL hκ' hae (fun _ ha' => ev_not_ff hF ha' fun _ ha => ?_)
            (.inl rfl)
          obtain ⟨ty, rfl⟩ := resolveE_var ha
          exact ev_var hF.var hOnA.canonL u1
    obtain ⟨-, hskA, wsub, hw, trA, hhA, hclA⟩ := hitA itemsA hiAs σ σg t cnd b tr hOnA hd hclaim
    refine' ⟨rfl, ?_, wsub, fun q hq => ⟨hbA _ _ (hw q hq).1, (hw q hq).2⟩, _,
      .plain (EvalCmdE.eval_init hgev (.init hg0 u1 u2) (bool_valueOfTy ?_) hF.var) ?_, ?_⟩
  any_goals first
    | exact .iteT g E.sk [] hskA | exact .iteE g T.sk [] hskA
    | exact .branchT (.plain .eval_assume hhA) | exact .branchE (.plain .eval_assume hhA)
    | exact HitIn.plain EvalCmdE.eval_assume hhA | exact Or.inl rfl | exact Or.inr rfl
  all_goals exact claimK_prepend nofun (claimK_prepend
    (fun _ harg => Event.assume.inj (List.mem_singleton.mp harg) ▸ haev) hclA)

end -- public section

end WP
end Imperative
