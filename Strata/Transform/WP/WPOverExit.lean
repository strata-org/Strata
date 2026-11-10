/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
import Strata.Transform.WP.WPOverState
import Strata.Transform.WP.WPOverEval
import Strata.Transform.WP.WPOverEmit
import Strata.DL.Imperative.BigStep.SemProps

/-! # The simulation through exits

The walk of an `exit` has the simulation property (`Spec`).  Under `top` it emits nothing and
its exit leaves the region.  Under a variable reach context `κ` it emits `setReach κ false`,
preceded, when the label has a target block, by `init e := κ` for a fresh snapshot `e`
registered for the label: on the path the run binds `e` to true and makes `κ` false, off the
path it binds `e` to false and keeps `κ` false.

Key theorems: `stmtSpec_exit`. -/

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
variable {F : P.Factory} {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident} {κ : RE P}
  {σL : SemanticStore P}
omit iLB iHI iLI iOp iLF iLFs
variable {tE : TypedEval P}


omit iLV in
/-- The run of `setReach κ false` (`κ` not `top`) from a store where the variables of `κ` hold
    Booleans makes `κ` false, changes only the variables of `κ`, keeps them Boolean, and keeps
    the first variable of an `andNeg` context true. -/
private theorem setReach_run (hF : WellFormedSemanticEvalBase F) (hκ : κ ≠ .top) {items : List
    (Item P)} (hres : resolveItems T Y (setReach κ (.lit false)).toList = .ok items)
    (hB : ∀ y ∈ RE.vars κ, σL y = some (HasBool.ttVal F) ∨ σL y = some (HasBool.ffVal F)) :
    ∃ σL', MainRun F items σL [] σL' ∧ κ.Fails F σL' ∧ (∀ y, y ∉ RE.vars κ → σL' y = σL y) ∧
      (∀ y ∈ RE.vars κ, σL' y = some (HasBool.ttVal F) ∨ σL' y = some (HasBool.ffVal F)) ∧
      ∀ q g, κ = .andNeg q g → σL q = some (HasBool.ttVal F) → σL' q = some (HasBool.ttVal F) := by
  rcases κ with _ | r | g | ⟨q, g⟩
  · exact absurd rfl hκ
  all_goals rw [setReach, Rope.toList_one] at hres; cases hres
  all_goals
    refine ⟨_, set_run hF (by first | exact hF.val.eval_ff σL | exact hF.val.eval_tt σL)
      (hB _ (by simp [RE.vars])) (by simp), ?_⟩
    grind [SemanticStore.update, RE.vars, RE.Fails]

/-- A store that differs from a value-valued store of values of their final types only at the
    variables of `κ`, which hold Booleans in both, and at names satisfying `E` that hold `tt` or
    `ff` and have the Boolean type as final declared type, is value-valued with values of their
    final types, and binds only names the first store binds or that satisfy `E`. -/
private theorem bool_ext_typed {E : P.Ident → Prop} {σL' : SemanticStore P}
    (hC : WellFormedStore σL F)
    (hT : ∀ n w, σL n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty)
    (hB : ∀ y ∈ RE.vars κ, σL y = some (HasBool.ttVal F) ∨ σL y = some (HasBool.ffVal F))
    (hb : ∀ y ∈ RE.vars κ, σL' y = some (HasBool.ttVal F) ∨ σL' y = some (HasBool.ffVal F))
    (hu : ∀ y, y ∉ RE.vars κ → ¬ E y → σL' y = σL y)
    (hE : ∀ y w, E y → σL' y = some w →
      (w = HasBool.ttVal F ∨ w = HasBool.ffVal F) ∧ T[y]? = some HasBool.boolTy) :
    WellFormedStore σL' F ∧ (∀ n w, σL' n = some w → Y[n]? = none → ∀ ty,
      tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty) ∧
      ∀ y, (σL' y).isSome → (σL y).isSome ∨ E y := by
  have h : ∀ y w, σL' y = some w → σL y = some w ∨ ((w = HasBool.ttVal F ∨ w = HasBool.ffVal F) ∧
      ((σL y = some (HasBool.ttVal F) ∨ σL y = some (HasBool.ffVal F)) ∨
        T[y]? = some HasBool.boolTy)) := fun y w hw => by
    by_cases hy : y ∈ RE.vars κ <;> by_cases he : E y <;> grind
  refine ⟨fun y w hy => (h y w hy).elim (hC y w) fun hb =>
    LawfulHasVal.valueOfTy_isVal _ _ _ (bool_valueOfTy hb.1), fun n w hn hY ty hty => ?_,
    fun y hy => ?_⟩
  · rcases h n w hn with h1 | ⟨hb, hb0 | hT0⟩
    · exact hT n w h1 hY ty hty
    · rcases hb0 with hb0 | hb0 <;> exact LawfulHasVal.valueOfTy_congr _ _ _ _ _
        (hT n _ hb0 hY ty hty) (bool_valueOfTy (by simp)) (bool_valueOfTy hb)
    · simp only [tyOfName, hT0] at hty
      exact Except.ok.inj hty ▸ bool_valueOfTy hb
  · by_cases hy' : y ∈ RE.vars κ <;> by_cases he : E y <;> grind

omit iLV in
/-- The run of `init e := κ` then `setReach κ false` (`κ` not `top`, `e` unbound, the
    variables of `κ` Boolean, `κ` evaluating to the Boolean `v`) binds `e` to `v`, makes `κ`
    false, keeps its variables Boolean and the first variable of an `andNeg` context true, and
    changes nothing else. -/
private theorem snap_run (hF : WellFormedSemanticEvalBase F) (hκ : κ ≠ .top) {e : P.Ident}
    {items : List (Item P)}
    (hres : resolveItems T Y ((Rope.one (.init e (.known HasBool.boolTy) (some (kExpr κ)))).app
      (setReach κ (.lit false))).toList = .ok items) (he : σL e = none)
    (hB : ∀ y ∈ RE.vars κ, σL y = some (HasBool.ttVal F) ∨ σL y = some (HasBool.ffVal F))
    {v : P.Val} (hv : v = HasBool.ttVal F ∨ v = HasBool.ffVal F)
    (hx : ∀ x, resolveE T Y (kExpr κ) = .ok x → P.eval F σL x = some v) :
    ∃ σL', MainRun F items σL [] σL' ∧ κ.Fails F σL' ∧ σL' e = some v ∧
      (∀ y, y ∉ RE.vars κ → y ≠ e → σL' y = σL y) ∧
      (∀ y ∈ RE.vars κ, σL' y = some (HasBool.ttVal F) ∨ σL' y = some (HasBool.ffVal F)) ∧
      ∀ q g, κ = .andNeg q g → σL q = some (HasBool.ttVal F) → σL' q = some (HasBool.ttVal F) := by
  simp only [Rope.toList_app, Rope.toList_one, List.singleton_append] at hres
  obtain ⟨i, il, hi, hil, rfl⟩ := resolveItems_cons_ok hres
  obtain ⟨x, hx', rfl⟩ := resolveItem_init_det hi
  obtain ⟨σL', hr, hf, hu, hb, hq⟩ := setReach_run hF hκ hil (σL := σL.update e v)
    fun y hy => by grind [SemanticStore.update]
  refine ⟨σL', .plain (evs1 := []) (.eval_init (hx x hx') (.init he (update_facts σL e v).1
    (update_facts σL e v).2) (bool_valueOfTy hv) hF.var) hr, hf, ?_, ?_, hb, ?_⟩
  all_goals grind [SemanticStore.update]

include iLB iHI iLI in
omit iLV iWL in
/-- After a walk from a well-formed state that keeps the renamings, the type references and the
    avoided names, the current WP name of a variable of a scope whose fresh-form names are
    avoided has no type reference in final type maps `Y` whose keys are type references or
    names not yet drawn. -/
private theorem cur_noTyRef {st st' : WSt P} {S : List P.Ident} (hwf : WFSt st)
    (hS : ∀ x ∈ S, ∀ b j, x = freshName b j → st.avoid.contains x = true)
    (hY : ∀ n, (Y[n]?).isSome → (st'.tyOf[n]?).isSome ∨ ∃ b j, n = freshName b j ∧
      st'.next ≤ j ∧ st'.avoid.contains n = false) (hnm : st'.nm = st.nm)
    (htyOf : st'.tyOf = st.tyOf) (hnext : st.next ≤ st'.next) (havd : st'.avoid = st.avoid)
    {x n : P.Ident} (hx : x ∈ S) (hn : curName st' x = some n) : Y[n]? = none := by
  have hk := hwf.tyOf_keys
  have hn' := hwf.nm_fresh
  have hf := hwf.tyOf_fresh
  rcases curName_cases hn with h | ⟨-, -, rfl⟩ <;> grind [freshName_counter_inj]

include iLB iHI iLI iOp iLF iIL in
/-- The walk of an `exit` has the simulation property. -/
theorem stmtSpec_exit {F : P.Factory} (hF : WellFormedSemanticEvalBase F) (Lc : List P.Ident)
    (κ : RE P) (d : Nat) (f : Bool)
    (l : String) (md : MetaData P) : StmtSpec F tE Lc κ d f (.exit l md) := by
  intro st r st' hWF h T Y hFin items hres S hwf Γ hΓ hwt hav Ex hEx k Lab hLab hsep _ _ _
  refine ⟨fun σ σL t _ _ tr _ hR _ => (nomatch hR), ?_⟩
  rcases Classical.em (κ = .top) with rfl | hκ
  · exact ⟨fun _ _ _ _ _ _ _ hD _ => .inl ⟨rfl, by cases hD; exact ⟨_, _, rfl⟩⟩,
      fun _ σs σL K hO _ => hO.reach.elim⟩
  cases f
  · exact ⟨nofun, nofun⟩
  have hS : ∀ x ∈ S, ∀ b j, x = freshName b j → st.avoid.contains x = true :=
    fun x hx => hav x (List.mem_append_left _ hx)
  have hcur : ∀ x ∈ S, ∀ n, curName st x = some n → (∃ b j, n = freshName (P := P) b j) →
      st.avoid.contains n = false → (∀ z : P.Ident, st.nm[z]? ≠ some n) → False :=
    fun x hx n hn ⟨b, j, hb⟩ ha hz => (curName_cases hn).elim (hz x) fun ⟨_, _, he⟩ => by
      subst he; exact absurd (hS n hx b j hb) (by simp [ha])
  have hnk : ∀ x ∈ S, ∀ n, curName st x = some n → n ∉ RE.vars κ := fun x hx n hn hn' =>
    let ⟨⟨b, j, hb, _⟩, ha, hz, _⟩ := hsep n hn'
    hcur x hx n hn ⟨b, j, hb⟩ ha hz
  simp only [wpStmt, StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h <;> rename_i hl
  all_goals simp only [Bool.not_true, Bool.false_eq_true, ite_false, wFreshBool_run,
    StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind] at h
  · obtain ⟨live, clock, hL, hlive, -⟩ := liveAdd_run (RE.vars κ) { st with
      next := (freshIn st.avoid "r" st.next).2
      tys := st.tys.insert (freshIn st.avoid "r" st.next).1 HasBool.boolTy
      pending := st.pending.insert l ((freshIn st.avoid "r" st.next).1 :: st.pending.getD l []) }
    simp only [bind, Except.bind, hL, pure, Except.pure] at h
    obtain ⟨hr, hst⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨k0, hk, hn0, hav0⟩ := freshIn_spec st.avoid "r" st.next
    have hlt : ∀ b, (∃ j, freshName (P := P) "r" k0 = freshName b j ∧ j < st.next) → False :=
      fun _ ⟨_, he, hj⟩ => absurd (freshName_counter_inj he) (by omega)
    have hnm0 : ∀ x : P.Ident, st.nm[x]? ≠ some (freshName "r" k0) := fun x hx =>
      (hWF.nm_fresh x _ hx).2.elim fun b ⟨j, he, hj, _⟩ => hlt b ⟨j, he, hj⟩
    rename_i t
    simp only [hk] at hr hst hlive
    have hreg' : ∀ e, e ∈ r.regs.toList ↔ e = freshName "r" k0 := by simp [← hr, Rope.toList_one]
    have hpd : ∀ l', freshName "r" k0 ∈ (st.pending.insert l (freshName "r" k0 ::
        st.pending.getD l [])).getD l' [] → l' = l := fun l' h => Classical.byContradiction
      fun hl' => (hWF.pending_fresh l' _ <| by
        simpa [Std.HashMap.getD_insert, Ne.symm hl'] using h).elim hlt
    have hne : ∀ x ∈ S, ∀ n, curName st x = some n → n ≠ freshName (P := P) "r" k0 :=
      fun x hx n hn he => hcur x hx n hn ⟨"r", k0, he⟩ (he ▸ hav0) (he ▸ hnm0)
    have hfp : ∀ σL, FreshInv Lc Ex st' σL → σL (freshName "r" k0) = none ∧
        ∀ σL' : SemanticStore P, (∀ y, (σL' y).isSome → (σL y).isSome ∨ y = freshName "r" k0) →
          FreshInv Lc Ex st σL' := fun σL hf => by
      rw [← hst] at hf
      refine ⟨Option.not_isSome_iff_eq_none.1 fun hs => ?_, fun σL' hs y hy => ?_⟩
      · exact ((hf _ hs).2 "r" k0 rfl hav0).elim (absurd · (Nat.not_succ_le_self k0))
          fun h => h.elim (·.elim hnm0) fun h => Nat.not_le_of_lt ((hEx _ h).1 "r" k0 rfl) hn0
      · rcases hs y hy with hy | rfl
        · exact (hf y hy).imp id fun h b j hb ha => (h b j hb ha).imp_left
            fun h' => Nat.le_trans hn0 (Nat.le_of_succ_le h')
        · exact ⟨fun _ h => absurd (h "r" k0 rfl) (by simp [hav0]),
            fun b j hb _ => .inl (freshName_counter_inj hb ▸ hn0)⟩
    have hcr : ∀ k i n v xB, CarryReg r st' k i n v xB → False := fun k i n v xB h => by
      rw [← hst] at h
      exact (hWF.carries_fresh k i n v _ ((hreg' xB).1 h.2 ▸ h.1)).elim hlt
    subst hst hr
    have hTe : T[freshName (P := P) "r" k0]? = some HasBool.boolTy :=
      (hFin.1 _ _ (by simp)).resolve_right (by grind [→ freshName_counter_inj])
    refine ⟨fun _ σ σL X evs o hI hD _ => ?_, fun _ σs σL K hO hSh => ?_⟩
    · cases hD
      have hσe := (hfp σL hI.fresh).1
      obtain ⟨σL', hM, hfl, hσ', hu, hb, hq⟩ := snap_run hF hκ hres hσe (hI.reach.bools)
        (.inl rfl) fun x h => ev_kExpr_holds hF hI.canonL hI.reach h
      have hkeep : ∀ x ∈ S, ∀ n, curName st x = some n → σL' n = σL n :=
        fun x hx n hn => hu n (hnk x hx n hn) (hne x hx n hn)
      obtain ⟨hC', hT', hs⟩ := bool_ext_typed hI.canonL hI.gtyped hI.reach.bools hb hu
        (E := (· = freshName "r" k0)) fun _ w h hw => ⟨.inl (Option.some.inj
          (hw.symm.trans (h ▸ hσ'))), h ▸ hTe⟩
      have hfr := (hfp σL hI.fresh).2 σL' hs
      have hLV : ∀ x ∈ Lab l, x ∈ contFV ([.exit l md] :: k) :=
        fun x h => contFV_tail_sub ((hLab l t hl).2 x h).1
      refine .inr ⟨[], σL', hM, nofun, ⟨hC', hfl, hb, fun x hx hv n hn => ?_, hT', hfr⟩,
        ⟨fun h => by simp at h, fun l' e he hp hl' => ?_⟩,
        fun q g hqg => hq q g hqg (by subst hqg; exact hI.reach.1),
        fun _ _ _ _ _ h => (hcr _ _ _ _ _ h).elim, ?_⟩
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hI.defd x hx (contFV_tail_sub hv)).2 n hn)
        rw [← hkeep x hx n hn] at hw
        exact ⟨w, hw, hT' n w hw (cur_noTyRef hWF hS hFin.2.2 rfl rfl (.step hn0) rfl hx hn)⟩
      · exact absurd (hpd l' ((hreg' e).1 he ▸ hp)) fun h => hl' (h ▸ rfl)
      · simp only [hl]
        refine ⟨_, (hreg' _).2 rfl, by simp, hσ',
          fun _ e he _ hne' => absurd ((hreg' e).1 he ▸ rfl) hne',
          ⟨fun x hx hlab n hn hlv _ w hw => ⟨fun _ _ _ _ h => (hcr _ _ _ _ _ h).elim,
            .inl ⟨fun _ _ _ _ _ h => (hcr _ _ _ _ _ h).elim, (hkeep x hx n hn).trans
              ((hI.agree x hx (hLV x hlab) n hn ((hlive n).2 (.inl hlv))).trans hw)⟩⟩,
            fun x hx hlab => ⟨(hI.defd x hx (hLV x hlab)).1,
              fun n hn => hkeep x hx n hn ▸ (hI.defd x hx (hLV x hlab)).2 n hn⟩,
            fun x hx hlab n hn hty w w' hw hw' =>
              hI.alike x hx (hLV x hlab) n hn hty w w' hw ((hkeep x hx n hn) ▸ hw'),
            hI.undef, hI.canon, hC', hT', fun x hx hlab => hI.ltyped x hx (hLV x hlab), hfr⟩,
          fun _ _ _ _ _ _ h => (hcr _ _ _ _ _ h).elim⟩
    · have hσe := (hfp σL hO.fresh).1
      obtain ⟨σL', hM, hfl, hσ', hu, hb, hq⟩ := snap_run hF hκ hres hσe hO.bools
        (.inr rfl) fun x h => ev_kExpr_fails hF hO.canonL hO.reach hO.bools h
      obtain ⟨hC', hT', hs⟩ := bool_ext_typed hO.canonL hO.gtyped hO.bools hb hu
        (E := (· = freshName "r" k0)) fun _ w h hw => ⟨.inr (Option.some.inj
          (hw.symm.trans (h ▸ hσ'))), h ▸ hTe⟩
      have hfr := (hfp σL hO.fresh).2 σL' hs
      refine ⟨[], σL', hM, nofun, ?_, fun y hy hy' => hu y hy' fun h => by simp [h, hσe] at hy,
        fun _ e he _ _ => (hreg' e).1 he ▸ hσ', fun _ _ _ _ _ h => (hcr _ _ _ _ _ h).elim,
        fun _ _ _ _ _ h => (hcr _ _ _ _ _ h).elim, fun h => by simp at h,
        fun l' e he hp _ => ⟨σs, hpd l' ((hreg' e).1 he ▸ hp) ▸ hSh⟩⟩
      rw [ite_eq_left rfl]
      exact ⟨hC', hfl, hb, fun x hx hv n hn => (hO.defd x hx (contFV_tail_sub hv) n hn).imp
        fun _ h => ⟨(hu n (hnk x hx n hn) (hne x hx n hn)).trans h.1, h.2⟩, hT', hfr⟩
  · cases h
    have hnil : ∀ e, e ∉ ({ out := setReach κ (.lit false), ax := true } : WRes P).regs.toList := by
      simp [Rope.toList_nil]
    refine ⟨fun _ σ σL X evs o hI hD _ => ?_, fun _ σs σL K hO hSh => ?_⟩
    · cases hD
      obtain ⟨σL', hM, hfl, hu, hb, hq⟩ := setReach_run hF hκ hres (hI.reach.bools)
      obtain ⟨hC', hT', hs⟩ := bool_ext_typed hI.canonL hI.gtyped hI.reach.bools hb
        (E := fun _ => False) (fun y hy _ => hu y hy) fun _ _ h => h.elim
      refine .inr ⟨[], σL', hM, nofun, ⟨hC', hfl, hb, fun x hx hv n hn => ?_, hT', fun y hy =>
        hI.fresh y ((hs y hy).resolve_right id)⟩,
        ⟨fun h => by simp at h, fun _ e he => absurd he (hnil e)⟩,
        fun q g hqg => hq q g hqg (by subst hqg; exact hI.reach.1),
        fun _ _ _ _ _ h => absurd h.2 (hnil _),
        by simp only [hl]; exact fun _ e he => absurd he (hnil e)⟩
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hI.defd x hx (contFV_tail_sub hv)).2 n hn)
      rw [← hu n (hnk x hx n hn)] at hw
      exact ⟨w, hw, hT' n w hw (cur_noTyRef hWF hS hFin.2.2 rfl rfl (Nat.le_refl _) rfl hx hn)⟩
    · obtain ⟨σL', hM, hfl, hu, hb, hq⟩ := setReach_run hF hκ hres hO.bools
      obtain ⟨hC', hT', hs⟩ := bool_ext_typed hO.canonL hO.gtyped hO.bools hb
        (E := fun _ => False) (fun y hy _ => hu y hy) fun _ _ h => h.elim
      refine ⟨[], σL', hM, nofun, ?_, fun y _ hy => hu y hy, fun _ e he => absurd he (hnil e),
        fun _ _ _ _ _ h => absurd h.2 (hnil _), fun _ _ _ _ _ h => absurd h.2 (hnil _),
        fun h => by simp at h, fun _ e he => absurd he (hnil e)⟩
      rw [ite_eq_left rfl]
      exact ⟨hC', hfl, hb, fun x hx hv n hn => (hO.defd x hx (contFV_tail_sub hv) n hn).imp
        fun _ h => ⟨(hu n (hnk x hx n hn)).trans h.1, h.2⟩, hT', fun y hy =>
        hO.fresh y ((hs y hy).resolve_right id)⟩

end -- public section

end WP
end Imperative
