/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
public import Strata.Transform.WP.WPOverEmit
public import Strata.Transform.WP.WPOverEval
import Strata.Transform.WP.WPOverFacts
public import Strata.Transform.WP.WPOverEffects
public import Strata.Transform.WP.WPReads
import Strata.DL.Imperative.BigStep.StoreAgree
public import Strata.Transform.WP.WPOverIteLaidCore
import all Strata.Transform.WP.WPOverIteLaidCore
public import Strata.Transform.WP.WPOverIteLaidNoExit
import all Strata.Transform.WP.WPOverIteLaidNoExit
public import Strata.Transform.WP.WPOverIteLaidExit
import all Strata.Transform.WP.WPOverIteLaidExit

/-! # The simulation through laid-out `ite`s

The walk of an `ite` after which an obligation follows (laid out: guard, arms under their reach
contexts, saves, restores, copies and merges) has the simulation property (`Spec`) when the walks
of its arms have it (`iteLaidSpec`): the walk is inverted (`LaidRunAx`), and the output is
matched along the then path, the else path and off the path, both when no arm always exits
(`LaidEnv`) and when one does (`LaidEnvAx`).  The walk of a laid-out `ite` has the read property
when the walks of its arms have it (`iteLaidReads`).

Key theorems: `iteLaidSpec`, `iteLaidReads`. -/

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
variable {tE : TypedEval P}

variable {F : P.Factory} {Lc : List P.Ident} {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P}
  {md : MetaData P} {st0 : WSt P} {r : WRes P} {st' : WSt P} {T : Std.HashMap P.Ident P.Ty}
  {Y : Std.HashMap P.Ident P.Ident} {items : List (Item P)} {S : List P.Ident} {Ex : P.Ident → Prop}
  {k : List (PStmts P)} {Lab : String → List P.Ident} {wc : WExpr P} {rdc : List P.Ident}
  {s1 : WSt P} {g : P.Ident} {s2 : WSt P} {rT : P.Ident} {s3 : WSt P} {κE : RE P}
  {rE? : Option P.Ident} {s4 : WSt P} {Er : WRes P} {s5 : WSt P} {Tr : WRes P} {s6 : WSt P}
  {M : List P.Ident} {sv cp rs : Rope (WItem P)} {cps : List (P.Ident × P.Ident)} {s7 : WSt P}
  {gm? : Option P.Ident} {s8 : WSt P} {cr : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))}
  {ns : List (P.Ident × P.Ident × P.Ident)} {σ σL σ1 σs σ' σE : SemanticStore P} {n : P.Ident}
  {X K : Outcome P → Prop} {evs : List (Event P)} {st : WSt P} {gv : P.Expr} {iE iU : List (Item P)}
  {ss : PStmts P} {ext : List P.Ident} {qm? : Option P.Ident} {o oT oE : Outcome P}


/-! ## The simulation property -/

include iIL in
/-- The walk of a laid-out `ite` (an obligation follows it) has the simulation property when
    the walks of its arms (at the same depth, under every context, an obligation following them)
    have it. -/
theorem iteLaidSpec {F : P.Factory} (hF : WellFormedSemanticEvalBase F) {Lc : List P.Ident}
    {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P} (md : MetaData P)
    (hT : ∀ κ', ListSpec F tE Lc κ' d true tss) (hE : ∀ κ', ListSpec F tE Lc κ' d true ess) :
    Spec F tE Lc κ d (wpIteLaid κ d c tss ess) [.ite (.det c) tss ess md]
      (fun S => Stmt.WellScoped Lc S (.ite (.det c) tss ess md)) true
      (DReachS F (.ite (.det c) tss ess md))
      (fun X => DRunS F X (.ite (.det c) tss ess md)) (ShS F (.ite (.det c) tss ess md)) := by
  intro st0 r st' hwf h T Y hfin items hres S hS Γ hΓ hwt hav Ex hEx k Lab hLab hκv hdead hLK hhigh
  obtain ⟨wc, rdc, s1, g, s2, rT, s3, κE, rE?, s4, Er, s5, Tr, s6, h1, h2, h3, hctx, hEw, hTw,
    htail⟩ := laid_run_inv_ax h
  obtain ⟨sv3, cp3, rs3, cps3, s7, h7, svT, cpT, rsT, cpsT, s7T, h7T, svE, cpE, rsE, cpsE, s7E, h7E,
    hrest⟩ := htail
  have core := LaidCore.mk hF hT hE hwf h1 h2 h3 hctx hEw hTw hfin hres hS hav hEx hLab
    (fun y hy => ⟨(hκv y hy).1, (hκv y hy).2.1, (hκv y hy).2.2.1⟩) (fun y hy => (hκv y hy).2.2.2)
    (wpIteLaid_walkOK h) hdead hLK hhigh (hΓ (.inl rfl)) hwt
  obtain ⟨gm?, s8, qm?, s9, rEm?, s10, ht⟩ := laidTailRest_names hrest
  by_cases hax : Tr.ax = true ∨ Er.ax = true
  · have e := LaidEnvAx.mk core hax h7 h7T h7E hrest
    obtain ⟨M, sv, cp, rs, cps, ⟨ns, hns⟩, hMnd, hsv, hcp, hrs, hcase⟩ := e.saves
    have hs := e.states ⟨ns, hns⟩ (ht.after hns.eq (saveRestore_run h7E))
    have hgap := e.declNotLive hs
    have hMv : ∀ x ∈ M, ∃ z ∈ S,
        (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧ curName st' z = some x := by
      rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
      · exact fun x hx => (e.mvars hs hx).imp fun _ ⟨hz, hfv, hzn⟩ => ⟨hz, .inr hfv, hzn⟩
      · exact fun x hx => e.saved3b hs hgap (.inl hx)
    have hCEv : ∀ x ∈ laidCE Er s6 s4.clock, _ := fun x hx => e.saved3b hs hgap (.inr hx)
    refine ⟨e.hit ht hs hns hMnd hsv hcp hrs hMv hCEv, fun _ σ σL X evs o hon hrun hfeas => ?_,
      fun _ => e.off ht hs hns hMnd hsv hcp hrs hcase hMv hCEv⟩
    rcases ht.out with ⟨hnil, -⟩ | ⟨hnil, -⟩
    · obtain ⟨rfl, rfl, rfl, hT0, hE0, hreg⟩ := e.nilParts ht hs hns hsv hnil
      exact .inr ⟨[], σL, .nil, nofun,
        e.nilRun hs hns rfl hT0 hE0 hreg ht.ax ht.drop hon hrun hfeas⟩
    · cases hrun with
      | ite_true hc hT' hsh =>
        exact e.runThen ht hs hns hMnd hsv hcp hrs hcase hMv hCEv hnil hon hc hsh hT' hfeas
      | ite_false hc hE' hsh =>
        exact e.runElse ht hs hns hMnd hsv hcp hrs hcase hMv hCEv hnil hon hc hE' hsh hfeas
  obtain ⟨hTa, hEa⟩ : Tr.ax = false ∧ Er.ax = false := by simpa using hax
  obtain ⟨hgm, hqm, hrEm, hrax, hdrop, hregs, hout⟩ := ht
  simp only [laidCT, laidCE, hTa, hEa, Bool.false_eq_true, ↓reduceIte, saveRestore_nil_run,
    Except.ok.injEq, Prod.mk.injEq] at h7 h7T h7E
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h7T
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := h7E
  simp only [laidCarry_nil, List.isEmpty_nil, Bool.true_eq_false, and_false, false_and,
    not_false_eq_true, true_and, false_or] at hqm hrEm
  obtain ⟨rfl, rfl⟩ := hqm
  obtain ⟨rfl, rfl⟩ := hrEm
  have e := LaidEnv.mk core hTa hEa h7 (gm? := gm?) (s8 := s10)
    (cr := laidCarries s10.carries Tr Er [] [] (optVar gm?) (elseGuard κ gm? none none))
    (by simpa [laidNeedGm, hEa, laidCarry_nil] using hgm) (fun k => by simp [rex_getD])
    (by simpa [hTa, hEa] using hrax) hdrop (by simpa [laidCarry_nil] using hregs) (by
      simp only [laidCarry_nil] at hout
      delta laidPartsAx laidParts at hout ⊢
      simp only [List.all_cons, List.all_nil, List.flatMap_cons, List.flatMap_nil, Rope.isNil,
        Rope.toList_nil, Bool.true_and, Bool.and_true, List.nil_append, List.append_nil,
        laidMergesAx_eq, hEa, Bool.false_eq_true, ↓reduceIte, Option.isNone_none] at hout ⊢
      exact hout.imp id fun ⟨h1, h2, h3, h4, _, _, h5⟩ => ⟨h1, h2, h3, h4, h5⟩)
  have hs := e.states
  obtain ⟨ns, hns⟩ := saveRestore_run h7
  rcases e.out with ⟨hnil, hnil', -⟩ | ⟨hnn, -, hsk, hobl, -⟩
  · obtain ⟨hTn, hEn, rfl, rfl, -⟩ := hs.nilParts hns hnil
    refine ⟨fun σ σL t cnd b tr hon hreach hcl => ?_, fun _ σ σL X evs o hon hrun hfeas =>
      e.runNil hs hns hon hnil' hrun hfeas, fun _ σs σL K hoff hsh => e.offAll hs hns hoff hsh⟩
    have hT0 : resolveItems T Y Tr.out.toList = .ok [] := by rw [Rope.isNil_toList hTn]; rfl
    cases hreach with
    | ite_true hc hR =>
      obtain ⟨-, -, -, -, trT, hhit, -⟩ := (e.armTp hs hT0).1 σ _ t cnd b tr
        (e.thenT hs hns hon (preStore_two hs.pre.g_rT) nofun nofun (wfStore_update_bool
          (wfStore_update_bool hon.canonL g (.inl rfl)) rT (.inl rfl))) hR hcl
      cases hhit
    | ite_false hc hR hsh =>
      obtain ⟨σE, -, -, honE⟩ := e.rn_elseStore hs hns rfl hT0 hon (shL_of_shB hsh)
      obtain ⟨-, -, -, -, trE, hhit, -⟩ :=
        (e.armEp hs (by rw [Rope.isNil_toList hEn]; rfl)).1 σ σE t cnd b tr honE hR hcl
      cases hhit
  obtain ⟨ce, iRT, iGM, iSV, iT, iCP, iRS, iRE, iE, iMG, iU, hsp⟩ := e.split hnn
  obtain ⟨hce, hRT, hGM, hSV, hT, hCP, hRS, hRE, hE, hMG, hU, hitems⟩ := hsp
  refine ⟨fun σ σL t cnd b tr hon hreach hcl => ?_, fun _ σ σL X evs o hon hrun hfeas => ?_,
    fun _ σs σL K hoff hsh => e.offAll hs hns hoff hsh⟩
  · have hsrcS := e.savedOn hs hon hns
    have hpre := fun {cv} (hc : P.eval F σ c = some cv) hgb => e.preRunQ hs hns hon.fresh hon.canonL
      hRT hGM (iQM := []) (qm? := none) (by cases κ <;> simp only [Rope.toList_nil] <;> rfl) nofun
      nofun hSV (e.guardOn hs hon hnn hs.aft.liveC hc hgb hce) hgb hsrcS
    cases hreach with
    | ite_true hc hR =>
      obtain ⟨σB, hrun, hCB, hB, -⟩ := hpre hc (.inl rfl)
      by_cases hrt : (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true
      · obtain rfl : iT = [] := resolve_isNil (Bool.and_eq_true_iff.1 hrt).1 hT
        have hBv := (show PreStore F σL σB (g :: gm?.toList) (HasBool.ttVal F) ns [] by
          simpa [hrt, laidQm] using hB).add (x := rT) (hs.rTFacts hns).2.1 nofun
        obtain ⟨-, -, -, -, trT, hhit, -⟩ := (e.armTp hs hT).1 σ _ t cnd b tr
          (e.thenT hs hns hon hBv nofun nofun (wfStore_update_bool hCB rT (.inl rfl))) hR hcl
        cases hhit
      · obtain ⟨hobT, hskT, wsub, hwsub, trT, hhit, hclT⟩ := (e.armTp hs hT).1 σ σB t cnd b tr
          (e.thenT hs hns hon (ext := []) (by simpa [hrt, laidQm] using hB) nofun nofun hCB) hR hcl
        refine ⟨by rw [hobl, hobT]; rfl, hsk ▸ .iteT g _ _ hskT, wsub,
          fun q hq => ⟨hs.aft.back ▸ (hwsub q hq).1, (hwsub q hq).2⟩, [] ++ trT, ?_,
          by simpa using hclT⟩
        rw [hitems]
        simpa only [List.cons_append, List.append_assoc, List.nil_append] using
          HitIn.append_right hrun (HitIn.append_left (b := iCP ++ (iRS ++ (iRE ++ (iE ++ (iMG ++
            iU))))) hhit)
    | ite_false hc hR hsh =>
      obtain ⟨σB, hrB, hCB, hB, -⟩ := hpre hc (.inr rfl)
      obtain ⟨trT, σ1, hrT, hfT, hC1, hfr1, hgt1, hk1, -⟩ := e.of_T hs hns
        (fun x hx hv n hn => let ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hon.defd x hx hv).2 n hn)
          ⟨w, hw, hon.gtyped n w hw (e.curY hs hx hn)⟩) hon.gtyped hon.fresh
        (fun q hq => (hsrcS q hq).elim fun _ h => h.1 ▸ rfl) hB nofun nofun hCB hT (shL_of_shB hsh)
      obtain ⟨σR, hrR, hCR, -, hvR, hoR, -, -, hgR, hκR, h0R⟩ := e.ry_midRun hs hns hon.fresh
        hsrcS hB hC1 hgt1 (fun n => mainRun_mono hrT n) (fun n hn =>
          (hs.armT.writesW T Y iT hT σB trT σ1 hrT n hn).imp_right
            fun h => (Option.some.inj h).symm) hCP hRS
      obtain ⟨σD, hrD, hCD, hcase⟩ := rEiRun e.hF hCR (fun x hx => (h0R x hx).1)
        (.inl ⟨hon.reach.congr hκR, hgR, rfl⟩) hRE
      have hDR : ∀ n, (∀ x, rE? = some x → n ≠ x) → σD n = σR n := fun n hn => by
        rcases hcase with ⟨-, h, -⟩ | ⟨x, hx, -, h⟩ <;> rw [h]
        exact (update_facts σR x (HasBool.ttVal F)).2 n (Ne.symm (hn x hx))
      obtain ⟨σDv, hDv, hDvrE, hCDv⟩ : ∃ σDv : SemanticStore P,
          (∀ n, (∀ x, rE? = some x → n ≠ x) → σDv n = σD n) ∧
          (∀ x, rE? = some x → σDv x = some (HasBool.ttVal F)) ∧ WellFormedStore σDv F := by
        refine ⟨fun n => if rE? = some n then some (HasBool.ttVal F) else σD n,
          fun n h => ite_eq_right fun h' => h n h' rfl, fun x h => ite_eq_left h, fun x v hv => ?_⟩
        exact if h : rE? = some x then Option.some.inj ((ite_eq_left h).symm.trans hv) ▸
          (HasBool.boolIsVal F).1 else hCD x v ((ite_eq_right h).symm.trans hv)
      obtain ⟨-, hgtD, hfrD⟩ := e.ry_elseFacts hs hns hon hsrcS hgt1 hfr1
        (fun n h => by rw [hk1 n h]; exact h)
        (fun q hq => (hDR _ fun x hx h => ((h0R x hx).2 q hq).1 h.symm).trans (hvR q hq))
        (fun n hn hx => (hDR n hx).trans (hoR n hn)) hDv (.inl rfl) hDvrE
      have hnot : ∀ n, (σL n).isSome → ¬ ((n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n) :=
        fun n h hn => by simp [e.unbound hs hon.fresh hn] at h
      have hkeep : ∀ n, (σL n).isSome → σDv n = σL n := fun n h => by
        have hr : ∀ x, rE? = some x → n ≠ x := fun x hx he =>
          hnot n h (.inl (.inr (.inr (he ▸ hx))))
        rw [hDv n hr, hDR n hr]
        rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq, rfl⟩ | hq
        · exact hvR q hq
        · rw [hoR n fun q hq' => ⟨fun he => hq ⟨q, hq', he⟩,
            fun he => hnot n h (.inr (he ▸ (hns.drawn q hq').2.1.mono hs.aft.next))⟩]
          exact hk1 n h
      have hreach : κE.Holds F σDv := by
        have hg0 : rE? = none → σDv g = some (HasBool.ffVal F) := fun h => by
          rw [hDv g (by simp [h]), hDR g (by simp [h]), hgR]
        rcases LaidCtx.cases' e.ctx with ⟨h0, rfl | ⟨q, rfl, rfl⟩⟩ | ⟨x, rfl, rfl⟩
        · exact hg0 h0
        · exact ⟨(hDv q (by simp [h0])).trans <| (hDR q (by simp [h0])).trans <|
            (hκR q (.head _)).trans hon.reach, hg0 h0⟩
        · exact hDvrE x rfl
      obtain ⟨hobE, hskE, wsub, hw, trE, hhit, hcl'⟩ := (e.armEp hs hE).1 σ σDv t cnd b tr
        (hs.elseE hon hCDv hkeep hgtD hfrD hreach) hR hcl
      cases hb : (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil)
      · obtain rfl : σDv = σD := funext fun n => (Classical.em (rE? = some n)).elim (fun h => by
          rcases hcase with ⟨-, -, h' | h'⟩ | ⟨x, hx, -, rfl⟩
          · simp [h'] at h
          · simp [h'] at hb
          · obtain rfl := Option.some.inj (h.symm.trans hx)
            exact (hDvrE n h).trans (update_facts σR n (HasBool.ttVal F)).1.symm)
          fun h => hDv n fun x hx he => h (he ▸ hx)
        refine ⟨by rw [hobl, hobE, Bool.or_true], hsk ▸ .iteE g _ _ hskE, wsub, fun q hq =>
          ⟨by rw [hs.aft.back]; exact hs.wT.toWalkCore.back_keep hs.wf5 (hw q hq).1, (hw q hq).2⟩,
          trT ++ trE, ?_, claimK_prepend hfT hcl'⟩
        rw [hitems]
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using HitIn.append_right
          (hrB.append (hrT.append (hrR.append hrD))) (hhit.append_left (b := iMG ++ iU))
      · obtain rfl := resolve_isNil (Bool.and_eq_true_iff.1 hb).1 hE
        nomatch hhit
  · cases hrun with
    | ite_true hc hT' hsh => exact e.runThen hns hon hnn hc hT' hsh hfeas
    | ite_false hc hE' hsh => exact e.runElse hns hon hnn hc hE' hsh hfeas

/-! ## The names the output of a laid-out `ite` reads -/

omit iLI iWL iOp iLF iLFs iLV in
/-- The saves and the copies of a run of `saveRestore` read the saved variables, and the
    restores read them and the save names. -/
private theorem SaveNs.reads {s s' : WSt P} {xs : List P.Ident}
    (h : SaveNs s xs sv cp rs cps s' ns) :
    (∀ n ∈ wFV true sv.toList, n ∈ xs) ∧ (∀ n ∈ wFV true cp.toList, n ∈ xs) ∧
      (∀ n ∈ wFV true rs.toList, n ∈ xs ∨ n ∈ wDecls sv.toList) ∧
      (∀ p ∈ cps, p.1 ∈ xs ∧ p.2 ∈ wDecls cp.toList) := by
  obtain ⟨rfl, hsv, hcp, hrs, rfl, -, -, -, -, -⟩ := h
  rw [hsv, hcp, hrs]
  clear hsv hcp hrs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> induction ns <;>
    simp only [List.map_cons, List.map_nil, wFV, wDecls, oreads, wreads] at * <;> grind

omit iLI iWL iOp iLF iLFs iLV in
/-- The saves, copies and restores of a run of `saveRestore` leave no main path. -/
private theorem SaveNs.noBr {s s' : WSt P} {xs : List P.Ident}
    (h : SaveNs s xs sv cp rs cps s' ns) :
    sv.toList.any WItem.isBranching = false ∧ cp.toList.any WItem.isBranching = false ∧
      rs.toList.any WItem.isBranching = false := by
  simp [h.saves, h.copies, h.restores, WItem.isBranching]

omit iLI iWL iOp iLF iLFs iLV in
/-- The items of the merges of a laid-out `ite`. -/
private theorem laidMergesAx_toList (gm? : Option P.Ident) (E : WRes P)
    (l : List (P.Ident × P.Ident)) :
    (laidMergesAx gm? E l).toList = l.map fun p => .set p.1 (some (if E.A.contains p.1 && !E.ax then
      .ite (optVar gm?) (.var p.2) (.var p.1) else .var p.2)) := by
  rw [laidMergesAx, toList_foldl_one, Rope.toList_nil, List.nil_append]


omit iLV in
/-- The walk of a laid-out `ite` has the read property when the walks of its arms (at the same
    depth, under every context, an obligation following them) have it. -/
theorem iteLaidReads {Lc : List P.Ident} {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P}
    (md : MetaData P) (hT : ∀ κ', ListReads Lc κ' d true tss)
    (hE : ∀ κ', ListReads Lc κ' d true ess) :
    ReadsSpec κ d (wpIteLaid κ d c tss ess) [.ite (.det c) tss ess md]
      (fun S => Stmt.WellScoped Lc S (.ite (.det c) tss ess md)) true := by
  intro st0 r st' hwf h S hS hav hL hhigh hκ hD hLK
  obtain ⟨wc, rdc, s1, g, s2, rT, s3, κE, rE?, s4, E, s5, T, s6, h1, h2, h3, hctx, h5, h6,
    htail⟩ := laid_run_inv_ax h
  have hU : ∀ n ∈ wFV true (laidU κ κE rT T E d).toList,
      n = rT ∨ n ∈ RE.vars κE ∨ n ∈ RE.vars κ := by
    intro n hn
    unfold laidU at hn
    cases κ <;> split at hn <;> simp [setReach, Rope.toList_one, Rope.toList_nil, wFV, oreads,
      wreads, WExpr.or, WExpr.not] at hn <;> grind [wreads_kExpr, RE.vars]
  have c1 := wRen_walk h1
  have pre := pre_facts h2 h3 hctx
  have wE := wpList_walkOK h5
  have wT := wpList_walkOK h6
  obtain ⟨wf4, hκE⟩ := pre_wf h2 h3 hctx (c1.wf hwf fun _ h => nomatch h)
  have hκEv : ∀ y ∈ RE.vars κE, y = g ∨ rE? = some y ∨ y ∈ RE.vars κ := fun y hy => by
    rcases LaidCtx.cases' hctx with ⟨-, rfl | ⟨q, rfl, rfl⟩⟩ | ⟨x, rfl, rfl⟩ <;> grind [RE.vars]
  obtain ⟨hcS, hSt, hSe⟩ := hS
  have hav4 : s4.avoid = st0.avoid := by rw [pre.eq]; exact c1.avoid
  have hfa : ∀ x, x ∈ Block.idents tss ∨ x ∈ Block.idents ess → AvoidedIfFresh st0 x :=
    fun x hx => hav x (List.mem_append_right _ (by rcases hx with hx | hx <;>
      simp [Block.idents, Stmt.idents, hx, ExprOrNondet.getVars_det, getFvars_mem_exprFV]))
  have wf5 : WFSt s5 := wE.wf wf4 fun x hx b j hxj =>
    hav4 ▸ hfa x (.inr (stmtsInits_mem_idents x hx)) b j hxj
  have wf6 : WFSt s6 := wT.wf wf5 fun x hx b j hxj =>
    (wE.avoid.trans hav4) ▸ hfa x (.inl (stmtsInits_mem_idents x hx)) b j hxj
  obtain ⟨-, -, h01, -⟩ := wRen_run h1
  have hL4 : ∀ (l : String) (t : Nat), s4.labelDepth[l]? = some t → t ≤ d := fun l t h =>
    hL l t (by rwa [pre.eq, h01] at h)
  have hL5 : ∀ (l : String) (t : Nat), s5.labelDepth[l]? = some t → t ≤ d := fun l t h =>
    hL4 l t (wE.labelDepth l ▸ h)
  have hnext4 : st0.next ≤ s4.next := Nat.le_trans c1.next pre.next
  have hD4 : DeadBelow s4 := fun b j hj =>
    Nat.lt_of_lt_of_le (hD b j (by rwa [pre.eq, h01] at hj)) hnext4
  have hc4 : s4.carries = st0.carries := by rw [pre.eq, h01]
  have hhigh4 : ∀ k, d < k → s4.carries.getD k [] = [] := fun k hk => hc4 ▸ hhigh k hk
  have hκE4 : ∀ y ∈ RE.vars κE, ∃ b j, y = freshName b j ∧ j < s4.next := fun y hy => by
    rcases or_assoc.2 (hκEv y hy) with hp | hp
    · exact (pre.drawn y (hp.imp_right .inr)).imp fun _ ⟨j, h1, _, _, h4⟩ => ⟨j, h1, h4⟩
    · exact (hκ y hp).imp fun _ ⟨j, h1, h2⟩ => ⟨j, h1, Nat.lt_of_lt_of_le h2 hnext4⟩
  have hLK4 : LiveKeys s4 := fun n t ht =>
    (hLK n t (by rwa [pre.eq, h01] at ht)).of_le (by rw [hav4]) hnext4
  have havE : ∀ x ∈ S ++ Block.idents ess, AvoidedIfFresh s4 x := fun x hx b j hj => hav4 ▸
    (List.mem_append.1 hx).elim (hav x <| List.mem_append_left _ ·) (hfa x <| .inr ·) b j hj
  have havT : ∀ x ∈ S ++ Block.idents tss, AvoidedIfFresh s5 x := fun x hx b j hj =>
    (wE.avoid.trans hav4) ▸
      (List.mem_append.1 hx).elim (hav x <| List.mem_append_left _ ·) (hfa x <| .inl ·) b j hj
  have hRE := hE κE (fun h => absurd h hκE) s4 E s5 wf4 h5 S hSe havE hL4 hhigh4 hκE4 hD4 hLK4
  have hD5 := wpList_deadBelow h5 hD4
  have hLK5 : LiveKeys s5 := wpList_liveKeys h5 wf4 (fun x hx => havE x (List.mem_append_right _
    hx)) (fun y hy => .inr (hκE4 y hy)) hLK4
  have hhigh5 := wpList_carriesHigh h5 hL4 hhigh4
  have hrT5 : ∃ b j, rT = freshName b j ∧ j < s5.next := (pre.drawn rT (.inr (.inl rfl))).imp
    fun _ ⟨j, h1, _, _, h4⟩ => ⟨j, h1, Nat.lt_of_lt_of_le h4 wE.next⟩
  have hRT := hT (.name rT) nofun s5 T s6 wf5 h6 S hSt havT hL5 hhigh5
    (fun y hy => by simp only [RE.vars, List.mem_singleton] at hy; exact hy ▸ hrT5) hD5 hLK5
  have aEA := arm_assigned h5 hκE wf4 hSe havE hL4
  have aER := arm_read h5 hκE wf4 hSe havE hL4
  have aEd := arm_decl h5 hκE
  have aEl := arm_declNotLive h5 hκE wf4 hSe havE hL4
  have aTA := arm_assigned h6 nofun wf5 hSt havT hL5
  have aTc := arm_declNotCur h6 nofun wf5 hSt havT hL5
  have hc56 : ∀ z ∈ S, ∀ m, curName s5 z = some m → curName s6 z = some m := fun z hz m hm =>
    wT.names z m (wfl_inits_disjoint S tss hSt z hz) hm
  have hc45 : ∀ z ∈ S, ∀ m, curName s4 z = some m → curName s5 z = some m := fun z hz m hm =>
    wE.names z m (wfl_inits_disjoint S ess hSe z hz) hm
  have hc14 : ∀ z m, curName s1 z = some m → curName s4 z = some m := fun z m hm => by
    rwa [curName_eq_of_nm_taken (by rw [pre.eq]) (by rw [pre.eq])]
  have hV : ∀ z, z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess ∨ z ∈ exprFV c →
      z ∈ Block.freeVars [.ite (.det c) tss ess md] := fun z hz => by
    rcases hz with hz | hz | hz <;> simp [Block.freeVars, Stmt.freeVars, hz]
  have hdisj : ∀ x, x ∈ wDecls T.out.toList → x ∈ wDecls E.out.toList → False := by
    intro x hxT hxE
    rcases arm_decl h6 nofun x hxT with ⟨b, j, h1, h2, h3, -⟩ | ⟨hiT, htT⟩ | ⟨yT, -, hyT⟩
    · rcases aEd x hxE with ⟨b', j', h1', -, -, h4'⟩ | ⟨hiE, -⟩ | ⟨yE, -, hyE⟩
      · exact absurd (freshName_counter_inj (h1.symm.trans h1')) (by omega)
      · simp [wE.avoid, hav4, hfa x (.inr (stmtsInits_mem_idents x hiE)) b j h1] at h2
      · obtain ⟨-, b', j', h4, h5', -⟩ := wf4.nm_fresh yE x hyE
        have hn5 := wE.next
        exact absurd (freshName_counter_inj (h1.symm.trans h4)) (by omega)
    · rcases aEd x hxE with ⟨b', j', h1', h2', -, -⟩ | ⟨hiE, -⟩ | ⟨yE, -, hyE⟩
      · simp [hav4, hfa x (.inl (stmtsInits_mem_idents x hiT)) b' j' h1'] at h2'
      · simp [arm_takenIn h5 hκE x hiE] at htT
      · obtain ⟨-, b', j', h4, -, h6'⟩ := wf4.nm_fresh yE x hyE
        simp [hav4, hfa x (.inl (stmtsInits_mem_idents x hiT)) b' j' h4] at h6'
    · exact arm_declNotNm h5 hκE wf4 hSe havE hL4 x hxE yT hyT
  have hc45clk : s4.clock ≤ s5.clock := wE.clock
  have hlb : ∀ (st : WSt P) x, LiveKeys st → (∀ t, s6.live[x]? = some t → t < s4.clock →
      st.live[x]? = some t ∧ FreshAt st x) → liveBefore s6 x s4.clock = false := by
    intro st x hk h
    unfold liveBefore
    split
    · refine decide_eq_false fun hlt => ?_
      obtain ⟨ht, b, j, h1, h2, h3⟩ := h _ ‹_› hlt
      exact (hk x _ ht).elim (fun h => by simp [h b j h1] at h2)
        fun ⟨b', j', h4, h5⟩ => absurd (freshName_counter_inj (h1.symm.trans h4)) (by omega)
    · rfl
  have hTlive : ∀ x ∈ wDecls T.out.toList, liveBefore s6 x s4.clock = false := fun x hx =>
    hlb s5 x hLK5 fun t hsn hlt => arm_declNotLive h6 nofun wf5 hSt havT hL5 x hx t hsn (by omega)
  have hElive : ∀ x ∈ wDecls E.out.toList, liveBefore s6 x s4.clock = false := fun x hx =>
    hlb s4 x hLK4 fun t hsn hlt => aEl x hx t (wT.toWalkCore.liveOld x t hsn (by omega)) hlt
  obtain ⟨sv3, cp3, rs3, cps3, s7, h7, svT, cpT, rsT, cpsT, s7T, h7T, svE, cpE, rsE, cpsE, s7E,
    h7E, hrest⟩ := htail
  obtain ⟨gm?, s8, qm?, s9, rEm?, s10, hgm, hqm, hrEm, hax, hdrop, hregs, hout⟩ :=
    laidTailRest_names hrest
  obtain ⟨ns3, hns3⟩ := saveRestore_run h7
  obtain ⟨nsT, hnsT⟩ := saveRestore_run h7T
  obtain ⟨nsE, hnsE⟩ := saveRestore_run h7E
  obtain ⟨e8, -, -, -⟩ := optFresh_facts (hgm.imp (fun h => h.2) fun h => h.2)
  obtain ⟨e9, -, -, -⟩ := optFresh_facts (hqm.imp (fun h => h.2.2) fun h => h.2)
  obtain ⟨e10, -, -, -⟩ := optFresh_facts (hrEm.imp (fun h => h.2.2) fun h => h.2)
  have h10 : s10.nm = s6.nm ∧ s10.taken = s6.taken ∧ s10.pending = s6.pending ∧
      s10.carries = s6.carries := by
    rw [e10, e9, e8, hnsE.eq, hnsT.eq, hns3.eq]
    exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hcur, hpend, hcar⟩ : (∀ z, curName st' z = curName s6 z) ∧ st'.pending = s6.pending ∧
      st'.carries = laidCarries s10.carries T E (laidCarry T s6 cpsT) (laidCarry E s6 cpsE)
        (optVar gm?) (elseGuard κ gm? qm? rEm?) := by
    have hfin : ∀ (s : WSt P), s.nm = s10.nm → s.taken = s10.taken → s.pending = s10.pending →
        (∀ z, curName s z = curName s6 z) ∧ s.pending = s6.pending := fun s h1 h2 h3 =>
      ⟨curName_eq_of_nm_taken (h1.trans h10.1) (h2.trans h10.2.1), h3.trans h10.2.2.1⟩
    rcases hout with ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, hl⟩
    · exact ⟨(hfin _ rfl rfl rfl).1, (hfin _ rfl rfl rfl).2, rfl⟩
    · obtain ⟨live, clock, hrun, -⟩ := liveAdd_run (P := P) (rdc ++ RE.vars κ) _
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj (hrun.symm.trans hl))
      exact ⟨(hfin _ rfl rfl rfl).1, (hfin _ rfl rfl rfl).2, rfl⟩
  have hS6 : ∀ z m, curName s6 z = some m → curName st' z = some m := fun z m h => (hcur z).trans h
  have hTA : ∀ x, T.A.contains x = true → x ∈ wDecls T.out.toList ∨
      ∃ z ∈ S, z ∈ Block.freeVars [.ite (.det c) tss ess md] ∧ curName st' z = some x := fun x hx =>
    (aTA x hx).elim (fun ⟨z, hz, hv, hc⟩ => .inr ⟨z, hz, hV z (.inl hv), hS6 z x hc⟩) .inl
  have hER : ∀ x, E.R.contains x = true → x ∈ wDecls T.out.toList →
      ∃ z ∈ S, z ∈ Block.freeVars [.ite (.det c) tss ess md] ∧ curName st' z = some x :=
    fun x hx hxT => (aER x hx).elim (fun ⟨z, hz, _, hc⟩ => absurd (hc56 z hz x hc) (aTc x hxT z hz))
      fun h => (hdisj x hxT h).elim
  have hsv : ∀ x, (x ∈ (if T.ax then [] else interSet T.A E.R) ∨ x ∈ laidCT T E s6 s4.clock ∨
      x ∈ laidCE E s6 s4.clock) →
      ∃ z ∈ S, z ∈ Block.freeVars [.ite (.det c) tss ess md] ∧ curName st' z = some x := by
    rintro x (hx | hx | hx)
    · split at hx
      · cases hx
      exact (mem_interSet.1 hx).elim fun hA hR => (hTA x hA).elim (hER x hR) id
    · obtain ⟨hA, hl⟩ := mem_laidCT hx
      refine (hTA x hA).elim (fun hxT => ?_) id
      exact (Bool.or_eq_true_iff.1 hl).elim (fun hl => by simp [hTlive x hxT] at hl) (hER x · hxT)
    · obtain ⟨hA, hl⟩ := mem_laidCE hx
      exact (aEA x hA).elim (fun ⟨z, hz, hv, hc⟩ => ⟨z, hz, hV z (.inr (.inl hv)),
        hS6 z x (hc56 z hz x hc)⟩) fun hxE => by simp [hElive x hxE] at hl
  have hdecl : ∀ x, (x ∈ wDecls T.out.toList ∨ x ∈ wDecls E.out.toList ∨
      x ∈ wDecls cpT.toList ∨ x ∈ wDecls cpE.toList ∨ gm? = some x ∨
      (∃ q, κ = .name q ∧ qm? = some x) ∨ (rE?.isSome ∧ rEm? = some x)) →
      x ∈ wDecls r.out.toList := by
    intro x hx
    rcases hout with ⟨hnil, hro, -⟩ | ⟨-, hro, -⟩
    · delta laidPartsAx at hnil
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hnil
      obtain ⟨-, hgm, hqm, -, -, hTn, -, hcT, -, -, -, hrm, -, hEn, hcE, -⟩ := hnil
      simp only [Rope.isNil_toList hTn, Rope.isNil_toList hEn, Rope.isNil_toList hcT,
        Rope.isNil_toList hcE, wDecls, List.not_mem_nil, false_or] at hx
      rcases hx with hx | ⟨q, rfl, hx⟩ | ⟨hr, hx⟩
      · simp [hx, Rope.isNil] at hgm
      · simp [hx, Rope.isNil] at hqm
      · obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 hr
        simp [hx, hr0, Rope.isNil] at hrm
    · rewrite [hro]
      unfold laidPartsAx
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, wDecls, List.mem_cons,
        mem_wDecls_append]
      rcases hx with hx | hx | hx | hx | hx | ⟨q, rfl, hx⟩ | ⟨hr, hx⟩
      any_goals (simp only [hx, or_true, true_or]; done)
      any_goals (simp only [Bool.and_eq_true, hx, Rope.toList_one, wDecls, List.mem_cons,
        List.not_mem_nil, or_false, Option.isNone_iff_eq_none, true_or, or_true]; done)
      · obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 hr
        simp [hx, hr0, Rope.toList_one, wDecls]
  have hcopy : ∀ {xs s s' sv cp rs cps ns}, SaveNs (P := P) s xs sv cp rs cps s' ns →
      s6.next ≤ s.next → ∀ p ∈ cps, p.1 ∈ xs ∧ p.2 ∈ wDecls cp.toList ∧
        ∃ b j, p.2 = freshName b j ∧ s6.next ≤ j := by
    intro _ _ _ _ _ _ _ _ hns hle p hp
    obtain ⟨h1, h2⟩ := hns.reads.2.2.2 p hp
    obtain ⟨q, hq, rfl⟩ := hns.mem_pairs.1 p hp
    obtain ⟨-, ⟨b, j, h3, -, h4, -⟩, -⟩ := hns.drawn q hq
    exact ⟨h1, h2, b, j, h3, Nat.le_trans hle h4⟩
  have hcT := hcopy hnsT hns3.next
  have hcE := hcopy hnsE (Nat.le_trans hns3.next hnsT.next)
  have hpendOK : ∀ l e, e ∈ st'.pending.getD l [] → e ∈ r.regs.toList →
      e ∈ wDecls r.out.toList := by
    intro l e he hr
    rw [hpend] at he
    rw [hregs, List.mem_append, List.mem_append, List.mem_append] at hr
    rcases hr with (hr | hr) | hr | hr
    · exact hdecl e (.inl (hRT.pend l e he hr))
    · have he5 : e ∈ s5.pending.getD l [] := by
        rcases wpList_pending_new h6 he with h | ⟨b, j, rfl, hj, -, -⟩
        · exact h
        · obtain ⟨b', j', he', -, hj', -⟩ := wpList_regs h5 _ hr
          exact absurd (freshName_counter_inj he') (by omega)
      exact hdecl e (.inr (.inl (hRE.pend l e he5 hr)))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      exact hdecl _ (.inr (.inr (.inl (hcT p (mem_laidCarry hp)).2.1)))
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      exact hdecl _ (.inr (.inr (.inr (.inl (hcE p (mem_laidCarry hp)).2.1))))
  have hcarOK : ∀ k q, q ∈ st'.carries.getD k [] → q.2.2 ∈ r.regs.toList →
      q.2.2 ∈ wDecls r.out.toList ∧ (∃ e, q.2.1 = .ite e (.var q.2.2) (.var q.1) ∧
        ∀ y ∈ wreads e, y ∈ wDecls r.out.toList) ∧ (true = true →
          (∃ z ∈ S, z ∈ Block.freeVars [.ite (.det c) tss ess md] ∧ curName st' z = some q.1) ∨
            q.1 ∈ wDecls r.out.toList) := by
    intro k q hq hr
    rw [hcar] at hq
    rw [hregs, List.mem_append, List.mem_append, List.mem_append] at hr
    have hgm' : ∀ y, y ∈ wreads (optVar gm?) → y ∈ wDecls r.out.toList := fun y hy => by
      cases hg : gm? <;> simp only [hg, optVar, wreads, List.mem_singleton, List.not_mem_nil] at hy
      exact hdecl _ (.inr (.inr (.inr (.inr (.inl (hy ▸ hg))))))
    rcases mem_laidCarries hq with hq | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · rw [h10.2.2.2] at hq
      rcases hr with (hr | hr) | hr | hr
      · obtain ⟨h1, ⟨e, he, h2⟩, h3⟩ := hRT.car k q hq hr
        refine ⟨hdecl _ (.inl h1), ⟨e, he, fun y hy => hdecl y (.inl (h2 y hy))⟩, fun _ => ?_⟩
        exact (h3 rfl).elim (fun ⟨z, hz, hv, hc⟩ => .inl ⟨z, hz, hV z (.inl hv), hS6 z _ hc⟩)
          fun h => .inr (hdecl _ (.inl h))
      · have hq5 : q ∈ s5.carries.getD k [] := by
          obtain ⟨new, hnew, hnd⟩ := arm_carriesNew h6 nofun hhigh5 k
          refine (List.mem_append.1 (hnew ▸ hq)).resolve_left fun hq => ?_
          obtain ⟨b, j, he, -, hj, -⟩ := hnd q hq
          obtain ⟨b', j', he', -, hj', -⟩ := wpList_regs h5 _ hr
          exact absurd (freshName_counter_inj (he.symm.trans he')) (by omega)
        obtain ⟨h1, ⟨e, he, h2⟩, h3⟩ := hRE.car k q hq5 hr
        refine ⟨hdecl _ (.inr (.inl h1)), ⟨e, he, fun y hy => hdecl y (.inr (.inl (h2 y hy)))⟩,
          fun _ => ?_⟩
        exact (h3 rfl).elim (fun ⟨z, hz, hv, hc⟩ => .inl ⟨z, hz, hV z (.inr (.inl hv)),
          hS6 z _ (hc56 z hz _ hc)⟩) fun h => .inr (hdecl _ (.inr (.inl h)))
      all_goals
        obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hr
        obtain ⟨⟨b, j, hq', hj⟩, -⟩ := wf6.carries_get hq
        obtain ⟨-, -, b', j', he', hj'⟩ : _ ∧ _ ∧ ∃ b j, p.2 = freshName b j ∧ s6.next ≤ j := by
          first | exact hcT p (mem_laidCarry hp) | exact hcE p (mem_laidCarry hp)
        exact absurd (freshName_counter_inj (hq'.symm.trans (hpe ▸ he'))) (by omega)
    · obtain ⟨h1, h2, -⟩ := hcT p (mem_laidCarry hp)
      exact ⟨hdecl _ (.inr (.inr (.inl h2))), ⟨optVar gm?, rfl, hgm'⟩,
        fun _ => .inl (hsv _ (.inr (.inl h1)))⟩
    · obtain ⟨h1, h2, -⟩ := hcE p (mem_laidCarry hp)
      refine ⟨hdecl _ (.inr (.inr (.inr (.inl h2)))), ⟨_, rfl, fun y hy => ?_⟩,
        fun _ => .inl (hsv _ (.inr (.inr h1)))⟩
      have hrm : ∀ x, rEm? = some x → x ∈ wDecls r.out.toList := fun x hx => by
        rcases hrEm with ⟨hr, -, x', hx', -⟩ | ⟨-, hn, -⟩
        · exact hdecl _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨hr, hx⟩))))))
        · simp [hn] at hx
      unfold elseGuard at hy
      split at hy
      · exact hgm' y (wreads_not hy)
      · rename_i q x
        simp only [WExpr.and, wreads, List.mem_append, List.mem_singleton, List.not_mem_nil,
          or_false] at hy
        rcases hy with rfl | hy
        · exact hdecl _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨q, rfl, rfl⟩))))))
        · exact hgm' y (wreads_not hy)
      · rename_i x _
        simp only [wreads, List.mem_singleton] at hy
        exact hy ▸ hrm _ rfl
      · simp [wreads] at hy
  rcases hout with ⟨hnil, hro, -⟩ | ⟨hnn, hro, -, hobl, -, -, -⟩
  · exact ⟨fun _ _ n hn => by simp [hro, Rope.toList_nil, wFV] at hn, hpendOK, hcarOK,
      fun h => by simp [hro, Rope.toList_nil] at h⟩
  · have r3 := hns3.reads
    have rT' := hnsT.reads
    have rE' := hnsE.reads
    have hnil : ∀ (s : Rope (WItem P)) n, n ∈ wFV true s.toList → s.isNil = false :=
      fun s n hn => Bool.eq_false_iff.2 fun h => by simp [Rope.isNil_toList h, wFV] at hn
    refine ⟨fun b _ x hx => ?_, hpendOK, hcarOK, fun h => ?_⟩
    · rw [hro, ← List.singleton_append] at hx
      refine (wFV_app_pre (Pre := []) (fun n hn => .inr ?_) ?_ x hx (Q := fun n =>
        (∃ z ∈ S, z ∈ Block.freeVars [.ite (.det c) tss ess md] ∧ curName st' z = some n) ∨
          n ∈ RE.vars κ)).resolve_left (by simp [wDecls])
      · simp only [wFV, oreads, Bool.true_or, ↓reduceIte, List.filter_nil, List.append_nil] at hn
        rcases wreads_kIte hn with h | h | h
        · exact .inr h
        · obtain ⟨z, hz, hc⟩ := wRen_reads h1 n h
          exact .inl ⟨z, hcS z hz, hV z (.inr (.inr hz)),
            hS6 z n (hc56 z (hcS z hz) n (hc45 z (hcS z hz) n (hc14 z n hc)))⟩
        · simp [wreads] at h
      unfold laidPartsAx
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine wFV_app_pre ?p1 (wFV_app_pre ?p2 (wFV_app_pre ?p3 (wFV_app_pre ?p4 (wFV_app_pre ?p5
        (wFV_app_pre ?p6 (wFV_app_pre ?p7 (wFV_app_pre ?p8 (wFV_app_pre ?p9 (wFV_app_pre ?p10
        (wFV_app_pre ?p11 (wFV_app_pre ?p12 (wFV_app_pre ?p13 (wFV_app_pre ?p14 (wFV_app_pre ?p15
        (wFV_app_pre ?p16 (wFV_app_pre ?p17 ?p18))))))))))))))))
      case p1 | p2 | p3 | p12 =>
        intro n hn
        split at hn <;> simp only [Rope.toList_one, Rope.toList_nil, wFV, oreads, wreads,
          Bool.true_or, ↓reduceIte, List.filter_nil, List.append_nil, List.mem_singleton,
          List.not_mem_nil] at hn
        all_goals first
          | (refine .inl ?_; simp only [Bool.and_eq_true, List.cons_append, List.nil_append,
              List.append_assoc, Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
              Rope.toList_one, wDecls, hn, List.mem_cons, mem_wDecls_append, List.not_mem_nil,
              or_false, or_true, true_or]; done)
          | (refine .inr (.inr ?_); simp [RE.vars, hn])
      case p4 | p5 | p7 | p8 | p13 | p15 =>
        refine fun n hn => .inr (.inl (hsv n ?_))
        first | exact .inl (r3.1 n hn) | exact .inl (r3.2.1 n hn) | exact .inr (.inl (rT'.1 n hn)) |
          exact .inr (.inl (rT'.2.1 n hn)) | exact .inr (.inr (rE'.1 n hn)) |
          exact .inr (.inr (rE'.2.1 n hn))
      case p6 =>
        intro n hn
        rcases hRT.reads true (fun _ => rfl) n hn with ⟨z, hz, hv, hc⟩ | h
        · exact .inr (.inl ⟨z, hz, hV z (.inl hv), hS6 z n hc⟩)
        · obtain rfl := List.mem_singleton.1 h
          exact .inl (by simp [mem_wDecls_append, hnil _ _ hn, Rope.toList_one, wDecls])
      case p9 | p10 | p16 =>
        intro n hn
        first | refine (r3.2.2.1 n hn).elim (fun h => .inr (.inl (hsv n (.inl h)))) fun h => ?_ |
          refine (rT'.2.2.1 n hn).elim (fun h => .inr (.inl (hsv n (.inr (.inl h))))) fun h => ?_ |
          refine (rE'.2.2.1 n hn).elim (fun h => .inr (.inl (hsv n (.inr (.inr h))))) fun h => ?_
        exact .inl (by simp only [mem_wDecls_append, h, or_true, true_or])
      case p11 =>
        intro n hn
        split at hn
        · split at hn
          · simp [Rope.toList_nil, wFV] at hn
          · simp only [Rope.toList_one, wFV, oreads, Bool.true_or, ↓reduceIte, List.filter_nil,
              List.append_nil] at hn
            rcases wreads_kIte hn with h | h | h
            · exact .inr (.inr h)
            · have h' := List.mem_singleton.1 (wreads_not h)
              exact .inl (by simp [mem_wDecls_append, wDecls, h'])
            · simp [wreads] at h
        · simp [Rope.toList_nil, wFV] at hn
      case p14 =>
        intro n hn
        rcases hRE.reads true (fun _ => rfl) n hn with ⟨z, hz, hv, hc⟩ | h
        · exact .inr (.inl ⟨z, hz, hV z (.inr (.inl hv)), hS6 z n (hc56 z hz n hc)⟩)
        · rcases hκEv n h with rfl | h | h
          · exact .inl (by simp [mem_wDecls_append, wDecls])
          · exact .inl (by simp [mem_wDecls_append, h, hnil _ _ hn, wDecls, Rope.toList_one])
          · exact .inr (.inr h)
      case p17 =>
        intro n hn
        rw [laidMergesAx_toList] at hn
        obtain ⟨q, hq, hn | hn⟩ := mem_wFV_map_set _ _ hn
        · subst hn
          exact .inr (.inl (hsv _ (.inl (r3.2.2.2 q (List.mem_filter.1 hq).1).1)))
        · obtain ⟨hq1, hq2⟩ := r3.2.2.2 q (List.mem_filter.1 hq).1
          simp only [oreads] at hn
          split at hn
          · simp only [wreads, List.mem_append, List.mem_singleton] at hn
            rcases hn with (hn | rfl) | rfl
            · cases hg : gm? <;> simp only [hg, optVar, wreads, List.mem_singleton,
                List.not_mem_nil] at hn
              exact .inl (by simp [hn, mem_wDecls_append, wDecls, Rope.toList_one])
            · exact .inl (by simp only [mem_wDecls_append, hq2, or_true, true_or])
            · exact .inr (.inl (hsv _ (.inl hq1)))
          · obtain rfl := List.mem_singleton.1 hn
            exact .inl (by simp only [mem_wDecls_append, hq2, or_true, true_or])
      case p18 =>
        intro n hn
        replace hn := wFV_true hn
        have hUn := hnil _ n hn
        rcases hU n hn with rfl | h | h
        · exact .inl (by simp [mem_wDecls_append, hUn, wDecls, Rope.toList_one])
        · rcases hκEv n h with rfl | h | h
          · exact .inl (by simp [mem_wDecls_append, wDecls])
          · exact .inl (by simp [mem_wDecls_append, h, hUn, wDecls, Rope.toList_one])
          · exact .inr (.inr h)
        · exact .inr (.inr h)
    · rw [hobl, Bool.or_eq_true]
      rw [hro] at h
      unfold laidPartsAx at h
      have bU : (laidU κ κE rT T E d).toList.any WItem.isBranching = false := by
        unfold laidU
        cases κ <;> split <;> simp [setReach, Rope.toList_one, Rope.toList_nil, WItem.isBranching]
      have bM : (laidMergesAx gm? E (List.filter (fun p => liveBefore s6 p.fst s4.clock)
          cps3)).toList.any WItem.isBranching = false := by
        rw [laidMergesAx_toList]
        simp [WItem.isBranching]
      simp only [List.any_cons, WItem.isBranching, Bool.false_or, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.any_append, hns3.noBr, hnsT.noBr, hnsE.noBr, bU,
        bM, Bool.or_false, Bool.or_eq_true] at h
      rcases h with h | h | h | h | h | h | h <;> try exact .inl (hRT.br h)
      all_goals first | exact .inr (hRE.br h) | (repeat' split at h) <;> simp [Rope.toList_one,
        Rope.toList_nil, WItem.isBranching] at h

end -- public section

end WP
end Imperative
