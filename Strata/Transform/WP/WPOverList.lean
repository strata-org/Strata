/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
import Strata.Transform.WP.WPOverEmit
import Strata.Transform.WP.WPOverFacts
import Strata.Transform.WP.WPOverEffects
import Strata.DL.Imperative.BigStep.SemProps

/-! # The simulation through statement lists

The walk of the empty list, of a list `s :: rest` from those of `s` and `rest` (including the
drop after a main-list `exit` and the discard after a statement that always exits), and of the
statements without a WP rule have the simulation property (`Spec`).

Key theorems: `listSpec_nil`, `listSpec_cons`, `stmtSpec_other`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P]
  [iWL : WPLang P] [iIL : WPIteLang P]
  [iOp : HasOps P] [iF : LawfulHasFvar P] [iFs : LawfulHasFvars P] [iV : LawfulHasVal P]
omit iIL
omit iI iOp iF iFs iV
variable {F : P.Factory} {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}
  {Lc S S' V V' D : List P.Ident} {Ex : P.Ident → Prop} {st st' : WSt P} {κ : RE P} {d : Nat}
  {σ σL : SemanticStore P} {s : PStmt P} {rest : PStmts P}
variable {tE : TypedEval P}


/-- `OnInv` survives replacing the read set by one with no more variables in scope. -/
private theorem OnInv.congrV (h : OnInv F T Y Lc Ex st κ S V σ σL) (hV : ∀ x ∈ S, x ∈ V' → x ∈ V) :
    OnInv F T Y Lc Ex st κ S V' σ σL :=
  ⟨⟨fun x hx hv => h.agree x hx (hV x hx hv), fun x hx hv => h.defd x hx (hV x hx hv),
    fun x hx hv => h.alike x hx (hV x hx hv), h.undef, h.canon, h.canonL, h.gtyped,
    fun x hx hv => h.ltyped x hx (hV x hx hv), h.fresh⟩, h.reach⟩

/-- `OffInv` survives replacing the scope and the read set by ones whose common variables are
    in scope and read before. -/
private theorem OffInv.congrV (h : OffInv F T Y Lc Ex st κ S V σL) (hV : ∀ x ∈ S', x ∈ V' →
    x ∈ S ∧ x ∈ V) : OffInv F T Y Lc Ex st κ S' V' σL := by grind [OffInv]

omit iDE iBE iLB iHB iHF iSF iHI iWL iHa iHFs in
/-- An obligation slot of a skeleton is one of the skeleton extended on the right. -/
private theorem SkObl.append_left {l : String} {a : List (SkEntry P)} (b : List (SkEntry P))
    (h : SkObl l a) : SkObl l (a ++ b) := by
  induction h <;> grind [SkObl]

omit iDE iBE iLB iHB iHF iSF iHI iWL iHa iHFs in
/-- An obligation slot of a skeleton is one of the skeleton extended on the left. -/
private theorem SkObl.append_right {l : String} (a : List (SkEntry P)) {b : List (SkEntry P)}
    (h : SkObl l b) : SkObl l (a ++ b) := by
  induction a <;> grind [SkObl]

omit iDE iHB iSF iHI iWL iHF in
/-- A variable in scope before a well-scoped `s` that the continuation `[s] :: rest :: k`
    reads is read by the continuation `(s :: rest) :: k`. -/
private theorem mem_contFV_split {k : List (PStmts P)} (hwf : Stmt.WellScoped Lc S s) {x : P.Ident}
    (hx : x ∈ S) (h : x ∈ contFV ([s] :: rest :: k)) : x ∈ contFV ((s :: rest) :: k) := by
  simp only [mem_contFV_cons] at h ⊢
  rcases s with ((⟨y, _, (_ | _), _⟩ | _) | _) | _ <;> grind [Block.freeVars, Stmt.WellScoped]

/-! ## Walk facts the composition uses -/

include iI in
omit iWL in
/-- A guarded store binding no name declared after the point after a walk binds none declared
    after the point before it. -/
private theorem FreshInv.back (hw : WalkCore D st st') (hf : FreshInv Lc Ex st' σL) :
    FreshInv Lc Ex st σL := by grind [FreshAt, FreshInv, WalkCore, freshName_counter_inj]

include iI in
/-- At a depth where `rest` registered a carried merge, the walk of `s` puts new merges in front
    of the merges of its input state: an index of the input list is shifted by the difference of
    the lengths.  A carried merge the combined result registered is one `s` registered, or one
    `rest` registered at the index shifted back by that difference. -/
private theorem carries_shift {fEnd f : Bool} {st1 st2 : WSt P} {r a : WRes P} (hwf : WFSt st)
    (hD : DeadBelow st) (hL : ∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d)
    (h1 : (wpList κ d fEnd rest).run st = .ok (r, st1))
    (h2 : (wpStmt κ d f s).run st1 = .ok (a, st2)) (k : Nat) :
    ((∃ q ∈ st1.carries.getD k [] ++ st2.carries.getD k [], q.2.2 ∈ r.regs.toList) →
      ∀ i q, (st1.carries.getD k [])[i]? = some q → (st2.carries.getD k [])[i +
        ((st2.carries.getD k []).length - (st1.carries.getD k []).length)]? = some q) ∧
    ∀ i n v xB, CarryReg (a.combine r) st2 k i n v xB → CarryReg a st2 k i n v xB ∨
      (st2.carries.getD k []).length - (st1.carries.getD k []).length ≤ i ∧
      CarryReg r st1 k (i - ((st2.carries.getD k []).length -
        (st1.carries.getD k []).length)) n v xB := by
  obtain ⟨pre, hpre, hc⟩ := wpStmt_carries hwf hL h1 h2 k
  have hnd : ∀ e ∈ r.regs.toList, st2.dead.contains e = false := fun e he => by
    have h1d := wpList_regs_live h1 hD e he
    obtain ⟨b, j, rfl, -, hj, -⟩ := wpList_regs h1 e he
    grind [wpStmt_dead h2 (freshName b j), → freshName_counter_inj]
  have hs : (∃ q ∈ st1.carries.getD k [] ++ st2.carries.getD k [], q.2.2 ∈ r.regs.toList) →
      st2.carries.getD k [] = pre ++ st1.carries.getD k [] := fun ⟨q, hq, hr⟩ =>
    hc.resolve_right fun h => h q hq hr
  refine ⟨fun hq i q hi => ?_, fun i n v xB ⟨hi, hx⟩ => ?_⟩
  · simp [hs hq, List.getElem?_append_right, hi]
  refine (List.mem_append.1 (by simpa only [WRes.combine, Rope.toList_app] using hx)).elim
    (fun hx => .inl ⟨hi, hx⟩) fun hx => ?_
  have he := hs ⟨_, List.mem_append_right _ (List.mem_of_getElem? hi), hx⟩
  by_cases hlt : i < pre.length
  · have hp : pre[i]? = some (n, v, xB) := (List.getElem?_append_left hlt).symm.trans (he ▸ hi)
    exact .inl ⟨hi, (hpre _ (List.mem_of_getElem? hp)).resolve_right (by simp [hnd _ hx])⟩
  · simp only [he, List.length_append, Nat.add_sub_cancel]
    exact .inr ⟨by omega, (List.getElem?_append_right (by omega)).symm.trans (he ▸ hi), hx⟩

include iI in
/-- `OffInv` after a walk gives `OffInv` before it, for a scope and read set whose common
    variables are in scope and read after the walk and not declared by the walked fragment. -/
private theorem OffInv.back (hw : WalkCore D st st') (h : OffInv F T Y Lc Ex st' κ S V σL)
    (hV : ∀ x ∈ S', x ∈ V' → x ∈ S ∧ x ∈ V ∧ x ∉ D) : OffInv F T Y Lc Ex st κ S' V' σL :=
  ⟨h.canonL, h.reach, h.bools, fun x hx hv n hn => h.defd x (hV x hx hv).1 (hV x hx hv).2.1 n
    (hw.names x n (hV x hx hv).2.2 hn), h.gtyped, FreshInv.back hw h.fresh⟩

/-- A walk that returns the empty result has the simulation property for a fragment that keeps
    the scope, never fails, ends every run normally in its start store without events, and whose
    shadow runs end normally. -/
private theorem spec_empty {m : WM P (WRes P)} {ss : PStmts P} {wf : List P.Ident → Prop}
    {fol : Bool} {hitP : SemanticStore P → List (Event P) → Prop}
    {runP : (Outcome P → Prop) → SemanticStore P → List (Event P) → Outcome P → Prop}
    {offP : SemanticStore P → (Outcome P → Prop) → Prop} (hm : m = pure {})
    (hS : ∀ S, scopeAfter S ss = S) (hhit : ∀ σ tr, ¬ hitP σ tr)
    (hrun : ∀ X σ evs o, runP X σ evs o → evs = [] ∧ o = .normal σ)
    (hoff : ∀ σs K, offP σs K → K (.normal σs)) : Spec F tE Lc κ d m ss wf fol hitP runP offP := by
  intro st r st' _ h T Y _ items hi S _ _ _ _ _ Ex _ k Lab _ _ _ _ _
  obtain ⟨rfl, rfl⟩ := wm_run_pure_ok (hm ▸ h)
  simp only [Rope.toList_nil] at hi
  cases hi
  rw [hS]
  refine ⟨fun _ _ _ _ _ _ _ h => (hhit _ _ h).elim, fun _ σ σL X evs o hon hr _ => ?_,
    fun _ σs σL _ hoff' hsh => ⟨[], σL, .nil, nofun, hoff'.congrV fun _ hx hv =>
    ⟨hx, contFV_tail_sub hv⟩, fun _ _ _ => rfl, ?_, ?_, ?_, fun _ => ⟨σs, hoff _ _ hsh⟩, ?_⟩⟩
  obtain ⟨rfl, rfl⟩ := hrun X σ evs o hr
  refine .inr ⟨[], σL, .nil, nofun, hon.congrV fun x _ hx => contFV_tail_sub hx, ?_⟩
  all_goals simp [SnapFF, CarryFF, CarryOK, CarryReg, ExitEnds, Rope.toList_nil]

/-- The walk of the empty list has the simulation property. -/
theorem listSpec_nil {F : P.Factory} (Lc : List P.Ident) (κ : RE P) (d : Nat) (fEnd : Bool) :
    ListSpec F tE Lc κ d fEnd [] := fun _ =>
  spec_empty (by rw [wpList]) (fun _ => rfl) nofun (fun _ _ _ _ h => by cases h; exact ⟨rfl, rfl⟩)
    fun _ _ h => h

include iI iOp iF iFs iV in
/-- The walk of `s :: rest` has the simulation property when the walks of `s` (for every
    obligation bit) and of `rest` have it. -/
theorem listSpec_cons {F : P.Factory} (hF : WellFormedSemanticEvalBase F) {Lc : List P.Ident}
    {κ : RE P} {d : Nat} {fEnd : Bool}
    {s : PStmt P} {rest : PStmts P} (hs : ∀ f, StmtSpec F tE Lc κ d f s)
    (hsT : StmtTyCtx Lc κ d s)
    (hr : ListSpec F tE Lc κ d fEnd rest) : ListSpec F tE Lc κ d fEnd (s :: rest) := by
  rintro htop st R st' hwf hrun T Y hfin items hitems S ⟨hwfs, hwfr⟩ Γ hΓ hwt hav Ex hEx k Lab hLab
    hκ hD hLK hhigh
  obtain ⟨hwts, hwtr⟩ := hwt.cons
  obtain ⟨r, st1, a, st2, h1, h2, hcase⟩ := wpList_run_cons hrun
  have hΓ2 : fEnd = true ∨ R.hasObl = true → TyCtx T Y st2 S Γ := fun hf x hx ty hty n hn =>
    hΓ hf x hx ty hty n
    (by rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> exact hn)
  have hw1 := wpList_walkOK h1
  have hw2 := wpStmt_walkOK h2
  have havRest : ∀ x ∈ Block.idents rest, AvoidedIfFresh st x := fun x hx =>
    hav x (by simp [Block.idents, hx])
  have hmem : ∀ x ∈ S ++ Block.idents [s], x ∈ S ++ Block.idents (s :: rest) := fun x hx =>
    by grind [Block.idents]
  have hdI : ∀ x ∈ stmtsInits rest, AvoidedIfFresh st x := fun x hx =>
    havRest x (wfl_inits_scope rest hwfr hx).2.1
  have hL : ∀ l t, st.labelDepth[l]? = some t → t ≤ d := fun l t hl => (hLab l t hl).1
  have hwf1 : WFSt st1 := hw1.wf hwf hdI
  obtain ⟨hst2, hfin2⟩ : st2.back = st'.back ∧ FinalOK Lc st2 T Y := by
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> exact ⟨rfl, hfin⟩
  have hfin1 : FinalOK Lc st1 T Y := by
    refine ⟨fun n ty hn => wpStmt_tys h2 hwf1 (fun x hx => (wfl_inits_scope [s] ⟨hwfs, trivial⟩
      hx).imp_right fun h => hw1.avoid ▸ hav x (hmem x (List.mem_append_right _ h.1))) hfin2.1 hn,
      fun n x hn => hfin2.2.1 n x (hw2.tyOf_keep hwf1 hn), fun n hn => ?_⟩
    rcases hfin2.2.2 n hn with hT | ⟨b, j, hj, hn', ha⟩
    · exact (Classical.em (st2.tyOf[n]? = st1.tyOf[n]?)).elim (.inl <| · ▸ hT) fun he =>
        .inr ((hw2.tyOf n he).imp fun b ⟨j, hj, ha, hn'⟩ => ⟨j, hj, hn', ha⟩)
    · exact .inr ⟨b, j, hj, Nat.le_trans hw2.next hn', hw2.avoid ▸ ha⟩
  have havR : ∀ x ∈ (Stmt.topInits s ++ S) ++ Block.idents rest, ∀ b j, x = freshName b j →
      st.avoid.contains x = true := fun x hx =>
    hav x (by grind [Block.idents, mem_idents_of_topInit])
  have hExS : ∀ y, Ex y → (∀ b j, y = freshName b j → j < st1.next) ∧ st2.back[y]? = none :=
    fun y hy => ⟨fun b j hj => Nat.lt_of_lt_of_le ((hEx y hy).1 b j hj) hw1.next,
      hst2 ▸ (hEx y hy).2⟩
  have hLab' : ∀ l t, st.labelDepth[l]? = some t → ∀ x ∈ Lab l, x ∈ contFV k ∧ x ∈ S :=
    fun l t hl => (hLab l t hl).2
  have hnmW : ∀ {D : List P.Ident} {s0 s1 : WSt P}, WalkCore D s0 s1 → ∀ y ∈ RE.vars κ,
      (∃ b j, y = freshName b j ∧ j < s0.next) → (∀ x : P.Ident, s0.nm[x]? ≠ some y) →
      ∀ x : P.Ident, s1.nm[x]? ≠ some y := fun hw y _ hf hn x hx =>
    (hw.nm x y hx).elim (hn x) fun h => absurd rfl (FreshAt.ne h hf)
  have hκS : ∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st1.next) ∧
      st1.avoid.contains y = false ∧ (∀ x : P.Ident, st1.nm[x]? ≠ some y) ∧
      st1.back[y]? = none := fun y hy =>
    let ⟨⟨b, j, hj, hl⟩, ha, hn, hb⟩ := hκ y hy
    ⟨⟨b, j, hj, Nat.lt_of_lt_of_le hl hw1.next⟩, hw1.avoid ▸ ha,
      hnmW hw1.toWalkCore y hy ⟨b, j, hj, hl⟩ hn, (Classical.em _).elim (fun he => he.trans hb)
        fun he => absurd rfl (FreshAt.ne (hw1.back y he) ⟨b, j, hj, hl⟩)⟩
  have hκL : ∀ l t, st.labelDepth[l]? = some t → ∀ z ∈ Lab l, ∀ m, curName st1 z = some m →
      m ∉ RE.vars κ := fun l t hl z hz m hm hv => by
    obtain ⟨hf, ha, hn, -⟩ := hκS m hv
    have hm2 := hw2.names z m
      (fun h => (wfl_inits_scope [s] ⟨hwfs, trivial⟩ h).2.2 (hLab' l t hl z hz).2) hm
    exact (curName_cases hm2).elim (hnmW hw2.toWalkCore m hv hf hn z) fun ⟨_, _, he⟩ =>
      hf.elim fun b ⟨j, hj, _⟩ => absurd (hav z (List.mem_append_left _ (hLab' l t hl z hz).2) b j
        (he ▸ hj)) (by simp [← hw1.avoid, ← he, ha])
  have hD1 := wpList_deadBelow h1 hD
  have hfT : fEnd = true → (r.hasObl || (fEnd && !r.drop)) = true := fun hf => by
    simp [hf, Bool.eq_false_iff.2 fun hd => absurd (htop (wpList_drop h1 hd)) (by simp [hf])]
  have hfs : fEnd = true ∨ r.hasObl = true → (r.hasObl || (fEnd && !r.drop)) = true :=
    fun h => h.elim hfT fun h => by simp [h]
  have hSs := fun ia (hia : resolveItems T Y a.out.toList = .ok ia)
      (hT : (r.hasObl || (fEnd && !r.drop)) = true ∨ a.hasObl = true → TyCtx T Y st2 S Γ) =>
    hs _ st1 a st2 hwf1 h2 T Y hfin2 ia hia S hwfs Γ hT hwts
      (fun x hx => hw1.avoid ▸ hav x (hmem x hx)) Ex hExS (rest :: k) Lab
      (fun l t hl => (hLab l t ((hw1.labelDepth l).symm.trans hl)).imp_right fun h x hx =>
        (h x hx).imp_left (contFV_tail_sub ·)) hκS (wpList_deadBelow h1 hD)
      (wpList_liveKeys h1 hwf havRest (fun y hy => .inr (hκ y hy).1) hLK)
      fun k hk => List.eq_nil_iff_forall_not_mem.2 fun q hq => by
        simpa [hhigh k hk] using wpList_carries_high h1 hL k hk q hq
  have hRs := fun ir (hir : resolveItems T Y r.out.toList = .ok ir)
      (hT : fEnd = true ∨ r.hasObl = true → TyCtx T Y st2 S Γ) =>
    hr htop st r st1 hwf h1 T Y hfin1 ir hir (Stmt.topInits s ++ S) hwfr _
      (fun ho => hsT st1 a st2 hwf1 (hfs ho ▸ h2) T Y hfin2 S hwfs
        (fun x hx => hw1.avoid ▸ hav x (hmem x hx)) Γ (hT ho)) hwtr havR Ex (fun y hy =>
      ⟨(hEx y hy).1, Option.eq_none_iff_forall_ne_some.2 fun _ hb =>
        nomatch (hExS y hy).2.symm.trans (hw2.back_keep hwf1 hb)⟩) k Lab (fun l t hl =>
        (hLab l t hl).imp_right fun h x hx => (h x hx).imp_right (List.mem_append_right _)) hκ hD
      hLK hhigh
  have hκt : fEnd = true → κ ≠ .top := fun hf h => by rw [htop h] at hf; cases hf
  have hVon : ∀ σ σL, OnInv F T Y Lc Ex st2 κ S (contFV ((s :: rest) :: k)) σ σL →
      OnInv F T Y Lc Ex st2 κ S (contFV ([s] :: rest :: k)) σ σL :=
    fun _ _ h => h.congrV fun _ hx hm => mem_contFV_split hwfs hx hm
  have hback : ∀ x ∈ S, x ∈ contFV k → x ∈ S ∧ x ∈ contFV (rest :: k) ∧
      x ∉ stmtsInits rest := fun x hx hv =>
    ⟨hx, contFV_tail_sub hv, wfl_inits_disjoint _ rest hwfr x (List.mem_append_right _ hx)⟩
  have hVoff : ∀ σL, OffInv F T Y Lc Ex st2 κ S (contFV ((s :: rest) :: k)) σL →
      OffInv F T Y Lc Ex st2 κ S (contFV ([s] :: rest :: k)) σL :=
    fun _ h => h.congrV fun _ hx hm => ⟨hx, mem_contFV_split hwfs hx hm⟩
  have hVL : ∀ l t, st.labelDepth[l]? = some t → ∀ x ∈ Lab l, x ∈ Stmt.topInits s ++ S :=
    fun l t hl x hx => List.mem_append_right _ (hLab' l t hl x hx).2
  have hXB : fEnd = true → ∀ {l t}, st.labelDepth[l]? = some t →
      ∀ {st2 st2' : WSt P} {a R : WRes P} {σ1 σL1 σL2 : SemanticStore P},
      (∀ x ∈ Lab l, ∀ n, curName st1 x = some n → σL2 n = σL1 n) →
      (∀ n w, σL2 n = σL1 n → CarryAgree F T Y a st2 t σL1 n w →
        CarryAgree F T Y R st2' t σL2 n w) →
      ExitCore F T Y Lc Ex st1 st2 a t (Stmt.topInits s ++ S) (Lab l) σ1 σL1 →
      FreshInv Lc Ex st σL2 → WellFormedStore σL2 F →
      (∀ n w, σL2 n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty) →
      ExitCore F T Y Lc Ex st st2' R t (scopeAfter (Stmt.topInits s ++ S) rest) (Lab l) σ1 σL2 :=
    fun hf l t hld _ _ _ _ _ _ _ hkeep htr hc hfr hcan hgt => by
      have hn1 : ∀ x ∈ Lab l, ∀ n, curName st x = some n → curName st1 x = some n :=
        fun x hv n hn => hw1.names x n (wfl_inits_disjoint _ rest hwfr x (hVL l t hld x hv)) hn
      exact { hc with
        xagree := fun x _ hv n hn hl hf' w hw' => htr n w (hkeep x hv n (hn1 x hv n hn))
          (hc.xagree x (hVL l t hld x hv) hv n (hn1 x hv n hn) (wpList_live_keep h1 (hκt hf) hwf
            hdI x _ (wfl_inits_disjoint _ rest hwfr x (hVL l t hld x hv))
              (hav x (List.mem_append_left _ (hLab' l t hld x hv).2)) hn hl)
            (LiveFrom.walk hw1.toWalkCore hw1.labelDepth hwf (arm_liveKeep (hf ▸ h1) (hκt hf) hwf
              hwfr havR hL x (hVL l t hld x hv) n hn) hl hf') w hw')
        defd := fun x _ hv => ⟨(hc.defd x (hVL l t hld x hv) hv).1, fun n hn =>
          hkeep x hv n (hn1 x hv n hn) ▸ (hc.defd x (hVL l t hld x hv) hv).2 n (hn1 x hv n hn)⟩
        alike := fun x _ hv n hn hty w w' h1 h2 => hc.alike x (hVL l t hld x hv) hv n
          (hn1 x hv n hn) hty w w' h1 (hkeep x hv n (hn1 x hv n hn) ▸ h2)
        undef := fun x hx hn => hc.undef x hx fun h => hn (scopeAfter_sub _ rest h)
        canonL := hcan
        gtyped := hgt
        ltyped := fun x _ hv n hn => hc.ltyped x (hVL l t hld x hv) hv n (hn1 x hv n hn)
        fresh := hfr }
  have hsplit : ∀ {σ : SemanticStore P} {t cnd b tr}, DReach F (s :: rest) σ tr →
      ClaimK b t cnd tr →
      DReachS F s σ tr ∨ ∃ σ1 evs1 evs2, DRunS F (fun _ => True) s σ evs1 (.normal σ1) ∧
        Trace.AssumptionsHold P evalInterp () evs1 ∧ DReach F rest σ1 evs2 ∧ ClaimK b t cnd evs2 ∧
        (r.hasObl || (fEnd && !r.drop)) = true ∧ tr = evs1 ++ evs2 := fun hreach hcl => by
    rcases hreach.cons_inv with hh | ⟨σ1, evs1, evs2, hs1, hr1, rfl⟩
    · exact .inl hh
    rcases Classical.em (evs2 = []) with rfl | he2
    · rw [List.append_nil] at hcl ⊢
      exact .inl (hs1.toReachS fun h => by simp [h, ClaimK] at hcl)
    obtain ⟨hfe1, hcl2⟩ := claimK_split he2 hcl
    exact .inr ⟨σ1, evs1, evs2, hs1, hfe1, hr1, hcl2, Bool.of_not_eq_false fun hfv =>
      noObl_claim h1 hD (Bool.or_eq_false_iff.1 hfv).1 hr1 hcl2.claim, rfl⟩
  rcases hcase with ⟨hd, rfl, rfl⟩ | ⟨hd, hx, rfl, rfl⟩ | ⟨hd, hx, rfl, rfl⟩
  · obtain ⟨hκtop, l0, md0, rfl⟩ := wpStmt_drop h2 hd
    exact ⟨fun σ σL t cnd b tr hon hr hcl =>
      hr.cons_inv.elim (fun hh => (hSs items hitems fun _ => hΓ2
        (.inr (wpStmt_hit_hasObl h2 hD1 hh hcl.claim))).1 σ σL t cnd b tr (hVon _ _ hon) hh hcl)
      fun ⟨_, _, _, h, _⟩ => (nomatch h), (absurd hκtop <| hκt ·), (absurd hκtop <| hκt ·)⟩
  · have hS3 := fun (hT : TyCtx T Y st2 S Γ) => hSs items hitems fun _ => hT
    refine ⟨fun σ σL t cnd b tr hon hreach hcl => ?_, fun hf σ σL X evs o hon hrun hfeas => ?_,
      fun hf σs σL K hoff hsh => ?_⟩
    · have honS := hVon _ _ { hon with }
      rcases hsplit hreach hcl with hh | ⟨σ1, evs1, -, hs1, hfe1, -, -, hfv, -⟩
      · exact (hS3 (hΓ2 (.inr (wpStmt_hit_hasObl h2 hD1 hh hcl.claim)))).1 σ σL t cnd b tr honS
          hh hcl
      exact nomatch hx.symm.trans (wpStmt_ax_normal (hfv ▸ h2) hD1 hs1)
    · have honS := hVon _ _ { hon with }
      obtain ⟨-, runS, -⟩ := hS3 (hΓ2 (.inl hf))
      refine .inr ?_
      rcases hrun.cons_inv with ⟨σ1, evs1, evs2, hs1, -, rfl⟩ | ⟨l, σ1, hs1, rfl⟩
      · obtain ⟨-, -, -, -, -, -, -, -, hax, -⟩ := (runS (hfT hf) σ σL _ evs1 _ honS hs1
          ((Trace.AssumptionsHold_append _ _ _ _).1 hfeas).1).resolve_left fun h => hκt hf h.1
        exact nomatch hx.symm.trans hax
      · obtain ⟨tr1, σL1, hm1, hft1, hoff1, hends1, hq1, hok1, hmatch1⟩ :=
          (runS (hfT hf) σ σL _ evs (.exit l σ1) honS hs1 hfeas).resolve_left fun h => hκt hf h.1
        refine ⟨tr1, σL1, hm1, hft1, hoff1.back hw1.toWalkCore hback,
          ⟨by simp [hx], hends1.2⟩, hq1, hok1, ?_⟩
        rcases hld : st.labelDepth[l]? with _ | t <;> simp only [hw1.labelDepth l, hld] at hmatch1 ⊢
        · exact hmatch1
        obtain ⟨e, he, hp, htt, hsnap, hcore, hbelow⟩ := hmatch1
        exact ⟨e, he, hp, htt, hsnap, { hXB hf hld (fun _ _ _ _ => rfl) (fun _ _ _ h => h) hcore
          (FreshInv.back hw1.toWalkCore hcore.fresh) hcore.canonL hcore.gtyped with }, hbelow⟩
    · obtain ⟨-, -, offS⟩ := hS3 (hΓ2 (.inl hf))
      obtain ⟨tr1, σL1, hm1, hft1, hoff1, hfr1, hsnap1, hcf1, hok1, hends1⟩ :=
        offS (hfT hf) σs σL _ (hVoff _ { hoff with }) hsh
      have hoffC : OffInv F T Y Lc Ex st κ (if a.ax then S else scopeAfter S (s :: rest))
          (contFV k) σL1 := by
        simp only [hx, ↓reduceIte] at hoff1 ⊢
        exact hoff1.back hw1.toWalkCore hback
      exact ⟨tr1, σL1, hm1, hft1, hoffC, hfr1, hsnap1, hcf1, hok1,
        ⟨by simp [hx], hends1.2⟩⟩
  · rw [show (a.combine r).out = a.out.app r.out from rfl, Rope.toList_app,
      resolveItems_append] at hitems
    obtain ⟨ia, ir, hia, hir, rfl⟩ := hitems
    obtain ⟨hitS, runS, offS⟩ := hSs ia hia fun h => hΓ2 (by
      simp only [WRes.combine, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
      rcases h with (h | ⟨h, -⟩) | h <;> simp [h])
    obtain ⟨hitR, runR, offR⟩ := hRs ir hir fun h => hΓ2 (by
      simp only [WRes.combine, Bool.or_eq_true] at h ⊢
      rcases h with h | h <;> simp [h])
    have hcs := carries_shift hwf hD hL h1 h2
    have hκn := fun y (hy : y ∈ RE.vars κ) => (hκ y hy).imp_right (And.imp_right And.left)
    have hks := fun {σL1 σL2 tr} (hm : MainRun F ir σL1 tr σL2) =>
      keep_sel hF hwf h1 h2 hav hκn hir hm
    have hkr := fun {σL1 σL2 tr} (hm : MainRun F ir σL1 tr σL2) {e} (he : e ∈ a.regs.toList) =>
      keep_regs hwf h1 h2 hav hκn hir hm he
    have hme : ∀ e, e ∈ (a.combine r).regs.toList ↔ e ∈ a.regs.toList ∨ e ∈ r.regs.toList :=
      fun e => by simp only [WRes.combine, Rope.toList_app, List.mem_append]
    have hCC : ∀ {p : Nat → Prop} {σL1 σL2 tr}, MainRun F ir σL1 tr σL2 →
        WellFormedStore σL1 F →
        (∀ k i n v xB, p k → CarryReg a st2 k i n v xB → SelIs F T Y σL1 v false) →
        (∀ k i n v xB, p k → CarryReg r st1 k i n v xB → SelIs F T Y σL2 v false) →
        ∀ k i n v xB, p k → CarryReg (a.combine r) st2 k i n v xB → SelIs F T Y σL2 v false :=
      fun hm hC ha hr k i n v xB hk hc => ((hcs k).2 i n v xB hc).elim (fun hca =>
        (hks hm hC hca false).2 (ha k i n v xB hk hca)) fun ⟨_, hcr⟩ => hr k _ n v xB hk hcr
    have hOK : ∀ {σL1 σL2 tr}, MainRun F ir σL1 tr σL2 → WellFormedStore σL1 F →
        CarryOK F T Y a st2 σL1 → CarryOK F T Y r st1 σL2 →
        CarryOK F T Y (a.combine r) st2 σL2 := fun hm hC ha hr k i n v xB hc => by
      rcases (hcs k).2 i n v xB hc with hca | ⟨-, hcr⟩
      · obtain ⟨hsel, hty, ⟨w, hw, hwt⟩, ⟨u, hu, hut⟩⟩ := ha k i n v xB hca
        have hks1 := hks hm hC hca
        exact ⟨hsel.imp (hks1 true).2 (hks1 false).2, hty, keep_typed hm hw hwt,
          u, (hkr hm hca.2).trans hu, hut⟩
      · exact hr k _ n v xB hcr
    have hEA : ∀ {σL1 σL2 tr t S1 V σ1}, MainRun F ir σL1 tr σL2 → WellFormedStore σL1 F →
        CarryFF F T Y a st2 σL1 → ExitCore F T Y Lc Ex st st1 r t S1 V σ1 σL2 →
        ExitCore F T Y Lc Ex st st2 (a.combine r) t S1 V σ1 σL2 := fun hm hC ha hc => by
      refine { hc with xagree := fun x hx hv n hn hl hf w hw' => ?_ }
      obtain ⟨hb, hsel⟩ := hc.xagree x hx hv n hn hl hf w hw'
      have haF := fun k i v xB (hca : CarryReg a st2 k i n v xB) =>
        (hks hm hC hca false).2 (ha k i n v xB hca)
      have hR := fun {k i v xB} (h : CarryReg (a.combine r) st2 k i n v xB) => (hcs k).2 i n v xB h
      refine ⟨fun k i v xB hca => (hR hca).elim (fun h => .inr (haF k i v xB h))
        fun ⟨_, h⟩ => hb k _ v xB h, ?_⟩
      rcases hsel with ⟨hnone, hw''⟩ | ⟨k, i, v, xB, hk, hcr, htrue, hxw, hmax⟩
      · exact .inl ⟨fun k i v xB hk hca => (hR hca).elim (haF k i v xB)
          fun ⟨_, h⟩ => hnone k _ v xB hk h, hw''⟩
      have hfwd := (hcs k).1 ⟨_, List.mem_append_left _ (List.mem_of_getElem? hcr.1), hcr.2⟩ i _
        hcr.1
      refine .inr ⟨k, _, v, xB, hk, ⟨hfwd, (hme xB).2 (.inr hcr.2)⟩, htrue, hxw,
        fun k' i' v' xB' hk' hc' ht' => ?_⟩
      obtain ⟨hle, hc1⟩ := (hR hc').resolve_left fun ha' => SelIs.ne ht' (haF k' i' v' xB' ha')
      exact (hmax k' _ v' xB' hk' hc1 ht').imp_right fun ⟨he, hle'⟩ => ⟨he, by subst he; omega⟩
    have hsW : ∀ {q : WRes P} {sq : WSt P} {σq : SemanticStore P} {ex : Option P.Ident},
        SnapFF F q sq none σq → SnapFF F q sq ex σq := fun h l e he hp _ => h l e he hp (by simp)
    have hexW : ∀ {q : WRes P} {sq : WSt P} {K : Outcome P → Prop} {ex : Option String},
        ExitEnds q sq none K → ExitEnds q sq ex K := fun h l e he hp _ => h l e he hp (by simp)
    have hsnapC : ∀ {σL1 σL2 : SemanticStore P} {tr : List (Event P)} {ex : Option P.Ident},
        MainRun F ir σL1 tr σL2 → SnapFF F a st2 ex σL1 → SnapFF F r st1 ex σL2 →
        SnapFF F (a.combine r) st2 ex σL2 := fun hm ha hr l e he hp hne =>
      ((hme e).1 he).elim (fun h => (hkr hm h).trans (ha l e h hp hne))
        (fun h => hr l e h (pending_regs h1 h2 h hp) hne)
    have hexC : ∀ {K : Outcome P → Prop} {ex : Option String}, ExitEnds a st2 ex K →
        ExitEnds r st1 ex K → ExitEnds (a.combine r) st2 ex K := fun ha hr l e he hp hne =>
      ((hme e).1 he).elim (fun h => ha l e h hp hne)
        (fun h => hr l e h (pending_regs h1 h2 h hp) hne)
    refine ⟨fun σ σL t cnd b tr hon hreach hcl => ?_, fun hf σ σL X evs o hon hrun hfeas => ?_,
      fun hf σs σL K hoff hsh => ?_⟩
    · have honS := hVon _ _ hon
      rcases hsplit hreach hcl with hh | ⟨σ1, evs1, evs2, hs1, hfe1, hr1, hcl2, hfv, rfl⟩
      · obtain ⟨hob, hsk, w, hw, tr', hhit, hc'⟩ := hitS σ σL t cnd b tr honS hh hcl
        exact ⟨by simp [WRes.combine, hob], hsk.append_left _, w, hw, tr', hhit.append_left, hc'⟩
      obtain ⟨tr1, σL1, hm1, hft1, hon1, -⟩ := (runS hfv σ σL (fun _ => True) evs1 (.normal σ1)
        honS hs1 hfe1).resolve_left fun ⟨_, _, _, h⟩ => nomatch h
      obtain ⟨hob, hsk, w, hw, tr2, hhit, hc⟩ := hitR σ1 σL1 t cnd b evs2 hon1 hr1 hcl2
      exact ⟨by simp [WRes.combine, hob], SkObl.append_right a.sk hsk, w,
        fun q hq => ⟨hw2.back_keep hwf1 (hw q hq).1, (hw q hq).2⟩, tr1 ++ tr2,
        HitIn.append_right hm1 hhit, claimK_prepend hft1 hc⟩
    · have honS := hVon _ _ hon
      have hqNe : ∀ q g, κ = .andNeg q g → q ≠ g := fun q g hqg he => by
        subst hqg he
        exact HasBool.ttVal_ne_ffVal F (Option.some.inj (hon.reach.1.symm.trans hon.reach.2))
      refine .inr ?_
      rcases hrun.cons_inv with ⟨σ1, evs1, evs2, hs1, hr1, rfl⟩ | ⟨l, σ1, hs1, rfl⟩
      · obtain ⟨tr1, σL1, hm1, hft1, hon1, hsnap1, hcf1, hok1, -, -, hexits1⟩ := (runS (hfT hf) σ
          σL _ evs1 _ honS hs1 ((Trace.AssumptionsHold_append _ _ _ _).1 hfeas).1).resolve_left
            fun h => hκt hf h.1
        have hC1 := hon1.canonL
        obtain ⟨tr2, σL2, hm2, hft2, hpost⟩ :=
          (runR hf σ1 σL1 X evs2 o hon1 hr1
            ((Trace.AssumptionsHold_append _ _ _ _).1 hfeas).2).resolve_left
            fun h => hκt hf h.1
        refine ⟨tr1 ++ tr2, σL2, hm1.append hm2, Trace.AssumptionsHold.append hft1 hft2, ?_⟩
        cases o with
        | normal σ' =>
          obtain ⟨honR, hsnapR, hcfR, hokR, haxR, hdropR, hexitsR⟩ := hpost
          exact ⟨honR, hsnapC hm2 hsnap1 hsnapR,
            fun k i n v xB => hCC (p := fun _ => True) hm2 hC1 (fun k i n v xB _ => hcf1 k i n v xB)
              (fun k i n v xB _ => hcfR k i n v xB) k i n v xB trivial,
            hOK hm2 hC1 hok1 hokR,
            by simp [WRes.combine, hx, haxR], hdropR, hexC hexits1 hexitsR⟩
        | exit l σ' =>
          obtain ⟨hoffR, hendsR, hqR, hokR, hmatchR⟩ := hpost
          refine ⟨hoffR.congrV fun _ hx hv => ⟨List.mem_append_right _ hx, hv⟩,
            ⟨fun h => hendsR.1 (Bool.or_eq_false_iff.1 h).2, hexC (hexW hexits1) hendsR.2⟩, hqR,
            hOK hm2 hC1 hok1 hokR, ?_⟩
          cases hld : st.labelDepth[l]? <;> simp only [hld] at hmatchR ⊢
          · exact hsnapC hm2 hsnap1 hmatchR
          obtain ⟨e, he, hp, htt, hsnap, hcore, hbelow⟩ := hmatchR
          exact ⟨e, (hme _).2 (.inr he), wpStmt_pending h2 hp, htt, hsnapC hm2 (hsW hsnap1) hsnap,
            hEA hm2 hC1 hcf1 hcore, hCC (p := (· < _)) hm2 hC1 (fun k i n v xB _ => hcf1 k i n v xB)
              hbelow⟩
      · obtain ⟨tr1, σL1, hm1, hft1, hoff1, hends1, hq1, hok1, hmatch1⟩ :=
          (runS (hfT hf) σ σL _ evs (.exit l σ1) honS hs1 hfeas).resolve_left fun h => hκt hf h.1
        obtain ⟨σv, hv⟩ := hends1.1 hx
        have hC1 := hoff1.canonL
        have hoff1' : OffInv F T Y Lc Ex st1 κ (Stmt.topInits s ++ S) (contFV (rest :: k)) σL1 := by
          cases s with
          | cmd c => cases hs1
          | _ => exact hoff1
        obtain ⟨tr2, σL2, hm2, hft2, hoff2, hfr2, hsnap2, hcf2, hok2, hends2⟩ :=
          offR hf σv σL1 X hoff1' hv
        have hS2 : ∀ x ∈ S, x ∈ (if r.ax then Stmt.topInits s ++ S
            else scopeAfter (Stmt.topInits s ++ S) rest) := fun x hx => by
          split <;> simp [hx, scopeAfter_sub _ rest (List.mem_append_right _ hx)]
        refine ⟨tr1 ++ tr2, σL2, hm1.append hm2, Trace.AssumptionsHold.append hft1 hft2,
          hoff2.congrV fun _ hx hv => ⟨hS2 _ hx, hv⟩,
          ⟨fun h => hends2.1 (Bool.or_eq_false_iff.1 h).2, hexC hends1.2 (hexW hends2.2)⟩,
          fun q g hqg => (keep_andNeg h1 havRest hκn hir hm2 hqg (hqNe q g hqg)).trans
            (hq1 q g hqg),
          hOK hm2 hC1 hok1 hok2, ?_⟩
        rcases hld : st.labelDepth[l]? with _ | t <;> simp only [hw1.labelDepth l, hld] at hmatch1 ⊢
        · exact hsnapC hm2 hmatch1 hsnap2
        obtain ⟨e, he, hp, htt, hsnap, hcore, hbelow⟩ := hmatch1
        refine ⟨e, (hme e).2 (.inl he), hp, (hkr hm2 he).trans htt, hsnapC hm2 hsnap (hsW hsnap2),
          ?_, hCC (p := (· < t)) hm2 hC1 hbelow (fun k i n v xB _ => hcf2 k i n v xB)⟩
        have hR : ∀ k i n v xB, CarryReg (a.combine r) st2 k i n v xB →
            CarryReg a st2 k i n v xB ∨ SelIs F T Y σL2 v false := fun k i n v xB hc =>
          ((hcs k).2 i n v xB hc).imp_right fun ⟨_, h⟩ => hcf2 k _ n v xB h
        have hka := fun {k i n v xB} (hca : CarryReg a st2 k i n v xB) => hks hm2 hcore.canonL hca
        refine hXB hf hld (fun x hx n hn => hfr2 n ((hcore.defd x (hVL l t hld x hx) hx).2 n hn)
          (hκL l t hld x hx n hn)) (fun n w heq ⟨hb, hsel⟩ => ?_) hcore hoff2.fresh
          hoff2.canonL hoff2.gtyped
        refine ⟨fun k i v xB hca => (hR k i n v xB hca).elim
          (fun ha => (hb k i v xB ha).imp (hka ha true).2 (hka ha false).2) .inr, ?_⟩
        rcases hsel with ⟨hnone, hw'⟩ | ⟨k, i, v, xB, hk, hca, htrue, hxw, hmax⟩
        · exact .inl ⟨fun k i v xB hk hc' => (hR k i n v xB hc').elim
            (fun ha => (hka ha false).2 (hnone k i v xB hk ha)) id, heq.trans hw'⟩
        refine .inr ⟨k, i, v, xB, hk, ⟨hca.1, (hme xB).2 (.inl hca.2)⟩, (hka hca true).2 htrue,
          (hkr hm2 hca.2).trans hxw, fun k' i' v' xB' hk' hc' ht' => ?_⟩
        have ha' := (hR k' i' n v' xB' hc').resolve_right (SelIs.ne ht')
        exact hmax k' i' v' xB' hk' ha' ((hka ha' true).1 ht')
    · obtain ⟨tr1, σL1, hm1, hft1, hoff1, hfr1, hsnap1, hcf1, hok1, hends1⟩ :=
        offS (hfT hf) σs σL _ (hVoff _ hoff) hsh
      obtain ⟨σv, hv⟩ := hends1.1 hx
      have hC1 := hoff1.canonL
      simp only [hx, Bool.false_eq_true, ↓reduceIte] at hoff1
      obtain ⟨tr2, σL2, hm2, hft2, hoff2, hfr2, hsnap2, hcf2, hok2, hends2⟩ :=
        offR hf σv σL1 K hoff1 hv
      have hoffC : OffInv F T Y Lc Ex st κ (if (a.combine r).ax then S
          else scopeAfter S (s :: rest)) (contFV k) σL2 := by
        simp only [WRes.combine, hx, Bool.false_or] at hoff2 ⊢
        cases hra : r.ax <;> simp only [hra, Bool.false_eq_true, ↓reduceIte] at hoff2 ⊢ <;>
          first | exact hoff2 | exact hoff2.congrV fun _ hx hv => ⟨List.mem_append_right _ hx, hv⟩
      exact ⟨tr1 ++ tr2, σL2, hm1.append hm2, Trace.AssumptionsHold.append hft1 hft2, hoffC,
        fun y hy hy' => (hfr2 y (by rw [hfr1 y hy hy']; exact hy) hy').trans (hfr1 y hy hy'),
        hsnapC hm2 hsnap1 hsnap2, fun k i n v xB => hCC (p := fun _ => True) hm2 hC1
          (fun k i n v xB _ => hcf1 k i n v xB) (fun k i n v xB _ => hcf2 k i n v xB) k i n v xB
          trivial,
        hOK hm2 hC1 hok1 hok2,
        ⟨fun h => hends2.1 (Bool.or_eq_false_iff.1 h).2, hexC hends1.2 hends2.2⟩⟩

/-- The walks of the statements without a WP rule (loops, nondeterministic guards) and of type
    declarations have the simulation property. -/
theorem stmtSpec_other {F : P.Factory} (Lc : List P.Ident) (κ : RE P) (d : Nat) (f : Bool)
    (s : PStmt P) (hs : (∀ c, s ≠ .cmd c) ∧ (∀ l md, s ≠ .exit l md) ∧
      (∀ l b md, s ≠ .block l b md) ∧ (∀ c t e md, s ≠ .ite (.det c) t e md)) :
    StmtSpec F tE Lc κ d f s := by
  obtain ⟨hc, he, hb, hit⟩ := hs
  rcases s with c | ⟨l, b, md⟩ | ⟨c | _, t, e, md⟩ | _ | ⟨l, md⟩ | _
  all_goals first
    | exact absurd rfl (hc _) | exact absurd rfl (he _ _) | exact absurd rfl (hb _ _ _)
    | exact absurd rfl (hit _ _ _ _) | (intro _ _ _ _ h; unfold wpStmt at h; cases h; done)
    | exact spec_empty (by unfold wpStmt; rfl) (fun _ => rfl) nofun
        (fun _ _ _ _ h => by cases h; exact ⟨rfl, rfl⟩) fun _ _ h => h

end -- public section

end WP
end Imperative
