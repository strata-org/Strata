/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.DeadDefsShape
public import Strata.DL.Imperative.BigStep.StoreAgree
import all Strata.Transform.Simplify.DeadDefsShape
import all Strata.Transform.Simplify
import Strata.Transform.Simplify.LiveSweep
import Strata.Languages.Core.IdentifiersProps
import Strata.DL.Imperative.StoreRelationsProps
import all Strata.Transform.DeadDefElimCorrect

/-! # The dead-definition sweep against a run

Over-approximation only needs the sweep's output to replay every run of its input: a
dropped `init` defines a variable nothing after it reads, so the output runs on with that
variable undefined, its store agreeing with the input's on everything that is still read.
Which definitions the sweep may drop (`Defined`, `surelyEvaluates`) plays no part here.

* `sweep_run`, `sweep_reach`: a run, or a run stopped after a command, of a list is replayed
  by a run of the swept list from any store agreeing on the names live before the list,
  with replaying events (`EvReplay`), to an outcome agreeing on the names live after it.
-/

namespace Core.Simplify

open Imperative Imperative.BigStep

/-- The identifiers a live set names. -/
def liveIds (L : Std.HashSet String) : List CoreIdent := L.toList.map fun n => ⟨n, ()⟩

/-- An identifier is among a live set's identifiers exactly when its name is in the set. -/
theorem mem_liveIds {L : Std.HashSet String} {x : CoreIdent} : x ∈ liveIds L ↔ x.name ∈ L := by
  simp only [liveIds, List.mem_map, Std.HashSet.mem_toList]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact hn
  · intro h; exact ⟨x.name, h, by cases x; rfl⟩

variable {Fl : Lambda.Factory CoreLParams} {M : Expression.Factory}

/-- Erasing an `init` of a variable that is not live: the store after it still agrees with
    the replaying store on what is live. -/
private theorem erase_init {x : CoreIdent} {ty : Expression.Ty} {e : Expression.Expr}
    {md : MetaData Expression} {L : Std.HashSet String} (hx : x.name ∉ L)
    {σ σ1 σ' : SemanticStore Expression} {evs : List (Event Expression)}
    (h : BRunS M (.cmd (.cmd (.init x ty (.det e) md))) σ evs (.normal σ1))
    (hC : WellFormedStore σ M) (hA : Agree (liveIds L) σ σ') :
    evs = [] ∧ Agree (liveIds L) σ1 σ' ∧ WellFormedStore σ1 M := by
  cases h with
  | cmd h =>
    obtain ⟨v, -, h0, h1, hfr, rfl, hty⟩ := EvalCmdE.init_det_inv h
    have hne : ∀ y : CoreIdent, y ∈ liveIds L → x ≠ y := fun y hy hxy =>
      hx (hxy ▸ mem_liveIds.mp hy)
    refine ⟨rfl, ⟨fun y hy => by rw [hfr y (hne y hy), hA.1 y hy], ?_⟩, fun y w hw => ?_⟩
    · refine storeAgreement_iff.2 fun y => ?_
      by_cases hxy : x = y
      · subst hxy
        exact .inr ((storeAgreement_iff.1 hA.2 x).elim (·.trans h0) id)
      · rw [hfr y hxy]; exact storeAgreement_iff.1 hA.2 y
    · by_cases hxy : x = y
      · subst hxy; rw [h1] at hw; cases hw
        exact LawfulHasVal.valueOfTy_isVal _ _ _ hty
      · exact hC y w (hfr y hxy ▸ hw)

/-- Agreement on a live set gives agreement on any smaller one. -/
private theorem agree_of_live {L L' : Std.HashSet String} {σ σ' : SemanticStore Expression}
    (hA : Agree (liveIds L) σ σ') (h : ∀ n, n ∈ L' → n ∈ L) : Agree (liveIds L') σ σ' :=
  hA.mono fun _ hy => mem_liveIds.mpr (h _ (mem_liveIds.mp hy))

/-- The live set before a swept branch holds the names live after it, the guard's variables,
    and the live sets before its two arms, each swept on its own. -/
private theorem ite_live (D : Defined) (L : Std.HashSet String) (added : List String)
    (c : ExprOrNondet Expression) (ts es : List Statement) (md : MetaData Expression) :
    let before := (dropDeadDefsStmt Fl D L added (.ite c ts es md)).2.1
    (∀ n ∈ c.getVars.map (·.name), n ∈ before) ∧ (∀ n, n ∈ L → n ∈ before) ∧
      (∀ n, n ∈ (dropDeadDefsAux Fl D L [] ts).2.1 → n ∈ before) ∧
      (∀ n, n ∈ (dropDeadDefsAux Fl D L [] es).2.1 → n ∈ before) := by
  intro before
  have hmem := mem_dropDeadDefsStmt_live (F := Fl) D L added (.ite c ts es md)
  rw [dropDeadDefsStmt_ite_arms] at hmem
  simp only [Stmt.getVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars,
    Bool.false_eq_true, ↓reduceIte, List.map_append, List.mem_append] at hmem
  refine ⟨fun n hn => (hmem n).mpr (by simp [hn]), fun n hn => (hmem n).mpr (.inl hn),
    fun n hn => ?_, fun n hn => ?_⟩
  · rcases (mem_dropDeadDefsAux_live D L [] ts n).mp hn with hn | hn | hn
    · exact (hmem n).mpr (.inl hn)
    · exact (hmem n).mpr (.inr (.inl (.inl (.inr hn))))
    · simp only [Block.modifiedOrDefinedVars, List.map_append, List.mem_append] at hn
      exact (hmem n).mpr (by grind)
  · rcases (mem_dropDeadDefsAux_live D L [] es n).mp hn with hn | hn | hn
    · exact (hmem n).mpr (.inl hn)
    · exact (hmem n).mpr (.inr (.inl (.inr hn)))
    · simp only [Block.modifiedOrDefinedVars, List.map_append, List.mem_append] at hn
      exact (hmem n).mpr (by grind)

mutual
/-- **The swept list replays the run of the list**, from any store agreeing on the names
    live before the list, to an outcome agreeing on the names live after it. -/
theorem sweep_run (hE : EvCongr M) : ∀ {ss : PStmts Expression} {σ : SemanticStore Expression}
    {evs : List (Event Expression)} {o : Outcome Expression}, BRun M ss σ evs o →
    Block.noLoops ss = true → ∀ {D : Defined} {L : Std.HashSet String} {added : List String}
      {σ' : SemanticStore Expression}, WellFormedStore σ M →
      Agree (liveIds (dropDeadDefsAux Fl D L added ss).2.1) σ σ' →
      ∃ evs' o', BRun M (dropDeadDefsAux Fl D L added ss).1 σ' evs' o' ∧
        List.Rel₂ (EvReplay M) evs evs' ∧ OAgree M (liveIds L) o o'
  | _, _, _, _, .nil, _, D, L, added, σ', hC, hA => by
    rw [dropDeadDefsAux_nil] at hA ⊢
    exact ⟨[], _, .nil, .nil, hA, hC⟩
  | _, _, _, _, .cons_normal (s := s) (rest := rest) h1 h2, hnl, D, L, added, σ', hC, hA => by
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    by_cases hdead : ∃ x, definedBy Fl D s = some x ∧
        (dropDeadDefsAux Fl (D.after s) L added rest).2.1.contains x.name = false
    · obtain ⟨x, hdef, hfalse⟩ := hdead
      rw [dropDeadDefsAux_cons_dead hdef hfalse] at hA ⊢
      obtain ⟨ty, e, md, rfl, -⟩ := init_of_definedBy hdef
      have hx : x.name ∉ (dropDeadDefsAux Fl (D.after _) L added rest).2.1 := fun h => by
        rw [Std.HashSet.mem_iff_contains, hfalse] at h; cases h
      obtain ⟨rfl, hA1, hC1⟩ := erase_init hx h1 hC hA
      exact sweep_run hE h2 hnl.2 hC1 hA1
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead)] at hA ⊢
      obtain ⟨evs1', o1', h1', hm1, hO1⟩ := sweep_runS hE h1 hnl.1 hC hA
      rcases o1' with σ1' | _ <;> simp only [OAgree] at hO1
      obtain ⟨evs2', o', h2', hm2, hO⟩ := sweep_run hE h2 hnl.2 hO1.2 hO1.1
      exact ⟨evs1' ++ evs2', o', .cons_normal h1' h2', hm1.append hm2, hO⟩
  | _, _, _, _, .cons_exit (s := s) (rest := rest) h1, hnl, D, L, added, σ', hC, hA => by
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    by_cases hdead : ∃ x, definedBy Fl D s = some x ∧
        (dropDeadDefsAux Fl (D.after s) L added rest).2.1.contains x.name = false
    · obtain ⟨x, hdef, -⟩ := hdead
      obtain ⟨ty, e, md, rfl, -⟩ := init_of_definedBy hdef
      cases h1
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead)] at hA ⊢
      obtain ⟨evs1', o1', h1', hm1, hO1⟩ := sweep_runS hE h1 hnl.1 hC hA
      rcases o1' with _ | ⟨l', σ1'⟩ <;> simp only [OAgree] at hO1
      obtain ⟨rfl, hA1, hC1⟩ := hO1
      refine ⟨evs1', _, .cons_exit h1', hm1, rfl, ?_, hC1⟩
      exact agree_of_live hA1 fun n hn =>
        live_iff_mem.mp (live_dropDeadDefsAux_mono (D.after s) L added rest
          (x := ⟨n, ()⟩) (live_iff_mem.mpr hn))
/-- `sweep_run` for one statement, swept with the names live after it. -/
private theorem sweep_runS (hE : EvCongr M) :
    ∀ {s : PStmt Expression} {σ : SemanticStore Expression}
    {evs : List (Event Expression)} {o : Outcome Expression}, BRunS M s σ evs o →
    Stmt.noLoops s = true → ∀ {D : Defined} {L : Std.HashSet String} {added : List String}
      {σ' : SemanticStore Expression}, WellFormedStore σ M →
      Agree (liveIds (dropDeadDefsStmt Fl D L added s).2.1) σ σ' →
      ∃ evs' o', BRunS M (dropDeadDefsStmt Fl D L added s).1 σ' evs' o' ∧
        List.Rel₂ (EvReplay M) evs evs' ∧ OAgree M (liveIds L) o o'
  | _, σ, _, _, .cmd (c := .cmd c) h, _, D, L, added, σ', hC, hA => by
    rw [dropDeadDefsStmt_cmd] at hA ⊢
    have hA' : Agree (Stmt.idents (.cmd (.cmd c) : PStmt Expression) ++ liveIds L) σ σ' :=
      hA.mono fun y hy => by
        refine mem_liveIds.mpr ((insertTracked_mem _ _ _ _).mpr ?_)
        rcases List.mem_append.mp hy with hy | hy
        · refine .inr (List.mem_map.mpr ⟨y, ?_, rfl⟩)
          rcases Stmt.idents_subset_vars _ y hy with h | h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_append_left _ h)
          · exact List.mem_append_right _ (List.mem_append_right _ h)
        · exact .inl (mem_liveIds.mp hy)
    obtain ⟨σ1', evs', h', hm, hA1, hC1⟩ := cmd_sim hE h hC hA'
    exact ⟨evs', _, .cmd h', hm, hA1, hC1⟩
  | _, _, _, _, .cmd (c := .call _ _ _ _) h, _, _, _, _, _, _, _ => h.elim
  | _, _, _, _, .ite_true (c := c) (tss := ts) (ess := es) (md := md) hc h, hnl, D, L, added, σ',
      hC, hA => by
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨hg, hL, ht, -⟩ := ite_live (Fl := Fl) D L added (.det c) ts es md
    rw [dropDeadDefsStmt_ite_arms]
    have hc' : Expression.eval M σ' c = some (HasBool.ttVal M) := by
      rw [ev_agree hE hC hA fun y hy => mem_liveIds.mpr (hg _ (List.mem_map.mpr ⟨y, hy, rfl⟩))]
      exact hc
    obtain ⟨evs', o', h', hm, hO⟩ := sweep_run hE h hnl.1 hC (agree_of_live hA ht)
    exact ⟨evs', _, .ite_true hc' h', hm, hO.proj (agree_of_live hA hL)⟩
  | _, _, _, _, .ite_false (c := c) (tss := ts) (ess := es) (md := md) hc h, hnl, D, L, added, σ',
      hC, hA => by
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨hg, hL, -, he⟩ := ite_live (Fl := Fl) D L added (.det c) ts es md
    rw [dropDeadDefsStmt_ite_arms]
    have hc' : Expression.eval M σ' c = some (HasBool.ffVal M) := by
      rw [ev_agree hE hC hA fun y hy => mem_liveIds.mpr (hg _ (List.mem_map.mpr ⟨y, hy, rfl⟩))]
      exact hc
    obtain ⟨evs', o', h', hm, hO⟩ := sweep_run hE h hnl.2 hC (agree_of_live hA he)
    exact ⟨evs', _, .ite_false hc' h', hm, hO.proj (agree_of_live hA hL)⟩
  | _, _, _, _, .ite_nondet_true (tss := ts) (ess := es) (md := md) h, hnl, D, L, added, σ',
      hC, hA => by
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨-, hL, ht, -⟩ := ite_live (Fl := Fl) D L added .nondet ts es md
    rw [dropDeadDefsStmt_ite_arms]
    obtain ⟨evs', o', h', hm, hO⟩ := sweep_run hE h hnl.1 hC (agree_of_live hA ht)
    exact ⟨evs', _, .ite_nondet_true h', hm, hO.proj (agree_of_live hA hL)⟩
  | _, _, _, _, .ite_nondet_false (tss := ts) (ess := es) (md := md) h, hnl, D, L, added, σ',
      hC, hA => by
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨-, hL, -, he⟩ := ite_live (Fl := Fl) D L added .nondet ts es md
    rw [dropDeadDefsStmt_ite_arms]
    obtain ⟨evs', o', h', hm, hO⟩ := sweep_run hE h hnl.2 hC (agree_of_live hA he)
    exact ⟨evs', _, .ite_nondet_false h', hm, hO.proj (agree_of_live hA hL)⟩
  | _, _, _, _, .block (ss := ss) (l := l) (md := md) h, hnl, D, L, added, σ', hC, hA => by
    rw [Stmt.noLoops_block] at hnl
    rw [dropDeadDefsStmt_block] at hA ⊢
    obtain ⟨evs', o', h', hm, hO⟩ := sweep_run hE h hnl hC hA
    exact ⟨evs', _, .block h', hm, hO.block l (agree_of_live hA fun n hn =>
      live_iff_mem.mp (live_dropDeadDefsAux_mono D L added ss (x := ⟨n, ()⟩)
        (live_iff_mem.mpr hn)))⟩
  | _, _, _, _, .exit (l := l) (md := md), _, D, L, added, σ', hC, hA => by
    rw [dropDeadDefsStmt_exit] at hA ⊢
    exact ⟨[], _, .exit, .nil, rfl, hA, hC⟩
  | _, _, _, _, .typeDecl (tc := tc) (md := md), _, D, L, added, σ', hC, hA => by
    rw [dropDeadDefsStmt_typeDecl] at hA ⊢
    exact ⟨[], _, .typeDecl, .nil, hA, hC⟩
  | _, _, _, _, .loop_exit _, hnl, _, _, _, _, _, _
  | _, _, _, _, .loop_iter _ _ _, hnl, _, _, _, _, _, _
  | _, _, _, _, .loop_break _ _, hnl, _, _, _, _, _, _ => by simp [Stmt.noLoops_loop] at hnl
end


mutual
/-- **The swept list replays every prefix of a run of the list** that emits an event. -/
theorem sweep_reach (hE : EvCongr M) : ∀ {ss : PStmts Expression}
    {σ : SemanticStore Expression} {evs : List (Event Expression)}, BReach M ss σ evs →
    evs ≠ [] → Block.noLoops ss = true →
    ∀ {D : Defined} {L : Std.HashSet String} {added : List String}
      {σ' : SemanticStore Expression}, WellFormedStore σ M →
      Agree (liveIds (dropDeadDefsAux Fl D L added ss).2.1) σ σ' →
      ∃ evs', BReach M (dropDeadDefsAux Fl D L added ss).1 σ' evs' ∧
        List.Rel₂ (EvReplay M) evs evs'
  | _, _, _, .here (s := s) (rest := rest) h, hne, hnl, D, L, added, σ', hC, hA => by
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    by_cases hdead : ∃ x, definedBy Fl D s = some x ∧
        (dropDeadDefsAux Fl (D.after s) L added rest).2.1.contains x.name = false
    · obtain ⟨x, hdef, -⟩ := hdead
      obtain ⟨ty, e, md, rfl, -⟩ := init_of_definedBy hdef
      cases h with
      | cmd h _ =>
        obtain ⟨_, -, -, -, -, he, -⟩ := EvalCmdE.init_det_inv h
        exact absurd he hne
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead)] at hA ⊢
      obtain ⟨evs', h', hm⟩ := sweep_reachS hE h hne hnl.1 hC hA
      exact ⟨evs', .here h', hm⟩
  | _, _, _, .later (s := s) (rest := rest) (evs1 := evs1) (evs2 := evs2) h1 h2, hne, hnl, D, L,
      added, σ', hC, hA => by
    rw [Block.noLoops_cons, Bool.and_eq_true] at hnl
    by_cases hdead : ∃ x, definedBy Fl D s = some x ∧
        (dropDeadDefsAux Fl (D.after s) L added rest).2.1.contains x.name = false
    · obtain ⟨x, hdef, hfalse⟩ := hdead
      rw [dropDeadDefsAux_cons_dead hdef hfalse] at hA ⊢
      obtain ⟨ty, e, md, rfl, -⟩ := init_of_definedBy hdef
      have hx : x.name ∉ (dropDeadDefsAux Fl (D.after _) L added rest).2.1 := fun h => by
        rw [Std.HashSet.mem_iff_contains, hfalse] at h; cases h
      obtain ⟨rfl, hA1, hC1⟩ := erase_init hx h1 hC hA
      exact sweep_reach hE h2 (by simpa using hne) hnl.2 hC1 hA1
    · rw [dropDeadDefsAux_cons_keep (keep_of_not_dead hdead)] at hA ⊢
      obtain ⟨evs1', o1', h1', hm1, hO1⟩ := sweep_runS hE h1 hnl.1 hC hA
      rcases o1' with σ1' | _ <;> simp only [OAgree] at hO1
      by_cases he2 : evs2 = []
      · subst he2
        have hne1 : evs1' ≠ [] := hm1.ne_nil (by simpa using hne)
        exact ⟨evs1', .here (brunS_breach h1' hne1), by simpa using hm1⟩
      · obtain ⟨evs2', h2', hm2⟩ := sweep_reach hE h2 he2 hnl.2 hO1.2 hO1.1
        exact ⟨evs1' ++ evs2', .later h1' h2', hm1.append hm2⟩
/-- `sweep_reach` for one statement. -/
private theorem sweep_reachS (hE : EvCongr M) : ∀ {s : PStmt Expression}
    {σ : SemanticStore Expression} {evs : List (Event Expression)}, BReachS M s σ evs →
    evs ≠ [] → Stmt.noLoops s = true →
    ∀ {D : Defined} {L : Std.HashSet String} {added : List String}
      {σ' : SemanticStore Expression}, WellFormedStore σ M →
      Agree (liveIds (dropDeadDefsStmt Fl D L added s).2.1) σ σ' →
      ∃ evs', BReachS M (dropDeadDefsStmt Fl D L added s).1 σ' evs' ∧
        List.Rel₂ (EvReplay M) evs evs'
  | _, σ, _, .cmd (c := .cmd c) h hne0, _, _, D, L, added, σ', hC, hA => by
    rw [dropDeadDefsStmt_cmd] at hA ⊢
    have hA' : Agree (Stmt.idents (.cmd (.cmd c) : PStmt Expression) ++ liveIds L) σ σ' :=
      hA.mono fun y hy => by
        refine mem_liveIds.mpr ((insertTracked_mem _ _ _ _).mpr ?_)
        rcases List.mem_append.mp hy with hy | hy
        · refine .inr (List.mem_map.mpr ⟨y, ?_, rfl⟩)
          rcases Stmt.idents_subset_vars _ y hy with h | h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_append_left _ h)
          · exact List.mem_append_right _ (List.mem_append_right _ h)
        · exact .inl (mem_liveIds.mp hy)
    obtain ⟨σ1', evs', h', hm, -, -⟩ := cmd_sim hE h hC hA'
    exact ⟨evs', .cmd h' (hm.ne_nil hne0), hm⟩
  | _, _, _, .cmd (c := .call _ _ _ _) h _, _, _, _, _, _, _, _, _ => h.elim
  | _, _, _, .ite_true (c := c) (tss := ts) (ess := es) (md := md) hc h, hne, hnl, D, L, added, σ',
      hC, hA => by
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨hg, -, ht, -⟩ := ite_live (Fl := Fl) D L added (.det c) ts es md
    rw [dropDeadDefsStmt_ite_arms]
    have hc' : Expression.eval M σ' c = some (HasBool.ttVal M) := by
      rw [ev_agree hE hC hA fun y hy => mem_liveIds.mpr (hg _ (List.mem_map.mpr ⟨y, hy, rfl⟩))]
      exact hc
    obtain ⟨evs', h', hm⟩ := sweep_reach hE h hne hnl.1 hC (agree_of_live hA ht)
    exact ⟨evs', .ite_true hc' h', hm⟩
  | _, _, _, .ite_false (c := c) (tss := ts) (ess := es) (md := md) hc h, hne, hnl, D, L, added, σ',
      hC, hA => by
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨hg, -, -, he⟩ := ite_live (Fl := Fl) D L added (.det c) ts es md
    rw [dropDeadDefsStmt_ite_arms]
    have hc' : Expression.eval M σ' c = some (HasBool.ffVal M) := by
      rw [ev_agree hE hC hA fun y hy => mem_liveIds.mpr (hg _ (List.mem_map.mpr ⟨y, hy, rfl⟩))]
      exact hc
    obtain ⟨evs', h', hm⟩ := sweep_reach hE h hne hnl.2 hC (agree_of_live hA he)
    exact ⟨evs', .ite_false hc' h', hm⟩
  | _, _, _, .ite_nondet_true (tss := ts) (ess := es) (md := md) h, hne, hnl, D, L, added, σ',
      hC, hA => by
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨-, -, ht, -⟩ := ite_live (Fl := Fl) D L added .nondet ts es md
    rw [dropDeadDefsStmt_ite_arms]
    obtain ⟨evs', h', hm⟩ := sweep_reach hE h hne hnl.1 hC (agree_of_live hA ht)
    exact ⟨evs', .ite_nondet_true h', hm⟩
  | _, _, _, .ite_nondet_false (tss := ts) (ess := es) (md := md) h, hne, hnl, D, L, added, σ',
      hC, hA => by
    simp only [Stmt.noLoops_ite, Bool.and_eq_true] at hnl
    obtain ⟨-, -, -, he⟩ := ite_live (Fl := Fl) D L added .nondet ts es md
    rw [dropDeadDefsStmt_ite_arms]
    obtain ⟨evs', h', hm⟩ := sweep_reach hE h hne hnl.2 hC (agree_of_live hA he)
    exact ⟨evs', .ite_nondet_false h', hm⟩
  | _, _, _, .block (ss := ss) (l := l) (md := md) h, hne, hnl, D, L, added, σ', hC, hA => by
    rw [Stmt.noLoops_block] at hnl
    rw [dropDeadDefsStmt_block] at hA ⊢
    obtain ⟨evs', h', hm⟩ := sweep_reach hE h hne hnl hC hA
    exact ⟨evs', .block h', hm⟩
  | _, _, _, .loop_here _ _, _, hnl, _, _, _, _, _, _
  | _, _, _, .loop_later _ _ _, _, hnl, _, _, _, _, _, _ => by simp [Stmt.noLoops_loop] at hnl
end

end Core.Simplify
