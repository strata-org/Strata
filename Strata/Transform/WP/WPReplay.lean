/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPEvalIface

/-! # Replaying a big-step run from a wider store

A big-step run or reach of a statement list from a value-valued store `σ` is replayed from any
value-valued store `σ'` that agrees with `σ` on the identifiers of the list, for a factory
evaluating alike on value-valued stores agreeing on the free variables (`EvCongr`), from the
replay of a command step (`cmd_widen`, the evaluator interface): the replay
takes the same path, its events are observed alike (`Event.obs`), and its outcome agrees with
the original one on the variables the context still reads.  Unlike `Agree`, the agreement
constrains the stores only on the agreed variables: `σ'` may bind variables that `σ` leaves
unbound, so a failure from a restriction of a store is one from the store, at an event of the
same kind (`claimK_widen`, `fails_widen`).

Key theorems: `claimK_widen`, `fails_widen`, `claimK_obs`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [HasBool P] [HasFvar P] [HasFvars P]
variable {F : P.Factory}

/-- The outcomes have the same kind and label, and their stores are value-valued and agree
    on `N`. -/
private def OWide (F : P.Factory) (N : List P.Ident) : Outcome P → Outcome P → Prop
  | .normal σ, .normal σ' => Wide F N σ σ'
  | .exit l σ, .exit l' σ' => l = l' ∧ Wide F N σ σ'
  | _, _ => False

section
omit [HasFvar P] [HasFvars P]

/-- Leaving a scope keeps agreement. -/
private theorem Wide.proj {N : List P.Ident} {σp σp' σ σ' : SemanticStore P}
    (hp : Wide F N σp σp') (h : Wide F N σ σ') :
    Wide F N (projectStore σp σ) (projectStore σp' σ') :=
  ⟨fun y hy => by simp only [projectStore, hp.1 y hy, h.1 y hy],
    WellFormedStore.proj h.2.1, WellFormedStore.proj h.2.2⟩

/-- Leaving an `ite` branch keeps outcome agreement. -/
private theorem OWide.proj {N : List P.Ident} {σ σ' : SemanticStore P} {o o' : Outcome P}
    (hW : Wide F N σ σ') (h : OWide F N o o') : OWide F N (o.proj σ) (o'.proj σ') := by
  cases o <;> cases o' <;> simp_all [OWide, Outcome.proj, Wide.proj]

/-- Leaving a block keeps outcome agreement. -/
private theorem OWide.block {N : List P.Ident} {σ σ' : SemanticStore P} {o o' : Outcome P}
    (l : String) (hW : Wide F N σ σ') (h : OWide F N o o') :
    OWide F N (o.block l σ) (o'.block l σ') := by
  cases o <;> cases o' <;> grind [OWide, Outcome.block, Wide.proj hW]

end

omit [HasFvar P] in
/-- Value-valued stores agreeing on the variables of a loop guard let the loop enter its body
    alike and stop alike. -/
private theorem guard_wide (hE : EvCongr F) {g : ExprOrNondet P} {N : List P.Ident}
    {σ σ' : SemanticStore P} (hW : Wide F N σ σ') (hg : ∀ y ∈ g.getVars, y ∈ N) :
    (guardEnters F σ g → guardEnters F σ' g) ∧ (guardExits F σ g → guardExits F σ' g) := by
  cases g with
  | det g =>
    have he := hE hW.2.1 hW.2.2 g fun y hy => hW.1 y (hg y hy)
    exact ⟨he.trans, he.trans⟩
  | nondet => exact ⟨id, id⟩

mutual
/-- **A run, replayed** from a value-valued store agreeing with the value-valued `σ` on the
    identifiers of the list and on `live`: a run of the list, observed alike, whose outcome
    agrees with the original on `live`. -/
private theorem brun_wide [DecidableEq P.Ident] [LawfulHasVal P] (hE : EvCongr F) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRun F ss σ evs o → ∀ {live : List P.Ident} {σ' : SemanticStore P},
    Wide F (Block.idents ss ++ live) σ σ' →
    ∃ evs' o', BRun F ss σ' evs' o' ∧ evs'.map Event.obs = evs.map Event.obs ∧ OWide F live o o'
  | _, _, _, _, .nil, _, _, hW => ⟨[], _, .nil, rfl, by simpa [Block.idents, OWide] using hW⟩
  | _, _, _, _, .cons_normal (rest := rest) h1 h2, live, _, hW => by
    obtain ⟨evs1', o1', h1', hm1, hO1⟩ := brunS_wide hE (live := Block.idents rest ++ live) h1
      (by simpa [Block.idents] using hW)
    rcases o1' with σ1' | _ <;> simp only [OWide] at hO1
    obtain ⟨evs2', o', h2', hm2, hO⟩ := brun_wide hE h2 hO1
    exact ⟨evs1' ++ evs2', o', .cons_normal h1' h2', by simp [hm1, hm2], hO⟩
  | _, _, _, _, .cons_exit (rest := rest) h1, live, _, hW => by
    obtain ⟨evs1', o1', h1', hm1, hO1⟩ := brunS_wide hE (live := Block.idents rest ++ live) h1
      (by simpa [Block.idents] using hW)
    rcases o1' with _ | ⟨l', σ1'⟩ <;> simp only [OWide] at hO1
    obtain ⟨rfl, hW1⟩ := hO1
    exact ⟨evs1', _, .cons_exit h1', hm1, rfl, hW1.mono fun _ => List.mem_append_right _⟩
/-- **A statement run, replayed**: `brun_wide` for one statement. -/
private theorem brunS_wide [DecidableEq P.Ident] [LawfulHasVal P] (hE : EvCongr F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
    BRunS F s σ evs o → ∀ {live : List P.Ident} {σ' : SemanticStore P},
    Wide F (Stmt.idents s ++ live) σ σ' →
    ∃ evs' o', BRunS F s σ' evs' o' ∧ evs'.map Event.obs = evs.map Event.obs ∧ OWide F live o o'
  | _, _, _, _, .cmd (c := .cmd c) h, _, _, hW =>
    (cmd_widen hE h hW).elim fun _ ⟨evs', h', hm, hO⟩ => ⟨evs', _, .cmd h', hm, hO⟩
  | _, _, _, _, .cmd (c := .call _ _ _) h, _, _, _ => h.elim
  | _, σ, _, _, .ite_true hc h, live, σ', hW | _, σ, _, _, .ite_false hc h, live, σ', hW => by
    simp only [Stmt.idents, ExprOrNondet.getVars, List.append_assoc] at hW
    obtain ⟨evs', o', h', hm, hO⟩ := brun_wide hE (live := live) h (hW.mono fun y hy => by
      simp only [List.mem_append] at hy ⊢; grind)
    have hc' := (hE hW.2.1 hW.2.2 _ fun y hy => hW.1 y (List.mem_append_left _ hy)).trans hc
    have hP := hO.proj (hW.mono fun _ h => by simp [h])
    first
      | exact ⟨evs', _, .ite_true hc' h', hm, hP⟩
      | exact ⟨evs', _, .ite_false hc' h', hm, hP⟩
  | _, σ, _, _, .ite_nondet_true h, live, σ', hW | _, σ, _, _, .ite_nondet_false h, live, σ', hW
    => by
    simp only [Stmt.idents, ExprOrNondet.getVars, List.append_assoc, List.nil_append] at hW
    obtain ⟨evs', o', h', hm, hO⟩ := brun_wide hE (live := live) h (hW.mono fun y hy => by
      simp only [List.mem_append] at hy ⊢; grind)
    have hP := hO.proj (hW.mono fun _ h => by simp [h])
    first
      | exact ⟨evs', _, .ite_nondet_true h', hm, hP⟩
      | exact ⟨evs', _, .ite_nondet_false h', hm, hP⟩
  | _, σ, _, _, .block (l := l) h, _, σ', hW =>
    (brun_wide hE h hW).elim fun _ ⟨_, h', hm, hO⟩ =>
      ⟨_, _, .block h', hm, hO.block l (hW.mono fun _ => List.mem_append_right _)⟩
  | _, _, _, _, .exit, _, _, hW =>
    ⟨[], _, .exit, rfl, rfl, hW.mono fun _ => List.mem_append_right _⟩
  | _, _, _, _, .typeDecl, _, _, hW =>
    ⟨[], _, .typeDecl, rfl, hW.mono fun _ => List.mem_append_right _⟩
  | _, _, _, _, .loop_exit hg, _, _, hW =>
    ⟨[], _, .loop_exit ((guard_wide hE hW fun y hy => by simp [Stmt.idents, hy]).2 hg), rfl,
      hW.mono fun _ => List.mem_append_right _⟩
  | _, _, _, _, .loop_iter (g := g) (m := m) (inv := i) (body := b) (md := md) hg h1 h2, live, _,
      hW => by
    obtain ⟨evs1', o1', h1', hm1, hO1⟩ :=
      brun_wide hE (live := (Stmt.loop g m i b md).idents ++ live) h1 (hW.mono fun y hy => by
      simp only [Stmt.idents, List.mem_append] at hy ⊢; grind)
    rcases o1' with σ1' | _ <;> simp only [OWide] at hO1
    obtain ⟨evs2', o', h2', hm2, hO⟩ := brunS_wide hE h2 (Wide.proj hW hO1)
    exact ⟨evs1' ++ evs2', o', .loop_iter ((guard_wide hE hW fun y hy => by
      simp [Stmt.idents, hy]).1 hg) h1' h2', by simp [hm1, hm2], hO⟩
  | _, _, _, _, .loop_break hg h, live, _, hW => by
    obtain ⟨evs', o1', h', hm, hO1⟩ := brun_wide hE (live := live) h (hW.mono fun y hy => by
      simp only [Stmt.idents, List.mem_append] at hy ⊢; grind)
    rcases o1' with _ | ⟨l', σ1'⟩ <;> simp only [OWide] at hO1
    obtain ⟨rfl, hW1⟩ := hO1
    exact ⟨evs', _, .loop_break ((guard_wide hE hW fun y hy => by
      simp [Stmt.idents, hy]).1 hg) h', hm, rfl,
      Wide.proj (hW.mono fun _ => List.mem_append_right _) hW1⟩
end

mutual
/-- **A reach, replayed** from a value-valued store agreeing with the value-valued `σ` on the
    identifiers of the list: a reach of the list, observed alike. -/
private theorem breach_wide [DecidableEq P.Ident] [LawfulHasVal P] (hE : EvCongr F) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}, BReach F ss σ evs →
    ∀ {σ' : SemanticStore P}, Wide F (Block.idents ss) σ σ' → ∃ evs', BReach F ss σ' evs' ∧
      evs'.map Event.obs = evs.map Event.obs
  | _, _, _, .here h, _, hW =>
    (breachS_wide hE h (hW.mono fun _ => List.mem_append_left _)).imp fun _ h => ⟨.here h.1, h.2⟩
  | _, _, _, .later (rest := rest) h1 h2, _, hW => by
    obtain ⟨evs1', o1', h1', hm1, hO1⟩ := brunS_wide hE (live := Block.idents rest) h1
      (by simpa [Block.idents] using hW)
    rcases o1' with σ1' | _ <;> simp only [OWide] at hO1
    obtain ⟨evs2', h2', hm2⟩ := breach_wide hE h2 hO1
    exact ⟨evs1' ++ evs2', .later h1' h2', by simp [hm1, hm2]⟩
/-- **A statement reach, replayed**: `breach_wide` for one statement. -/
private theorem breachS_wide [DecidableEq P.Ident] [LawfulHasVal P] (hE : EvCongr F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}, BReachS F s σ evs →
    ∀ {σ' : SemanticStore P}, Wide F (Stmt.idents s) σ σ' → ∃ evs', BReachS F s σ' evs' ∧
      evs'.map Event.obs = evs.map Event.obs
  | _, _, _, .cmd (c := .cmd c) h hne, _, hW => by
    obtain ⟨_, evs', h', hm, -⟩ := cmd_widen hE (N := []) h (by simpa using hW)
    exact ⟨evs', .cmd h' fun h0 => hne (by simpa [h0] using hm), hm⟩
  | _, _, _, .cmd (c := .call _ _ _) h _, _, _ => h.elim
  | _, _, _, .ite_true hc h, _, hW | _, _, _, .ite_false hc h, _, hW => by
    simp only [Stmt.idents, ExprOrNondet.getVars, List.append_assoc] at hW
    obtain ⟨evs', h', hm⟩ := breach_wide hE h (hW.mono fun y hy => by simp [hy])
    have hc' := (hE hW.2.1 hW.2.2 _ fun y hy => hW.1 y (List.mem_append_left _ hy)).trans hc
    first
      | exact ⟨evs', .ite_true hc' h', hm⟩
      | exact ⟨evs', .ite_false hc' h', hm⟩
  | _, _, _, .ite_nondet_true h, _, hW | _, _, _, .ite_nondet_false h, _, hW => by
    simp only [Stmt.idents, ExprOrNondet.getVars, List.nil_append] at hW
    obtain ⟨evs', h', hm⟩ := breach_wide hE h (hW.mono fun y hy => by simp [hy])
    first
      | exact ⟨evs', .ite_nondet_true h', hm⟩
      | exact ⟨evs', .ite_nondet_false h', hm⟩
  | _, _, _, .block h, _, hW => (breach_wide hE h hW).imp fun _ h => ⟨.block h.1, h.2⟩
  | _, _, _, .loop_here hg h, _, hW =>
    (breach_wide hE h (hW.mono fun y hy => by simp [Stmt.idents, hy])).imp fun _ h =>
      ⟨.loop_here ((guard_wide hE hW fun y hy => by simp [Stmt.idents, hy]).1 hg) h.1, h.2⟩
  | _, _, _, .loop_later (g := g) (m := m) (inv := i) (body := b) (md := md) hg h1 h2, _, hW => by
    obtain ⟨evs1', o1', h1', hm1, hO1⟩ :=
      brun_wide hE (live := (Stmt.loop g m i b md).idents) h1 (hW.mono fun y hy => by
      simp only [Stmt.idents, List.mem_append] at hy ⊢; grind)
    rcases o1' with σ1' | _ <;> simp only [OWide] at hO1
    obtain ⟨evs2', h2', hm2⟩ := breachS_wide hE h2 (Wide.proj hW hO1)
    exact ⟨evs1' ++ evs2', .loop_later ((guard_wide hE hW fun y hy => by
      simp [Stmt.idents, hy]).1 hg) h1' h2', by simp [hm1, hm2]⟩
end

omit [HasFvar P] [HasFvars P] in
/-- A trace observed like (`Event.obs`) a trace that fails `t` on a feasible path at an event of
    kind `k` with the condition `c` fails it on a feasible path at an event of kind `k` with the
    condition `c`. -/
theorem claimK_obs {tr tr' : List (Event P)} (hm : tr'.map Event.obs = tr.map Event.obs)
    {t : AssertId P} {c : P.Expr} {k : Bool} (h : ClaimK k t c tr) : ClaimK k t c tr' := by
  obtain ⟨evs, a, rfl, hfeas, hfe, hc⟩ := h
  obtain ⟨evs', b, rfl, ha, hb⟩ := List.map_eq_append_iff.1 (hm.trans (List.map_append ..))
  obtain ⟨e', rfl, he⟩ := List.map_eq_singleton_iff.1 hb
  obtain ⟨a', rfl⟩ : ∃ a', e' = if k then .cover a' else .assert a' := by
    cases k <;> cases e' <;> simp_all [Event.obs]
  refine ⟨evs', a', rfl, feasible_obs ha hfeas, failsAt_obs he hfe, ?_⟩
  cases k <;> simp only [Event.obs, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at he <;>
    exact he.2.2.1.trans hc

/-- **A failure, replayed from a wider store, keeps its kind.**  A statement list with a reach from
    the value-valued store `σ` whose trace fails the target `t` on a feasible path at an event of
    kind `k` with the condition `c` (`ClaimK`) has such a reach from every value-valued store `σ'`
    that agrees with `σ` on the identifiers of the list, for a factory evaluating alike on
    value-valued stores agreeing on the free variables (`EvCongr`); `σ'` may bind variables that
    `σ` leaves unbound. -/
theorem claimK_widen [DecidableEq P.Ident] [LawfulHasVal P] (hE : EvCongr F)
    {ss : PStmts P} {σ σ' : SemanticStore P}
    (hC : WellFormedStore σ F) (hC' : WellFormedStore σ' F)
    (hA : ∀ y ∈ Block.idents ss, σ' y = σ y) {tr : List (Event P)} (hb : BReach F ss σ tr)
    {t : AssertId P} {c : P.Expr} {k : Bool} (hc : ClaimK k t c tr) :
    ∃ tr', BReach F ss σ' tr' ∧ ClaimK k t c tr' :=
  (breach_wide hE hb ⟨hA, hC, hC'⟩).imp fun _ h => ⟨h.1, claimK_obs h.2 hc⟩

/-- **A failure, replayed from a wider store.**  A statement list that fails the target `t` with
    the condition `e` from the value-valued store `σ` (`Fails`) fails it from every value-valued
    store `σ'` that agrees with `σ` on the identifiers of the list, for a factory evaluating alike
    on value-valued stores agreeing on the free variables (`EvCongr`); `σ'` may bind variables
    that `σ` leaves unbound. -/
theorem fails_widen [DecidableEq P.Ident] [LawfulHasVal P] (hE : EvCongr F)
    {ss : PStmts P} {σ σ' : SemanticStore P}
    (hC : WellFormedStore σ F) (hC' : WellFormedStore σ' F)
    (hA : ∀ y ∈ Block.idents ss, σ' y = σ y) {t : AssertId P} {e : P.Expr}
    (h : Fails F ss σ t e) : Fails F ss σ' t e := by
  obtain ⟨evs, ev, hb, hfeas, hfe⟩ := h
  obtain ⟨_, hk⟩ := Claim.kind ⟨evs, ev, rfl, hfeas, hfe⟩
  obtain ⟨_, hb', evs', _, rfl, hf, hfe', -⟩ := claimK_widen hE hC hC' hA hb hk
  exact ⟨evs', _, hb', hf, hfe'⟩

end -- public section

end WP
end Imperative
