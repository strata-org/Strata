/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverWalk
public import Strata.Transform.Passive.Shadow
import Strata.Transform.WP.WPOverEmit
import Strata.Util.RopeProps
import Strata.Util.LeftistHeapProps
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.Replace

/-! # Facts about WP walk results

Facts relating the result of a WP walk (`wpList`, `wpStmt`, `wpIteLaid`, `wpIteReal`) to the
walk state and to the loop-free runs of the walked fragment:

* only a main-list `exit` drops the rest of its list (`wpStmt_drop`, `wpList_drop`);
* a reachable failing obligation makes the result carry an obligation (`wpList_hit_hasObl`,
  `noObl_claim`);
* a statement walked with an obligation following it does not always exit when it has a normal
  run (`wpStmt_ax_normal`);
* the registrations of a result (exit snapshots, carried copies) are fresh names drawn by its
  walk (`wpStmt_regs`, `wpList_regs`), not dead after it (`wpList_regs_live`) and registered for
  at most one label (`wpList_regs_one_label`); the snapshots of a block's label not dead after
  the walk of its body are registrations of the body (`body_snaps_regs`); snapshots and dead
  names only grow by drawn names (`wpList_pending_new`, `pending_regs`, `wpStmt_dead`);
* carried merges are only put in front, with registered or dead copies, at the depths of
  enclosing blocks (`wpStmt_carries`, `body_carries`), and target names that are no
  registrations or context variables (`body_carries_names`).

A successful walk of a laid-out `ite` has the steps of `LaidSteps` (`wpIteLaid_inv`), stated as
an elimination principle so that each proof about such a walk starts from its steps.

The facts about runs and dead names need the names marked dead to have counters below the
state's counter (`DeadBelow`, defined with the walk facts), which every walk keeps
(`wpList_deadBelow`) and a state without dead names has (`deadBelow_of_dead_empty`).

Key theorems: `wpStmt_drop`, `wpList_drop`, `wpList_hit_hasObl`, `noObl_claim`,
`wpStmt_ax_normal`, `wpList_regs`, `wpList_regs_live`, `body_snaps_regs`, `wpList_regs_one_label`,
`pending_regs`, `wpList_deadBelow`, `wpStmt_carries`, `body_carries`, `body_carries_names`,
`wpIteLaid_inv`.

Key definitions: `NewIn`, `wsimple`, `wvars`, `LaidSteps`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iHS : HasSubstFvar P] [iHI : HasIdent P]
  [iL : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHV : HasFvars P] [iW : WPOps P]
variable {κ : RE P} {d : Nat} {fEnd f : Bool} {s : PStmt P} {ss : PStmts P} {st st' : WSt P}
  {r a : WRes P}


/-! ## State changes of walks -/

/-- `n` is a fresh name drawn between the states `s` and `s'`: not avoided, with a counter from
    `s.next` on and below `s'.next`. -/
@[expose] def NewIn (s s' : WSt P) (n : P.Ident) : Prop :=
  ∃ b j, n = freshName b j ∧ s.avoid.contains n = false ∧ s.next ≤ j ∧ j < s'.next

/-- How a walk changes the parts of the state the facts of this file follow: the avoided names
    and the label depths are kept, the counter does not decrease, the exit snapshots registered
    stay registered and new ones are drawn by the walk, and the names newly marked dead are
    drawn by the walk. -/
private structure Ext (st st' : WSt P) : Prop where
  avoid : st'.avoid = st.avoid
  next : st.next ≤ st'.next
  ld : ∀ l : String, st'.labelDepth[l]? = st.labelDepth[l]?
  pend : ∀ (l : String) (e : P.Ident), e ∈ st.pending.getD l [] → e ∈ st'.pending.getD l []
  pendNew : ∀ (l : String) (e : P.Ident), e ∈ st'.pending.getD l [] →
    e ∈ st.pending.getD l [] ∨ NewIn st st' e
  dead : ∀ e : P.Ident, st'.dead.contains e = true → st.dead.contains e = true ∨ NewIn st st' e
  deadMono : ∀ e : P.Ident, st.dead.contains e = true → st'.dead.contains e = true

section
omit iL iW

/-- A name drawn between two states is drawn between any wider pair of states. -/
theorem NewIn.widen {s0 s1 s2 s3 : WSt P} {n : P.Ident} (h : NewIn s1 s2 n)
    (ha : s1.avoid = s0.avoid) (h0 : s0.next ≤ s1.next) (h3 : s2.next ≤ s3.next) :
    NewIn s0 s3 n := by grind [NewIn]

include iL in
/-- A name drawn from the state `s` on is not a name of fresh-name form with a counter below
    `s.next`. -/
private theorem NewIn.ne {s s' : WSt P} {n : P.Ident} (h : NewIn s s' n) {b : String} {j : Nat}
    (hj : j < s.next) : n ≠ freshName b j := by grind [NewIn, freshName_counter_inj]

include iL in
/-- Names drawn in disjoint counter ranges differ. -/
private theorem NewIn.disj {s0 s1 s2 : WSt P} {n m : P.Ident} (hn : NewIn s0 s1 n)
    (hm : NewIn s1 s2 m) : n ≠ m := by grind [NewIn, freshName_counter_inj]

/-- No change is an `Ext` step. -/
private theorem Ext.refl (st : WSt P) : Ext st st :=
  ⟨rfl, Nat.le_refl _, fun _ => rfl, fun _ _ h => h, fun _ _ => .inl, fun _ => .inl, fun _ h => h⟩

/-- `Ext` steps compose. -/
private theorem Ext.trans {s0 s1 s2 : WSt P} (h1 : Ext s0 s1) (h2 : Ext s1 s2) : Ext s0 s2 := by
  grind [Ext, NewIn]

/-- A state change keeping the avoided names, the label depths, the exit snapshots and the dead
    names, with a counter that does not decrease, is an `Ext` step. -/
private theorem Ext.of_eq (h1 : st'.avoid = st.avoid) (h2 : st.next ≤ st'.next)
    (h3 : st'.labelDepth = st.labelDepth) (h4 : st'.pending = st.pending)
    (h5 : st'.dead = st.dead) : Ext st st' := by constructor <;> simp_all

include iL in
/-- An `Ext` step keeps `DeadBelow`. -/
private theorem Ext.deadBelow (h : Ext st st') (hd : DeadBelow st) :
    DeadBelow st' := by grind [DeadBelow, NewIn, freshName_counter_inj, h.dead, h.next]

/-! ## Runs of the state primitives -/

/-- From `st` to `st'`, each block depth's carried merges gain merges in front only, satisfying
    `CP` at that depth. -/
private def CarPre (CP : Nat → P.Ident × WExpr P × P.Ident → Prop) (st st' : WSt P) : Prop :=
  ∀ k, ∃ pre, st'.carries.getD k [] = pre ++ st.carries.getD k [] ∧ ∀ q ∈ pre, CP k q

/-- No change is a `CarPre` step. -/
private theorem CarPre.of_eq {CP : Nat → P.Ident × WExpr P × P.Ident → Prop}
    (h : st'.carries = st.carries) : CarPre CP st st' := fun _ => ⟨[], by simp [h], nofun⟩

/-- A `CarPre` step allowing no copy keeps the carried merges. -/
private theorem CarPre.noCP (h : CarPre (fun _ _ => False) st st') (k : Nat) :
    st'.carries.getD k [] = st.carries.getD k [] :=
  (h k).elim fun _ ⟨h1, h2⟩ => (List.eq_nil_iff_forall_not_mem.2 h2 ▸ h1 :)

/-- `CarPre` steps compose. -/
private theorem CarPre.trans {CP : Nat → P.Ident × WExpr P × P.Ident → Prop} {s0 s1 s2 : WSt P}
    (h1 : CarPre CP s0 s1) (h2 : CarPre CP s1 s2) : CarPre CP s0 s2 :=
  fun k => (h2 k).elim fun p2 ⟨e2, q2⟩ => (h1 k).elim fun p1 ⟨e1, q1⟩ => ⟨p2 ++ p1, by grind⟩

/-- From `st` to `st'`, the back map changes only at fresh names drawn from `st` on. -/
private def BackNew (st st' : WSt P) : Prop := ∀ n, st'.back[n]? ≠ st.back[n]? → FreshAt st n

/-- `BackNew` steps compose along steps keeping the avoided names and not decreasing the
    counter. -/
private theorem BackNew.trans {s0 s1 s2 : WSt P} (h1 : BackNew s0 s1) (h2 : BackNew s1 s2)
    (ha : s1.avoid = s0.avoid) (hn : s0.next ≤ s1.next) : BackNew s0 s2 := by
  grind [BackNew, FreshAt]

/-- A change keeping the back map is a `BackNew` step. -/
private theorem BackNew.of_eq (h : st'.back = st.back) : BackNew st st' :=
  fun _ hn => (hn (by rw [h])).elim

end

omit iW in
/-- A name with a counter below `s.next` keeps its back-map entry along a `BackNew` step. -/
private theorem BackNew.keep {s s' : WSt P} (hb : BackNew s s') {n : P.Ident}
    (hn : ∃ b j, n = freshName b j ∧ j < s.next) : s'.back[n]? = s.back[n]? :=
  by grind [BackNew, FreshAt, freshName_counter_inj]

/-- Every successful run of `m` is an `Ext` step keeping the dead names and the snapshots,
    putting carried merges with copies satisfying `CP` in front only, changing the back map only
    at drawn names, and returning a value with the property `Q`. -/
private structure Good {α : Type} (CP : Nat → P.Ident × WExpr P × P.Ident → Prop) (m : WM P α)
    (Q : α → Prop) : Prop where
  run : ∀ st a st', m.run st = .ok (a, st') →
    Ext st st' ∧ (st'.dead = st.dead ∧ st'.pending = st.pending) ∧ CarPre CP st st' ∧
      BackNew st st' ∧ Q a

section
variable {CP : Nat → P.Ident × WExpr P × P.Ident → Prop}

section
omit iL iW

/-- `pure a` is a `Good` step when `a` has the property. -/
private theorem good_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    Good CP (pure a : WM P α) Q := ⟨fun _ _ _ hr => by
  cases hr
  exact ⟨.refl _, ⟨rfl, rfl⟩, .of_eq rfl, .of_eq rfl, h⟩⟩

/-- A bind of `Good` steps is a `Good` step with the property of its continuation. -/
private theorem good_bind {α β : Type} {x : WM P α} {f : α → WM P β} {Q : β → Prop}
    (hx : Good CP x fun _ => True) (hf : ∀ a, Good CP (f a) Q) : Good CP (x >>= f) Q :=
  ⟨fun _ _ _ h => by
    obtain ⟨a, s1, h1, h2⟩ := wm_run_bind_ok h
    obtain ⟨e1, ⟨d1, p1⟩, c1, b1, -⟩ := hx.run _ _ _ h1
    obtain ⟨e2, ⟨d2, p2⟩, c2, b2, q⟩ := (hf a).run _ _ _ h2
    exact ⟨e1.trans e2, ⟨d2.trans d1, p2.trans p1⟩, c1.trans c2, b1.trans b2 e1.avoid e1.next, q⟩⟩

/-- A successful run of a `Good` step has its facts. -/
private theorem good_use {α : Type} {m : WM P α} {Q : α → Prop} {s s' : WSt P} {a : α}
    (h : m.run s = .ok (a, s')) (hg : Good CP m Q) :
    Ext s s' ∧ (s'.dead = s.dead ∧ s'.pending = s.pending) ∧ CarPre CP s s' ∧ BackNew s s' ∧
      Q a := hg.run _ _ _ h

/-- `throw` is a `Good` step (it has no successful run). -/
private theorem good_throw {α : Type} {Q : α → Prop} (e : String) :
    Good CP (throw e : WM P α) Q := ⟨fun _ _ _ h => nomatch h⟩

/-- A run changing only the parts of the state `Ext` does not follow is a `Good` step. -/
private theorem good_of_eq {α : Type} {m : WM P α}
    (h : ∀ st a st', m.run st = .ok (a, st') → st'.avoid = st.avoid ∧ st.next ≤ st'.next ∧
      st'.labelDepth = st.labelDepth ∧ st'.pending = st.pending ∧ st'.dead = st.dead ∧
      st'.carries = st.carries ∧ BackNew st st') : Good CP m fun _ => True := ⟨fun st a st' hr =>
  let ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h st a st' hr
  ⟨.of_eq h1 h2 h3 h4 h5, ⟨h5, h4⟩, .of_eq h6, h7, trivial⟩⟩

/-- A `modify` keeping the parts `Ext` follows is a `Good` step. -/
private theorem good_modify (g : WSt P → WSt P)
    (h : ∀ st, (g st).avoid = st.avoid ∧ st.next ≤ (g st).next ∧
      (g st).labelDepth = st.labelDepth ∧ (g st).pending = st.pending ∧ (g st).dead = st.dead ∧
      (g st).carries = st.carries ∧ (g st).back = st.back := by
        exact fun _ => ⟨rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩) :
    Good CP (modify g : WM P Unit) fun _ => True :=
  good_of_eq fun st _ _ hr => (Prod.mk.inj (Except.ok.inj hr)).2 ▸ by simp [h st, BackNew]

/-- `liveAdd` is a `Good` step. -/
private theorem good_liveAdd (xs : List P.Ident) : Good CP (liveAdd xs : WM P Unit) fun _ => True :=
  good_modify _

/-- `liveDel` is a `Good` step. -/
private theorem good_liveDel (x : P.Ident) : Good CP (liveDel x : WM P Unit) fun _ => True :=
  good_modify _

end

omit iW in
/-- `wFresh` is a `Good` step. -/
private theorem good_wFresh (b : String) : Good CP (wFresh b : WM P P.Ident) fun _ => True :=
  good_of_eq fun st _ _ hr => (Prod.mk.inj (Except.ok.inj hr)).2 ▸ ⟨rfl,
    (freshIn_spec st.avoid b st.next).elim fun _ ⟨hk, h2, _⟩ =>
      Nat.le_trans (Nat.le_add_right_of_le h2) (Nat.le_of_eq (congrArg Prod.snd hk).symm),
    rfl, rfl, rfl, rfl, BackNew.of_eq rfl⟩

omit iW in
/-- `wFreshBool` is a `Good` step. -/
private theorem good_wFreshBool (b : String) :
    Good CP (wFreshBool b : WM P P.Ident) fun _ => True :=
  good_bind (good_wFresh b) fun _ => good_bind (good_modify _) fun _ => good_pure trivial

/-- `wFreshLike` is a `Good` step. -/
private theorem good_wFreshLike (x : P.Ident) :
    Good CP (wFreshLike x : WM P P.Ident) fun _ => True :=
  good_bind (good_wFresh _) fun _ => good_bind (good_modify _) fun _ => good_pure trivial

/-- `wName` is a `Good` step. -/
private theorem good_wName (x : P.Ident) : Good CP (wName x : WM P P.Ident) fun _ => True :=
  good_of_eq fun st _ _ hr => by
    rcases wName_cases hr with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl, rfl⟩ <;>
      try exact ⟨rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, BackNew.of_eq rfl⟩
    obtain ⟨k, hk, h1, h2⟩ := freshIn_spec st.avoid (baseOf x) st.next
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, fun m hm => ?_⟩ <;> grind [FreshAt]

/-- `wDecl` is a `Good` step. -/
private theorem good_wDecl (x : P.Ident) : Good CP (wDecl x : WM P P.Ident) fun _ => True :=
  good_bind (good_wName x) fun _ => good_bind (good_modify _) fun _ => good_pure trivial

/-- `wRen` is a `Good` step. -/
private theorem good_wRen (e : P.Expr) : Good CP (wRen e : WM P (WExpr P × List P.Ident))
    fun _ => True := good_of_eq fun st _ st' hr => by
  obtain ⟨-, hn, he, -⟩ := wRen_run hr
  exact ⟨by rw [he], hn, by rw [he], by rw [he], by rw [he], by rw [he], (wRen_walk hr).back⟩

/-- A join step from `s` to `s'`: an `Ext` step keeping the dead names, the snapshots, the
    carried merges and the back map, the names satisfying `S` being drawn by the step. -/
private structure JStep (s : WSt P) (S : P.Ident → Prop) (s' : WSt P) : Prop where
  ext : Ext s s'
  dead : s'.dead = s.dead
  pend : s'.pending = s.pending
  car : s'.carries = s.carries
  back : s'.back = s.back
  sel : ∀ y, S y → ∃ b j, y = freshName b j ∧ s.next ≤ j ∧ j < s'.next ∧ s.avoid.contains y = false

omit iL iW in
/-- Join steps compose. -/
private theorem JStep.trans {s0 s1 s2 : WSt P} {S1 S2 : P.Ident → Prop} (h1 : JStep s0 S1 s1)
    (h2 : JStep s1 S2 s2) : JStep s0 (fun y => S1 y ∨ S2 y) s2 :=
  ⟨h1.ext.trans h2.ext, h2.dead.trans h1.dead, h2.pend.trans h1.pend, h2.car.trans h1.car,
    h2.back.trans h1.back, fun y hy => hy.elim (fun h => by grind [h1.sel y h, h2.ext.next])
      fun h => by grind [h2.sel y h, h1.ext.next, h1.ext.avoid]⟩

omit iL iW in
/-- No step is a join step drawing nothing. -/
private theorem JStep.refl (s : WSt P) : JStep s (fun y => (none : Option P.Ident) = some y) s :=
  ⟨Ext.refl _, rfl, rfl, rfl, rfl, nofun⟩

omit iL iW in
/-- A join step drawing the names satisfying `S` draws the names satisfying a stronger `S'`. -/
private theorem JStep.mono {s s' : WSt P} {S S' : P.Ident → Prop} (h : JStep s S s')
    (hS : ∀ y, S' y → S y) : JStep s S' s' := { h with sel := fun y hy => h.sel y (hS y hy) }

omit iW in
/-- A run of `wFreshBool` is a join step drawing its name. -/
private theorem wfb_step {b : String} {x : P.Ident} {s s' : WSt P}
    (hx : (wFreshBool b).run s = .ok (x, s')) : JStep s (fun y => some x = some y) s' := by
  cases (wFreshBool_run b s).symm.trans hx
  obtain ⟨k, hk, h1, h2⟩ := freshIn_spec s.avoid b s.next
  exact ⟨Ext.of_eq rfl (by grind) rfl rfl rfl, rfl, rfl, rfl, rfl, fun y hy => ⟨b, k, by grind⟩⟩

/-- A run of `wFreshLike` is a join step drawing its name. -/
private theorem wFreshLike_new {y n : P.Ident} {s s' : WSt P}
    (h : (wFreshLike y).run s = .ok (n, s')) : JStep s (fun x => n = x) s' := by
  cases (wFreshLike_run y s).symm.trans h
  obtain ⟨k, hk, h1, h2⟩ := freshIn_spec s.avoid (baseOf y) s.next
  exact ⟨Ext.of_eq rfl (by grind) rfl rfl rfl, rfl, rfl, rfl, rfl,
    fun _ _ => ⟨baseOf y, k, by grind⟩⟩

/-- A run of `saveRestore xs` is a join step drawing the copy names of its copy pairs, which pair
    variables of `xs` with them. -/
private theorem saveRestore_new {xs : List P.Ident} {s s' : WSt P} {sv cp rs : Rope (WItem P)}
    {cps : List (P.Ident × P.Ident)} (h : (saveRestore xs).run s = .ok ((sv, cp, rs, cps), s')) :
    JStep s (fun y => ∃ p ∈ cps, p.2 = y) s' ∧ ∀ p ∈ cps, p.1 ∈ xs := by
  unfold saveRestore at h
  obtain ⟨⟨_, _, _, cps⟩, s1, hl, h⟩ := wm_run_bind_ok h
  cases h
  have hI := wm_forIn_inv (fun S b st => JStep s (fun y => ∃ p ∈ b.2.2.2, p.2 = y) st ∧
      ∀ p ∈ b.2.2.2, p.1 ∈ S) _ ?_ xs [] _ s _ _ ⟨(JStep.refl s).mono (by simp), nofun⟩ hl
  · simpa using hI
  intro S y b st b' st' hb hy
  obtain ⟨n1, s2, h1, hy⟩ := wm_run_bind_ok hy
  obtain ⟨n2, s3, h2, hy⟩ := wm_run_bind_ok hy
  cases hy
  refine ⟨_, rfl, ((hb.1.trans (wFreshLike_new h1)).trans (wFreshLike_new h2)).mono ?_, ?_⟩
  all_goals grind

/-- `saveRestore` is a `Good` step. -/
private theorem good_saveRestore (xs : List P.Ident) : Good CP (saveRestore xs : WM P _)
    fun _ => True := ⟨fun _ _ _ h =>
  let ⟨J, _⟩ := saveRestore_new h
  ⟨J.ext, ⟨J.dead, J.pend⟩, .of_eq J.car, .of_eq J.back, trivial⟩⟩
end

/-- Closes the result goal of a `pure` step of a `Good` decomposition. -/
syntax "gclose" : tactic

macro_rules | `(tactic| gclose) => `(tactic| trivial)

/-- The result facts of the walk of a command `s`: no registrations, no drop, not always
    exiting, an obligation only with a nonempty output, no exit target, and an assigned name only
    when `s` is a `set`. -/
private def CmdQ (s : PStmt P) (a : WRes P) : Prop :=
  a.regs = .nil ∧ a.drop = false ∧ a.ax = false ∧ (a.hasObl = false ∨ a.out.isNil = false) ∧
    a.tgt = .empty ∧ ∀ n, a.A.contains n = true → ∃ x e md, s = .cmd (.cmd (.set x e md))

macro_rules
  | `(tactic| gclose) =>
    `(tactic| (show CmdQ _ _; exact ⟨rfl, rfl, rfl,
      by (first | exact .inl rfl | exact .inr rfl), rfl,
      fun _ h => by first | exact ⟨_, _, _, rfl⟩ | simp at h⟩))

/-- One step of the `Good` decomposition of a command walk. -/
local macro "gstep" : tactic => `(tactic| first
  | (with_reducible apply good_bind)
  | prim good
  | (with_reducible apply good_modify
     intro _
     exact ⟨rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl⟩)
  | (with_reducible refine good_pure ?_
     gclose)
  | intro _
  | split
  | dsimp only)

/-- The walk of a command or a statement without a WP rule is a `Good` step with the result
    facts `CmdQ`. -/
private theorem wpStmt_cmd_good (κ : RE P) (d : Nat) (f : Bool) :
    ∀ s : PStmt P, (∀ {l md}, s = .exit l md → False) →
      (∀ {l b md}, s = .block l b md → False) → (∀ {c t e md}, s = .ite (.det c) t e md → False) →
      Good (fun _ _ => False) (wpStmt κ d f s) (CmdQ s)
  | s, h1, h2, h3 => by
    unfold wpStmt
    split
    all_goals first | exact (h1 rfl).elim | exact (h2 rfl).elim | exact (h3 rfl).elim | skip
    all_goals repeat' gstep

/-- The walk of an `exit` is an `Ext` step keeping the dead names, the carried merges and the
    back map, assigning nothing, whose registrations are drawn by it; it has no obligation, drops
    only under `top`, and otherwise always exits; the snapshots it registers are registrations,
    registered for its label, and under a variable context with an obligation following and an
    enclosing target block it registers one; its exit targets are an ordered heap of depths of
    labels of its input state, holding the depth of its label under a variable context. -/
private theorem wpStmt_exit_run {l : String} {md : MetaData P}
    (h : (wpStmt κ d f (.exit l md)).run st = .ok (a, st')) :
    Ext st st' ∧ (∀ e ∈ a.regs.toList, NewIn st st' e) ∧ a.hasObl = false ∧
      (a.drop = true → κ = .top) ∧ (κ ≠ .top → a.ax = true ∧ a.drop = false) ∧
      (κ ≠ .top → f = true → (∃ t, st.labelDepth[l]? = some t) →
        ∃ e ∈ a.regs.toList, NewIn st st' e ∧ e ∈ st'.pending.getD l []) ∧
      st'.dead = st.dead ∧ (∀ l' x, x ∈ st'.pending.getD l' [] → x ∉ st.pending.getD l' [] →
        l' = l ∧ x ∈ a.regs.toList) ∧
      st'.carries = st.carries ∧ st'.back = st.back ∧ (∀ n, a.A.contains n = false) ∧
      a.tgt.Ord ∧ (∀ t ∈ a.tgt.elems, ∃ l' : String, st.labelDepth[l']? = some t) ∧
      (κ ≠ .top → ∀ t, st.labelDepth[l]? = some t → t ∈ a.tgt.elems) := by
  unfold wpStmt at h
  split at h
  all_goals run_peel h
  (repeat' split at h)
  all_goals try
    cases h
    refine ⟨Ext.of_eq rfl (Nat.le_refl _) rfl rfl rfl, ?_⟩
    grind [Rope.toList_nil, LeftistHeap.Ord, LeftistHeap.elems, LeftistHeap.single]
  obtain ⟨e, s2, he, h⟩ := wm_run_bind_ok h
  cases (wFreshBool_run _ _).symm.trans he
  run_peel h
  obtain ⟨_, s3, hl, h⟩ := wm_run_bind_ok h
  obtain ⟨live, clock, rfl, -⟩ := liveAdd_step hl
  cases h
  obtain ⟨k, hk, h1, h2⟩ := freshIn_spec st.avoid "r" st.next
  refine ⟨⟨rfl, ?_, fun _ => rfl, ?_, ?_, fun _ hx => .inl hx, fun _ hx => hx⟩, ?_, ?_, ?_, ?_,
    fun _ _ _ => ⟨(freshIn st.avoid "r" st.next).1, ?_, ⟨"r", k, ?_⟩, ?_⟩, ?_⟩
  and_intros
  all_goals grind [Rope.toList_one, LeftistHeap.Ord, LeftistHeap.elems, LeftistHeap.single, NewIn]

/-- A one-element rope is not empty. -/
theorem Rope.isNil_one_eq {α : Type} (a : α) : (Rope.one a).isNil = false := rfl

omit iL iW in
/-- The walk state a block's body is walked from is well formed when the block's is. -/
theorem wfSt_blk (hwf : WFSt st) (l : String) (d c : Nat) :
    WFSt { st with
      labelDepth := st.labelDepth.insert l (d + 1)
      pending := st.pending.insert l []
      stampAt := st.stampAt.insert (d + 1) c
      carries := st.carries.insert (d + 1) [] } :=
  { hwf with
    pending_fresh := fun l' e he => hwf.pending_fresh l' e (by grind)
    carries_fresh := fun k i n v xB h => hwf.carries_fresh k i n v xB (by grind)
    carries_sel := fun k i n v xB h => hwf.carries_sel k i n v xB (by grind) }

omit iDE iHB iHF iHS iHI iL iHV iW in
/-- A name is in a hash set after inserting the first components of a list exactly when it was
    before or is the first component of an element. -/
theorem foldl_insert_fst {L : List (P.Ident × WExpr P × P.Ident)}
    {g : Std.HashSet P.Ident → P.Ident × WExpr P × P.Ident → Std.HashSet P.Ident}
    (hg : ∀ s e, g s e = s.insert e.1) {A : Std.HashSet P.Ident} {x : P.Ident}
    (h : (L.foldl g A).contains x = true) : A.contains x = true ∨ ∃ e ∈ L, e.1 = x :=
  by induction L generalizing A <;> grind

omit iL iW in
/-- The snapshots of a label after restoring it from the state `st`. -/
private theorem pending_restore {st1 : WSt P} {l l' : String} :
    (match st.pending[l]? with
      | some v => st1.pending.insert l v
      | none => st1.pending.erase l).getD l' [] =
    if l = l' then st.pending.getD l' [] else st1.pending.getD l' [] :=
  by split <;> grind [Std.HashMap.getD_eq_getD_getElem?]

omit iL iW in
/-- The label depths after restoring a label from the state `st`. -/
private theorem labelDepth_restore {st1 : WSt P} {l l' : String} :
    (match st.labelDepth[l]? with
      | some v => st1.labelDepth.insert l v
      | none => st1.labelDepth.erase l)[l']? =
    if l = l' then st.labelDepth[l']? else st1.labelDepth[l']? := by split <;> grind

/-- The walk of a block: from the state with the label's depth and an empty snapshot list for it
    (and a fresh top-level reach `rL` under `top`), the body is walked under a variable context;
    the label's depth and snapshots are restored at the end, and the result has the body's
    obligation bit and registrations and always exits when the body does and no snapshot for the
    label survives. -/
private theorem wpStmt_block_run {l : String} {body : PStmts P} {md : MetaData P}
    (h : (wpStmt κ d f (.block l body md)).run st = .ok (a, st')) :
    ∃ κB s0 B st1, (wpList κB (d + 1) f body).run s0 = .ok (B, st1) ∧ κB ≠ .top ∧
      (κ ≠ .top → κB = κ) ∧ s0.avoid = st.avoid ∧ st.next ≤ s0.next ∧
      (∀ l', s0.labelDepth[l']? = if l = l' then some (d + 1) else st.labelDepth[l']?) ∧
      (∀ l', s0.pending.getD l' [] = if l = l' then [] else st.pending.getD l' []) ∧
      s0.dead = st.dead ∧ st'.avoid = st1.avoid ∧ st'.next = st1.next ∧ st'.dead = st1.dead ∧
      (∀ l', st'.labelDepth[l']? = if l = l' then st.labelDepth[l']? else st1.labelDepth[l']?) ∧
      (∀ l', st'.pending.getD l' [] =
        if l = l' then st.pending.getD l' [] else st1.pending.getD l' []) ∧
      a.hasObl = B.hasObl ∧ a.regs = B.regs ∧ a.drop = false ∧
      a.ax = (B.ax &&
        ((st1.pending.getD l []).filter fun e => !st1.dead.contains e).reverse.isEmpty) ∧
      (B.out.isNil = false → a.out.isNil = false) ∧
      (∀ k, s0.carries.getD k [] = if d + 1 = k then [] else st.carries.getD k []) ∧
      (∀ k, st'.carries.getD k [] = if d + 1 = k then [] else st1.carries.getD k []) ∧
      a.tgt = B.tgt.popEq (d + 1) ∧ st'.back = st1.back ∧
      (∀ x, a.A.contains x = true →
        B.A.contains x = true ∨ ∃ e ∈ st1.carries.getD (d + 1) [], e.1 = x) ∧
      (WFSt st → WFSt s0) := by
  unfold wpStmt at h
  run_peel h
  run_peel h
  jp_gen h
  split at h
  case' h_1 =>
    obtain ⟨r, s2, h2, h⟩ := wm_run_bind_ok h
    have hw2 := wFreshBool_walk h2
    cases (wFreshBool_run _ _).symm.trans h2
  all_goals
    run_peel h
    subst hK
    head_red_at h
    obtain ⟨B, st1, hB, h⟩ := wm_run_bind_ok h
    run_peel h
    run_peel h
    obtain ⟨_, s4, hl, h⟩ := wm_run_bind_ok h
    obtain ⟨live, clock, rfl, -⟩ := liveAdd_step hl
    cases h
    refine ⟨_, _, B, st1, hB, ?_⟩
    and_intros
  all_goals first
    | exact fun _ => labelDepth_restore | exact fun _ => pending_restore
    | (intro _; simp only [Std.HashMap.getElem?_insert, Std.HashMap.getD_insert,
        Std.HashMap.getD_erase, beq_iff_eq]; done)
    | rfl | exact fun _ => rfl | exact Nat.le_refl _ | assumption | exact hw2.next
    | (intro h; cases h; done) | (intro h; exact absurd rfl h)
    | exact fun hw => hw2.wf (wfSt_blk hw l d st.clock) nofun | exact fun hw => wfSt_blk hw l d _
    | exact fun x hx => (foldl_insert_fst (fun _ _ => rfl) hx).imp id
        fun ⟨e, he, h⟩ => ⟨e, (List.mem_filter.1 he).1, h⟩
    | exact fun hB => by simp [Rope.isNil_app', hB]

open Lean Meta Elab Tactic in
/-- On a hypothesis `h : m.run s = .ok (a, s')`, adds the facts of `Good CP m Q` for this run to
    the context, leaving `Good CP m Q` as the first goal. -/
local elab "good_at " h:ident " with " q:term:max " using " cp:term : tactic =>
    withMainContext do
  let fv ← getFVarId h
  let ty ← instantiateMVars (← fv.getType)
  let m := ty.appFn!.appArg!.appFn!.appArg!
  let Q ← elabTerm q none
  let CP ← elabTerm cp none
  let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Good #[CP, m, Q])
  let pf ← mkAppM ``good_use #[mkFVar fv, g]
  let (_, main) ← (← (← getMainGoal).assert `hq (← inferType pf) pf).intro1P
  replaceMainGoal [g.mvarId!, main]

omit iW in
/-- A name of the guarded program with a counter from the state's counter on has no back-map
    entry in a well-formed state. -/
private theorem back_none (hw : WFSt st) {b : String} {j : Nat} (hj : st.next ≤ j) :
    st.back[freshName (P := P) b j]? = none :=
  Option.eq_none_iff_forall_ne_some.2 fun x hx => by grind [hw.back_fresh, freshName_counter_inj]

section
omit iDE iHB iHF iHS iHI iL iHV iW

/-- An element of a filtering fold over a hash set is an element of the set. -/
theorem fold_filter_mem {A : Std.HashSet P.Ident} {c : P.Ident → Bool} {t : Bool}
    {x : P.Ident} (h : x ∈ (if t = true then A.fold (fun l y => if c y = true then y :: l else l) []
      else [])) : A.contains x = true :=
  by split at h <;> simp_all [Std.HashSet.fold_eq_foldl_toList, ← List.foldl_filter]

/-- A name is in a hash set after inserting the names of a list exactly when it was before or
    is in the list. -/
theorem foldl_insert_contains (L : List P.Ident) :
    ∀ (D : Std.HashSet P.Ident) (e : P.Ident),
      (L.foldl (·.insert ·) D).contains e = true ↔ D.contains e = true ∨ e ∈ L :=
  by induction L <;> grind

/-- A name is in the union of two hash sets exactly when it is in one of them. -/
theorem unionSet_contains (a b : Std.HashSet P.Ident) (x : P.Ident) :
    (unionSet a b).contains x = (a.contains x || b.contains x) := by
  unfold unionSet
  split <;> rw [Std.HashSet.fold_eq_foldl_toList] <;> grind [foldl_insert_contains]

/-- A name in the union of two hash sets each replaced by the empty set under a condition is in
    one of them. -/
private theorem union_ite_contains {t e : Bool} {A B : Std.HashSet P.Ident} {x : P.Ident}
    (h : (unionSet (if t = true then ∅ else A) (if e = true then ∅ else B)).contains x = true) :
    A.contains x = true ∨ B.contains x = true := by grind [unionSet_contains]

end

/-- A selector condition of the guarded program: built from variables, literals and
    conditionals. -/
@[expose] def wsimple : WExpr P → Prop
  | .var _ | .lit _ => True
  | .ite c t e => wsimple c ∧ wsimple t ∧ wsimple e
  | .user _ _ => False

/-- The variables of an expression of the guarded program built without loop-free
    expressions. -/
@[expose] def wvars : WExpr P → List P.Ident
  | .var x => [x]
  | .lit _ => []
  | .ite c t e => wvars c ++ wvars t ++ wvars e
  | .user _ _ => []

/-- A name of the guarded program that a walk with loop-free names `D` may assign, as seen in
    the walk state `s`: a renaming recorded in the back map, or a loop-free name. -/
private def TName (D : List P.Ident) (s : WSt P) (n : P.Ident) : Prop :=
  (∃ x, s.back[n]? = some x) ∨ n ∈ D

/-- A name drawn between `st` and `st'` that is no renaming at `st'`. -/
private def FName (st st' : WSt P) (y : P.Ident) : Prop :=
  (∃ b j, y = freshName b j ∧ st.next ≤ j ∧ j < st'.next ∧ st.avoid.contains y = false) ∧
    st'.back[y]? = none

/-- A concatenation fold is empty exactly when its start and all its operands are. -/
theorem Rope.isNil_foldl_app' {α : Type} (l : List (Rope α)) (s : Rope α) :
    (l.foldl Rope.app s).isNil = (s.isNil && l.all Rope.isNil) :=
  by induction l generalizing s <;> simp_all [Rope.isNil_app', Bool.and_assoc]

/-- An optionally drawn name: `none` leaves the state unchanged, `some x` is drawn by
    `wFreshBool b`. -/
@[expose] def OptDraw (b : String) (s s' : WSt P) : Option P.Ident → Prop
  | none => s' = s
  | some x => (wFreshBool b).run s = .ok (x, s')

/-- The variable of an optional guard name, `false` without one. -/
@[expose] def optVar : Option P.Ident → WExpr P
  | some x => .var x
  | none => .lit false

/-- The copy pairs of `cps` whose carried merges an arm registers when `o` is the largest target
    depth of its exits: the pairs whose variable is live in `st` before the clock at which the
    walk entered the block at that depth. -/
@[expose] def carryOf (st : WSt P) (cps : List (P.Ident × P.Ident)) :
    Option Nat → List (P.Ident × P.Ident)
  | some t => cps.filter fun p => liveBefore st p.1 (st.stampAt.getD t 0)
  | none => []

/-- The carried merges `C` after registering at the depth `o` (if any) the merges
    `(x, ite(e, xB, x), xB)` of the copy pairs `(x, xB)` of `cps`. -/
@[expose] def carryIns (e : WExpr P) (cps : List (P.Ident × P.Ident))
    (C : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))) :
    Option Nat → Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))
  | some t => C.insert t (cps.foldl (fun l x => (x.1, e.ite (.var x.2) (.var x.1), x.2) :: l)
      (C.getD t []))
  | none => C

/-- The guard of the carried merges of the else arm of a laid-out `ite` under the context `κ`,
    with the optional merge guard `gm` and the optional else-arm carry guards `qm`, `rEm`. -/
@[expose] def elseGuard (κ : RE P) (gm qm rEm : Option P.Ident) : WExpr P :=
  match κ, qm, rEm with
  | .top, _, _ => (optVar gm).not
  | .name _, some qm, _ => (WExpr.var qm).and (optVar gm).not
  | _, _, some rEm => .var rEm
  | _, _, _ => .lit false

/-- The context of the else arm of a laid-out `ite` under `κ`, with guard `g`, drawn from `s3`
    to `s4`: `neg g` under `top`, `andNeg q g` under `name q`, otherwise `name x` for a reach `x`
    drawn for it, recorded in `rE`. -/
@[expose] def LaidElseCtx (κ : RE P) (g : P.Ident) (s3 : WSt P) (κE : RE P) (rE : Option P.Ident)
    (s4 : WSt P) : Prop :=
  κ = .top ∧ κE = .neg g ∧ rE = none ∧ s4 = s3 ∨
    (∃ q, κ = .name q ∧ κE = .andNeg q g) ∧ rE = none ∧ s4 = s3 ∨
    (κ ≠ .top ∧ ∀ q, κ ≠ .name q) ∧ ∃ x, κE = .name x ∧ rE = some x ∧
      (wFreshBool "r").run s3 = .ok (x, s4)

/-- The steps of a successful run of a laid-out `ite` from `s` to `s'` with result `r`, as an
    elimination principle (every `Q` that follows from the steps holds): the renaming of the
    condition, the draws of the guard `g` and of the then-arm reach `rT`, the else-arm context
    `κE` (`LaidElseCtx`), the runs of the arms, the three save/restore steps, the optional draws of
    the merge guard `gm` (drawn exactly when `needGm` holds) and of the else-arm carry guards `qm`
    (drawn exactly under `name q` when the else arm carries merges) and `rEm` (drawn exactly when
    the else arm has a reach `rE` and carries merges), the registrations of the carried merges, and
    the result. -/
@[expose] def LaidSteps (κ : RE P) (d : Nat) (c : P.Expr) (tss ess : PStmts P) (s : WSt P)
    (r : WRes P) (s' : WSt P) : Prop :=
  ∀ Q : Prop, (∀ wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT rsT cpsT s8 svE
      cpE rsE cpsE s9 gm s10 qm s11 rEm s12,
    let t0 := s4.clock
    let M := if T.ax then [] else interSet T.A E.R
    let CT := if T.ax then T.A.fold (fun l x =>
        if liveBefore s6 x t0 || E.R.contains x then x :: l else l) [] else []
    let CE := if E.ax then E.A.fold (fun l x => if liveBefore s6 x t0 then x :: l else l) [] else []
    let liveM := cps3.filter fun (p : P.Ident × P.Ident) => liveBefore s6 p.1 t0
    let carryT := carryOf s6 cpsT T.tgt.max?
    let carryE := carryOf s6 cpsE E.tgt.max?
    let needGm := (liveM.any fun (x, _) => E.A.contains x && !E.ax) || !carryT.isEmpty ||
      (!carryE.isEmpty && match κ with | .top | .name _ => true | _ => false)
    let regs : Rope P.Ident :=
      (T.regs.app E.regs).app (Rope.ofList (carryT.map (·.2) ++ carryE.map (·.2)))
    let gmE := optVar gm
    let mergesL : Rope (WItem P) := liveM.foldl (fun acc (x, xT) =>
      acc.app (.one (.set x (some (if E.A.contains x && !E.ax then .ite gmE (.var xT) (.var x)
        else .var xT))))) .nil
    let s14 := { s12 with carries := (carryIns (elseGuard κ gm qm rEm) carryE
      (carryIns gmE carryT s12.carries T.tgt.max?) E.tgt.max?) }
    let U : Rope (WItem P) :=
      if leOpt T.minT d || leOpt E.minT d then
        let X := (WExpr.var rT).or (kExpr κE)
        match κ with
        | .top => .one (.assume joinLabel X .empty)
        | κ => setReach κ X
      else .nil
    let bool := TyRef.known (P := P) HasBool.boolTy
    let rTi : Rope (WItem P) := if T.out.isNil && U.isNil then .nil
      else .one (.init rT bool (some (.var g)))
    let gmi : Rope (WItem P) := match gm with
      | some x => .one (.init x bool (some (.var g))) | none => .nil
    let qmi : Rope (WItem P) := match κ, qm with
      | .name q, some x => .one (.init x bool (some (.var q))) | _, _ => .nil
    let rEi : Rope (WItem P) := match rE with
      | some r => if E.out.isNil && U.isNil && rEm.isNone then .nil
        else .one (.init r bool (some (kAnd κ (WExpr.var g).not)))
      | none => .nil
    let rEmi : Rope (WItem P) := match rE, rEm with
      | some r, some x => .one (.init x bool (some (.var r))) | _, _ => .nil
    let body : Rope (WItem P) :=
      [rTi, gmi, qmi, sv3, svT, T.out, cp3, cpT, rs3, rsT, rEi, rEmi, svE, E.out, cpE, rsE,
        mergesL, U].foldl Rope.app .nil
    (wRen c).run s = .ok ((wc, rdc), s1) → (wFreshBool "g").run s1 = .ok (g, s2) →
    (wFreshBool "r").run s2 = .ok (rT, s3) → LaidElseCtx κ g s3 κE rE s4 →
    (wpList κE d true ess).run s4 = .ok (E, s5) →
    (wpList (.name rT) d true tss).run s5 = .ok (T, s6) →
    (saveRestore M).run s6 = .ok ((sv3, cp3, rs3, cps3), s7) →
    (saveRestore CT).run s7 = .ok ((svT, cpT, rsT, cpsT), s8) →
    (saveRestore CE).run s8 = .ok ((svE, cpE, rsE, cpsE), s9) →
    OptDraw "g" s9 s10 gm → (gm.isSome ↔ needGm = true) → OptDraw "r" s10 s11 qm →
    (qm.isSome ↔ (∃ q, κ = .name q) ∧ carryE.isEmpty = false) → OptDraw "r" s11 s12 rEm →
    (rEm.isSome ↔ rE.isSome ∧ carryE.isEmpty = false) →
    (body.isNil = true ∧ s' = s14 ∧
      r = { A := {}, R := {}, minT := minOpt T.minT E.minT, tgt := T.tgt.merge E.tgt,
            ax := T.ax && E.ax, regs := regs }) ∨
    (body.isNil = false ∧ (liveAdd (rdc ++ RE.vars κ)).run s14 = .ok ((), s') ∧
      r = { out := Rope.app (.one (.init g bool (some (kAnd κ wc)))) body, sk := [.ite g T.sk E.sk],
            hasObl := T.hasObl || E.hasObl, minT := minOpt T.minT E.minT,
            A := unionSet (if T.ax then {} else T.A) (if E.ax then {} else E.A),
            R := unionSet (unionSet T.R E.R) (Std.HashSet.ofList rdc),
            ax := T.ax && E.ax, tgt := T.tgt.merge E.tgt, regs := regs }) → Q) → Q

/-- The inversion of the first bind of the walk run `h`, `h` becoming the continuation's run. -/
local macro "wm_peel " h:ident p:Lean.Parser.Tactic.rcasesPatMed : tactic => `(tactic| (
  replace $h:ident := wm_run_bind_ok $h
  obtain $p := $h))

/-- From `h : (do let x ← wFreshBool b; K (some x)).run s = .ok (r, s')` or
    `h : (K none).run s = .ok (r, s')`, closes the goal that some optional draw `o` from `s`,
    present exactly when a condition holds, is followed by a run of `K o`, given a proof `p` of the
    condition (first form) or a proof `n` of its negation (second form). -/
local macro "laid_draw " h:ident p:term:max n:term:max : tactic => `(tactic| first
  | (obtain ⟨x, _, h1, $h:ident⟩ := wm_run_bind_ok $h
     simp only [pure_bind] at $h:ident
     exact ⟨some x, _, h1, iff_of_true rfl $p, $h⟩)
  | (simp only [pure_bind] at $h:ident
     exact ⟨none, _, rfl, iff_of_false nofun $n, $h⟩))

omit iL iW in
/-- A run of the optional registration at depth `o` of the carried merges of the copy pairs
    `cps` under the guard `e`, followed by `K`, is a run of `K` from the state with the carried
    merges `carryIns e cps`. -/
private theorem carry_run {α : Type} {o : Option Nat} {e : WExpr P}
    {cps : List (P.Ident × P.Ident)} {K : Unit → WM P α} {s : WSt P} {r : Except String (α × WSt P)}
    (h : (match o with
      | some t => do
        let y ← modify fun st : WSt P => { st with carries := carryIns e cps st.carries (some t) }
        K y
      | _ => do let y ← pure PUnit.unit; K y).run s = r) :
    (K ()).run { s with carries := carryIns e cps s.carries o } = r := by cases o <;> exact h

omit iL in
/-- Every successful run of a laid-out `ite` has the steps of `LaidSteps`. -/
theorem wpIteLaid_inv {c : P.Expr} {tss ess : PStmts P} {s s' : WSt P} {r : WRes P}
    (h : (wpIteLaid κ d c tss ess).run s = .ok (r, s')) : LaidSteps κ d c tss ess s r s' := by
  intro Q hQ
  unfold wpIteLaid at h
  wm_peel h ⟨⟨wc, rdc⟩, s1, h1, h⟩
  wm_peel h ⟨g, s2, h2, h⟩
  wm_peel h ⟨rT, s3, h3, h⟩
  jp_gen h
  replace h : ∃ κE rE s4, LaidElseCtx κ g s3 κE rE s4 ∧ (K (κE, rE)).run s4 = .ok (r, s') := by
    cases κ
    · exact ⟨_, _, _, .inl ⟨rfl, rfl, rfl, rfl⟩, h⟩
    · exact ⟨_, _, _, .inr (.inl ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩), h⟩
    all_goals
      wm_peel h ⟨x, s4, h4, h⟩
      exact ⟨_, _, _, .inr (.inr ⟨⟨nofun, nofun⟩, x, rfl, rfl, h4⟩), h⟩
  obtain ⟨κE, rE, s4, hctx, h⟩ := h
  subst hK
  head_whnf_at h
  wm_peel h ⟨_, _, ⟨⟩, h⟩
  wm_peel h ⟨E, s5, h5, h⟩
  wm_peel h ⟨T, s6, h6, h⟩
  wm_peel h ⟨_, _, ⟨⟩, h⟩
  wm_peel h ⟨⟨sv3, cp3, rs3, cps3⟩, s7, h7, h⟩
  head_whnf_at h
  wm_peel h ⟨⟨svT, cpT, rsT, cpsT⟩, s8, h8, h⟩
  head_whnf_at h
  wm_peel h ⟨⟨svE, cpE, rsE, cpsE⟩, s9, h9, h⟩
  head_red_at h
  jp_gen h
  replace h : ∃ gm s10, OptDraw "g" s9 s10 gm ∧ (gm.isSome ↔
      (((cps3.filter fun p => liveBefore s6 p.1 s4.clock).any fun (x, _) =>
        E.A.contains x && !E.ax) || !(carryOf s6 cpsT T.tgt.max?).isEmpty ||
        (!(carryOf s6 cpsE E.tgt.max?).isEmpty &&
          match (generalizing := false) κ with | .top | .name _ => true | _ => false)) = true) ∧
      (K gm).run s10 = .ok (r, s') := by
    rcases wm_run_ite h with ⟨hb, h⟩ | ⟨hb, h⟩ <;> laid_draw h hb hb
  obtain ⟨gm, s10, hgm, hg, h⟩ := h
  subst hK
  head_red_at h
  jp_gen h
  replace h : ∃ qm s11, OptDraw "r" s10 s11 qm ∧
      (qm.isSome ↔ (∃ q, κ = .name q) ∧ (carryOf s6 cpsE E.tgt.max?).isEmpty = false) ∧
      (K qm).run s11 = .ok (r, s') := by
    split at h <;> rename_i hne <;> laid_draw h ⟨⟨_, rfl⟩, hne⟩ fun ⟨⟨q, hq⟩, he⟩ => hne q hq he
  obtain ⟨qm, s11, hqm, hq, h⟩ := h
  subst hK
  head_red_at h
  jp_gen h
  replace h : ∃ rEm s12, OptDraw "r" s11 s12 rEm ∧
      (rEm.isSome ↔ rE.isSome ∧ (carryOf s6 cpsE E.tgt.max?).isEmpty = false) ∧
      (K rEm).run s12 = .ok (r, s') := by
    split at h <;> rename_i hne <;> laid_draw h ⟨rfl, hne⟩
      fun ⟨hs, he⟩ => (Option.isSome_iff_exists.1 hs).elim fun _ hx => hne _ hx he
  obtain ⟨rEm, s12, hrm, hr, h⟩ := h
  refine hQ wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT rsT cpsT s8 svE cpE
    rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hctx h5 h6 h7 h8 h9 hgm hg hqm hq hrm hr ?_
  subst hK
  head_red_at h
  replace h := carry_run (carry_run h)
  head_whnf_at h
  rcases wm_run_ite h with ⟨hb, h⟩ | ⟨hb, h⟩
  · exact .inl ⟨hb, (wm_run_pure_ok h).2.symm, (wm_run_pure_ok h).1.symm⟩
  · wm_peel h ⟨_, s13, h13, h⟩
    exact .inr ⟨Bool.eq_false_iff.2 hb, (wm_run_pure_ok h).2 ▸ h13, (wm_run_pure_ok h).1.symm⟩

omit iL iW in
/-- The registered copy pairs are copy pairs. -/
theorem carryOf_sub {cps : List (P.Ident × P.Ident)} {o : Option Nat} {p : P.Ident × P.Ident}
    (h : p ∈ carryOf st cps o) : p ∈ cps := by cases o <;> grind [carryOf]

omit iW in
/-- An optional draw is a join step drawing the name it returns, and keeps well-formedness. -/
private theorem OptDraw.jstep {b : String} {s s' : WSt P} {o : Option P.Ident}
    (h : OptDraw b s s' o) : JStep s (fun y => o = some y) s' ∧ (WFSt s → WFSt s') := by
  cases o with
  | none => exact h ▸ ⟨JStep.refl _, id⟩
  | some x => exact ⟨wfb_step h, fun hw => (wFreshBool_walk h).wf hw nofun⟩

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW in
/-- The carried merges at depth `k` after `carryIns e cps C o` are new merges in front of those
    of `C`, the merges `(x, ite(e, xB, x), xB)` of copy pairs `(x, xB)` of `cps`, when `o` is
    `some k`. -/
theorem carryIns_getD (e : WExpr P) (cps : List (P.Ident × P.Ident))
    (C : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))) (o : Option Nat) (k : Nat) :
    ∃ new, (carryIns e cps C o).getD k [] = new ++ C.getD k [] ∧
      ∀ q ∈ new, o = some k ∧ ∃ p ∈ cps, q = (p.1, e.ite (.var p.2) (.var p.1), p.2) := by
  cases o with
  | none => exact ⟨[], rfl, nofun⟩
  | some t =>
    rw [carryIns, Std.HashMap.getD_insert]
    split
    · obtain rfl := beq_iff_eq.1 ‹_›
      exact ⟨_, List.foldl_flip_cons_eq_append, fun q hq => ⟨rfl, by grind⟩⟩
    · exact ⟨[], rfl, nofun⟩

/-- The facts of a laid-out `ite` walk from `st` to `st'` with result `a`: an `Ext` step to
    the walk of the else arm under a variable context, the walk of the then arm under `name rT`,
    and an `Ext` step after it; the result always exits when both arms do, does not drop, has
    the registrations of both arms and names drawn after the arms, and has the obligations of
    the arms when an arm's output is not empty. -/
private def LaidInv (d : Nat) (tss ess : PStmts P) (st : WSt P) (a : WRes P) (st' : WSt P) : Prop :=
  ∃ κE s4 E s5 rT T s6, (wpList κE d true ess).run s4 = .ok (E, s5) ∧
    (wpList (.name rT) d true tss).run s5 = .ok (T, s6) ∧ κE ≠ .top ∧ Ext st s4 ∧
    (s4.dead = st.dead ∧ s4.pending = st.pending ∧
      ∀ k, s4.carries.getD k [] = st.carries.getD k []) ∧ Ext s6 st' ∧
    (st'.dead = s6.dead ∧ st'.pending = s6.pending ∧
      ∀ k, ∃ pre, st'.carries.getD k [] = pre ++ s6.carries.getD k [] ∧
        ∀ q ∈ pre, (T.tgt.max? = some k ∨ E.tgt.max? = some k) ∧ q.2.2 ∈ a.regs.toList ∧
          NewIn s6 st' q.2.2 ∧ (T.A.contains q.1 = true ∨ E.A.contains q.1 = true) ∧
          (WFSt s6 → ∃ c, q.2.1 = .ite c (.var q.2.2) (.var q.1) ∧ wsimple c ∧
            ∀ y ∈ wvars c, FName s6 st' y)) ∧
    a.ax = (T.ax && E.ax) ∧
    a.drop = false ∧
    (∀ e ∈ a.regs.toList, e ∈ T.regs.toList ∨ e ∈ E.regs.toList ∨
      NewIn s6 st' e ∧ (WFSt s6 → st'.back[e]? = none)) ∧
    (∀ e, e ∈ T.regs.toList ∨ e ∈ E.regs.toList → e ∈ a.regs.toList) ∧
    (a.hasObl = true → a.out.isNil = false) ∧
    (T.out.isNil = false ∨ E.out.isNil = false → a.hasObl = (T.hasObl || E.hasObl)) ∧
    a.tgt = T.tgt.merge E.tgt ∧
    (∀ x, a.A.contains x = true → T.A.contains x = true ∨ E.A.contains x = true) ∧
    BackNew s6 st' ∧ (WFSt st → WFSt s4) ∧ BackNew st s4

/-- The walk of a laid-out `ite` has the facts `LaidInv`. -/
private theorem wpIteLaid_run {c : P.Expr} {tss ess : PStmts P} {st st' : WSt P} {a : WRes P}
    (h : (wpIteLaid κ d c tss ess).run st = .ok (a, st')) : LaidInv d tss ess st a st' := by
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hc h5 h6 h7 h8 h9 h10 _ h11 _
    h12 _ hEnd => ?_
  obtain ⟨e1, ⟨d1, p1⟩, c1, b1, -⟩ := (good_wRen (CP := fun _ _ => False) c).run _ _ _ h1
  obtain ⟨h4, hne⟩ : OptDraw "r" s3 s4 rE ∧ κE ≠ .top := by
    rcases hc with ⟨-, rfl, rfl, rfl⟩ | ⟨⟨q, -, rfl⟩, rfl, rfl⟩ | ⟨-, x, rfl, rfl, hx⟩ <;>
      exact ⟨by first | rfl | exact hx, nofun⟩
  have J1 := ((wfb_step h2).trans (wfb_step h3)).trans h4.jstep.1
  have J := (((saveRestore_new h7).1.trans (saveRestore_new h8).1).trans
    (saveRestore_new h9).1).trans ((h10.jstep.1.trans h11.jstep.1).trans h12.jstep.1)
  generalize hX : carryIns (elseGuard κ gm qm rEm) (carryOf s6 cpsE E.tgt.max?)
    (carryIns (optVar gm) (carryOf s6 cpsT T.tgt.max?) s12.carries T.tgt.max?)
      E.tgt.max? = X at hEnd
  obtain ⟨e10, b10, d10, p10, rfl, hax, hdr, htg, hAL, hob, hho, hreg⟩ : Ext s12 st' ∧
      BackNew s12 st' ∧ st'.dead = s12.dead ∧ st'.pending = s12.pending ∧ X = st'.carries ∧
      a.ax = (T.ax && E.ax) ∧ a.drop = false ∧ a.tgt = T.tgt.merge E.tgt ∧
      (∀ x, a.A.contains x = true → T.A.contains x = true ∨ E.A.contains x = true) ∧
      (a.hasObl = true → a.out.isNil = false) ∧
      (T.out.isNil = false ∨ E.out.isNil = false → a.hasObl = (T.hasObl || E.hasObl)) ∧
      a.regs = _ := by
    rcases hEnd with ⟨hb, rfl, rfl⟩ | ⟨hb, hl, rfl⟩
    case' inr => obtain ⟨live, clock, rfl, -⟩ := liveAdd_step hl
    all_goals refine ⟨Ext.of_eq rfl (Nat.le_refl _) rfl rfl rfl, BackNew.of_eq rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, fun x hx => ?_, ?_, ?_, rfl⟩
    all_goals first
      | exact union_ite_contains hx
      | simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at hx
      | (intro h; cases h; done)
      | (intro _; simp only [Rope.isNil_app', Rope.isNil_one_eq, Bool.false_and]; done)
      | exact fun _ => rfl
      | (intro hTE
         simp only [Rope.isNil_foldl_app', List.all_cons, List.all_nil, Bool.and_true,
           Bool.and_eq_true] at hb
         rcases hTE with h | h <;> simp [h] at hb)
  have hG : (wsimple (optVar gm) ∧ ∀ y ∈ wvars (optVar gm), gm = some y) ∧
      wsimple (elseGuard κ gm qm rEm) ∧
        ∀ y ∈ wvars (elseGuard κ gm qm rEm), gm = some y ∨ qm = some y ∨ rEm = some y := by
    unfold elseGuard
    cases gm <;> split <;> simp [optVar, wsimple, wvars, WExpr.not, WExpr.and]
  have hJ := fun y hy => (J.sel y hy).elim fun b ⟨j, hj, h1, h2, h3⟩ =>
    And.intro (⟨b, j, hj, h3, h1, Nat.lt_of_lt_of_le h2 e10.next⟩ : NewIn s6 st' y)
      fun ws6 => (⟨⟨b, j, hj, h1, Nat.lt_of_lt_of_le h2 e10.next, h3⟩, hj ▸
        (BackNew.keep b10 ⟨b, j, rfl, h2⟩).trans (J.back ▸ back_none ws6 h1)⟩ : FName s6 st' y)
  refine ⟨_, _, E, _, rT, T, s6, h5, h6, hne, e1.trans J1.ext,
    ⟨J1.dead.trans d1, J1.pend.trans p1, fun k => J1.car ▸ c1.noCP k⟩, J.ext.trans e10,
    ⟨d10.trans J.dead, p10.trans J.pend, fun k => ?_⟩, hax, hdr, fun e he => ?_,
    fun e he => by simp only [hreg, Rope.toList_app, List.mem_append]; exact .inl he, hob, hho,
    htg, hAL, (BackNew.of_eq J.back).trans b10 J.ext.avoid J.ext.next, fun hw => h4.jstep.2
      ((wFreshBool_walk h3).wf ((wFreshBool_walk h2).wf ((wRen_walk h1).wf hw nofun) nofun) nofun),
    b1.trans (BackNew.of_eq J1.back) e1.avoid e1.next⟩
  · obtain ⟨n5, e5, hn5⟩ := carryIns_getD (optVar gm) (carryOf s6 cpsT T.tgt.max?) s12.carries
      T.tgt.max? k
    obtain ⟨n6, e6, hn6⟩ := carryIns_getD (elseGuard κ gm qm rEm) (carryOf s6 cpsE E.tgt.max?)
      (carryIns (optVar gm) (carryOf s6 cpsT T.tgt.max?) s12.carries T.tgt.max?) E.tgt.max? k
    refine ⟨n6 ++ n5, by rw [← hX, e6, e5, List.append_assoc, J.car], fun q hq => ?_⟩
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨hk, p, hp, rfl⟩ := hn6 q hq
      exact ⟨.inr hk, by simp [hreg, Rope.toList_app, Rope.toList_ofList, List.mem_map_of_mem hp],
        (hJ _ (.inl (.inr ⟨p, carryOf_sub hp, rfl⟩))).1,
        .inr (fold_filter_mem ((saveRestore_new h9).2 p (carryOf_sub hp))),
        fun ws6 => ⟨_, rfl, hG.2.1, fun y hy => (hJ y (.inr (or_assoc.2 (hG.2.2 y hy)))).2 ws6⟩⟩
    · obtain ⟨hk, p, hp, rfl⟩ := hn5 q hq
      exact ⟨.inl hk, by simp [hreg, Rope.toList_app, Rope.toList_ofList, List.mem_map_of_mem hp],
        (hJ _ (.inl (.inl (.inr ⟨p, carryOf_sub hp, rfl⟩)))).1,
        .inl (fold_filter_mem ((saveRestore_new h8).2 p (carryOf_sub hp))),
        fun ws6 => ⟨_, rfl, hG.1.1, fun y hy => (hJ y (.inr (.inl (.inl (hG.1.2 y hy))))).2 ws6⟩⟩
  · simp only [hreg, Rope.toList_app, Rope.toList_ofList, List.mem_append, List.mem_map] at he
    refine or_assoc.1 (he.imp_right fun h => ?_)
    exact (hJ e (.inl (h.imp (fun ⟨p, hp, h⟩ => .inr ⟨p, carryOf_sub hp, h⟩)
      fun ⟨p, hp, h⟩ => ⟨p, carryOf_sub hp, h⟩))).imp_right fun f w => (f w).2

/-- The part of `Ext` that a walk from a state with other label depths and snapshots keeps: the
    avoided names, a counter that does not decrease, and dead names that are old or drawn. -/
private structure ExtD (st st' : WSt P) : Prop where
  avoid : st'.avoid = st.avoid
  next : st.next ≤ st'.next
  dead : ∀ e : P.Ident, st'.dead.contains e = true → st.dead.contains e = true ∨ NewIn st st' e
  deadMono : ∀ e : P.Ident, st.dead.contains e = true → st'.dead.contains e = true

section
omit iL iW

/-- An `Ext` step is an `ExtD` step. -/
private theorem Ext.toExtD (h : Ext st st') : ExtD st st' := ⟨h.avoid, h.next, h.dead, h.deadMono⟩

/-- `ExtD` steps compose. -/
private theorem ExtD.trans {s0 s1 s2 : WSt P} (h1 : ExtD s0 s1) (h2 : ExtD s1 s2) : ExtD s0 s2 := by
  grind [ExtD, NewIn]

/-- A change keeping the avoided names and the dead names, with a counter that does not
    decrease, is an `ExtD` step. -/
private theorem ExtD.of_eq (h1 : st'.avoid = st.avoid) (h2 : st.next ≤ st'.next)
    (h3 : st'.dead = st.dead) : ExtD st st' := ⟨h1, h2, fun _ h => .inl (h3 ▸ h), fun _ h => h3 ▸ h⟩

/-- An `ExtD` step to a state with the label depths and snapshots of the start, followed by an
    `Ext` step, is an `Ext` step. -/
private theorem Ext.of_extD {s1 : WSt P} (h1 : ExtD st s1) (hl : s1.labelDepth = st.labelDepth)
    (hp : s1.pending = st.pending) (h2 : Ext s1 st') : Ext st st' := by grind [ExtD, Ext, NewIn]

/-- The facts of a real-branch walk from `st` to `st'` with result `a`: the arms are walked under
    `top` from the state with no live names, label depths and snapshots (each arm from its own
    copy for the live set), as an `ExtD` chain; the label depths and snapshots are restored. -/
private def RealInv (d : Nat) (tss ess : PStmts P) (st : WSt P) (a : WRes P) (st' : WSt P) : Prop :=
  ∃ E s2 T s3 s6, (wpList .top d false ess).run
      { st with live := {}, labelDepth := {}, pending := {} } = .ok (E, s2) ∧
    (wpList .top d false tss).run { s2 with live := {} } = .ok (T, s3) ∧
    ExtD s3 s6 ∧ s6.dead = s3.dead ∧ s6.labelDepth = st.labelDepth ∧ s6.pending = st.pending ∧
    Ext s6 st' ∧ (st'.dead = s6.dead ∧ st'.pending = s6.pending) ∧
    a.ax = false ∧ a.drop = false ∧ a.hasObl = (T.hasObl || E.hasObl) ∧
    (a.hasObl = true → a.out.isNil = false) ∧
    (∀ e ∈ a.regs.toList, e ∈ T.regs.toList ∨ e ∈ E.regs.toList) ∧
    (∀ k, st'.carries.getD k [] = s3.carries.getD k []) ∧ a.tgt = .empty ∧
    BackNew s3 st' ∧ (∀ x, a.A.contains x = true → T.A.contains x = true ∨ E.A.contains x = true)

macro_rules
  | `(tactic| gclose) => `(tactic| (
    refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
    split <;> (try split) <;> simp only [Rope.isNil_app', Rope.isNil_one_eq, Bool.false_and]))

include iL iW in
/-- The walk of a real branch has the facts `RealInv`. -/
private theorem wpIteReal_run {c : P.Expr} {tss ess : PStmts P}
    (h : (wpIteReal κ d c tss ess).run st = .ok (a, st')) : RealInv d tss ess st a st' := by
  unfold wpIteReal at h
  run_peel h
  run_peel h
  obtain ⟨E, s2, h2, h⟩ := wm_run_bind_ok h
  run_peel h
  run_peel h
  obtain ⟨T, s3, h3, h⟩ := wm_run_bind_ok h
  run_peel h
  obtain ⟨_, s6, h6, h⟩ := wm_run_bind_ok h
  refine ⟨E, s2, T, s3, s6, h2, h3, ?_⟩
  cases h6
  refine ⟨ExtD.of_eq rfl (Nat.le_refl _) rfl, rfl, rfl, rfl, ?_⟩
  split at h
  all_goals rename_i hc
  · cases h
    exact ⟨Ext.refl _, ⟨rfl, rfl⟩, rfl, rfl, by simpa using hc, nofun,
      fun _ h => by simp [Rope.toList_nil] at h, fun _ => rfl, rfl, BackNew.of_eq rfl,
      fun _ h => by simp at h⟩
  good_at h with (fun a : WRes P => a.ax = false ∧ a.drop = false ∧ a.hasObl = true ∧
      a.out.isNil = false ∧ a.regs = T.regs.app E.regs ∧ a.tgt = .empty ∧ a.A = unionSet T.A E.A)
    using fun (_ : Nat) (_ : P.Ident × WExpr P × P.Ident) => False
  · repeat' gstep
  obtain ⟨e7, ⟨d7, p7⟩, c7, b7, hax, hdr, hob, hout, hrg, htg, hA⟩ := hq
  refine ⟨e7, ⟨d7, p7⟩, hax, hdr, by simpa [hob, Decidable.or_iff_not_imp_left] using hc,
    fun _ => hout, fun e he => by simpa [hrg, Rope.toList_app] using he, c7.noCP, htg,
    (BackNew.of_eq rfl).trans b7 rfl (Nat.le_refl _), fun x hx => by
      simpa [hA, unionSet_contains] using hx⟩

include iW in
/-- A successful walk of `s :: rest` walks `rest`, then `s` with the obligation bit of the rest,
    and returns the result of `s` alone (after a drop, or after marking the registrations of the
    rest dead when `s` always exits) or the combination of both results. -/
theorem wpList_run_cons {rest : PStmts P} {st st' : WSt P} {R : WRes P}
    (h : (wpList κ d fEnd (s :: rest)).run st = .ok (R, st')) :
    ∃ r st1 a st2, (wpList κ d fEnd rest).run st = .ok (r, st1) ∧
      (wpStmt κ d (r.hasObl || (fEnd && !r.drop)) s).run st1 = .ok (a, st2) ∧
      ((a.drop = true ∧ a = R ∧ st2 = st') ∨
       (a.drop = false ∧ a.ax = true ∧ a = R ∧
         { st2 with dead := r.regs.toList.foldl (·.insert ·) st2.dead } = st') ∨
       (a.drop = false ∧ a.ax = false ∧ a.combine r = R ∧ st2 = st')) := by
  rw [wpList] at h
  obtain ⟨r, st1, h1, h⟩ := wm_run_bind_ok h
  obtain ⟨a, st2, h2, h⟩ := wm_run_bind_ok h
  refine ⟨r, st1, a, st2, h1, h2, ?_⟩
  cases ha : a.drop <;> cases hx : a.ax <;>
    simp only [ha, hx, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, map_pure, StateT.run_map,
      StateT.run_modify, StateT.run_pure] at h <;> cases h <;> simp

/-- Marking dead names drawn by an `Ext` step keeps it an `Ext` step. -/
private theorem Ext.markDead {st2 : WSt P} (h : Ext st st2) {L : List P.Ident}
    (hL : ∀ e ∈ L, NewIn st st2 e) : Ext st { st2 with dead := L.foldl (·.insert ·) st2.dead } := by
  grind [Ext, NewIn, foldl_insert_contains]

/-- A block walk is an `Ext` step when its body walk is. -/
private theorem block_ext {s0 st1 : WSt P} {l : String} (h1 : s0.avoid = st.avoid)
    (h2 : st.next ≤ s0.next)
    (h3 : ∀ l', s0.labelDepth[l']? = if l = l' then some (d + 1) else st.labelDepth[l']?)
    (h4 : ∀ l', s0.pending.getD l' [] = if l = l' then [] else st.pending.getD l' [])
    (h5 : s0.dead = st.dead) (hB : Ext s0 st1) (h6 : st'.avoid = st1.avoid)
    (h7 : st'.next = st1.next) (h8 : st'.dead = st1.dead)
    (h9 : ∀ l', st'.labelDepth[l']? = if l = l' then st.labelDepth[l']? else st1.labelDepth[l']?)
    (h10 : ∀ l', st'.pending.getD l' [] = if l = l' then st.pending.getD l' []
      else st1.pending.getD l' []) : Ext st st' := by grind [Ext, NewIn]

end

/-! ## Drops -/

/-- Only a main-list `exit` (under the reach context `top`) drops the rest of its list. -/
theorem wpStmt_drop (h : (wpStmt κ d f s).run st = .ok (a, st')) (hd : a.drop = true) :
    κ = .top ∧ ∃ l md, s = .exit l md := by
  cases s
  case exit l md => exact ⟨(wpStmt_exit_run h).2.2.2.1 hd, l, md, rfl⟩
  case block l b md => grind [wpStmt_block_run h]
  case' ite g t e md => cases g
  case det =>
    unfold wpStmt at h
    split at h
    · grind [LaidInv, wpIteLaid_run h]
    · grind [RealInv, wpIteReal_run h]
  all_goals grind [good_use h (wpStmt_cmd_good κ d f _ nofun nofun nofun), CmdQ]

/-- A list walk that drops the rest of an enclosing list is under the reach context `top` and
    walks a list without a normal run. -/
private theorem wpList_drop_run :
    ∀ {ss : PStmts P} {st st' : WSt P} {r : WRes P}, (wpList κ d fEnd ss).run st = .ok (r, st') →
      r.drop = true → κ = .top ∧ ∀ {F : P.Factory} {X : Outcome P → Prop}
        {σ σ1 : SemanticStore P} {evs : List (Event P)}, DRun F X ss σ evs (.normal σ1) → False
  | [], _, _, _, h, hd => by
    simp only [wpList, StateT.run_pure] at h
    cases h
    cases hd
  | _ :: _, _, _, _, h, hd => by
    obtain ⟨r, st1, a, st2, h1, h2, hc⟩ := wpList_run_cons h
    rcases hc with ⟨ha, rfl, rfl⟩ | ⟨ha, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
    · obtain ⟨hκ, l, md, rfl⟩ := wpStmt_drop h2 ha
      refine ⟨hκ, fun hr => ?_⟩
      rcases DRun.cons_inv hr with ⟨_, _, _, ⟨⟩, -⟩ | ⟨_, _, -, ⟨⟩⟩
    · cases ha.symm.trans hd
    · refine ⟨(wpList_drop_run h1 hd).1, fun hr => ?_⟩
      rcases DRun.cons_inv hr with ⟨σ2, evs1, evs2, hs, hr', -⟩ | ⟨l, σ2, -, ⟨⟩⟩
      exact (wpList_drop_run h1 hd).2 hr'

/-- A list walk that drops the rest of an enclosing list is under the reach context `top`. -/
theorem wpList_drop (h : (wpList κ d fEnd ss).run st = .ok (r, st')) (hd : r.drop = true) :
    κ = .top := (wpList_drop_run h hd).1

/-! ## The walk facts -/

section
omit iL iW

/-- A name drawn from a state with `DeadBelow` is not dead in it. -/
private theorem NewIn.not_dead {s' : WSt P} {e : P.Ident} (h : NewIn st s' e)
    (hd : DeadBelow st) : st.dead.contains e = false := by grind [NewIn, DeadBelow]

/-- `DeadBelow` holds after a change keeping the dead names and not decreasing the counter. -/
theorem DeadBelow.of_le (hd : DeadBelow st) (h1 : st'.dead = st.dead)
    (h2 : st.next ≤ st'.next) : DeadBelow st' := by grind [DeadBelow]

include iL in
/-- A name drawn by a walk step that was not dead before it is not dead after it. -/
private theorem not_dead_after {s0 s1 s2 : WSt P} {e : P.Ident} (he : NewIn s0 s1 e)
    (hd : s1.dead.contains e = false) (h : Ext s1 s2) : s2.dead.contains e = false :=
  Bool.eq_false_iff.2 fun hc => (h.dead e hc).elim (by simp [hd]) fun hn => he.disj hn rfl

omit iDE iHB iHF iHS iHI iHV in
/-- A name not dead in `D` and not in `L` is not dead after marking the names of `L` dead. -/
private theorem markDead_false {L : List P.Ident} {D : Std.HashSet P.Ident} {e : P.Ident}
    (hd : D.contains e = false) (hn : e ∉ L) : (L.foldl (·.insert ·) D).contains e = false := by
  induction L generalizing D <;> grind

/-- The snapshots of fresh-name form registered in a walk state have counters below the state's
    counter. -/
private def PendBelow (st : WSt P) : Prop :=
  ∀ (l : String) (e : P.Ident), e ∈ st.pending.getD l [] → ∀ b j, e = freshName b j → j < st.next

/-- A name drawn by a walk from `st` to `st'` is registered after it for at most one label. -/
private def Uniq (st st' : WSt P) : Prop :=
  PendBelow st → ∀ e, NewIn st st' e → ∀ l1 l2, e ∈ st'.pending.getD l1 [] →
    e ∈ st'.pending.getD l2 [] → l1 = l2

include iL in
/-- An `Ext` step keeps `PendBelow`. -/
private theorem PendBelow.ext (hP : PendBelow st) (h : Ext st st') : PendBelow st' :=
  fun l e he b j hj => by grind [PendBelow, NewIn, h.pendNew l e he, h.next, freshName_counter_inj]

/-- A name drawn from `st` on is not a snapshot of a state with `PendBelow`. -/
private theorem NewIn.not_pending {s' : WSt P} {e : P.Ident} (h : NewIn st s' e) (hP : PendBelow st)
    (l : String) : e ∉ st.pending.getD l [] := by grind [NewIn, PendBelow]

include iL in
/-- `Uniq` composes along `Ext` steps. -/
private theorem Uniq.trans {s0 s1 s2 : WSt P} (e1 : Ext s0 s1) (e2 : Ext s1 s2) (h1 : Uniq s0 s1)
    (h2 : Uniq s1 s2) : Uniq s0 s2 := by grind [Uniq, Ext, NewIn, PendBelow, freshName_counter_inj]

/-- A change keeping the snapshots draws nothing registered twice. -/
private theorem Uniq.of_pending (h : st'.pending = st.pending) : Uniq st st' :=
  fun hP _ hn l1 _ hl1 _ => absurd (h ▸ hl1) (hn.not_pending hP l1)

/-- The label depths of a walk state are at most `d`. -/
private def LabLe (st : WSt P) (d : Nat) : Prop :=
  ∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d

/-- The carried-merge facts of a walk at depth `d` from `st` to `st'` with result `r`: its exit
    targets are an ordered heap of depths of labels of `st`; at each depth up to `d` the carried
    merges gain merges in front only, at depths of labels of `st` that are exit targets, whose
    copies are registrations, or dead (when `c` holds); deeper merges are merges of `st`. -/
private structure CI (c : Prop) (d : Nat) (st : WSt P) (r : WRes P) (st' : WSt P) : Prop where
  ord : r.tgt.Ord
  tgt : ∀ t ∈ r.tgt.elems, ∃ l : String, st.labelDepth[l]? = some t
  pre : c → ∀ k, k ≤ d → ∃ pre, st'.carries.getD k [] = pre ++ st.carries.getD k [] ∧
    ∀ q ∈ pre, (q.2.2 ∈ r.regs.toList ∨ st'.dead.contains q.2.2 = true) ∧
      (k ∈ r.tgt.elems ∨ st'.dead.contains q.2.2 = true) ∧ ∃ l : String, st.labelDepth[l]? = some k
  high : ∀ k, d < k → ∀ q ∈ st'.carries.getD k [], q ∈ st.carries.getD k []

/-- No change of the carried merges, with an empty target heap, has the facts `CI`. -/
private theorem CI.of_eq {c : Prop} (ht : r.tgt = .empty)
    (hc : ∀ k, st'.carries.getD k [] = st.carries.getD k []) : CI c d st r st' :=
  ⟨by rw [ht]; trivial, fun _ h' => by simp [ht, LeftistHeap.elems] at h',
    fun _ k _ => ⟨[], by rw [hc, List.nil_append], nofun⟩, fun k _ q hq => hc k ▸ hq⟩

include iL in
/-- A `TName` of a well-formed state stays one along a `BackNew` step. -/
private theorem TName.keep {D : List P.Ident} {s s' : WSt P} (hw : WFSt s) (hb : BackNew s s')
    {n : P.Ident} (h : TName D s n) : TName D s' n :=
  h.imp (fun ⟨x, hx⟩ => ⟨x, (hb.keep (hw.back_fresh n x hx)).trans hx⟩) id

include iL in
/-- An `FName` stays one along a `BackNew` step that does not decrease the counter. -/
private theorem FName.keep {s s' : WSt P} (hb : BackNew s s') (hn : s.next ≤ s'.next) {y : P.Ident}
    (h : FName st s y) : FName st s' y := by grind [FName, hb.keep]

/-- An `FName` from a later start state is one from an earlier start state. -/
private theorem FName.widen {s0 s1 s2 : WSt P} (ha : s1.avoid = s0.avoid) (hn : s0.next ≤ s1.next)
    {y : P.Ident} (h : FName s1 s2 y) : FName s0 s2 y := by grind [FName]

end

omit iW in
/-- A name drawn before a `BackNew` step keeps its back-map entry along it. -/
private theorem BackNew.keepN {s0 s s' : WSt P} (hb : BackNew s s') {n : P.Ident}
    (hn : NewIn s0 s n) : s'.back[n]? = s.back[n]? := by grind [NewIn, hb.keep]

macro_rules | `(tactic| gclose) => `(tactic| rfl)

/-- The name a `set x` walk assigns is a renaming recorded after the walk, or `x`. -/
private theorem wpStmt_set_A {x : P.Ident} {e : ExprOrNondet P} {md : MetaData P}
    (h : (wpStmt κ d f (.cmd (.cmd (.set x e md)))).run st = .ok (a, st')) (hw : WFSt st) :
    ∀ n, a.A.contains n = true → (∃ y, st'.back[n]? = some y) ∨ n = x := by
  have key : ∀ {s1 s2 : WSt P} {n : P.Ident}, WFSt s1 → (wName x).run s1 = .ok (n, s2) →
      ∀ {s3 : WSt P}, BackNew s2 s3 → (∃ y, s3.back[n]? = some y) ∨ n = x := by
    intro s1 s2 n hw1 h2 s3 hb
    rcases wName_cases h2 with ⟨hnm, rfl⟩ | ⟨-, -, rfl, -⟩ | ⟨hx, ht, -, -⟩
    · obtain ⟨hbk, b, j, hn, hj, -⟩ := hw1.nm_fresh x n hnm
      exact .inl ⟨x, by rw [hb.keep ⟨b, j, hn, hj⟩, hbk]⟩
    · exact .inr rfl
    · obtain ⟨k, hn, -, hk, -, -, hbk⟩ := wName_fresh h2 hx ht
      exact .inl ⟨x, by rw [hb.keep ⟨_, k, hn, by omega⟩, hbk]⟩
  cases e <;> unfold wpStmt at h <;>
    rcases wm_run_ite h with ⟨-, h⟩ | ⟨-, h⟩ <;> try (cases h; simp; done)
  all_goals try head_whnf_at h
  case' det.inr =>
    obtain ⟨⟨we, rd⟩, s1, h1, h⟩ := wm_run_bind_ok h
    replace hw := (wRen_walk h1).wf hw nofun
    try head_whnf_at h
  all_goals
    obtain ⟨n, s2, h2, h⟩ := wm_run_bind_ok h
    good_at h with (fun r : WRes P => r.A = Std.HashSet.ofList [n])
      using fun (_ : Nat) (_ : P.Ident × WExpr P × P.Ident) => False
    · repeat' gstep
    obtain ⟨-, -, -, hb, hA⟩ := hq
    exact fun m hm => (by simpa [hA] using hm : n = m) ▸ key hw h2 hb

omit iL iW in
/-- A well-formed state with an empty live set is well formed. -/
private theorem wfSt_live (hw : WFSt st) : WFSt { st with live := {} } :=
  { hw with live_stamp := by simp }

/-- The facts of a walk from `st` to `st'` with result `r` about the names it assigns, registers
    and merges, for loop-free names `D`: an assigned name is a renaming recorded after the walk or
    a name of `D`; a registration is no renaming after the walk; a carried merge put by the walk
    targets such a name with a selector built from variables, literals and conditionals whose
    variables are names drawn by the walk and no renamings after it. -/
private structure NI (D : List P.Ident) (st : WSt P) (r : WRes P) (st' : WSt P) : Prop where
  A : ∀ n, r.A.contains n = true → TName D st' n
  regs : ∀ e ∈ r.regs.toList, st'.back[e]? = none
  car : ∀ k q, q ∈ st'.carries.getD k [] → q ∉ st.carries.getD k [] → TName D st' q.1 ∧
    ∃ c, q.2.1 = .ite c (.var q.2.2) (.var q.1) ∧ wsimple c ∧ ∀ y ∈ wvars c, FName st st' y

/-- The facts of a walk at depth `d` from `st` to `st'` with result `r`: an `Ext` step,
    registrations drawn by the walk and not dead after it (from a state with `DeadBelow`), an
    obligation only with a nonempty output, a snapshot registered after the walk and not before
    being a registration or dead (when `c` holds), each drawn name registered for at most one
    label, from a state with label depths at most `d` the carried-merge facts `CI`, those in
    front of each depth when `cC st` holds, and, from a well-formed state whose names of `D`
    (holding the identifiers `I` of the walked fragment) are avoided if they have the form of a
    fresh name, the name facts `NI`. -/
private structure WF (c : Prop) (cC : WSt P → Prop) (d : Nat) (I : List P.Ident) (st : WSt P)
    (r : WRes P) (st' : WSt P) : Prop where
  ext : Ext st st'
  regs : ∀ e ∈ r.regs.toList, NewIn st st' e
  obl : r.hasObl = true → r.out.isNil = false
  nodead : DeadBelow st → ∀ e ∈ r.regs.toList, st'.dead.contains e = false
  pendReg : c → ∀ l e, e ∈ st'.pending.getD l [] → e ∉ st.pending.getD l [] →
    e ∈ r.regs.toList ∨ st'.dead.contains e = true
  uniq : Uniq st st'
  ci : LabLe st d → CI (cC st) d st r st'
  ni : ∀ D, WFSt st → (∀ x ∈ D, AvoidedIfFresh st x) → (∀ x ∈ I, x ∈ D) → NI D st r st'

/-! ## Runs: normal ends, exit snapshots and reachable failures -/

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW in
/-- An outcome projected to an exit is an exit to the same label. -/
theorem outcome_proj_exit {σp σ1 : SemanticStore P} {o : Outcome P} {l : String}
    (h : o.proj σp = .exit l σ1) : ∃ σ', o = .exit l σ' := by cases o <;> grind [Outcome.proj]

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW in
/-- A body outcome that a block labelled `l'` turns into an exit to `l` is an exit to `l ≠ l'`. -/
theorem outcome_block_exit {σp σ1 : SemanticStore P} {o : Outcome P} {l l' : String}
    (h : o.block l' σp = .exit l σ1) : l ≠ l' ∧ ∃ σ', o = .exit l σ' := by
  cases o <;> grind [Outcome.block]

/-- What a walk at depth `d` from `st` to `st'` with result `a` gives for a run of the walked
    fragment ending with `o`: a normal end means the result does not always exit, and an exit to
    an enclosing block under a variable context has a snapshot registered for its label, in the
    result's registrations and not dead, and has the label's depth among the exit targets of the
    walk when the label depths of `st` are at most `d`. -/
private def AxEx (κ : RE P) (d : Nat) (st : WSt P) (a : WRes P) (st' : WSt P) (o : Outcome P) :
    Prop :=
  (∀ σ1, o = .normal σ1 → a.ax = false) ∧
  (∀ l σ1, o = .exit l σ1 → κ ≠ .top → (∃ t, st.labelDepth[l]? = some t) →
    ∃ e ∈ a.regs.toList, e ∈ st'.pending.getD l [] ∧ st'.dead.contains e = false) ∧
  (∀ l σ1 t, o = .exit l σ1 → κ ≠ .top → LabLe st d → st.labelDepth[l]? = some t → t ∈ a.tgt.elems)

omit iL in
/-- The walk of a command whose events claim a failure (an `assert` or a `cover`) has an
    obligation. -/
private theorem cmd_claim_hasObl {F : P.Factory} {σ σ' : SemanticStore P} {c : CmdExt P}
    {tr : List (Event P)} {t : AssertId P} {e : P.Expr} (he : EvalE F σ c σ' tr)
    (hc : Claim t e tr) (h : (wpStmt κ d f (.cmd c)).run st = .ok (a, st')) : a.hasObl = true := by
  obtain ⟨evs, ev, htr, -, hf⟩ := hc
  cases c with
  | call => exact he.elim
  | cmd c =>
    cases he
    all_goals first
      | (exfalso; cases evs <;> grind [FailsAt, List.cons_eq_cons, List.append_eq_nil_iff]; done)
      | (unfold wpStmt at h
         obtain ⟨⟨_, _⟩, _, -, h⟩ := wm_run_bind_ok h
         obtain ⟨_, _, -, h⟩ := wm_run_bind_ok h
         exact (Prod.mk.inj (Except.ok.inj h)).1 ▸ rfl)
/-- The facts of a statement walk from `st` to `st'` with result `a` about the runs of `s`: an
    obligation when a reach of `s` fails a target on a feasible path, and, walked with an obligation
    following it, the facts `AxEx` for every run of `s`. -/
private def AXs (κ : RE P) (d : Nat) (f : Bool) (s : PStmt P) (st : WSt P) (a : WRes P)
    (st' : WSt P) : Prop :=
  (∀ (F : P.Factory) σ tr (t : AssertId P) (e : P.Expr), DReachS F s σ tr → Claim t e tr →
    a.hasObl = true) ∧
  (f = true → ∀ (F : P.Factory) (X : Outcome P → Prop) σ evs o, DRunS F X s σ evs o →
    AxEx κ d st a st' o)

/-- The facts of a list walk from `st` to `st'` with result `r` about the runs of `ss`: an
    obligation when a reach of `ss` fails a target on a feasible path, and, walked with an
    obligation following it, the facts `AxEx` for every run of `ss`. -/
private def AXl (κ : RE P) (d : Nat) (fEnd : Bool) (ss : PStmts P) (st : WSt P) (r : WRes P)
    (st' : WSt P) : Prop :=
  (∀ (F : P.Factory) σ tr (t : AssertId P) (e : P.Expr), DReach F ss σ tr → Claim t e tr →
    r.hasObl = true) ∧
  (fEnd = true → ∀ (F : P.Factory) (X : Outcome P → Prop) σ evs o, DRun F X ss σ evs o →
    AxEx κ d st r st' o)

/-- The walk facts `WF c cC d I` and, from a state with `DeadBelow`, the fact `X`. -/
private structure WFA (c : Prop) (cC : WSt P → Prop) (d : Nat) (I : List P.Ident) (st : WSt P)
    (r : WRes P) (st' : WSt P) (X : Prop) : Prop extends WF c cC d I st r st' where
  ax : DeadBelow st → X

/-- Every successful run of `m` has the walk facts `WF c cC d I` and, from a state with
    `DeadBelow`, the facts `X`. -/
private def WFm (c : Prop) (cC : WSt P → Prop) (d : Nat) (I : List P.Ident)
    (X : WSt P → WRes P → WSt P → Prop) (m : WM P (WRes P)) : Prop :=
  ∀ st a st', m.run st = .ok (a, st') → WFA c cC d I st a st' (X st a st')

/-- A list walk under `κ` at depth `d` has the walk facts `WF` with the snapshot fact under a
    variable context and the carried merges in front of each depth when under `top` the state has
    no label, and the facts `AXl` from a state with `DeadBelow`. -/
private def WFl (κ : RE P) (d : Nat) (f : Bool) (ss : PStmts P) : Prop :=
  WFm (κ ≠ .top) (fun st => κ = .top → ∀ l : String, st.labelDepth[l]? = none) d
    (Block.idents ss) (AXl κ d f ss) (wpList κ d f ss)

/-- A list walk with the walk facts `WF` from a well-formed state whose names of `D` (holding the
    list's identifiers) are avoided if they have the form of a fresh name has the name facts `NI`,
    ends in such a state, and changes the back map only at drawn names. -/
private theorem WF.niStep {c : Prop} {cC : WSt P → Prop} {D : List P.Ident}
    (W : WF c cC d (Block.idents ss) st r st') (h : (wpList κ d f ss).run st = .ok (r, st'))
    (hw : WFSt st) (hav : ∀ x ∈ D, AvoidedIfFresh st x) (hD : ∀ x ∈ Block.idents ss, x ∈ D) :
    NI D st r st' ∧ WFSt st' ∧ (∀ x ∈ D, AvoidedIfFresh st' x) ∧ BackNew st st' :=
  let W' := wpList_walkOK h
  ⟨W.ni D hw hav hD, W'.wf hw fun x hx => hav x (hD x (stmtsInits_mem_idents x hx)),
    fun x hx b j he => W'.avoid ▸ hav x hx b j he, W'.back⟩

/-- A laid-out `ite` walk has the walk facts `WF` and, from a state with `DeadBelow`, the facts
    `AXs` of the `ite` walked with an obligation following it. -/
private theorem wpIteLaid_wf (κ : RE P) (d : Nat) (c : P.Expr)
    (tss ess : PStmts P) (IT : ∀ κ f, WFl κ d f tss) (IE : ∀ κ f, WFl κ d f ess) :
    WFm True (fun _ => True) d (Block.idents tss ++ Block.idents ess)
      (fun st a st' => ∀ md, AXs κ d true (.ite (.det c) tss ess md) st a st')
      (wpIteLaid κ d c tss ess) := fun st a st' h => by
  obtain ⟨κE, s4, E, s5, rT, T, s6, hE, hT, hκE, hx4, ⟨hd4, hp4, hc4⟩, hx6, ⟨hd6, hp6, hc6⟩, hax,
    -, hreg, hreg2, hob, hob2, htg, hA, hb6, hw4, hb4⟩ := wpIteLaid_run h
  have WE := IE κE true s4 E s5 hE
  have WT := IT (.name rT) true s5 T s6 hT
  have hκT : RE.name (P := P) rT ≠ .top := nofun
  have hl5 : ∀ l : String, s5.labelDepth[l]? = st.labelDepth[l]? := fun l =>
    (WE.ext.ld l).trans (hx4.ld l)
  have hX6 : Ext st s6 := (hx4.trans WE.ext).trans WT.ext
  refine ⟨⟨hX6.trans hx6, fun e he => ?_, hob, fun hD e he => ?_, fun _ l e he hn => ?_,
    ((Uniq.trans (hx4.trans WE.ext) WT.ext (Uniq.trans hx4 WE.ext (.of_pending hp4) WE.uniq)
      WT.uniq).trans hX6 hx6 (.of_pending hp6) :), fun hL => ?_, fun D hw hav hD => ?_⟩,
    fun hD md => ⟨fun F σ tr t _ hr hc => ?_, fun _ F X σ evs o hr => ?_⟩⟩
  · rcases hreg e he with h | h | ⟨h, -⟩
    · exact (WT.regs e h).widen (WE.ext.avoid.trans hx4.avoid) (hx4.trans WE.ext).next hx6.next
    · exact (WE.regs e h).widen hx4.avoid hx4.next (WT.ext.trans hx6).next
    · exact h.widen hX6.avoid hX6.next (Nat.le_refl _)
  · rw [hd6]
    rcases hreg e he with h | h | ⟨h, -⟩
    · exact WT.nodead ((hx4.trans WE.ext).deadBelow hD) e h
    · exact not_dead_after (WE.regs e h) (WE.nodead (hx4.deadBelow hD) e h) WT.ext
    · exact h.not_dead (hX6.deadBelow hD)
  · rw [hp6] at he
    rw [hd6]
    by_cases h1 : e ∈ s5.pending.getD l []
    · exact (WE.pendReg hκE l e h1 (hp4 ▸ hn)).imp (fun h => hreg2 e (.inr h)) (WT.ext.deadMono e)
    · exact (WT.pendReg hκT l e he h1).imp_left fun h => hreg2 e (.inl h)
  · have CE := WE.ci fun l t ht => hL l t ((hx4.ld l) ▸ ht)
    have CT := WT.ci fun l t ht => hL l t ((hl5 l) ▸ ht)
    have hmg := LeftistHeap.mem_merge T.tgt E.tgt
    have htT : ∀ t ∈ T.tgt.elems, ∃ l : String, st.labelDepth[l]? = some t := fun t ht =>
      (CT.tgt t ht).imp fun l h => (hl5 l) ▸ h
    have htE : ∀ t ∈ E.tgt.elems, ∃ l : String, st.labelDepth[l]? = some t := fun t ht =>
      (CE.tgt t ht).imp fun l h => (hx4.ld l) ▸ h
    have hk6 : ∀ k, (T.tgt.max? = some k ∨ E.tgt.max? = some k) → ∃ l : String,
        st.labelDepth[l]? = some k := fun k hm =>
      hm.elim (fun h => htT k (LeftistHeap.max?_mem h)) fun h => htE k (LeftistHeap.max?_mem h)
    refine ⟨htg ▸ LeftistHeap.ord_merge _ _ CT.ord CE.ord,
      fun t ht => ((hmg t).1 (htg ▸ ht)).elim (htT t) (htE t), fun _ k hk => ?_,
      fun k hk q hq => ?_⟩
    · obtain ⟨p6, h6', q6⟩ := hc6 k
      obtain ⟨pT, hT', qT⟩ := CT.pre nofun k hk
      obtain ⟨pE, hE', qE⟩ := CE.pre (fun h => absurd h hκE) k hk
      refine ⟨p6 ++ pT ++ pE, by rw [h6', hT', hE', hc4, List.append_assoc, List.append_assoc],
        fun q hq => ?_⟩
      rcases List.mem_append.1 hq with hq | hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨hm, hr, -⟩ := q6 q hq
        exact ⟨.inl hr, .inl (htg ▸ (hmg k).2 (hm.imp LeftistHeap.max?_mem LeftistHeap.max?_mem)),
          hk6 k hm⟩
      · obtain ⟨h1, h2, l', hl'⟩ := qT q hq
        exact ⟨h1.imp (fun h => hreg2 _ (.inl h)) (hd6 ▸ ·),
          h2.imp (fun h => htg ▸ (hmg k).2 (.inl h)) (hd6 ▸ ·), l', (hl5 l') ▸ hl'⟩
      · obtain ⟨h1, h2, l', hl'⟩ := qE q hq
        exact ⟨h1.imp (fun h => hreg2 _ (.inr h)) fun h => hd6 ▸ WT.ext.deadMono _ h,
          h2.imp (fun h => htg ▸ (hmg k).2 (.inr h)) fun h => hd6 ▸ WT.ext.deadMono _ h, l',
          (hx4.ld l') ▸ hl'⟩
    · obtain ⟨p6, h6', q6⟩ := hc6 k
      rw [h6'] at hq
      exact (List.mem_append.1 hq).elim (fun hq => (hk6 k (q6 q hq).1).elim fun l' hl' =>
        absurd (hL l' k hl') (by omega)) fun hq => hc4 k ▸ CE.high k hk q (CT.high k hk q hq)
  · have hav4 : ∀ x ∈ D, AvoidedIfFresh s4 x := fun x hx b j he => hx4.avoid ▸ hav x hx b j he
    obtain ⟨NE, w5, av5, b45⟩ :=
      WF.niStep WE.toWF hE (hw4 hw) hav4 fun x hx => hD x (List.mem_append_right _ hx)
    obtain ⟨NT, w6, -, b56⟩ :=
      WF.niStep WT.toWF hT w5 av5 fun x hx => hD x (List.mem_append_left _ hx)
    have hTA : ∀ n, T.A.contains n = true ∨ E.A.contains n = true → TName D st' n := fun n h =>
      (h.elim (NT.A n) fun h => (NE.A n h).keep w5 b56).keep w6 hb6
    refine ⟨fun n hn => hTA n (hA n hn), fun e he => ?_, fun k q h1 h2 => ?_⟩
    · rcases hreg e he with h | h | ⟨-, h⟩
      · exact (hb6.keepN (WT.regs e h)).trans (NT.regs e h)
      · exact (hb6.keepN ((WE.regs e h).widen rfl (Nat.le_refl _) WT.ext.next)).trans
          ((b56.keepN (WE.regs e h)).trans (NE.regs e h))
      · exact h w6
    · obtain ⟨p6, h6', q6⟩ := hc6 k
      rw [h6'] at h1
      rcases List.mem_append.1 h1 with hq | hq
      · obtain ⟨-, -, -, hAq, hc⟩ := q6 q hq
        obtain ⟨c, hc, hs, hy⟩ := hc w6
        exact ⟨hTA _ hAq, c, hc, hs, fun y hy' => (hy y hy').widen hX6.avoid hX6.next⟩
      · by_cases h5 : q ∈ s5.carries.getD k []
        · obtain ⟨hT, c, hc, hs, hy⟩ := NE.car k q h5 (hc4 k ▸ h2)
          exact ⟨(hT.keep w5 b56).keep w6 hb6, c, hc, hs, fun y hy' =>
            (((hy y hy').keep b56 WT.ext.next).keep hb6 hx6.next).widen hx4.avoid hx4.next⟩
        · obtain ⟨hT, c, hc, hs, hy⟩ := NT.car k q hq h5
          exact ⟨hT.keep w6 hb6, c, hc, hs, fun y hy' => ((hy y hy').keep hb6 hx6.next).widen
            (WE.ext.avoid.trans hx4.avoid) (hx4.trans WE.ext).next⟩
  · cases hr with
    | ite_true _ hr =>
      have h1 := (WT.ax ((hx4.trans WE.ext).deadBelow hD)).1 F σ tr t _ hr hc
      rw [hob2 (.inl (WT.obl h1)), h1, Bool.true_or]
    | ite_false _ hr =>
      have h1 := (WE.ax (hx4.deadBelow hD)).1 F σ tr t _ hr hc
      rw [hob2 (.inr (WE.obl h1)), h1, Bool.or_true]
  · have hL5 : LabLe st d → LabLe s5 d := fun hL l t h => hL l t ((hl5 l) ▸ h)
    have hmg := LeftistHeap.mem_merge T.tgt E.tgt
    cases hr with
    | ite_true _ hr hs =>
      rename_i o0 _
      obtain ⟨A1, A2, A3⟩ := (WT.ax ((hx4.trans WE.ext).deadBelow hD)).2 rfl F _ σ evs _ hr
      refine ⟨fun σ1 ho => ?_, fun l σ1 ho hk ht => ?_, fun l σ1 t ho hk hL ht => ?_⟩
      · cases o0 with
        | normal σ' => simp [hax, A1 σ' rfl]
        | exit => simp [Outcome.proj] at ho
      · obtain ⟨σ', rfl⟩ := outcome_proj_exit ho
        obtain ⟨e, he, hp, hd⟩ := A2 l σ' rfl hκT (ht.imp fun t h => (hl5 l).trans h)
        exact ⟨e, hreg2 e (.inl he), hp6 ▸ hp, hd6 ▸ hd⟩
      · obtain ⟨σ', rfl⟩ := outcome_proj_exit ho
        exact htg ▸ (hmg t).2 (.inl (A3 l σ' t rfl hκT (hL5 hL) ((hl5 l).trans ht)))
    | ite_false _ hr hs =>
      rename_i o0 _
      obtain ⟨A1, A2, A3⟩ := (WE.ax (hx4.deadBelow hD)).2 rfl F _ σ evs _ hr
      refine ⟨fun σ1 ho => ?_, fun l σ1 ho hk ht => ?_, fun l σ1 t ho hk hL ht => ?_⟩
      · cases o0 with
        | normal σ' => simp [hax, A1 σ' rfl]
        | exit => simp [Outcome.proj] at ho
      · obtain ⟨σ', rfl⟩ := outcome_proj_exit ho
        obtain ⟨e, he, hp, hd⟩ := A2 l σ' rfl hκE (ht.imp fun t h => (hx4.ld l).trans h)
        exact ⟨e, hreg2 e (.inr he), hp6 ▸ WT.ext.pend l e hp,
          hd6 ▸ not_dead_after (WE.regs e he) hd WT.ext⟩
      · obtain ⟨σ', rfl⟩ := outcome_proj_exit ho
        exact htg ▸ (hmg t).2 (.inr (A3 l σ' t rfl hκE (fun l t h => hL l t ((hx4.ld l) ▸ h))
          ((hx4.ld l).trans ht)))

/-- A real-branch walk has the walk facts `WF`, has from a state with `DeadBelow` an obligation
    when a reach of the `ite` fails a target on a feasible path, keeps the carried merges at the
    depths up to `d` and adds none at deeper depths. -/
private theorem wpIteReal_wf (κ : RE P) (d : Nat) (c : P.Expr)
    (tss ess : PStmts P) (IT : ∀ κ f, WFl κ d f tss)
    (IE : ∀ κ f, WFl κ d f ess) : ∀ st a st', (wpIteReal κ d c tss ess).run st = .ok (a, st') →
      WFA True (fun _ => True) d (Block.idents tss ++ Block.idents ess) st a st'
        (∀ md (F : P.Factory) σ tr (t : AssertId P) (e : P.Expr),
          DReachS F (.ite (.det c) tss ess md) σ tr → Claim t e tr → a.hasObl = true) ∧ ∀ k,
        (k ≤ d → st'.carries.getD k [] = st.carries.getD k []) ∧
          ∀ q ∈ st'.carries.getD k [], q ∈ st.carries.getD k [] := fun st a st' h => by
  obtain ⟨E, s2, T, s3, s6, hE, hT, hx, hd6, hl6, hp6, he6, ⟨hd', hp'⟩, -, -, hob, hob2, hreg,
    hcar, htg, hb, hA⟩ := wpIteReal_run h
  have WE := IE .top false _ _ _ hE
  have WT := IT .top false _ _ _ hT
  have arm : ∀ {s s' : WSt P} {r : WRes P} {X : Prop} {I : List P.Ident},
      WFA (RE.top (P := P) ≠ .top) (fun st => RE.top (P := P) = .top →
        ∀ l : String, st.labelDepth[l]? = none) d I s r s' X →
      (∀ l : String, s.labelDepth[l]? = none) → ∀ k, (k ≤ d → s'.carries.getD k [] =
        s.carries.getD k []) ∧ ∀ q ∈ s'.carries.getD k [], q ∈ s.carries.getD k [] := by
    intro s s' r X I W hl k
    have hci := W.ci fun l t h => by simp [hl] at h
    by_cases hk : k ≤ d
    · obtain ⟨pre, hpre, hq⟩ := hci.pre (fun _ => hl) k hk
      obtain rfl : pre = [] := List.eq_nil_iff_forall_not_mem.2 fun q hq' =>
        (hq q hq').2.2.elim fun l h => nomatch (hl l).symm.trans h
      exact ⟨fun _ => hpre, fun q h => by simpa [hpre] using h⟩
    · exact ⟨fun h => absurd h hk, hci.high k (by omega)⟩
  have hCE := arm WE fun l => by simp
  have hCT := arm WT fun l => by simp [WE.ext.ld l]
  have hC : ∀ k, (k ≤ d → st'.carries.getD k [] = st.carries.getD k []) ∧
      ∀ q ∈ st'.carries.getD k [], q ∈ st.carries.getD k [] := fun k => by
    rw [hcar k]
    exact ⟨fun hk => ((hCT k).1 hk).trans ((hCE k).1 hk), fun q hq => (hCE k).2 q ((hCT k).2 q hq)⟩
  have hE1 : ExtD st { st with live := {}, labelDepth := {}, pending := {} } :=
    ExtD.of_eq rfl (Nat.le_refl _) rfl
  have hE2 : ExtD st s3 := (hE1.trans WE.ext.toExtD).trans
    ((ExtD.of_eq rfl (Nat.le_refl _) rfl : ExtD s2 { s2 with live := {} }).trans WT.ext.toExtD)
  have hX : Ext st st' := Ext.of_extD (hE2.trans hx) hl6 hp6 he6
  refine ⟨⟨⟨hX, ?_, hob2, ?_, fun _ l e h1 h2 => absurd (hp6 ▸ hp' ▸ h1) h2,
    Uniq.of_pending (hp'.trans hp6), fun _ => ?_, ?_⟩, fun hD => ?_⟩, hC⟩
  · intro e he
    have hY : ExtD s3 st' := hx.trans he6.toExtD
    exact (hreg e he).elim (fun h => (WT.regs e h).widen WE.ext.avoid WE.ext.next hY.next)
      fun h => (WE.regs e h).widen rfl (Nat.le_refl _) ((WT.ext.toExtD.trans hY).next)
  · intro hD e he
    rw [hd', hd6]
    exact (hreg e he).elim (WT.nodead (WE.ext.deadBelow hD) e)
      fun h => not_dead_after (s1 := { s2 with live := {} }) (WE.regs e h) (WE.nodead hD e h) WT.ext
  · exact ⟨by rw [htg]; trivial, fun _ h' => by simp [htg, LeftistHeap.elems] at h',
      fun _ k hk => ⟨[], by rw [(hC k).1 hk, List.nil_append], nofun⟩, fun k _ => (hC k).2⟩
  · intro D hw hav hD
    obtain ⟨nE, wE2, avE, bE⟩ := WF.niStep WE.toWF hE { hw with
      pending_fresh := fun _ _ h => by simp at h, live_stamp := fun _ _ h => by simp at h }
      hav fun x hx => hD x (List.mem_append_right _ hx)
    obtain ⟨nT, wT3, -, bT⟩ := WF.niStep WT.toWF hT (wfSt_live wE2) avE
      fun x hx => hD x (List.mem_append_left _ hx)
    refine ⟨fun n hn => ?_, fun e he => ?_, fun k q h1 h2 => absurd ((hC k).2 q h1) h2⟩
    · exact (hA n hn).elim (fun h => (nT.A n h).keep wT3 hb)
        fun h => ((nE.A n h).keep (wfSt_live wE2) bT).keep wT3 hb
    · exact (hreg e he).elim (fun h => (hb.keepN (WT.regs e h)).trans (nT.regs e h))
        fun h => (hb.keepN ((WE.regs e h).widen rfl (Nat.le_refl _) WT.ext.next)).trans
          ((bT.keepN (WE.regs e h)).trans (nE.regs e h))
  · intro md F σ tr t _ hr hc
    cases hr with
    | ite_true _ hr => rw [hob, (WT.ax (WE.ext.deadBelow hD)).1 F σ tr t _ hr hc, Bool.true_or]
    | ite_false _ hr => rw [hob, (WE.ax hD).1 F σ tr t _ hr hc, Bool.or_true]

/-- A list walk of `s :: rest` has the walk facts `WF` and the facts `AXl` when the walk of `rest`
    and the walks of `s` (with any obligation bit) have theirs. -/
private theorem wpList_cons_wf {rest : PStmts P} (IR : WFl κ d fEnd rest)
    (IS : ∀ f, WFm True (fun _ => True) d (Stmt.idents s) (AXs κ d f s) (wpStmt κ d f s)) :
    WFl κ d fEnd (s :: rest) := fun st R st' h => by
  obtain ⟨r, st1, a, st2, hr, hs, hc⟩ := wpList_run_cons h
  have WR := IR st r st1 hr
  have WS := IS _ st1 a st2 hs
  have hRn : ∀ e ∈ r.regs.toList, NewIn st st2 e := fun e he =>
    (WR.regs e he).widen rfl (Nat.le_refl _) WS.ext.next
  have hAn : ∀ e ∈ a.regs.toList, NewIn st st2 e := fun e he =>
    (WS.regs e he).widen WR.ext.avoid WR.ext.next (Nat.le_refl _)
  have hLd : LabLe st d → LabLe st1 d := fun hL l t ht => hL l t ((WR.ext.ld l) ▸ ht)
  have hfT : κ ≠ .top → fEnd = true → (r.hasObl || (fEnd && !r.drop)) = true := fun hk hf => by
    simp [hf, Bool.eq_false_iff.2 fun h => hk (wpList_drop hr h)]
  have hreach : DeadBelow st → ∀ F σ tr (t : AssertId P) (e : P.Expr), DReach F (s :: rest) σ tr →
      Claim t e tr → a.hasObl = true ∨ r.hasObl = true ∧ a.ax = false ∧
        ∃ σ evs σ1, DRunS F (fun _ => True) s σ evs (.normal σ1) := by
    intro hD F σ tr t _ hrc hcl
    cases hrc with
    | here h' => exact .inl ((WS.ax (WR.ext.deadBelow hD)).1 F σ _ t _ h' hcl)
    | later h1 h2 =>
      rename_i evs1 σ1 evs2
      by_cases he : evs2 = []
      · subst he
        rw [List.append_nil] at hcl
        exact .inl ((WS.ax (WR.ext.deadBelow hD)).1 F σ _ t _
          (h1.toReachS (hcl.elim fun _ ⟨_, he, _⟩ => by simp [he])) hcl)
      · have hro := (WR.ax hD).1 F σ1 evs2 t _ h2 (claim_split he hcl).2
        exact .inr ⟨hro, ((WS.ax (WR.ext.deadBelow hD)).2 (by simp [hro]) F _ σ _ _ h1).1 _ rfl,
          _, _, _, h1⟩
  have hrun : DeadBelow st → fEnd = true → ∀ F X σ evs o, DRun F X (s :: rest) σ evs o →
      (AxEx κ d st r st1 o ∧ ((∃ σ1, o = .normal σ1) ∨ κ ≠ .top → a.ax = false)) ∨
      ((∀ σ1, o ≠ .normal σ1) ∧ (κ ≠ .top → AxEx κ d st1 a st2 o)) := by
    intro hD hf F X σ evs o hrn
    have hD1 := WR.ext.deadBelow hD
    cases hrn with
    | cons_normal h1 h2 =>
      refine .inl ⟨(WR.ax hD).2 hf F X _ _ _ h2, fun ho => ?_⟩
      have hf' : (r.hasObl || (fEnd && !r.drop)) = true := ho.elim (fun ⟨_, he⟩ => by
        simp [hf, Bool.eq_false_iff.2 fun h => (wpList_drop_run hr h).2 (he ▸ h2)]) (hfT · hf)
      exact ((WS.ax hD1).2 hf' F _ _ _ _ h1).1 _ rfl
    | cons_exit h1 =>
      exact .inr ⟨fun _ h => (nomatch h), fun hk => (WS.ax hD1).2 (hfT hk hf) F _ _ _ _ h1⟩
  have hN : ∀ {R' : WRes P}, (∀ n, R'.A.contains n = true → a.A.contains n = true ∨
      r.A.contains n = true) → (∀ e ∈ R'.regs.toList, e ∈ a.regs.toList ∨ e ∈ r.regs.toList) →
      ∀ D, WFSt st → (∀ x ∈ D, AvoidedIfFresh st x) →
        (∀ x ∈ Block.idents (s :: rest), x ∈ D) → NI D st R' st2 := by
    intro R' hA hg D hw hav hD
    obtain ⟨NR, w1, av1, -⟩ :=
      WF.niStep WR.toWF hr hw hav fun x hx => hD x (List.mem_append_right _ hx)
    have NS := WS.ni D w1 av1 fun x hx => hD x (List.mem_append_left _ hx)
    have b2 : BackNew st1 st2 := (wpStmt_walkOK hs).back
    refine ⟨fun n hn => (hA n hn).elim (NS.A n) fun h => (NR.A n h).keep w1 b2,
      fun e he => (hg e he).elim (NS.regs e) fun h =>
        (b2.keepN (WR.regs e h)).trans (NR.regs e h),
      fun k q h1 h2 => ?_⟩
    by_cases hq : q ∈ st1.carries.getD k []
    · obtain ⟨hT, c, hc, hs, hy⟩ := NR.car k q hq h2
      exact ⟨hT.keep w1 b2, c, hc, hs, fun y hy' => (hy y hy').keep b2 WS.ext.next⟩
    · obtain ⟨hT, c, hc, hs, hy⟩ := NS.car k q h1 hq
      exact ⟨hT, c, hc, hs, fun y hy' => (hy y hy').widen WR.ext.avoid WR.ext.next⟩
  have hCI : LabLe st d → ∀ {R' : WRes P} {sd : Std.HashSet P.Ident}, R'.tgt.Ord →
      (∀ t ∈ R'.tgt.elems, t ∈ a.tgt.elems ∨ t ∈ r.tgt.elems) →
      (∀ e, st2.dead.contains e = true → sd.contains e = true) →
      (∀ e ∈ a.regs.toList, e ∈ R'.regs.toList) → (∀ k ∈ a.tgt.elems, k ∈ R'.tgt.elems) →
      (∀ (q : P.Ident) k, (κ = .top → ∀ l : String, st.labelDepth[l]? = none) →
        (∃ l : String, st.labelDepth[l]? = some k) →
        (q ∈ r.regs.toList ∨ st1.dead.contains q = true) →
        (k ∈ r.tgt.elems ∨ st1.dead.contains q = true) →
        (q ∈ R'.regs.toList ∨ sd.contains q = true) ∧ (k ∈ R'.tgt.elems ∨ sd.contains q = true)) →
      CI (κ = .top → ∀ l : String, st.labelDepth[l]? = none) d st R' { st2 with dead := sd } := by
    intro hL R' sd ho ht hsd hga hta hqr
    have CS := WS.ci (hLd hL)
    have CR := WR.ci hL
    refine ⟨ho, fun t h => (ht t h).elim (fun h => (CS.tgt t h).imp fun l h => (WR.ext.ld l) ▸ h)
      (CR.tgt t), fun hc k hk => ?_, fun k hk q hq => CR.high k hk q (CS.high k hk q hq)⟩
    obtain ⟨pS, hS, qS⟩ := CS.pre trivial k hk
    obtain ⟨pR, hR, qR⟩ := CR.pre hc k hk
    refine ⟨pS ++ pR, by rw [hS, hR, List.append_assoc], fun q hq => ?_⟩
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨h1, h2, l', hl'⟩ := qS q hq
      exact ⟨h1.imp (hga _) (hsd _), h2.imp (hta k) (hsd _), l', (WR.ext.ld l').symm.trans hl'⟩
    · exact (qR q hq).elim fun h1 ⟨h2, hl'⟩ => (hqr _ k hc hl' h1 h2).imp id fun h => ⟨h, hl'⟩
  rcases hc with ⟨hdr, rfl, rfl⟩ | ⟨hdr, hax, rfl, rfl⟩ | ⟨hdr, hax, rfl, rfl⟩
  · obtain ⟨rfl, l, md, rfl⟩ := wpStmt_drop hs hdr
    refine ⟨⟨WR.ext.trans WS.ext, hAn, WS.obl, fun hD => WS.nodead (WR.ext.deadBelow hD),
      fun h => absurd rfl h, Uniq.trans WR.ext WS.ext WR.uniq WS.uniq, fun hL => ?_,
      hN (fun n h => .inl h) (fun e h => .inl h)⟩,
      fun hD => ⟨fun F σ tr t _ hrc hcl => ?_, fun hf F X σ evs o hrn => ?_⟩⟩
    · exact hCI hL (WS.ci (hLd hL)).ord (fun t h => .inl h) (fun _ h => h) (fun _ h => h)
        (fun _ h => h) fun _ _ hc ⟨l, hl⟩ => by simp [hc rfl] at hl
    · exact (hreach hD F σ tr t _ hrc hcl).elim id fun ⟨_, _, _, _, _, h⟩ => nomatch h
    · refine ⟨fun σ1 ho => ?_, fun _ _ _ hk => absurd rfl hk, fun _ _ _ _ hk => absurd rfl hk⟩
      exact (hrun hD hf F X σ evs o hrn).elim (fun h => h.2 (.inl ⟨σ1, ho⟩))
        fun h => absurd ho (h.1 σ1)
  · have hdis : ∀ e ∈ a.regs.toList, e ∉ r.regs.toList := fun e he hr' =>
      NewIn.disj (WR.regs e hr') (WS.regs e he) rfl
    have hdd : ∀ e, st2.dead.contains e = true ∨ e ∈ r.regs.toList →
        (r.regs.toList.foldl (·.insert ·) st2.dead).contains e = true := fun e h =>
      (foldl_insert_contains _ _ _).2 h
    refine ⟨⟨Ext.markDead (WR.ext.trans WS.ext) hRn, hAn, WS.obl,
      fun hD e he => markDead_false (WS.nodead (WR.ext.deadBelow hD) e he) (hdis e he),
      fun hk l e he hn => ?_, (Uniq.trans WR.ext WS.ext WR.uniq WS.uniq :), fun hL => ?_,
      fun D hw hav hD => (fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩)
        (hN (fun n h => .inl h) (fun e h => .inl h) D hw hav hD)⟩,
      fun hD => ⟨fun F σ tr t _ hrc hcl => ?_, fun hf F X σ evs o hrn => ?_⟩⟩
    · by_cases h1 : e ∈ st1.pending.getD l []
      · exact .inr (hdd e ((WR.pendReg hk l e h1 hn).imp_right (WS.ext.deadMono e)).symm)
      · exact (WS.pendReg trivial l e he h1).imp_right fun h => hdd e (.inl h)
    · exact hCI hL (WS.ci (hLd hL)).ord (fun t h => .inl h) (fun e h => hdd e (.inl h))
        (fun _ h => h) (fun _ h => h) fun q _ _ _ h1 _ =>
        (fun h => ⟨.inr h, .inr h⟩) (hdd q (h1.imp_right (WS.ext.deadMono q)).symm)
    · exact (hreach hD F σ tr t _ hrc hcl).elim id fun ⟨_, h, _⟩ => by simp [hax] at h
    · rcases hrun hD hf F X σ evs o hrn with ⟨-, h⟩ | ⟨hn, AS⟩
      · have hF := fun x => Bool.false_ne_true ((h x).symm.trans hax)
        exact ⟨fun σ1 ho => (hF (.inl ⟨σ1, ho⟩)).elim, fun _ _ _ hk => (hF (.inr hk)).elim,
          fun _ _ _ _ hk => (hF (.inr hk)).elim⟩
      · refine ⟨fun σ1 ho => absurd ho (hn σ1), fun l σ1 ho hk ht => ?_,
          fun l σ1 t ho hk hL ht => (AS hk).2.2 l σ1 t ho hk (hLd hL) ((WR.ext.ld l).trans ht)⟩
        obtain ⟨e, he, hp, hd⟩ := (AS hk).2.1 l σ1 ho hk (ht.imp fun t h => (WR.ext.ld l).trans h)
        exact ⟨e, he, hp, markDead_false hd (hdis e he)⟩
  · have hreg : ∀ e, e ∈ (a.combine r).regs.toList ↔ e ∈ a.regs.toList ∨ e ∈ r.regs.toList :=
      fun e => by simp [WRes.combine, Rope.toList_app]
    have hmg := LeftistHeap.mem_merge a.tgt r.tgt
    refine ⟨⟨WR.ext.trans WS.ext, fun e he => ((hreg e).1 he).elim (hAn e) (hRn e),
      fun h' => ?_, fun hD e he => ((hreg e).1 he).elim (WS.nodead (WR.ext.deadBelow hD) e)
        fun h => not_dead_after (WR.regs e h) (WR.nodead hD e h) WS.ext,
      fun hk l e he hn => ?_, Uniq.trans WR.ext WS.ext WR.uniq WS.uniq, fun hL => ?_,
      hN (fun n h => by simpa [WRes.combine, unionSet_contains] using h) fun e h => (hreg e).1 h⟩,
      fun hD => ⟨fun F σ tr t _ hrc hcl => ?_, fun hf F X σ evs o hrn => ?_⟩⟩
    · simp only [WRes.combine, Bool.or_eq_true, Rope.isNil_app', Bool.and_eq_false_iff] at h' ⊢
      exact h'.imp WS.obl WR.obl
    · by_cases h1 : e ∈ st1.pending.getD l []
      · exact (WR.pendReg hk l e h1 hn).imp (fun h => (hreg e).2 (.inr h)) (WS.ext.deadMono e)
      · exact (WS.pendReg trivial l e he h1).imp_left fun h => (hreg e).2 (.inl h)
    · exact hCI hL (LeftistHeap.ord_merge _ _ (WS.ci (hLd hL)).ord (WR.ci hL).ord)
        (fun t h => (hmg t).1 h) (fun _ h => h) (fun e h => (hreg e).2 (.inl h))
        (fun k h => (hmg k).2 (.inl h)) fun _ k _ _ h1 h2 =>
        ⟨h1.imp (fun h => (hreg _).2 (.inr h)) (WS.ext.deadMono _),
          h2.imp (fun h => (hmg k).2 (.inr h)) (WS.ext.deadMono _)⟩
    · rcases hreach hD F σ tr t _ hrc hcl with h | ⟨h, -⟩
      all_goals simp [WRes.combine, h]
    · rcases hrun hD hf F X σ evs o hrn with ⟨⟨AR1, AR2, AR3⟩, h⟩ | ⟨hn, AS⟩
      · refine ⟨fun σ1 ho => ?_, fun l σ1 ho hk ht => ?_, fun l σ1 t ho hk hL ht => ?_⟩
        · simp [WRes.combine, h (.inl ⟨σ1, ho⟩), AR1 σ1 ho]
        · exact (AR2 l σ1 ho hk ht).imp fun e ⟨he, hp, hd⟩ =>
            ⟨(hreg e).2 (.inr he), WS.ext.pend l e hp, not_dead_after (WR.regs e he) hd WS.ext⟩
        · exact (hmg t).2 (.inr (AR3 l σ1 t ho hk hL ht))
      · refine ⟨fun σ1 ho => absurd ho (hn σ1), fun l σ1 ho hk ht => ?_,
          fun l σ1 t ho hk hL ht => ?_⟩
        · exact ((AS hk).2.1 l σ1 ho hk (ht.imp fun t h => (WR.ext.ld l).trans h)).imp
            fun e ⟨he, hp, hd⟩ => ⟨(hreg e).2 (.inl he), hp, hd⟩
        · exact (hmg t).2 (.inl ((AS hk).2.2 l σ1 t ho hk (hLd hL) ((WR.ext.ld l).trans ht)))

/-- A block walk has the walk facts `WF` and, from a state with `DeadBelow`, the facts `AXs` when
    the walks of its body under every reach context have the walk facts `WF`. -/
private theorem wpStmt_block_wf {l : String} {body : PStmts P} {md : MetaData P}
    (IB : ∀ κB, WFl κB (d + 1) f body) : WFm True (fun _ => True) d (Stmt.idents (.block l body md))
      (AXs κ d f (.block l body md)) (wpStmt κ d f (.block l body md)) := fun st a st' h => by
  obtain ⟨κB, s0, B, st1, hB, hκB, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hob, hrg, -, hax,
    hout, hc0, hc1, htg, hbk, hA, hw0⟩ := wpStmt_block_run h
  have W := IB κB s0 B st1 hB
  have hp0 := fun l' (hl : l ≠ l') => (h4 l').trans (ite_eq_right hl)
  have hld0 := fun l' (hl : l ≠ l') => (h3 l').trans (ite_eq_right hl)
  have hc' := fun k (hk : d + 1 ≠ k) => (hc1 k).trans (ite_eq_right hk)
  have hc0' := fun k (hk : d + 1 ≠ k) => (hc0 k).trans (ite_eq_right hk)
  have hl1 : ∀ {l' t}, l = l' → s0.labelDepth[l']? = some t → t = d + 1 := fun hl h =>
    (Option.some.inj ((ite_eq_left hl ▸ h3 _).symm.trans h)).symm
  have hL0 : LabLe st d → LabLe s0 (d + 1) := fun hL l' t ht =>
    (Classical.em (l = l')).elim (fun hl => Nat.le_of_eq (hl1 hl ht))
      fun hl => Nat.le_succ_of_le (hL l' t (hld0 l' hl ▸ ht))
  have hD0 : DeadBelow st → DeadBelow s0 := fun hD => hD.of_le h5 h2
  refine ⟨⟨block_ext h1 h2 h3 h4 h5 W.ext h6 h7 h8 h9 h10,
    fun e he => (W.regs e (hrg ▸ he)).widen h1 h2 (h7 ▸ Nat.le_refl _),
    fun h' => hout (W.obl (hob ▸ h')), fun hD e he => h8 ▸ W.nodead (hD0 hD) e (hrg ▸ he),
    fun _ l' e he hn => ?_, fun hP e hn l1 l2 he1 he2 => ?_, fun hL => ?_,
    fun D hw hav hI => ?_⟩, fun hD => ⟨fun F σ tr t _ hr hc => ?_, fun hf F X σ evs o hr => ?_⟩⟩
  · rw [h10] at he
    split at he
    · exact absurd he hn
    exact hrg ▸ h8 ▸ W.pendReg hκB l' e he (by rwa [hp0 l' ‹_›])
  · have hnot := hn.not_pending hP
    rw [h10] at he1 he2
    split at he1
    · exact absurd he1 (hnot _)
    split at he2
    · exact absurd he2 (hnot _)
    have hP0 : PendBelow s0 := fun l' e he b j hb => (Classical.em (l = l')).elim
      (fun hl => by simp [h4, hl] at he)
      fun hl => Nat.lt_of_lt_of_le (hP l' e (hp0 l' hl ▸ he) b j hb) h2
    refine W.uniq hP0 e ((W.ext.pendNew l1 e he1).resolve_left ?_) l1 l2 he1 he2
    rw [hp0 l1 ‹_›]
    exact hnot l1
  · have C := W.ci (hL0 hL)
    obtain ⟨ho, hsub, hlt⟩ := LeftistHeap.popEq_facts (d + 1) B.tgt C.ord
    have hlt := hlt fun t ht => (C.tgt t ht).elim fun l' hl' => hL0 hL l' t hl'
    refine ⟨htg ▸ ho, fun t ht => ?_, fun _ k hk => ?_, fun k hk q hq => ?_⟩
    · exact (C.tgt t (hsub t (htg ▸ ht))).imp fun l' hl' =>
        hld0 l' (fun hl => absurd (hlt t (htg ▸ ht)) (hl1 hl hl' ▸ Nat.lt_irrefl _)) ▸ hl'
    · obtain ⟨pre, hpre, hq⟩ := C.pre (fun h => absurd h hκB) k (by omega)
      refine ⟨pre, by rw [hc' k (by omega), hpre, hc0' k (by omega)], fun q hq' => ?_⟩
      obtain ⟨h1', h2', l', hl'⟩ := hq q hq'
      exact ⟨hrg ▸ h8 ▸ h1', h8 ▸ htg ▸ h2'.imp_left fun h => LeftistHeap.mem_popEq _ _ _ h
        (by omega), l', hld0 l' (fun hl => absurd (hl1 hl hl') (by omega)) ▸ hl'⟩
    · exact (Classical.em (d + 1 = k)).elim (fun hk1 => by simp [hk1, hc1] at hq) fun hk1 =>
        hc0' k hk1 ▸ C.high k (by omega) q (hc' k hk1 ▸ hq)
  · have N := W.ni D (hw0 hw) (fun x hx b j he => h1 ▸ hav x hx b j he) hI
    have hT : ∀ n, TName D st1 n → TName D st' n := fun n =>
      Or.imp_left fun ⟨x, hx⟩ => ⟨x, hbk ▸ hx⟩
    refine ⟨fun n hn => ?_, fun e he => hbk ▸ N.regs e (hrg ▸ he), fun k q h1' h2' => ?_⟩
    · exact (hA n hn).elim (fun h' => hT n (N.A n h')) fun ⟨q, hq, he⟩ =>
        he ▸ hT _ (N.car (d + 1) q hq (by simp [hc0])).1
    · have hk1 : d + 1 ≠ k := fun hk => by simp [← hk, hc1] at h1'
      obtain ⟨hq1, c, hc, hs, hy⟩ := N.car k q (hc' k hk1 ▸ h1') (hc0' k hk1 ▸ h2')
      exact ⟨hT _ hq1, c, hc, hs,
        fun y hy' => ((hy y hy').widen h1 h2).keep (BackNew.of_eq hbk) (h7 ▸ Nat.le_refl _)⟩
  · cases hr with
    | block hr => exact hob ▸ (W.ax (hD0 hD)).1 F σ tr t _ hr hc
  · cases hr with
    | block hr => ?_
    rename_i o
    obtain ⟨An, Ae, At⟩ := (W.ax (hD0 hD)).2 hf F _ σ evs _ hr
    refine ⟨fun σ1 ho => ?_, fun l' σ1 ho hk ht => ?_, fun l' σ1 t ho hk hL ht => ?_⟩
    · rw [hax]
      cases o with
      | normal σ' => simp [An σ' rfl]
      | exit l'' σ'' =>
        simp only [Outcome.block] at ho
        split at ho
        · subst l''
          obtain ⟨e, he, hp, hd⟩ := Ae l σ'' rfl hκB ⟨d + 1, by simp [h3]⟩
          simpa using fun _ => ⟨e, hp, by simp [Std.HashSet.mem_iff_contains, hd]⟩
        · cases ho
    · obtain ⟨hne, σ', rfl⟩ := outcome_block_exit ho
      obtain ⟨e, he, hp, hd⟩ := Ae l' σ' rfl hκB (ht.imp fun t h => (hld0 l' hne.symm).trans h)
      exact ⟨e, hrg ▸ he, by rw [h10, ite_eq_right hne.symm]; exact hp, h8 ▸ hd⟩
    · obtain ⟨hne, σ', rfl⟩ := outcome_block_exit ho
      rw [htg]
      exact LeftistHeap.mem_popEq _ _ _ (At l' σ' t rfl hκB (hL0 hL) ((hld0 l' hne.symm).trans ht))
        (by have := hL l' t ht; omega)

omit iL in
mutual
/-- A statement walk has the walk facts `WF` and, from a state with `DeadBelow`, the facts
    `AXs`. -/
private theorem wpStmt_wf [LawfulHasIdent P] (κ : RE P) (d : Nat) (f : Bool) : ∀ s : PStmt P,
    WFm True (fun _ => True) d (Stmt.idents s) (AXs κ d f s) (wpStmt κ d f s)
  | .exit l md => fun st a st' h => by
    obtain ⟨hx, hr, ho, -, -, hs, hd, hp, hc, hb, hA, hord, htg, hm⟩ := wpStmt_exit_run h
    refine ⟨⟨hx, hr, fun h' => by simp [ho] at h', fun hD e he => hd ▸ (hr e he).not_dead hD,
      fun _ l e h1 h2 => .inl (hp l e h1 h2).2, fun hP e hn l1 l2 h1 h2 => ?_,
      fun _ => ⟨hord, htg, fun _ k _ => ⟨[], by rw [hc, List.nil_append], nofun⟩,
        fun k _ q hq => hc ▸ hq⟩,
      fun D hw _ _ => ⟨fun n hn => by simp [hA n] at hn, fun e he => ?_,
        fun k q h1 h2 => absurd (hc ▸ h1) h2⟩⟩, fun hD => ⟨nofun, fun hf F X σ evs o hr => ?_⟩⟩
    · exact (hp l1 e h1 (hn.not_pending hP l1)).1.trans (hp l2 e h2 (hn.not_pending hP l2)).1.symm
    · exact (hr e he).elim fun b ⟨j, he', _, hj, _⟩ => hb ▸ he' ▸ back_none hw hj
    · cases hr
      refine ⟨fun _ h => (nomatch h), fun l' σ1 h hk ht => ?_, fun l' σ1 t h hk _ ht => ?_⟩
      all_goals cases h
      · exact (hs hk hf ht).elim fun e ⟨he, hn, hp⟩ => ⟨e, he, hp, hd ▸ hn.not_dead hD⟩
      · exact hm hk t ht
  | .block l body md => wpStmt_block_wf (wpList_wf · (d + 1) f body)
  | .ite (.det c) tss ess md => fun st a st' h => by
    have hI : ∀ x ∈ Block.idents tss ++ Block.idents ess,
        x ∈ Stmt.idents (.ite (.det c) tss ess md) := fun x hx => by grind [Stmt.idents]
    have IT := fun κ f => wpList_wf κ d f tss
    have IE := fun κ f => wpList_wf κ d f ess
    cases f <;> simp only [wpStmt, Bool.false_eq_true, ite_false, ite_true] at h
    · have W := (wpIteReal_wf κ d c tss ess IT IE st a st' h).1
      exact ⟨{ W.toWF with ni := fun D hw hav hD => W.ni D hw hav fun x hx => hD x (hI x hx) },
        fun hD => ⟨W.ax hD md, nofun⟩⟩
    · have W := wpIteLaid_wf κ d c tss ess IT IE st a st' h
      exact ⟨{ W.toWF with ni := fun D hw hav hD => W.ni D hw hav fun x hx => hD x (hI x hx) },
        fun hD => W.ax hD md⟩
  | .cmd c | .typeDecl .. | .loop .. | .ite .nondet .. => fun st a st' h => by
    obtain ⟨hx, ⟨-, hp⟩, hc, -, hrg, -, hax, hob, htg, hA⟩ :=
      good_use h (wpStmt_cmd_good κ d f _ nofun nofun nofun)
    have hr0 : ∀ e, e ∈ a.regs.toList → False := fun e he => by simp [hrg, Rope.toList_nil] at he
    refine ⟨⟨hx, fun e he => (hr0 e he).elim, fun h' => hob.resolve_left (by simp [h']),
      fun _ e he => (hr0 e he).elim,
      fun _ l e h1 h2 => absurd (hp ▸ h1) h2, Uniq.of_pending hp, fun _ => CI.of_eq htg hc.noCP,
      fun D hw _ hI => ⟨fun n hn => ?_, fun e he => (hr0 e he).elim,
        fun k q h1 h2 => absurd (hc.noCP k ▸ h1) h2⟩⟩,
      fun _ => ⟨fun F σ tr t _ hr hc => ?_, fun _ F X σ evs o hr => ?_⟩⟩
    · obtain ⟨x, e, md, ⟨⟩⟩ := hA n hn
      all_goals
        exact (wpStmt_set_A h hw n hn).imp_right fun | rfl => hI _ (by cases e <;> exact .head _)
    · cases hr <;> exact cmd_claim_hasObl ‹_› hc h
    · cases hr <;> exact ⟨fun _ _ => hax, fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩
  termination_by structural s => s

/-- A list walk has the walk facts `WF`, the snapshot fact under a variable context and the
    carried merges in front of each depth when under `top` the state has no label. -/
private theorem wpList_wf [LawfulHasIdent P] (κ : RE P) (d : Nat) (fEnd : Bool) :
    ∀ ss : PStmts P, WFl κ d fEnd ss
  | [] => fun st a st' h => by
    unfold wpList at h
    cases h
    have hr0 : ∀ e, e ∈ (({} : WRes P)).regs.toList → False := fun e he => by
      simp [Rope.toList_nil] at he
    refine ⟨⟨Ext.refl _, fun e he => (hr0 e he).elim, nofun, fun _ e he => (hr0 e he).elim,
      fun _ _ _ h1 h2 => absurd h1 h2, Uniq.of_pending rfl, fun _ => CI.of_eq rfl fun _ => rfl,
      fun _ _ _ _ => ⟨fun _ h => by simp at h, fun e he => (hr0 e he).elim,
        fun _ _ h1 h2 => absurd h1 h2⟩⟩,
      fun _ => ⟨fun _ _ _ _ _ h => (nomatch h), fun _ F X σ evs o hr => ?_⟩⟩
    cases hr
    exact ⟨fun _ _ => rfl, fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩
  | s :: rest => wpList_cons_wf (wpList_wf κ d fEnd rest) (wpStmt_wf κ d · s)
  termination_by structural ss => ss
end

/-! ## The facts as stated for the users -/

omit iL iW in
/-- A name drawn between two states, spelled out. -/
private theorem NewIn.spec {e : P.Ident} (h : NewIn st st' e) :
    ∃ b j, e = freshName b j ∧ st.next ≤ j ∧ j < st'.next ∧ st.avoid.contains e = false :=
  h.imp fun _ ⟨j, h1, h2, h3, h4⟩ => ⟨j, h1, h3, h4, h2⟩

omit iL iW in
/-- A walk state with no dead name has `DeadBelow`. -/
theorem deadBelow_of_dead_empty (h : st.dead = {}) : DeadBelow st := fun _ _ hj => by simp [h] at hj

/-- A list walk keeps `DeadBelow`. -/
theorem wpList_deadBelow (h : (wpList κ d fEnd ss).run st = .ok (r, st')) (hD : DeadBelow st) :
    DeadBelow st' := (wpList_wf κ d fEnd ss _ _ _ h).ext.deadBelow hD

/-- The registrations of a statement walk's result are fresh names drawn by the walk: not
    avoided, with counters from the input counter on and below the output counter. -/
theorem wpStmt_regs (h : (wpStmt κ d f s).run st = .ok (a, st')) :
    ∀ e ∈ a.regs.toList, ∃ b j, e = freshName b j ∧ st.next ≤ j ∧ j < st'.next ∧
      st.avoid.contains e = false := fun e he => ((wpStmt_wf κ d f s _ _ _ h).regs e he).spec

/-- The registrations of a list walk's result are fresh names drawn by the walk: not avoided,
    with counters from the input counter on and below the output counter. -/
theorem wpList_regs (h : (wpList κ d fEnd ss).run st = .ok (r, st')) :
    ∀ e ∈ r.regs.toList, ∃ b j, e = freshName b j ∧ st.next ≤ j ∧ j < st'.next ∧
      st.avoid.contains e = false := fun e he => ((wpList_wf κ d fEnd ss _ _ _ h).regs e he).spec

/-- An exit snapshot registered for a label after a list walk was registered before it or is a
    fresh name drawn by the walk. -/
theorem wpList_pending_new (h : (wpList κ d fEnd ss).run st = .ok (r, st')) {l : String}
    {e : P.Ident} (he : e ∈ st'.pending.getD l []) : e ∈ st.pending.getD l [] ∨
      ∃ b j, e = freshName b j ∧ st.next ≤ j ∧ j < st'.next ∧ st.avoid.contains e = false :=
  ((wpList_wf κ d fEnd ss st r st' h).ext.pendNew l e he).imp id NewIn.spec

/-- After the walks of `rest` and then of `s`, a registration of `rest` registered for a label
    was registered for it before the walk of `s`. -/
theorem pending_regs {rest : PStmts P} {st st1 st2 : WSt P} {r a : WRes P}
    (h1 : (wpList κ d fEnd rest).run st = .ok (r, st1))
    (h2 : (wpStmt κ d f s).run st1 = .ok (a, st2)) {l : String} {e : P.Ident}
    (he : e ∈ r.regs.toList) (hp : e ∈ st2.pending.getD l []) : e ∈ st1.pending.getD l [] :=
  ((wpStmt_wf κ d f s _ _ _ h2).ext.pendNew l e hp).resolve_right
  fun hn => NewIn.disj ((wpList_wf κ d fEnd rest _ _ _ h1).regs e he) hn rfl

/-- A statement walk keeps the names marked dead, and marks dead only fresh names it draws. -/
theorem wpStmt_dead (h : (wpStmt κ d f s).run st = .ok (a, st')) (e : P.Ident) :
    (st.dead.contains e = true → st'.dead.contains e = true) ∧
    (st'.dead.contains e = true → st.dead.contains e = true ∨
      ∃ b j, e = freshName b j ∧ st.next ≤ j ∧ j < st'.next ∧ st.avoid.contains e = false) :=
  ⟨(wpStmt_wf κ d f s _ _ _ h).ext.deadMono e,
  fun hd => ((wpStmt_wf κ d f s _ _ _ h).ext.dead e hd).imp_right NewIn.spec⟩

/-- A statement walked with an obligation following it (from a state with `DeadBelow`) that has
    a normal run does not always exit. -/
theorem wpStmt_ax_normal (h : (wpStmt κ d true s).run st = .ok (a, st')) (hD : DeadBelow st)
    {F : P.Factory} {X : Outcome P → Prop} {σ σ1 : SemanticStore P} {evs : List (Event P)}
    (hr : DRunS F X s σ evs (.normal σ1)) : a.ax = false :=
  (((wpStmt_wf κ d true s _ _ _ h).ax hD).2 rfl _ _ _ _ _ hr).1 _ rfl

/-- A statement walk (from a state with `DeadBelow`) of a statement with a reach of a failing
    target has an obligation. -/
theorem wpStmt_hit_hasObl (h : (wpStmt κ d f s).run st = .ok (a, st')) (hD : DeadBelow st)
    {F : P.Factory} {σ : SemanticStore P} {tr : List (Event P)} {t : AssertId P} {e : P.Expr}
    (hr : DReachS F s σ tr) (hc : Claim t e tr) : a.hasObl = true :=
  ((wpStmt_wf κ d f s _ _ _ h).ax hD).1 _ _ _ _ _ hr hc

/-- A list walk (from a state with `DeadBelow`) of a list with a reach of a failing target has
    an obligation. -/
theorem wpList_hit_hasObl (h : (wpList κ d fEnd ss).run st = .ok (r, st')) (hD : DeadBelow st)
    {F : P.Factory} {σ : SemanticStore P} {tr : List (Event P)} {t : AssertId P} {e : P.Expr}
    (hr : DReach F ss σ tr) (hc : Claim t e tr) : r.hasObl = true :=
  ((wpList_wf κ d fEnd ss _ _ _ h).ax hD).1 _ _ _ _ _ hr hc

/-- A list walk (from a state with `DeadBelow`) whose result has no obligation reaches no failing
    target of the list. -/
theorem noObl_claim (h : (wpList κ d fEnd ss).run st = .ok (r, st')) (hD : DeadBelow st)
    (hobl : r.hasObl = false) {F : P.Factory} {σ : SemanticStore P} {tr : List (Event P)}
    {t : AssertId P} {e : P.Expr} (hr : DReach F ss σ tr) (hc : Claim t e tr) : False :=
  by simp [wpList_hit_hasObl h hD hr hc] at hobl

/-! ## Registrations, snapshots and dead names -/

/-- The registrations of a list walk's result (from a state with `DeadBelow`) are not dead after
    the walk. -/
theorem wpList_regs_live (h : (wpList κ d fEnd ss).run st = .ok (r, st')) (hD : DeadBelow st) :
    ∀ e ∈ r.regs.toList, st'.dead.contains e = false := (wpList_wf κ d fEnd ss _ _ _ h).nodead hD

/-- For the walk of a block's body under a variable context, from a state with no snapshot for
    the block's label: the snapshots for the label that are not dead after the walk are
    registrations of the body. -/
theorem body_snaps_regs (hκ : κ ≠ .top) {d : Nat} {fEnd : Bool} {l : String} {ss : PStmts P}
    {st st' : WSt P} {r : WRes P} (hp : st.pending.getD l [] = [])
    (h : (wpList κ d fEnd ss).run st = .ok (r, st')) :
    ∀ e ∈ ((st'.pending.getD l []).filter fun e => !st'.dead.contains e).reverse,
      e ∈ r.regs.toList := fun e he => by
  obtain ⟨hm, hd⟩ := List.mem_filter.1 (List.mem_reverse.1 he)
  refine ((wpList_wf κ d fEnd ss _ _ _ h).pendReg hκ l e hm (by simp [hp])).resolve_right ?_
  simpa using hd

/-! ## Snapshots under one label -/

/-- A registration of a list walk's result, from a state whose snapshots of fresh-name form
    have counters below its counter, is registered after the walk for at most one label. -/
theorem wpList_regs_one_label (h : (wpList κ d fEnd ss).run st = .ok (r, st'))
    (hP : ∀ (l : String) (e : P.Ident), e ∈ st.pending.getD l [] → ∀ b j, e = freshName b j →
      j < st.next) :
    ∀ e ∈ r.regs.toList, ∀ l1 l2, e ∈ st'.pending.getD l1 [] → e ∈ st'.pending.getD l2 [] →
      l1 = l2 :=
  fun e he => (wpList_wf κ d fEnd ss _ _ _ h).uniq hP e ((wpList_wf κ d fEnd ss _ _ _ h).regs e he)

/-! ## Carried merges -/

/-- An exit of an arm walk under a variable context with an obligation following (from a state
    with `DeadBelow` whose label depths are at most `d`) to a label of the region at depth `t`
    gives the walk a largest exit target `K` at least `t`, the depth of a label of the walk's
    input state. -/
theorem arm_exitTgt (h : (wpList κ d true ss).run st = .ok (r, st')) (hκ : κ ≠ .top)
    (hD : DeadBelow st) (hL : ∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d)
    {F : P.Factory} {X : Outcome P → Prop} {σ : SemanticStore P} {evs : List (Event P)} {l : String}
    {σ1 : SemanticStore P} (hr : DRun F X ss σ evs (.exit l σ1)) {t : Nat}
    (ht : st.labelDepth[l]? = some t) :
    ∃ K, r.tgt.max? = some K ∧ t ≤ K ∧ ∃ l' : String, st.labelDepth[l']? = some K := by
  have W := wpList_wf κ d true ss _ _ _ h
  obtain ⟨K, hK, htK⟩ := LeftistHeap.le_max (W.ci hL).ord
    ((W.ax hD).2 rfl _ _ _ _ _ hr |>.2.2 l σ1 t rfl hκ hL ht)
  exact ⟨K, hK, htK, (W.ci hL).tgt K (LeftistHeap.max?_mem hK)⟩

/-- A carried merge registered by a list walk (from a well-formed state with `DeadBelow` whose
    label depths are at most `d`, with no label under `top`) lies at a depth at most the walk's
    largest exit target. -/
theorem arm_carryDepth (h : (wpList κ d fEnd ss).run st = .ok (r, st')) (hwf : WFSt st)
    (hD : DeadBelow st) (hL : ∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d)
    (hT : κ = .top → ∀ l : String, st.labelDepth[l]? = none) {k i : Nat} {n : P.Ident} {v : WExpr P}
    {xB : P.Ident} (hi : (st'.carries.getD k [])[i]? = some (n, v, xB))
    (hx : xB ∈ r.regs.toList) : ∃ K, r.tgt.max? = some K ∧ k ≤ K := by
  have W := wpList_wf κ d fEnd ss st r st' h
  have C := W.ci hL
  have hq := List.mem_of_getElem? hi
  have hold : (n, v, xB) ∉ st.carries.getD k [] := fun hm =>
    (hwf.carries_get hm).1.elim fun _ ⟨_, hb, hj⟩ => (W.regs xB hx).ne hj hb
  by_cases hk : k ≤ d
  · obtain ⟨pre, hpre, hpq⟩ := C.pre hT k hk
    exact (List.mem_append.1 (hpre ▸ hq)).elim (fun hq => LeftistHeap.le_max C.ord
      (((hpq _ hq).2.1).resolve_right (by simp [W.nodead hD _ hx]))) (absurd · hold)
  · exact absurd (C.high k (by omega) _ hq) hold

/-- After the walks of `rest` and then of `s` at depth `d` (from a well-formed state whose label
    depths are at most `d`), at each block depth, the carried merges of the output state of `s`
    are new merges, with copies registered by `s` or dead, followed by those of its input state,
    or neither state has a carried merge registered by `rest` at that depth. -/
theorem wpStmt_carries {rest : PStmts P} {st st1 st2 : WSt P} {r a : WRes P} (hwf : WFSt st)
    (hL : ∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d)
    (h1 : (wpList κ d fEnd rest).run st = .ok (r, st1))
    (h2 : (wpStmt κ d f s).run st1 = .ok (a, st2)) (k : Nat) :
    ∃ pre : List (P.Ident × WExpr P × P.Ident),
      (∀ q ∈ pre, q.2.2 ∈ a.regs.toList ∨ st2.dead.contains q.2.2 = true) ∧
      (st2.carries.getD k [] = pre ++ st1.carries.getD k [] ∨
        ∀ q ∈ st1.carries.getD k [] ++ st2.carries.getD k [], q.2.2 ∉ r.regs.toList) := by
  have W1 := wpList_wf κ d fEnd rest st r st1 h1
  have W2 := wpStmt_wf κ d f s st1 a st2 h2
  have hL1 : LabLe st1 d := fun l t ht => hL l t (W1.ext.ld l ▸ ht)
  rcases Nat.lt_or_ge d k with hk | hk
  · refine ⟨[], nofun, .inr fun q hq hr => ?_⟩
    have hq' := (W1.ci hL).high k hk q <| (List.mem_append.1 hq).elim id ((W2.ci hL1).high k hk q)
    exact (hwf.carries_get hq').1.elim fun _ ⟨_, hb, hj⟩ => (W1.regs _ hr).ne hj hb
  · obtain ⟨pre, he, hpre⟩ := (W2.ci hL1).pre trivial k hk
    exact ⟨pre, fun q hq => (hpre q hq).1, .inl he⟩

/-- For the walk of a block's body at depth `d + 1` under a variable context, from a state with
    no carried merge at depth `d + 1` and label depths at most `d + 1`: the carried merges at
    depth `d + 1` that are not dead after the walk have copies registered by the body; and, when
    the carried copies of the input state have counters below its counter, a carried merge whose
    copy is registered by the body is at a depth at most `d + 1`. -/
theorem body_carries (hκ : κ ≠ .top) {d : Nat} {f : Bool} {body : PStmts P} {stB st1 : WSt P}
    {B : WRes P} (hL : ∀ (l : String) (t : Nat), stB.labelDepth[l]? = some t → t ≤ d + 1)
    (hst : stB.carries.getD (d + 1) [] = [])
    (hB : (wpList κ (d + 1) f body).run stB = .ok (B, st1)) :
    (∀ e ∈ (st1.carries.getD (d + 1) []).filter (fun e => !st1.dead.contains e.2.2),
      e.2.2 ∈ B.regs.toList) ∧
    ((∀ (k : Nat) (e : P.Ident × WExpr P × P.Ident), e ∈ stB.carries.getD k [] →
        ∃ b j, e.2.2 = freshName b j ∧ j < stB.next) →
      ∀ (k i : Nat) (n : P.Ident) (v : WExpr P) (xB : P.Ident),
        (st1.carries.getD k [])[i]? = some (n, v, xB) → xB ∈ B.regs.toList → k ≤ d + 1) := by
  have W := wpList_wf κ (d + 1) f body stB B st1 hB
  refine ⟨fun e he => ?_, fun hF k i n v xB hi hx => Nat.not_lt.1 fun hk => ?_⟩
  · obtain ⟨hm, hd⟩ := List.mem_filter.1 he
    obtain ⟨pre, he', hpre⟩ := (W.ci hL).pre (absurd · hκ) (d + 1) (Nat.le_refl _)
    rw [he', hst, List.append_nil] at hm
    exact (hpre e hm).1.resolve_right (by simpa using hd)
  · obtain ⟨b, j, hb, hj⟩ := hF k _ ((W.ci hL).high k hk _ (List.mem_of_getElem? hi))
    exact (W.regs xB hx).ne hj hb

/-- The carried merges after the walk of a real branch are those before it. -/
theorem wpIteReal_carries_eq {c : P.Expr} {tss ess : PStmts P} {st st' : WSt P} {a : WRes P}
    (h : (wpIteReal κ d c tss ess).run st = .ok (a, st')) :
    ∀ k q, q ∈ st'.carries.getD k [] → q ∈ st.carries.getD k [] :=
  fun k => ((wpIteReal_wf κ d c tss ess (wpList_wf · d · tss) (wpList_wf · d · ess) _ _ _ h).2 k).2

/-! ## Assigned names, merge targets and selector variables -/

/-- For the walk of a block's body at depth `d + 1` from a well-formed state with no carried
    merge at depth `d + 1`, whose names of `D` (holding the body's identifiers) are avoided if
    they have the form of a fresh name, and whose reach context's variables are fresh names drawn
    before, not avoided and no renamings: the targets of the merges at depth `d + 1` not dead
    after the walk are no registrations of the body; a carried merge whose copy is registered by
    the body has a selector built from variables, literals and conditionals, reading no such
    target and no variable of the context, and targets no variable of the context. -/
theorem body_carries_names {body : PStmts P} {stB st1 : WSt P} {B : WRes P} {D : List P.Ident}
    (hw : WFSt stB) (hav : ∀ x ∈ D, AvoidedIfFresh stB x) (hD : ∀ x ∈ Block.idents body, x ∈ D)
    (hκ : ∀ z ∈ RE.vars κ, (∃ b j, z = freshName b j ∧ j < stB.next) ∧
      stB.avoid.contains z = false ∧ stB.back[z]? = none) (hst : stB.carries.getD (d + 1) [] = [])
    (hB : (wpList κ (d + 1) f body).run stB = .ok (B, st1)) :
    (∀ e ∈ (st1.carries.getD (d + 1) []).filter (fun e => !st1.dead.contains e.2.2),
      e.1 ∉ B.regs.toList) ∧
    (∀ (k i : Nat) (n : P.Ident) (v : WExpr P) (xB : P.Ident) (c : WExpr P),
      (st1.carries.getD k [])[i]? = some (n, v, xB) → xB ∈ B.regs.toList →
      v = .ite c (.var xB) (.var n) → wsimple c ∧ ∀ y ∈ wvars c,
        y ∉ ((st1.carries.getD (d + 1) []).filter
          (fun e => !st1.dead.contains e.2.2)).map (·.1) ∧ y ∉ RE.vars κ) ∧
    (∀ (k i : Nat) (n : P.Ident) (v : WExpr P) (xB : P.Ident),
      (st1.carries.getD k [])[i]? = some (n, v, xB) → xB ∈ B.regs.toList → n ∉ RE.vars κ) := by
  have W := wpList_wf κ (d + 1) f body stB B st1 hB
  have N := W.ni D hw hav hD
  have hT : ∀ y, FName stB st1 y → ¬ TName D st1 y := fun y ⟨⟨b, j, hy, _, _, ha⟩, hb⟩ ht =>
    ht.elim (fun ⟨x, hx⟩ => by simp [hb] at hx) fun hm => by simp [hav y hm b j hy] at ha
  have hF : ∀ y ∈ B.regs.toList, FName stB st1 y := fun y hy => ⟨(W.regs y hy).spec, N.regs y hy⟩
  have hnew : ∀ k i n v xB, (st1.carries.getD k [])[i]? = some (n, v, xB) →
      xB ∈ B.regs.toList → TName D st1 n ∧ ∃ c, v = WExpr.ite c (.var xB) (.var n) ∧ wsimple c ∧
        ∀ y ∈ wvars c, FName stB st1 y := fun k i n v xB hi hx =>
    N.car k _ (List.mem_of_getElem? hi) fun hm =>
      (hw.carries_get hm).1.elim fun _ ⟨_, hb, hj⟩ => (W.regs xB hx).ne hj hb
  refine ⟨fun e he hr => ?_, fun k i n v xB c hi hx hv => ?_, fun k i n v xB hi hx hn => ?_⟩
  · exact hT _ (hF _ hr) (N.car _ e (List.mem_filter.1 he).1 (by simp [hst])).1
  · obtain ⟨-, c', hc', hs, hy⟩ := hnew k i n v xB hi hx
    cases hv.symm.trans hc'
    refine ⟨hs, fun y hy' => ⟨fun hm => ?_, fun hm => ?_⟩⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      exact hT _ (hy _ hy') (N.car _ e (List.mem_filter.1 he).1 (by simp [hst])).1
    · obtain ⟨⟨b, j, h1, h2, -⟩, -⟩ := hy y hy'
      obtain ⟨⟨b', j', h3, h4⟩, -⟩ := hκ y hm
      grind [freshName_counter_inj]
  · obtain ⟨⟨b, j, hn', hj⟩, ha, hb⟩ := hκ n hn
    refine (hnew k i n v xB hi hx).1.elim (fun ⟨x, hx'⟩ => ?_) fun hm => ?_
    · obtain ⟨b', j', h1, -, h2⟩ := (wpList_walkOK hB).back n (by simp [hb, hx'])
      grind [freshName_counter_inj]
    · simp [hav n hm b j hn'] at ha

/-- A list walk at depth `d`, from a state whose label depths are at most `d`, adds no carried
    merge at a depth below `d`. -/
theorem wpList_carries_high (h : (wpList κ d fEnd ss).run st = .ok (r, st'))
    (hL : ∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d) :
    ∀ k, d < k → ∀ q ∈ st'.carries.getD k [], q ∈ st.carries.getD k [] :=
  ((wpList_wf κ d fEnd ss _ _ _ h).ci hL).high

end -- public section

end WP
end Imperative

