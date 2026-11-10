/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverState
public import Strata.Transform.Passive.SimulationProps
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.Replace

/-! # Facts about whole WP walks

How a walk of a statement, a list or a laid-out or real `ite` changes the walk state: the
avoided names, the label depths, the counter and the clock, the declared types, the type
references and the back map, the current names of the variables it does not declare, and the
well-formedness of the state (`WFSt`); the declared types kept by the final type maps; and,
under a variable reach context, the live current names of the variables it does not declare.

Key definitions: `DeadBelow`, `FreshAt`, `AvoidedIfFresh`, `TyKey`, `WFSt`, `WalkCore`, `WalkOK`.

Key theorems: `wpList_walkOK`, `wpStmt_walkOK`, `wpList_top_facts`, `wpStmt_tys`,
`wpList_live_keep`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iL : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPOps P]
omit iW iL


/-- Every discarded registration of the walk state `st` of the form of a fresh name has a counter
    below `st.next` (it was drawn before). -/
@[expose] def DeadBelow (st : WSt P) : Prop :=
  ∀ b j, st.dead.contains (freshName b j) = true → j < st.next

/-- `n` is a fresh name that the walk from state `st` on may create: a name `freshName b j`
    that `st` does not avoid, with a counter `j` from `st.next` on. -/
@[expose] def FreshAt (st : WSt P) (n : P.Ident) : Prop :=
  ∃ b j, n = freshName b j ∧ st.avoid.contains n = false ∧ st.next ≤ j

/-- `n` is avoided whenever it has the form of a fresh name. -/
@[expose] def AvoidedIfFresh (st : WSt P) (n : P.Ident) : Prop :=
  ∀ b j, n = freshName b j → st.avoid.contains n = true

/-- A name that may have a declared type in the walk state `st`: avoided, or recorded as
    declared later and avoided if it has the form of a fresh name, or a fresh name with a counter
    below `st.next` that is no recorded renaming. -/
@[expose] def TyKey (st : WSt P) (n : P.Ident) : Prop :=
  st.avoid.contains n = true ∨ (st.taken.contains n = true ∧ AvoidedIfFresh st n) ∨
    ((∃ b j, n = freshName b j ∧ j < st.next) ∧ ∀ x : P.Ident, st.nm[x]? ≠ some n)

/-- Well-formedness of a walk state: a recorded renaming is a fresh name (a counter below
    `st.next`, not avoided) recorded in the back map, no two variables have the same recorded
    renaming; the keys of the back map and of the type references and the exit snapshots are
    fresh names with a counter below `st.next`; the stamps of the live set are below the clock;
    a name with a declared type is avoided, or recorded as declared later and avoided if it has
    the form of a fresh name, or a fresh name with a counter below `st.next` that is no recorded
    renaming (`TyKey`); a key of the type references is not avoided and no recorded renaming;
    a carried merge of a variable `n` is a selection between its carried copy `xB`, a fresh name
    with a counter below `st.next`, and `n`. -/
structure WFSt (st : WSt P) : Prop where
  nm_fresh : ∀ x n : P.Ident, st.nm[x]? = some n → st.back[n]? = some x ∧
    ∃ b j, n = freshName b j ∧ j < st.next ∧ st.avoid.contains n = false
  nm_inj : ∀ x z n : P.Ident, st.nm[x]? = some n → st.nm[z]? = some n → x = z
  back_fresh : ∀ n x : P.Ident, st.back[n]? = some x → ∃ b j, n = freshName b j ∧ j < st.next
  tyOf_fresh : ∀ n x : P.Ident, st.tyOf[n]? = some x → ∃ b j, n = freshName b j ∧ j < st.next
  pending_fresh : ∀ (l : String) (e : P.Ident), e ∈ st.pending.getD l [] →
    ∃ b j, e = freshName b j ∧ j < st.next
  live_stamp : ∀ (n : P.Ident) (s : Nat), st.live[n]? = some s → s < st.clock
  tys_keys : ∀ n : P.Ident, (st.tys[n]?).isSome → TyKey st n
  tyOf_keys : ∀ n x : P.Ident, st.tyOf[n]? = some x →
    st.avoid.contains n = false ∧ ∀ z : P.Ident, st.nm[z]? ≠ some n
  carries_fresh : ∀ (k i : Nat) (n : P.Ident) (v : WExpr P) (xB : P.Ident),
    (st.carries.getD k [])[i]? = some (n, v, xB) → ∃ b j, xB = freshName b j ∧ j < st.next
  carries_sel : ∀ (k i : Nat) (n : P.Ident) (v : WExpr P) (xB : P.Ident),
    (st.carries.getD k [])[i]? = some (n, v, xB) → ∃ e, v = .ite e (.var xB) (.var n)

/-- How a walk changes the state, apart from the label depths: the avoided names are unchanged
    and the counter and the clock do not decrease; a new recorded renaming is a fresh name
    (`FreshAt`); the names recorded as declared later stay recorded; the declared types change
    only at names the fragment declares (`decl`) not yet recorded as declared, recorded
    renamings and fresh names; the type references and the back map change only at fresh names;
    a variable that the fragment does not declare keeps its current name; well-formedness is
    kept when the declared names of the fragment are avoided if they have the form of a fresh
    name; a live entry stamped before the walk's clock was already there with that stamp. -/
structure WalkCore (decl : List P.Ident) (st st' : WSt P) : Prop where
  avoid : st'.avoid = st.avoid
  next : st.next ≤ st'.next
  clock : st.clock ≤ st'.clock
  nm : ∀ x n : P.Ident, st'.nm[x]? = some n → st.nm[x]? = some n ∨ FreshAt st n
  taken : ∀ y : P.Ident, st.taken.contains y = true → st'.taken.contains y = true
  tys : ∀ n : P.Ident, st'.tys[n]? ≠ st.tys[n]? →
    (n ∈ decl ∧ st.taken.contains n = false) ∨ (∃ x : P.Ident, st.nm[x]? = some n) ∨
      FreshAt st n
  tyOf : ∀ n : P.Ident, st'.tyOf[n]? ≠ st.tyOf[n]? → FreshAt st n
  back : ∀ n : P.Ident, st'.back[n]? ≠ st.back[n]? → FreshAt st n
  names : ∀ z m, z ∉ decl → curName st z = some m → curName st' z = some m
  wf : WFSt st → (∀ x ∈ decl, AvoidedIfFresh st x) → WFSt st'
  liveOld : ∀ (n : P.Ident) (t : Nat), st'.live[n]? = some t → t < st.clock →
    st.live[n]? = some t
  /-- A block entry stamp the walk changes is from the clock before the walk on. -/
  stamp : ∀ j, st'.stampAt.getD j 0 = st.stampAt.getD j 0 ∨ st.clock ≤ st'.stampAt.getD j 0

/-- How a walk changes the state (`WalkCore`), the label depths being unchanged and the exit
    snapshots registered for each label staying registered. -/
structure WalkOK (decl : List P.Ident) (st st' : WSt P) : Prop extends WalkCore decl st st' where
  labelDepth : ∀ l : String, st'.labelDepth[l]? = st.labelDepth[l]?
  pending : ∀ (l : String) (e : P.Ident), e ∈ st.pending.getD l [] → e ∈ st'.pending.getD l []

open Lean in
/-- A `WalkCore` proof whose fields and `WFSt.of_next` arguments (`w3` to `w11`, the counter and
    the names recorded as declared being the `next` and `taken` fields) are given by name, every
    other one being the proof for an unchanged component of the state. -/
local macro "wcore%" "[" args:(ident " := " term),* "]" : term => do
  let g (n : Name) (d : MacroM Term) : MacroM Term := do
    match args.getElems.find? (·.raw[0].getId == n) with
    | some a => pure ⟨a.raw[2]⟩
    | none => d
  let nx ← g `next `(Nat.le_refl _)
  let tk ← g `taken `(fun _ h => h)
  let ne ← `(fun _ h => absurd rfl h)
  `(⟨rfl, $nx, $(← g `clock `(Nat.le_refl _)), $(← g `nm `(fun _ _ h => .inl h)), $tk,
    $(← g `tys (pure ne)), $(← g `tyOf (pure ne)), $(← g `back (pure ne)),
    $(← g `names `(fun _ _ _ h => h)),
    fun hw _ => hw.of_next $nx rfl rfl $(← g `w3 `(fun _ _ h => .inl h)) $(← g `w4 (pure ne))
      $(← g `w5 (pure ne)) $(← g `w6 `(fun _ _ h => .inl h)) $(← g `w7 `(id)) $tk
      $(← g `w11 `(fun _ _ h => .inl h)),
    $(← g `liveOld `(fun _ _ h _ => h)), $(← g `stamp `(fun _ => .inl rfl))⟩)

include iL in
/-- A fresh name differs from a fresh name with a counter below `st.next`. -/
theorem FreshAt.ne {st : WSt P} {n m : P.Ident} (h : FreshAt st n)
    (hm : ∃ b j, m = freshName b j ∧ j < st.next) : n ≠ m := by
  grind [FreshAt, freshName_counter_inj]
/-- A carried entry of a well-formed state has a fresh copy with a counter below the counter
    and is a selection between the copy and its variable. -/
theorem WFSt.carries_get {st : WSt P} (hw : WFSt st) {k : Nat} {e : P.Ident × WExpr P × P.Ident}
    (he : e ∈ st.carries.getD k []) :
    (∃ b j, e.2.2 = freshName b j ∧ j < st.next) ∧ ∃ w, e.2.1 = .ite w (.var e.2.2) (.var e.1) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
  exact ⟨hw.carries_fresh k i _ _ _ hi, hw.carries_sel k i _ _ _ hi⟩
/-- In a well-formed state, no recorded renaming has a declared type. -/
theorem WFSt.nm_untyped {st : WSt P} (hw : WFSt st) {x n : P.Ident} (hx : st.nm[x]? = some n) :
    st.tys[n]? = none := by
  grind [WFSt, TyKey, AvoidedIfFresh, Option.isSome_iff_exists]
include iL in
/-- A walk step from a well-formed state keeps every type reference. -/
theorem WalkCore.tyOf_keep {D : List P.Ident} {st st' : WSt P} (h : WalkCore D st st')
    (hw : WFSt st) {n x : P.Ident} (hn : st.tyOf[n]? = some x) : st'.tyOf[n]? = some x :=
  Classical.byContradiction fun hne => (h.tyOf n (hn ▸ hne)).ne (hw.tyOf_fresh n x hn) rfl
include iL in
/-- A walk step from a well-formed state keeps every entry of the back map. -/
theorem WalkCore.back_keep {D : List P.Ident} {st st' : WSt P} (h : WalkCore D st st')
    (hw : WFSt st) {n x : P.Ident} (hn : st.back[n]? = some x) : st'.back[n]? = some x :=
  Classical.byContradiction fun hne => (h.back n (hn ▸ hne)).ne (hw.back_fresh n x hn) rfl
/-- `WalkCore` steps compose. -/
private theorem WalkCore.trans {D : List P.Ident} {s0 s1 s2 : WSt P} (h1 : WalkCore D s0 s1)
    (h2 : WalkCore D s1 s2) : WalkCore D s0 s2 := by
  have hf : ∀ n, FreshAt s1 n → FreshAt s0 n := fun _ h => h.imp fun _ => .imp fun _ ⟨e, ha, hj⟩ =>
    ⟨e, h1.avoid ▸ ha, Nat.le_trans h1.next hj⟩
  refine ⟨h2.avoid.trans h1.avoid, Nat.le_trans h1.next h2.next, Nat.le_trans h1.clock h2.clock,
    fun x n h => (h2.nm x n h).elim (h1.nm x n) (.inr ∘ hf n), fun y h => h2.taken y (h1.taken y h),
    fun n h => ?_, fun n h => (Classical.em (s1.tyOf[n]? = s0.tyOf[n]?)).elim
      (fun e => hf n (h2.tyOf n (e ▸ h))) (h1.tyOf n),
    fun n h => (Classical.em (s1.back[n]? = s0.back[n]?)).elim
      (fun e => hf n (h2.back n (e ▸ h))) (h1.back n),
    fun z m hz hc => h2.names z m hz (h1.names z m hz hc),
    fun hw hd => h2.wf (h1.wf hw hd) fun x hx b j e => h1.avoid ▸ hd x hx b j e,
    fun n t h ht => h1.liveOld n t (h2.liveOld n t h (Nat.lt_of_lt_of_le ht h1.clock)) ht,
    fun j => (h2.stamp j).elim (fun e => (h1.stamp j).imp e.trans fun h => e ▸ h)
      fun h => .inr (Nat.le_trans h1.clock h)⟩
  have ht1 := h1.taken n
  have hy1 := h1.tys n
  have hy2 := h2.tys n
  have hn1 := h1.nm
  grind +splitImp

/-- `n` is a fresh name of `st` with a counter below `st'.next`: drawn between the two states. -/
private def NewAt (st st' : WSt P) (n : P.Ident) : Prop :=
  st.avoid.contains n = false ∧ (∃ b j, n = freshName b j ∧ j < st'.next) ∧
    ∀ b j, n = freshName b j → st.next ≤ j

/-- Well-formedness is kept by a state change that keeps the avoided names and the declared
    types, does not decrease the counter, keeps the names recorded as declared
    later, adds renamings only to names drawn by the change (`NewAt`) recorded in the back map,
    changes the back map only at drawn names and the type references only at drawn names with
    the renamings unchanged, adds only exit snapshots and carried merges with fresh copies with
    a counter below the new counter, and stamps the live set below the new clock. -/
private theorem WFSt.of_next {st st' : WSt P} (h : WFSt st) (h1 : st.next ≤ st'.next)
    (h2 : st'.avoid = st.avoid) (h9 : st'.tys = st.tys)
    (h3 : ∀ x n : P.Ident, st'.nm[x]? = some n →
      st.nm[x]? = some n ∨ st'.back[n]? = some x ∧ NewAt st st' n)
    (h4 : ∀ n : P.Ident, st'.back[n]? ≠ st.back[n]? → NewAt st st' n)
    (h5 : ∀ n : P.Ident, st'.tyOf[n]? ≠ st.tyOf[n]? → NewAt st st' n ∧ st'.nm = st.nm)
    (h6 : ∀ l e, e ∈ st'.pending.getD l [] →
      e ∈ st.pending.getD l [] ∨ ∃ b j, e = freshName b j ∧ j < st'.next)
    (h7 : (∀ (n : P.Ident) (s : Nat), st.live[n]? = some s → s < st.clock) →
      ∀ (n : P.Ident) (s : Nat), st'.live[n]? = some s → s < st'.clock)
    (h10 : ∀ y : P.Ident, st.taken.contains y = true → st'.taken.contains y = true)
    (h11 : ∀ k e, e ∈ st'.carries.getD k [] → e ∈ st.carries.getD k [] ∨
      (∃ b j, e.2.2 = freshName b j ∧ j < st'.next) ∧ ∃ w, e.2.1 = .ite w (.var e.2.2) (.var e.1)) :
    WFSt st' := by
  have hO : ∀ n : P.Ident, (∃ b j, n = freshName b j ∧ j < st.next) → ¬ NewAt st st' n :=
    fun n ⟨b, j, e, hj⟩ ⟨_, _, hge⟩ => absurd (hge b j e) (by omega)
  have hm : ∀ n : P.Ident, (∃ b j, n = freshName b j ∧ j < st.next) →
      ∃ b j, n = freshName b j ∧ j < st'.next :=
    fun n ⟨b, j, e, hj⟩ => ⟨b, j, e, Nat.lt_of_lt_of_le hj h1⟩
  have hb : ∀ x n : P.Ident, st'.nm[x]? = some n → st'.back[n]? = some x := fun x n hx =>
    (h3 x n hx).elim (fun ho =>
      have ⟨hb, b, j, e, hj, _⟩ := h.nm_fresh x n ho
      Classical.byContradiction fun hne => hO n ⟨b, j, e, hj⟩ (h4 n (hb ▸ hne))) And.left
  have hc : ∀ k e, e ∈ st'.carries.getD k [] → (∃ b j, e.2.2 = freshName b j ∧ j < st'.next) ∧
      ∃ w, e.2.1 = .ite w (.var e.2.2) (.var e.1) := fun k e he =>
    (h11 k e he).elim (fun h0 => (h.carries_get h0).imp_left (hm _)) id
  refine ⟨fun x n hx => ⟨hb x n hx, ?_⟩,
    fun x z n hx hz => Option.some.inj ((hb x n hx).symm.trans (hb z n hz)),
    fun n x hn => (Classical.em (st'.back[n]? = st.back[n]?)).elim
      (fun e => hm n (h.back_fresh n x (e ▸ hn))) fun e => (h4 n e).2.1,
    fun n x hn => (Classical.em (st'.tyOf[n]? = st.tyOf[n]?)).elim
      (fun e => hm n (h.tyOf_fresh n x (e ▸ hn))) fun e => (h5 n e).1.2.1,
    fun l e he => (h6 l e he).elim (fun h0 => hm e (h.pending_fresh l e h0)) id,
    h7 h.live_stamp, fun n hn => ?_, fun n x hn => ?_,
    fun k i _ _ _ hi => (hc k _ (List.mem_of_getElem? hi)).1,
    fun k i _ _ _ hi => (hc k _ (List.mem_of_getElem? hi)).2⟩
  · refine (h3 x n hx).elim (fun ho => ?_) fun ⟨_, ha, ⟨b, j, e, hj⟩, _⟩ => ⟨b, j, e, hj, h2 ▸ ha⟩
    obtain ⟨-, b, j, e, hj, ha⟩ := h.nm_fresh x n ho
    exact ⟨b, j, e, Nat.lt_of_lt_of_le hj h1, h2 ▸ ha⟩
  · rcases h.tys_keys n (h9 ▸ hn) with ha | ⟨ht, hf⟩ | ⟨hj, hnm⟩
    · exact .inl (h2 ▸ ha)
    · exact .inr (.inl ⟨h10 n ht, fun b j e => h2 ▸ hf b j e⟩)
    · exact .inr (.inr ⟨hm n hj, fun x hx => (h3 x n hx).elim (hnm x) fun ⟨_, hN⟩ => hO n hj hN⟩)
  · by_cases e : st'.tyOf[n]? = st.tyOf[n]?
    · have ho := e ▸ hn
      obtain ⟨ha, hz⟩ := h.tyOf_keys n x ho
      exact ⟨h2 ▸ ha, fun z hz' => (h3 z n hz').elim (hz z) fun ⟨_, hN⟩ =>
        hO n (h.tyOf_fresh n x ho) hN⟩
    · obtain ⟨hN, hnm⟩ := h5 n e
      refine ⟨h2 ▸ hN.1, fun z hz => ?_⟩
      obtain ⟨-, b, j, e', hj, -⟩ := h.nm_fresh z n (hnm ▸ hz)
      exact hO n ⟨b, j, e', hj⟩ hN
/-- Entering a block at depth `k` with label `l` (the label at depth `k` with no exit snapshots,
    the depth stamped with the clock and without carried merges) is a `WalkCore` step. -/
private theorem WalkCore.blkIn (D : List P.Ident) (st : WSt P) (l : String) (k : Nat) :
    WalkCore D st { st with
      labelDepth := st.labelDepth.insert l k, pending := st.pending.insert l [],
      stampAt := st.stampAt.insert k st.clock, carries := st.carries.insert k [] } :=
  wcore% [w6 := fun _ _ _ => .inl (by grind), w11 := fun _ _ _ => .inl (by grind),
    stamp := fun _ => by grind]
/-- A state is related to itself. -/
private theorem WalkOK.refl (D : List P.Ident) (st : WSt P) : WalkOK D st st :=
  ⟨wcore% [], fun _ => rfl, fun _ _ h => h⟩
/-- `WalkOK` steps compose. -/
private theorem WalkOK.trans {D : List P.Ident} {s0 s1 s2 : WSt P} (h1 : WalkOK D s0 s1)
    (h2 : WalkOK D s1 s2) : WalkOK D s0 s2 :=
  ⟨h1.1.trans h2.1, fun l => (h2.labelDepth l).trans (h1.labelDepth l),
    fun l e h => h2.pending l e (h1.pending l e h)⟩
/-- A walk step for the declared names `D` is one for any list containing them. -/
private theorem WalkOK.mono {D D' : List P.Ident} {st st' : WSt P} (h : WalkOK D st st')
    (hD : ∀ x ∈ D, x ∈ D') : WalkOK D' st st' :=
  { h with
    tys := fun n hn => (h.tys n hn).imp_left fun ⟨h1, h2⟩ => ⟨hD n h1, h2⟩
    names := fun z m hz => h.names z m fun h' => hz (hD z h')
    wf := fun hw hx => h.wf hw fun x h' => hx x (hD x h') }
/-- Replaces a successful run `h` of a bind whose first step is deterministic (`get`, `set` or
    `modify`) by the run of the continuation, `n` times (once by default). -/
scoped macro "run_peel " h:ident n:(ppSpace num)? : tactic =>
  `(tactic| iterate $(n.getD (Lean.quote 1)) (
    replace $h:ident := wm_run_bind_ok $h
    obtain ⟨_, _, h0, $h:ident⟩ := $h
    cases h0))

/-- A reflexive and transitive relation between the input and the output state of a run: the
    facts about runs that bind composes. -/
private class RunRel (R : WSt P → WSt P → Prop) : Prop where
  refl : ∀ st, R st st
  trans : ∀ {s0 s1 s2}, R s0 s1 → R s1 s2 → R s0 s2

/-- Every successful run of `m` relates its input and output states by `R`. -/
private structure Runs (R : WSt P → WSt P → Prop) {α : Type} (m : WM P α) : Prop where
  run : ∀ st a st', m.run st = .ok (a, st') → R st st'

section
variable {R : WSt P → WSt P → Prop} {α β : Type}
/-- `pure` relates the state to itself. -/
private theorem runs_pure [RunRel R] (a : α) : Runs R (pure a : WM P α) :=
  ⟨fun st _ _ h => (wm_run_pure_ok h).2 ▸ RunRel.refl st⟩
/-- `get` relates the state to itself. -/
private theorem runs_get [RunRel R] : Runs R (get : WM P (WSt P)) :=
  ⟨fun st _ _ h => (Prod.mk.inj (Except.ok.inj h)).2 ▸ RunRel.refl st⟩
/-- `throw` has no successful run. -/
private theorem runs_throw (e : String) : Runs R (throw e : WM P α) := ⟨fun _ _ _ h => nomatch h⟩
/-- A `modify` whose function is related to the state it is applied to is a `Runs R` step. -/
private theorem runs_modify {g : WSt P → WSt P} (h : ∀ st, R st (g st)) :
    Runs R (modify g : WM P Unit) := ⟨fun st _ _ hr => (Prod.mk.inj (Except.ok.inj hr)).2 ▸ h st⟩
/-- A bind of `Runs R` computations is one. -/
private theorem runs_bind [RunRel R] {x : WM P α} {f : α → WM P β} (hx : Runs R x)
    (hf : ∀ a, Runs R (f a)) : Runs R (x >>= f) :=
  ⟨fun _ _ _ h => (wm_run_bind_ok h).elim fun a ⟨_, h1, h2⟩ =>
    RunRel.trans (hx.run _ _ _ h1) ((hf a).run _ _ _ h2)⟩
/-- `pure a >>= f` is a `Runs R` computation when `f a` is. -/
private theorem runs_pure_bind {a : α} {f : α → WM P β} (h : Runs R (f a)) :
    Runs R (pure a >>= f) := ⟨h.run⟩
/-- A computation followed by a `modify` depending on its result and by `Runs R` computations is
    a `Runs R` computation when the first two steps relate their states. -/
private theorem runs_bind_modify [RunRel R] {x : WM P α} {g : α → WSt P → WSt P}
    {k : α → PUnit → WM P β} (h : ∀ st a s1, x.run st = .ok (a, s1) → R st (g a s1))
    (hk : ∀ a u, Runs R (k a u)) : Runs R (x >>= fun a => modify (g a) >>= k a) := by
  refine ⟨fun st b st' hr => ?_⟩
  obtain ⟨a, s1, h1, hr⟩ := wm_run_bind_ok hr
  run_peel hr
  exact RunRel.trans (h st a s1 h1) ((hk a ()).run _ _ _ hr)
/-- A `get` followed by a `set` of a function of the state and by `Runs R` computations is a
    `Runs R` computation when the `modify` of that function is. -/
private theorem runs_get_set [RunRel R] {g : WSt P → WSt P} {k : WSt P → PUnit → WM P β}
    (h : Runs R (modify g : WM P Unit)) (hk : ∀ s u, Runs R (k s u)) :
    Runs R (get >>= fun s => set (g s) >>= k s) :=
  ⟨fun st _ _ hr => RunRel.trans (h.run st () _ rfl) ((hk st ()).run _ _ _ hr)⟩
/-- A `Runs R` computation is a `Runs R'` one for a weaker `R'`. -/
private theorem Runs.imp {R' : WSt P → WSt P → Prop} {m : WM P α} (h : ∀ s s', R s s' → R' s s')
    (hm : Runs R m) : Runs R' m := ⟨fun s a s' hr => h s s' (hm.run s a s' hr)⟩
/-- A `for` loop whose body is a `Runs R` computation is one. -/
private theorem runs_forIn [RunRel R] (f : P.Ident → β → WM P (ForInStep β))
    (hf : ∀ x b, Runs R (f x b)) : ∀ (xs : List P.Ident) (b : β), Runs R (forIn xs b f)
  | [], b => runs_pure b
  | x :: xs, b => by
    rw [List.forIn_cons]
    exact runs_bind (hf x b) fun | .done c => runs_pure c | .yield c => runs_forIn f hf xs c
end

private local instance (D : List P.Ident) : RunRel (WalkOK D) := ⟨WalkOK.refl D, WalkOK.trans⟩

/-- Every successful run of `m` changes the state as `WalkOK D` says. -/
private abbrev Good {α : Type} (D : List P.Ident) (m : WM P α) : Prop := Runs (WalkOK D) m
/-- A `modify` changing only the live set and the discarded registrations, adding no stamp to
    the live set, is a `WalkOK` step. -/
private theorem good_modify (D : List P.Ident) (g : WSt P → WSt P)
    (h : ∀ st, g st = { st with live := (g st).live, dead := (g st).dead } ∧
      ∀ (n : P.Ident) (s : Nat), (g st).live[n]? = some s → st.live[n]? = some s) :
    Good D (modify g : WM P Unit) := by
  refine runs_modify fun st => ?_
  rw [(h st).1]
  exact ⟨wcore% [w7 := fun hl n s hs => hl n s ((h st).2 n s hs),
    liveOld := fun n t ht _ => (h st).2 n t ht], fun _ => rfl, fun _ _ h => h⟩
/-- `liveAdd` is a `WalkOK` step. -/
private theorem good_liveAdd (D : List P.Ident) (xs : List P.Ident) :
    Good D (liveAdd xs : WM P Unit) := ⟨fun st _ st' h => by
  cases h
  obtain ⟨live, clock, hr, -, hk, hn, hc⟩ := liveAdd_run xs st
  cases hr
  exact ⟨wcore% [clock := hc, liveOld := fun n t ht hlt => by grind,
    w7 := fun hs n s h => by grind], fun _ => rfl, fun _ _ h => h⟩⟩
/-- `liveDel` is a `WalkOK` step. -/
private theorem good_liveDel (D : List P.Ident) (x : P.Ident) :
    Good D (liveDel x : WM P Unit) :=
  good_modify D _ fun _ => ⟨rfl, fun _ _ h => by simp_all [Std.HashMap.getElem?_erase]⟩

include iL in
/-- The name `freshIn` draws from `st` is `freshName b k` for a counter `k` from `st.next` on,
    the counter advancing to `k + 1`, and is a fresh name of `st`. -/
private theorem fresh_run {b : String} {st : WSt P} :
    ∃ k, (freshIn st.avoid b st.next).1 = freshName b k ∧ (freshIn st.avoid b st.next).2 = k + 1 ∧
      st.next ≤ k ∧ FreshAt st (freshIn st.avoid b st.next).1 := by
  obtain ⟨k, hk, hn, hav⟩ := freshIn_spec st.avoid b st.next
  rw [hk]
  exact ⟨k, rfl, rfl, hn, b, k, rfl, hav, hn⟩
/-- Giving a declared type to a name that may have one keeps well-formedness. -/
private theorem WFSt.ins_ty {st : WSt P} (hw : WFSt st) {n : P.Ident} (hn : TyKey st n)
    (ty : P.Ty) : WFSt { st with tys := st.tys.insert n ty } :=
  { hw with tys_keys := fun m hm => show TyKey st m by grind [hw.tys_keys m] }

include iL in
/-- A run of `wFresh` is a `WalkOK` step returning a fresh name, which may then get a declared
    type. -/
private theorem walk_wFresh {D : List P.Ident} {b : String} {st st' : WSt P} {a : P.Ident}
    (h : (wFresh b).run st = .ok (a, st')) :
    WalkOK D st st' ∧ ((a ∈ D ∧ st.taken.contains a = false) ∨
      (∃ y : P.Ident, st.nm[y]? = some a) ∨ FreshAt st a) ∧
    (WFSt st → (∀ y ∈ D, AvoidedIfFresh st y) → TyKey st' a) := by
  obtain ⟨k, hk, hk1, hle, hF⟩ := fresh_run (b := b) (st := st)
  refine ⟨?_, .inr (.inr ?_), fun hw _ => ?_⟩
  all_goals cases (wFresh_run b st).symm.trans h
  · exact ⟨wcore% [next := hk1 ▸ Nat.le_succ_of_le hle], fun _ => rfl, fun _ _ h => h⟩
  · exact hF
  · exact .inr (.inr ⟨⟨b, k, hk, by simp [hk1]⟩, fun x hx => by
      grind [FreshAt, WFSt, → freshName_counter_inj]⟩)
/-- A computation returning a name that may get a declared type, followed by giving it a type and
    by `WalkOK` steps, is a `WalkOK` step. -/
private theorem good_ins {β : Type} {D : List P.Ident} {m : WM P P.Ident} {ty : P.Ty}
    {k : P.Ident → PUnit → WM P β}
    (hm : ∀ st a st', m.run st = .ok (a, st') →
      WalkOK D st st' ∧ ((a ∈ D ∧ st.taken.contains a = false) ∨
        (∃ y : P.Ident, st.nm[y]? = some a) ∨ FreshAt st a) ∧
      (WFSt st → (∀ y ∈ D, AvoidedIfFresh st y) → TyKey st' a))
    (hk : ∀ a u, Good D (k a u)) :
    Good D (m >>= fun a => modify (fun st => { st with tys := st.tys.insert a ty }) >>= k a) := by
  refine runs_bind_modify (fun st a s1 h1 => ?_) hk
  obtain ⟨hw, ha, hk'⟩ := hm st a s1 h1
  refine { hw with tys := fun n hn => ?_, wf := fun h hd => (hw.wf h hd).ins_ty (hk' h hd) ty }
  grind [hw.tys n]

include iL in
/-- Drawing a fresh name and giving it a type, followed by `WalkOK` steps, is a `WalkOK` step. -/
private theorem good_freshTy {β : Type} {D : List P.Ident} {b : String} {ty : P.Ty}
    {k : P.Ident → PUnit → WM P β} (hk : ∀ a u, Good D (k a u)) :
    Good D (wFresh b >>= fun a => modify (fun st => { st with tys := st.tys.insert a ty }) >>=
      k a) := good_ins (fun _ _ _ h => walk_wFresh h) hk
include iL in
/-- `wFreshBool` is a `WalkOK` step. -/
private theorem good_wFreshBool (D : List P.Ident) (b : String) :
    Good D (wFreshBool b : WM P P.Ident) := good_freshTy fun a _ => runs_pure a
/-- An insertion into a hash map changes it only at the inserted key. -/
private theorem ins_ne {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] {m : Std.HashMap α β}
    {k n : α} {v : β} (h : (m.insert k v)[n]? ≠ m[n]?) : k = n :=
  Classical.byContradiction fun e => h (by simp [Std.HashMap.getElem?_insert, e])
include iL in
/-- The name `freshIn` draws from `st` is drawn between `st` and a state whose counter is the
    advanced one, and is a fresh name of `st`. -/
private theorem fresh_new {b : String} {st st' : WSt P}
    (h : st'.next = (freshIn st.avoid b st.next).2) : st.next ≤ st'.next ∧
    NewAt st st' (freshIn st.avoid b st.next).1 ∧ FreshAt st (freshIn st.avoid b st.next).1 := by
  obtain ⟨k, hk, hn, hav⟩ := freshIn_spec st.avoid b st.next
  rw [hk] at h ⊢
  exact ⟨by omega, ⟨hav, ⟨b, k, rfl, by omega⟩, fun b' j he => freshName_counter_inj he ▸ hn⟩, b, k,
    rfl, hav, hn⟩
section
include iW iL
/-- `wFreshLike` is a `WalkOK` step. -/
private theorem good_wFreshLike (D : List P.Ident) (x : P.Ident) :
    Good D (wFreshLike x : WM P P.Ident) := ⟨fun st _ st' h => by
  cases (wFreshLike_run x st).symm.trans h
  obtain ⟨hle, hN, hF⟩ := fresh_new (b := baseOf x) (st := st) (st' := { st with
    next := (freshIn st.avoid (baseOf x) st.next).2 }) rfl
  exact ⟨wcore% [next := hle, tyOf := fun n hn => ins_ne hn ▸ hF,
    w5 := fun n hn => ⟨ins_ne hn ▸ hN, rfl⟩], fun _ => rfl, fun _ _ h => h⟩⟩
/-- A run of `wName x` is a `WalkOK` step and returns a recorded renaming, `x` itself (not
    recorded as declared later), or a fresh name. -/
private theorem walk_wName {D : List P.Ident} {x n : P.Ident} {st st' : WSt P}
    (h : (wName x).run st = .ok (n, st')) :
    WalkOK D st st' ∧ ((∃ y : P.Ident, st.nm[y]? = some n) ∨
      (n = x ∧ st.taken.contains x = false) ∨ FreshAt st n) := by
  have hk := wName_curName_keep h
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨-, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩
  · exact ⟨WalkOK.refl D _, .inl ⟨x, h1⟩⟩
  · exact ⟨WalkOK.refl D _, .inr (.inl ⟨rfl, h2⟩)⟩
  · obtain ⟨hle, hN, hF⟩ := fresh_new (b := baseOf x) (st := st) (st' := { st with
      next := (freshIn st.avoid (baseOf x) st.next).2 }) rfl
    refine ⟨⟨wcore% [next := hle, nm := fun _ _ _ => by grind, back := fun _ hn => ins_ne hn ▸ hF,
      names := fun z m _ hz => hk z m hz, w3 := fun _ _ _ => by grind [NewAt],
      w4 := fun _ hn => ins_ne hn ▸ hN], fun _ => rfl, fun _ _ h => h⟩, .inr (.inr hF)⟩

/-- `wName` is a `WalkOK` step. -/
private theorem good_wName (D : List P.Ident) (x : P.Ident) : Good D (wName x : WM P P.Ident) :=
  ⟨fun _ _ _ h => (walk_wName h).1⟩
/-- A run of `wDecl x` for a declared `x` is a `WalkOK` step; it returns `x` itself (not recorded
    as declared before the run), a recorded renaming or a fresh name, which may then get a
    declared type. -/
private theorem walk_wDecl {D : List P.Ident} {x n : P.Ident} {st st' : WSt P} (hx : x ∈ D)
    (h : (wDecl x).run st = .ok (n, st')) :
    WalkOK D st st' ∧ ((n ∈ D ∧ st.taken.contains n = false) ∨
      (∃ y : P.Ident, st.nm[y]? = some n) ∨ FreshAt st n) ∧
    (WFSt st → (∀ y ∈ D, AvoidedIfFresh st y) → TyKey st' n) := by
  obtain ⟨n1, s1, h1⟩ := wName_ok x st
  cases (wDecl_run h1).symm.trans h
  obtain ⟨hw1, hc⟩ := walk_wName (D := D) h1
  refine ⟨hw1.trans ⟨wcore% [nm := fun _ _ _ => .inl (by grind), taken := fun _ _ => by grind,
    w3 := fun _ _ _ => .inl (by grind), names := fun z m hz hc => by
      simpa [curName, Std.HashMap.getElem?_erase, show x ≠ z from fun e => hz (e ▸ hx)] using hc],
    fun _ => rfl, fun _ _ h => h⟩, by grind, fun hw hD => ?_⟩
  obtain ⟨k, hk, hk1, hle, hF⟩ := fresh_run (b := baseOf x) (st := st)
  rcases wName_cases h1 with ⟨h2, rfl⟩ | ⟨h2, h3, rfl, rfl⟩ | ⟨h2, h3, rfl, rfl⟩
  · refine .inr (.inr ⟨(hw.nm_fresh x _ h2).2.imp fun _ => .imp fun _ h => ⟨h.1, h.2.1⟩,
      fun y hy => ?_⟩)
    obtain rfl := hw.nm_inj y x _ (by grind) h2
    simp at hy
  · exact .inr (.inl ⟨by simp, hD _ hx⟩)
  · refine .inr (.inr ⟨⟨baseOf x, k, hk, by simp [hk1]⟩, fun y hy => ?_⟩)
    grind [WFSt, → freshName_counter_inj]
end
open Lean Meta Elab Tactic in
/-- Splits the `if` or `match` heading the computation of a `Good` goal. -/
local elab "head_split" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.isApp do throwError "head_split: not a walk goal"
  let m := tgt.appArg!.consumeMData
  let ok ← match m.getAppFn with
    | .const n _ => pure (n == ``ite || n == ``dite || (← isMatcher n))
    | _ => pure false
  unless ok do throwError "head_split: no `if` or `match` at the head"
  evalTactic (← `(tactic| split))
open Lean Meta Elab Tactic in
/-- Fails unless the computation of the goal (its last argument), or the first computation of
    that computation when it is a bind, is headed by the constant `c`. -/
local elab "on_head " c:ident : tactic => withMainContext do
  let n ← realizeGlobalConstNoOverload c
  let some m := (← instantiateMVars (← getMainTarget)).getAppArgs.back? | throwError "on_head"
  let x := if m.isAppOfArity ``Bind.bind 6 then m.getArg! 4 else m.consumeMData
  unless x.getAppFn.isConstOf n do throwError "on_head: no {n} at the head"
open Lean Meta Elab Tactic in
/-- Fails unless the goal is `Runs R m` for a relation `R` headed by the constant `c`. -/
local elab "goal_head " c:ident : tactic => withMainContext do
  let n ← realizeGlobalConstNoOverload c
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  unless t.isAppOf ``Runs && t.appFn!.appFn!.appArg!.getAppFn.isConstOf n do throwError "goal_head"
open Lean Meta Elab Tactic in
/-- Closes a goal `X … c …` for a primitive computation `c` headed by a constant `N.f` (the last
    argument of the goal with such a head for which `pfx_f` exists) with the lemma `pfx_f` (all of
    whose arguments are fixed by the goal or are instances). -/
scoped elab "prim " pfx:ident : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some c ← tgt.getAppArgs.reverse.findSomeM? (fun a => do
      let some f := a.consumeMData.getAppFn.constName? | return none
      let n := s!"{pfx.getId.eraseMacroScopes}_{f.getString!}"
      try some <$> realizeGlobalConstNoOverload (mkIdent (.mkSimple n)) catch _ => return none)
    | throwError "prim: no lemma"
  let e ← mkConstWithFreshMVarLevels c
  let (args, bis, concl) ← forallMetaTelescope (← inferType e)
  unless ← withTransparency .instances (isDefEq concl tgt) do throwError "prim: mismatch"
  for a in args, bi in bis do
    if bi.isInstImplicit && !(← a.mvarId!.isAssigned) then
      a.mvarId!.assign (← synthInstance (← inferType a))
  let v ← instantiateMVars (mkAppN e args)
  if v.hasExprMVar then throwError "prim: arguments left"
  g.assign v
  replaceMainGoal []

open Lean Meta Elab Tactic in
/-- On a hypothesis `h : m.run s = r`, replaces `m` by the definitionally equal `red m`, computed
    under the configuration `cfg` sets. -/
private meta def headRedAt (cfg : Meta.Config → Meta.Config) (h : Ident)
    (red : Expr → MetaM Expr := whnfCore) : TacticM Unit := withMainContext do
  let fv ← getFVarId h
  let ty ← instantiateMVars (← fv.getType)
  let lhs := ty.appFn!.appArg!
  let m := lhs.appFn!.appArg!
  let m' ← withConfig cfg (red m)
  if m' == m then throwError "head reduction: no progress"
  let ty' := mkApp2 ty.appFn!.appFn! (mkApp2 lhs.appFn!.appFn! m' lhs.appArg!) ty.appArg!
  replaceMainGoal [← (← getMainGoal).replaceLocalDeclDefEq fv ty']

/-- On `h : m.run s = r`, reduces the head of `m`, substituting `let`s and `have`s. -/
scoped elab "head_whnf_at " h:ident : tactic => headRedAt id h

/-- On `h : m.run s = r`, reduces the head of `m` without substituting `let`s and `have`s. -/
scoped elab "head_red_at " h:ident : tactic => headRedAt (fun c => { c with zeta := false }) h

open Lean Meta in
/-- The value and body of the first `have` of `m` whose value is a function, after substituting
    the values of the leading `have`s that are not functions. -/
private meta partial def peelJP (m : Expr) : MetaM (Expr × Expr) := do
  let .letE _ t v b _ := m.consumeMData | throwError "jp_gen: no join point"
  if (← whnf t).isForall then return (v, b) else peelJP (b.instantiate1 v)

open Lean Meta Elab Tactic in
/-- On a hypothesis `h : (have x₁ := v₁; …; have j := v; b).run s = r`, substitutes the values of
    the leading `have`s that are not functions and replaces the first function `v` (a join point
    `j` of a `do` block) by a new local `K` with `hK : v = K`, leaving `h : b[K].run s = r`. -/
scoped elab "jp_gen " h:ident : tactic => withMainContext do
  let fv ← getFVarId h
  let ty ← instantiateMVars (← fv.getType)
  let lhs := ty.appFn!.appArg!
  let (v, b) ← peelJP lhs.appFn!.appArg!
  let t ← inferType v
  let (_, g) ← (← getMainGoal).revert #[fv]
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let newTy ← withLocalDeclD `K t fun K => do
      let tyK := mkApp2 ty.appFn!.appFn! (mkApp2 lhs.appFn!.appFn! (b.instantiate1 K) lhs.appArg!)
        ty.appArg!
      withLocalDeclD `hK (← mkEq v K) fun hK =>
        withLocalDeclD h.getId tyK fun hh => mkForallFVars #[K, hK, hh] tgt.bindingBody!
    let g' ← mkFreshExprSyntheticOpaqueMVar newTy
    g.assign (.lam `h ty (mkApp3 g' v (← mkEqRefl v) (.bvar 0)) .default)
    let (_, g'') ← g'.mvarId!.introNP 3
    replaceMainGoal [g'']

/-- A property of computations holds for a computation using a join point when it holds for
    every call of the join point and for the computation using any join point with that
    property. -/
private theorem jp_of {α β γ : Type} {Q : ∀ {δ : Type}, WM P δ → Prop} {v : α → WM P β}
    {b : (α → WM P β) → WM P γ} (hv : ∀ x, Q (v x))
    (hb : ∀ jp : α → WM P β, (∀ x, Q (jp x)) → Q (b jp)) : Q (b v) := hb v hv
open Lean Meta Elab Tactic in
/-- Turns the `have` heading the computation of a `Good` goal into a local definition, or
    reduces a head beta-redex or a head local definition. -/
local elab "head_let" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  unless tgt.isApp do throwError "head_let: not a walk goal"
  let m := tgt.appArg!.consumeMData
  if let .letE n t v b nd := m then
    if t.isForall then
      let t' ← whnfR tgt
      let r := if t'.isAppOf ``Runs then t'.appFn!.appFn!.appArg! else t'
      let some hd := r.getAppFn.constName? | throwError "head_let: not a walk goal"
      let pairRE := t.bindingDomain!.isAppOf ``Prod &&
        (t.bindingDomain!.getArg! 0).isAppOf ``RE
      let pair := pairRE && (← getEnv).contains (.str hd "jp_pair")
      let e ← mkConstWithFreshMVarLevels (if pair then .str hd "jp_pair" else ``jp_of)
      let (args, _, concl) ← forallMetaTelescope (← inferType e)
      let k := args.size
      unless pair do
        let ty ← inferType m
        let as := tgt.getAppArgs
        let some i := as.findIdx? (· == ty.appArg!) | throwError "head_let: jp"
        let q ← withLocalDeclD `δ (← inferType ty.appArg!) fun δ =>
          withLocalDeclD `c (mkApp ty.appFn! δ) fun c =>
            mkLambdaFVars #[δ, c] (mkAppN tgt.getAppFn ((as.set! i δ).set! (as.size - 1) c))
        unless ← isDefEq args[k - 5]! q do throwError "head_let: jp"
      unless ← isDefEq args[k - 3]! (.lam n t b .default) do throwError "head_let: jp"
      unless ← isDefEq args[k - 4]! v do throwError "head_let: jp"
      unless ← isDefEq concl tgt do throwError "head_let: jp"
      g.assign (mkAppN e args)
      replaceMainGoal [args[k - 2]!.mvarId!, args[k - 1]!.mvarId!]
      return
    let g' ← g.replaceTargetDefEq (.letE n t v (mkApp tgt.appFn! b) nd)
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    return
  let fn := m.getAppFn
  let m' ← match fn with
    | .lam .. => pure m.headBeta
    | .fvar id => do
      match ← id.getValue? with
      | some v => pure (v.beta m.getAppArgs)
      | none => throwError "head_let: nothing to reduce"
    | _ => throwError "head_let: nothing to reduce"
  replaceMainGoal [← g.replaceTargetDefEq (mkApp tgt.appFn! m')]

/-- One step of a `Runs` decomposition common to every relation: a bind, an introduction, a
    primitive, a `for` loop or a hypothesis. -/
local macro "run_step" : tactic => `(tactic| first
  | with_reducible_and_instances apply runs_pure_bind
  | with_reducible_and_instances apply runs_bind
  | intro _
  | prim runs
  | (on_head ForIn.forIn; apply runs_forIn; intro _ _)
  | with_reducible (apply_assumption; done))

/-- One step of the `Good` decomposition of a walk. -/
local macro "walk_step" : tactic => `(tactic| first
  | head_let
  | head_split
  | (on_head saveRestore
     with_reducible_and_instances apply $(Lean.mkIdent `good_bind_sr)
     intro _)
  | (on_head wDecl
     with_reducible_and_instances apply $(Lean.mkIdent `good_decl) (by simp [stmtsInits])
     intro _ _)
  | (on_head wFresh; with_reducible_and_instances apply good_freshTy; intro _ _)
  | (on_head wFreshBool
     with_reducible_and_instances apply $(Lean.mkIdent `good_pend)
     intro _ _)
  | run_step
  | prim good
  | (on_head modify; with_reducible_and_instances apply good_modify; intro _
     refine ⟨rfl, fun _ _ h => ?_⟩
     first | exact h | simp at h))

include iW iL in
/-- `wRen` is a `WalkOK` step. -/
private theorem good_wRen (D : List P.Ident) (e : P.Expr) :
    Good D (wRen e : WM P (WExpr P × List P.Ident)) := by
  unfold wRen
  repeat' walk_step
include iW iL in
/-- `saveRestore` is a `WalkOK` step. -/
private theorem good_saveRestore (D : List P.Ident) (xs : List P.Ident) :
    Good D (saveRestore xs : WM P _) := by
  unfold saveRestore
  repeat' walk_step
/-- A computation that is a `WalkOK D` step is one for any list containing `D`. -/
private theorem Good.mono {α : Type} {D D' : List P.Ident} {m : WM P α} (h : Good D m)
    (hD : ∀ x ∈ D, x ∈ D') : Good D' m := ⟨fun st a st' hr => (h.run st a st' hr).mono hD⟩
include iW iL in
/-- Declaring `x ∈ D` and giving the returned name a type, followed by `WalkOK` steps, is a
    `WalkOK` step. -/
private theorem good_decl {β : Type} {D : List P.Ident} {x : P.Ident} {ty : P.Ty}
    {k : P.Ident → PUnit → WM P β} (hx : x ∈ D) (hk : ∀ a u, Good D (k a u)) :
    Good D (wDecl x >>= fun a => modify (fun st => { st with tys := st.tys.insert a ty }) >>=
      k a) := good_ins (fun _ _ _ h => walk_wDecl hx h) hk
include iL in
/-- Drawing a fresh Boolean name and registering it as an exit snapshot is a `WalkOK` step. -/
private theorem walk_pend {D : List P.Ident} {b l : String} {st s1 : WSt P} {a : P.Ident}
    (ha : (wFreshBool b).run st = .ok (a, s1)) :
    WalkOK D st { s1 with pending := s1.pending.insert l (a :: s1.pending.getD l []) } := by
  refine ((good_wFreshBool D b).run _ _ _ ha).trans ⟨wcore% [w6 := fun l' e he => ?_], fun _ => rfl,
    fun l' e he => by grind⟩
  cases (wFreshBool_run b st).symm.trans ha
  obtain ⟨k, hk, hn, hav⟩ := freshIn_spec st.avoid b st.next
  grind
include iL in
/-- Drawing a fresh Boolean name and registering it as an exit snapshot, followed by `WalkOK`
    steps, is a `WalkOK` step. -/
private theorem good_pend {β : Type} {D : List P.Ident} {b l : String}
    {k : P.Ident → PUnit → WM P β} (hk : ∀ a u, Good D (k a u)) :
    Good D (wFreshBool b >>= fun a =>
      modify (fun st => { st with pending := st.pending.insert l (a :: st.pending.getD l []) }) >>=
        k a) := runs_bind_modify (fun _ _ _ h1 => walk_pend h1) hk
/-- The names of `L` are fresh names with a counter below `st.next`. -/
private def FreshL (L : List P.Ident) (st : WSt P) : Prop :=
  ∀ y ∈ L, ∃ b j, y = freshName b j ∧ j < st.next

/-- Names drawn before a state are drawn before every state with a larger counter. -/
private theorem FreshL.mono {L : List P.Ident} {st st' : WSt P} (h : FreshL L st)
    (hn : st.next ≤ st'.next) : FreshL L st' :=
  fun y hy => (h y hy).imp fun _ => .imp fun _ h => ⟨h.1, Nat.lt_of_lt_of_le h.2 hn⟩

/-- From a state in which the names of `L` were drawn, the state changes as `WalkOK D` says. -/
private def PreOK (D L : List P.Ident) (st st' : WSt P) : Prop := FreshL L st → WalkOK D st st'

private local instance (D L : List P.Ident) : RunRel (PreOK D L) :=
  ⟨fun _ _ => WalkOK.refl D _, fun h1 h2 hL => (h1 hL).trans (h2 (hL.mono (h1 hL).next))⟩

/-- Every successful run of `c` from a state in which the names of `L` were drawn changes the
    state as `WalkOK D` says. -/
private abbrev GoodPre {α : Type} (D L : List P.Ident) (c : WM P α) : Prop := Runs (PreOK D L) c

/-- A `WalkOK` step is one from any state. -/
private theorem goodPre_of_good {α : Type} {D L : List P.Ident} {c : WM P α} (g : Good D c) :
    GoodPre D L c := g.imp fun _ _ h _ => h
include iW iL in
/-- The copies `saveRestore` returns are fresh names with a counter below the counter of its
    output state. -/
private theorem saveRestore_fresh {xs : List P.Ident} {st st' : WSt P}
    {r : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) × List (P.Ident × P.Ident)}
    (h : (saveRestore xs).run st = .ok (r, st')) : FreshL (r.2.2.2.map Prod.snd) st' := by
  unfold saveRestore at h
  obtain ⟨⟨copies, cps, restores, saves⟩, s1, hl, h⟩ := wm_run_bind_ok h
  cases h
  refine wm_forIn_inv (fun _ b s => FreshL (b.2.2.2.map Prod.snd) s) _ ?_ xs [] _ st _ _
    (by simp [FreshL]) hl
  intro S y b s b' s' hI hb
  obtain ⟨a, s1, h1, hb⟩ := wm_run_bind_ok hb
  obtain ⟨c, s2, h2, hb⟩ := wm_run_bind_ok hb
  cases hb
  cases (wFreshLike_run y s).symm.trans h1
  cases (wFreshLike_run y _).symm.trans h2
  obtain ⟨k1, e1, h1, -⟩ := freshIn_spec s.avoid (baseOf y) s.next
  obtain ⟨k2, e2, h2, -⟩ := freshIn_spec s.avoid (baseOf y) (k1 + 1)
  exact ⟨_, rfl, by grind [FreshL]⟩
include iW iL in
/-- `saveRestore` followed by `GoodPre` computations for its copies and the names `L` is a
    `GoodPre` computation for `L`. -/
private theorem goodPre_bind_sr {β : Type} {D L : List P.Ident} {xs : List P.Ident}
    {f : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) × List (P.Ident × P.Ident) → WM P β}
    (hf : ∀ r, GoodPre D (L ++ r.2.2.2.map Prod.snd) (f r)) :
    GoodPre D L (saveRestore xs >>= f) :=
  ⟨fun _ _ _ h hL => (wm_run_bind_ok h).elim fun r ⟨_, h1, h2⟩ =>
  have hw := (good_saveRestore D xs).run _ _ _ h1
  hw.trans ((hf r).run _ _ _ h2 fun y hy =>
    (List.mem_append.1 hy).elim (hL.mono hw.next y) (saveRestore_fresh h1 y))⟩
include iW iL in
/-- `saveRestore` followed by `GoodPre` computations for its copies is a `WalkOK` step. -/
private theorem good_bind_sr {β : Type} {D : List P.Ident} {xs : List P.Ident}
    {f : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) × List (P.Ident × P.Ident) → WM P β}
    (hf : ∀ r, GoodPre D (r.2.2.2.map Prod.snd) (f r)) : Good D (saveRestore xs >>= f) :=
  (goodPre_bind_sr (L := []) hf).imp fun _ _ h => h fun _ h => nomatch h
/-- Pushing at depth `t` the selector merges of pairs whose copies are among the drawn names `L`
    is a `GoodPre` computation for `L`. -/
private theorem goodPre_carries {D L : List P.Ident} {C : List (P.Ident × P.Ident)} {e0 : WExpr P}
    {t : Nat}
    {F : List (P.Ident × WExpr P × P.Ident) → P.Ident × P.Ident →
      List (P.Ident × WExpr P × P.Ident)}
    (hF : ∀ l x xB, F l (x, xB) = (x, .ite e0 (.var xB) (.var x), xB) :: l)
    (hC : ∀ p ∈ C, p.2 ∈ L) :
    GoodPre D L (modify fun st =>
      { st with carries := st.carries.insert t (C.foldl F (st.carries.getD t [])) } :
        WM P Unit) := by
  refine runs_modify fun st hL => ?_
  obtain rfl : F = fun l p => (p.1, .ite e0 (.var p.2) (.var p.1), p.2) :: l :=
    funext fun l => funext fun ⟨x, xB⟩ => hF l x xB
  simp only [List.foldl_flip_cons_eq_append]
  have hL' := fun p hp => hL p.2 (hC p hp)
  refine ⟨wcore% [w11 := fun _ _ h => ?_], fun _ => rfl, fun _ _ h => h⟩
  grind

/-- One step of the `GoodPre` decomposition of a walk. -/
local macro "walkP_step" : tactic => `(tactic| first
  | head_let
  | head_split
  | (with_reducible_and_instances apply goodPre_bind_sr; intro _)
  | ((with_reducible_and_instances apply goodPre_carries) <;>
      first | (intro _ _ _; rfl) | grind +zetaDelta)
  | (goal_head PreOK; with_reducible_and_instances apply runs_bind)
  | (apply goodPre_of_good; walk_step)
  | with_reducible (apply_assumption; done))


omit iDE iBo iFv iSu iId iFs in
/-- A stamp of a union of live sets is a stamp of one of them. -/
private theorem unionLive_getElem {a b : Std.HashMap P.Ident Nat} {n : P.Ident} {s : Nat}
    (h : (unionLive a b)[n]? = some s) : a[n]? = some s ∨ b[n]? = some s := by
  have key : ∀ (f : Std.HashMap P.Ident Nat → P.Ident × Nat → Std.HashMap P.Ident Nat),
      (∀ m p, (f m p)[n]? = some s → m[n]? = some s ∨ p = (n, s)) →
      ∀ (l : List (P.Ident × Nat)) m, (l.foldl f m)[n]? = some s → m[n]? = some s ∨ (n, s) ∈ l := by
    intro f hf l
    induction l <;> grind
  unfold unionLive at h
  split at h <;> rw [Std.HashMap.fold_eq_foldl_toList] at h
  all_goals
    have hk := key _ (fun m p h => by split at h <;> grind) _ _ h
    grind
section
include iW iL
/-- A block walk is a `WalkOK` step for the names its body declares, when the walks of the
    body are. -/
private theorem wpStmt_block_good (κ : RE P) (d : Nat) (f : Bool) (l : String) (body : PStmts P)
    (md : MetaData P) (hB0 : ∀ κ', Good (stmtsInits body) (wpList κ' (d + 1) f body)) :
    Good (stmtsInits [.block l body md]) (wpStmt κ d f (.block l body md)) := ⟨fun st r st' h => by
  rw [wpStmt] at h
  run_peel h 2
  jp_gen h
  have hK' : ∀ p s, WalkOK (stmtsInits body) { st with
      labelDepth := st.labelDepth.insert l (d + 1), pending := st.pending.insert l [],
      stampAt := st.stampAt.insert (d + 1) st.clock, carries := st.carries.insert (d + 1) [] } s →
      (K p).run s = .ok (r, st') → WalkOK (stmtsInits [.block l body md]) st st' := by
    clear h
    subst hK
    intro ⟨κB, rL?⟩ s hs h
    head_red_at h
    replace h := wm_run_bind_ok h
    obtain ⟨B, s2, hB, h⟩ := h
    run_peel h
    head_whnf_at h
    run_peel h
    head_whnf_at h
    replace h := wm_run_bind_ok h
    obtain ⟨u, s4, h4, h⟩ := h
    cases h
    have hw := hs.trans ((hB0 κB).run _ _ _ hB)
    have hc := (WalkCore.blkIn (stmtsInits body) st l (d + 1)).trans hw.toWalkCore
    refine WalkOK.mono (D := stmtsInits body) (.trans ?_ ((good_liveAdd _ _).run _ _ _ h4))
      (by simp [stmtsInits])
    refine ⟨{ hc with wf := fun hwf hd => ?_ }, fun l' => ?_, fun l' e he => ?_⟩
    · refine (hc.wf hwf hd).of_next (Nat.le_refl _) rfl rfl (fun _ _ h => .inl h)
        (fun _ h => absurd rfl h) (fun _ h => absurd rfl h) (fun l' e he => ?_) id (fun _ h => h)
        (fun k e he => .inl (by grind))
      have hp := hwf.pending_fresh l
      have hn := hc.next
      split at he <;> grind [Std.HashMap.getD_eq_getD_getElem?]
    · have hl := hw.labelDepth l'
      split <;> grind
    · have hp := hw.pending l'
      split <;> grind [Std.HashMap.getD_eq_getD_getElem?]
  split at h
  · obtain ⟨x, s', hx, h⟩ := wm_run_bind_ok h
    exact hK' _ _ ((good_wFreshBool _ _).run _ _ _ hx) h
  · exact hK' _ _ (WalkOK.refl _ _) h⟩
/-- A laid-out `ite` walk is a `WalkOK` step for the names its arms declare, when the walks of
    its arms are. -/
private theorem wpIteLaid_good (κ : RE P) (d : Nat) (c : P.Expr) (tss ess : PStmts P)
    (hT : ∀ κ' fE, Good (stmtsInits tss ++ stmtsInits ess) (wpList κ' d fE tss))
    (hE : ∀ κ' fE, Good (stmtsInits tss ++ stmtsInits ess) (wpList κ' d fE ess)) :
    Good (stmtsInits tss ++ stmtsInits ess) (wpIteLaid κ d c tss ess) := by
  unfold wpIteLaid
  repeat' first | walkP_step | walk_step
/-- A real-branch `ite` walk is a `WalkOK` step for the names its arms declare, when the walks
    of its arms are. -/
private theorem wpIteReal_good (κ : RE P) (d : Nat) (c : P.Expr) (tss ess : PStmts P)
    (hT : ∀ κ' fE, Good (stmtsInits tss ++ stmtsInits ess) (wpList κ' d fE tss))
    (hE : ∀ κ' fE, Good (stmtsInits tss ++ stmtsInits ess) (wpList κ' d fE ess)) :
    Good (stmtsInits tss ++ stmtsInits ess) (wpIteReal κ d c tss ess) := by
  have hA : ∀ (s : WSt P) (lab : Std.HashMap String Nat) (pend : Std.HashMap String (List P.Ident)),
      (∀ l e, e ∈ pend.getD l [] → e ∈ s.pending.getD l []) →
      WalkCore (stmtsInits tss ++ stmtsInits ess) s
        { s with live := {}, labelDepth := lab, pending := pend } :=
    fun s _ _ hp => wcore% [w6 := fun l e h => .inl (hp l e h), w7 := fun _ _ _ h => by simp at h,
      liveOld := fun _ _ h _ => by simp at h]
  unfold wpIteReal
  refine ⟨fun st r st' h => ?_⟩
  run_peel h 2
  obtain ⟨E, s2, hE2, h⟩ := wm_run_bind_ok h
  have h12 := (hE _ _).run _ _ _ hE2
  run_peel h 2
  obtain ⟨T, s5, hT5, h⟩ := wm_run_bind_ok h
  have h45 := (hT _ _).run _ _ _ hT5
  run_peel h 2
  have h7 : WalkOK (stmtsInits tss ++ stmtsInits ess) _ st' :=
    Runs.run (by repeat' walk_step) _ _ _ h
  have hc2 := (hA st {} {} (by simp)).trans h12.toWalkCore
  have hc := (hc2.trans (hA s2 _ _ fun _ _ h => h)).trans h45.toWalkCore
  refine ⟨(?_ : WalkCore _ st _).trans h7.toWalkCore, fun l' => h7.labelDepth l',
    fun l' e he => h7.pending l' e he⟩
  refine { hc with wf := fun hw hd => ?_, liveOld := fun n t h ht => ?_ }
  rotate_left
  · have h4 := h45.liveOld n t
    have h1 := h12.liveOld n t
    grind [→ unionLive_getElem, hc2.clock]
  have hw5 := hc.wf hw hd
  have hw2 := hc2.wf hw hd
  refine { hw5 with pending_fresh := fun l' e he => ?_, live_stamp := fun n s hs => ?_ }
  · obtain ⟨b, j, rfl, hj⟩ := hw.pending_fresh l' e he
    exact ⟨b, j, rfl, Nat.lt_of_lt_of_le hj hc.next⟩
  · have h5 := hw5.live_stamp n s
    have h2 := hw2.live_stamp n s
    have h0 := hw.live_stamp n s
    grind [→ unionLive_getElem, h45.clock, hc.clock]
omit iL in
mutual
/-- A statement walk is a `WalkOK` step for the names the statement declares. -/
private theorem wpStmt_good [LawfulHasIdent P] (κ : RE P) (d : Nat) (f : Bool) :
    ∀ s : PStmt P, Good (stmtsInits [s]) (wpStmt κ d f s)
  | .block l body md => wpStmt_block_good κ d f l body md fun κ' => wpList_good κ' (d + 1) f body
  | .ite (.det c) tss ess md => by
    have hT := fun κ' fE => (wpList_good κ' d fE tss).mono (D' := stmtsInits tss ++ stmtsInits ess)
      (by simp_all)
    have hE := fun κ' fE => (wpList_good κ' d fE ess).mono (D' := stmtsInits tss ++ stmtsInits ess)
      (by simp_all)
    refine Good.mono (D := stmtsInits tss ++ stmtsInits ess) ?_ (by simp [stmtsInits])
    rw [wpStmt]
    split
    · exact wpIteLaid_good κ d c tss ess hT hE
    · exact wpIteReal_good κ d c tss ess hT hE
  | .cmd c => by
    rcases c with ((_ | _ | _ | _ | _) | _) <;> (try cases ‹ExprOrNondet P›) <;> unfold wpStmt <;>
      repeat' walk_step
  | .ite .nondet .. | .loop .. | .exit .. | .typeDecl .. => by
    unfold wpStmt
    repeat' walk_step
  termination_by structural s => s
/-- A statement-list walk is a `WalkOK` step for the names the list declares. -/
private theorem wpList_good [LawfulHasIdent P] (κ : RE P) (d : Nat) (fEnd : Bool) :
    ∀ ss : PStmts P, Good (stmtsInits ss) (wpList κ d fEnd ss)
  | [] => by simpa only [wpList] using runs_pure _
  | s :: rest => by
    have h1 := (wpList_good κ d fEnd rest).mono fun x hx =>
      stmtsInits_cons_eq s rest ▸ List.mem_append_right _ hx
    have h2 := fun f => (wpStmt_good κ d f s).mono fun x hx =>
      stmtsInits_cons_eq s rest ▸ List.mem_append_left _ hx
    simp only [wpList]
    repeat' walk_step
  termination_by structural ss => ss
end

/-- A run of `wRen e` is a `WalkCore` step declaring nothing. -/
theorem wRen_walk {e : P.Expr} {st st' : WSt P} {p : WExpr P × List P.Ident}
    (h : (wRen e).run st = .ok (p, st')) : WalkCore [] st st' := ((good_wRen [] e).run _ _ _ h).1
omit iW in
/-- A run of `wFreshBool b` is a `WalkCore` step declaring nothing. -/
theorem wFreshBool_walk {b : String} {st st' : WSt P} {x : P.Ident}
    (h : (wFreshBool b).run st = .ok (x, st')) : WalkCore [] st st' :=
  ((good_wFreshBool [] b).run _ _ _ h).1
/-- A run of `wFreshLike y` is a `WalkCore` step declaring nothing. -/
theorem wFreshLike_walk {y : P.Ident} {st st' : WSt P} {x : P.Ident}
    (h : (wFreshLike y).run st = .ok (x, st')) : WalkCore [] st st' :=
  ((good_wFreshLike [] y).run _ _ _ h).1
/-- A statement-list walk changes the state as `WalkOK` says, the declared variables being the
    `init`s of the list at any depth. -/
theorem wpList_walkOK {κ : RE P} {d : Nat} {fEnd : Bool} {ss : PStmts P} {st st' : WSt P}
    {r : WRes P} (h : (wpList κ d fEnd ss).run st = .ok (r, st')) :
    WalkOK (stmtsInits ss) st st' := (wpList_good κ d fEnd ss).run _ _ _ h
/-- A statement walk changes the state as `WalkOK` says, the declared variables being the
    `init`s of the statement at any depth. -/
theorem wpStmt_walkOK {κ : RE P} {d : Nat} {f : Bool} {s : PStmt P} {st st' : WSt P}
    {r : WRes P} (h : (wpStmt κ d f s).run st = .ok (r, st')) :
    WalkOK (stmtsInits [s]) st st' := (wpStmt_good κ d f s).run _ _ _ h
/-- A statement walk keeps the exit snapshots registered for each label. -/
theorem wpStmt_pending {κ : RE P} {d : Nat} {f : Bool} {s : PStmt P} {st st' : WSt P}
    {a : WRes P} (h : (wpStmt κ d f s).run st = .ok (a, st')) {l : String} {e : P.Ident}
    (he : e ∈ st.pending.getD l []) : e ∈ st'.pending.getD l [] := (wpStmt_walkOK h).pending l e he
/-- A statement-list walk keeps the exit snapshots registered for each label. -/
theorem wpList_pending {κ : RE P} {d : Nat} {fEnd : Bool} {ss : PStmts P} {st st' : WSt P}
    {r : WRes P} (h : (wpList κ d fEnd ss).run st = .ok (r, st')) {l : String} {e : P.Ident}
    (he : e ∈ st.pending.getD l []) : e ∈ st'.pending.getD l [] := (wpList_walkOK h).pending l e he
/-- A laid-out `ite` walk changes the state as `WalkOK` says, the declared variables being the
    `init`s of its arms at any depth. -/
theorem wpIteLaid_walkOK {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P}
    {st st' : WSt P} {r : WRes P} (h : (wpIteLaid κ d c tss ess).run st = .ok (r, st')) :
    WalkOK (stmtsInits tss ++ stmtsInits ess) st st' :=
  (wpIteLaid_good κ d c tss ess (fun κ' fE => (wpList_good κ' d fE tss).mono (by simp_all))
    (fun κ' fE => (wpList_good κ' d fE ess).mono (by simp_all))).run _ _ _ h
omit iW iL in
/-- A declared type of the input state of a walk step is kept by type maps `T` that keep the
    declared types of the output state except stale types of loop-free locals (of `Lc`) not yet
    declared and of fresh names not yet drawn, or is itself such a stale type; the declared
    names are loop-free locals avoided if they have the form of a fresh name. -/
theorem WalkCore.tys_final {D Lc : List P.Ident} {st st' : WSt P} (hw : WalkCore D st st')
    (hwf : WFSt st) (hd : ∀ x ∈ D, x ∈ Lc ∧ AvoidedIfFresh st x)
    {T : Std.HashMap P.Ident P.Ty}
    (hT : ∀ (n : P.Ident) ty, st'.tys[n]? = some ty → T[n]? = some ty ∨
      (n ∈ Lc ∧ (∀ b j, n = freshName b j → st'.avoid.contains n = true) ∧
        st'.taken.contains n = false) ∨
      ∃ b j, n = freshName b j ∧ st'.next ≤ j ∧ st'.avoid.contains n = false)
    {n : P.Ident} {ty : P.Ty} (hn : st.tys[n]? = some ty) : T[n]? = some ty ∨
      (n ∈ Lc ∧ (∀ b j, n = freshName b j → st.avoid.contains n = true) ∧
        st.taken.contains n = false) ∨
      ∃ b j, n = freshName b j ∧ st.next ≤ j ∧ st.avoid.contains n = false := by
  grind +splitImp [WalkCore, WFSt.nm_untyped, FreshAt, AvoidedIfFresh]

/-- A declared type of the input state of a statement walk is kept by type maps `T` that keep
    the declared types of the output state except stale types of loop-free locals not yet
    declared and of fresh names not yet drawn, or is itself such a stale type; the statement
    declares loop-free locals avoided if they have the form of a fresh name. -/
theorem wpStmt_tys {Lc : List P.Ident} {κ : RE P} {d : Nat} {f : Bool} {s : PStmt P}
    {st st' : WSt P} {a : WRes P} {T : Std.HashMap P.Ident P.Ty}
    (h : (wpStmt κ d f s).run st = .ok (a, st')) (hwf : WFSt st)
    (hd : ∀ x ∈ stmtsInits [s], x ∈ Lc ∧ ∀ b j, x = freshName b j → st.avoid.contains x = true)
    (hT : ∀ (n : P.Ident) ty, st'.tys[n]? = some ty → T[n]? = some ty ∨
      (n ∈ Lc ∧ (∀ b j, n = freshName b j → st'.avoid.contains n = true) ∧
        st'.taken.contains n = false) ∨
      ∃ b j, n = freshName b j ∧ st'.next ≤ j ∧ st'.avoid.contains n = false)
    {n : P.Ident} {ty : P.Ty} (hn : st.tys[n]? = some ty) : T[n]? = some ty ∨
      (n ∈ Lc ∧ (∀ b j, n = freshName b j → st.avoid.contains n = true) ∧
        st.taken.contains n = false) ∨
      ∃ b j, n = freshName b j ∧ st.next ≤ j ∧ st.avoid.contains n = false :=
  (wpStmt_walkOK h).1.tys_final hwf hd hT hn
/-- Facts of the top-level walk of a loop-free list `ss` well scoped from `S` from a state with
    no renamings and no recorded declarations, the variables of `S` of the form of a fresh name
    being avoided: every variable of `S` keeps its name and is not recorded as declared, the
    avoided names are unchanged, and the final declared type of a variable of `S` is its type
    in `tys0`. -/
theorem wpList_top_facts {ss : PStmts P} {Lc S : List P.Ident} (hwf : Block.WellScoped Lc S ss)
    {tys0 : Tys P} {st0 : WSt P} (h0 : st0.nm = {} ∧ st0.taken = {} ∧ st0.tyOf = {} ∧
      st0.tys = tys0.foldr (fun (x, ty) m => m.insert x ty) {})
    (hav : ∀ x ∈ S, ∀ b j, x = freshName b j → st0.avoid.contains x = true)
    {r : WRes P} {st1 : WSt P} (h : (wpList .top 0 false ss).run st0 = .ok (r, st1)) :
    (∀ x ∈ S, curName st1 x = some x ∧ st1.taken.contains x = false) ∧
    st1.avoid = st0.avoid ∧
    ∀ x ∈ S, ∀ ty, tyOfName st1.tys st1.tyOf x = .ok ty → tys0.get? x = some ty := by
  obtain ⟨hnm, htk, hto, hty⟩ := h0
  have hw := (wpList_walkOK h).1
  have hdis := wfl_inits_disjoint S ss hwf
  have hF : ∀ x ∈ S, ¬ FreshAt st0 x := fun x hx ⟨b, j, e, ha, _⟩ => by simp [hav x hx b j e] at ha
  have hget : ∀ x, st0.tys[x]? = tys0.get? x := by
    rw [hty]
    clear hty
    intro x
    induction tys0 <;> grind [Tys.get?]
  refine ⟨fun x hx => ?_, hw.avoid, fun x hx ty hty' => ?_⟩
  · have hc := hw.names x x (hdis x hx) (by simp [curName, hnm, htk])
    grind [curName, WalkCore]
  · have e1 : st1.tys[x]? = st0.tys[x]? := Classical.byContradiction fun e => by grind [WalkCore]
    have e2 : st1.tyOf[x]? = st0.tyOf[x]? :=
      Classical.byContradiction fun e => hF x hx (hw.tyOf x e)
    cases hg : tys0.get? x <;> simp_all [tyOfName, pure, Except.pure]
/-- After the top-level walk of a list well scoped from `S` from a state with the initial
    types `tys0`, every variable of `S` with a type in `tys0` has that final type. -/
theorem wpList_top_tyOfName {ss : PStmts P} {Lc S : List P.Ident}
    (hwf : Block.WellScoped Lc S ss) {tys0 : Tys P} {st0 : WSt P}
    (h0 : st0.nm = {} ∧ st0.taken = {} ∧ st0.tyOf = {} ∧
      st0.tys = tys0.foldr (fun (x, ty) m => m.insert x ty) {})
    (hav : ∀ x ∈ S, ∀ b j, x = freshName b j → st0.avoid.contains x = true)
    {r : WRes P} {st1 : WSt P} (h : (wpList .top 0 false ss).run st0 = .ok (r, st1)) :
    ∀ x ∈ S, ∀ ty, tys0.get? x = some ty → tyOfName st1.tys st1.tyOf x = .ok ty := by
  obtain ⟨hnm, htk, hto, hty⟩ := h0
  have hw := (wpList_walkOK h).1
  have hdis := wfl_inits_disjoint S ss hwf
  have hF : ∀ x ∈ S, ¬ FreshAt st0 x := fun x hx ⟨b, j, e, ha, _⟩ => by simp [hav x hx b j e] at ha
  have hget : ∀ x, st0.tys[x]? = tys0.get? x := by
    rw [hty]
    clear hty
    intro x
    induction tys0 <;> grind [Tys.get?]
  intro x hx ty hg
  have e1 : st1.tys[x]? = st0.tys[x]? := Classical.byContradiction fun e => by grind [WalkCore]
  simp_all [tyOfName, pure, Except.pure]

/-! ## Live names under a variable reach context -/
end

/-- The facts a walk keeps about the variable `z` with current name `m`: `z` is not declared by
    the fragment (`D`), the state is well formed, `m` is the current name of `z`, and `z` and the
    declared names of `D` are avoided when they have the form of a fresh name. -/
private def LInv (D : List P.Ident) (z m : P.Ident) (st : WSt P) : Prop :=
  z ∉ D ∧ WFSt st ∧ curName st z = some m ∧ AvoidedIfFresh st z ∧ ∀ x ∈ D, AvoidedIfFresh st x

/-- `m` stays in the live set. -/
private def LMR (m : P.Ident) (st st' : WSt P) : Prop :=
  st.live.contains m = true → st'.live.contains m = true

/-- From a state with `LInv D z m`, the state keeps it and the avoided names, and keeps `m` in the
    live set. -/
private def LGR (D : List P.Ident) (z m : P.Ident) (st st' : WSt P) : Prop :=
  LInv D z m st → LInv D z m st' ∧ st'.avoid = st.avoid ∧ LMR m st st'

private local instance (m : P.Ident) : RunRel (LMR m) := ⟨fun _ => id, fun h1 h2 => h2 ∘ h1⟩

private local instance (D : List P.Ident) (z m : P.Ident) : RunRel (LGR D z m) :=
  ⟨fun _ h => ⟨h, rfl, id⟩, fun h1 h2 hi => (h1 hi).elim fun hi1 ⟨ha1, hl1⟩ =>
    (h2 hi1).imp_right fun ⟨ha2, hl2⟩ => ⟨ha2.trans ha1, hl2 ∘ hl1⟩⟩

/-- Every successful run of `c` keeps `LInv D z m` and the avoided names, and keeps `m` in the
    live set. -/
private abbrev LG {α : Type} (D : List P.Ident) (z m : P.Ident) (c : WM P α) : Prop :=
  Runs (LGR D z m) c

/-- Every successful run of `c` keeps `m` in the live set. -/
private abbrev LM {α : Type} (m : P.Ident) (c : WM P α) : Prop := Runs (LMR m) c

/-- A `WalkCore` step keeps `LInv`. -/
private theorem LInv.of_walk {D : List P.Ident} {z m : P.Ident} {st st' : WSt P}
    (h : LInv D z m st) (hw : WalkCore D st st') : LInv D z m st' :=
  let ⟨hz, hw', hc, ha, hd⟩ := h
  ⟨hz, hw.wf hw' hd, hw.names z m hz hc, fun b j he => hw.avoid ▸ ha b j he,
    fun x hx b j he => hw.avoid ▸ hd x hx b j he⟩
/-- `LInv` for declared names `D'` gives `LInv` for fewer declared names. -/
private theorem LInv.mono {D D' : List P.Ident} {z m : P.Ident} {st : WSt P}
    (h : LInv D' z m st) (hD : ∀ x ∈ D, x ∈ D') : LInv D z m st :=
  let ⟨hz, hw, hc, ha, hd⟩ := h
  ⟨fun h' => hz (hD _ h'), hw, hc, ha, fun x hx => hd x (hD x hx)⟩
/-- An `LG` computation for declared names `D` is one for any list containing `D`. -/
private theorem LG.mono {α : Type} {D D' : List P.Ident} {z m : P.Ident} {c : WM P α}
    (h : LG D z m c) (hD : ∀ x ∈ D, x ∈ D') : LG D' z m c := ⟨fun _ _ _ hr hI =>
  let ⟨hz, _, _, _, hd⟩ := hI
  let ⟨⟨_, hw, hc, ha, _⟩, hav, hl⟩ := h.run _ _ _ hr (hI.mono hD)
  ⟨⟨hz, hw, hc, ha, fun x hx b j he => hav ▸ hd x hx b j he⟩, hav, hl⟩⟩
/-- A `WalkOK` step keeping `m` live is an `LG` computation. -/
private theorem lg_of_good {α : Type} {D : List P.Ident} {z m : P.Ident} {c : WM P α}
    (g : Good D c) (hl : LM m c) : LG D z m c :=
  ⟨fun _ _ _ hr hi => ⟨hi.of_walk (g.run _ _ _ hr).1, (g.run _ _ _ hr).avoid, hl.run _ _ _ hr⟩⟩
/-- `liveAdd` keeps every live name. -/
private theorem lm_liveAdd (m : P.Ident) (xs : List P.Ident) : LM m (liveAdd xs : WM P Unit) :=
  ⟨fun _ _ _ h hm =>
  let ⟨_, _, he, hc⟩ := liveAdd_step h
  he ▸ (hc m).2 (.inl hm)⟩
/-- `wFreshBool` keeps the live set. -/
private theorem lm_wFreshBool (m : P.Ident) (b : String) : LM m (wFreshBool b : WM P P.Ident) :=
  ⟨fun st _ _ h hl => (Prod.mk.inj (Except.ok.inj ((wFreshBool_run b st).symm.trans h))).2 ▸ hl⟩

include iW in
/-- `wFreshLike` keeps the live set. -/
private theorem lm_wFreshLike (m : P.Ident) (x : P.Ident) : LM m (wFreshLike x : WM P P.Ident) :=
  ⟨fun st _ _ h hl => (Prod.mk.inj (Except.ok.inj ((wFreshLike_run x st).symm.trans h))).2 ▸ hl⟩

include iW iL in
/-- `wName` keeps the live set. -/
private theorem lm_wName (m : P.Ident) (x : P.Ident) : LM m (wName x : WM P P.Ident) :=
  ⟨fun _ _ _ h hl => (wName_state h).2 ▸ hl⟩

include iW iL in
/-- `wRen` keeps the live set. -/
private theorem lm_wRen (m : P.Ident) (e : P.Expr) :
    LM m (wRen e : WM P (WExpr P × List P.Ident)) := ⟨fun _ _ _ h hm => (wRen_run h).2.2.1 ▸ hm⟩

/-- One step of the `LM` decomposition of a computation. -/
local macro "lm_step" : tactic => `(tactic| first
  | head_let
  | head_split
  | run_step
  | prim lm
  | (on_head modify; exact runs_modify fun _ => id))

include iW in
/-- `saveRestore` keeps the live set. -/
private theorem lm_saveRestore (m : P.Ident) (xs : List P.Ident) :
    LM m (saveRestore xs : WM P _) := by
  unfold saveRestore
  repeat' lm_step
include iW iL in
/-- `saveRestore` followed by computations that are `GoodPre` for its copies and keep `m` live
    is an `LG` computation. -/
private theorem lg_bind_sr {β : Type} {D : List P.Ident} {z m : P.Ident} {xs : List P.Ident}
    {f : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) × List (P.Ident × P.Ident) → WM P β}
    (hf : ∀ r, GoodPre D (r.2.2.2.map Prod.snd) (f r) ∧ LM m (f r)) :
    LG D z m (saveRestore xs >>= f) :=
  lg_of_good (good_bind_sr fun r => (hf r).1) (runs_bind (lm_saveRestore m xs) fun r => (hf r).2)
/-- Removing a name other than `m` from the live set is an `LG` computation. -/
private theorem lg_liveDel {D : List P.Ident} {z m n : P.Ident} (hn : n ≠ m) :
    LG D z m (liveDel n : WM P Unit) :=
  runs_modify fun st hi => ⟨hi.of_walk ((good_liveDel D n).run _ _ _ (liveDel_run n st)).1, rfl,
    fun hm => by simp [Std.HashMap.contains_erase, hm, hn]⟩
/-- A computation returning a name other than `m` that may get a declared type, keeping the live
    set, followed by giving it a type and by `LG` computations, is an `LG` computation. -/
private theorem lg_ins {β : Type} {D : List P.Ident} {z m : P.Ident} {c : WM P P.Ident}
    {ty : P.Ty} {k : P.Ident → PUnit → WM P β} {Q : P.Ident → Prop}
    (hc : ∀ st a st', c.run st = .ok (a, st') → LInv D z m st →
      WalkOK D st st' ∧ (WFSt st → (∀ y ∈ D, AvoidedIfFresh st y) → TyKey st' a) ∧
      st'.live = st.live ∧ Q a)
    (hk : ∀ a, Q a → ∀ u, LG D z m (k a u)) :
    LG D z m (c >>= fun a => modify (fun st => { st with tys := st.tys.insert a ty }) >>= k a) := by
  refine ⟨fun st r st' h hi => ?_⟩
  obtain ⟨a, s1, h1, h⟩ := wm_run_bind_ok h
  run_peel h
  obtain ⟨hw1, hT, hl, ham⟩ := hc st a s1 h1 hi
  obtain ⟨hz, hW1, hc1, hzA, hA1⟩ := hi.of_walk hw1.1
  obtain ⟨-, hW, -, -, hA⟩ := hi
  obtain ⟨hi3, ha3, hl3⟩ := (hk a ham ()).run _ _ _ h ⟨hz, hW1.ins_ty (hT hW hA) ty, hc1, hzA, hA1⟩
  exact ⟨hi3, ha3.trans hw1.avoid, fun hm => hl3 (hl ▸ hm)⟩
include iW iL in
/-- Declaring `x ∈ D` and giving the returned name (not `m`) a type, followed by `LG`
    computations, is an `LG` computation. -/
private theorem lg_declTy {β : Type} {D : List P.Ident} {z m x : P.Ident} {ty : P.Ty}
    {k : P.Ident → PUnit → WM P β} (hx : x ∈ D) (hk : ∀ a, a ≠ m → ∀ u, LG D z m (k a u)) :
    LG D z m (wDecl x >>= fun a => modify (fun st => { st with tys := st.tys.insert a ty }) >>=
      k a) :=
  lg_ins (fun st a st' h hi => by
    obtain ⟨⟨s1, h2⟩, -, -, -, he⟩ := wDecl_spec h
    refine ⟨(walk_wDecl hx h).1, (walk_wDecl hx h).2.2, by rw [he], ?_⟩
    rintro rfl
    obtain ⟨hz, hW, hcur, hzA, hA⟩ := hi
    obtain ⟨k, hfk, -, hle, -, -, -, hav, -⟩ := fresh_run (b := baseOf x) (st := st)
    have hxz : x ≠ z := fun e => hz (e ▸ hx)
    rcases wName_cases h2 with ⟨h3, -⟩ | ⟨h3, h4, rfl, -⟩ | ⟨h3, h4, rfl, -⟩
    · rcases curName_cases hcur with h5 | ⟨-, -, rfl⟩
      · exact hxz (hW.nm_inj x z _ h3 h5)
      · obtain ⟨-, b, j, e, -, ha⟩ := hW.nm_fresh x _ h3
        simp [hzA b j e] at ha
    · rcases curName_cases hcur with h5 | ⟨-, -, rfl⟩
      · obtain ⟨-, b, j, e, -, ha⟩ := hW.nm_fresh z _ h5
        simp [hA _ hx b j e] at ha
      · exact hxz rfl
    · rcases curName_cases hcur with h5 | ⟨-, -, e⟩
      · obtain ⟨-, b, j, e, hj, -⟩ := hW.nm_fresh z _ h5
        exact absurd (freshName_counter_inj (hfk.symm.trans e)) (by omega)
      · rw [e] at hav
        simp [hzA _ _ (e.symm.trans hfk)] at hav) hk
include iL in
/-- Drawing a fresh name and giving it a type, followed by `LG` computations, is an `LG`
    computation. -/
private theorem lg_freshTy {β : Type} {D : List P.Ident} {z m : P.Ident} {b : String} {ty : P.Ty}
    {k : P.Ident → PUnit → WM P β} (hk : ∀ a u, LG D z m (k a u)) :
    LG D z m (wFresh b >>= fun a => modify (fun st => { st with tys := st.tys.insert a ty }) >>=
      k a) :=
  lg_ins (Q := fun _ => True) (fun st _ _ h _ => ⟨(walk_wFresh h).1, (walk_wFresh h).2.2,
    by cases (wFresh_run b st).symm.trans h; rfl, trivial⟩) fun a _ => hk a
include iL in
/-- Drawing a fresh Boolean name and registering it as an exit snapshot, followed by `LG`
    computations, is an `LG` computation. -/
private theorem lg_pend {β : Type} {D : List P.Ident} {z m : P.Ident} {b l : String}
    {k : P.Ident → PUnit → WM P β} (hk : ∀ a u, LG D z m (k a u)) :
    LG D z m (wFreshBool b >>= fun a =>
      modify (fun st => { st with pending := st.pending.insert l (a :: st.pending.getD l []) }) >>=
        k a) :=
  runs_bind_modify (fun st a s1 h1 hi => ⟨hi.of_walk (walk_pend h1).1,
    (walk_pend (D := D) h1).avoid, (lm_wFreshBool m b).run st a s1 h1⟩) hk

/-- One step of the `LG` decomposition of a walk. -/
local macro "lg_step" : tactic => `(tactic| first
  | head_let
  | head_split
  | (on_head wDecl
     with_reducible_and_instances apply lg_declTy (by simp [stmtsInits])
     intro _ _ _)
  | (on_head wFresh; with_reducible_and_instances apply lg_freshTy; intro _ _)
  | (on_head wFreshBool; with_reducible_and_instances apply lg_pend; intro _ _)
  | run_step
  | (apply lg_of_good; prim good; prim lm)
  | (on_head liveDel; with_reducible_and_instances apply lg_liveDel; assumption)
  | (on_head modify
     exact lg_of_good (good_modify _ _ fun _ => ⟨rfl, fun _ _ h => h⟩) (runs_modify fun _ => id))
  | contradiction)


/-- A computation using a join point on contexts and optional names, all of whose calls on a
    variable context are `LG` computations, with the join point being one on variable contexts,
    is an `LG` computation. -/
private theorem LGR.jp_pair {β γ : Type} {D : List P.Ident} {z m : P.Ident}
    {v : RE P × Option P.Ident → WM P β} {b : (RE P × Option P.Ident → WM P β) → WM P γ}
    (hv : ∀ x, x.1 ≠ .top → LG D z m (v x))
    (hb : ∀ jp : RE P × Option P.Ident → WM P β, (∀ x, x.1 ≠ .top → LG D z m (jp x)) →
      LG D z m (b jp)) : LG D z m (b v) := hb v hv
omit iDE iLB iBo iFv iSu iId iFs in
/-- A fold over a list of stamped names whose step keeps the names of the live set and adds the
    step's name contains the names of the start and of the list. -/
private theorem foldl_contains
    (f : Std.HashMap P.Ident Nat → P.Ident × Nat → Std.HashMap P.Ident Nat)
    (hf : ∀ m p n, (f m p).contains n = true ↔ m.contains n = true ∨ n = p.1) :
    ∀ (l : List (P.Ident × Nat)) (m : Std.HashMap P.Ident Nat) (n : P.Ident),
    (l.foldl f m).contains n = true ↔ m.contains n = true ∨ ∃ s, (n, s) ∈ l := fun l => by
  induction l <;> grind

omit iBo iFv iSu iId iFs in
/-- The union of two live sets contains the names of both. -/
theorem unionLive_contains {a b : Std.HashMap P.Ident Nat} {n : P.Ident} :
    (unionLive a b).contains n = true ↔ a.contains n = true ∨ b.contains n = true := by
  unfold unionLive
  split <;> rw [Std.HashMap.fold_eq_foldl_toList, foldl_contains _ fun m p n => by
    split <;> (try split) <;> grind]
  all_goals simp only [Std.HashMap.mem_toList_iff_getElem?_eq_some,
    Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists]
  exact Or.comm
include iW iL in
/-- A real-branch `ite` walk is an `LG` computation. -/
private theorem wpIteReal_lg (κ : RE P) (d : Nat) (c : P.Expr) (tss ess : PStmts P)
    (z m : P.Ident) : LG (stmtsInits tss ++ stmtsInits ess) z m (wpIteReal κ d c tss ess) := by
  refine lg_of_good (wpIteReal_good κ d c tss ess (fun _ _ => (wpList_good _ d _ tss).mono
    fun _ => List.mem_append_left _) fun _ _ => (wpList_good _ d _ ess).mono fun _ =>
      List.mem_append_right _) ⟨fun st a st' h hm => ?_⟩
  unfold wpIteReal at h
  run_peel h 2
  obtain ⟨E, s1, -, h⟩ := wm_run_bind_ok h
  run_peel h 2
  obtain ⟨T, s2, -, h⟩ := wm_run_bind_ok h
  run_peel h 2
  refine (?_ : LM m _).run _ _ _ h (unionLive_contains.2 (.inr hm))
  repeat' lm_step
include iW iL in
/-- Under a variable reach context, a laid-out `ite` walk is an `LG` computation when the walks
    of its arms under variable contexts are. -/
private theorem wpIteLaid_lg (κ : RE P) (hκ : κ ≠ .top) (d : Nat) (c : P.Expr)
    (tss ess : PStmts P) (z m : P.Ident)
    (hT' : ∀ κ', κ' ≠ .top → ∀ fE, LG (stmtsInits tss ++ stmtsInits ess) z m (wpList κ' d fE tss))
    (hE' : ∀ κ', κ' ≠ .top → ∀ fE, LG (stmtsInits tss ++ stmtsInits ess) z m (wpList κ' d fE ess)) :
    LG (stmtsInits tss ++ stmtsInits ess) z m (wpIteLaid κ d c tss ess) := by
  unfold wpIteLaid
  repeat' first
    | (with_reducible_and_instances apply lg_bind_sr; intro _; refine ⟨?_, ?_⟩)
    | (intros; goal_head LGR; lg_step)
    | (intros; goal_head PreOK; walkP_step)
    | (intros; goal_head LMR; lm_step)
    | (apply hE'; assumption)
    | (apply_assumption; nofun)
include iW in
mutual
/-- Under a variable reach context, a statement walk is an `LG` computation. -/
private theorem wpStmt_lg [LawfulHasIdent P] (κ : RE P) (hκ : κ ≠ .top) (d : Nat) (f : Bool)
    (z m : P.Ident) :
    ∀ s : PStmt P, LG (stmtsInits [s]) z m (wpStmt κ d f s)
  | .cmd c => by
    rcases c with (⟨_, _, _ | _, _⟩ | ⟨_, _ | _, _⟩ | _ | _ | _) | _ <;> unfold wpStmt <;>
      repeat' lg_step
  | .typeDecl _ _ | .loop _ _ _ _ _ | .ite .nondet _ _ _ | .exit _ _ => by
    unfold wpStmt
    repeat' lg_step
  | .block l body md => by
    have hB := wpList_lg κ hκ (d + 1) f z m body
    refine ⟨fun st a st' h hi => ?_⟩
    have hw := (wpStmt_block_good κ d f l body md fun κ' => wpList_good κ' (d + 1) f body).run
      _ _ _ h
    refine ⟨hi.of_walk hw.1, hw.avoid, fun hm => ?_⟩
    have hi0 := ((hi.mono fun x hx => by simp [stmtsInits, hx]).of_walk
      (WalkCore.blkIn (stmtsInits body) st l (d + 1)))
    simp only [wpStmt] at h
    run_peel h 3
    obtain ⟨B, s2, h2, h⟩ := wm_run_bind_ok h
    run_peel h 2
    refine (?_ : LM m _).run _ _ _ h ((hB.run _ _ _ h2 hi0).2.2 hm)
    repeat' lm_step
  | .ite (.det c) tss ess md => by
    have hT' := fun κ' h fE => (wpList_lg κ' h d fE z m tss).mono fun x =>
      List.mem_append_left (stmtsInits ess)
    have hE' := fun κ' h fE => (wpList_lg κ' h d fE z m ess).mono fun x =>
      List.mem_append_right (stmtsInits tss)
    simp only [wpStmt]
    split
    · exact (wpIteLaid_lg κ hκ d c tss ess z m hT' hE').mono (by simp [stmtsInits])
    · exact (wpIteReal_lg κ d c tss ess z m).mono (by simp [stmtsInits])
  termination_by structural s => s
/-- Under a variable reach context, a statement-list walk is an `LG` computation. -/
private theorem wpList_lg [LawfulHasIdent P] (κ : RE P) (hκ : κ ≠ .top) (d : Nat) (fEnd : Bool)
    (z m : P.Ident) :
    ∀ ss : PStmts P, LG (stmtsInits ss) z m (wpList κ d fEnd ss)
  | [] => by simpa only [wpList] using runs_pure _
  | s :: rest => by
    have h1 := (wpList_lg κ hκ d fEnd z m rest).mono fun x hx =>
      stmtsInits_cons_eq s rest ▸ List.mem_append_right _ hx
    have h2 := fun f => (wpStmt_lg κ hκ d f z m s).mono fun x hx =>
      stmtsInits_cons_eq s rest ▸ List.mem_append_left _ hx
    simp only [wpList]
    repeat' lg_step
  termination_by structural ss => ss
end

include iW iL in
/-- Under a variable reach context, a statement-list walk from a well-formed state keeps in the
    live set the live current name `m` of a variable `z` the list does not declare, when `z` and
    the declared variables are avoided if they have the form of a fresh name. -/
theorem wpList_live_keep {κ : RE P} {d : Nat} {fEnd : Bool} {ss : PStmts P} {st st' : WSt P}
    {r : WRes P} (h : (wpList κ d fEnd ss).run st = .ok (r, st')) (hκ : κ ≠ .top)
    (hwf : WFSt st) (hd : ∀ x ∈ stmtsInits ss, AvoidedIfFresh st x) :
    ∀ z m, z ∉ stmtsInits ss → AvoidedIfFresh st z → curName st z = some m →
      st.live.contains m = true → st'.live.contains m = true := fun z m hz hav hc hl =>
  ((wpList_lg κ hκ d fEnd z m ss).run _ _ _ h ⟨hz, hwf, hc, hav, hd⟩).2.2 hl
/-! ## Keys of the live set -/

/-- A name that may be a key of the live set of the walk state `st`: avoided if it has the form
    of a fresh name, or a fresh name with a counter below `st.next`. -/
@[expose] def KeyOK (st : WSt P) (n : P.Ident) : Prop :=
  AvoidedIfFresh st n ∨ ∃ b j, n = freshName b j ∧ j < st.next

/-- Every key of the live set of `st` is a `KeyOK` name. -/
@[expose] def LiveKeys (st : WSt P) : Prop :=
  ∀ (n : P.Ident) (s : Nat), st.live[n]? = some s → KeyOK st n

/-- `KeyOK` is kept by a state change keeping the avoided names and not decreasing the
    counter. -/
theorem KeyOK.of_le {st st' : WSt P} {n : P.Ident} (ha : st'.avoid = st.avoid)
    (hn : st.next ≤ st'.next) (h : KeyOK st n) : KeyOK st' n :=
  h.imp (fun h b j e => ha ▸ h b j e) fun ⟨b, j, e, hj⟩ => ⟨b, j, e, Nat.lt_of_lt_of_le hj hn⟩
/-- A state with an empty live set satisfies `LiveKeys`. -/
theorem liveKeys_empty {st : WSt P} (h : st.live = {}) : LiveKeys st :=
  fun n s hs => by simp [h] at hs
/-- The facts a walk keeps for the live keys: the recorded renamings are fresh names with a
    counter below `st.next`, the live keys are `KeyOK`, and the identifiers `Ids` are avoided if
    they have the form of a fresh name. -/
private def KI (Ids : List P.Ident) (st : WSt P) : Prop :=
  (∀ x n : P.Ident, st.nm[x]? = some n → ∃ b j, n = freshName b j ∧ j < st.next) ∧
    LiveKeys st ∧ ∀ x ∈ Ids, AvoidedIfFresh st x

/-- From a state whose names of `L` are `KeyOK`, the state keeps `KI Ids` and the avoided names,
    and the counter does not decrease. -/
private def KGR (Ids L : List P.Ident) (st st' : WSt P) : Prop :=
  KI Ids st → (∀ y ∈ L, KeyOK st y) → KI Ids st' ∧ st'.avoid = st.avoid ∧ st.next ≤ st'.next

private local instance (Ids L : List P.Ident) : RunRel (KGR Ids L) :=
  ⟨fun _ hi _ => ⟨hi, rfl, Nat.le_refl _⟩, fun h1 h2 hi hk => (h1 hi hk).elim fun hi1 ⟨ha1, hn1⟩ =>
    (h2 hi1 fun y hy => (hk y hy).of_le ha1 hn1).imp_right fun ⟨ha2, hn2⟩ =>
      ⟨ha2.trans ha1, Nat.le_trans hn1 hn2⟩⟩

/-- Every successful run of `c` from a state whose names of `L` are `KeyOK` keeps `KI Ids`
    and the avoided names, and does not decrease the counter. -/
private abbrev KG {α : Type} (Ids L : List P.Ident) (c : WM P α) : Prop := Runs (KGR Ids L) c

/-- A `KG` computation for the names `L` is one for any list containing them. -/
private theorem KG.monoL {α : Type} {Ids L L' : List P.Ident} {c : WM P α} (h : KG Ids L c)
    (hL : ∀ y ∈ L, y ∈ L') : KG Ids L' c :=
  h.imp fun _ _ h1 hi hk => h1 hi fun y hy => hk y (hL y hy)
/-- A `KG` computation for the identifiers `Ids` is one for any list containing them. -/
private theorem KG.monoI {α : Type} {Ids Ids' L : List P.Ident} {c : WM P α} (h : KG Ids L c)
    (hI : ∀ x ∈ Ids, x ∈ Ids') : KG Ids' L c := by
  refine h.imp fun _ _ h1 ⟨k1, k2, k3⟩ hk => ?_
  obtain ⟨⟨h1', h2', -⟩, ha, hn⟩ := h1 ⟨k1, k2, fun x hx => k3 x (hI x hx)⟩ hk
  exact ⟨⟨h1', h2', fun x hx b j e => ha ▸ k3 x hx b j e⟩, ha, hn⟩
/-- A computation returning `KeyOK` names `ext a`, followed by `KG` computations for those
    names, is a `KG` computation. -/
private theorem kg_bind_ext {α β : Type} {Ids L : List P.Ident} {x : WM P α} {f : α → WM P β}
    (ext : α → List P.Ident)
    (hx : ∀ st a st', x.run st = .ok (a, st') → KI Ids st → KI Ids st' ∧ st'.avoid = st.avoid ∧
      st.next ≤ st'.next ∧ ∀ y ∈ ext a, KeyOK st' y)
    (hf : ∀ a, KG Ids (L ++ ext a) (f a)) : KG Ids L (x >>= f) :=
  ⟨fun _ _ _ h hi hL => (wm_run_bind_ok h).elim fun a ⟨_, h1, h2⟩ =>
  let ⟨i1, a1, n1, he⟩ := hx _ _ _ h1 hi
  let ⟨i2, a2, n2⟩ := (hf a).run _ _ _ h2 i1 fun y hy =>
    (List.mem_append.1 hy).elim (fun hy => (hL y hy).of_le a1 n1) (he y)
  ⟨i2, a2.trans a1, Nat.le_trans n1 n2⟩⟩
/-- A state change keeping the avoided names, the counter, the renamings and the live set keeps
    `KI`. -/
private theorem KI.of_frame {Ids : List P.Ident} {st st' : WSt P} (hi : KI Ids st)
    (h1 : st'.avoid = st.avoid) (h2 : st'.next = st.next) (h3 : st'.nm = st.nm)
    (h4 : ∀ (n : P.Ident) (t : Nat), st'.live[n]? = some t → st.live[n]? = some t) :
    KI Ids st' :=
  ⟨fun x n hx => by rw [h2]; exact hi.1 x n (h3 ▸ hx),
    fun n t ht => KeyOK.of_le h1 (Nat.le_of_eq h2.symm) (hi.2.1 n t (h4 n t ht)),
    fun x hx b j he => h1 ▸ hi.2.2 x hx b j he⟩

/-- A `modify` keeping the avoided names, the counter and the renamings and adding no live entry
    is a `KG` computation. -/
private theorem kg_modify (Ids L : List P.Ident) (g : WSt P → WSt P)
    (h : ∀ st, (g st).avoid = st.avoid ∧ (g st).next = st.next ∧ (g st).nm = st.nm ∧
      ∀ (n : P.Ident) (t : Nat), (g st).live[n]? = some t → st.live[n]? = some t) :
    KG Ids L (modify g : WM P Unit) :=
  runs_modify fun st hi _ => match h st with
    | ⟨h1, h2, h3, h4⟩ => ⟨hi.of_frame h1 h2 h3 h4, h1, Nat.le_of_eq h2.symm⟩

/-- `liveDel` is a `KG` computation. -/
private theorem kg_liveDel (Ids L : List P.Ident) (x : P.Ident) :
    KG Ids L (liveDel x : WM P Unit) :=
  kg_modify Ids L _ fun _ => ⟨rfl, rfl, rfl, fun _ _ h => by grind⟩
/-- Adding names of `L` to the live set is a `KG` computation. -/
private theorem kg_liveAdd {Ids L : List P.Ident} {xs : List P.Ident} (hx : ∀ y ∈ xs, y ∈ L) :
    KG Ids L (liveAdd xs : WM P Unit) := by
  refine ⟨fun st _ st' hr ⟨h1, h2, h3⟩ hk => ?_⟩
  obtain ⟨live, clock, h, hc, -⟩ := liveAdd_run xs st
  cases h.symm.trans hr
  refine ⟨⟨h1, fun n t ht => ?_, h3⟩, rfl, Nat.le_refl _⟩
  grind [LiveKeys, KeyOK, AvoidedIfFresh, Std.HashMap.contains_eq_isSome_getElem?,
    Option.isSome_iff_exists]
include iL in
/-- A run of `wFresh` keeps `KI`, and its result is `KeyOK`. -/
private theorem kx_wFresh {Ids : List P.Ident} {b : String} {st st' : WSt P} {a : P.Ident}
    (h : (wFresh b).run st = .ok (a, st')) (hi : KI Ids st) :
    KI Ids st' ∧ st'.avoid = st.avoid ∧ st.next ≤ st'.next ∧ ∀ y ∈ [a], KeyOK st' y := by
  rw [wFresh_run] at h
  cases h
  obtain ⟨k, h1, h2, hle, -⟩ := fresh_run (b := b) (st := st)
  simp only [h1, h2] at *
  grind [KI, LiveKeys, KeyOK, AvoidedIfFresh]

include iL in
/-- A run of `wFreshBool` keeps `KI`, and its result is `KeyOK`. -/
private theorem kx_wFreshBool {Ids : List P.Ident} {b : String} {st st' : WSt P} {a : P.Ident}
    (h : (wFreshBool b).run st = .ok (a, st')) (hi : KI Ids st) :
    KI Ids st' ∧ st'.avoid = st.avoid ∧ st.next ≤ st'.next ∧ ∀ y ∈ [a], KeyOK st' y := by
  cases (wFreshBool_run b st).symm.trans h
  exact (kx_wFresh (wFresh_run b st) hi :)
include iL in
/-- `wFresh` is a `KG` computation. -/
private theorem kg_wFresh (Ids L : List P.Ident) (b : String) :
    KG Ids L (wFresh b : WM P P.Ident) :=
  ⟨fun _ _ _ hr hi _ => (kx_wFresh hr hi).imp_right fun h => ⟨h.1, h.2.1⟩⟩

section
include iW iL
/-- A run of `wFreshLike` keeps `KI`, and its result is `KeyOK`. -/
private theorem kx_wFreshLike {Ids : List P.Ident} {x : P.Ident} {st st' : WSt P} {a : P.Ident}
    (h : (wFreshLike x).run st = .ok (a, st')) (hi : KI Ids st) :
    KI Ids st' ∧ st'.avoid = st.avoid ∧ st.next ≤ st'.next ∧ ∀ y ∈ [a], KeyOK st' y := by
  cases (wFreshLike_run x st).symm.trans h
  exact (kx_wFresh (wFresh_run _ st) hi :)
/-- A run of `wName x` keeps `KI`. -/
private theorem ki_wName {Ids : List P.Ident} {x : P.Ident} {st st' : WSt P} {a : P.Ident}
    (h : (wName x).run st = .ok (a, st')) (hi : KI Ids st) :
    KI Ids st' ∧ st'.avoid = st.avoid ∧ st.next ≤ st'.next := by
  obtain ⟨k, hk1, hk2, hle, -⟩ := fresh_run (b := baseOf x) (st := st)
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, h3, rfl⟩
  all_goals simp only [hk1, hk2] at *
  all_goals grind [KI, LiveKeys, KeyOK, AvoidedIfFresh]

/-- A run of `wName x` for an identifier `x` of `Ids` keeps `KI`, and its result is `KeyOK`. -/
private theorem kx_wName {Ids : List P.Ident} {x : P.Ident} (hx : x ∈ Ids) {st st' : WSt P}
    {a : P.Ident} (h : (wName x).run st = .ok (a, st')) (hi : KI Ids st) :
    KI Ids st' ∧ st'.avoid = st.avoid ∧ st.next ≤ st'.next ∧ ∀ y ∈ [a], KeyOK st' y := by
  obtain ⟨k, hk1, hk2, -, -⟩ := fresh_run (b := baseOf x) (st := st)
  have hk := ki_wName h hi
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, h3, rfl⟩
  all_goals simp only [hk1, hk2] at *
  all_goals grind [KI, KeyOK]

/-- `wDecl` is a `KG` computation. -/
private theorem kg_wDecl (Ids L : List P.Ident) (x : P.Ident) :
    KG Ids L (wDecl x : WM P P.Ident) := ⟨fun st a st' h hi _ => by
  obtain ⟨n1, s1, h1⟩ := wName_ok x st
  cases (wDecl_run h1).symm.trans h
  obtain ⟨⟨hn, hl, hd⟩, ha, hle⟩ := ki_wName h1 hi
  exact ⟨⟨fun y n hy => hn y n (by grind), hl, hd⟩, ha, hle⟩⟩
/-- `wName` is a `KG` computation. -/
private theorem kg_wName (Ids L : List P.Ident) (x : P.Ident) :
    KG Ids L (wName x : WM P P.Ident) := ⟨fun _ _ _ h hi _ => ki_wName h hi⟩
end
/-- A computation using a join point on contexts and optional names, each of whose calls is a
    `KG` computation for the names of `L` and of the context, with the join point being one, is a
    `KG` computation. -/
private theorem KGR.jp_pair {β γ : Type} {Ids L : List P.Ident}
    {v : RE P × Option P.Ident → WM P β} {b : (RE P × Option P.Ident → WM P β) → WM P γ}
    (hv : ∀ x, KG Ids (L ++ RE.vars x.1) (v x))
    (hb : ∀ jp : RE P × Option P.Ident → WM P β, (∀ x, KG Ids (L ++ RE.vars x.1) (jp x)) →
      KG Ids L (b jp)) : KG Ids L (b v) := hb v hv
/-- One step of the `KG` decomposition of a walk. -/
local macro "kg_step" : tactic => `(tactic| first
  | head_let
  | head_split
  | ((on_head wRen; with_reducible_and_instances apply $(Lean.mkIdent `kg_bind_wRen)) <;>
      first | (intro y hy; simp [Block.idents, Stmt.idents, hy,
          ExprOrNondet.getVars_det, ExprOrNondet.getVars_nondet,
          getFvars_mem_exprFV]; done) | (intro _))
  | ((on_head wName; with_reducible_and_instances apply $(Lean.mkIdent `kg_bind_wName)) <;>
      first | (simp [Block.idents, Stmt.idents, ExprOrNondet.getVars_det,
          ExprOrNondet.getVars_nondet, getFvars_mem_exprFV]; done) | (intro _))
  | (on_head wFreshBool
     with_reducible_and_instances apply kg_bind_ext _ fun _ _ _ h hi => kx_wFreshBool h hi
     intro _)
  | (on_head wFreshLike
     with_reducible_and_instances apply kg_bind_ext _ fun _ _ _ h hi => kx_wFreshLike h hi
     intro _)
  | run_step
  | prim kg
  | (on_head liveAdd; with_reducible_and_instances apply kg_liveAdd; grind [RE.vars])
  | (on_head modify; with_reducible_and_instances apply kg_modify; intro _
     refine ⟨rfl, rfl, rfl, fun _ _ h => ?_⟩
     first | exact h | simp at h)
  | (refine KG.monoL (by apply_assumption) ?_; grind [RE.vars])
  | contradiction)
section
include iW iL
/-- `wRen` is a `KG` computation. -/
private theorem kg_wRen (Ids L : List P.Ident) (e : P.Expr) :
    KG Ids L (wRen e : WM P (WExpr P × List P.Ident)) := by
  unfold wRen
  repeat' kg_step
/-- `saveRestore` is a `KG` computation. -/
private theorem kg_saveRestore (Ids L : List P.Ident) (xs : List P.Ident) :
    KG Ids L (saveRestore xs : WM P _) := by
  unfold saveRestore
  repeat' kg_step
/-- A run of `wRen e` for an expression whose free variables are in `Ids` keeps `KI`, and the
    names it reads are `KeyOK`. -/
private theorem kx_wRen {Ids : List P.Ident} {e : P.Expr} (hfv : ∀ y ∈ exprFV e, y ∈ Ids)
    {st st' : WSt P} {p : WExpr P × List P.Ident} (h : (wRen e).run st = .ok (p, st'))
    (hi : KI Ids st) :
    KI Ids st' ∧ st'.avoid = st.avoid ∧ st.next ≤ st'.next ∧ ∀ y ∈ p.2, KeyOK st' y := by
  obtain ⟨⟨h1, h2, h3⟩, ha, hn⟩ := (kg_wRen Ids [] e).run _ _ _ h hi nofun
  refine ⟨⟨h1, h2, h3⟩, ha, hn, fun y hy => ?_⟩
  obtain ⟨⟨-, -, -, -, hrd⟩, -⟩ := wRen_run (we := p.1) (rd := p.2) h
  obtain ⟨z, hz, hc⟩ := hrd y hy
  grind [KeyOK, curName]
/-- Renaming an expression whose free variables are in `Ids`, followed by `KG` computations for
    the names it reads, is a `KG` computation. -/
private theorem kg_bind_wRen {β : Type} {Ids L : List P.Ident} {e : P.Expr}
    {f : WExpr P × List P.Ident → WM P β} (hfv : ∀ y ∈ exprFV e, y ∈ Ids)
    (hf : ∀ p, KG Ids (L ++ p.2) (f p)) : KG Ids L (wRen e >>= f) :=
  kg_bind_ext Prod.snd (fun _ _ _ h hi => kx_wRen hfv h hi) hf
/-- `wName x` for an `x` of `Ids`, followed by `KG` computations for its result, is a `KG`
    computation. -/
private theorem kg_bind_wName {β : Type} {Ids L : List P.Ident} {x : P.Ident}
    {f : P.Ident → WM P β} (hx : x ∈ Ids) (hf : ∀ n, KG Ids (L ++ [n]) (f n)) :
    KG Ids L (wName x >>= f) := kg_bind_ext (fun n => [n]) (fun _ _ _ h hi => kx_wName hx h hi) hf


/-- Under a context whose variables are in `L`, a real-branch `ite` walk is a `KG` computation
    when the walks of its arms under `top` are. -/
private theorem wpIteReal_kg (κ : RE P) (d : Nat) (c : P.Expr) (tss ess : PStmts P)
    (L : List P.Ident) (hκ : ∀ y ∈ RE.vars κ, y ∈ L)
    (hT : KG (Block.idents tss) [] (wpList .top d false tss))
    (hE : KG (Block.idents ess) [] (wpList .top d false ess)) :
    KG (exprFV c ++ Block.idents tss ++ Block.idents ess) L (wpIteReal κ d c tss ess) := by
  refine ⟨fun st r st' h hi hk => ?_⟩
  unfold wpIteReal at h
  run_peel h 2
  obtain ⟨E, s2, hE2, h⟩ := wm_run_bind_ok h
  obtain ⟨hi2, ha2, hn2⟩ := (hE.monoI (Ids' := exprFV c ++ Block.idents tss ++ Block.idents ess)
    fun x hx => by simp [hx]).run _ _ _ hE2 (hi.of_frame rfl rfl rfl fun _ _ h => by simp at h)
    nofun
  run_peel h 2
  obtain ⟨T, s5, hT5, h⟩ := wm_run_bind_ok h
  obtain ⟨hi5, ha5, hn5⟩ := (hT.monoI (Ids' := exprFV c ++ Block.idents tss ++ Block.idents ess)
    fun x hx => by simp [hx]).run _ _ _ hT5 (hi2.of_frame rfl rfl rfl fun _ _ h => by simp at h)
    nofun
  run_peel h 2
  obtain ⟨hi8, ha8, hn8⟩ := Runs.run (R := KGR (exprFV c ++ Block.idents tss ++ Block.idents ess) L)
    (by repeat' kg_step) _ _ _ h ⟨hi5.1, fun n t ht => by
      grind [KI, LiveKeys, KeyOK.of_le, → unionLive_getElem], hi5.2.2⟩
    fun y hy => (((hk y hy).of_le ha2 hn2).of_le ha5 hn5)
  exact ⟨hi8, ha8.trans (ha5.trans ha2), Nat.le_trans hn2 (Nat.le_trans hn5 hn8)⟩

/-- Under a context whose variables are in `L`, a laid-out `ite` walk is a `KG` computation when
    the walks of its arms are. -/
private theorem wpIteLaid_kg (κ : RE P) (d : Nat) (c : P.Expr) (tss ess : PStmts P)
    (L : List P.Ident) (hκ : ∀ y ∈ RE.vars κ, y ∈ L)
    (hT' : ∀ κ' fE L', (∀ y ∈ RE.vars κ', y ∈ L') →
      KG (exprFV c ++ Block.idents tss ++ Block.idents ess) L' (wpList κ' d fE tss))
    (hE' : ∀ κ' fE L', (∀ y ∈ RE.vars κ', y ∈ L') →
      KG (exprFV c ++ Block.idents tss ++ Block.idents ess) L' (wpList κ' d fE ess)) :
    KG (exprFV c ++ Block.idents tss ++ Block.idents ess) L (wpIteLaid κ d c tss ess) := by
  unfold wpIteLaid
  repeat' first | kg_step | (apply hE'; grind [RE.vars]) | (apply hT'; grind [RE.vars])
omit iL in
mutual
/-- Under a context whose variables are in `L`, a statement walk is a `KG` computation. -/
private theorem wpStmt_kg [LawfulHasIdent P] (κ : RE P) (d : Nat) (f : Bool) (L : List P.Ident)
    (hκ : ∀ y ∈ RE.vars κ, y ∈ L) : ∀ s : PStmt P, KG (Block.idents [s]) L (wpStmt κ d f s)
  | .cmd c => by
    rcases c with (⟨_, _, _ | _, _⟩ | ⟨_, _ | _, _⟩ | _ | _ | _) | _ <;> unfold wpStmt <;>
      repeat' kg_step
  | .typeDecl _ _ | .loop _ _ _ _ _ | .ite .nondet _ _ _ | .exit _ _ => by
    unfold wpStmt
    repeat' kg_step
  | .block l body md => by
    have hB' : ∀ κ' L', (∀ y ∈ RE.vars κ', y ∈ L') →
        KG (Block.idents [.block l body md]) L' (wpList κ' (d + 1) f body) :=
      fun κ' L' h => (wpList_kg κ' (d + 1) f L' h body).monoI fun x hx => by
        simpa [Block.idents, Stmt.idents, ExprOrNondet.getVars_det,
          ExprOrNondet.getVars_nondet, getFvars_mem_exprFV] using hx
    simp only [wpStmt]
    repeat' first
      | (with_reducible_and_instances apply runs_get_set
         · exact kg_modify _ _ _ fun _ => ⟨rfl, rfl, rfl, fun _ _ h => h⟩
         intro _ _)
      | kg_step
      | (apply hB' <;> grind [RE.vars])
      | exact kg_liveAdd hκ
  | .ite (.det c) tss ess md => by
    simp only [wpStmt]
    split
    · exact (wpIteLaid_kg κ d c tss ess L hκ
        (fun κ' fE L' h => (wpList_kg κ' d fE L' h tss).monoI (by simp_all))
        fun κ' fE L' h => (wpList_kg κ' d fE L' h ess).monoI (by simp_all)).monoI
        (by simp [Block.idents, Stmt.idents, ExprOrNondet.getVars_det, getFvars_mem_exprFV])
    · exact (wpIteReal_kg κ d c tss ess L hκ (wpList_kg .top d false [] nofun tss)
        (wpList_kg .top d false [] nofun ess)).monoI
            (by simp [Block.idents, Stmt.idents, ExprOrNondet.getVars_det, getFvars_mem_exprFV])
  termination_by structural s => s
/-- Under a context whose variables are in `L`, a statement-list walk is a `KG` computation. -/
private theorem wpList_kg [LawfulHasIdent P] (κ : RE P) (d : Nat) (fEnd : Bool) (L : List P.Ident)
    (hκ : ∀ y ∈ RE.vars κ, y ∈ L) : ∀ ss : PStmts P, KG (Block.idents ss) L (wpList κ d fEnd ss)
  | [] => by simpa only [wpList] using runs_pure _
  | s :: rest => by
    simp only [wpList]
    apply runs_bind ((wpList_kg κ d fEnd L hκ rest).monoI fun x hx => by simp [Block.idents, hx])
    intro r
    apply runs_bind ((wpStmt_kg κ d _ L hκ s).monoI fun x hx => by simp_all [Block.idents])
    intro a
    repeat' kg_step
  termination_by structural ss => ss
end

/-- A statement-list walk from a well-formed state whose identifiers are avoided if they have
    the form of a fresh name, under a context with `KeyOK` variables, keeps `LiveKeys`. -/
theorem wpList_liveKeys {κ : RE P} {d : Nat} {fEnd : Bool} {ss : PStmts P} {st st' : WSt P}
    {r : WRes P} (h : (wpList κ d fEnd ss).run st = .ok (r, st')) (hwf : WFSt st)
    (hid : ∀ x ∈ Block.idents ss, AvoidedIfFresh st x) (hκ : ∀ y ∈ RE.vars κ, KeyOK st y)
    (hk : LiveKeys st) : LiveKeys st' :=
  ((wpList_kg κ d fEnd (RE.vars κ) (fun _ h => h) ss).run _ _ _ h
    ⟨fun x n hx => (hwf.nm_fresh x n hx).2.imp fun _ => .imp fun _ h => ⟨h.1, h.2.1⟩, hk, hid⟩
    hκ).1.2.1
end

end -- public section

end WP
end Imperative
