/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
import Strata.Transform.WP.WPOverEmit
import Strata.Transform.WP.WPOverEval
public import Strata.Transform.WP.WPOverFacts
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.Generalize
public import Strata.Transform.WP.WPOverEffectsWalk
import all Strata.Transform.WP.WPOverEffectsWalk

/-! # The declarations and writes of an arm walk

The walk of an arm of a laid-out `ite` (a list under a variable context with an obligation
following it) walks every nested statement with an obligation following it.  Its output declares
names drawn by the walk, loop-free locals of the arm or their renamings (`wpList_arm`, `ArmW`).
The facts are restated one by one: the names the walk records as taken (`arm_takenIn`), the
names the output declares (`arm_decl`), the registrations (`arm_regs`), the carried merges and
their selectors (`arm_carriesNew`, `arm_carrySel`), and the names a run of the output writes
(`arm_writes`, `arm_writesQ`).

Key definitions: `wDecls`, `ArmW`.

Key theorems: `wpList_arm`, `arm_decl`, `arm_regs`, `arm_takenIn`, `arm_carriesNew`,
`arm_carrySel`, `arm_writes`, `arm_writesQ`. -/

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
omit iOp iLF iLFs iLV
variable {s' s : WSt P} {κ : RE P} {r : WRes P} {d : Nat} {D xs I : List P.Ident} {F : P.Factory}
  {n x y : P.Ident} {Y : Std.HashMap P.Ident P.Ident} {T : Std.HashMap P.Ident P.Ty}


/-! ## Arm walks

The walk of a list under a variable context with an obligation following it (the walk of an arm
of a laid-out `ite`) walks every nested statement with an obligation following it: it has no
real branch and walks every `init` of the list.  Its output declares names drawn by the walk,
the loop-free locals of the list, or their renamings; its registrations are declared by its
output and its carried merges select with names its output declares (`ArmW`). -/

/-- The names the guarded items declare (`init` targets), at any depth. -/
@[expose] def wDecls : List (WItem P) → List P.Ident
  | [] => []
  | .init x _ _ :: rest => x :: wDecls rest
  | .branch t e :: rest => wDecls t ++ wDecls e ++ wDecls rest
  | _ :: rest => wDecls rest

/-- The facts of the walk of a fragment declaring the locals `I` at block depth `d`, from `s`
    to `s'` with result `r`, every nested statement walked with an obligation following it:
    the names recorded as declared later stay recorded and include `I`; the output has no real
    branch and declares names drawn by the walk, or locals of `I` not recorded at `s`, or
    renamings of locals of `I` at `s`; the registrations are declared by the output; up to
    depth `d` the carried merges only gain merges in front, with copies drawn by the walk; a new
    carried merge registered by the result selects with names its output declares. -/
structure ArmW (d : Nat) (I : List P.Ident) (s s' : WSt P) (r : WRes P) : Prop where
  taken : ∀ y, s.taken.contains y = true → s'.taken.contains y = true
  takenIn : ∀ z ∈ I, s'.taken.contains z = true
  nobr : ∀ it ∈ r.out.toList, ∀ t e, it ≠ .branch t e
  decl : ∀ n ty v, WItem.init n ty v ∈ r.out.toList → NewIn s s' n ∨
    (n ∈ I ∧ s.taken.contains n = false) ∨ ∃ x ∈ I, s.nm[x]? = some n
  regs : ∀ e ∈ r.regs.toList, InitIn r.out.toList e
  pre : ∀ k, k ≤ d → ∃ new, s'.carries.getD k [] = new ++ s.carries.getD k [] ∧
    ∀ q ∈ new, NewIn s s' q.2.2
  sel : ∀ k q, q ∈ s'.carries.getD k [] → q ∉ s.carries.getD k [] → q.2.2 ∈ r.regs.toList →
    ∃ e, q.2.1 = .ite e (.var q.2.2) (.var q.1) ∧ SelOK (InitIn r.out.toList) e

omit iLI iWL in
/-- The arm facts from the facts of the items of the output. -/
private theorem ArmW.mk' (ht : ∀ y, s.taken.contains y = true → s'.taken.contains y = true)
    (hI : ∀ z ∈ I, s'.taken.contains z = true)
    (hit : ∀ it ∈ r.out.toList, (∀ t e, it ≠ .branch t e) ∧
      ∀ n ty v, it = .init n ty v → NewIn s s' n ∨ (n ∈ I ∧ s.taken.contains n = false) ∨
      ∃ x ∈ I, s.nm[x]? = some n) (hr : ∀ e ∈ r.regs.toList, InitIn r.out.toList e)
    (hp : ∀ k, k ≤ d → ∃ new, s'.carries.getD k [] = new ++ s.carries.getD k [] ∧
      ∀ q ∈ new, NewIn s s' q.2.2)
    (hs : ∀ k q, q ∈ s'.carries.getD k [] → q ∉ s.carries.getD k [] → q.2.2 ∈ r.regs.toList →
      ∃ e, q.2.1 = .ite e (.var q.2.2) (.var q.1) ∧ SelOK (InitIn r.out.toList) e) :
    ArmW d I s s' r := by grind [ArmW]
omit iLI iWL in
/-- A walk step that keeps the carried merges and outputs only `init`s of names the walk draws or
    of `x ∈ I` (as `wDecl x` returns at `s1`), with no registration, has the arm facts. -/
private theorem ArmW.of_cmd {s1 : WSt P} (hm : WMono [] s s1) (hm' : WMono [] s1 s')
    (ht : ∀ y, s.taken.contains y = true → s'.taken.contains y = true) (ht1 : s1.taken = s.taken)
    (hI : ∀ z ∈ I, s'.taken.contains z = true) (hc : s'.carries = s.carries)
    (ho : ∀ it ∈ r.out.toList, (∀ t e, it ≠ .branch t e) ∧
      ∀ n ty v, it = .init n ty v → NewIn s s' n ∨ ∃ x ∈ I, s1.nm[x]? = some n ∨
      (n = x ∧ s1.taken.contains x = false)) (hr : r.regs = .nil) : ArmW d I s s' r := by
  refine ⟨ht, hI, fun it hit => (ho it hit).1, fun n ty v hit => ?_, by simp [hr, Rope.toList_nil],
    fun k _ => ⟨[], by simp [hc], nofun⟩, fun k q hq hq' => absurd (hc ▸ hq) hq'⟩
  rcases (ho _ hit).2 n ty v rfl with h | ⟨x, hx, h | ⟨rfl, h⟩⟩
  · exact .inl h
  · exact (hm.nm x n h).elim (fun h => .inr (.inr ⟨x, hx, h⟩)) (.inl <| ·.up hm'.next)
  · exact .inr (.inl ⟨hx, ht1 ▸ h⟩)
/-- A run of `wName` keeps the names recorded as declared later and the carried merges. -/
theorem wName_keep (h : (wName x).run s = .ok (n, s')) :
    s'.taken = s.taken ∧ s'.carries = s.carries := by
  rw [(wName_state h).2]
  exact ⟨rfl, rfl⟩
/-- A run of `wDecl x` is a `WMono` step that records `x` as declared later, keeps the carried
    merges, and returns the recorded renaming of `x`, `x` itself when not yet recorded as declared
    later, or a name it draws. -/
theorem wDecl_k (h : (wDecl x).run s = .ok (n, s')) :
    WMono D s s' ∧ s'.taken = s.taken.insert x ∧ s'.carries = s.carries ∧
      (s.nm[x]? = some n ∨ (n = x ∧ s.taken.contains x = false) ∨ NewIn s s' n) := by
  obtain ⟨hm, -⟩ := wDecl_w (D := D) h
  obtain ⟨n1, s1, h1⟩ := wName_ok x s
  cases (wDecl_run h1).symm.trans h
  obtain ⟨ht, hc⟩ := wName_keep h1
  refine ⟨hm, by rw [ht], hc, ?_⟩
  rcases wName_cases h1 with ⟨h, -⟩ | ⟨-, h, rfl, -⟩ | ⟨-, -, rfl, rfl⟩
  · exact .inl h
  · exact .inr (.inl ⟨rfl, h⟩)
  · exact .inr (.inr (freshIn_drawn _ _ _ (Nat.le_refl _)))
/-- A run of `wRen` keeps the names recorded as declared later and the carried merges. -/
theorem wRen_keep {e : P.Expr} {p : WExpr P × List P.Ident}
    (h : (wRen e).run s = .ok (p, s')) : s'.taken = s.taken ∧ s'.carries = s.carries := by
  obtain ⟨-, -, hs, -⟩ := wRen_run h
  rw [hs]
  exact ⟨rfl, rfl⟩

omit iLI iWL in
/-- A run of `liveAdd` keeps the names recorded as declared later and the carried merges. -/
theorem liveAdd_tc {u : Unit}
    (h : (liveAdd xs).run s = .ok (u, s')) : s'.taken = s.taken ∧ s'.carries = s.carries := by
  obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h
  exact ⟨rfl, rfl⟩
omit iLI iWL in
/-- A run of `liveDel` keeps the names recorded as declared later and the carried merges. -/
theorem liveDel_tc {u : Unit}
    (h : (liveDel x).run s = .ok (u, s')) : s'.taken = s.taken ∧ s'.carries = s.carries :=
  by grind [liveDel_run]

/-- The arm facts of the walk of a deterministic `init` with an obligation following it. -/
private theorem init_det_a (hκ : κ ≠ .top) {ty : P.Ty} {e : P.Expr} {md : MetaData P}
    (h : (wpStmt κ d true (.cmd (.cmd (.init x ty (.det e) md)))).run s = .ok (r, s')) :
    ArmW d [x] s s' r := by
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨n, s2, h2⟩ _ ⟨xd, s4, h4⟩ _ ⟨_, s5, h5⟩ ⟨_, s6, h6⟩ rfl
  have m1 := wRen_w (D := []) h1
  obtain ⟨m2, t2, c2, hn⟩ := wDecl_k (D := []) h2
  obtain ⟨m4, hx⟩ := wFresh_w (D := []) h4
  have m6 : WMono [] s4 s6 := (WMono.same).trans ((liveDel_w h5).trans (liveAdd_w h6))
  have k1 := wRen_keep h1
  obtain ⟨-, -, k4, -, -, -, c4, -⟩ := wFresh_laidSame h4
  have k5 := liveDel_tc h5
  have k6 := liveAdd_tc h6
  refine ArmW.of_cmd m1 (m2.trans ((WMono.same).trans (m4.trans m6))) (by grind) k1.1 (by grind)
    (by grind) (fun it hit => ⟨?_, ?_⟩) rfl
  all_goals simp only [Rope.toList_app, Rope.toList_one, List.mem_append, List.mem_singleton] at hit
  · rcases hit with rfl | rfl <;> exact nofun
  rintro _ _ _ rfl
  rcases hit with hit | hit <;> cases hit
  · exact .inl (hx.widen (m1.trans m2).avoid (m1.trans m2).next m6.next)
  · exact hn.elim (fun h => .inr ⟨x, List.mem_singleton_self x, .inl h⟩) (·.elim
      (fun h => .inr ⟨x, List.mem_singleton_self x, .inr h⟩)
      fun h => .inl (h.widen m1.avoid m1.next (m4.trans m6).next))
/-- The arm facts of the walk of a nondeterministic `init` with an obligation following it. -/
private theorem init_nondet_a {ty : P.Ty} {md : MetaData P}
    (h : (wpStmt κ d true (.cmd (.cmd (.init x ty .nondet md)))).run s = .ok (r, s')) :
    ArmW d [x] s s' r := by
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  peel h ⟨n, s2, h2⟩ _ ⟨_, s5, h5⟩ rfl
  obtain ⟨hm2, ht2, hc2, hn⟩ := wDecl_k (D := []) h2
  obtain ⟨ht5, hc5⟩ := liveDel_tc h5
  have hm5 := WMono.trans (D := []) (s0 := s2) .same (liveDel_w h5)
  have hu := hm5.next
  exact ArmW.of_cmd (.refl [] s) (hm2.trans hm5) (fun y hy => by simp [ht5, ht2, hy]) rfl
    (by simp [ht5, ht2]) (by rw [hc5]; exact hc2)
    (fun it hit => by grind [Rope.toList_one, NewIn.up]) rfl
/-- The arm facts of the walk of a deterministic `set` with an obligation following it. -/
private theorem set_det_a {e : P.Expr} {md : MetaData P}
    (h : (wpStmt κ d true (.cmd (.cmd (.set x (.det e) md)))).run s = .ok (r, s')) :
    ArmW d [] s s' r := by
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨n, s2, h2⟩
  have k1 := wRen_keep h1
  have k2 := wName_keep h2
  split at h <;>
  · obtain ⟨_, s3, h3, h⟩ := wm_run_bind_ok h
    peel h ⟨_, s4, h4⟩ rfl
    have k3 : s3.taken = s2.taken ∧ s3.carries = s2.carries := by
      first | exact liveDel_tc h3 | exact liveAdd_tc h3
    have k4 := liveAdd_tc h4
    exact ⟨fun y hy => by grind, nofun, fun it hit => (by cases Rope.mem_one hit; exact nofun),
      fun n ty v hit => (by cases Rope.mem_one hit), by simp [Rope.toList_nil],
      fun k _ => ⟨[], by grind, nofun⟩, fun k q hq hq' => absurd (by grind) hq'⟩
/-- The arm facts of the walk of a nondeterministic `set` with an obligation following it. -/
private theorem set_nondet_a {md : MetaData P}
    (h : (wpStmt κ d true (.cmd (.cmd (.set x .nondet md)))).run s = .ok (r, s')) :
    ArmW d [] s s' r := by
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  peel h ⟨n, s2, h2⟩ ⟨xh, s3, h3⟩
  obtain ⟨ht2, hc2⟩ := wName_keep h2
  obtain ⟨-, -, ht3, -, -, -, hc3, -⟩ := wFreshLike_laidSame h3
  obtain ⟨hm3, hx⟩ := wFreshLike_w (D := []) h3
  split at h <;>
  · obtain ⟨_, s4, h4, h⟩ := wm_run_bind_ok h
    obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
    obtain ⟨ht4, hc4⟩ : s4.taken = s3.taken ∧ s4.carries = s3.carries := by
      first | exact liveDel_tc h4 | exact liveAdd_tc h4
    have hm4 : WMono [] s3 s4 := by first | exact liveDel_w h4 | exact liveAdd_w h4
    have hm2 := (wName_w (D := []) h2).1
    have hx' := hx.widen hm2.avoid hm2.next hm4.next
    refine ArmW.of_cmd (.refl [] s) (hm2.trans (hm3.trans hm4))
      (fun y hy => by rw [ht4, ht3, ht2]; exact hy) rfl nofun (by rw [hc4, hc3, hc2])
      (fun it hit => by grind [Rope.toList_app, Rope.toList_one]) rfl
omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL in
/-- The items of `setReach κ X` are assignments. -/
theorem setReach_set (κ : RE P) (X : WExpr P) :
    ∀ it ∈ (setReach κ X).toList, ∃ y v, it = .set y v := by
  cases κ <;> simp [setReach, Rope.toList_one, Rope.toList_nil]
/-- The arm facts of the walk of an `exit` under a variable context with an obligation following
    it. -/
private theorem exit_a (hκ : κ ≠ .top) {l : String} {md : MetaData P}
    (h : (wpStmt κ d true (.exit l md)).run s = .ok (r, s')) :
    ArmW d [] s s' r := by
  rcases exit_inv hκ h with ⟨t, -, ⟨⟨⟩, -⟩ | ⟨-, e, s2, h2, h4, rfl⟩⟩ | ⟨-, rfl, ⟨⟨⟩, -⟩ | ⟨-, rfl⟩⟩
  · obtain ⟨m2, hd2⟩ := wFreshBool_w (D := []) h2
    obtain ⟨-, -, t2, -, -, -, c2, -⟩ := wFreshBool_laidSame h2
    obtain ⟨t4, c4⟩ := liveAdd_tc h4
    have hd := hd2.widen rfl (Nat.le_refl _) (liveAdd_w (D := []) h4).next
    refine ⟨fun y hy => by rw [t4]; exact t2 ▸ hy, nofun, fun it hit t e => ?_,
      fun n ty v hit => ?_, fun e' he => ?_, fun k _ => ⟨[], by rw [c4, c2]; rfl, nofun⟩,
      fun k q hq hn => absurd (by rw [c4] at hq; exact c2 ▸ hq) hn⟩
    iterate 2 grind [Rope.toList_app, Rope.toList_one, setReach_set]
    · cases Rope.mem_one he
      exact ⟨_, _, by rw [Rope.toList_app, Rope.toList_one]; exact .head _⟩
  · refine ⟨fun _ h => h, nofun, fun it hit t e he => ?_, fun n ty v hit => ?_,
      by simp [Rope.toList_nil], fun k _ => ⟨[], rfl, nofun⟩, fun k q hq hn => absurd hq hn⟩
    iterate 2 grind [setReach_set]

section
include iOp iLF iLFs

omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL iOp iLF iLFs in
/-- An item of the output of a block under a variable context is an item of its body or an
    assignment. -/
private theorem mem_block_out {it : WItem P} {Bo : Rope (WItem P)}
    {L : List (P.Ident × WExpr P × P.Ident)} {c c2 : Prop} [Decidable c] [Decidable c2]
    {X : WExpr P}
    (h : it ∈ ((Bo.app (L.foldl (fun acc x => acc.app (Rope.one (WItem.set x.1 (some x.2.1))))
      Rope.nil)).app (if c then Rope.nil else if c2 then Rope.nil else setReach κ X)).toList) :
    it ∈ Bo.toList ∨ ∃ y v, it = .set y v := by
  simp only [Rope.toList_app, List.mem_append] at h
  rcases h with (h | h) | h
  · exact .inl h
  · rcases mem_sets _ _ h with h | ⟨q, -, rfl⟩
    · simp [Rope.toList_nil] at h
    · exact .inr ⟨_, _, rfl⟩
  · exact .inr (setReach_set κ X it (mem_ite_nil (mem_ite_nil h)))
omit iLI iOp iLF iLFs in
/-- The arm facts of the walk of a block under a variable context with an obligation following
    it, from those of its body. -/
private theorem block_a (hκ : κ ≠ .top) {l : String} {body : PStmts P} {md : MetaData P}
    (hB : ∀ s0 B s1, (wpList κ (d + 1) true body).run s0 = .ok (B, s1) →
      ArmW (d + 1) (stmtsInits body) s0 s1 B)
    (h : (wpStmt κ d true (.block l body md)).run s = .ok (r, s')) :
    ArmW d (stmtsInits body) s s' r := by
  obtain ⟨s0, B, s4, rfl, hB4, h5, rfl⟩ := block_inv hκ h
  have AB := hB _ _ _ hB4
  obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h5
  have hk : ∀ k, k ≤ d → d + 1 ≠ k := fun k hk => Nat.ne_of_gt (Nat.lt_succ_of_le hk)
  refine ⟨AB.taken, AB.takenIn, fun it hit => ?_, fun n ty v hit => ?_, fun e he => ?_,
    fun k hk' => ?_, fun k q hq hq' hr => ?_⟩
  · rcases mem_block_out hit with hit | ⟨y, v, rfl⟩
    · exact AB.nobr it hit
    · exact nofun
  · rcases mem_block_out hit with hit | ⟨y, v, ⟨⟩⟩
    exact AB.decl n ty v hit
  · exact (AB.regs e he).imp fun ty ⟨v, hi⟩ => ⟨v, by out_mem hi⟩
  · obtain ⟨new, he, hn⟩ := AB.pre k (Nat.le_succ_of_le hk')
    exact ⟨new, by simpa [Std.HashMap.getD_erase, Std.HashMap.getD_insert, hk k hk'] using he, hn⟩
  · have hk1 : d + 1 ≠ k := fun e => by simp [← e] at hq
    obtain ⟨e, he, hs⟩ := AB.sel k q (by simpa [Std.HashMap.getD_erase, hk1] using hq)
      (by simpa [Std.HashMap.getD_insert, hk1] using hq') hr
    exact ⟨e, he, hs.imp fun n ⟨ty, v, hi⟩ => ⟨ty, v, by out_mem hi⟩⟩
omit iLI iWL iOp iLF iLFs in
/-- An `init` target of the output of a walk from `s1` to `s2` with the arm facts, after a
    `WMono` step from `s` to `s1` that keeps the names recorded as declared later, satisfies
    the arm-fact condition relative to `s` and any later state. -/
private theorem decl_lift {I' : List P.Ident} {s1 s2 : WSt P} (hm : WMono D s s1)
    (ht : ∀ y, s.taken.contains y = true → s1.taken.contains y = true) (hI : ∀ x ∈ I', x ∈ I)
    (h12 : s1.next ≤ s2.next) (h2 : s2.next ≤ s'.next)
    (h : NewIn s1 s2 n ∨ (n ∈ I' ∧ s1.taken.contains n = false) ∨ ∃ x ∈ I', s1.nm[x]? = some n) :
    NewIn s s' n ∨ (n ∈ I ∧ s.taken.contains n = false) ∨ ∃ x ∈ I, s.nm[x]? = some n := by
  grind [WMono, NewIn]
omit iLI iWL iOp iLF iLFs in
/-- An `init` of a name drawn by the walk meets the item condition of the arm facts. -/
private theorem armIt_init {ty : TyRef P} {v : Option (WExpr P)} (h : NewIn s s' x) :
    (∀ t e, WItem.init x ty v ≠ .branch t e) ∧ ∀ n ty' v', WItem.init x ty v = .init n ty' v' →
      NewIn s s' n ∨ (n ∈ I ∧ s.taken.contains n = false) ∨ ∃ x ∈ I, s.nm[x]? = some n :=
  ⟨nofun, fun _ _ _ he => by cases he; exact .inl h⟩
/-- Reduces `h : a ∈ X.toList`, for `X` either `Rope.one b` or an `if` or `match` choosing
    between `Rope.one b` and `Rope.nil`, to `a = b` and substitutes it. -/
local macro "one_at " h:ident : tactic => `(tactic| (
  (try split at $h:ident) <;>
    simp only [Rope.toList_one, Rope.toList_nil, List.mem_singleton, List.not_mem_nil] at $h:ident
  subst $h))

omit iWL iOp iLF iLFs in
/-- The arm facts of the walks of `rest` (from `st` to `st1`) and then of `s` (to `st2`) give
    those of the walk of `s :: rest` with the result of `s` alone or combined with that of
    `rest`, for a final state with the names recorded, the carried merges and the counter of
    `st2`. -/
private theorem ArmW.cons {κ' : RE P} {Ia Ir : List P.Ident} {st st1 st2 st' : WSt P} {a R : WRes P}
    (Ar : ArmW d Ir st st1 r) (Aa : ArmW d Ia st1 st2 a) (Wr : WalkW D κ st st1 r)
    (Wa : WalkW D κ' st1 st2 a) (ht : st'.taken = st2.taken) (hc : st'.carries = st2.carries)
    (hn : st'.next = st2.next) (hR : R = a ∨ R = a.combine r) : ArmW d (Ia ++ Ir) st st' R := by
  have hout : ∀ it ∈ R.out.toList, it ∈ a.out.toList ∨ it ∈ r.out.toList := fun it h => by
    rcases hR with rfl | rfl <;> simp_all [WRes.combine, Rope.toList_app]
  have hin : ∀ n, InitIn a.out.toList n → InitIn R.out.toList n := fun n ⟨ty, v, h⟩ =>
    ⟨ty, v, by rcases hR with rfl | rfl <;> simp [WRes.combine, Rope.toList_app, h]⟩
  have hinr : ∀ n, InitIn r.out.toList n → R = a.combine r → InitIn R.out.toList n :=
    fun n ⟨ty, v, h⟩ hR => ⟨ty, v, by simp [hR, WRes.combine, Rope.toList_app, h]⟩
  have hreg : ∀ e ∈ R.regs.toList, e ∈ a.regs.toList ∨ e ∈ r.regs.toList ∧ R = a.combine r := by
    rcases hR with rfl | rfl
    · exact fun e he => .inl he
    · simp [WRes.combine, Rope.toList_app]
  have h2' : st2.next ≤ st'.next := Nat.le_of_eq hn.symm

  refine ⟨fun y hy => ht ▸ Aa.taken y (Ar.taken y hy),
    fun z hz => ht ▸ (List.mem_append.1 hz).elim (Aa.takenIn z) fun hz =>
      Aa.taken z (Ar.takenIn z hz),
    fun it hit => (hout it hit).elim (Aa.nobr it) (Ar.nobr it), fun n ty v hit => ?_,
    fun e he => (hreg e he).elim (hin _ <| Aa.regs e ·) fun ⟨h, hc⟩ => hinr _ (Ar.regs e h) hc,
    fun k hk => ?_, fun k q hq hq' hr => ?_⟩
  · refine (hout _ hit).elim (fun h => decl_lift Wr.toWMono Ar.taken (fun x hx =>
      List.mem_append_left _ hx) Wa.next h2' (Aa.decl n ty v h)) fun h => ?_
    exact decl_lift (.refl D st) (fun _ h => h) (fun x hx => List.mem_append_right _ hx) Wr.next
      (Nat.le_trans Wa.next h2') (Ar.decl n ty v h)
  · obtain ⟨n2, e2, hn2⟩ := Aa.pre k hk
    obtain ⟨n1, e1, hn1⟩ := Ar.pre k hk
    refine ⟨n2 ++ n1, by rw [hc, e2, e1, List.append_assoc], fun q hq => ?_⟩
    exact (List.mem_append.1 hq).elim (fun hq => (hn2 q hq).widen Wr.avoid Wr.next h2')
      fun hq => (hn1 q hq).up (Nat.le_trans Wa.next h2')
  rw [hc] at hq
  by_cases hq1 : q ∈ st1.carries.getD k []
  · have hnew := ((Wr.carries k q hq1).resolve_left hq').2.1
    rcases hreg _ hr with hr | ⟨hr, hR⟩
    · exact (hnew.disj (Wa.regs _ hr) (Nat.le_refl _)).elim
    · exact (Ar.sel k q hq1 hq' hr).imp fun e ⟨he, hs⟩ => ⟨he, hs.imp (hinr · · hR)⟩
  · have hnew := ((Wa.carries k q hq).resolve_left hq1).2.1
    rcases hreg _ hr with hr | ⟨hr, -⟩
    · exact (Aa.sel k q hq hq1 hr).imp fun e ⟨he, hs⟩ => ⟨he, hs.imp hin⟩
    · exact ((Wr.regs _ hr).disj hnew (Nat.le_refl _)).elim

omit iLI iWL iOp iLF iLFs in
/-- A registration of the result of a laid-out `ite` is a registration of one of its arms or a
    copy name of a copy pair of its arms, which a walk from `a` to `b` draws. -/
private theorem mem_laidRegs {T E : WRes P} {A B : List (P.Ident × P.Ident)} {a b : WSt P}
    {x : P.Ident} (hA : ∀ p ∈ A, NewIn a b p.2) (hB : ∀ p ∈ B, NewIn a b p.2)
    (hx : x ∈ ((T.regs.app E.regs).app (Rope.ofList (A.map (·.2) ++ B.map (·.2)))).toList) :
    x ∈ T.regs.toList ∨ x ∈ E.regs.toList ∨ NewIn a b x := by
  simp only [Rope.toList_app, Rope.toList_ofList, List.mem_append, List.mem_map] at hx
  exact hx.elim (·.elim .inl (.inr ∘ .inl)) (·.elim (fun ⟨p, hp, e⟩ => e ▸ .inr (.inr (hA p hp)))
    fun ⟨p, hp, e⟩ => e ▸ .inr (.inr (hB p hp)))
/-- The arm facts of the walk of a laid-out `ite`, from those of its arms. -/
private theorem laid_a {c : P.Expr} {tss ess : PStmts P}
    (hT : ∀ κ', κ' ≠ .top → ∀ s0 R s1, (wpList κ' d true tss).run s0 = .ok (R, s1) →
      ArmW d (stmtsInits tss) s0 s1 R)
    (hE : ∀ κ', κ' ≠ .top → ∀ s0 R s1, (wpList κ' d true ess).run s0 = .ok (R, s1) →
      ArmW d (stmtsInits ess) s0 s1 R) (h : (wpIteLaid κ d c tss ess).run s = .ok (r, s')) :
    ArmW d (stmtsInits tss ++ stmtsInits ess) s s' r := by
  let D := Block.idents tss ++ Block.idents ess
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hc h5 h6 h7 h8 h9 h10 _ h11
    hq11 h12 hr12 hEnd => ?_
  have m1 := wRen_w (D := D) h1
  obtain ⟨m2, hg⟩ := wFreshBool_w (D := D) h2
  obtain ⟨m3, hrT⟩ := wFreshBool_w (D := D) h3
  obtain ⟨t1, c1⟩ := wRen_keep h1
  have m13 := m1.trans (m2.trans m3)
  obtain ⟨h4, hκE, -⟩ := hc.facts
  obtain ⟨m4, S4, hx4, -⟩ := h4.w (D := D)
  have S14 := (wFreshBool_laidSame h2).trans ((wFreshBool_laidSame h3).trans S4)
  have AE := hE κE hκE s4 E s5 h5
  have AT := hT (.name rT) nofun s5 T s6 h6
  have WE := wpList_writes (D := D) κE d true ess (fun _ h => List.mem_append_right _ h) h5
  have WT := wpList_writes (D := D) (.name rT) d true tss (fun _ h => List.mem_append_left _ h) h6
  have ATE := ArmW.cons AE AT WE WT rfl rfl rfl (.inr rfl)
  obtain ⟨m7, S7, hk3, hsc3, hr3, -, hcps3, hi3⟩ := srFacts (D := D) h7
  obtain ⟨m8, S8, hkT, hscT, hrT', -, hcpsT, hiT⟩ := srFacts (D := D) h8
  obtain ⟨m9, S9, hkE, hscE, hrE', -, hcpsE, hiE⟩ := srFacts (D := D) h9
  have m49 := WE.toWMono.trans (WT.toWMono.trans (m7.trans (m8.trans m9)))
  obtain ⟨m10, S10, hgm0, -⟩ := h10.w (D := D)
  obtain ⟨m11, S11, hqm0, -⟩ := h11.w (D := D)
  obtain ⟨m12, S12, hrEm0, -⟩ := h12.w (D := D)
  have S612 := S7.trans (S8.trans (S9.trans (S10.trans (S11.trans S12))))
  have m09 := m13.trans (m4.trans m49)
  have m04 := m13.trans m4
  have m05 := m04.trans WE.toWMono
  have m06 := m05.trans WT.toWMono
  have m07 := m06.trans m7
  have m08 := m07.trans m8
  have m912 := m10.trans (m11.trans m12)

  have hsT : SelOK (fun y => gm = some y) (optVar gm) := by cases gm <;> first | rfl | trivial
  have hsE : SelOK (fun y => gm = some y ∨ qm = some y ∨ rEm = some y)
      (elseGuard κ gm qm rEm) := by
    unfold elseGuard
    split <;> cases gm <;> simp [SelOK, optVar, WExpr.not, WExpr.and]
  have hta : ∀ y, s.taken.contains y = true → s12.taken.contains y = true := fun y hy =>
    S612.taken ▸ ATE.taken y (S14.taken ▸ t1 ▸ hy)
  have htI : ∀ z ∈ stmtsInits tss ++ stmtsInits ess, s12.taken.contains z = true :=
    fun z hz => S612.taken ▸ ATE.takenIn z hz
  have hc4 : ∀ k, s4.carries.getD k [] = s.carries.getD k [] := fun k => by rw [S14.carries, c1]
  have hpre : ∀ k, k ≤ d → ∃ new, (carryIns (elseGuard κ gm qm rEm) (carryOf s6 cpsE E.tgt.max?)
      (carryIns (optVar gm) (carryOf s6 cpsT T.tgt.max?) s12.carries T.tgt.max?)
        E.tgt.max?).getD k [] = new ++ s.carries.getD k [] ∧ ∀ q ∈ new, NewIn s s12 q.2.2 := by
    intro k hk
    obtain ⟨n6, e6, hn6⟩ := carryIns_getD (elseGuard κ gm qm rEm) (carryOf s6 cpsE E.tgt.max?)
      (carryIns (optVar gm) (carryOf s6 cpsT T.tgt.max?) s12.carries T.tgt.max?) E.tgt.max? k
    obtain ⟨n5, e5, hn5⟩ := carryIns_getD (optVar gm) (carryOf s6 cpsT T.tgt.max?) s12.carries
      T.tgt.max? k
    obtain ⟨pTE, ePTE, hPTE⟩ := ATE.pre k hk
    refine ⟨n6 ++ n5 ++ pTE, ?_, fun q hq => ?_⟩
    · rw [e6, e5]
      simp [S612.carries, ePTE, hc4]
    · simp only [List.mem_append] at hq
      rcases hq with (hq | hq) | hq
      · obtain ⟨-, p, hp, rfl⟩ := hn6 q hq
        exact (hcpsE p (carryOf_sub hp)).2.widen m08.avoid m08.next m912.next
      · obtain ⟨-, p, hp, rfl⟩ := hn5 q hq
        exact (hcpsT p (carryOf_sub hp)).2.widen m07.avoid m07.next (m9.trans m912).next
      · exact (hPTE q hq).widen m04.avoid m04.next (m7.trans (m8.trans (m9.trans m912))).next
  rcases hEnd with ⟨hb, rfl, rfl⟩ | ⟨-, hFr, rfl⟩
  · simp only [Rope.isNil_foldl_app', Bool.and_eq_true, List.all_eq_true] at hb
    refine ArmW.mk' hta htI (by simp [Rope.toList_nil]) (fun e he => ?_) hpre fun k q _ _ he => ?_
    all_goals
      simp only [Rope.toList_app, Rope.toList_ofList, List.mem_append, List.mem_map] at he
      rcases he with (he | he) | ⟨p, hp, -⟩ | ⟨p, hp, -⟩
      · simpa [InitIn, Rope.isNil_toList (hb.2 T.out (by out_mem))] using AT.regs _ he
      · simpa [InitIn, Rope.isNil_toList (hb.2 E.out (by out_mem))] using AE.regs _ he
      · simpa [InitIn, Rope.isNil_toList (hb.2 cpT (by out_mem))] using hiT p (carryOf_sub hp)
      · simpa [InitIn, Rope.isNil_toList (hb.2 cpE (by out_mem))] using hiE p (carryOf_sub hp)
  obtain ⟨tF, cF⟩ := liveAdd_tc hFr
  have nF : s12.next ≤ s'.next := (liveAdd_w (D := []) hFr).next
  have N : ∀ {a b : WSt P} {x : P.Ident}, WMono D s a → WMono D b s12 → NewIn a b x →
      NewIn s s' x := fun ha hb hx => hx.widen ha.avoid ha.next (Nat.le_trans hb.next nF)
  have q8 := m9.trans m912
  have q4 := m49.trans m912
  refine ArmW.mk' (fun y hy => tF ▸ hta y hy) (fun z hz => tF ▸ htI z hz) (fun it hit => ?_)
    (fun e he => ?_) (fun k hk => ?_) (fun k q hq hn hx => ?_)
  · simp only [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
      List.mem_append, List.mem_singleton] at hit
    rcases hit with rfl | hit | hit | hit | hit | hit | hit | hit | hit | hit | hit |
      hit | hit | hit | hit | hit | hit | hit | hit
    · exact armIt_init (N m1 (m3.trans (m4.trans q4)) hg)
    · have hit := mem_ite_nil hit
      one_at hit
      exact armIt_init (N (m1.trans m2) (m4.trans q4) hrT)
    · one_at hit
      exact armIt_init (N m09 (m11.trans m12) (hgm0 _ rfl))
    · one_at hit
      exact armIt_init (N (m09.trans m10) m12 (hqm0 _ rfl))
    · obtain ⟨n, ty, v, rfl⟩ := hk3 _ (List.mem_append_left _ hit)
      exact armIt_init (N m06 (m8.trans q8) (hsc3 _ (List.mem_append_left _ hit) n rfl))
    · obtain ⟨n, ty, v, rfl⟩ := hkT _ (List.mem_append_left _ hit)
      exact armIt_init (N m07 q8 (hscT _ (List.mem_append_left _ hit) n rfl))
    · exact ⟨AT.nobr it hit, fun n ty v he => decl_lift m05
        (fun y hy => AE.taken y (S14.taken ▸ t1 ▸ hy)) (fun x hx => List.mem_append_left _ hx)
        WT.next (Nat.le_trans (m7.trans (m8.trans q8)).next nF) (AT.decl n ty v (he ▸ hit))⟩
    · obtain ⟨n, ty, v, rfl⟩ := hk3 _ (List.mem_append_right _ hit)
      exact armIt_init (N m06 (m8.trans q8) (hsc3 _ (List.mem_append_right _ hit) n rfl))
    · obtain ⟨n, ty, v, rfl⟩ := hkT _ (List.mem_append_right _ hit)
      exact armIt_init (N m07 q8 (hscT _ (List.mem_append_right _ hit) n rfl))
    · exact (hr3 _ hit).elim fun x ⟨v, h⟩ => h ▸ ⟨nofun, nofun⟩
    · exact (hrT' _ hit).elim fun x ⟨v, h⟩ => h ▸ ⟨nofun, nofun⟩
    · split at hit
      · have hit := mem_ite_nil hit
        one_at hit
        exact armIt_init (N m13 q4 (hx4 _ rfl))
      · simp [Rope.toList_nil] at hit
    · one_at hit
      exact armIt_init (N (m09.trans (m10.trans m11)) (.refl D s12) (hrEm0 _ rfl))
    · obtain ⟨n, ty, v, rfl⟩ := hkE _ (List.mem_append_left _ hit)
      exact armIt_init (N m08 m912 (hscE _ (List.mem_append_left _ hit) n rfl))
    · exact ⟨AE.nobr it hit, fun n ty v he => decl_lift m04 (fun y hy => S14.taken ▸ t1 ▸ hy)
        (fun x hx => List.mem_append_right _ hx) WE.next
        (Nat.le_trans (WT.toWMono.trans (m7.trans (m8.trans q8))).next nF)
        (AE.decl n ty v (he ▸ hit))⟩
    · obtain ⟨n, ty, v, rfl⟩ := hkE _ (List.mem_append_right _ hit)
      exact armIt_init (N m08 m912 (hscE _ (List.mem_append_right _ hit) n rfl))
    · exact (hrE' _ hit).elim fun x ⟨v, h⟩ => h ▸ ⟨nofun, nofun⟩
    · rcases mem_sets _ _ hit with hit | ⟨q, -, rfl⟩
      · simp [Rope.toList_nil] at hit
      · exact ⟨nofun, nofun⟩
    · have hit := mem_ite_nil' hit
      split at hit
      · exact Rope.mem_one hit ▸ ⟨nofun, nofun⟩
      · exact (setReach_set _ _ _ hit).elim fun y ⟨v, h⟩ => h ▸ ⟨nofun, nofun⟩
  · simp only [Rope.toList_app, Rope.toList_ofList, List.mem_append, List.mem_map] at he
    rcases he with (he | he) | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact (AT.regs e he).imp fun ty ⟨v, hi⟩ => ⟨v, by out_mem hi⟩
    · exact (AE.regs e he).imp fun ty ⟨v, hi⟩ => ⟨v, by out_mem hi⟩
    · exact (hiT p (carryOf_sub hp)).imp fun ty ⟨v, hi⟩ => ⟨v, by out_mem hi⟩
    · exact (hiE p (carryOf_sub hp)).imp fun ty ⟨v, hi⟩ => ⟨v, by out_mem hi⟩
  · rw [cF]
    exact (hpre k hk).elim fun new ⟨e, hd⟩ => ⟨new, e, fun q hq => (hd q hq).up nF⟩
  · rw [cF] at hq
    obtain ⟨e, he, hs⟩ : ∃ e, q.2.1 = .ite e (.var q.2.2) (.var q.1) ∧ SelOK (fun y =>
        (gm = some y ∨ qm = some y ∨ rEm = some y) ∨ InitIn T.out.toList y ∨
          InitIn E.out.toList y) e := by
      have hx' := mem_laidRegs (fun p hp => (hcpsT p (carryOf_sub hp)).2.widen m7.avoid m7.next
        m9.next) (fun p hp => (hcpsE p (carryOf_sub hp)).2.widen (m7.trans m8).avoid
          (m7.trans m8).next (Nat.le_refl _)) hx
      refine (mem_carryIns hq).elim (fun hq => (mem_carryIns hq).elim (fun hq => ?_)
        fun ⟨p, _, h⟩ => h ▸ ⟨_, rfl, SelOK.imp (fun y hy => .inl (.inl hy)) hsT⟩)
        fun ⟨p, _, h⟩ => h ▸ ⟨_, rfl, SelOK.imp (fun y hy => .inl hy) hsE⟩
      rw [S612.carries] at hq
      have hq4 : q ∉ s4.carries.getD k [] := by rw [hc4]; exact hn
      have hD := (((WE.toWMono.trans WT.toWMono).carries k q hq).resolve_left hq4).2.1
      have hxTE : q.2.2 ∈ (T.combine E).regs.toList := by
        simp only [WRes.combine, Rope.toList_app, List.mem_append]
        exact hx'.imp_right (·.resolve_right fun h => hD.disj h (Nat.le_refl _))
      obtain ⟨e, he, hs⟩ := ATE.sel k q hq hq4 hxTE
      refine ⟨e, he, SelOK.imp (fun y ⟨ty, v, hy⟩ => .inr ?_) hs⟩
      simp only [WRes.combine, Rope.toList_app, List.mem_append] at hy
      exact hy.imp (⟨ty, v, ·⟩) (⟨ty, v, ·⟩)
    refine ⟨e, he, SelOK.imp (fun y hy => ?_) hs⟩
    rcases hy with (rfl | rfl | rfl) | ⟨ty, v, hi⟩ | ⟨ty, v, hi⟩
    · exact ⟨.known HasBool.boolTy, some (.var g), by out_mem⟩
    · obtain ⟨q0, rfl⟩ := (hq11.1 rfl).1
      exact ⟨.known HasBool.boolTy, some (.var q0), by out_mem⟩
    · obtain ⟨r0, rfl⟩ := Option.isSome_iff_exists.1 (hr12.1 rfl).1
      exact ⟨.known HasBool.boolTy, some (.var r0), by out_mem⟩
    all_goals exact ⟨ty, v, by out_mem hi⟩

omit iLI iWL iOp iLF iLFs in
/-- The arm facts for a list of declared locals transfer to an equal list. -/
private theorem ArmW.congrI {I' : List P.Ident} (h : ArmW d I s s' r)
    (hI : I = I') : ArmW d I' s s' r := hI ▸ h

mutual
/-- The walk of a statement under a variable context with an obligation following it has the
    arm facts. -/
theorem wpStmt_arm {κ : RE P} (hκ : κ ≠ .top) (d : Nat) :
    ∀ (s : PStmt P) {st st' : WSt P} {r : WRes P},
      (wpStmt κ d true s).run st = .ok (r, st') → ArmW d (stmtsInits [s]) st st' r
  | .cmd (.cmd (.init x ty (.det e) md)), _, _, _, h =>
    (init_det_a hκ h).congrI (by simp [stmtsInits])
  | .cmd (.cmd (.init x ty .nondet md)), _, _, _, h =>
    (init_nondet_a h).congrI (by simp [stmtsInits])
  | .cmd (.cmd (.set x (.det e) md)), _, _, _, h => (set_det_a h).congrI (by simp [stmtsInits])
  | .cmd (.cmd (.set x .nondet md)), _, _, _, h => (set_nondet_a h).congrI (by simp [stmtsInits])
  | .cmd (.cmd (.assume ..)), _, _, _, h | .cmd (.cmd (.assert ..)), _, _, _, h
  | .cmd (.cmd (.cover ..)), _, _, _, h | .cmd (.call ..), _, _, _, h | .typeDecl .., _, _, _, h
  | .loop .., _, _, _, h | .ite .nondet .., _, _, _, h => by
    simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    first
      | (peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨_, s2, h2⟩ rfl
         obtain ⟨ht1, hc1⟩ := wRen_keep h1
         obtain ⟨ht2, hc2⟩ := liveAdd_tc h2
         exact ArmW.of_cmd (wRen_w h1) (liveAdd_w h2) (fun y hy => by rw [ht2, ht1]; exact hy)
           ht1 (by simp [stmtsInits]) (hc2.trans hc1)
           (fun it hit => by cases Rope.mem_one hit; exact ⟨nofun, nofun⟩) rfl)
      | (obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
         exact (ArmW.mk' (I := []) (fun _ h => h) nofun (by simp [Rope.toList_nil])
           (by simp [Rope.toList_nil]) (fun _ _ => ⟨[], rfl, nofun⟩)
           fun _ _ hq hq' => absurd hq hq').congrI (by simp [stmtsInits]))
      | cases h
  | .exit l md, _, _, _, h => (exit_a hκ h).congrI (by simp [stmtsInits])
  | .block l body md, _, _, _, h =>
    (block_a hκ (fun _ _ _ hB => wpList_arm hκ (d + 1) body hB) h).congrI (by simp [stmtsInits])
  | .ite (.det c) tss ess md, _, _, _, h => by
    simp only [wpStmt, ↓reduceIte] at h
    exact (laid_a (fun κ' hκ' _ _ _ hT => wpList_arm hκ' d tss hT)
      (fun κ' hκ' _ _ _ hE => wpList_arm hκ' d ess hE) h).congrI (by simp [stmtsInits])

/-- The walk of a list under a variable context with an obligation following it has the arm
    facts. -/
theorem wpList_arm {κ : RE P} (hκ : κ ≠ .top) (d : Nat) :
    ∀ (ss : PStmts P) {st st' : WSt P} {r : WRes P},
      (wpList κ d true ss).run st = .ok (r, st') → ArmW d (stmtsInits ss) st st' r
  | [], _, _, _, h => by
    unfold wpList at h
    obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
    exact ⟨fun _ h => h, by simp [stmtsInits], by simp [Rope.toList_nil], by simp [Rope.toList_nil],
      by simp [Rope.toList_nil], fun k _ => ⟨[], rfl, nofun⟩, fun k q hq hq' => absurd hq hq'⟩
  | s :: rest, _, _, _, h => by
    obtain ⟨r, st1, a, st2, h1, h2, hc⟩ := wpList_cons_arm hκ h
    have W1 := wpList_writes (D := Block.idents rest ++ Stmt.idents s) κ d true rest
      (fun _ h => List.mem_append_left _ h) h1
    have W2 := wpStmt_writes (D := Block.idents rest ++ Stmt.idents s) κ d true s
      (fun _ h => List.mem_append_right _ h) h2
    rw [stmtsInits_cons_eq]
    rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;>
      exact (wpList_arm hκ d rest h1).cons (wpStmt_arm hκ d s h2) W1 W2 rfl rfl rfl (by simp)
end

/-! ## The facts of an arm walk -/

omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL iOp iLF iLFs in
/-- A name the items declare is declared by an `init` of the items when they have no branch. -/
theorem initIn_of_wDecls : ∀ {l : List (WItem P)} {n : P.Ident},
    (∀ it ∈ l, ∀ t e, it ≠ .branch t e) → n ∈ wDecls l → InitIn l n := by
  intro l n hb h
  induction l with
  | nil => simp [wDecls] at h
  | cons it l ih => cases it <;> grind [wDecls, InitIn]

omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL iOp iLF iLFs in
/-- A name an `init` of the items declares is declared by the items. -/
theorem wDecls_of_initIn : ∀ {l : List (WItem P)} {n : P.Ident}, InitIn l n → n ∈ wDecls l := by
  rintro l n ⟨ty, v, h⟩
  induction l with
  | nil => cases h
  | cons it l ih => cases it <;> grind [wDecls]

omit iHI iLI iOp iLF in
/-- The free variables of a resolved selector over names satisfying `p` satisfy `p`. -/
theorem SelOK.fv {p : P.Ident → Prop} : ∀ {e : WExpr P} {e' : P.Expr}, SelOK p e →
      resolveE T Y e = .ok e' → ∀ y ∈ exprFV e', p y
  | .user _ _, _, h, _, _, _ => h.elim
  | .var x, _, h, he, y, hy => by
    obtain ⟨ty, rfl⟩ := resolveE_var he
    exact List.mem_singleton.1 (LawfulHasFvars.mkTypedFvar_getFvars (P := P) x ty
      (mem_exprFV.mp hy)) ▸ h
  | .lit b, _, _, he, y, hy => by
    cases he
    cases b <;> simp [mem_exprFV, WPLang.getFvars_ff, WPLang.getFvars_tt] at hy
  | .ite c t e, _, ⟨h1, h2, h3⟩, he, y, hy => by
    obtain ⟨c', t', e', hc, ht, hee, rfl⟩ := resolveE_ite.1 he
    exact ((WPLang.getFvars_ite c' t' e' y).1 (mem_exprFV.mp hy)).elim
      (SelOK.fv h1 hc y ∘ mem_exprFV.mpr) (·.elim (SelOK.fv h2 ht y ∘ mem_exprFV.mpr)
        (SelOK.fv h3 hee y ∘ mem_exprFV.mpr))

end

section
include iLI iWL iOp iLF iLFs

/-- The names the output of an arm walk declares are drawn by the walk, loop-free locals of the
    arm not yet recorded as declared, or renamings of loop-free locals of the arm. -/
theorem arm_decl {ss : PStmts P} {st st' : WSt P} (h : (wpList κ d true ss).run st = .ok (r, st'))
    (hκ : κ ≠ .top) :
    ∀ n ∈ wDecls r.out.toList, NewIn st st' n ∨
      (n ∈ stmtsInits ss ∧ st.taken.contains n = false) ∨
      ∃ x ∈ stmtsInits ss, st.nm[x]? = some n := fun n hn =>
  have A := wpList_arm hκ d ss h
  (initIn_of_wDecls A.nobr hn).elim fun ty ⟨v, hi⟩ => A.decl n ty v hi

/-- The registrations of an arm walk are declared by its output. -/
theorem arm_regs {ss : PStmts P} {st st' : WSt P} (h : (wpList κ d true ss).run st = .ok (r, st'))
    (hκ : κ ≠ .top) :
    ∀ e ∈ r.regs.toList, e ∈ wDecls r.out.toList :=
  fun e he => wDecls_of_initIn ((wpList_arm hκ d ss h).regs e he)

/-- An arm walk records the loop-free locals of the arm as declared. -/
theorem arm_takenIn {ss : PStmts P} {st st' : WSt P}
    (h : (wpList κ d true ss).run st = .ok (r, st')) (hκ : κ ≠ .top) :
    ∀ z ∈ stmtsInits ss, st'.taken.contains z = true := (wpList_arm hκ d ss h).takenIn

/-- From a state with no carried merge deeper than `d`, an arm walk at depth `d` only puts
    carried merges in front, with copies drawn by the walk. -/
theorem arm_carriesNew {ss : PStmts P} {st st' : WSt P}
    (h : (wpList κ d true ss).run st = .ok (r, st')) (hκ : κ ≠ .top)
    (hhigh : ∀ k, d < k → st.carries.getD k [] = []) :
    ∀ k, ∃ new, st'.carries.getD k [] = new ++ st.carries.getD k [] ∧
      ∀ q ∈ new, NewIn st st' q.2.2 := by
  intro k
  rcases Nat.lt_or_ge d k with hk | hk
  · refine ⟨st'.carries.getD k [], by rw [hhigh k hk, List.append_nil], fun q hq => ?_⟩
    have W := wpList_writes (D := Block.idents ss) κ d true ss (fun _ h => h) h
    exact ((W.carries k q hq).resolve_left (by simp [hhigh k hk])).2.1
  · exact (wpList_arm hκ d ss h).pre k hk

/-- The selectors of the carried merges an arm walk (from a well-formed state) registers read
    only names its output declares. -/
theorem arm_carrySel {ss : PStmts P} {st st' : WSt P}
    (h : (wpList κ d true ss).run st = .ok (r, st')) (hκ : κ ≠ .top) (hwf : WFSt st) :
    ∀ (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) k i n v xB,
      CarryReg r st' k i n v xB → ∀ e xB' x, v = .ite e (.var xB') (.var x) → ∀ e',
        resolveE T Y e = .ok e' → ∀ y ∈ exprFV e', y ∈ wDecls r.out.toList := by
  intro T Y k i n v xB ⟨hq, hx⟩ e xB' x hv e' he y hy
  have W := wpList_writes (D := Block.idents ss) κ d true ss (fun _ h => h) h
  obtain ⟨e0, he0, hs⟩ := (wpList_arm hκ d ss h).sel k _ (List.mem_of_getElem? hq) (fun h0 =>
    NewIn.not_below (W.regs xB hx) (hwf.carries_get h0).1) hx
  cases he0.symm.trans hv
  exact wDecls_of_initIn (SelOK.fv hs he y hy)

/-- A run of the resolved output of an arm walk changes only names the walk may assign (drawn
    by it, renamings of its input state, identifiers of the arm) and the reach variable of the
    context. -/
theorem arm_writes {ss : PStmts P} {st st' : WSt P}
    (h : (wpList κ d true ss).run st = .ok (r, st')) :
    ∀ T Y items, resolveItems T Y r.out.toList = .ok items → ∀ σL tr σL',
      MainRun F items σL tr σL' → ∀ n, σL' n ≠ σL n →
        Wr0 (Block.idents ss) st st' n ∨ κ.wvar = some n :=
  fun _ _ _ hi _ _ _ hm _ hn => Classical.byContradiction fun hc =>
  hn (WalkW.frame (wpList_writes κ d true ss (fun _ h => h) h) hi hm (hc ∘ .inl) (hc ∘ .inr))

/-- Under a context `andNeg q g` with `q ≠ g` whose variables are fresh names drawn before the
    walk, not avoided and no renamings, a run of the resolved output of an arm walk (from a
    state avoiding the names of the form of a fresh name of the arm) keeps `q`. -/
theorem arm_writesQ {ss : PStmts P} {st st' : WSt P}
    (h : (wpList κ d true ss).run st = .ok (r, st'))
    (hav : ∀ x ∈ Block.idents ss, ∀ b j, x = freshName b j → st.avoid.contains x = true)
    (hκv : ∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st.next) ∧
      st.avoid.contains y = false ∧ ∀ x : P.Ident, st.nm[x]? ≠ some y)
    (hqg : ∀ q g, κ = .andNeg q g → q ≠ g) :
    ∀ T Y items, resolveItems T Y r.out.toList = .ok items → ∀ σL tr σL',
      MainRun F items σL tr σL' → ∀ q g, κ = .andNeg q g → σL' q = σL q :=
  fun _ _ _ hi _ _ _ hm q g hq => keep_andNeg h hav hκv hi hm hq (hqg q g hq)

end

end -- public section

end WP
end Imperative
