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
public import Strata.Transform.WP.WPOverEffectsArm
import all Strata.Transform.WP.WPOverEffectsArm

/-! # Scope facts of arm walks

After the walk of an arm of a laid-out `ite`, the names its output declares are no renamings,
and the assigned and read names and the targets of its carried merges are current live names of
variables in scope, or declared by the output (`wpList_scope`, `ArmX`); an exit of the arm bounds
its least exit depth (`wpList_exitMin`).  The facts are restated one by one (`arm_declNotNm`,
`arm_declNotCur`, `arm_assigned`, `arm_read`, `arm_liveKeep`, `arm_carryTgt`, `arm_exitMin`).  A
declared name live after an arm walk with a stamp below the clock before it was live before it
and is a fresh name of the state before it (`arm_declNotLive`).

Key definitions: `LiveStep`, `ArmX`.

Key theorems: `wpList_scope`, `wpList_exitMin`, `arm_declNotNm`, `arm_declNotCur`,
`arm_declNotLive`, `arm_assigned`, `arm_read`, `arm_liveKeep`, `arm_carryTgt`, `arm_exitMin`. -/

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


/-! ## Scope facts of arm walks -/

/-- How a walk step changes the live set: the stamps of names other than those satisfying `E`
    are kept, a new stamp is not below the clock of the start, and the clock does not
    decrease. -/
structure LiveStep (E : P.Ident → Prop) (s s' : WSt P) : Prop where
  keep : ∀ (m : P.Ident) (t : Nat), s.live[m]? = some t → ¬ E m → s'.live[m]? = some t
  stamp : ∀ (m : P.Ident) (t : Nat), s'.live[m]? = some t → s.live[m]? = some t ∨ s.clock ≤ t
  clock : s.clock ≤ s'.clock

section
omit iLI iWL

/-- A step keeping the live set and the clock is a `LiveStep`. -/
theorem LiveStep.of_eq {E : P.Ident → Prop} (hl : s'.live = s.live)
    (hc : s'.clock = s.clock) : LiveStep E s s' := by grind [LiveStep]

/-- `LiveStep`s compose, the exceptions joining. -/
theorem LiveStep.trans {E E' : P.Ident → Prop} {s0 s1 s2 : WSt P} (h1 : LiveStep E s0 s1)
    (h2 : LiveStep E' s1 s2) : LiveStep (fun m => E m ∨ E' m) s0 s2 := by grind [LiveStep]

/-- A `LiveStep` with exceptions `E` is one with weaker exceptions. -/
theorem LiveStep.mono {E E' : P.Ident → Prop} (h : LiveStep E s s')
    (hE : ∀ m, E m → E' m) : LiveStep E' s s' := by grind [LiveStep]

/-- A `LiveStep` from a state with the live set and the clock of `s` is a `LiveStep` from `s`. -/
theorem LiveStep.pre {E : P.Ident → Prop} {s1 : WSt P} (h : LiveStep E s1 s')
    (hl : s1.live = s.live) (hc : s1.clock = s.clock) : LiveStep E s s' := by grind [LiveStep]

/-- A run of `liveAdd xs` is a `LiveStep` without exceptions that makes `xs` live. -/
theorem liveAdd_ls {E : P.Ident → Prop} {u : Unit} (h : (liveAdd xs).run s = .ok (u, s')) :
    LiveStep E s s' ∧ ∀ y ∈ xs, s'.live.contains y = true := by
  obtain ⟨live, clock, h', hc, hk, hn, hcl⟩ := liveAdd_run xs s
  cases h.symm.trans h'
  refine ⟨⟨fun m t hm _ => hk m t hm, fun m t hm => ?_, hcl⟩, fun y hy => (hc y).2 (.inr hy)⟩
  cases hs : s.live[m]? <;> grind

/-- A run of `liveDel x` is a `LiveStep` with the exception `x`. -/
theorem liveDel_ls {u : Unit} (h : (liveDel x).run s = .ok (u, s')) : LiveStep (· = x) s s' :=
  by grind [LiveStep, liveDel_run]

/-- Unfold the run `h` of a command walk under a context `κ ≠ .top` (`hκ`) into its steps down to
    the returned result, and close the target facts of its output. -/
local macro "cmd_unfold " h:ident hκ:ident : tactic => do
  let eq := Lean.mkIdent `rfl
  `(tactic| first | exact absurd rfl $hκ | (
  repeat' (first
    | (obtain ⟨_, _, _, $h:ident⟩ := wm_run_bind_ok $h)
    | split at $h:ident)
  all_goals first
    | (obtain ⟨$eq:ident, $eq:ident⟩ := wm_run_pure_ok $h)
    | skip
  all_goals first
    | (intro it hit y hy
       have hit0 := hit
       simp only [Rope.toList_app, Rope.toList_one, Rope.toList_nil, setReach, List.mem_append,
         List.mem_singleton, List.not_mem_nil, or_false, false_or] at hit
       all_goals rcases hit with $eq:ident | $eq:ident <;>
         simp only [WItem.tgt, Option.some.injEq, reduceCtorEq] at hy
       all_goals subst hy
       all_goals first
         | exact .inr (.inl ⟨_, _, hit0⟩)
         | (left; simp only [Std.HashSet.contains_ofList, List.contains_cons, BEq.rfl,
             Bool.true_or]; done)
         | (right; right; simp only [RE.vars, List.mem_cons, true_or, or_true]; done))))

include iWL in
/-- The output of the walk of a command, an `exit` or a type declaration under a variable
    context with an obligation following it only assigns names the walk assigns, names it
    declares and variables of the context. -/
private theorem cmd_tgt (hκ : κ ≠ .top) {s : PStmt P}
    (hs : (∃ c, s = .cmd c) ∨ (∃ l md, s = .exit l md) ∨ (∃ t md, s = .typeDecl t md))
    {st st' : WSt P} (h : (wpStmt κ d true s).run st = .ok (r, st')) :
    ∀ it ∈ r.out.toList, ∀ y, it.tgt = some y →
      r.A.contains y = true ∨ InitIn r.out.toList y ∨ y ∈ RE.vars κ := by
  rcases hs with ⟨c, rfl⟩ | ⟨l, md, rfl⟩ | ⟨t, md, rfl⟩
  · cases c with
    | call => simp only [wpStmt] at h; cases h
    | cmd c =>
      cases c with
      | init _ _ e _ | set _ e _ =>
        cases e <;>
          simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h <;>
          cases κ <;> cmd_unfold h hκ
      | _ =>
        simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cmd_unfold h hκ
  · unfold wpStmt at h
    cases κ <;> cmd_unfold h hκ
  · simp only [wpStmt] at h
    cmd_unfold h hκ

/-- The scope facts of the walk of a fragment reading `V` well scoped from `S`, from `s` to `s'`
    with result `r`: the names its output declares are no renamings after it; an assigned name,
    a read name and the target of a carried merge the result registers are each the current live
    name after the walk of a variable of `S` the fragment reads, or declared by the output; the
    live set keeps the stamps of the current names before the walk of the variables of `S`; a
    name the output declares with a stamp after the walk older than the clock before it is drawn
    by the walk. -/
structure ArmScope (S V : List P.Ident) (s s' : WSt P) (r : WRes P) : Prop where
  declNm : ∀ n ty v, WItem.init n ty v ∈ r.out.toList → ∀ x : P.Ident, s'.nm[x]? ≠ some n
  asg : ∀ n, r.A.contains n = true → (∃ z ∈ S, z ∈ V ∧ curName s' z = some n ∧
    s'.live.contains n = true) ∨ InitIn r.out.toList n
  rd : ∀ n, r.R.contains n = true → (∃ z ∈ S, z ∈ V ∧ curName s' z = some n ∧
    s'.live.contains n = true) ∨ InitIn r.out.toList n
  ctgt : ∀ k q, q ∈ s'.carries.getD k [] → q ∉ s.carries.getD k [] → q.2.2 ∈ r.regs.toList →
    (∃ z ∈ S, z ∈ V ∧ curName s' z = some q.1 ∧ s'.live.contains q.1 = true) ∨
      InitIn r.out.toList q.1
  live : LiveStep (fun m => ¬ ∃ z ∈ S, curName s z = some m) s s'
  old : ∀ n ty v, WItem.init n ty v ∈ r.out.toList → ∀ t, s'.live[n]? = some t → t < s.clock →
    NewIn s s' n

/-- The scope facts `ArmScope` of a walk under the context `κ`, and the targets of its output:
    every name an item of the output assigns is a name the walk assigns, a name its output
    declares, a variable of `κ`, or the current name after the walk of a variable of `S`. -/
structure ArmX (κ : RE P) (S V : List P.Ident) (s s' : WSt P) (r : WRes P) : Prop
    extends ArmScope S V s s' r where
  tgt : ∀ it ∈ r.out.toList, ∀ y, it.tgt = some y → r.A.contains y = true ∨
    InitIn r.out.toList y ∨ y ∈ RE.vars κ ∨ ∃ z ∈ S, curName s' z = some y

include iWL in
/-- The walk of a command, an `exit` or a type declaration under a variable context with an
    obligation following it has the facts of `ArmX` when it has those of `ArmScope`. -/
private theorem ArmX.of_cmd (hκ : κ ≠ .top) {s : PStmt P}
    (hs : (∃ c, s = .cmd c) ∨ (∃ l md, s = .exit l md) ∨ (∃ t md, s = .typeDecl t md))
    {S V : List P.Ident} {st st' : WSt P} (h : (wpStmt κ d true s).run st = .ok (r, st'))
    (X : ArmScope S V st st' r) :
    ArmX κ S V st st' r :=
  { X with tgt := fun it hit y hy => (cmd_tgt hκ hs h it hit y hy).imp_right (.imp_right .inl) }

/-- A run of `liveAdd` keeps the renamings and the avoided names. -/
theorem liveAdd_nm {u : Unit}
    (h : (liveAdd xs).run s = .ok (u, s')) : s'.nm = s.nm ∧ s'.next = s.next := by
  obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h
  exact ⟨rfl, rfl⟩

/-- A run of `liveDel` keeps the renamings and the counter. -/
theorem liveDel_nm {u : Unit}
    (h : (liveDel x).run s = .ok (u, s')) : s'.nm = s.nm ∧ s'.next = s.next :=
  by grind [liveDel_run]

/-- A run of `liveAdd` keeps the current names. -/
private theorem liveAdd_cur {u : Unit}
    (h : (liveAdd xs).run s = .ok (u, s')) : ∀ z, curName s' z = curName s z :=
  curName_eq_of_nm_taken (liveAdd_nm h).1 (liveAdd_tc h).1

end

/-- A run of `wRen` keeps the live set and the clock, and the read names are current names of
    free variables of the expression after it. -/
theorem wRen_live {e : P.Expr} {we : WExpr P} {rd : List P.Ident}
    (h : (wRen e).run s = .ok ((we, rd), s')) : s'.live = s.live ∧ s'.clock = s.clock ∧
      ∀ n ∈ rd, ∃ y ∈ exprFV e, curName s' y = some n := by
  obtain ⟨⟨-, -, -, -, hrd⟩, -, hst, -⟩ := wRen_run h
  exact ⟨by rw [hst], by rw [hst], hrd⟩

/-- A run of `wName x` keeps the live set and the clock and changes the renamings only at `x`;
    the returned name is the renaming of `x` or a name not a renaming before. -/
theorem wName_nmx (h : (wName x).run s = .ok (n, s')) :
    s'.live = s.live ∧ s'.clock = s.clock ∧ (∀ y, y ≠ x → s'.nm[y]? = s.nm[y]?) ∧
      (s.nm[x]? = some n ∨ (n = x ∧ s.taken.contains x = false) ∨
        ∃ k, n = freshName (baseOf x) k ∧ s.next ≤ k) := by
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨-, h2, rfl, rfl⟩ | ⟨h1, h2, -, rfl⟩
  · exact ⟨rfl, rfl, fun _ _ => rfl, .inl h1⟩
  · exact ⟨rfl, rfl, fun _ _ => rfl, .inr (.inl ⟨rfl, h2⟩)⟩
  · obtain ⟨k, hk, hn, -⟩ := wName_fresh h h1 h2
    exact ⟨rfl, rfl, fun y hy => by grind, .inr (.inr ⟨k, hk, hn⟩)⟩

omit iWL in
/-- A name with a counter from `s.next` on is no renaming of a well-formed state `s`. -/
theorem WFSt.nm_ne_new (hw : WFSt s) (hy : s.nm[y]? = some n) {b : String} {k : Nat}
    (hn : n = freshName b k) (hk : s.next ≤ k) : False := by
  obtain ⟨-, b', j, rfl, hj, -⟩ := hw.nm_fresh y n hy
  exact absurd (freshName_counter_inj hn) (by omega)

/-- The name `wDecl x` returns at a well-formed state, for `x` avoided when of fresh-name form,
    is no renaming of another variable after it. -/
theorem wDecl_notNm (hw : WFSt s) (hx : ∀ b j, x = freshName b j → s.avoid.contains x = true)
    (h : (wDecl x).run s = .ok (n, s')) (y : P.Ident) : s'.nm[y]? ≠ some n := by
  intro hy
  obtain ⟨n1, s1, h1⟩ := wName_ok x s
  cases (wDecl_run h1).symm.trans h
  obtain ⟨-, -, hnm, hc⟩ := wName_nmx h1
  have hyx : y ≠ x := by grind
  replace hy : s.nm[y]? = some n := by grind
  rcases hc with h2 | ⟨rfl, -⟩ | ⟨k, rfl, hk⟩
  · exact hyx (hw.nm_inj y x n hy h2)
  · obtain ⟨-, b, j, hb, -, hav⟩ := hw.nm_fresh y n hy
    simp [hx b j hb] at hav
  · exact hw.nm_ne_new hy rfl hk

/-- The name a run of `wName x` returns at a well-formed state is no current name there of
    another variable avoided if of fresh-name form, when `x` is avoided if of fresh-name form. -/
theorem wName_notCur (hw : WFSt s) (hx : ∀ b j, x = freshName b j → s.avoid.contains x = true)
    (h : (wName x).run s = .ok (n, s')) {z : P.Ident} (hzx : z ≠ x)
    (hz : ∀ b j, z = freshName b j → s.avoid.contains z = true) : curName s z ≠ some n := by
  intro hc
  have hcs : s.nm[z]? = some n ∨ z = n := by grind [curName]
  rcases wName_cases h with ⟨h1, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩
  · rcases hcs with hcs | rfl
    · exact hzx (hw.nm_inj z x n hcs h1)
    · obtain ⟨-, b, j, he, -, hna⟩ := hw.nm_fresh x z h1
      simp [hz b j he] at hna
  · obtain ⟨-, b, j, he, -, hna⟩ := hw.nm_fresh z _ (hcs.resolve_right hzx)
    simp [hx b j he] at hna
  · obtain ⟨k, hk, hk1, hk2⟩ := freshIn_spec s.avoid (baseOf x) s.next
    rw [hk] at hcs
    exact hcs.elim (hw.nm_ne_new · rfl hk1) (by rintro rfl; simp [hz _ _ rfl] at hk2)

omit iLI in
/-- After a run of `wName x`, the renaming of `x` is the returned name, and the other renamings
    are those before it. -/
theorem wName_nm_after (h : (wName x).run s = .ok (n, s')) (y v : P.Ident)
    (hy : s'.nm[y]? = some v) : (y = x ∧ v = n) ∨ s.nm[y]? = some v := by
  rcases wName_cases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl, rfl⟩ <;> grind

omit iLI in
/-- After a run of `wDecl`, every renaming is one before it. -/
theorem wDecl_nmOld (h : (wDecl x).run s = .ok (n, s')) (y v : P.Ident)
    (hy : s'.nm[y]? = some v) : s.nm[y]? = some v := by
  obtain ⟨n1, s1, h1⟩ := wName_ok x s
  cases (wDecl_run h1).symm.trans h
  exact (wName_nm_after h1 y v (by grind)).resolve_left (by grind)

/-- The scope facts of the walk of a deterministic `init` with an obligation following it. -/
private theorem init_det_x (hκ : κ ≠ .top) {ty : P.Ty} {e : P.Expr} {md : MetaData P}
    {Lc S : List P.Ident}
    (h : (wpStmt κ d true (.cmd (.cmd (.init x ty (.det e) md)))).run s = .ok (r, s'))
    (hwf : WFSt s) (hx : ∀ b j, x = freshName b j → s.avoid.contains x = true)
    (havS : ∀ z ∈ S, ∀ b j, z = freshName b j → s.avoid.contains z = true)
    (hS : Stmt.WellScoped Lc S (.cmd (.cmd (.init x ty (.det e) md)))) :
    ArmScope S (Block.freeVars [.cmd (.cmd (.init x ty (.det e) md))]) s s' r := by
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨n, s2, h2⟩ _ ⟨xd, s4, h4⟩ _ ⟨_, s5, h5⟩ ⟨_, s6, h6⟩ rfl
  obtain ⟨⟨-, -, -, -, hrd⟩, -, hs1, hcur1⟩ := wRen_run h1
  have hw1 : WFSt s1 := (wRen_walk h1).wf hwf nofun
  have m1 := wRen_w (D := []) h1
  have hx1 : ∀ b j, x = freshName b j → s1.avoid.contains x = true := m1.avoid ▸ hx
  obtain ⟨⟨s1', h1'⟩, -, hcur2, -, hs2⟩ := wDecl_spec h2
  have m2 := (wDecl_k (D := []) h2).1
  obtain ⟨-, n4, t4, l4, c4, -, c4', -⟩ := wFresh_laidSame h4
  have m6 : WMono [] s4 s6 := (WMono.same).trans ((liveDel_w h5).trans (liveAdd_w h6))
  have hl5 : s5.live = s4.live.erase n := by cases h5; rfl
  have hcur : ∀ z, z ∈ S → curName s6 z = curName s1 z := fun z hz =>
    (liveAdd_cur h6 z).trans <|
      (curName_eq_of_nm_taken (liveDel_nm h5).1 (liveDel_tc h5).1 z).trans <|
      (curName_eq_of_nm_taken n4 t4 z).trans <| hcur2 z fun e => hS.1 (e ▸ hz)
  obtain ⟨-, hd⟩ := wFresh_w (D := []) h4
  have hi : ∀ m t v, WItem.init m t v ∈ ((Rope.one (WItem.init xd (.known ty) none)).app
      (Rope.one (WItem.init n (.known ty) (some (kIte κ we (.var xd)))))).toList → m = xd ∨ m = n :=
    fun m t v hit => by grind [Rope.toList_app, Rope.toList_one]
  refine ⟨fun m t v hit y hy => ?_, fun m hm => by simp at hm, fun m hm => ?_,
    fun k q hq hq' => absurd (by grind [wRen_keep h1, wDecl_k (D := []) h2,
      liveDel_tc h5, liveAdd_tc h6]) hq', ?_, fun m t v hit k ht hlt => ?_⟩
  · have hy' : s2.nm[y]? = some m := (n4.symm.trans ((liveDel_nm h5).1.symm.trans
      (liveAdd_nm h6).1.symm)) ▸ hy
    rcases hi m t v hit with rfl | rfl
    · obtain ⟨b, j, he, -, hj, -⟩ := hd
      exact hw1.nm_ne_new (wDecl_nmOld h2 y m hy') he (Nat.le_trans m2.next hj)
    · exact wDecl_notNm hw1 hx1 h2 y hy'
  · have hm' : m ∈ rd := by simpa using hm
    obtain ⟨y, hy, hcy⟩ := hrd m hm'
    exact .inl ⟨y, hS.2.2 y hy, by simp [Block.freeVars, hy], (hcur y (hS.2.2 y hy)).trans hcy,
      (liveAdd_ls (E := fun _ => False) h6).2 _ (List.mem_append_left _ hm')⟩
  · refine (((liveDel_ls h5).mono fun m hm ⟨z, hz, hc⟩ => wName_notCur hw1 hx1 h1'
      (fun e => hS.1 (e ▸ hz)) (m1.avoid ▸ havS z hz) (hm ▸ hcur1 z m hc)).trans
      (liveAdd_ls h6).1).mono (fun m h => h.elim id id) |>.pre (by rw [l4, hs2, hs1])
      (by rw [c4, hs2, hs1])
  · rcases hi m t v hit with rfl | rfl
    · exact hd.widen (m1.trans m2).avoid (m1.trans m2).next m6.next
    · rcases (liveAdd_ls (E := fun _ => False) h6).1.stamp _ _ ht with h | h
      · simp [hl5] at h
      · have hc5 : s5.clock = s.clock := by cases h5; rw [c4, hs2, hs1]
        omega

/-- A run of `wName x` from a well-formed state returns a renaming of the state, `x` itself, or
    a name with a counter below the counter after it. -/
theorem wName_below (hw : WFSt s) (h : (wName x).run s = .ok (n, s')) :
    (∃ b j, n = freshName b j ∧ j < s'.next) ∨ n = x := by
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨h1, h2, -, -⟩
  · obtain ⟨-, b, j, rfl, hj, -⟩ := hw.nm_fresh x n h1
    exact .inl ⟨b, j, rfl, hj⟩
  · exact .inr rfl
  · obtain ⟨k, rfl, -, hk, -⟩ := wName_fresh h h1 h2
    exact .inl ⟨_, k, rfl, by omega⟩

/-- The scope facts of the walk of a nondeterministic `init` with an obligation following it. -/
private theorem init_nondet_x {ty : P.Ty} {md : MetaData P} {S : List P.Ident}
    (h : (wpStmt κ d true (.cmd (.cmd (.init x ty .nondet md)))).run s = .ok (r, s')) (hwf : WFSt s)
    (hx : ∀ b j, x = freshName b j → s.avoid.contains x = true)
    (havS : ∀ z ∈ S, ∀ b j, z = freshName b j → s.avoid.contains z = true) (hxS : x ∉ S) :
    ArmScope S (Block.freeVars [.cmd (.cmd (.init x ty .nondet md))]) s s' r := by
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  peel h ⟨n, s2, h2⟩ _ ⟨_, s5, h5⟩ rfl
  obtain ⟨⟨s1, h1⟩, -, -, -, hs⟩ := wDecl_spec h2
  have hl5 : s5.live = s2.live.erase n := by cases h5; rfl
  refine ⟨fun m ty v hit y => ?_, fun m hm => by simp at hm, fun m hm => by simp at hm,
    fun k q hq hq' => absurd (by grind [wDecl_k (D := []) h2, liveDel_tc h5]) hq',
    ((liveDel_ls h5).mono fun m hm ⟨z, hz, hc⟩ => wName_notCur hwf hx h1
      (fun e => hxS (e ▸ hz)) (havS z hz) (hm ▸ hc)).pre (by rw [hs]) (by rw [hs]),
    fun m ty v hit t ht => ?_⟩ <;> cases Rope.mem_one hit
  · exact (liveDel_nm h5).1 ▸ wDecl_notNm hwf hx h2 y
  · simp [hl5] at ht

omit iLI iWL in
/-- A run of `liveAdd` keeps every live name live. -/
theorem liveAdd_keepC {u : Unit} (h : (liveAdd xs).run s = .ok (u, s')) (y : P.Ident)
    (hy : s.live.contains y = true) :
    s'.live.contains y = true := by
  obtain ⟨live, clock, rfl, hl⟩ := liveAdd_step h
  exact (hl y).2 (.inl hy)

/-- The scope facts of the walk of a deterministic `set` with an obligation following it. -/
private theorem set_det_x (hκ : κ ≠ .top) {e : P.Expr} {md : MetaData P} {Lc S : List P.Ident}
    (h : (wpStmt κ d true (.cmd (.cmd (.set x (.det e) md)))).run s = .ok (r, s'))
    (hS : Stmt.WellScoped Lc S (.cmd (.cmd (.set x (.det e) md)))) :
    ArmScope S (Block.freeVars [.cmd (.cmd (.set x (.det e) md))]) s s' r := by
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨n, s2, h2⟩ ⟨_, s3, h3⟩ ⟨_, s4, h4⟩ rfl
  obtain ⟨hl1, hc1, hrd⟩ := wRen_live h1
  obtain ⟨hl2, hc2, -⟩ := wName_nmx h2
  have hcur : ∀ z m, curName s2 z = some m → curName s4 z = some m := fun z m h =>
    (liveAdd_cur h4 z).trans ((liveAdd_cur h3 z).trans h)
  refine ⟨fun n ty v hit => (by cases Rope.mem_one hit), fun m hm => ?_, fun m hm => ?_,
    fun k q hq hq' => absurd (by grind [wRen_keep h1, wName_keep h2, liveAdd_tc h3,
      liveAdd_tc h4]) hq',
    (((liveAdd_ls h3).1.trans (liveAdd_ls h4).1).mono fun _ h => h.elim id id).pre
      (hl2.trans hl1) (hc2.trans hc1), fun n ty v hit => (by cases Rope.mem_one hit)⟩
  · cases contains_one hm
    exact .inl ⟨x, hS.1, by simp [Block.freeVars, Stmt.freeVars], hcur x _ (wName_curName h2),
      liveAdd_keepC h4 _ ((liveAdd_ls (E := fun _ => False) h3).2 _ (List.mem_singleton_self _))⟩
  · have hm' : m ∈ rd := by simpa using hm
    obtain ⟨y, hy, hcy⟩ := hrd m hm'
    exact .inl ⟨y, hS.2 y hy, by simp [Block.freeVars, Stmt.freeVars, hy],
      hcur y _ (wName_curName_keep h2 y m hcy),
      (liveAdd_ls (E := fun _ => False) h4).2 _ (List.mem_append_left _ hm')⟩

/-- The scope facts of the walk of a nondeterministic `set` with an obligation following it. -/
private theorem set_nondet_x (hκ : κ ≠ .top) {md : MetaData P} {Lc S : List P.Ident}
    (h : (wpStmt κ d true (.cmd (.cmd (.set x .nondet md)))).run s = .ok (r, s')) (hwf : WFSt s)
    (hx : ∀ b j, x = freshName b j → s.avoid.contains x = true)
    (hS : Stmt.WellScoped Lc S (.cmd (.cmd (.set x .nondet md)))) :
    ArmScope S (Block.freeVars [.cmd (.cmd (.set x .nondet md))]) s s' r := by
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  peel h ⟨n, s2, h2⟩ ⟨xh, s3, h3⟩ ⟨_, s4, h4⟩ rfl
  obtain ⟨hl2, hc2, -⟩ := wName_nmx h2
  obtain ⟨-, n3, t3, hl3, hc3, -, c3, -⟩ := wFreshLike_laidSame h3
  obtain ⟨n4, x4⟩ := liveAdd_nm h4
  have m2 := (wName_w (D := []) h2).1
  have hd0 := (wFreshLike_w (D := []) h3).2
  have hi : ∀ m ty v, WItem.init m ty v ∈ ((Rope.one (WItem.init xh (.of n) none)).app
      (Rope.one (WItem.set n (some (kIte κ (.var xh) (.var n)))))).toList → m = xh :=
    fun m ty v hit => by grind [Rope.toList_app, Rope.toList_one]
  refine ⟨fun m ty v hit y hy => ?_, fun m hm => ?_, fun m hm => by simp at hm,
    fun k q hq hq' => absurd (by grind [wName_keep h2, liveAdd_tc h4]) hq',
    (liveAdd_ls h4).1.pre (hl3.trans hl2) (hc3.trans hc2),
    fun m ty v hit _ _ _ => hi m ty v hit ▸ hd0.widen m2.avoid m2.next (Nat.le_of_eq x4.symm)⟩
  · cases hi m ty v hit
    obtain ⟨b, j, he, ha, hj, -⟩ := hd0
    rcases wName_nm_after h2 y xh (by rw [← n3, ← n4]; exact hy) with ⟨rfl, rfl⟩ | hy
    · rcases wName_below hwf h2 with ⟨b', j', he', hj'⟩ | rfl
      · exact absurd (freshName_counter_inj (he.symm.trans he')) (by omega)
      · simp [hx b j he, m2.avoid] at ha
    · exact hwf.nm_ne_new hy he (Nat.le_trans m2.next hj)
  · cases contains_one hm
    refine .inl ⟨x, hS, by simp [Block.freeVars, Stmt.freeVars], ?_,
      (liveAdd_ls (E := fun _ => False) h4).2 _
      (List.mem_cons_self ..)⟩
    rw [liveAdd_cur h4, curName_eq_of_nm_taken n3 t3]
    exact wName_curName h2

/-- A walk step made of a renaming of an expression reading variables of `S` that the fragment
    reads (`V`) and an insertion into the live set of the read names, returning an output
    without `init`s with the read names as `R`, has the scope facts. -/
private theorem ren_live_x {e : P.Expr} {S V : List P.Ident} {g : WExpr P × List P.Ident → WRes P}
    (hFV : ∀ y ∈ exprFV e, y ∈ S ∧ y ∈ V)
    (hg : ∀ p, (∀ it ∈ (g p).out.toList, ∀ n ty v, it ≠ .init n ty v) ∧ (g p).A = {} ∧
      (g p).R = Std.HashSet.ofList p.2)
    (h : (do let p ← wRen e; liveAdd (p.2 ++ xs); pure (g p) : WM P (WRes P)).run s = .ok (r, s')) :
    ArmScope S V s s' r := by
  peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨_, s2, h2⟩ rfl
  obtain ⟨hi, hA, hR⟩ := hg (we, rd)
  obtain ⟨hl1, hc1, hrd⟩ := wRen_live h1
  have k1 := wRen_keep h1
  have k2 := liveAdd_tc h2
  refine ⟨fun n ty v hit => absurd rfl (hi _ hit n ty v), fun n hn => by simp [hA] at hn,
    fun n hn => ?_, fun k q hq hq' => absurd (by grind) hq', (liveAdd_ls h2).1.pre hl1 hc1,
    fun n ty v hit => absurd rfl (hi _ hit n ty v)⟩
  have hn' : n ∈ rd := by simpa [hR] using hn
  obtain ⟨y, hy, hcy⟩ := hrd n hn'
  exact .inl ⟨y, (hFV y hy).1, (hFV y hy).2, liveAdd_cur h2 y ▸ hcy,
    (liveAdd_ls (E := fun _ => False) h2).2 n (List.mem_append_left _ hn')⟩

/-- The scope facts of the walk of an `exit` under a variable context with an obligation
    following it, from a well-formed state. -/
private theorem exit_x (hκ : κ ≠ .top) {l : String} {md : MetaData P} {S V : List P.Ident}
    (hwf : WFSt s)
    (h : (wpStmt κ d true (.exit l md)).run s = .ok (r, s')) : ArmScope S V s s' r := by
  rcases exit_inv hκ h with ⟨t, -, ⟨⟨⟩, -⟩ | ⟨-, e, s2, h2, h4, rfl⟩⟩ | ⟨-, rfl, ⟨⟨⟩, -⟩ | ⟨-, rfl⟩⟩
  · obtain ⟨-, hn2, -, hl2, hc2, -, c2, -⟩ := wFreshBool_laidSame h2
    obtain ⟨-, hd2⟩ := wFreshBool_w (D := []) h2
    have hie : ∀ n ty v, WItem.init n ty v ∈ (Rope.app (.one (.init e (.known HasBool.boolTy)
        (some (kExpr κ)))) (setReach κ (.lit false))).toList → n = e := by
      grind [Rope.toList_app, Rope.toList_one, setReach_set]
    refine ⟨fun n ty v hi x hx => ?_, fun _ h => by simp at h, fun _ h => by simp at h,
      fun k q hq hn => absurd ?_ hn, (liveAdd_ls h4).1.pre hl2 hc2,
      fun n ty v hi _ _ _ => hie n ty v hi ▸ hd2.up (liveAdd_w (D := []) h4).next⟩
    · obtain rfl := hie n ty v hi
      obtain ⟨b, j, rfl, -, hj, -⟩ := hd2
      exact hwf.nm_ne_new (hn2 ▸ (liveAdd_nm h4).1 ▸ hx) rfl hj
    · rw [(liveAdd_tc h4).2] at hq
      exact c2 ▸ hq
  · refine ⟨fun _ _ _ hi => ?_, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ _ h hn => absurd h hn, LiveStep.of_eq rfl rfl, fun _ _ _ hi => ?_⟩
    all_goals grind [setReach_set]

omit iLI iWL in
/-- Entering a block (a label with a depth, an empty snapshot list, a stamp and an empty list
    of carried merges at the new depth) keeps a state well formed. -/
theorem WFSt.block_entry (hw : WFSt s) (l : String) (k t : Nat) :
    WFSt { s with pending := s.pending.insert l [], labelDepth := s.labelDepth.insert l k
                  stampAt := s.stampAt.insert k t, carries := s.carries.insert k [] } := { hw with
    pending_fresh := fun l' e he => hw.pending_fresh l' e (by grind)
    carries_fresh := fun k' i n v xB he => hw.carries_fresh k' i n v xB (by grind)
    carries_sel := fun k' i n v xB he => hw.carries_sel k' i n v xB (by grind) }

/-- The scope facts of the walk of a block under a variable context with an obligation
    following it, from those of its body. -/
private theorem block_x (hκ : κ ≠ .top) {l : String} {body : PStmts P} {md : MetaData P}
    {S : List P.Ident} (hwf : WFSt s)
    (hL : ∀ (l : String) (t : Nat), s.labelDepth[l]? = some t → t ≤ d)
    (hB : ∀ s0 B s1, (wpList κ (d + 1) true body).run s0 = .ok (B, s1) → WFSt s0 →
      (∀ (l : String) (t : Nat), s0.labelDepth[l]? = some t → t ≤ d + 1) → s0.avoid = s.avoid →
      ArmX κ S (Block.freeVars body) s0 s1 B)
    (h : (wpStmt κ d true (.block l body md)).run s = .ok (r, s')) :
    ArmX κ S (Block.freeVars body) s s' r := by
  obtain ⟨s0, B, s4, rfl, hB4, h5, rfl⟩ := block_inv hκ h
  have hL0 : ∀ (l' : String) (t : Nat), (s.labelDepth.insert l (d + 1))[l']? = some t →
      t ≤ d + 1 := fun l' t ht => by
    rw [Std.HashMap.getElem?_insert] at ht
    split at ht <;> grind
  have XB := hB _ _ _ hB4 (hwf.block_entry l (d + 1) s.clock) hL0 rfl
  have hreg := (body_carries hκ hL0 (by simp) hB4).1
  have hcur : ∀ z, curName s' z = curName s4 z :=
    curName_eq_of_nm_taken (liveAdd_nm h5).1 (liveAdd_tc h5).1
  have hlift : ∀ n, (∃ z ∈ S, z ∈ Block.freeVars body ∧ curName s4 z = some n ∧
      s4.live.contains n = true) → ∃ z ∈ S, z ∈ Block.freeVars body ∧ curName s' z = some n ∧
      s'.live.contains n = true := fun n ⟨z, hz, hv, hc, hl⟩ =>
    ⟨z, hz, hv, (hcur z).trans hc, liveAdd_keepC h5 _ hl⟩
  have hin : ∀ n, InitIn B.out.toList n → ∀ X Y : Rope (WItem P),
      InitIn ((B.out.app X).app Y).toList n := fun n ⟨ty, v, h⟩ X Y =>
    ⟨ty, v, by simp [Rope.toList_app, h]⟩
  have hk : ∀ k q, q ∈ s'.carries.getD k [] → d + 1 ≠ k ∧ q ∈ s4.carries.getD k [] :=
    fun k q hq => by
      rw [(liveAdd_tc h5).2, Std.HashMap.getD_erase] at hq
      split at hq
      · simp at hq
      · rename_i hne
        exact ⟨by simpa using hne, hq⟩

  refine ⟨⟨fun n ty v hit x => ?_, fun n hn => ?_, fun n hn => (XB.rd n hn).imp (hlift n)
    (hin n · _ _), fun k q hq hq' hr => ?_, ?_, fun n ty v hit t ht hlt => ?_⟩,
    fun it hit y hy => ?_⟩
  · rcases mem_block_out hit with hit | ⟨_, _, ⟨⟩⟩
    exact (liveAdd_nm h5).1 ▸ XB.declNm n ty v hit x
  · rcases (mem_insert_merges _ _).1 hn with hn | ⟨q, hq, rfl⟩
    · exact (XB.asg n hn).imp (hlift n) (hin n · _ _)
    · exact (XB.ctgt (d + 1) q (List.mem_filter.1 hq).1 (by simp) (hreg q hq)).imp (hlift _)
        (hin _ · _ _)
  · obtain ⟨hk, hq4⟩ := hk k q hq
    exact (XB.ctgt k q hq4 (by simpa [Std.HashMap.getD_insert, hk] using hq') hr).imp (hlift _)
      (hin _ · _ _)
  · exact ((XB.live.trans ((liveAdd_ls h5).1.pre rfl rfl)).mono fun m h => h.elim id id).pre rfl rfl
  · rcases mem_block_out hit with hit | ⟨_, _, ⟨⟩⟩
    rcases (liveAdd_ls (E := fun _ => False) h5).1.stamp _ _ ht with h | h
    · exact (XB.old n ty v hit t h hlt).up (Nat.le_of_eq (liveAdd_nm h5).2.symm)
    · exact absurd (Nat.lt_of_lt_of_le hlt XB.live.clock) (Nat.not_lt.2 h)
  · simp only [Rope.toList_app, List.mem_append] at hit
    rcases hit with (hit | hit) | hit
    · grind [XB.tgt it hit y hy, mem_insert_merges, Rope.toList_app, InitIn]
    · obtain ⟨q, hq, rfl⟩ := (mem_sets _ _ hit).resolve_left (by simp [Rope.toList_nil])
      exact Option.some.inj hy ▸ .inl ((mem_insert_merges _ _).2 (.inr ⟨q, hq, rfl⟩))
    · exact .inr (.inr (.inl (wvar_mem (setReach_tgt _ _ _ (mem_ite_nil (mem_ite_nil hit)) y hy))))

/-- Transfers a name the arms of a laid-out `ite` may assign (a current live name at the end of
    the arms, or a name an arm declares) to the end of the walk of the `ite`, from the run `hFr`
    of its final `liveAdd` and the equality `hcur` of the current names after and before it. -/
local macro "lift_x " hcur:ident hFr:ident t:term : tactic => `(tactic| (
  rcases ($t) with ⟨z, hz, hv, hcz, hl⟩ | hi
  · exact .inl ⟨z, hz, hv, by rw [$hcur:ident]; exact hcz, liveAdd_keepC $hFr _ hl⟩
  first | (rcases hi with ⟨ty, v, hi⟩ | ⟨ty, v, hi⟩) | obtain ⟨ty, v, hi⟩ := hi
  all_goals exact .inr ⟨ty, v, by out_mem hi⟩))

omit iLI iWL in
/-- The scope facts of a walk from those of its declared names: each name the output declares
    has the property `Q`, and every name with `Q` is no renaming after the walk and, live after
    the walk with a stamp below the clock before it, is drawn by the walk. -/
private theorem ArmScope.of_cls {S V : List P.Ident} (Q : P.Ident → Prop)
    (hQ : ∀ n ty v, WItem.init n ty v ∈ r.out.toList → Q n)
    (hnm : ∀ n, Q n → ∀ x : P.Ident, s'.nm[x]? ≠ some n)
    (hold : ∀ n, Q n → ∀ t, s'.live[n]? = some t → t < s.clock → NewIn s s' n)
    (h : (∀ n ty v, WItem.init n ty v ∈ r.out.toList → ∀ x : P.Ident, s'.nm[x]? ≠ some n) →
      (∀ n ty v, WItem.init n ty v ∈ r.out.toList → ∀ t, s'.live[n]? = some t → t < s.clock →
      NewIn s s' n) → ArmScope S V s s' r) : ArmScope S V s s' r :=
  h (fun n ty v hi => hnm n (hQ n ty v hi)) fun n ty v hi => hold n (hQ n ty v hi)

omit iLI iWL in
/-- A live name outside the exceptions of a `LiveStep` stays live. -/
private theorem LiveStep.keepC {E : P.Ident → Prop} (h : LiveStep E s s')
    (hn : s.live.contains n = true) (hE : ¬ E n) :
    s'.live.contains n = true := by
  simp only [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists] at hn ⊢
  exact hn.imp fun t ht => h.keep n t ht hE

/-- Close the goal that a name an `init` of an arm output declares is declared by the output of a
    laid-out `ite`. -/
local macro "laidx_init " h:ident : tactic => `(tactic| (
  obtain ⟨ty, v, hi⟩ := $h:ident
  exact .inr (.inl ⟨ty, v, by simp only [List.mem_append, hi, true_or, or_true]⟩)))

omit iLI in
/-- A run of `wName x` at a state where `x` has the current name `n` returns `n`. -/
theorem wName_eq_cur {n' : P.Ident} (hc : curName s x = some n)
    (h : (wName x).run s = .ok (n', s')) : n' = n := by
  rcases wName_cases h with ⟨h1, -⟩ | ⟨h1, h2, rfl, -⟩ | ⟨h1, h2, -⟩ <;> simp_all [curName]

/-- The walk of a statement with an obligation following it declares the current name before
    it of the variable `z` that the statement declares at top level. -/
theorem init_decl_cur (hκ : κ ≠ .top) {z : P.Ident} {t : PStmt P} {a : WRes P}
    (h : (wpStmt κ d true t).run s = .ok (a, s')) (hz : z ∈ Stmt.topInits t)
    (hc : curName s z = some n) : InitIn a.out.toList n := by
  obtain ⟨ty, e, md, rfl⟩ : ∃ ty e md, t = .cmd (.cmd (.init z ty e md)) := by
    unfold Stmt.topInits at hz
    split at hz <;> simp_all
  cases e <;> simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  · peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨n', s2, h2⟩ _
    obtain ⟨⟨s3, h3⟩, -⟩ := wDecl_spec h2
    obtain rfl := wName_eq_cur ((wRen_run h1).2.2.2 z n hc) h3
    cases κ
    · exact absurd rfl hκ
    all_goals
      peel h ⟨xd, s4, -⟩ _ ⟨_, _, -⟩ ⟨_, _, -, ⟨⟩⟩
      rw [InitIn, Rope.toList_app, Rope.toList_one, Rope.toList_one]
      exact ⟨_, _, .tail _ (.head _)⟩
  · peel h ⟨n', s2, h2⟩ _ ⟨_, _, -, ⟨⟩⟩
    obtain ⟨⟨s3, h3⟩, -⟩ := wDecl_spec h2
    obtain rfl := wName_eq_cur hc h3
    rw [InitIn, Rope.toList_one]
    exact ⟨_, _, .head _⟩

omit iDE iHB iHF iSF iHI iLI iWL in
/-- The variables a statement reads are read by a list headed by it. -/
theorem fv_head {s : PStmt P} {rest : PStmts P} {z : P.Ident} (h : z ∈ Block.freeVars [s]) :
    z ∈ Block.freeVars (s :: rest) := by
  simp only [Block.freeVars] at h ⊢
  split at h <;> simp_all

omit iDE iHB iHF iSF iHI iLI iWL in
/-- The variables the rest of a list reads, other than the one its head declares, are read by
    the list. -/
theorem fv_tail {s : PStmt P} {rest : PStmts P} {z : P.Ident} (h : z ∈ Block.freeVars rest)
    (hz : z ∉ Stmt.topInits s) : z ∈ Block.freeVars (s :: rest) := by
  unfold Block.freeVars
  split <;> simp_all [Stmt.topInits]

omit iLI iWL in
/-- A name of the merges of the variables both arms of a laid-out `ite` assign or read, when the
    then arm does not always exit, is assigned by the then arm. -/
private theorem mem_ite_interSet {T E : WRes P}
    (h : x ∈ (if T.ax = true then [] else interSet T.A E.R)) :
    T.ax = false ∧ T.A.contains x = true :=
  (List.mem_ite_nil_left.1 h).imp Bool.eq_false_iff.2 mem_interSet_left

include iOp iLF iLFs in
/-- The scope facts of the walk of a laid-out `ite` well scoped from `S`, from those of the walks
    of its arms. -/
private theorem laid_x {c : P.Expr} {tss ess : PStmts P} {md : MetaData P} {Lc S : List P.Ident}
    (hκ : κ ≠ .top) (hwf : WFSt s)
    (hav : ∀ x ∈ S ++ (Block.idents tss ++ Block.idents ess), ∀ b j,
      x = freshName b j → s.avoid.contains x = true) (hc : ∀ y ∈ exprFV c, y ∈ S)
    (hST : Block.WellScoped Lc S tss) (hSE : Block.WellScoped Lc S ess)
    (hL : ∀ (l : String) (t : Nat), s.labelDepth[l]? = some t → t ≤ d)
    (hT : ∀ κ', κ' ≠ .top → ∀ s0 R s1, (wpList κ' d true tss).run s0 = .ok (R, s1) → WFSt s0 →
      (∀ (l : String) (t : Nat), s0.labelDepth[l]? = some t → t ≤ d) → s0.avoid = s.avoid →
      ArmX κ' S (Block.freeVars tss) s0 s1 R)
    (hE : ∀ κ', κ' ≠ .top → ∀ s0 R s1, (wpList κ' d true ess).run s0 = .ok (R, s1) → WFSt s0 →
      (∀ (l : String) (t : Nat), s0.labelDepth[l]? = some t → t ≤ d) → s0.avoid = s.avoid →
      ArmX κ' S (Block.freeVars ess) s0 s1 R) (h : (wpIteLaid κ d c tss ess).run s = .ok (r, s')) :
    ArmX κ S (Block.freeVars [.ite (.det c) tss ess md]) s s' r := by
  let D := Block.idents tss ++ Block.idents ess
  let V := exprFV c ++ Block.freeVars tss ++ Block.freeVars ess
  rw [show Block.freeVars [(.ite (.det c) tss ess md : PStmt P)] = V
      by simp [V, Block.freeVars, Stmt.freeVars]]
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hcx h5 h6 h7 h8 h9 h10 _ h11 _
    h12 _ hEnd => ?_
  have m1 := wRen_w (D := D) h1
  obtain ⟨m2, hg⟩ := wFreshBool_w (D := D) h2
  obtain ⟨m3, hrT⟩ := wFreshBool_w (D := D) h3
  have wf1 : WFSt s1 := (wRen_walk h1).wf hwf (by simp)
  obtain ⟨⟨-, -, -, -, hrdc⟩, -, hs1, hcur1⟩ := wRen_run h1
  obtain ⟨h4, hκE, hvE, -⟩ := hcx.facts
  obtain ⟨m4, S4, hrE, hwf4⟩ := h4.w (D := D)
  have S14 := (wFreshBool_laidSame h2).trans ((wFreshBool_laidSame h3).trans S4)
  have wf4 := hwf4 ((wFreshBool_walk h3).wf ((wFreshBool_walk h2).wf wf1 (by simp)) (by simp))
  have m04 := (m1.trans (m2.trans m3)).trans m4
  have hl4 : s4.labelDepth = s.labelDepth := by rw [S14.labelDepth, hs1]
  have XE := hE κE hκE s4 E s5 h5 wf4 (hl4 ▸ hL) m04.avoid
  have OE := wpList_walkOK h5
  have wf5 : WFSt s5 := OE.wf wf4 fun x hx b j hj =>
    m04.avoid ▸ hav x (by simp [stmtsInits_mem_idents x hx]) b j hj
  have WE := wpList_writes (D := D) κE d true ess (fun _ h => List.mem_append_right _ h) h5
  have ha5 : s5.avoid = s.avoid := WE.avoid.trans m04.avoid
  have XT := hT (.name rT) nofun s5 T s6 h6 wf5
    (fun l t ht => hL l t (by rwa [OE.labelDepth l, hl4] at ht)) ha5
  have OT := wpList_walkOK h6
  have wf6 : WFSt s6 := OT.wf wf5 fun x hx b j hj =>
    ha5 ▸ hav x (by simp [stmtsInits_mem_idents x hx]) b j hj
  have WT := wpList_writes (D := D) (.name rT) d true tss (fun _ h => List.mem_append_left _ h) h6
  obtain ⟨m7, S7, hk3, hsc3, hr3, hrs3, hcps3, -⟩ := srFacts (D := D) h7
  obtain ⟨m8, S8, hkT, hscT, hrT', hrsT, hcpsT, -⟩ := srFacts (D := D) h8
  obtain ⟨m9, S9, hkE, hscE, hrE', hrsE, hcpsE, -⟩ := srFacts (D := D) h9
  obtain ⟨m10, S10, hgm, -⟩ := h10.w (D := D)
  obtain ⟨m11, S11, hqm, -⟩ := h11.w (D := D)
  obtain ⟨m12, S12, hrEm, -⟩ := h12.w (D := D)
  have S612 := S7.trans (S8.trans (S9.trans (S10.trans (S11.trans S12))))
  have hcur65 : ∀ z ∈ S, ∀ m, curName s5 z = some m → curName s6 z = some m :=
    fun z hz m hm => OT.names z m (wfl_inits_disjoint S tss hST z hz) hm
  have hcur54 : ∀ z ∈ S, ∀ m, curName s4 z = some m → curName s5 z = some m :=
    fun z hz m hm => OE.names z m (wfl_inits_disjoint S ess hSE z hz) hm
  have hTx : ∀ n, ((∃ z ∈ S, z ∈ Block.freeVars tss ∧ curName s6 z = some n ∧
      s6.live.contains n = true) ∨ InitIn T.out.toList n) →
      (∃ z ∈ S, z ∈ V ∧ curName s12 z = some n ∧ s12.live.contains n = true) ∨
        InitIn T.out.toList n := fun n h => h.imp_left fun ⟨z, hz, hv, hcz, hl⟩ =>
    ⟨z, hz, by simp [V, hv], (curName_eq_of_nm_taken S612.nm S612.taken z).trans hcz,
      S612.live ▸ hl⟩
  have hEx : ∀ n, ((∃ z ∈ S, z ∈ Block.freeVars ess ∧ curName s5 z = some n ∧
      s5.live.contains n = true) ∨ InitIn E.out.toList n) →
      (∃ z ∈ S, z ∈ V ∧ curName s12 z = some n ∧
        s12.live.contains n = true) ∨ InitIn E.out.toList n := fun n h =>
    h.imp_left fun ⟨z, hz, hv, hcz, hl⟩ => ⟨z, hz, by simp [V, hv],
      (curName_eq_of_nm_taken S612.nm S612.taken z).symm ▸ hcur65 z hz n hcz,
      S612.live ▸ XT.live.keepC hl fun h' => h' ⟨z, hz, hcz⟩⟩
  have hTA := fun n hn => hTx n (XT.asg n hn)
  have hEA := fun n hn => hEx n (XE.asg n hn)
  have hctgt : ∀ k q, q ∈ (carryIns (elseGuard κ gm qm rEm) (carryOf s6 cpsE E.tgt.max?)
      (carryIns (optVar gm) (carryOf s6 cpsT T.tgt.max?) s12.carries T.tgt.max?)
        E.tgt.max?).getD k [] → q ∉ s.carries.getD k [] → q.2.2 ∈ ((T.regs.app E.regs).app
          (Rope.ofList ((carryOf s6 cpsT T.tgt.max?).map (·.2) ++
            (carryOf s6 cpsE E.tgt.max?).map (·.2)))).toList →
      (∃ z ∈ S, z ∈ V ∧ curName s12 z = some q.1 ∧ s12.live.contains q.1 = true) ∨
        InitIn T.out.toList q.1 ∨ InitIn E.out.toList q.1 := by
    intro k q hq hqs hx
    have hx' := mem_laidRegs (fun p hp => (hcpsT p (carryOf_sub hp)).2.widen m7.avoid m7.next
      m9.next) (fun p hp => (hcpsE p (carryOf_sub hp)).2.widen (m7.trans m8).avoid
        (m7.trans m8).next (Nat.le_refl _)) hx
    rcases mem_carryIns hq with hq | ⟨p, hp, rfl⟩
    · rcases mem_carryIns hq with hq | ⟨p, hp, rfl⟩
      · rw [S612.carries] at hq
        by_cases hq5 : q ∈ s5.carries.getD k []
        · have hq4 : q ∉ s4.carries.getD k [] := by rw [S14.carries, hs1]; exact hqs
          have hnew : NewIn s4 s5 q.2.2 := ((WE.carries k q hq5).resolve_left hq4).2.1
          have hxE : q.2.2 ∈ E.regs.toList := hx'.elim (fun h => (hnew.disj (WT.regs _ h)
            (Nat.le_refl _)).elim) (·.elim id fun h => (hnew.disj h WT.next).elim)
          exact (hEx _ (XE.ctgt k q hq5 hq4 hxE)).imp id .inr
        · have hnew : NewIn s5 s6 q.2.2 := ((WT.carries k q hq).resolve_left hq5).2.1
          have hxT : q.2.2 ∈ T.regs.toList := hx'.elim id (·.elim (fun h => ((WE.regs _ h).disj
            hnew (Nat.le_refl _)).elim) fun h => (hnew.disj h (Nat.le_refl _)).elim)
          exact (hTx _ (XT.ctgt k q hq hq5 hxT)).imp id .inl
      · exact (hTA _ (fold_filter_mem (hcpsT p (carryOf_sub hp)).1)).imp id .inl
    · exact (hEA _ (fold_filter_mem (hcpsE p (carryOf_sub hp)).1)).imp id .inr
  have hcur41 : ∀ z m, curName s z = some m → curName s4 z = some m := fun z m hz =>
    (curName_eq_of_nm_taken S14.nm S14.taken z).symm ▸ hcur1 z m hz
  have hL06 : LiveStep (fun m => ¬ ∃ z ∈ S, curName s z = some m) s s6 := by
    have L4 : LiveStep (fun _ => False) s s4 := LiveStep.of_eq
      (by rw [S14.live, hs1]) (by rw [S14.clock, hs1])
    exact ((L4.trans XE.live).trans XT.live).mono fun m hm ⟨z, hz, hcz⟩ => hm.elim
      (·.elim id (· ⟨z, hz, hcur41 z m hcz⟩)) (· ⟨z, hz, hcur54 z hz m (hcur41 z m hcz)⟩)
  rcases hEnd with ⟨hb, rfl, rfl⟩ | ⟨-, hFr, rfl⟩
  · simp only [Rope.isNil_foldl_app', Bool.and_eq_true, List.all_eq_true] at hb
    have hTn := Rope.isNil_toList (hb.2 T.out (by out_mem))
    have hEn := Rope.isNil_toList (hb.2 E.out (by out_mem))
    refine ⟨⟨?_, ?_, ?_, fun k q hq hn hx => (hctgt k q hq hn hx).imp_right fun h =>
        absurd h (by simp [InitIn, hTn, hEn]), ?live, ?_⟩, ?_⟩
    case live => exact LiveStep.mono (hL06.trans (LiveStep.of_eq (E := fun _ => False) S612.live
      S612.clock)) fun m hm => hm.resolve_right id
    all_goals simp [Rope.toList_nil]
  obtain ⟨LF, hinF⟩ := liveAdd_ls (E := fun _ => False) hFr
  obtain ⟨nmF, -⟩ := liveAdd_nm hFr
  obtain ⟨tF, cF⟩ := liveAdd_tc hFr
  have hcurF : ∀ z, curName s' z = curName s12 z := curName_eq_of_nm_taken nmF tF
  have hcF : ∀ z m, curName s6 z = some m → curName s' z = some m := fun z m hm =>
    (hcurF z).trans ((curName_eq_of_nm_taken S612.nm S612.taken z).trans hm)
  have m612' : WMono D s8 s12 := m9.trans (m10.trans (m11.trans m12))
  have m612 : WMono D s6 s12 := m7.trans (m8.trans m612')
  refine ⟨ArmScope.of_cls (fun n => NewIn s1 s4 n ∨ NewIn s6 s12 n ∨
      (∃ ty v, WItem.init n ty v ∈ T.out.toList) ∨
      ∃ ty v, WItem.init n ty v ∈ E.out.toList) (fun n ty v hit => ?_)
    (fun n hn y => ?_) (fun n hn t ht htc => ?_) fun hd ho =>
    ⟨hd, fun n hn => ?_, fun n hn => ?_, fun k q hq hn hx => ?_, ?_, ho⟩, fun it hit y hy => ?_⟩
  · have hW : ∀ a b x, WMono D s6 a → WMono D b s12 → NewIn a b x → NewIn s6 s12 x :=
      fun _ _ _ ha hb hx => hx.widen ha.avoid ha.next hb.next
    have m69 := m7.trans (m8.trans m9)
    simp only [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
      List.mem_append, List.mem_singleton] at hit
    rcases hit with hit | hit | hit | hit | hit | hit | hit | hit | hit | hit | hit |
      hit | hit | hit | hit | hit | hit | hit | hit
    all_goals try with_reducible (first
      | obtain ⟨_, _, ⟨⟩⟩ := hr3 _ hit
      | obtain ⟨_, _, ⟨⟩⟩ := hrT' _ hit
      | obtain ⟨_, _, ⟨⟩⟩ := hrE' _ hit
      | ((try replace hit := mem_ite_nil hit) <;> (try split at hit) <;>
          (try replace hit := mem_ite_nil hit) <;>
          simp only [Rope.toList_one, Rope.toList_nil, List.mem_singleton,
            List.not_mem_nil] at hit <;> cases hit))
    · cases hit
      exact .inl (hg.widen rfl (Nat.le_refl _) (Nat.le_trans m3.next m4.next))
    · exact .inl (hrT.widen m2.avoid m2.next m4.next)
    · exact .inr (.inl (hW _ _ _ m69 (m11.trans m12) (hgm _ rfl)))
    · exact .inr (.inl (hW _ _ _ (m69.trans m10) m12 (hqm _ rfl)))
    · exact .inr (.inl (hW _ _ _ (.refl D s6) (m8.trans m612')
        (hsc3 _ (List.mem_append_left _ hit) n rfl)))
    · exact .inr (.inl (hW _ _ _ m7 m612' (hscT _ (List.mem_append_left _ hit) n rfl)))
    · exact .inr (.inr (.inl ⟨ty, v, hit⟩))
    · exact .inr (.inl (hW _ _ _ (.refl D s6) (m8.trans m612')
        (hsc3 _ (List.mem_append_right _ hit) n rfl)))
    · exact .inr (.inl (hW _ _ _ m7 m612' (hscT _ (List.mem_append_right _ hit) n rfl)))
    · exact .inl ((hrE _ rfl).widen (m2.trans m3).avoid (m2.trans m3).next (Nat.le_refl _))
    · exact .inr (.inl (hW _ _ _ ((m69.trans m10).trans m11) (.refl D s12) (hrEm _ rfl)))
    · exact .inr (.inl (hW _ _ _ (m7.trans m8) (m10.trans (m11.trans m12))
        (hscE _ (List.mem_append_left _ hit) n rfl)))
    · exact .inr (.inr (.inr ⟨ty, v, hit⟩))
    · exact .inr (.inl (hW _ _ _ (m7.trans m8) (m10.trans (m11.trans m12))
        (hscE _ (List.mem_append_right _ hit) n rfl)))
    · obtain ⟨q, -, ⟨⟩⟩ := (mem_sets _ _ hit).resolve_left (by simp [Rope.toList_nil])
    · obtain ⟨_, _, ⟨⟩⟩ := setReach_set _ _ _ (mem_ite_nil' hit)
  · rw [nmF.trans S612.nm]
    rcases hn with hd | ⟨_, k, rfl, -, hk, -⟩ | ⟨ty, v, hit⟩ | ⟨ty, v, hit⟩
    · intro hc
      rcases WT.nm y n hc with hc | hc
      · rcases WE.nm y n hc with hc | hc
        · obtain ⟨_, k, rfl, -, hk, -⟩ := hd
          exact wf1.nm_ne_new (S14.nm ▸ hc) rfl hk
        · exact hd.disj hc (Nat.le_refl _)
      · exact hd.disj hc WE.next
    · exact fun hc => wf6.nm_ne_new hc rfl hk
    · exact XT.declNm n ty v hit y
    · intro hc
      rcases WT.nm y n hc with hc | hc
      · exact XE.declNm n ty v hit y hc
      rcases (wpList_arm hκE d ess h5).decl n ty v hit with hd | ⟨hi, -⟩ | ⟨x, -, hx⟩
      · exact hd.disj hc (Nat.le_refl _)
      · obtain ⟨b, j, rfl, hna, -, -⟩ := hc
        simp [ha5, hav _ (by simp [stmtsInits_mem_idents _ hi]) b j rfl] at hna
      · obtain ⟨_, k, rfl, -, hk, -⟩ := hc
        exact wf4.nm_ne_new hx rfl (Nat.le_trans WE.next hk)
  · have n12F : s12.next ≤ s'.next := (liveAdd_w (D := []) hFr).next
    have m06 := m04.trans (WE.toWMono.trans WT.toWMono)
    have hk4 : s4.clock = s.clock := by rw [S14.clock, hs1]
    have c45 := XE.live.clock
    have h6 : s6.live[n]? = some t := (S612.live ▸ LF.stamp n t ht).resolve_right
      (Nat.not_le.2 (S612.clock ▸ Nat.lt_of_lt_of_le htc hL06.clock))
    rcases hn with hd | hd | ⟨ty, v, hit⟩ | ⟨ty, v, hit⟩
    · exact hd.widen m1.avoid m1.next
        (Nat.le_trans ((WE.toWMono.trans WT.toWMono).trans m612).next n12F)
    · exact hd.widen m06.avoid m06.next n12F
    · exact (XT.old n ty v hit t h6 (Nat.lt_of_lt_of_le htc (hk4 ▸ c45))).widen ha5
        (m04.trans WE.toWMono).next (Nat.le_trans m612.next n12F)
    · rcases XT.live.stamp n t h6 with h5 | h5
      · exact (XE.old n ty v hit t h5 (hk4 ▸ htc)).widen m04.avoid m04.next
          (Nat.le_trans (WT.toWMono.trans m612).next n12F)
      · exact absurd (Nat.lt_of_lt_of_le htc (hk4 ▸ c45)) (Nat.not_lt.2 h5)
  · rcases unionSet_iff.mp hn with hn | hn <;> split at hn <;>
      try simp only [Std.HashSet.contains_empty, Bool.false_eq_true] at hn
    · lift_x hcurF hFr hTA n hn
    · lift_x hcurF hFr hEA n hn
  · rcases (unionSet_iff.mp hn).imp_left unionSet_iff.mp with (hn | hn) | hn
    · lift_x hcurF hFr hTx n (XT.rd n hn)
    · lift_x hcurF hFr hEx n (XE.rd n hn)
    · have hm' : n ∈ rdc := by simpa [Std.HashSet.contains_ofList] using hn
      obtain ⟨y, hy, hcy⟩ := hrdc n hm'
      exact .inl ⟨y, hc y hy, by simp [V, hy], hcF y n (hcur65 y (hc y hy) n
        (hcur54 y (hc y hy) n ((curName_eq_of_nm_taken S14.nm S14.taken y).symm ▸ hcy))),
        hinF n (List.mem_append_left _ hm')⟩
  · lift_x hcurF hFr hctgt k q (cF ▸ hq :) hn hx
  · exact ((hL06.trans (LiveStep.of_eq (E := fun _ => False) S612.live S612.clock)).trans
      ⟨LF.keep, LF.stamp, LF.clock⟩).mono fun m hm => (hm.resolve_right id).resolve_right id
  · have hTU : ∀ x ∈ (if T.ax = true then [] else interSet T.A E.R), (unionSet
        (if T.ax = true then ∅ else T.A) (if E.ax = true then ∅ else E.A)).contains x = true :=
      fun x hx => unionSet_iff.mpr (.inl (by simp [mem_ite_interSet hx]))
    obtain ⟨ty, v, rfl⟩ | ⟨v, rfl⟩ : (∃ ty v, it = .init y ty v) ∨ ∃ v, it = .set y v := by
      revert hy
      cases it <;> simp [WItem.tgt]
    · exact .inr (.inl ⟨ty, v, hit⟩)
    simp only [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil] at ⊢
    have hXT : ∀ x, T.A.contains x = true → (∃ z ∈ S, curName s' z = some x) ∨
        InitIn T.out.toList x := fun x hx =>
      (XT.asg x hx).imp_left fun ⟨z, hz, _, hc, _⟩ => ⟨z, hz, hcF z x hc⟩
    have hXE : ∀ x, E.A.contains x = true → (∃ z ∈ S, curName s' z = some x) ∨
        InitIn E.out.toList x := fun x hx =>
      (XE.asg x hx).imp_left fun ⟨z, hz, _, hc, _⟩ => ⟨z, hz, hcF z x (hcur65 z hz x hc)⟩
    simp only [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
      List.mem_append, List.mem_singleton] at hit
    rcases hit with hit | hit | hit | hit | hit | hit | hit | hit | hit | hit | hit |
      hit | hit | hit | hit | hit | hit | hit | hit
    all_goals try with_reducible (first
      | obtain ⟨_, _, _, ⟨⟩⟩ := hk3 _ (List.mem_append_left _ hit)
      | obtain ⟨_, _, _, ⟨⟩⟩ := hk3 _ (List.mem_append_right _ hit)
      | obtain ⟨_, _, _, ⟨⟩⟩ := hkT _ (List.mem_append_left _ hit)
      | obtain ⟨_, _, _, ⟨⟩⟩ := hkT _ (List.mem_append_right _ hit)
      | obtain ⟨_, _, _, ⟨⟩⟩ := hkE _ (List.mem_append_left _ hit)
      | obtain ⟨_, _, _, ⟨⟩⟩ := hkE _ (List.mem_append_right _ hit)
      | ((try replace hit := mem_ite_nil hit) <;> (try split at hit) <;>
          (try replace hit := mem_ite_nil hit) <;>
          simp only [Rope.toList_one, Rope.toList_nil, List.mem_singleton,
            List.not_mem_nil, reduceCtorEq] at hit))
    · rcases XT.tgt _ hit y hy with h' | h' | h' | ⟨z, hz, hc⟩
      · exact (hXT y h').elim (fun h => .inr (.inr (.inr h))) fun h => by laidx_init h
      · laidx_init h'
      · simp only [RE.vars, List.mem_singleton] at h'
        subst h'
        have hTn : T.out.isNil = false := Bool.eq_false_iff.2 fun hn => by
          simp [Rope.isNil_toList hn] at hit
        exact .inr (.inl ⟨.known HasBool.boolTy, some (.var g), by out_mem hTn⟩)
      · exact .inr (.inr (.inr ⟨z, hz, hcF z y hc⟩))
    · exact .inl (hTU y (hrs3 _ hit y hy))
    · exact (hXT y (fold_filter_mem (hrsT _ hit y hy))).elim
        (fun h => .inr (.inr (.inr h))) fun h => by laidx_init h
    · rcases XE.tgt _ hit y hy with h' | h' | h' | ⟨z, hz, hc⟩
      · exact (hXE y h').elim (fun h => .inr (.inr (.inr h))) fun h => by laidx_init h
      · laidx_init h'
      · rcases hvE y h' with rfl | h'' | rfl
        · exact .inr (.inl ⟨.known HasBool.boolTy, some (kAnd κ wc), by out_mem⟩)
        · exact .inr (.inr (.inl h''))
        · have hEn : E.out.isNil = false := Bool.eq_false_iff.2 fun hn => by
            simp [Rope.isNil_toList hn] at hit
          exact .inr (.inl ⟨.known HasBool.boolTy, some (kAnd κ (WExpr.var g).not), by out_mem hEn⟩)
      · exact .inr (.inr (.inr ⟨z, hz, hcF z y (hcur65 z hz y hc)⟩))
    · exact (hXE y (fold_filter_mem (hrsE _ hit y hy))).elim
        (fun h => .inr (.inr (.inr h))) fun h => by laidx_init h
    · obtain ⟨p, hp, ⟨⟩⟩ := (mem_sets _ _ hit).resolve_left (by simp [Rope.toList_nil])
      exact .inl (hTU _ (hcps3 p (List.mem_filter.mp hp).1).1)
    · exact .inr (.inr (.inl (wvar_mem (setReach_tgt _ _ _ (mem_ite_nil' hit) y hy))))

include iOp in
mutual
/-- The walk of a statement well scoped from `S` (from a well-formed state whose label depths
    are at most `d`, avoiding the names of the form of a fresh name of `S` and of the statement)
    under a variable context with an obligation following it has the scope facts. -/
theorem wpStmt_scope [LawfulHasFvar P] [LawfulHasFvars P] {κ : RE P} (hκ : κ ≠ .top) (d : Nat)
    {Lc : List P.Ident} :
    ∀ (s : PStmt P) {st st' : WSt P} {r : WRes P} {S : List P.Ident},
      (wpStmt κ d true s).run st = .ok (r, st') → WFSt st →
      (∀ x ∈ S ++ Stmt.idents s, ∀ b j, x = freshName b j → st.avoid.contains x = true) →
      Stmt.WellScoped Lc S s → (∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d) →
      ArmX κ S (Block.freeVars [s]) st st' r
  | .cmd (.cmd (.init x ty (.det e) md)), _, _, _, S, h, hwf, hav, hS, _ =>
    .of_cmd hκ (by simp) h <| init_det_x hκ h hwf
        (hav x (by simp [Stmt.idents, getFvars_mem_exprFV])) (fun z hz => hav z (by simp [hz])) hS
  | .cmd (.cmd (.init x ty .nondet md)), _, _, _, S, h, hwf, hav, hS, _ =>
    .of_cmd hκ (by simp) h <| init_nondet_x h hwf (hav x (by simp [Stmt.idents]))
      (fun z hz => hav z (by simp [hz])) hS.1
  | .cmd (.cmd (.set x (.det e) md)), _, _, _, _, h, _, _, hS, _ =>
    .of_cmd hκ (by simp) h (set_det_x hκ h hS)
  | .cmd (.cmd (.set x .nondet md)), _, _, _, _, h, hwf, hav, hS, _ =>
    .of_cmd hκ (by simp) h (set_nondet_x hκ h hwf (hav x (by simp [Stmt.idents])) hS)
  | .cmd (.cmd (.assume ..)), _, _, _, _, h, _, _, hS, _
  | .cmd (.cmd (.assert ..)), _, _, _, _, h, _, _, hS, _
  | .cmd (.cmd (.cover ..)), _, _, _, _, h, _, _, hS, _
  | .cmd (.call ..), _, _, _, _, h, _, _, hS, _ | .typeDecl .., _, _, _, _, h, _, _, hS, _ => by
    refine .of_cmd hκ (by simp) h ?_
    simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    first
      | exact ren_live_x (fun y hy => ⟨hS y hy, by simp [Block.freeVars, Stmt.freeVars, hy]⟩)
          (fun _ => ⟨by simp [Rope.toList_one], rfl, rfl⟩) h
      | (obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
         exact ⟨fun _ _ _ h => by simp [Rope.toList_nil] at h, fun _ h => by simp at h,
           fun _ h => by simp at h, fun _ _ h hn => absurd h hn, LiveStep.of_eq rfl rfl,
           fun _ _ _ h => by simp [Rope.toList_nil] at h⟩)
      | cases h
  | .loop .., _, _, _, _, h, _, _, _, _ | .ite .nondet .., _, _, _, _, h, _, _, _, _ => by
    simp only [wpStmt] at h
    cases h
  | .exit l md, _, _, _, _, h, hwf, _, _, _ => .of_cmd hκ (by simp) h (exit_x hκ hwf h)
  | .block l body md, st, _, _, S, h, hwf, hav, hS, hL => by
    rw [show Block.freeVars [(.block l body md : PStmt P)] = Block.freeVars body
        by simp [Block.freeVars, Stmt.freeVars]]
    exact block_x hκ hwf hL (fun s0 B s1 hB hwf0 hL0 ha0 => wpList_scope hκ (d + 1) body hB hwf0
      (fun x hx b j hj => ha0 ▸ hav x (by simpa [Stmt.idents,
          ExprOrNondet.getVars_det, ExprOrNondet.getVars_nondet,
          getFvars_mem_exprFV] using hx) b j hj) hS hL0) h
  | .ite (.det c) tss ess md, s, s', r, S, h, hwf, hav0, hS, hL => by
    simp only [wpStmt, ↓reduceIte] at h
    obtain ⟨hc, hST, hSE⟩ := hS
    have hav : ∀ x ∈ S ++ (Block.idents tss ++ Block.idents ess), ∀ b j, x = freshName b j →
        s.avoid.contains x = true := fun x hx => hav0 x (by grind [Stmt.idents])
    exact laid_x hκ hwf hav hc hST hSE hL
      (fun _ hκ' _ _ _ hT hwf0 hL0 ha0 => wpList_scope hκ' d tss hT hwf0
        (fun x hx b j hj => ha0 ▸ hav x (by grind) b j hj) hST hL0)
      (fun _ hκ' _ _ _ hE hwf0 hL0 ha0 => wpList_scope hκ' d ess hE hwf0
        (fun x hx b j hj => ha0 ▸ hav x (by grind) b j hj) hSE hL0) h
  termination_by structural s => s

/-- The walk of a list well scoped from `S` (from a well-formed state whose label depths are at
    most `d`, avoiding the names of the form of a fresh name of `S` and of the list) under a
    variable context with an obligation following it has the scope facts. -/
theorem wpList_scope [LawfulHasFvar P] [LawfulHasFvars P] {κ : RE P} (hκ : κ ≠ .top) (d : Nat)
    {Lc : List P.Ident} :
    ∀ (ss : PStmts P) {st st' : WSt P} {r : WRes P} {S : List P.Ident},
      (wpList κ d true ss).run st = .ok (r, st') → WFSt st →
      (∀ x ∈ S ++ Block.idents ss, ∀ b j, x = freshName b j → st.avoid.contains x = true) →
      Block.WellScoped Lc S ss → (∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d) →
      ArmX κ S (Block.freeVars ss) st st' r
  | [], st, _, _, _, h, _, _, _, _ => by
    simp only [wpList, StateT.run_pure] at h
    cases h
    refine ⟨⟨?_, ?_, ?_, fun k q hq hn => absurd hq hn, LiveStep.of_eq rfl rfl, ?_⟩, ?_⟩ <;>
      simp [Rope.toList_nil]
  | s :: rest, st, st', R, S, h, hwf, hav, hS, hL => by
    obtain ⟨r, st1, a, st2, h1, h2, hc⟩ := wpList_cons_arm hκ h
    simp only [Block.WellScoped] at hS
    have Xr := wpList_scope hκ d rest h1 hwf (fun x hx => hav x (by
      simp only [List.mem_append, Block.idents] at hx ⊢
      grind [mem_idents_of_topInit])) hS.2 hL
    have Or := wpList_walkOK h1
    have hwf1 : WFSt st1 := Or.wf hwf fun x hx b j hj =>
      hav x (by simp [Block.idents, stmtsInits_mem_idents x hx]) b j hj
    have Xa := wpStmt_scope hκ d s h2 hwf1 (fun x hx b j hj => Or.avoid ▸ hav x (by
      simp only [List.mem_append, Block.idents] at hx ⊢
      exact hx.imp_right .inl) b j hj) hS.1 (fun l t ht => hL l t (by rwa [Or.labelDepth l] at ht))
    have Wr := wpList_writes (D := Block.idents (s :: rest)) κ d true rest
      (fun x hx => by simp [Block.idents, hx]) h1
    have Wa := wpStmt_writes (D := Block.idents (s :: rest)) κ d true s
      (fun x hx => by simp [Block.idents, hx]) h2
    have Oa := wpStmt_walkOK h2
    have Ar := wpList_arm hκ d rest h1
    obtain ⟨hR, hnm, ht, hcr, hl, hk, hnx⟩ : (R = a ∨ R = a.combine r) ∧ st'.nm = st2.nm ∧
        st'.taken = st2.taken ∧ st'.carries = st2.carries ∧ st'.live = st2.live ∧
        st'.clock = st2.clock ∧ st2.next ≤ st'.next := by
      rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> simp
    have hcur : ∀ z, curName st' z = curName st2 z := curName_eq_of_nm_taken hnm ht
    have hS1 : ∀ z ∈ S, ∀ m, curName st1 z = some m → curName st2 z = some m := fun z hz m =>
      Oa.names z m (wfl_inits_disjoint S [s] ⟨hS.1, trivial⟩ z hz)
    have hS0 : ∀ z ∈ Stmt.topInits s ++ S, ∀ m, curName st z = some m → curName st1 z = some m :=
      fun z hz m => Or.names z m (wfl_inits_disjoint _ rest hS.2 z hz)
    have hliftA : ∀ n, ((∃ z ∈ S, z ∈ Block.freeVars [s] ∧ curName st2 z = some n ∧
        st2.live.contains n = true) ∨ InitIn a.out.toList n) →
        (∃ z ∈ S, z ∈ Block.freeVars (s :: rest) ∧
            curName st' z = some n ∧ st'.live.contains n = true) ∨
          InitIn a.out.toList n := fun n h => h.imp_left fun ⟨z, hz, hv, hc, hlv⟩ =>
      ⟨z, hz, fv_head hv, (hcur z).trans hc, hl ▸ hlv⟩
    have Xa' : ArmX κ S (Block.freeVars (s :: rest)) st st' a := by
      refine ⟨⟨fun n ty v hi x => hnm ▸ Xa.declNm n ty v hi x, fun n hn => hliftA n (Xa.asg n hn),
        fun n hn => hliftA n (Xa.rd n hn), fun k q hq hn hx => hliftA _ (Xa.ctgt k q (hcr ▸ hq)
          (fun h1 => ((Wr.carries k q h1).resolve_left hn).2.1.disj (Wa.regs _ hx) (Nat.le_refl _))
          hx), ?_, fun n ty v hi t ht htc => ?_⟩, fun it hit y hy => ?_⟩
      · refine ((Xr.live.trans Xa.live).trans (LiveStep.of_eq (E := fun _ => False) hl hk)).mono
          fun m hm ⟨z, hz, hcz⟩ => ?_
        exact hm.elim (·.elim (fun h => h ⟨z, List.mem_append_right _ hz, hcz⟩)
          fun h => h ⟨z, hz, hS0 z (List.mem_append_right _ hz) m hcz⟩) id
      · exact (Xa.old n ty v hi t (hl ▸ ht) (Nat.lt_of_lt_of_le htc Or.clock)).widen Or.avoid
          Or.next hnx
      · exact (Xa.tgt it hit y hy).imp_right (.imp_right (.imp_right fun ⟨z, hz, hcz⟩ =>
          ⟨z, hz, (hcur z).trans hcz⟩))
    rcases hR with rfl | rfl
    · exact Xa'
    have hz : ∀ z ∈ Stmt.topInits s ++ S, ∀ y, curName st1 z = some y →
        InitIn a.out.toList y ∨ z ∈ S ∧ z ∉ Stmt.topInits s ∧ curName st' z = some y :=
      fun z hz y hy => if hzt : z ∈ Stmt.topInits s then .inl (init_decl_cur hκ h2 hzt hy) else
        have hzS := (List.mem_append.1 hz).resolve_left hzt
        .inr ⟨hzS, hzt, (hcur z).trans (hS1 z hzS _ hy)⟩
    have ho : (a.combine r).out.toList = a.out.toList ++ r.out.toList := Rope.toList_app _ _
    have hIa : ∀ n, InitIn a.out.toList n → InitIn (a.combine r).out.toList n :=
      fun n ⟨ty, v, hi⟩ => ⟨ty, v, ho ▸ List.mem_append_left _ hi⟩
    have hIr : ∀ n, InitIn r.out.toList n → InitIn (a.combine r).out.toList n :=
      fun n ⟨ty, v, hi⟩ => ⟨ty, v, ho ▸ List.mem_append_right _ hi⟩
    have hliftR : ∀ n, ((∃ z ∈ Stmt.topInits s ++ S, z ∈ Block.freeVars rest ∧
        curName st1 z = some n ∧ st1.live.contains n = true) ∨ InitIn r.out.toList n) →
        (∃ z ∈ S, z ∈ Block.freeVars (s :: rest) ∧
            curName st' z = some n ∧ st'.live.contains n = true) ∨
          InitIn (a.combine r).out.toList n := by
      rintro n (⟨z, hzs, hv, hcz, hlv⟩ | hi)
      · rcases hz z hzs _ hcz with hi | ⟨hzS, hzt, hc'⟩
        · exact .inr (hIa n hi)
        · exact .inl ⟨z, hzS, fv_tail hv hzt, hc', hl ▸ Xa.live.keepC hlv fun h => h ⟨z, hzS, hcz⟩⟩
      · exact .inr (hIr n hi)
    refine ⟨⟨fun n ty v hi x hx => ?_, fun n hn => ?_, fun n hn => ?_, fun k q hq hn hx => ?_,
      Xa'.live, fun n ty v hi t ht htc => ?_⟩, fun it hit y hy => ?_⟩
    · rcases List.mem_append.1 (ho ▸ hi) with hi | hi
      · exact Xa'.declNm n ty v hi x hx
      rcases Oa.nm x n (hnm ▸ hx) with h1 | ⟨b, j, he, hna, hj⟩
      · exact Xr.declNm n ty v hi x h1
      rcases Ar.decl n ty v hi with ⟨b', j', rfl, -, -, hj'⟩ | ⟨hI, -⟩ | ⟨y, -, hy⟩
      · exact absurd (freshName_counter_inj he) (by omega)
      · simp [Or.avoid, hav n (by simp [Block.idents, stmtsInits_mem_idents n hI]) b j he] at hna
      · exact hwf.nm_ne_new hy he (Nat.le_trans Or.next hj)
    · exact (unionSet_iff.1 hn).elim (fun h => (Xa'.asg n h).imp_right (hIa n))
        fun h => hliftR n (Xr.asg n h)
    · exact (unionSet_iff.1 hn).elim (fun h => (Xa'.rd n h).imp_right (hIa n))
        fun h => hliftR n (Xr.rd n h)
    · rcases List.mem_append.1 ((Rope.toList_app _ _).symm ▸ hx :) with hx | hx
      · exact (Xa'.ctgt k q hq hn hx).imp_right (hIa _)
      · exact hliftR _ (Xr.ctgt k q ((Wa.carries k q (hcr ▸ hq)).resolve_right fun h1 =>
          (Wr.regs _ hx).disj h1.2.1 (Nat.le_refl _)) hn hx)
    · rcases List.mem_append.1 (ho ▸ hi) with hi | hi
      · exact Xa'.old n ty v hi t ht htc
      · exact (Xr.old n ty v hi t (Oa.liveOld n t (hl ▸ ht) (Nat.lt_of_lt_of_le htc Or.clock))
          htc).widen rfl (Nat.le_refl _) (Nat.le_trans Oa.next hnx)
    · rcases List.mem_append.1 (ho ▸ hit) with hit | hit
      · exact (Xa'.tgt it hit y hy).imp (fun h => unionSet_iff.2 (.inl h)) (.imp_left (hIa y))
      rcases Xr.tgt it hit y hy with h | ⟨ty, v, hi⟩ | h | ⟨z, hzs, hcz⟩
      · exact .inl (unionSet_iff.2 (.inr h))
      · exact .inr (.inl (hIr y ⟨ty, v, hi⟩))
      · exact .inr (.inr (.inl h))
      · exact (hz z hzs _ hcz).elim (fun h => .inr (.inl (hIa y h)))
          fun ⟨hzS, _, hc'⟩ => .inr (.inr (.inr ⟨z, hzS, hc'⟩))
  termination_by structural ss => ss
end

section

variable {κ : RE P} {d : Nat} {ss : PStmts P} {st st' : WSt P} {r : WRes P} {Lc S : List P.Ident}
  (h : (wpList κ d true ss).run st = .ok (r, st')) (hκ : κ ≠ .top) (hwf : WFSt st)
  (hS : Block.WellScoped Lc S ss)
  (hav : ∀ x ∈ S ++ Block.idents ss, ∀ b j, x = freshName b j → st.avoid.contains x = true)
  (hL : ∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d)
include iLI iWL iOp iLF iLFs h hκ hwf hS hav hL

/-- The names the output of an arm walk declares are no renamings after it. -/
theorem arm_declNotNm :
    ∀ n ∈ wDecls r.out.toList, ∀ x : P.Ident, st'.nm[x]? ≠ some n := fun n hn => by
  obtain ⟨ty, v, hi⟩ := initIn_of_wDecls (wpList_arm hκ d ss h).nobr hn
  exact (wpList_scope hκ d ss h hwf hav hS hL).declNm n ty v hi

/-- The names the output of an arm walk declares are no current names, after it, of variables
    in scope. -/
theorem arm_declNotCur : ∀ n ∈ wDecls r.out.toList, ∀ z ∈ S, curName st' z ≠ some n := by
  intro n hn z hz hc
  obtain ⟨ty, v, hi⟩ := initIn_of_wDecls (wpList_arm hκ d ss h).nobr hn
  have hnm := (wpList_scope hκ d ss h hwf hav hS hL).declNm n ty v hi z
  obtain rfl : z = n := by grind [curName]
  have ha := hav z (List.mem_append_left _ hz)
  rcases (wpList_arm hκ d ss h).decl z ty v hi with ⟨b, j, hb, hz', -⟩ | ⟨hzI, -⟩ | ⟨x, -, hx⟩
  · simp [ha b j hb] at hz'
  · exact wfl_inits_disjoint S ss hS z hz hzI
  · obtain ⟨-, b, j, hb, -, hz'⟩ := hwf.nm_fresh x z hx
    simp [ha b j hb] at hz'

/-- A name the output of an arm walk declares, live after it with a stamp below the clock
    before it, is live with that stamp before it and of fresh-name form not avoided before it,
    with a counter from the counter before it on. -/
theorem arm_declNotLive : ∀ n ∈ wDecls r.out.toList, ∀ t, st'.live[n]? = some t → t < st.clock →
      st.live[n]? = some t ∧ FreshAt st n := by
  intro n hn t ht hlt
  obtain ⟨ty, v, hi⟩ := initIn_of_wDecls (wpList_arm hκ d ss h).nobr hn
  have X := wpList_scope hκ d ss h hwf hav hS hL
  obtain ⟨b, j, rfl, ha, hj, -⟩ := X.old n ty v hi t ht hlt
  exact ⟨(X.live.stamp _ t ht).resolve_right (Nat.not_le.2 hlt), b, j, rfl, ha, hj⟩

/-- An assigned name of an arm walk is the current name after it of a variable in scope that the
    arm reads, or a name its output declares. -/
theorem arm_assigned : ∀ n, r.A.contains n = true →
      (∃ z ∈ S, z ∈ Block.freeVars ss ∧ curName st' z = some n) ∨ n ∈ wDecls r.out.toList :=
  fun n hn => ((wpList_scope hκ d ss h hwf hav hS hL).asg n hn).imp
    (fun ⟨z, hz, hv, hc, _⟩ => ⟨z, hz, hv, hc⟩) wDecls_of_initIn

/-- A read name of an arm walk is the current name after it of a variable in scope that the arm
    reads, or a name its output declares. -/
theorem arm_read : ∀ n, r.R.contains n = true →
      (∃ z ∈ S, z ∈ Block.freeVars ss ∧ curName st' z = some n) ∨ n ∈ wDecls r.out.toList :=
  fun n hn => ((wpList_scope hκ d ss h hwf hav hS hL).rd n hn).imp
    (fun ⟨z, hz, hv, hc, _⟩ => ⟨z, hz, hv, hc⟩) wDecls_of_initIn

/-- An arm walk keeps the stamps of the live current names before it of variables in scope. -/
theorem arm_liveKeep : ∀ z ∈ S, ∀ n, curName st z = some n → ∀ s : Nat, st.live[n]? = some s →
      st'.live[n]? = some s :=
  fun z hz n hn s hs => (wpList_scope hκ d ss h hwf hav hS hL).live.keep n s hs fun hne =>
    hne ⟨z, hz, hn⟩

/-- The targets of the carried merges an arm walk registers are current names after it of
    variables in scope, or names its output declares. -/
theorem arm_carryTgt : ∀ k i n v xB, CarryReg r st' k i n v xB →
      (∃ z ∈ S, curName st' z = some n) ∨ n ∈ wDecls r.out.toList := by
  intro k i n v xB ⟨hi, hx⟩
  have hns : (n, v, xB) ∉ st.carries.getD k [] := fun hq =>
    (List.mem_iff_getElem?.mp hq).elim fun i' hi' => ((wpList_writes (D := Block.idents ss) κ d
      true ss (fun _ h => h) h).regs xB hx).not_below (hwf.carries_fresh k i' n v xB hi')
  exact ((wpList_scope hκ d ss h hwf hav hS hL).ctgt k _ (List.mem_of_getElem? hi) hns hx).imp
    (fun ⟨z, hz, _, hc, _⟩ => ⟨z, hz, hc⟩) wDecls_of_initIn

end

/-- The minimum of two optional depths, one of which is a depth at most `x`, is a depth at most
    `x`. -/
private theorem minOpt_le {a b : Option Nat} {x : Nat}
    (h : (∃ t, a = some t ∧ t ≤ x) ∨ ∃ t, b = some t ∧ t ≤ x) :
    ∃ t, minOpt a b = some t ∧ t ≤ x := by
  cases a <;> cases b <;> simp only [minOpt] <;> grind

/-- A depth at most the depth of a label (0 for a label outside the map) is at most a bound of
    all the depths of the map. -/
private theorem le_of_le_depth {m : Std.HashMap String Nat} {l : String} {t : Nat}
    (h : t ≤ (m[l]?).getD 0) (hL : ∀ (l : String) (t : Nat), m[l]? = some t → t ≤ d) : t ≤ d := by
  cases hm : m[l]? <;> grind

omit iLI in
mutual
/-- An exit of a statement walked under a variable context with an obligation following it (from
    a state with `DeadBelow` whose label depths are at most `d`) gives its result a least exit
    depth at most the depth of the exit's label (0 for a label outside the region). -/
theorem wpStmt_exitMin [LawfulHasIdent P] {κ : RE P} (hκ : κ ≠ .top) (d : Nat) {F : P.Factory} :
    ∀ (s : PStmt P) {st st' : WSt P} {a : WRes P},
      (wpStmt κ d true s).run st = .ok (a, st') → DeadBelow st →
      (∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d) →
      ∀ {X : Outcome P → Prop} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
        DRunS F X s σ evs o → ∀ l σ1, o = .exit l σ1 →
          ∃ t, a.minT = some t ∧ t ≤ (st.labelDepth[l]?).getD 0
  | .exit l' md, st, _, a, h, _, _, X, σ, evs, o, hr, l, σ1, ho => by
    cases hr <;> cases ho
    rcases exit_inv hκ h with
      ⟨t, ht, ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, rfl⟩⟩ | ⟨ht, -, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ <;> simp [ht]
  | .block l' body md, st, _, a, h, hD, hL, X, σ, evs, o, hr, l, σ1, ho => by
    obtain ⟨s0, B, s1, hs0, hB, -, rfl⟩ := block_inv hκ h
    cases hr with
    | block hb =>
      obtain ⟨hne, σ', rfl⟩ := outcome_block_exit ho
      have hL0 : ∀ (l3 : String) (t : Nat), s0.labelDepth[l3]? = some t → t ≤ d + 1 := by
        intro l3 t ht
        rw [hs0, Std.HashMap.getElem?_insert] at ht
        split at ht <;> grind
      obtain ⟨t, ht, htl⟩ := wpList_exitMin hκ (d + 1) body hB
        (DeadBelow.of_le hD (by rw [hs0]) (by rw [hs0]; exact Nat.le_refl _)) hL0 hb l σ' rfl
      have hlab : (s0.labelDepth[l]?).getD 0 = (st.labelDepth[l]?).getD 0 := by
        simp [hs0, Std.HashMap.getElem?_insert, Ne.symm hne]
      exact ⟨t, by simp [ht, leOpt, le_of_le_depth (hlab ▸ htl) hL], hlab ▸ htl⟩
  | .ite (.det c) tss ess md, st, _, a, h, hD, hL, X, σ, evs, o, hr, l, σ1, ho => by
    simp only [wpStmt, ↓reduceIte] at h
    refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT
      cpT rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hc hE hT _ _ _ _ _ _ _ _ _
      hEnd => ?_
    obtain ⟨h4, hκE, -⟩ := hc.facts
    obtain ⟨m4, S4, -, -⟩ := h4.w (D := [])
    have S14 := (wFreshBool_laidSame h2).trans ((wFreshBool_laidSame h3).trans S4)
    obtain ⟨-, hn1, hs1, -⟩ := wRen_run h1
    have hl4 : s4.labelDepth = st.labelDepth := by rw [S14.labelDepth, hs1]
    have hm : a.minT = minOpt T.minT E.minT := by rcases hEnd with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
    have hD4 : DeadBelow s4 := DeadBelow.of_le hD (by rw [S14.dead, hs1])
      (Nat.le_trans hn1 ((wFreshBool_w (D := []) h2).1.trans ((wFreshBool_w h3).1.trans m4)).next)
    have hl5 : ∀ l', s5.labelDepth[l']? = st.labelDepth[l']? := fun l' =>
      hl4 ▸ (wpList_walkOK hE).labelDepth l'
    cases hr with
    | ite_true _ hr _ =>
      obtain ⟨σ', rfl⟩ := outcome_proj_exit ho
      obtain ⟨t, ht, htl⟩ := wpList_exitMin (κ := .name rT) nofun d tss hT
        (wpList_deadBelow hE hD4) (fun l t ht => hL l t (by rwa [hl5] at ht)) hr l σ' rfl
      exact hm ▸ minOpt_le (.inl ⟨t, ht, hl5 l ▸ htl⟩)
    | ite_false _ hr _ =>
      obtain ⟨σ', rfl⟩ := outcome_proj_exit ho
      obtain ⟨t, ht, htl⟩ := wpList_exitMin hκE d ess hE hD4 (hl4 ▸ hL) hr l σ' rfl
      exact hm ▸ minOpt_le (.inr ⟨t, ht, hl4 ▸ htl⟩)
  | .cmd _, _, _, _, _, _, _, _, _, _, _, hr, _, _, ho
  | .typeDecl .., _, _, _, _, _, _, _, _, _, _, hr, _, _, ho => by
    cases hr <;> cases ho
  | .loop .., _, _, _, h, _, _, _, _, _, _, _, _, _, _
  | .ite .nondet .., _, _, _, h, _, _, _, _, _, _, _, _, _, _ => by
    simp only [wpStmt] at h
    cases h
  termination_by structural s => s

/-- An exit of a list walked under a variable context with an obligation following it (from a
    state with `DeadBelow` whose label depths are at most `d`) gives its result a least exit
    depth at most the depth of the exit's label. -/
theorem wpList_exitMin [LawfulHasIdent P] {κ : RE P} (hκ : κ ≠ .top) (d : Nat) {F : P.Factory} :
    ∀ (ss : PStmts P) {st st' : WSt P} {r : WRes P},
      (wpList κ d true ss).run st = .ok (r, st') → DeadBelow st →
      (∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d) →
      ∀ {X : Outcome P → Prop} {σ : SemanticStore P} {evs : List (Event P)} {o : Outcome P},
        DRun F X ss σ evs o → ∀ l σ1, o = .exit l σ1 →
          ∃ t, r.minT = some t ∧ t ≤ (st.labelDepth[l]?).getD 0
  | [], _, _, _, _, _, _, X, σ, evs, o, hr, l, σ1, ho => by
    cases hr <;> cases ho
  | s :: rest, st, _, R, h, hD, hL, X, σ, evs, o, hr, l, σ1, ho => by
    obtain ⟨r, st1, a, st2, h1, h2, hc⟩ := wpList_cons_arm hκ h
    have Or := wpList_walkOK h1
    have hD1 := wpList_deadBelow h1 hD
    have hL1 : ∀ (l : String) (t : Nat), st1.labelDepth[l]? = some t → t ≤ d := fun l t ht =>
      hL l t (by rwa [Or.labelDepth l] at ht)
    rcases hc with ⟨hax, rfl, rfl⟩ | ⟨hax, rfl, rfl⟩ <;> cases hr
    · exact absurd (wpStmt_ax_normal h2 hD1 ‹_›) (by rw [hax]; decide)
    rotate_left
    · exact minOpt_le (.inr (wpList_exitMin hκ d rest h1 hD hL ‹_› l σ1 ho))
    all_goals
      cases ho
      obtain ⟨t, ht, htl⟩ := wpStmt_exitMin hκ d s h2 hD1 hL1 ‹_› l σ1 rfl
      have htl' := Or.labelDepth l ▸ htl
      first | exact ⟨t, ht, htl'⟩ | exact minOpt_le (.inl ⟨t, ht, htl'⟩)
  termination_by structural ss => ss
end

/-- An exit of an arm walk (from a state with `DeadBelow` whose label depths are at most `d`)
    gives its result a least exit depth at most `d`. -/
theorem arm_exitMin {ss : PStmts P} {st st' : WSt P}
    (h : (wpList κ d true ss).run st = .ok (r, st')) (hκ : κ ≠ .top) (hD : DeadBelow st) :
    (∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d) → ∀ X σ evs l σ1,
      DRun F X ss σ evs (.exit l σ1) → leOpt r.minT d = true := by
  intro hL X σ evs l σ1 hr
  obtain ⟨t, ht, htl⟩ := wpList_exitMin hκ d ss h hD hL hr l σ1 rfl
  simp [ht, leOpt, le_of_le_depth htl hL]

end -- public section

end WP
end Imperative
