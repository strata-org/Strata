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
public import Strata.Transform.WP.WPOverEffectsScope
import all Strata.Transform.WP.WPOverEffectsScope

/-! # The names a run of an arm walk's output keeps

A run of the output of an arm walk of a laid-out `ite` from a value-valued store changes only
names the arm assigns or its output declares, variables of the context, and names not live after
the walk whose stamp is below the clock before the walk (`arm_writesLive`): the variables an
always-exiting nested arm assigns that are live after it are saved before it and restored after
it.  A walk at depth `d` from a state without carried merges deeper than `d` ends without them
(`wpList_carriesHigh`).  A run of the output of the else arm of a laid-out `ite` keeps the names
the output of its then arm declares (`arm_crossKeep`): every name an arm output assigns is
assigned by the arm, declared by its output, a variable of its context, or a current name of a
variable in scope.

This module imports the write sets of walks (`WPOverEffectsWalk`), the declarations and writes
of arm walks (`WPOverEffectsArm`) and their scope facts (`WPOverEffectsScope`) publicly.

Key theorems: `arm_writesLive`, `arm_crossKeep`, `wpList_carriesHigh`. -/

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


/-! ## Names kept by the runs of arm outputs -/

/-- Every run of the resolved items of `l` from a value-valued store keeps every name with
    property `g`. -/
private def KeepL (F : P.Factory) (l : List (WItem P)) (g : P.Ident → Prop) : Prop :=
  ∀ (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) (items : List (Item P)),
    resolveItems T Y l = .ok items → ∀ σ tr σ', WellFormedStore σ F → MainRun F items σ tr σ' →
      ∀ n, g n → σ' n = σ n

omit iDE iBE iLB iSF iHI iLI iHa iHFs iWL in
/-- A main-path run of a concatenation is a run of its first part followed by one of its
    second part. -/
private theorem MainRun.split :
    ∀ {a b : List (Item P)} {σ σ' : SemanticStore P} {tr : List (Event P)},
      MainRun F (a ++ b) σ tr σ' →
        ∃ σ1 t1 t2, MainRun F a σ t1 σ1 ∧ MainRun F b σ1 t2 σ'
  | [], _, _, _, _, h => ⟨_, _, _, .nil, h⟩
  | _ :: _, _, _, _, _, .plain hc h =>
    (MainRun.split h).elim fun σ1 ⟨_, _, h1, h2⟩ => ⟨σ1, _, _, .plain hc h1, h2⟩
  | _ :: _, _, _, _, _, .side h =>
    (MainRun.split h).elim fun σ1 ⟨_, _, h1, h2⟩ => ⟨σ1, _, _, .side h1, h2⟩

section
omit iLB iHI iLI

include iLV in
/-- The items of a concatenation keep what both parts keep. -/
private theorem KeepL.app {F : P.Factory} (hF : WellFormedSemanticEvalBase F) {a b : List (WItem P)}
    {g : P.Ident → Prop}
    (ha : KeepL F a g) (hb : KeepL F b g) : KeepL F (a ++ b) g := by
  intro T Y items hi σ tr σ' hC hm n hn
  obtain ⟨ia, ib, ha', hb', rfl⟩ := (resolveItems_append T Y a b).1 hi
  obtain ⟨σ1, t1, t2, h1, h2⟩ := MainRun.split hm
  exact (hb _ _ _ hb' _ _ _ (MainRun.canon hF h1 hC) h2 n hn).trans (ha _ _ _ ha' _ _ _ hC h1 n hn)

/-- Items keep the names with a property none of them assigns. -/
private theorem KeepL.frame {l : List (WItem P)} {g : P.Ident → Prop}
    (h : ∀ it ∈ l, ∀ y, it.tgt = some y → ¬ g y) : KeepL F l g :=
  fun _ _ _ hi _ _ _ _ hm n hn => MainRun.frame hi hm n fun it hit ht => h it hit n ht hn

/-- Items keeping the names with a property keep those with a stronger one. -/
private theorem KeepL.mono {l : List (WItem P)} {g g' : P.Ident → Prop} (h : KeepL F l g)
    (hg : ∀ n, g' n → g n) : KeepL F l g' := by grind [KeepL]

/-- Items that assign only by `init`s, none of `n`, keep `n`. -/
private theorem KeepL.inits {l : List (WItem P)} (hl : ∀ it ∈ l, ∃ m ty v, it = .init m ty v)
    (hn : ∀ ty v, WItem.init n ty v ∉ l) : KeepL F l (· = n) :=
  KeepL.frame fun it hit y hy hyn => by grind [WItem.tgt]

/-- The names that every run of the resolved output of a walk from `st` to `st'` with result
    `r` under the context `κ` keeps: names not assigned by `r`, not declared by its output, no
    variables of `κ`, and live after the walk with a stamp below the clock before it. -/
private def Keeps (F : P.Factory) (κ : RE P) (st st' : WSt P) (r : WRes P) : Prop :=
  KeepL F r.out.toList fun n => r.A.contains n = false ∧ ¬ InitIn r.out.toList n ∧
    n ∉ RE.vars κ ∧ liveBefore st' n st.clock = true

include iLB iHI in
omit iWL in
/-- `liveBefore` holds exactly for a live name with a stamp below the bound. -/
private theorem liveBefore_iff {st : WSt P} {t : Nat} :
    liveBefore st n t = true ↔ ∃ u, st.live[n]? = some u ∧ u < t := by grind [liveBefore]

include iOp iLF in
/-- A run of resolved items starting with an `init` or a `set` of `x` from the variable `y`
    gives `x` the value of `y` and keeps the other names, then runs the rest. -/
private theorem run_var_head (hF : WellFormedSemanticEvalBase F) {it : WItem P} {l : List (WItem P)}
    {items : List (Item P)} {σ σ' : SemanticStore P} {tr : List (Event P)}
    (hit : (∃ ty, it = .init x ty (some (.var y))) ∨ it = .set x (some (.var y)))
    (hi : resolveItems T Y (it :: l) = .ok items) (hm : MainRun F items σ tr σ')
    (hC : WellFormedStore σ F) :
    ∃ i' σ1 t', resolveItems T Y l = .ok i' ∧ MainRun F i' σ1 t' σ' ∧ σ1 x = σ y ∧
      ∀ z, x ≠ z → σ1 z = σ z := by
  obtain ⟨a, r, ha, hr, rfl⟩ := resolveItems_cons_ok hi
  rcases hit with ⟨ty, rfl⟩ | rfl <;>
    simp only [resolveItem, resolveOE, bind, Except.bind, pure, Except.pure] at ha <;>
    (repeat' split at ha) <;> cases ha
  all_goals
    rename_i heq
    split at heq <;> cases heq
    rename_i e he
    obtain ⟨τ, rfl⟩ := resolveE_var he
    have hv : P.eval F σ (HasFvar.mkVar y (some τ)) = σ y :=
      hF.var _ y σ hC (LawfulHasFvar.getFvar_mkTypedFvar y τ)
    cases hm with | plain hc hm => ?_
    refine ⟨_, _, _, hr, hm, ?_⟩
    unfold EvalE at hc
    cases hc <;> grind [cases InitState, cases UpdateState]

omit iBE iHF iSF iHa iHFs iWL in
/-- A store that changes one name to the value of another name of a value-valued store stays
    value-valued. -/
private theorem canon_copy {σ σ1 : SemanticStore P} (hC : WellFormedStore σ F) (h1 : σ1 x = σ y)
    (h2 : ∀ z, x ≠ z → σ1 z = σ z) : WellFormedStore σ1 F := fun z v hv =>
  if hz : x = z then hC y v ((hz ▸ h1).symm.trans hv) else hC z v ((h2 z hz).symm.trans hv)

include iOp iLF in
/-- A run of the resolved copies `it p` (`tgt p := src p`, an `init` or a `set`) of the elements
    `p` of `ps`, no target a source, from a value-valued store gives each target the value of its
    source, when the targets are distinct or sources of a shared target have equal values. -/
private theorem run_copies {α : Type} (hF : WellFormedSemanticEvalBase F) {it : α → WItem P}
    {tgt src : α → P.Ident}
    (hit : ∀ p, (∃ ty, it p = .init (tgt p) ty (some (.var (src p)))) ∨
      it p = .set (tgt p) (some (.var (src p)))) :
    ∀ (ps : List α) {items : List (Item P)} {σ σ' : SemanticStore P} {tr : List (Event P)},
      (∀ p ∈ ps, ∀ q ∈ ps, tgt p ≠ src q) → ((ps.map tgt).Nodup ∨
        ∀ p ∈ ps, ∀ q ∈ ps, tgt p = tgt q → σ (src p) = σ (src q)) →
      resolveItems T Y (ps.map it) = .ok items → MainRun F items σ tr σ' →
      WellFormedStore σ F → ∀ p ∈ ps, σ' (tgt p) = σ (src p)
  | [], _, _, _, _, _, _, _, _, _ => nofun
  | p :: ps, _, σ, σ', _, hd, hc, hi, hm, hC => by
    obtain ⟨i', σ1, t', hi', hm', h1, h2⟩ := run_var_head hF (hit p) hi hm hC
    have hs : ∀ q ∈ ps, σ1 (src q) = σ (src q) := fun q hq => h2 _ (hd p (.head _) q (.tail _ hq))
    have ih := run_copies hF hit ps (fun p hp q hq => hd p (.tail _ hp) q (.tail _ hq))
      (hc.imp (List.nodup_cons.1 · |>.2) fun hc p hp q hq he => (hs p hp).trans
        ((hc p (.tail _ hp) q (.tail _ hq) he).trans (hs q hq).symm)) hi' hm' (canon_copy hC h1 h2)
    rintro q (_ | ⟨_, hq⟩)
    · rcases Classical.em (∃ r ∈ ps, tgt r = tgt p) with ⟨r, hr, he⟩ | hn
      · rcases hc with hc | hc
        · exact ((List.nodup_cons.1 hc).1 (List.mem_map.2 ⟨r, hr, he⟩)).elim
        · rw [← he, ih r hr, hs r hr, hc r (.tail _ hr) p (.head _) he]
      rw [MainRun.frame hi' hm' _ fun it' hit' hy => hn ?_, h1]
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hit'
      exact ⟨r, hr, Option.some.inj (by rcases hit r with ⟨_, h⟩ | h <;> rw [h] at hy <;> exact hy)⟩
    · rw [ih q hq, hs q hq]

end

include iOp iLF iLV in
/-- The saves of a run of `saveRestore xs` from `s` to `s'` (of no variable of `xs` drawn by the
    run), then items `mid`, the copies and items `mid2` assigning no name the run draws, then the
    restores, keep `n` when no save initializes `n` and the middle keeps `n` unless `n` is
    saved. -/
private theorem saveRestore_keep (hF : WellFormedSemanticEvalBase F) {sv cp rs : Rope (WItem P)}
    {cps : List (P.Ident × P.Ident)} (h : (saveRestore xs).run s = .ok ((sv, cp, rs, cps), s'))
    {mid mid2 : List (WItem P)} (hnt : ∀ ty v, WItem.init n ty v ∉ sv.toList)
    (hxd : ∀ x ∈ xs, ¬ NewIn s s' x)
    (hmid : ∀ it ∈ mid ++ mid2, ∀ y, it.tgt = some y → ¬ NewIn s s' y)
    (hn : n ∉ xs → KeepL F (mid ++ cp.toList ++ mid2) (· = n)) :
    KeepL F (sv.toList ++ (mid ++ cp.toList ++ mid2) ++ rs.toList) (· = n) := by
  obtain ⟨-, ps, hxs, hsv, hcp, hrs, -, hnd, hcs, hd⟩ := saveRestore_str h
  have hmid' : ∀ q ∈ ps, KeepL F (mid ++ cp.toList ++ mid2) (· = q.2.1) := fun q hq =>
    KeepL.frame fun it hit y hy hyq => by
      subst hyq
      rcases Classical.em (it ∈ cp.toList) with hc | hc
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hcp ▸ hc)
        exact hcs p hp q hq (Option.some.inj hy)
      · exact hmid it (by simpa [hc] using hit) _ hy (hd q hq).1
  intro T Y items hi σ tr σ' hC hm m hm'
  subst hm'
  obtain ⟨i12, i3, hi12, hi3, rfl⟩ := (resolveItems_append T Y _ _).1 hi
  obtain ⟨i1, i2, hi1, hi2, rfl⟩ := (resolveItems_append T Y _ _).1 hi12
  obtain ⟨σ2, t12, t3, m12, m3⟩ := MainRun.split hm
  obtain ⟨σ1, t1, t2, m1, m2⟩ := MainRun.split m12
  have hC1 := MainRun.canon hF m1 hC
  by_cases hnx : m ∈ xs
  · have hsx : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2.1 := fun p hp q hq he =>
      hxd p.1 (hxs ▸ List.mem_map_of_mem hp) (he ▸ (hd q hq).1)
    have hs1 := run_copies hF (fun _ => .inl ⟨_, rfl⟩) ps (fun p hp q hq => (hsx q hq p hp).symm)
      (.inl hnd) (hsv ▸ hi1) m1 hC
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hxs ▸ hnx)
    have hv : ∀ q ∈ ps, σ2 q.2.1 = σ q.1 := fun q hq =>
      (hmid' q hq T Y i2 hi2 σ1 t2 σ2 hC1 m2 _ rfl).trans (hs1 q hq)
    exact (run_copies hF (fun _ => .inr rfl) ps hsx (.inr fun p hp q hq he =>
      (hv p hp).trans (he ▸ (hv q hq).symm)) (hrs ▸ hi3) m3 (MainRun.canon hF m2 hC1) p hp).trans
        (hv p hp)
  · rw [MainRun.frame hi3 m3 m fun it hit hy => ?_, hn hnx T Y i2 hi2 σ1 t2 σ2 hC1 m2 m rfl,
      MainRun.frame hi1 m1 m fun it hit hy => ?_]
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hsv ▸ hit)
      exact hnt _ _ (Option.some.inj hy ▸ hsv ▸ List.mem_map_of_mem hp)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hrs ▸ hit)
      exact hnx (Option.some.inj hy ▸ hxs ▸ List.mem_map_of_mem hp)

omit iDE iHB iHF iSF iHI iLI iHFs iWL in
/-- An element of a hash set satisfying `p` is in a fold consing its elements satisfying `p`. -/
private theorem mem_fold_cons_of {A : Std.HashSet P.Ident} {p : P.Ident → Bool}
    (h : A.contains y = true) (hp : p y = true) :
    y ∈ A.fold (fun l x => if p x = true then x :: l else l) [] := by
  rw [Std.HashSet.fold_eq_foldl_toList]
  have H : ∀ (L acc : List P.Ident), (y ∈ acc ∨ (y ∈ L ∧ p y = true)) →
      y ∈ L.foldl (fun l x => if p x = true then x :: l else l) acc := fun L => by
    induction L <;> grind
  exact H _ _ (.inr ⟨by simpa using h, hp⟩)

/-- Prove that a segment of the output of a laid-out `ite` keeps the name `n` the output does not
    declare (`hI`), the segment consisting of `init`s, from the `init` facts `h3`, `hT`, `hE` of
    the three runs of `saveRestore`. -/
local macro "laidk_inits " hI:ident h3:ident hT:ident hE:ident : tactic => `(tactic| (
  refine KeepL.inits (fun it hit => ?_) fun ty v h => $hI ty v (by
    simp only [List.mem_append, h, true_or, or_true])
  first
  | exact $h3 it (List.mem_append_left _ hit)
  | exact $h3 it (List.mem_append_right _ hit)
  | exact $hT it (List.mem_append_right _ hit)
  | exact $hE it (List.mem_append_right _ hit)
  | ((repeat' split at hit) <;>
      simp only [Rope.toList_one, Rope.toList_nil, List.mem_singleton, List.not_mem_nil] at hit <;>
      exact ⟨_, _, _, hit⟩)))

include iOp iLF iLFs iLV in
/-- The walk of a laid-out `ite` from a well-formed state avoiding the names of the form of a
    fresh name of its arms keeps the names of `Keeps` when the walks of its arms do. -/
private theorem laid_k (hF : WellFormedSemanticEvalBase F) {c : P.Expr} {tss ess : PStmts P}
    (hκ : κ ≠ .top) (hwf : WFSt s)
    (hav : ∀ x ∈ Block.idents tss ++ Block.idents ess, ∀ b j, x = freshName b j →
      s.avoid.contains x = true)
    (hT : ∀ κ', κ' ≠ .top → ∀ s0 R s1, (wpList κ' d true tss).run s0 = .ok (R, s1) → WFSt s0 →
      (∀ x ∈ Block.idents tss, ∀ b j, x = freshName b j → s0.avoid.contains x = true) →
      Keeps F κ' s0 s1 R)
    (hE : ∀ κ', κ' ≠ .top → ∀ s0 R s1, (wpList κ' d true ess).run s0 = .ok (R, s1) → WFSt s0 →
      (∀ x ∈ Block.idents ess, ∀ b j, x = freshName b j → s0.avoid.contains x = true) →
      Keeps F κ' s0 s1 R)
    (h : (wpIteLaid κ d c tss ess).run s = .ok (r, s')) : Keeps F κ s s' r := by
  let D := Block.idents tss ++ Block.idents ess
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hcx h5 h6 h7 h8 h9 h10 _ h11 _
    h12 _ hEnd => ?_
  obtain ⟨m2, hg⟩ := wFreshBool_w (D := D) h2
  obtain ⟨m3, hrT⟩ := wFreshBool_w (D := D) h3
  obtain ⟨-, -, hs1, -⟩ := wRen_run h1
  obtain ⟨h4, hκE, hvE, hwE⟩ := hcx.facts
  obtain ⟨m4, S4, hrE, hwf4⟩ := h4.w (D := D)
  have S14 := (wFreshBool_laidSame h2).trans ((wFreshBool_laidSame h3).trans S4)
  have wf4 := hwf4 ((wFreshBool_walk h3).wf ((wFreshBool_walk h2).wf
    ((wRen_walk h1).wf hwf (by simp)) (by simp)) (by simp))
  have OE := wpList_walkOK h5
  have OT := wpList_walkOK h6
  have WE := wpList_writes (D := D) κE d true ess (fun _ h => List.mem_append_right _ h) h5
  have WT := wpList_writes (D := D) (.name rT) d true tss (fun _ h => List.mem_append_left _ h) h6
  have hD4 := ((wRen_w (D := D) h1).trans (m2.trans (m3.trans m4))).avoid ▸ hav
  have hD5 := WE.avoid ▸ hD4
  have wf5 : WFSt s5 := OE.wf wf4 fun x hx => hD4 x (by simp [stmtsInits_mem_idents x hx])
  have KE := hE κE hκE s4 E s5 h5 wf4 fun x hx => hD4 x (List.mem_append_right _ hx)
  have KT := hT (.name rT) nofun s5 T s6 h6 wf5 fun x hx => hD5 x (List.mem_append_left _ hx)
  obtain ⟨m7, S7, hk3, hsc3, -, hrs3, hcps3, -⟩ := srFacts (D := D) h7
  obtain ⟨m8, S8, hkT, -, -, -, -, -⟩ := srFacts (D := D) h8
  obtain ⟨m9, S9, hkE, -, -, -, -, -⟩ := srFacts (D := D) h9
  obtain ⟨-, S10, -, -⟩ := h10.w (D := D)
  obtain ⟨-, S11, -, -⟩ := h11.w (D := D)
  obtain ⟨-, S12, -, -⟩ := h12.w (D := D)
  have S612 := S7.trans (S8.trans (S9.trans (S10.trans (S11.trans S12))))
  have hk4 : s4.clock = s.clock := by rw [S14.clock, hs1]
  rcases hEnd with ⟨-, -, rfl⟩ | ⟨-, hFr, rfl⟩
  · exact KeepL.frame fun it hit => by simp [Rope.toList_nil] at hit
  obtain ⟨LF, -⟩ := liveAdd_ls (E := fun _ => False) hFr
  intro Tm Ym items hi σ tr σ' hC hm n ⟨hA, hI, hv, hlb⟩
  refine (?_ : KeepL F _ (· = n)) Tm Ym items hi σ tr σ' hC hm n rfl
  obtain ⟨u, hu, hut⟩ := liveBefore_iff.mp hlb
  have hu5 := Nat.lt_of_lt_of_le hut (hk4 ▸ OE.clock)
  have h6u : s6.live[n]? = some u := (S612.live ▸ LF.stamp n u hu).resolve_right
    (Nat.not_le.2 (S612.clock ▸ Nat.lt_of_lt_of_le hu5 OT.clock))
  have hl0 : liveBefore s6 n s4.clock = true := liveBefore_iff.mpr ⟨u, h6u, hk4 ▸ hut⟩
  simp only [Bool.eq_false_iff, ne_eq, unionSet_iff, not_or] at hA
  have hTA : T.ax = false → T.A.contains n = false := fun hx =>
    Bool.eq_false_iff.mpr fun h' => hA.1 (by simp [hx, h'])
  simp only [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
    List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil] at hI ⊢
  have hI' : ∀ ty v, WItem.init n ty v ∉ _ := fun ty v h => hI ⟨ty, v, h⟩
  have hTw : ∀ x, T.A.contains x = true → ∀ y, NewIn s6 s9 y → x ≠ y :=
    fun x hx y hy he => not_wr0 wf5 WT.toWMono hD5 hy (he ▸ WT.A x hx)
  have hM : ∀ x ∈ (if T.ax = true then [] else interSet T.A E.R), x ≠ n := fun x hx he =>
    Bool.false_ne_true ((hTA (mem_ite_interSet hx).1).symm.trans (he ▸ (mem_ite_interSet hx).2))
  iterate 5 refine KeepL.app hF (by laidk_inits hI' hk3 hkT hkE) ?_
  rw [show ∀ a b c d e f g : List (WItem P), a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g))))) =
    a ++ (b ++ c ++ d ++ e) ++ f ++ g by simp]
  refine KeepL.app hF ?_ ?_
  · refine saveRestore_keep hF h8 (fun ty v h => hI' ty v (by out_mem h)) (fun x hx hy => hTw x
      (fold_filter_mem hx) x (hy.widen m7.avoid m7.next m9.next) rfl)
      (fun it hit y hy hy8 => ?_) (fun hn => ?_)
    · have hy9 := hy8.widen m7.avoid m7.next m9.next
      simp only [List.mem_append] at hit
      rcases hit with (h' | h') | h'
      · exact (WT.out it h' _ hy).elim (not_wr0 wf5 WT.toWMono hD5 hy9) fun h'' =>
          (Option.some.inj h'' ▸ hrT).disj hy9 (m4.trans (WE.toWMono.trans WT.toWMono)).next
      · exact (hsc3 it (List.mem_append_right _ h') _ hy).disj hy8 (Nat.le_refl _)
      · exact hTw _ (mem_ite_interSet (hrs3 it h' _ hy)).2 _ hy9 rfl
    · refine KeepL.app hF (KeepL.app hF (KeepL.app hF ?_ (by laidk_inits hI' hk3 hkT hkE))
        (by laidk_inits hI' hk3 hkT hkE))
        (KeepL.frame fun it hit y hy he => hM _ (hrs3 it hit y hy) he)
      by_cases hTn : T.out.isNil = true
      · exact Rope.isNil_toList hTn ▸ KeepL.frame nofun
      refine KeepL.mono KT fun m hm => ?_
      subst hm
      refine ⟨?_, fun ⟨ty, v, h'⟩ => hI' ty v (by out_mem h'), ?_, liveBefore_iff.mpr ⟨u, h6u, hu5⟩⟩
      · exact (Bool.eq_false_or_eq_true T.ax).elim (fun hx => Bool.eq_false_iff.mpr fun h' =>
          hn (List.mem_ite_nil_right.2 ⟨hx, mem_fold_cons_of h' (by simp [hl0])⟩)) hTA
      · exact fun hm => hI' (.known HasBool.boolTy) (some (.var g))
          (by out_mem (List.mem_singleton.1 hm) hTn)
  iterate 2 refine KeepL.app hF (by laidk_inits hI' hk3 hkT hkE) ?_
  rw [show ∀ a b c d e : List (WItem P), a ++ (b ++ (c ++ (d ++ e))) =
    a ++ (b ++ c ++ []) ++ d ++ e by simp]
  refine KeepL.app hF ?_ ?_
  · have m58 := WT.toWMono.trans (m7.trans m8)
    refine saveRestore_keep hF h9 (fun ty v h => hI' ty v (by out_mem h))
      (fun x hx hy => not_wr0 wf4 WE.toWMono hD4 (hy.widen m58.avoid m58.next (Nat.le_refl _))
        (WE.A x (fold_filter_mem hx))) (fun it hit y hy hy9 => ?_)
      (fun hn => ?_)
    · replace hy9 := hy9.widen m58.avoid m58.next (Nat.le_refl _)
      exact (WE.out it (by simpa using hit) _ hy).elim (not_wr0 wf4 WE.toWMono hD4 hy9) fun h =>
        (hwE _ h).elim (fun e => (e ▸ hg).disj hy9 (m3.trans (m4.trans WE.toWMono)).next)
          fun h => (hrE _ h).disj hy9 WE.next
    · refine KeepL.app hF (KeepL.app hF ?_ (by laidk_inits hI' hk3 hkT hkE))
        (KeepL.frame nofun)
      by_cases hEn : E.out.isNil = true
      · exact Rope.isNil_toList hEn ▸ KeepL.frame nofun
      refine KeepL.mono KE fun m hm => ?_
      subst hm
      refine ⟨?_, fun ⟨ty, v, h'⟩ => hI' ty v (by out_mem h'), fun hm => ?_,
        liveBefore_iff.mpr ⟨u, OT.liveOld _ u h6u hu5, hk4 ▸ hut⟩⟩
      · exact (Bool.eq_false_or_eq_true E.ax).elim (fun hx => Bool.eq_false_iff.mpr fun h' =>
          hn (List.mem_ite_nil_right.2 ⟨hx, mem_fold_cons_of h' (by simp [hl0])⟩))
          fun hx => Bool.eq_false_iff.mpr fun h' => hA.2 (by simp [hx, h'])
      · rcases hvE _ hm with rfl | hm | rfl
        · exact hI' (.known HasBool.boolTy) (some (kAnd κ wc)) (by out_mem)
        · exact hv hm
        · exact hI' (.known HasBool.boolTy) (some (kAnd κ (WExpr.var g).not)) (by out_mem hEn)
  refine KeepL.app hF (KeepL.frame fun it hit y hy he => ?_)
    (KeepL.frame fun it hit y hy he => hv (he ▸ wvar_mem (setReach_tgt _ _ _
      (mem_ite_nil' hit) y hy)))
  obtain ⟨p, hp, rfl⟩ := (mem_sets _ _ hit).resolve_left (by simp [Rope.toList_nil])
  exact hM _ (hcps3 p (List.mem_filter.mp hp).1).1 ((Option.some.inj hy).trans he)

include iOp iLV in
mutual
/-- The walk of a statement under a variable context with an obligation following it, from a
    well-formed state avoiding the names of the form of a fresh name of the statement, keeps the
    names of `Keeps`. -/
private theorem wpStmt_keep [LawfulHasFvar P] [LawfulHasFvars P] {κ : RE P} (hκ : κ ≠ .top)
    (d : Nat) (F : P.Factory) (hF : WellFormedSemanticEvalBase F) :
    ∀ (s : PStmt P) {st st' : WSt P} {r : WRes P},
      (wpStmt κ d true s).run st = .ok (r, st') → WFSt st →
      (∀ x ∈ Stmt.idents s, ∀ b j, x = freshName b j → st.avoid.contains x = true) →
      Keeps F κ st st' r
  | .cmd _, _, _, _, h, _, _ | .exit .., _, _, _, h, _, _ | .typeDecl .., _, _, _, h, _, _ =>
    KeepL.frame fun it hit y hy ⟨hA, hI, hv, _⟩ => (cmd_tgt hκ (by simp) h it hit y hy).elim
      (fun h' => nomatch hA.symm.trans h') fun h' => h'.elim hI hv
  | .loop .., _, _, _, h, _, _ | .ite .nondet .., _, _, _, h, _, _ => by
    simp only [wpStmt] at h
    cases h
  | .block l body md, s, _, _, h, hwf, hav => by
    obtain ⟨s0, B, s4, hs0, h4, h7, rfl⟩ := block_inv hκ h
    have KB := wpList_keep hκ (d + 1) F hF body h4 (hs0 ▸ hwf.block_entry l (d + 1) s.clock)
      fun x hx b j hj => (by rw [hs0] : s0.avoid = s.avoid) ▸ hav x (by simpa [Stmt.idents,
        ExprOrNondet.getVars_det, getFvars_mem_exprFV] using hx) b j hj
    obtain ⟨L7, -⟩ := liveAdd_ls (E := fun _ => False) h7
    have hc4 : s.clock ≤ s4.clock := by simpa [hs0] using (wpList_walkOK h4).clock
    simp only [Keeps, Rope.toList_app, List.append_assoc]
    intro T Y items hi σ tr σ' hC hm n ⟨hA, hI, hv, hl⟩
    obtain ⟨ia, ib, ha', hb', rfl⟩ := (resolveItems_append T Y _ _).1 hi
    obtain ⟨σ1, t1, t2, h1, h2⟩ := MainRun.split hm
    refine (MainRun.frame hb' h2 n fun it hit hy => ?_).trans
      (KB _ _ _ ha' _ _ _ hC h1 n ⟨?_, ?_, hv, ?_⟩)
    · rcases List.mem_append.1 hit with hit | hit
      · obtain ⟨q, hq, rfl⟩ := (mem_sets _ _ hit).resolve_left (by simp [Rope.toList_nil])
        simp [(mem_insert_merges _ _).2 (.inr ⟨q, hq, Option.some.inj hy⟩)] at hA
      · exact hv (wvar_mem (setReach_tgt _ _ _ (mem_ite_nil (mem_ite_nil hit)) n hy))
    · exact Bool.eq_false_iff.2 fun h' => by simp [(mem_insert_merges _ _).2 (.inl h')] at hA
    · exact fun ⟨ty, v, hi⟩ => hI ⟨ty, v, by simp [hi]⟩
    · obtain ⟨u, hu, hlt⟩ := liveBefore_iff.1 hl
      exact liveBefore_iff.2 ⟨u, (L7.stamp n u hu).resolve_right
        (Nat.not_le.2 (Nat.lt_of_lt_of_le hlt hc4)), by rwa [hs0]⟩
  | .ite (.det c) tss ess md, s, s', r, h, hwf, hav0 => by
    simp only [wpStmt, ↓reduceIte] at h
    exact laid_k hF hκ hwf (fun x hx => hav0 x (by grind [Stmt.idents]))
      (fun _ hκ' _ _ _ => wpList_keep hκ' d F hF tss)
      (fun _ hκ' _ _ _ => wpList_keep hκ' d F hF ess) h
  termination_by structural s => s

/-- The walk of a list under a variable context with an obligation following it, from a
    well-formed state avoiding the names of the form of a fresh name of the list, keeps the
    names of `Keeps`. -/
private theorem wpList_keep [LawfulHasFvar P] [LawfulHasFvars P] {κ : RE P} (hκ : κ ≠ .top)
    (d : Nat) (F : P.Factory) (hF : WellFormedSemanticEvalBase F) :
    ∀ (ss : PStmts P) {st st' : WSt P} {r : WRes P},
      (wpList κ d true ss).run st = .ok (r, st') → WFSt st →
      (∀ x ∈ Block.idents ss, ∀ b j, x = freshName b j → st.avoid.contains x = true) →
      Keeps F κ st st' r
  | [], _, _, _, h, _, _ => by
    simp only [wpList, StateT.run_pure] at h
    cases h
    exact KeepL.frame fun it hit => by simp [Rope.toList_nil] at hit
  | s :: rest, st, st', _, h, hwf, hav => by
    obtain ⟨r, st1, a, st2, h1, h2, hc⟩ := wpList_cons_arm hκ h
    have Kr := wpList_keep hκ d F hF rest h1 hwf fun x hx => hav x (by simp [Block.idents, hx])
    have Or := wpList_walkOK h1
    have hwf1 : WFSt st1 := Or.wf hwf fun x hx b j hj =>
      hav x (by simp [Block.idents, stmtsInits_mem_idents x hx]) b j hj
    have Ka := wpStmt_keep hκ d F hF s h2 hwf1 fun x hx b j hj =>
      Or.avoid ▸ hav x (by simp [Block.idents, hx]) b j hj
    have hc1 := Or.clock
    have hl : st'.live = st2.live := by rcases hc with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl
    have hb : ∀ n, liveBefore st' n st.clock = true →
        liveBefore st2 n st1.clock = true ∧ liveBefore st1 n st.clock = true := fun n hn => by
      obtain ⟨u, hu, hlt⟩ := liveBefore_iff.1 hn
      exact ⟨liveBefore_iff.2 ⟨u, hl ▸ hu, by omega⟩,
        liveBefore_iff.2 ⟨u, (wpStmt_walkOK h2).liveOld n u (hl ▸ hu) (by omega), hlt⟩⟩
    rcases hc with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact KeepL.mono Ka fun n ⟨hA, hI, hv, hn⟩ => ⟨hA, hI, hv, (hb n hn).1⟩
    simp only [Keeps, WRes.combine, Rope.toList_app]
    refine KeepL.app hF (KeepL.mono Ka fun n ⟨hA, hI, hv, hn⟩ => ⟨?_, ?_, hv, (hb n hn).1⟩)
      (KeepL.mono Kr fun n ⟨hA, hI, hv, hn⟩ => ⟨?_, ?_, hv, (hb n hn).2⟩)
    · exact Bool.eq_false_iff.2 fun h' => by simp [unionSet_iff.2 (.inl h')] at hA
    · exact fun ⟨ty, v, hi⟩ => hI ⟨ty, v, List.mem_append_left _ hi⟩
    · exact Bool.eq_false_iff.2 fun h' => by simp [unionSet_iff.2 (.inr h')] at hA
    · exact fun ⟨ty, v, hi⟩ => hI ⟨ty, v, List.mem_append_right _ hi⟩
  termination_by structural ss => ss
end

include iOp iLF iLFs iLV in
/-- A main-path run of the resolved output of an arm walk, from a value-valued store, changes
    only names the arm assigns, names its output declares, variables of the context, and names
    not live after the walk with a stamp below the clock before it. -/
theorem arm_writesLive (hF : WellFormedSemanticEvalBase F) {ss : PStmts P} {st st' : WSt P}
    (h : (wpList κ d true ss).run st = .ok (r, st')) (hκ : κ ≠ .top) (hwf : WFSt st)
    (hav : ∀ x ∈ Block.idents ss, ∀ b j, x = freshName b j → st.avoid.contains x = true) :
    ∀ T Y items, resolveItems T Y r.out.toList = .ok items → ∀ σL tr σL', WellFormedStore σL F →
      MainRun F items σL tr σL' → ∀ n, σL' n ≠ σL n →
        r.A.contains n = true ∨ n ∈ wDecls r.out.toList ∨ n ∈ RE.vars κ ∨
          liveBefore st' n st.clock = false := by
  intro T Y items hi σL tr σL' hC hm n hn
  refine Classical.byContradiction fun hc => hn ?_
  obtain ⟨h1, h2, h3, h4⟩ := by simpa only [not_or, Bool.not_eq_true, Bool.not_eq_false] using hc
  exact wpList_keep hκ d F hF ss h hwf hav T Y items hi σL tr σL' hC hm n
    ⟨h1, fun hi => h2 (wDecls_of_initIn hi), h3, h4⟩

/-! ## The targets of arm outputs -/

include iOp iLF iLFs in
/-- A main-path run of the resolved output of the else arm of a laid-out `ite`, walked from `s4`
    to `s5` under the context `κE`, keeps every name that the output of the then arm, walked from
    `s5` to `s6` under `name rT`, declares: both arms are well scoped from `S`, the walk starts
    from a well-formed state with label depths at most `d` that avoids the names of the form of
    a fresh name of `S` and of the arms, and the variables of `κE` are fresh names drawn before
    `s4`, not avoided and no renamings at `s4`. -/
theorem arm_crossKeep {κE : RE P} {tss ess : PStmts P} {s4 s5 s6 : WSt P} {Er Tr : WRes P}
    {rT : P.Ident} {Lc S : List P.Ident} (hE : (wpList κE d true ess).run s4 = .ok (Er, s5))
    (hT : (wpList (.name rT) d true tss).run s5 = .ok (Tr, s6)) (hκE : κE ≠ .top) (hwf : WFSt s4)
    (hav : ∀ x ∈ S ++ (Block.idents tss ++ Block.idents ess), ∀ b j,
      x = freshName b j → s4.avoid.contains x = true) (hST : Block.WellScoped Lc S tss)
    (hSE : Block.WellScoped Lc S ess)
    (hL : ∀ (l : String) (t : Nat), s4.labelDepth[l]? = some t → t ≤ d)
    (hκv : ∀ y ∈ RE.vars κE, (∃ b j, y = freshName b j ∧ j < s4.next) ∧
      s4.avoid.contains y = false ∧ ∀ x : P.Ident, s4.nm[x]? ≠ some y) :
    ∀ T Y iE, resolveItems T Y Er.out.toList = .ok iE → ∀ σa tr σb, MainRun F iE σa tr σb →
      ∀ n ∈ wDecls Tr.out.toList, σb n = σa n := by
  intro T Y iE hiE σa tr σb hm n hn
  refine MainRun.frame hiE hm n fun it hit hy => ?_
  have OE := wpList_walkOK hE
  have AE := wpList_arm hκE d ess hE
  have XE := wpList_scope hκE d ess hE hwf (fun x hx => hav x (by grind)) hSE hL
  have hwf5 : WFSt s5 := OE.wf hwf fun x hx b j hj =>
    hav x (by simp [stmtsInits_mem_idents x hx]) b j hj
  have hC : ∀ z ∈ S, curName s5 z ≠ some n := fun z hz hcz =>
    arm_declNotCur hT nofun hwf5 hST (fun x hx b j hj => OE.avoid ▸ hav x (by grind) b j hj)
      (fun l t ht => hL l t (by rwa [OE.labelDepth l] at ht)) n hn z hz
      ((wpList_walkOK hT).names z n (wfl_inits_disjoint S tss hST z hz) hcz)
  have hI : ¬ InitIn Er.out.toList n := fun ⟨ty, v, hi⟩ => by
    rcases arm_decl hT nofun n hn with hd | ⟨hnI, ht⟩ | ⟨x, -, hx⟩
    · rcases AE.decl n ty v hi with hd' | ⟨hnE, -⟩ | ⟨x, -, hx4⟩
      · exact hd'.disj hd (Nat.le_refl _)
      · obtain ⟨b, j, rfl, hna, -, -⟩ := hd
        simp [OE.avoid, hav _ (by simp [stmtsInits_mem_idents _ hnE]) b j rfl] at hna
      · obtain ⟨b, j, he, -, hj, -⟩ := hd
        exact hwf.nm_ne_new hx4 he (Nat.le_trans OE.next hj)
    · rcases AE.decl n ty v hi with ⟨b, j, he, hna, -, -⟩ | ⟨hnE, -⟩ | ⟨x, -, hx4⟩
      · simp [hav n (by simp [stmtsInits_mem_idents n hnI]) b j he] at hna
      · simp [AE.takenIn n hnE] at ht
      · obtain ⟨-, b, j, he, -, hna⟩ := hwf.nm_fresh x n hx4
        simp [hav n (by simp [stmtsInits_mem_idents n hnI]) b j he] at hna
    · exact XE.declNm n ty v hi x hx
  rcases XE.tgt it hit n hy with hA | hI' | hv | ⟨z, hz, hcz⟩
  · exact (XE.asg n hA).elim (fun ⟨z, hz, _, hcz, _⟩ => hC z hz hcz) hI
  · exact hI hI'
  · obtain ⟨⟨b, j, he, hj⟩, hna, hnm⟩ := hκv n hv
    rcases arm_decl hT nofun n hn with hd | ⟨hnI, -⟩ | ⟨x, -, hx⟩
    · exact hd.not_below ⟨b, j, he, Nat.lt_of_lt_of_le hj OE.next⟩
    · simp [hav n (by simp [stmtsInits_mem_idents n hnI]) b j he] at hna
    · exact (OE.nm x n hx).elim (hnm x) fun hf => hf.ne ⟨b, j, he, hj⟩ rfl
  · exact hC z hz hcz

/-- A list walk at depth `d`, from a state whose label depths are at most `d` and without
    carried merges at depths above `d`, ends without carried merges at depths above `d`. -/
theorem wpList_carriesHigh {f : Bool} {ss : PStmts P} {st st' : WSt P}
    (h : (wpList κ d f ss).run st = .ok (r, st'))
    (hL : ∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d)
    (hhigh : ∀ k, d < k → st.carries.getD k [] = []) :
    ∀ k, d < k → st'.carries.getD k [] = [] := fun k hk =>
  List.eq_nil_iff_forall_not_mem.2 fun q hq =>
    List.not_mem_nil (hhigh k hk ▸ wpList_carries_high h hL k hk q hq :)

omit iLI iWL in
/-- A walk step keeping the label depths and the live stamp of a live name `n` keeps `n` live
    before the enclosing blocks from depth `t` on: a block entry stamp the step changes is from
    the clock before the step on, above every live stamp. -/
theorem LiveFrom.walk {st st1 : WSt P} {t : Nat} (hw : WalkCore D st st1)
    (hld : ∀ l : String, st1.labelDepth[l]? = st.labelDepth[l]?) (hwf : WFSt st)
    (hk : ∀ s, st.live[n]? = some s → st1.live[n]? = some s) (hl : st.live.contains n = true)
    (h : LiveFrom st t n) : LiveFrom st1 t n := by
  intro l j hj ht
  obtain ⟨s, hs⟩ : ∃ s, st.live[n]? = some s := Option.isSome_iff_exists.1 (by simpa using hl)
  have hb := h l j (hld l ▸ hj) ht
  simp only [liveBefore, hs, hk s hs, decide_eq_true_eq] at hb ⊢
  exact (hw.stamp j).elim (fun he => he ▸ hb) (Nat.lt_of_lt_of_le (hwf.live_stamp n s hs))

end -- public section

end WP
end Imperative
