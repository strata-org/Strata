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

/-! # The names a run of a walk's guarded output writes

A run of the resolved output of a WP walk (`wpList`, `wpStmt`, `wpIteLaid`, `wpIteReal`) from
`st` to `st'` changes only names of four kinds (`WalkW`, `WalkW.frame`): fresh names drawn by
the walk, recorded renamings of `st`, identifiers of the walked fragment (together `Wr0`), and
the variable of the reach context that `setReach` assigns (`RE.wvar`: `r` under `name r`, `g`
under `neg g` and under `andNeg q g`, never `q`).  The walks also register only carried merges
whose targets are such names and whose selectors read only names they draw (`CarryNew`).  A run
of items keeps every bound name bound to a value of the types of its value (`MainRun.typed`).

From these, for the walks of `s` after `rest` in a list `s :: rest`, a run of the output of
`rest` keeps the registrations of `s` (`keep_regs`), the selectors of its carried merges
(`keep_sel`), the enclosing reach `q` of a context `andNeg q g` (`keep_andNeg`), and the types of
bound names (`keep_typed`).

Key definitions: `Wr0`, `WMono`, `WalkW`, `CarryNew`, `RE.wvar`, `InitIn`.

Key theorems: `wpList_writes`, `wpStmt_writes`, `WalkW.frame`, `MainRun.frame`, `MainRun.typed`,
`keep_regs`, `keep_andNeg`, `keep_sel`, `keep_typed`. -/

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


/-! ## Runs of resolved items -/

/-- The name an item of the guarded program assigns: the target of an `init` or a `set`. -/
@[expose] def WItem.tgt : WItem P → Option P.Ident
  | .init x _ _ => some x
  | .set x _ => some x
  | _ => none


omit iLB iHI iLI in
/-- A run of resolved items changes no name that none of the items assigns. -/
theorem MainRun.frame :
    ∀ {l : List (WItem P)} {items : List (Item P)} {σ σ' : SemanticStore P}
      {tr : List (Event P)}, resolveItems T Y l = .ok items → MainRun F items σ tr σ' →
      ∀ y, (∀ it ∈ l, it.tgt ≠ some y) → σ' y = σ y
  | [], _, _, _, _, h, hr, _, _ => by cases h; cases hr; rfl
  | it :: l, _, _, _, _, h, hr, y, hy => by
    obtain ⟨a, r, ha, hr', rfl⟩ := resolveItems_cons_ok h
    cases hr with
    | side hm => exact MainRun.frame hr' hm y fun it hit => hy it (.tail _ hit)
    | plain hc hm =>
      rw [MainRun.frame hr' hm y fun it hit => hy it (.tail _ hit)]
      have hy0 := hy it (.head _)
      cases it <;> simp only [resolveItem, resolveOE, bind, Except.bind, pure, Except.pure] at ha
      all_goals (repeat' split at ha) <;> cases ha <;> unfold EvalE at hc <;> cases hc
      all_goals grind [InitState, UpdateState, WItem.tgt, mkInit]

section
omit iDE iBE iLB iSF iHI iLI iHa iWL
include iLV

omit iHF iHFs in
/-- An initialization keeps a bound name bound, to a value with every type of the types `Q` its
    value has; so does an assignment of a value of the stored type. -/
private theorem store_typed {σ σ1 : SemanticStore P} {v : P.Val}
    (h : InitState P σ x v σ1 ∨ (UpdateState P σ x v σ1 ∧ HasVal.valueOfStoredTy (P := P) F σ x v))
    {Q : P.Ty → Prop} {w : P.Val} (hw : σ n = some w) (hQ : ∀ ty, Q ty → HasVal.valueOfTy F w ty) :
    ∃ w', σ1 n = some w' ∧ ∀ ty, Q ty → HasVal.valueOfTy F w' ty := by
  rcases Classical.em (x = n) with rfl | hn
  · rcases h with ⟨h0, -, -⟩ | ⟨⟨_, h1, -⟩, ⟨p, ty0, hp, hp0, hv⟩⟩
    · cases hw.symm.trans h0
    · cases hw.symm.trans hp
      exact ⟨v, h1, fun ty hq => LawfulHasVal.valueOfTy_congr _ _ _ _ _ (hQ ty hq) hp0 hv⟩
  · rcases h with ⟨_, -, h2⟩ | ⟨⟨_, -, h2⟩, -⟩ <;> exact ⟨w, (h2 n hn).trans hw, hQ⟩
omit iHFs in
/-- A command keeps a bound name bound, to a value with every type of the types `Q` its value
    has. -/
private theorem evalE_typed {σ σ1 : SemanticStore P} {c : CmdExt P} {evs : List (Event P)}
    (h : EvalE F σ c σ1 evs) {Q : P.Ty → Prop} {w : P.Val} (hw : σ n = some w)
    (hQ : ∀ ty, Q ty → HasVal.valueOfTy F w ty) :
    ∃ w', σ1 n = some w' ∧ ∀ ty, Q ty → HasVal.valueOfTy F w' ty := by
  rcases c with c | _ <;> unfold EvalE at h <;> cases h
  all_goals try first | exact ⟨w, hw, hQ⟩ | exact store_typed (.inl ‹_›) hw hQ
  all_goals exact store_typed (.inr ⟨‹_›, ‹_›⟩) hw hQ
omit iHFs in
/-- A run of items keeps a bound name bound, to a value with every type of the types `Q` its
    value has. -/
theorem MainRun.typed {Q : P.Ty → Prop} :
    ∀ {items : List (Item P)} {σ σ' : SemanticStore P} {tr : List (Event P)},
      MainRun F items σ tr σ' → ∀ {n : P.Ident} {w : P.Val}, σ n = some w →
      (∀ ty, Q ty → HasVal.valueOfTy F w ty) →
      ∃ w', σ' n = some w' ∧ ∀ ty, Q ty → HasVal.valueOfTy F w' ty
  | _, _, _, _, .nil, _, w, hw, hQ => ⟨w, hw, hQ⟩
  | _, _, _, _, .plain hc hm, _, _, hw, hQ =>
    (evalE_typed hc hw hQ).elim fun _ ⟨hw1, hQ1⟩ => MainRun.typed hm hw1 hQ1
  | _, _, _, _, .side hm, _, _, hw, hQ => MainRun.typed hm hw hQ

end

/-! ## Selectors -/

/-- The expression is built from variables satisfying `good`, Boolean literals and conditionals
    (the form of the selector of a carried merge). -/
@[expose] def SelOK (good : P.Ident → Prop) : WExpr P → Prop
  | .user _ _ => False
  | .var x => good x
  | .lit _ => True
  | .ite c t e => SelOK good c ∧ SelOK good t ∧ SelOK good e

omit iBE iLB iHI iLI iHa in
/-- A value of a conditional in one store is its value in another store where its three parts
    evaluate alike. -/
private theorem ev_ite_congr {F : P.Factory} {σ σ' : SemanticStore P} {c t e : P.Expr} {v : P.Val}
    (hc : P.eval F σ' c = P.eval F σ c) (ht : P.eval F σ' t = P.eval F σ t)
    (he : P.eval F σ' e = P.eval F σ e) (h : P.eval F σ (WPOps.ite c t e) = some v) :
    P.eval F σ' (WPOps.ite c t e) = some v :=
  WPLang.ev_ite_congr h (fun _ hw => hc.trans hw) (fun _ hw => ht.trans hw) fun _ hw => he.trans hw
include iOp iLF iLV in
omit iLB iHI iLI iLV in
/-- A resolved selector evaluates alike in two value-valued stores that agree on its
    variables. -/
theorem sel_eval (hF : WellFormedSemanticEvalBase F) {σ σ' : SemanticStore P}
    (hC : WellFormedStore σ F)
    (hC' : WellFormedStore σ' F) {good : P.Ident → Prop} (hg : ∀ x, good x → σ' x = σ x) :
    ∀ {e : WExpr P} {e' : P.Expr}, SelOK good e → resolveE T Y e = .ok e' →
      P.eval F σ' e' = P.eval F σ e'
  | .user _ _, _, h, _ => h.elim
  | .var x, _, h, he => by
    obtain ⟨ty, rfl⟩ := resolveE_var he
    show P.eval F σ' (HasFvar.mkTypedFvar x ty) = P.eval F σ (HasFvar.mkTypedFvar x ty)
    rw [hF.var _ x σ' hC' (LawfulHasFvar.getFvar_mkTypedFvar x ty),
      hF.var _ x σ hC (LawfulHasFvar.getFvar_mkTypedFvar x ty), hg x h]
  | .lit b, _, _, he => by cases he; cases b <;> simp [hF.val.eval_ff, hF.val.eval_tt]
  | .ite c t e, _, ⟨h1, h2, h3⟩, he => by
    obtain ⟨c', t', e', hc, ht, hee, rfl⟩ := resolveE_ite.1 he
    have ec := sel_eval hF hC hC' hg h1 hc
    have et := sel_eval hF hC hC' hg h2 ht
    have ee := sel_eval hF hC hC' hg h3 hee
    exact Option.ext fun v => ⟨ev_ite_congr ec.symm et.symm ee.symm, ev_ite_congr ec et ee⟩

/-! ## The write set of a walk -/

/-- The names a walk from `s` to `s'` of a fragment with identifiers among `D` may assign, apart
    from its reach variable: fresh names drawn by the walk, recorded renamings of `s`, and the
    identifiers `D`. -/
@[expose] def Wr0 (D : List P.Ident) (s s' : WSt P) (y : P.Ident) : Prop :=
  NewIn s s' y ∨ (∃ z : P.Ident, s.nm[z]? = some y) ∨ y ∈ D

/-- The variable of a reach context that `setReach` assigns. -/
@[expose] def RE.wvar : RE P → Option P.Ident
  | .top => none
  | .name r => some r
  | .neg g => some g
  | .andNeg _ g => some g

/-- A carried merge `(x, v, xB)` registered by a walk from `s` to `s'`: its target `x` may be
    assigned by the walk (`Wr0`), its copy `xB` is drawn by the walk, and `v` selects between
    `xB` and `x` with a selector over names drawn by the walk. -/
@[expose] def CarryNew (D : List P.Ident) (s s' : WSt P) (q : P.Ident × WExpr P × P.Ident) :
    Prop :=
  Wr0 D s s' q.1 ∧ NewIn s s' q.2.2 ∧
    ∃ e, q.2.1 = .ite e (.var q.2.2) (.var q.1) ∧ SelOK (NewIn s s') e

/-- How a walk from `s` to `s'` changes the state: the avoided names are kept, the counter does
    not decrease, the recorded renaming of a variable after it is the one before it or a name
    drawn by the walk, and a new carried merge is registered by it (`CarryNew`). -/
structure WMono (D : List P.Ident) (s s' : WSt P) : Prop where
  avoid : s'.avoid = s.avoid
  next : s.next ≤ s'.next
  nm : ∀ x n : P.Ident, s'.nm[x]? = some n → s.nm[x]? = some n ∨ NewIn s s' n
  carries : ∀ k q, q ∈ s'.carries.getD k [] → q ∈ s.carries.getD k [] ∨ CarryNew D s s' q

/-- The write facts of a walk from `s` to `s'` with result `r` under the reach context `κ`, of a
    fragment with identifiers among `D`: the state changes as `WMono` says, every item of the
    output assigns a name the walk may assign (`Wr0`) or the reach variable of `κ`, every
    assigned name of the result may be assigned by the walk, and the registrations are drawn by
    the walk. -/
structure WalkW (D : List P.Ident) (κ : RE P) (s s' : WSt P) (r : WRes P) : Prop
    extends WMono D s s' where
  out : ∀ it ∈ r.out.toList, ∀ x, it.tgt = some x → Wr0 D s s' x ∨ κ.wvar = some x
  A : ∀ x, r.A.contains x = true → Wr0 D s s' x
  regs : ∀ e ∈ r.regs.toList, NewIn s s' e

section
omit iLI iWL

/-- A name drawn between `s` and `a` is drawn between `s` and any state with a counter from
    `a.next` on. -/
theorem NewIn.up {a b : WSt P} (h : NewIn s a n) (hb : a.next ≤ b.next) :
    NewIn s b n := by grind [NewIn]
omit iDE iBE iLB iHB iHF iSF iHI iHa iHFs in
/-- Selectors over names satisfying `p` are selectors over names satisfying a weaker `q`. -/
theorem SelOK.imp {p q : P.Ident → Prop} (h : ∀ x, p x → q x) :
    ∀ {e : WExpr P}, SelOK p e → SelOK q e :=
  fun {e} => by induction e <;> simp_all [SelOK]

/-- A name a walk from `s1` to `s2` may assign may be assigned by a wider walk. -/
theorem Wr0.widen {s0 s1 s2 s3 : WSt P} (h : Wr0 D s1 s2 y) (hm : WMono D s0 s1)
    (h12 : s1.next ≤ s2.next) (h3 : s2.next ≤ s3.next) :
    Wr0 D s0 s3 y := by
  rcases h with h | ⟨z, hz⟩ | h
  · exact .inl (h.widen hm.avoid hm.next h3)
  · exact (hm.nm z y hz).elim (fun h => .inr (.inl ⟨z, h⟩)) (.inl <| ·.up (Nat.le_trans h12 h3))
  · exact .inr (.inr h)
/-- A carried merge registered by a walk from `s1` to `s2` is registered by a wider walk. -/
theorem CarryNew.widen {s0 s1 s2 s3 : WSt P} {q : P.Ident × WExpr P × P.Ident}
    (h : CarryNew D s1 s2 q) (hm : WMono D s0 s1) (h12 : s1.next ≤ s2.next)
    (h3 : s2.next ≤ s3.next) : CarryNew D s0 s3 q :=
  let ⟨h1, h2, e, he, hs⟩ := h
  ⟨h1.widen hm h12 h3, h2.widen hm.avoid hm.next h3, e, he,
    hs.imp fun _ hx => hx.widen hm.avoid hm.next h3⟩
/-- A state change keeping the avoided names, the renamings and the carried merges, with a
    counter that does not decrease, is a `WMono` step. -/
theorem WMono.of_eq (ha : s'.avoid = s.avoid) (hn : s.next ≤ s'.next) (hnm : s'.nm = s.nm)
    (hc : s'.carries = s.carries) : WMono D s s' :=
  ⟨ha, hn, fun _ _ h => .inl (hnm ▸ h), fun _ _ h => .inl (hc ▸ h)⟩
/-- `WMono` steps compose. -/
theorem WMono.trans {s0 s1 s2 : WSt P} (h1 : WMono D s0 s1)
    (h2 : WMono D s1 s2) : WMono D s0 s2 where
  avoid := h2.avoid.trans h1.avoid
  next := Nat.le_trans h1.next h2.next
  nm x n h := (h2.nm x n h).elim (fun h => (h1.nm x n h).imp_right (·.up h2.next))
    (.inr <| ·.widen h1.avoid h1.next (Nat.le_refl _))
  carries k q h := (h2.carries k q h).elim
    (fun h => (h1.carries k q h).imp_right
      (·.widen (.of_eq rfl (Nat.le_refl _) rfl rfl) h1.next h2.next))
    (.inr <| ·.widen h1 h2.next (Nat.le_refl _))
/-- A state change keeping the avoided names, the counter, the renamings and the carried merges
    is a `WMono` step. -/
theorem WMono.same
    (h : s'.avoid = s.avoid ∧ s'.next = s.next ∧ s'.nm = s.nm ∧
      s'.carries = s.carries := by exact ⟨rfl, rfl, rfl, rfl⟩) : WMono D s s' := by grind [WMono]
/-- `WMono` holds from a state to itself. -/
theorem WMono.refl (D : List P.Ident) (s : WSt P) : WMono D s s := WMono.same

end

/-! ## The state primitives -/

section
omit iWL

/-- `freshIn` does not decrease the counter. -/
private theorem freshIn_le (s : WSt P) (b : String) : s.next ≤ (freshIn s.avoid b s.next).2 :=
  let ⟨_, hk, hn, _⟩ := freshIn_spec s.avoid b s.next
  hk ▸ Nat.le_succ_of_le hn
/-- The name `freshIn` draws from a state is drawn between it and any state with a counter from
    the new counter on. -/
private theorem freshIn_drawn (s s' : WSt P) (b : String)
    (hn : (freshIn s.avoid b s.next).2 ≤ s'.next) : NewIn s s' (freshIn s.avoid b s.next).1 := by
  obtain ⟨k, hk, hk', hav⟩ := freshIn_spec s.avoid b s.next
  rw [hk] at hn ⊢
  exact ⟨b, k, rfl, hav, hk', hn⟩
/-- A run of `wFresh` is a `WMono` step drawing the name it returns. -/
theorem wFresh_w {b : String}
    (h : (wFresh b).run s = .ok (x, s')) : WMono D s s' ∧ NewIn s s' x := by
  cases (wFresh_run b s).symm.trans h
  exact ⟨.of_eq rfl (freshIn_le s b) rfl rfl, freshIn_drawn _ _ b (Nat.le_refl _)⟩
/-- A run of `wFreshBool` is a `WMono` step drawing the name it returns. -/
theorem wFreshBool_w {b : String}
    (h : (wFreshBool b).run s = .ok (x, s')) : WMono D s s' ∧ NewIn s s' x := by
  cases (wFreshBool_run b s).symm.trans h
  exact ⟨.of_eq rfl (freshIn_le s b) rfl rfl, freshIn_drawn _ _ b (Nat.le_refl _)⟩

end
/-- A run of `wFreshLike` is a `WMono` step drawing the name it returns. -/
theorem wFreshLike_w (h : (wFreshLike y).run s = .ok (x, s')) : WMono D s s' ∧ NewIn s s' x := by
  cases (wFreshLike_run y s).symm.trans h
  exact ⟨.of_eq rfl (freshIn_le s _) rfl rfl, freshIn_drawn _ _ _ (Nat.le_refl _)⟩
/-- A run of `wName x` is a `WMono` step returning the recorded renaming of `x`, `x` itself, or a
    name it draws. -/
theorem wName_w (h : (wName x).run s = .ok (n, s')) :
    WMono D s s' ∧ (s.nm[x]? = some n ∨ n = x ∨ NewIn s s' n) := by
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
  · exact ⟨.refl D _, .inl h1⟩
  · exact ⟨.refl D _, .inr (.inl rfl)⟩
  · refine ⟨⟨rfl, freshIn_le s _, ?_, fun _ _ => .inl⟩, .inr (.inr (freshIn_drawn _ _ _ .refl))⟩
    grind [freshIn_drawn]

/-- A run of `wDecl x` is a `WMono` step returning the recorded renaming of `x`, `x` itself, or a
    name it draws. -/
theorem wDecl_w (h : (wDecl x).run s = .ok (n, s')) :
    WMono D s s' ∧ (s.nm[x]? = some n ∨ n = x ∨ NewIn s s' n) := by
  obtain ⟨n1, s1, h1⟩ := wName_ok x s
  cases (wDecl_run h1).symm.trans h
  obtain ⟨hm, hn⟩ := wName_w (D := D) h1
  exact ⟨⟨hm.avoid, hm.next, fun y m hy => hm.nm y m (by grind), hm.carries⟩, hn⟩
omit iLI iWL in
/-- A run of `liveAdd` is a `WMono` step. -/
theorem liveAdd_w {u : Unit} (h : (liveAdd xs).run s = .ok (u, s')) : WMono D s s' := by
  obtain ⟨live, clock, hr, -⟩ := liveAdd_run xs s
  exact (Prod.mk.inj (Except.ok.inj (hr.symm.trans h))).2 ▸ .same
omit iLI iWL in
/-- A run of `liveDel` is a `WMono` step. -/
theorem liveDel_w {u : Unit} (h : (liveDel x).run s = .ok (u, s')) : WMono D s s' :=
  (Prod.mk.inj (Except.ok.inj ((liveDel_run x s).symm.trans h))).2 ▸ .same
/-- A run of `wRen` is a `WMono` step. -/
theorem wRen_w {e : P.Expr} {p : WExpr P × List P.Ident}
    (h : (wRen e).run s = .ok (p, s')) : WMono D s s' := by
  unfold wRen at h
  obtain ⟨r, s1, hl, ⟨⟩⟩ := wm_run_bind_ok h
  refine wm_forIn_inv (fun _ _ s1 => WMono D s s1) _ (fun S y b s1 b' s2 hI hy => ?_) _ [] _ s _ _
    (.refl D s) hl
  obtain ⟨n, s3, hn, hy⟩ := wm_run_bind_ok hy
  dsimp only at hy
  split at hy <;> cases hy <;> exact ⟨_, rfl, hI.trans (wName_w hn).1⟩


/-- Peels the binds of a successful run `h` of a do-block in order: a pattern `⟨a, s, ha⟩` names
    the result of the step, the state after it and its run; `_` peels a deterministic step
    (`get`, `set` or `modify`); a last step `⟨a, s, ha, hk⟩` also destructs the run `hk` of the
    rest, and a last `rfl` substitutes the result and the state of a final `pure`. -/
scoped syntax "peel " ident (ppSpace colGt rcasesPat)+ : tactic
macro_rules
  | `(tactic| peel $h:ident _) => `(tactic| run_peel $h)
  | `(tactic| peel $h:ident rfl) => do
    let eq := Lean.mkIdent `rfl
    `(tactic| obtain ⟨$eq:ident, $eq:ident⟩ := wm_run_pure_ok $h)
  | `(tactic| peel $h:ident ⟨$a, $b, $c, $d⟩) =>
    `(tactic| obtain ⟨$a, $b, $c, $d⟩ := wm_run_bind_ok $h)
  | `(tactic| peel $h:ident ⟨$ps,*⟩) => `(tactic| obtain ⟨$ps,*, $h:ident⟩ := wm_run_bind_ok $h)
  | `(tactic| peel $h:ident $p $ps*) => `(tactic| (peel $h $p; peel $h $ps*))

/-- Closes the membership of an item in an output built by appends, one-element ropes and folds of
    appends, using the facts `hs` about its parts. -/
scoped macro "out_mem" hs:(ppSpace term:max)* : tactic => `(tactic| simp only [Rope.toList_app,
  Rope.toList_one, Rope.toList_foldl_app, List.flatMap_cons, List.mem_append, List.mem_singleton,
  true_or, or_true, Bool.false_and, Bool.false_eq_true, ite_false, List.mem_cons, $[$hs:term],*])

section
omit iLI iWL

/-- Two states agree on everything but the counter and the declared types: the avoided names,
    the renamings, the names declared later, the live set and its clock, the label depths, the
    carried merges and the dead registrations. -/
private structure LaidSame (s s' : WSt P) : Prop where
  avoid : s'.avoid = s.avoid
  nm : s'.nm = s.nm
  taken : s'.taken = s.taken
  live : s'.live = s.live
  clock : s'.clock = s.clock
  labelDepth : s'.labelDepth = s.labelDepth
  carries : s'.carries = s.carries
  dead : s'.dead = s.dead

/-- `LaidSame` is transitive. -/
private theorem LaidSame.trans {s1 s2 s3 : WSt P} (h1 : LaidSame s1 s2) (h2 : LaidSame s2 s3) :
    LaidSame s1 s3 := by grind [LaidSame]
/-- A run of `wFreshBool` changes only the counter and the declared types. -/
private theorem wFreshBool_laidSame {b : String}
    (h : (wFreshBool b).run s = .ok (x, s')) : LaidSame s s' := by grind [LaidSame, wFreshBool_run]
/-- A run of `wFresh` changes only the counter and the declared types. -/
private theorem wFresh_laidSame {b : String}
    (h : (wFresh b).run s = .ok (x, s')) : LaidSame s s' := by grind [LaidSame, wFresh_run]
include iWL in
/-- A run of `wFreshLike` changes only the counter and the declared types. -/
private theorem wFreshLike_laidSame (h : (wFreshLike y).run s = .ok (x, s')) : LaidSame s s' :=
  by grind [LaidSame, wFreshLike_run]
include iWL in
/-- A run of `saveRestore` changes only the counter and the declared types. -/
private theorem saveRestore_laidSame
    {p : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) × List (P.Ident × P.Ident)}
    (h : (saveRestore xs).run s = .ok (p, s')) : LaidSame s s' := by
  unfold saveRestore at h
  obtain ⟨⟨cp', cps', rs', sv'⟩, s1, hl, ⟨⟩⟩ := wm_run_bind_ok h
  refine wm_forIn_inv (fun _ _ s1 => LaidSame s s1) _ ?_ xs [] _ s _ _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hl
  intro S y _ s1 b' s2 hI hy
  peel hy ⟨a, s3, ⟨⟩⟩ ⟨c, s4, ⟨⟩, ⟨⟩⟩
  exact ⟨_, rfl, hI.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
include iLI in
/-- Names drawn in two counter ranges, the first ending before the second starts, differ. -/
private theorem NewIn.disj {a b c e : WSt P} (h1 : NewIn a b x) (h2 : NewIn c e x)
    (h : b.next ≤ c.next) : False := by
  grind [NewIn, freshName_counter_inj]
include iLI iWL in
/-- A run of `saveRestore xs` does not decrease the counter and, for each variable `x` of `xs`,
    draws a save name and a copy name, all distinct; the saves initialize the save names with the
    variables, the copies initialize the copy names with them, the restores assign the variables
    their save names, and the copy pairs pair the variables with their copy names. -/
private theorem saveRestore_str {sv cp rs : Rope (WItem P)} {cps : List (P.Ident × P.Ident)}
    (h : (saveRestore xs).run s = .ok ((sv, cp, rs, cps), s')) :
    s.next ≤ s'.next ∧ ∃ ps : List (P.Ident × P.Ident × P.Ident), ps.map (·.1) = xs ∧
      sv.toList = ps.map (fun p => WItem.init p.2.1 (.of p.1) (some (.var p.1))) ∧
      cp.toList = ps.map (fun p => WItem.init p.2.2 (.of p.1) (some (.var p.1))) ∧
      rs.toList = ps.map (fun p => WItem.set p.1 (some (.var p.2.1))) ∧
      cps.reverse = ps.map (fun p => (p.1, p.2.2)) ∧
      (ps.map (·.2.1)).Nodup ∧ (∀ p ∈ ps, ∀ q ∈ ps, p.2.2 ≠ q.2.1) ∧
      ∀ p ∈ ps, NewIn s s' p.2.1 ∧ NewIn s s' p.2.2 := by
  unfold saveRestore at h
  obtain ⟨⟨sv1, cp1, rs1, cps1⟩, s1, hl, h⟩ := wm_run_bind_ok h
  cases h
  refine (fun H => ⟨H.1.next, H.2⟩) (wm_forIn_inv (fun S (b : Rope (WItem P) × Rope (WItem P) ×
      Rope (WItem P) × List (P.Ident × P.Ident)) st =>
      WMono [] s st ∧ ∃ ps : List (P.Ident × P.Ident × P.Ident), ps.map (·.1) = S ∧
      b.1.toList = ps.map (fun p => WItem.init p.2.1 (.of p.1) (some (.var p.1))) ∧
      b.2.1.toList = ps.map (fun p => WItem.init p.2.2 (.of p.1) (some (.var p.1))) ∧
      b.2.2.1.toList = ps.map (fun p => WItem.set p.1 (some (.var p.2.1))) ∧
      b.2.2.2.reverse = ps.map (fun p => (p.1, p.2.2)) ∧
      (ps.map (·.2.1)).Nodup ∧ (∀ p ∈ ps, ∀ q ∈ ps, p.2.2 ≠ q.2.1) ∧
      ∀ p ∈ ps, NewIn s st p.2.1 ∧ NewIn s st p.2.2) _ ?_ xs [] _ s _ _
    ⟨WMono.refl [] s, [], rfl, by simp [Rope.toList_nil], by simp [Rope.toList_nil],
      by simp [Rope.toList_nil], rfl, by simp, nofun, nofun⟩ hl)
  intro S y b st b' st' ⟨hm, ps, h1, h2, h3, h4, hc, h5, h6, h7⟩ hb
  peel hb ⟨n1, st1, g1⟩ ⟨n2, st2, g2⟩
  obtain ⟨m1, d1⟩ := wFreshLike_w (D := []) g1
  obtain ⟨m2, d2⟩ := wFreshLike_w (D := []) g2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hb)
  have hw : ∀ n, NewIn s st n → NewIn s st2 n := fun n hn => hn.up (m1.trans m2).next
  have e1 : NewIn s st2 n1 := d1.widen hm.avoid hm.next m2.next
  have e2 : NewIn s st2 n2 := d2.widen (hm.trans m1).avoid (hm.trans m1).next (Nat.le_refl _)
  have o1 : ∀ p ∈ ps, p.2.1 ≠ n1 ∧ p.2.2 ≠ n1 ∧ p.2.1 ≠ n2 := fun p hp =>
    ⟨fun he => (h7 p hp).1.disj (he ▸ d1) (Nat.le_refl _),
      fun he => (h7 p hp).2.disj (he ▸ d1) (Nat.le_refl _),
      fun he => (h7 p hp).1.disj (he ▸ d2) m1.next⟩
  have o2 : n2 ≠ n1 := fun he => d1.disj (he ▸ d2) (Nat.le_refl _)
  refine ⟨_, rfl, hm.trans (m1.trans m2), ps ++ [(y, n1, n2)], by simp [h1], ?_, ?_, ?_,
    by simp [hc], by simpa [List.nodup_append] using ⟨h5, fun _ _ _ hp => (o1 _ hp).1⟩, by grind,
    fun p hp => (List.mem_append.1 hp).elim (fun hp => ⟨hw _ (h7 p hp).1, hw _ (h7 p hp).2⟩)
      fun hp => List.mem_singleton.1 hp ▸ ⟨e1, e2⟩⟩
  all_goals simp [Rope.toList_app, Rope.toList_one, h2, h3, h4]

/-- The items `l` contain an `init` of `y`. -/
@[expose] def InitIn (l : List (WItem P)) (y : P.Ident) : Prop :=
  ∃ ty v, WItem.init y ty v ∈ l

/-- The facts of a run of `saveRestore xs` from `s` to `s'` with saves `sv`, copies `cp`,
    restores `rs` and copy pairs `cps`: a `WMono` step changing only the counter and the declared
    types; the saves and copies are `init`s of names the run draws, the restores assign variables
    of `xs`, and each copy pair pairs a variable of `xs` with a name the run draws and the copies
    initialize. -/
private structure SRFacts (D xs : List P.Ident) (s s' : WSt P) (sv cp rs : Rope (WItem P))
    (cps : List (P.Ident × P.Ident)) : Prop where
  mono : WMono D s s'
  same : LaidSame s s'
  init : ∀ it ∈ sv.toList ++ cp.toList, ∃ n ty v, it = .init n ty v
  drawn : ∀ it ∈ sv.toList ++ cp.toList, ∀ x, it.tgt = some x → NewIn s s' x
  set : ∀ it ∈ rs.toList, ∃ x v, it = .set x v
  rsIn : ∀ it ∈ rs.toList, ∀ x, it.tgt = some x → x ∈ xs
  pairs : ∀ p ∈ cps, p.1 ∈ xs ∧ NewIn s s' p.2
  pairsI : ∀ p ∈ cps, InitIn cp.toList p.2

include iLI iWL in
/-- A run of `saveRestore` has the facts `SRFacts`. -/
private theorem srFacts {sv cp rs : Rope (WItem P)} {cps : List (P.Ident × P.Ident)}
    (h : (saveRestore xs).run s = .ok ((sv, cp, rs, cps), s')) :
    SRFacts D xs s s' sv cp rs cps := by
  have hl := saveRestore_laidSame h
  obtain ⟨hn, ps, hxs, hsv, hcp, hrs, hcps, -, -, hd⟩ := saveRestore_str h
  have hc : ∀ p ∈ cps, ∃ q ∈ ps, (q.1, q.2.2) = p := fun p hp =>
    List.mem_map.1 (hcps ▸ List.mem_reverse.2 hp)
  refine ⟨.of_eq hl.avoid hn hl.nm hl.carries, hl, ?_, ?_, ?_, ?_, fun p hp => ?_, fun p hp => ?_⟩
  all_goals try simp only [hsv, hcp, hrs, List.mem_append, List.mem_map]
  all_goals try grind [WItem.tgt]
  obtain ⟨q, hq, rfl⟩ := hc p hp
  exact ⟨_, _, List.mem_map_of_mem hq⟩

omit iDE iBE iLB iHB iHF iSF iHI iHa iHFs in
/-- The items of `setReach κ X` assign the reach variable of `κ`. -/
theorem setReach_tgt (κ : RE P) (X : WExpr P) :
    ∀ it ∈ (setReach κ X).toList, ∀ x, it.tgt = some x → κ.wvar = some x := by
  cases κ <;> simp [setReach, Rope.toList_one, Rope.toList_nil, WItem.tgt, RE.wvar]

/-- The name `wName x` or `wDecl x` returns at `s1` (a recorded renaming, `x` itself, or a name
    drawn up to `s2`) may be assigned by a walk from `s` on of a fragment with identifier `x`. -/
theorem Wr0.of_name {s1 s2 : WSt P} (hm : WMono D s s1)
    (hn : s1.nm[x]? = some n ∨ n = x ∨ NewIn s1 s2 n) (hx : x ∈ D) (h12 : s1.next ≤ s2.next)
    (h2 : s2.next ≤ s'.next) : Wr0 D s s' n := by
  rcases hn with hn | rfl | hn
  · exact (hm.nm x n hn).elim (fun h => .inr (.inl ⟨x, h⟩)) (.inl <| ·.up (Nat.le_trans h12 h2))
  · exact .inr (.inr hx)
  · exact .inl (hn.widen hm.avoid hm.next h2)
/-- The empty result of a walk that keeps the state has the write facts. -/
theorem WalkW.empty (D : List P.Ident) (κ : RE P) (s : WSt P) : WalkW D κ s s {} :=
  ⟨.refl D s, by simp [Rope.toList_nil], by simp, by simp [Rope.toList_nil]⟩
/-- A walk step with an empty output, no assigned names and no registrations has the write
    facts. -/
theorem WalkW.of_nil (hm : WMono D s s') (ho : r.out = .nil) (hA : r.A = {}) (hr : r.regs = .nil) :
    WalkW D κ s s' r :=
  ⟨hm, by simp [ho, Rope.toList_nil], by simp [hA], by simp [hr, Rope.toList_nil]⟩
/-- The write facts of a walk from `s1` to `s2` hold for any wider pair of `WMono` steps. -/
theorem WalkW.widen {s0 s1 s2 s3 : WSt P} {a : WRes P} (h : WalkW D κ s1 s2 a) (h0 : WMono D s0 s1)
    (h3 : WMono D s2 s3) : WalkW D κ s0 s3 a where
  toWMono := h0.trans (h.toWMono.trans h3)
  out it hit x hx := (h.out it hit x hx).imp_left (·.widen h0 h.next h3.next)
  A x hx := (h.A x hx).widen h0 h.next h3.next
  regs e he := (h.regs e he).widen h0.avoid h0.next h3.next

end

/-- Splits on the obligation bit `f` of a command walk `h`: closes `f = false` (an empty result
    and an unchanged state) and unfolds the walk at `f = true`. -/
local macro "walk_on " f:ident h:ident : tactic => do
  let eq := Lean.mkIdent `rfl
  `(tactic| (
  cases $f:ident
  · simp only [wpStmt, Bool.not_false, ↓reduceIte] at $h:ident
    obtain ⟨$eq:ident, $eq:ident⟩ := wm_run_pure_ok $h
    exact WalkW.empty _ _ _
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at $h:ident))

/-- The walk of an `init` has the write facts. -/
private theorem init_w {f : Bool} {ty : P.Ty} {e : ExprOrNondet P} {md : MetaData P}
    (h : (wpStmt κ d f (.cmd (.cmd (.init x ty e md)))).run s = .ok (r, s'))
    (hD : x ∈ D) : WalkW D κ s s' r := by
  cases e
  case' det =>
    walk_on f h
    peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨n, s2, h2⟩ _
    have hm1 := wRen_w (D := D) h1
    obtain ⟨hm2, hn⟩ := wDecl_w (D := D) h2
    split at h
    case' h_1 =>
      peel h ⟨_, s5, h5⟩ ⟨_, s6, h6, ⟨⟩⟩
      have hmt : WMono D s2 s' := (WMono.same).trans ((liveDel_w h5).trans (liveAdd_w h6))
    case' h_2 =>
      peel h ⟨xd, s4, h4⟩ _ ⟨_, s5, h5⟩ ⟨_, s6, h6, ⟨⟩⟩
      obtain ⟨hm4, hx⟩ := wFresh_w (D := D) h4
      have hm5 : WMono D s4 s' := (WMono.same).trans ((liveDel_w h5).trans (liveAdd_w h6))
      have hmt : WMono D s2 s' := (WMono.same).trans (hm4.trans hm5)
      have hx' : Wr0 D s s' xd :=
        .inl (hx.widen (hm1.trans hm2).avoid (hm1.trans hm2).next hm5.next)
  case' nondet =>
    walk_on f h
    peel h ⟨n, s2, h2⟩ _ ⟨_, s4, h4, ⟨⟩⟩
    obtain ⟨hm2, hn⟩ := wDecl_w (D := D) h2
    have hm1 := WMono.refl D s
    have hmt : WMono D s2 s' := (WMono.same).trans (liveDel_w h4)
  all_goals
    have hn' := Wr0.of_name hm1 hn hD hm2.next hmt.next
    exact ⟨(hm1.trans hm2).trans hmt,
      by grind [Rope.toList_app, Rope.toList_one, WItem.tgt], by simp,
      by simp [Rope.toList_nil]⟩

omit iDE iHB iHF iSF iHI iLI iHFs iWL in
/-- The one-element hash set contains only its element. -/
private theorem contains_one (h : (Std.HashSet.ofList [n]).contains y = true) :
    y = n := (by simpa using h : n = y).symm
/-- The walk of a deterministic `set` has the write facts. -/
private theorem set_det_w {f : Bool} {e : P.Expr} {md : MetaData P}
    (h : (wpStmt κ d f (.cmd (.cmd (.set x (.det e) md)))).run s = .ok (r, s'))
    (hD : x ∈ D) : WalkW D κ s s' r := by
  walk_on f h
  peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨n, s2, h2⟩
  have hm1 := wRen_w (D := D) h1
  obtain ⟨hm2, hn⟩ := wName_w (D := D) h2
  split at h <;>
  · obtain ⟨_, s3, h3, h⟩ := wm_run_bind_ok h
    obtain ⟨_, s4, h4, ⟨⟩⟩ := wm_run_bind_ok h
    have hm3 : WMono D s2 s3 := by first | exact liveDel_w h3 | exact liveAdd_w h3
    have hw := Wr0.of_name hm1 hn hD hm2.next (hm3.trans (liveAdd_w h4)).next
    exact ⟨hm1.trans (hm2.trans (hm3.trans (liveAdd_w h4))), by grind [Rope.toList_one, WItem.tgt],
      fun y hy => contains_one hy ▸ hw, by simp [Rope.toList_nil]⟩
/-- The walk of a nondeterministic `set` has the write facts. -/
private theorem set_nondet_w {f : Bool} {md : MetaData P}
    (h : (wpStmt κ d f (.cmd (.cmd (.set x .nondet md)))).run s = .ok (r, s'))
    (hD : x ∈ D) : WalkW D κ s s' r := by
  walk_on f h
  peel h ⟨n, s2, h2⟩ ⟨xh, s3, h3⟩
  obtain ⟨hm2, hn⟩ := wName_w (D := D) h2
  obtain ⟨hm3, hx⟩ := wFreshLike_w (D := D) h3
  split at h <;>
  · obtain ⟨_, s4, h4, ⟨⟩⟩ := wm_run_bind_ok h
    have hm4 : WMono D s3 s' := by first | exact liveDel_w h4 | exact liveAdd_w h4
    have hw := Wr0.of_name (.refl D s) hn hD hm2.next (hm3.trans hm4).next
    have hx' : Wr0 D s s' xh := .inl (hx.widen hm2.avoid hm2.next hm4.next)
    exact ⟨hm2.trans (hm3.trans hm4), by grind [Rope.toList_app, Rope.toList_one, WItem.tgt],
      fun y hy => contains_one hy ▸ hw, by simp [Rope.toList_nil]⟩
/-- A walk step made of a renaming of an expression and an insertion into the live set,
    returning an output without assignments, has the write facts. -/
private theorem ren_live_w {e : P.Expr} {g : WExpr P × List P.Ident → WRes P}
    (hg : ∀ p, (∀ it ∈ (g p).out.toList, it.tgt = none) ∧ (g p).A = {} ∧ (g p).regs = .nil)
    (h : (do let p ← wRen e; liveAdd (p.2 ++ xs); pure (g p) : WM P (WRes P)).run s = .ok (r, s')) :
    WalkW D κ s s' r := by
  peel h ⟨p, s1, h1⟩ ⟨_, s2, h2, ⟨⟩⟩
  obtain ⟨ho, hA, hr⟩ := hg p
  exact ⟨(wRen_w h1).trans (liveAdd_w h2), fun it hit y hy => by simp [ho it hit] at hy,
    fun y hy => by simp [hA] at hy, by simp [hr, Rope.toList_nil]⟩
omit iLI in
/-- The walk of an `exit` to a label of depth `t` under a variable context: without an
    obligation following it, an exit result; with one, it also draws the reach copy `e` of the
    context, records it as pending for the label and adds the context's variables to the live
    set.  The walk of an exit to a label outside the region keeps the state. -/
private theorem exit_inv (hκ : κ ≠ .top) {f : Bool} {l : String} {md : MetaData P}
    (h : (wpStmt κ d f (.exit l md)).run s = .ok (r, s')) :
    (∃ t, s.labelDepth[l]? = some t ∧
      ((f = false ∧ s' = s ∧ r = { ax := true, minT := some t, tgt := .single t }) ∨
      (f = true ∧ ∃ e s2, (wFreshBool "r").run s = .ok (e, s2) ∧
        (liveAdd (RE.vars κ)).run
          { s2 with pending := s2.pending.insert l (e :: s2.pending.getD l []) } = .ok ((), s') ∧
        r = { out := Rope.app (.one (.init e (.known HasBool.boolTy) (some (kExpr κ))))
                (setReach κ (.lit false))
              ax := true, minT := some t, tgt := .single t, regs := .one e }))) ∨
    (s.labelDepth[l]? = none ∧ s' = s ∧ ((f = false ∧ r = { ax := true, minT := some 0 }) ∨
      (f = true ∧ r = { out := setReach κ (.lit false), ax := true, minT := some 0 }))) := by
  simp only [wpStmt] at h
  run_peel h
  cases ht : s.labelDepth[l]? <;> cases f <;>
    simp only [ht, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true] at h
  all_goals try obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
  · exact .inr ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩
  · exact .inr ⟨rfl, rfl, .inr ⟨rfl, rfl⟩⟩
  · exact .inl ⟨_, rfl, .inl ⟨rfl, rfl, rfl⟩⟩
  · exact .inl ⟨_, rfl, .inr ⟨rfl, _, _, rfl, rfl, rfl⟩⟩
/-- The walk of an `exit` has the write facts. -/
private theorem exit_w {f : Bool} {l : String} {md : MetaData P}
    (h : (wpStmt κ d f (.exit l md)).run s = .ok (r, s')) : WalkW D κ s s' r := by
  rcases Classical.em (κ = .top) with rfl | hκ
  · unfold wpStmt at h
    obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
    exact WalkW.of_nil (WMono.same) rfl rfl rfl
  rcases exit_inv hκ h with
    ⟨t, -, ⟨-, rfl, rfl⟩ | ⟨-, e, s2, h2, h4, rfl⟩⟩ | ⟨-, rfl, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
  · exact WalkW.of_nil (WMono.refl D _) rfl rfl rfl
  · obtain ⟨m2, hd2⟩ := wFreshBool_w (D := D) h2
    have m4 : WMono D s2 s' := (WMono.same).trans (liveAdd_w h4)
    have hd := hd2.widen rfl (Nat.le_refl _) m4.next
    exact ⟨m2.trans m4, by grind [Rope.toList_app, Rope.toList_one, WItem.tgt, Wr0, setReach_tgt],
      by simp, by grind [Rope.toList_one]⟩
  · exact WalkW.of_nil (WMono.refl D _) rfl rfl rfl
  · exact ⟨WMono.refl D _, fun it hit y hy => .inr (setReach_tgt _ _ it hit y hy), by simp,
      by simp [Rope.toList_nil]⟩

/-- An element of a rope that is empty under a condition is an element of the other rope. -/
private theorem mem_ite_nil {α : Type} {c : Prop} [Decidable c] {a : α} {X : Rope α}
    (h : a ∈ (if c then Rope.nil else X).toList) : a ∈ X.toList := by
  split at h <;> simp_all [Rope.toList_nil]
/-- An element of a rope that is empty unless a condition holds is an element of the other
    rope. -/
private theorem mem_ite_nil' {α : Type} {c : Prop} [Decidable c] {a : α} {X : Rope α}
    (h : a ∈ (if c then X else Rope.nil).toList) : a ∈ X.toList := by
  split at h <;> simp_all [Rope.toList_nil]
omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL in
/-- An item of the items `f x` of the elements `x` of a list, appended one by one to `acc`, is an
    item of `acc` or the item of an element of the list. -/
private theorem mem_sets {α : Type} {f : α → WItem P} {it : WItem P} :
    ∀ (L : List α) (acc : Rope (WItem P)),
      it ∈ (L.foldl (fun acc x => acc.app (Rope.one (f x))) acc).toList →
      it ∈ acc.toList ∨ ∃ p ∈ L, it = f p :=
  fun L => by induction L <;> grind [Rope.toList_app, Rope.toList_one]

omit iDE iHB iHF iSF iHI iLI iHFs iWL in
/-- A name is in a set after inserting the variables of a list of carried merges exactly when it
    is in the set or the variable of an entry of the list. -/
private theorem mem_insert_merges :
    ∀ (L : List (P.Ident × WExpr P × P.Ident)) (A : Std.HashSet P.Ident),
      (L.foldl (fun s x => s.insert x.1) A).contains y = true ↔
      A.contains y = true ∨ ∃ q ∈ L, q.1 = y :=
  fun L => by induction L <;> grind

omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iWL in
/-- A local a statement puts in scope occurs in the statement. -/
theorem mem_idents_of_topInit {s : PStmt P} (h : x ∈ Stmt.topInits s) :
    x ∈ Stmt.idents s := by
  rcases s with ⟨⟨_, _, _ | _, _⟩ | _⟩ | _ <;> simp_all [Stmt.topInits, Stmt.idents]
/-- An element of a one-element rope is its element. -/
private theorem Rope.mem_one {α : Type} {a b : α} (h : a ∈ (Rope.one b).toList) : a = b := by
  simpa [Rope.toList_one] using h
/-- An element of an appended rope is an element of one of its two parts. -/
private theorem Rope.mem_app {α : Type} {a : α} {x y : Rope α} :
    a ∈ (x.app y).toList ↔ a ∈ x.toList ∨ a ∈ y.toList := by simp [Rope.toList_app]
omit iLI in
/-- The walk of a block under a variable context walks its body under the same context from the
    state entering the block (`s0`), restores the label's depth and pending exits, drops the
    carried merges of the body's depth, adds the context's variables to the live set, and
    returns the body's output followed by the carried merges and the join of its exits. -/
private theorem block_inv (hκ : κ ≠ .top) {f : Bool} {l : String} {body : PStmts P}
    {md : MetaData P} (h : (wpStmt κ d f (.block l body md)).run s = .ok (r, s')) :
    ∃ s0 B s4, s0 = { s with
        pending := s.pending.insert l []
        labelDepth := s.labelDepth.insert l (d + 1)
        stampAt := s.stampAt.insert (d + 1) s.clock
        carries := s.carries.insert (d + 1) [] } ∧
      (wpList κ (d + 1) f body).run s0 = .ok (B, s4) ∧
      (liveAdd (RE.vars κ)).run { s4 with
        pending := match s.pending[l]? with
          | some v => s4.pending.insert l v
          | none => s4.pending.erase l
        labelDepth := match s.labelDepth[l]? with
          | some v => s4.labelDepth.insert l v
          | none => s4.labelDepth.erase l
        carries := s4.carries.erase (d + 1) } = .ok ((), s') ∧
      r = { out := (B.out.app (((s4.carries.getD (d + 1) []).filter
              fun x => !s4.dead.contains x.2.2).foldl
              (fun acc x => acc.app (Rope.one (WItem.set x.1 (some x.2.1)))) Rope.nil)).app
              (if (!f) = true then Rope.nil
              else if ((s4.pending.getD l []).filter fun e => !s4.dead.contains e).reverse.isEmpty
              then Rope.nil
              else setReach κ (disjW (kExpr κ :: (((s4.pending.getD l []).filter
                fun e => !s4.dead.contains e).reverse.map WExpr.var))))
            sk := [.block B.sk], hasObl := B.hasObl, R := B.R, regs := B.regs
            minT := if leOpt B.minT d = true then B.minT else none
            A := ((s4.carries.getD (d + 1) []).filter fun x => !s4.dead.contains x.2.2).foldl
              (fun s x => s.insert x.1) B.A
            ax := B.ax &&
              ((s4.pending.getD l []).filter fun e => !s4.dead.contains e).reverse.isEmpty
            tgt := B.tgt.popEq (d + 1) } := by
  simp only [wpStmt] at h
  iterate 2 run_peel h
  simp only [pure_bind] at h
  peel h ⟨B, s4, hB⟩ _ _ ⟨_, s5, h5, ⟨⟩⟩
  exact ⟨_, B, s4, rfl, hB, h5, rfl⟩
/-- The walk of a block has the write facts when the walks of its body do. -/
private theorem block_w {f : Bool} {l : String} {body : PStmts P} {md : MetaData P}
    (hB : ∀ κB {s0 B s1}, (wpList κB (d + 1) f body).run s0 = .ok (B, s1) → WalkW D κB s0 s1 B)
    (h : (wpStmt κ d f (.block l body md)).run s = .ok (r, s')) : WalkW D κ s s' r := by
  rcases Classical.em (κ = .top) with rfl | hκ
  case' inl =>
    simp only [wpStmt] at h
    peel h _ _ ⟨rr, sB, h1⟩
    simp only [pure_bind] at h
    peel h ⟨B, s4, hB4⟩ _ _ ⟨_, s5, h5, ⟨⟩⟩
    have WB := hB (.name rr) hB4
    obtain ⟨hm1, hr⟩ := wFreshBool_w (D := D) h1
    have hm0 : WMono D s sB := .trans (by exact ⟨rfl, Nat.le_refl _, fun _ _ => .inl,
      fun k q hq => .inl (List.mem_ite_nil_left.1 (by rwa [Std.HashMap.getD_insert] at hq)).2⟩) hm1
    have hc0 : sB.carries.getD (d + 1) [] = [] := by simp [(wFreshBool_laidSame h1).carries]
  case' inr =>
    obtain ⟨sB, B, s4, hs0, hB4, h5, rfl⟩ := block_inv hκ h
    have WB := hB κ hB4
    have hm0 : WMono D s sB :=
      hs0 ▸ ⟨rfl, Nat.le_refl _, fun _ _ => .inl,
        fun k q hq => .inl (List.mem_ite_nil_left.1 (by rwa [Std.HashMap.getD_insert] at hq)).2⟩
    have hc0 : sB.carries.getD (d + 1) [] = [] := by simp [hs0]
  all_goals
    have hm5 : WMono D s4 s' := .trans (by exact ⟨rfl, Nat.le_refl _, fun _ _ => .inl,
      fun k q hq => .inl (List.mem_ite_nil_left.1 (by rwa [Std.HashMap.getD_erase] at hq)).2⟩)
      (liveAdd_w h5)
    have W := WB.widen hm0 hm5
    have hq : ∀ q ∈ (s4.carries.getD (d + 1) []).filter (fun x => !s4.dead.contains x.2.2),
        Wr0 D s s' q.1 := fun q hq => ((WB.carries (d + 1) q (List.mem_filter.1 hq).1).resolve_left
      (by simp [hc0])).1.widen hm0 WB.next hm5.next
    refine ⟨W.toWMono, fun it hit y hy => ?_,
      fun y hy => ((mem_insert_merges _ _).1 hy).elim (W.A y) fun ⟨q, hq', e⟩ => e ▸ hq q hq',
      W.regs⟩
  · rcases (Rope.mem_app.1 hit).imp_left Rope.mem_app.1 with (hit | hit) | hit
    · exact W.out it hit y hy
    · obtain ⟨q, hq', rfl⟩ := (mem_sets _ _ hit).resolve_left (by simp [Rope.toList_nil])
      exact Option.some.inj hy ▸ .inl (hq q hq')
    · exact .inr (setReach_tgt κ _ it (mem_ite_nil (mem_ite_nil hit)) y hy)
  · have hrw : Wr0 D s s' rr := .inl (hr.widen rfl (Nat.le_refl _) (Nat.le_trans WB.next hm5.next))
    have hit := mem_ite_nil hit
    simp only [Rope.toList_app, Rope.toList_one, List.mem_append, List.mem_singleton] at hit
    rcases hit with rfl | ((hit | hit) | hit)
    · exact Option.some.inj hy ▸ .inl hrw
    · exact (W.out it hit y hy).elim .inl fun h => Option.some.inj h ▸ .inl hrw
    · obtain ⟨q, hq', rfl⟩ := (mem_sets _ _ hit).resolve_left (by simp [Rope.toList_nil])
      exact Option.some.inj hy ▸ .inl (hq q hq')
    · cases Rope.mem_one (mem_ite_nil' (mem_ite_nil hit))
      cases hy
omit iDE iHB iHF iSF iHI iLI iHFs iWL in
/-- A name of a union of two hash sets is exactly a name of one of them. -/
private theorem unionSet_iff {a b : Std.HashSet P.Ident} :
    (unionSet a b).contains y = true ↔ a.contains y = true ∨ b.contains y = true := by
  rw [unionSet_contains, Bool.or_eq_true]
/-- The walk of a real branch has the write facts when the walks of its arms do. -/
private theorem real_w {c : P.Expr} {tss ess : PStmts P}
    (hT : ∀ {s0 R s1}, (wpList .top d false tss).run s0 = .ok (R, s1) → WalkW D .top s0 s1 R)
    (hE : ∀ {s0 R s1}, (wpList .top d false ess).run s0 = .ok (R, s1) → WalkW D .top s0 s1 R)
    (h : (wpIteReal κ d c tss ess).run s = .ok (r, s')) : WalkW D κ s s' r := by
  unfold wpIteReal at h
  peel h _ _ ⟨E, s1, h1⟩ _ _ ⟨T, s3, h3⟩ _ _
  have WE := hE h1
  have WT := hT h3
  have hm3 : WMono D s s3 :=
    .trans (by exact .same) (WE.toWMono.trans (.trans (by exact .same) WT.toWMono))
  split at h
  · obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
    exact .of_nil (hm3.trans .same) rfl rfl rfl
  peel h ⟨⟨wc, rdc⟩, s5, h5⟩ ⟨g, s6, h6⟩ ⟨_, s7, h7, ⟨⟩⟩
  obtain ⟨hm6, hg⟩ := wFreshBool_w (D := D) h6
  have hm4 : WMono D s3 s5 := .trans (by exact .same) (wRen_w h5)
  have hm7 := hm6.trans (liveAdd_w h7)
  have WE' := WE.widen (by exact .same) (.trans (by exact .same) (WT.toWMono.trans (hm4.trans hm7)))
  have WT' := WT.widen (.trans (by exact .same) (WE.toWMono.trans (by exact .same))) (hm4.trans hm7)
  refine ⟨hm3.trans (hm4.trans hm7), fun it hit y hy => ?_, fun y hy => ?_, fun e he => ?_⟩
  · have hg' : Wr0 D s s' g :=
      .inl (hg.widen (hm3.trans hm4).avoid (hm3.trans hm4).next (liveAdd_w (D := D) h7).next)
    dsimp only at hit
    split at hit <;> (try split at hit) <;>
      simp only [Rope.toList_app, Rope.toList_one, List.mem_append, List.mem_singleton] at hit
    · rcases hit with rfl | rfl <;> first | exact Option.some.inj hy ▸ .inl hg' | cases hy
    all_goals rcases hit with (rfl | rfl) | hit
    all_goals first
      | (cases hy; done)
      | (cases hy; exact .inl hg')
      | exact .inl ((WT'.out it hit y hy).resolve_right nofun)
      | exact .inl ((WE'.out it hit y hy).resolve_right nofun)
  · exact (unionSet_iff.1 hy).elim (WT'.A y) (WE'.A y)
  · exact (Rope.mem_app.1 he).elim (WT'.regs e) (WE'.regs e)
omit iDE iHB iHF iSF iHI iLI iHFs iWL in
/-- An element of `interSet a b` is in `a`. -/
private theorem mem_interSet_left {a b : Std.HashSet P.Ident}
    (h : y ∈ interSet a b) : a.contains y = true := by
  simp only [interSet, Std.HashSet.fold_eq_foldl_toList, ← List.foldl_filter] at h
  split at h <;> simp_all
omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL in
/-- The negation of a selector over names satisfying `p` is one. -/
private theorem SelOK.not {p : P.Ident → Prop} {a : WExpr P} (h : SelOK p a) :
    SelOK p a.not := by
  cases a <;> first | trivial | exact ⟨h, trivial, trivial⟩
omit iLI iWL in
/-- A step from `s1` to `s2` that keeps the avoided names, the counter and the renamings of `s1`
    and registers only carried merges registered by a walk from `s` to `s2`, after a `WMono`
    step from `s` to `s1`, is a `WMono` step from `s`. -/
private theorem WMono.carry {s1 s2 : WSt P} (h : WMono D s s1) (ha : s2.avoid = s1.avoid)
    (hn : s2.next = s1.next) (hnm : s2.nm = s1.nm)
    (hc : ∀ k q, q ∈ s2.carries.getD k [] → q ∈ s1.carries.getD k [] ∨ CarryNew D s s2 q) :
    WMono D s s2 :=
  ⟨ha.trans h.avoid, hn ▸ h.next,
    fun x n hx => (h.nm x n (hnm ▸ hx)).imp_right
      (·.widen rfl (Nat.le_refl _) (Nat.le_of_eq hn.symm)),
    fun k q hq => (hc k q hq).elim (fun h' => (h.carries k q h').imp_right
      (·.widen (WMono.refl D s) h.next (Nat.le_of_eq hn.symm))) .inr⟩

omit iWL in
/-- An optional draw is a `WMono` step changing only the counter and the declared types, and
    draws the name it returns, keeping well-formedness. -/
private theorem OptDraw.w {b : String} {o : Option P.Ident}
    (h : OptDraw b s s' o) : WMono D s s' ∧ LaidSame s s' ∧ (∀ x, o = some x → NewIn s s' x) ∧
      (WFSt s → WFSt s') := by
  cases o with
  | none => exact (h : s' = s) ▸ ⟨.refl D _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, nofun, id⟩
  | some x =>
    exact ⟨(wFreshBool_w h).1, wFreshBool_laidSame h,
      fun _ hx => Option.some.inj hx ▸ (wFreshBool_w (D := D) h).2,
      fun hw => (wFreshBool_walk h).wf hw nofun⟩
omit iLI iWL in
/-- The else-arm context of a laid-out `ite` is drawn as `rE`, is not `top`, reads only the
    guard, the variables of `κ` and `rE`, and assigns only the guard or `rE`. -/
private theorem LaidElseCtx.facts {κE : RE P} {g : P.Ident} {s3 s4 : WSt P} {rE : Option P.Ident}
    (h : LaidElseCtx κ g s3 κE rE s4) : OptDraw "r" s3 s4 rE ∧ κE ≠ .top ∧
      (∀ y ∈ RE.vars κE, y = g ∨ y ∈ RE.vars κ ∨ rE = some y) ∧
      ∀ y, κE.wvar = some y → y = g ∨ rE = some y := by
  grind [LaidElseCtx, OptDraw, RE.vars, RE.wvar]
omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL in
/-- A carried merge after `carryIns` is one before or the merge of a copy pair of `cps`. -/
private theorem mem_carryIns {e : WExpr P} {cps : List (P.Ident × P.Ident)}
    {C : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))} {o : Option Nat} {k : Nat}
    {q : P.Ident × WExpr P × P.Ident} (hq : q ∈ (carryIns e cps C o).getD k []) :
    q ∈ C.getD k [] ∨ ∃ p ∈ cps, q = (p.1, e.ite (.var p.2) (.var p.1), p.2) := by
  obtain ⟨new, he, hn⟩ := carryIns_getD e cps C o k
  rw [he, List.mem_append] at hq
  exact hq.symm.imp_right fun h => (hn q h).2
/-- The walk of a laid-out `ite` has the write facts when the walks of its arms do. -/
private theorem laid_w {c : P.Expr} {tss ess : PStmts P}
    (hT : ∀ κ' {s0 R s1}, (wpList κ' d true tss).run s0 = .ok (R, s1) → WalkW D κ' s0 s1 R)
    (hE : ∀ κ' {s0 R s1}, (wpList κ' d true ess).run s0 = .ok (R, s1) → WalkW D κ' s0 s1 R)
    (h : (wpIteLaid κ d c tss ess).run s = .ok (r, s')) : WalkW D κ s s' r := by
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hctx h5 h6 h7 h8 h9 hgm _ hqm _
    hrm _ hend => ?_
  have WE := hE κE h5
  have WT := hT (.name rT) h6
  obtain ⟨hctx4, hκE, hvE, hwE⟩ := hctx.facts
  obtain ⟨hm4, -, hrE, -⟩ := OptDraw.w (D := D) hctx4
  obtain ⟨hm2, hg⟩ := wFreshBool_w (D := D) h2
  obtain ⟨hm3, hrT⟩ := wFreshBool_w (D := D) h3
  obtain ⟨hm7, -, -, hd7, -, hr7, hp7, -⟩ := srFacts (D := D) h7
  obtain ⟨hm8, -, -, hd8, -, hr8, hp8, -⟩ := srFacts (D := D) h8
  obtain ⟨hm9, -, -, hd9, -, hr9, hp9, -⟩ := srFacts (D := D) h9
  obtain ⟨hm10, -, hgm', -⟩ := OptDraw.w (D := D) hgm
  obtain ⟨hm11, -, hqm', -⟩ := OptDraw.w (D := D) hqm
  obtain ⟨hm12, -, hrm', -⟩ := OptDraw.w (D := D) hrm
  have p1 := wRen_w (D := D) h1
  have p2 := p1.trans hm2
  have p3 := p2.trans hm3
  have p4 := p3.trans hm4
  have p5 := p4.trans WE.toWMono
  have p6 := p5.trans WT.toWMono
  have p7 := p6.trans hm7
  have p8 := p7.trans hm8
  have p9 := p8.trans hm9
  have p10 := p9.trans hm10
  have p11 := p10.trans hm11
  have q10 := hm11.trans hm12
  have q9 := hm10.trans q10
  have q8 := hm9.trans q9
  have q7 := hm8.trans q8
  have q6 := hm7.trans q7
  have q5 := WT.toWMono.trans q6
  have q4 := WE.toWMono.trans q5
  have q3 := hm4.trans q4
  have L : ∀ {a b : WSt P} {x : P.Ident}, WMono D s a → WMono D b s12 → NewIn a b x →
      NewIn s s12 x := fun ha hb hx => hx.widen ha.avoid ha.next hb.next
  have WE12 := WE.widen p4 q5
  have WT12 := WT.widen p5 q6
  have hM : ∀ x ∈ (if T.ax then [] else interSet T.A E.R), Wr0 D s s12 x :=
    fun x hx => WT12.A x (mem_interSet_left (List.mem_ite_nil_left.1 hx).2)
  have hCT : ∀ x ∈ (if T.ax then T.A.fold (fun l x =>
      if liveBefore s6 x s4.clock || E.R.contains x then x :: l else l) [] else []),
      Wr0 D s s12 x := fun x hx => WT12.A x (fold_filter_mem hx)
  have hCE : ∀ x ∈ (if E.ax then
      E.A.fold (fun l x => if liveBefore s6 x s4.clock then x :: l else l) [] else []),
      Wr0 D s s12 x := fun x hx => WE12.A x (fold_filter_mem hx)
  have hgm12 : SelOK (NewIn s s12) (optVar gm) := by
    cases gm <;> first | exact L p9 q10 (hgm' _ rfl) | trivial
  have hsel : SelOK (NewIn s s12) (elseGuard κ gm qm rEm) := by
    unfold elseGuard
    split
    · exact SelOK.not hgm12
    · exact ⟨L p10 hm12 (hqm' _ rfl), SelOK.not hgm12, trivial⟩
    · exact L p11 (.refl D _) (hrm' _ rfl)
    · trivial
  have hc : ∀ k q, q ∈ (carryIns (elseGuard κ gm qm rEm) (carryOf s6 cpsE E.tgt.max?)
      (carryIns (optVar gm) (carryOf s6 cpsT T.tgt.max?) s12.carries T.tgt.max?)
      E.tgt.max?).getD k [] → q ∈ s12.carries.getD k [] ∨ CarryNew D s s12 q := fun k q hq => by
    rcases mem_carryIns hq with hq | ⟨p, hp, rfl⟩
    · rcases mem_carryIns hq with hq | ⟨p, hp, rfl⟩
      · exact .inl hq
      · obtain ⟨hp1, hp2⟩ := hp8 p (carryOf_sub hp)
        exact .inr ⟨hCT _ hp1, L p7 q8 hp2, _, rfl, hgm12⟩
    · obtain ⟨hp1, hp2⟩ := hp9 p (carryOf_sub hp)
      exact .inr ⟨hCE _ hp1, L p8 q9 hp2, _, rfl, hsel⟩
  have hregs : ∀ e ∈ r.regs.toList, NewIn s s12 e := by
    rcases hend with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> intro e he <;>
      simp only [Rope.toList_app, Rope.toList_ofList, List.mem_append, List.mem_map] at he <;>
      rcases he with (he | he) | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    all_goals first
      | exact WT12.regs e he
      | exact WE12.regs e he
      | exact L p7 q8 (hp8 p (carryOf_sub hp)).2
      | exact L p8 q9 (hp9 p (carryOf_sub hp)).2
  have p12 := p11.trans hm12
  rcases hend with ⟨-, rfl, rfl⟩ | ⟨hb, h13, rfl⟩
  · exact ⟨WMono.carry p12 rfl rfl rfl hc, by simp [Rope.toList_nil], by simp, hregs⟩
  have hn := (liveAdd_w (D := D) h13).next
  refine ⟨.trans (by exact WMono.carry p12 rfl rfl rfl hc) (liveAdd_w h13), fun it hit y hy => ?_,
    fun y hy => ?_, fun e he => (hregs e he).up hn⟩
  · have W' : ∀ x, Wr0 D s s12 x → Wr0 D s s' x := fun x h => h.widen (.refl D s) p12.next hn
    have DW : ∀ x, NewIn s s12 x → Wr0 D s s' x ∨ κ.wvar = some x :=
      fun x h => .inl (.inl (h.up hn))
    have I1 : ∀ {it z ty v y}, it ∈ (Rope.one (WItem.init z ty v)).toList → it.tgt = some y →
        NewIn s s12 z → Wr0 D s s' y ∨ κ.wvar = some y := fun hit hy hz =>
      Option.some.inj ((congrArg WItem.tgt (Rope.mem_one hit)).symm.trans hy) ▸ DW _ hz
    have N : ∀ {it : WItem P}, it ∉ (Rope.nil : Rope (WItem P)).toList := by simp [Rope.toList_nil]
    simp only [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
      List.nil_append, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hit
    rcases hit with rfl | ⟨X, hX | hX | hX | hX | hX | hX | hX | hX | hX | hX | hX | hX | hX | hX |
      hX | hX | hX | hX, hit⟩ <;> try subst hX
    · exact Option.some.inj hy ▸ DW _ (L p1 (hm3.trans q3) hg)
    · exact I1 (mem_ite_nil hit) hy (L p2 q3 hrT)
    · cases gm <;> first | exact I1 hit hy (L p9 q10 (hgm' _ rfl)) | exact (N hit).elim
    · split at hit <;> first | exact I1 hit hy (L p10 hm12 (hqm' _ rfl)) | exact (N hit).elim
    · exact DW _ (L p6 q7 (hd7 it (List.mem_append_left _ hit) y hy))
    · exact DW _ (L p7 q8 (hd8 it (List.mem_append_left _ hit) y hy))
    · exact (WT12.out it hit y hy).elim (.inl <| W' y ·)
        fun h => Option.some.inj h ▸ DW _ (L p2 q3 hrT)
    · exact DW _ (L p6 q7 (hd7 it (List.mem_append_right _ hit) y hy))
    · exact DW _ (L p7 q8 (hd8 it (List.mem_append_right _ hit) y hy))
    · exact .inl (W' y (hM y (hr7 it hit y hy)))
    · exact .inl (W' y (hCT y (hr8 it hit y hy)))
    · cases rE <;> first | exact I1 (mem_ite_nil hit) hy (L p3 q4 (hrE _ rfl)) | exact (N hit).elim
    · split at hit <;> first | exact I1 hit hy (L p11 (.refl D _) (hrm' _ rfl)) | exact (N hit).elim
    · exact DW _ (L p8 q9 (hd9 it (List.mem_append_left _ hit) y hy))
    · exact (WE12.out it hit y hy).elim (.inl <| W' y ·) fun h => (hwE y h).elim
        (fun e => e ▸ DW _ (L p1 (hm3.trans q3) hg)) fun hy' => DW _ (L p3 q4 (hrE y hy'))
    · exact DW _ (L p8 q9 (hd9 it (List.mem_append_right _ hit) y hy))
    · exact .inl (W' y (hCE y (hr9 it hit y hy)))
    · obtain ⟨q, hq, rfl⟩ := (mem_sets _ _ hit).resolve_left N
      exact Option.some.inj hy ▸ .inl (W' _ (hM _ (hp7 q (List.mem_filter.1 hq).1).1))
    · have hit := mem_ite_nil' hit
      split at hit
      · obtain rfl := Rope.mem_one hit
        cases hy
      · exact .inr (setReach_tgt κ _ it hit y hy)
  · rcases unionSet_iff.1 hy with hy | hy <;> split at hy
    all_goals first
      | exact (WT12.A y hy).widen (.refl D s) p12.next hn
      | exact (WE12.A y hy).widen (.refl D s) p12.next hn
      | simp at hy

/-- A successful walk of `s :: rest` under a variable context with an obligation following it
    walks `rest`, then `s` with an obligation following it, and returns the result of `s` alone
    (after marking the registrations of the rest dead, when `s` always exits) or the
    combination of both results. -/
private theorem wpList_cons_arm (hκ : κ ≠ .top) {s : PStmt P} {rest : PStmts P} {st st' : WSt P}
    {R : WRes P} (h : (wpList κ d true (s :: rest)).run st = .ok (R, st')) :
    ∃ r st1 a st2, (wpList κ d true rest).run st = .ok (r, st1) ∧
      (wpStmt κ d true s).run st1 = .ok (a, st2) ∧
      ((a.ax = true ∧ a = R ∧
         { st2 with dead := r.regs.toList.foldl (·.insert ·) st2.dead } = st') ∨
       (a.ax = false ∧ a.combine r = R ∧ st2 = st')) := by
  obtain ⟨r, st1, a, st2, h1, h2, hc⟩ := wpList_run_cons h
  rw [Bool.eq_false_iff.2 fun hd => hκ (wpList_drop h1 hd)] at h2
  simp only [Bool.not_false, Bool.and_true, Bool.or_true] at h2
  rcases hc with ⟨hd, -, -⟩ | hc
  · exact absurd (wpStmt_drop h2 hd).1 hκ
  · exact ⟨r, st1, a, st2, h1, h2, hc.imp (·.2) (·.2)⟩
include iOp in
omit iLI in
mutual
/-- The walk of a statement whose identifiers are among `D` has the write facts. -/
theorem wpStmt_writes [LawfulHasIdent P] [LawfulHasFvar P] [LawfulHasFvars P] {D : List P.Ident}
    (κ : RE P) (d : Nat) (f : Bool) :
    ∀ (s : PStmt P) {st st' : WSt P} {r : WRes P}, (∀ x ∈ Stmt.idents s, x ∈ D) →
      (wpStmt κ d f s).run st = .ok (r, st') → WalkW D κ st st' r
  | .cmd (.cmd (.init x _ (.det _) _)), _, _, _, hD, h => init_w h (hD x (.head _))
  | .cmd (.cmd (.init x _ .nondet _)), _, _, _, hD, h => init_w h (hD x (.head _))
  | .cmd (.cmd (.set x (.det _) _)), _, _, _, hD, h => set_det_w h (hD x (.head _))
  | .cmd (.cmd (.set x .nondet _)), _, _, _, hD, h => set_nondet_w h (hD x (.head _))
  | .cmd (.cmd (.assume ..)), _, _, _, _, h | .cmd (.cmd (.assert ..)), _, _, _, _, h
  | .cmd (.cmd (.cover ..)), _, _, _, _, h | .cmd (.call ..), _, _, _, _, h
  | .typeDecl .., _, _, _, _, h | .loop .., _, _, _, _, h | .ite .nondet .., _, _, _, _, h => by
    unfold wpStmt at h
    first
      | exact ren_live_w (fun _ => ⟨by simp [Rope.toList_one, WItem.tgt], rfl, rfl⟩) h
      | (obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h; exact .empty D κ _)
      | cases h
      | (walk_on f h; exact ren_live_w
          (fun _ => ⟨by simp [Rope.toList_one, WItem.tgt], rfl, rfl⟩) h)
  | .exit l md, _, _, _, _, h => exit_w h
  | .block l body md, _, _, _, hD, h =>
    block_w (wpList_writes · (d + 1) f body
      (by simpa [Stmt.idents, ExprOrNondet.getVars_det, ExprOrNondet.getVars_nondet,
        getFvars_mem_exprFV] using hD)) h
  | .ite (.det c) tss ess md, _, _, _, hD, h => by
    simp only [wpStmt] at h
    have hT : ∀ x ∈ Block.idents tss, x ∈ D := fun x hx => hD x (by simp [Stmt.idents, hx])
    have hE : ∀ x ∈ Block.idents ess, x ∈ D := fun x hx => hD x (by simp [Stmt.idents, hx])
    split at h
    · exact laid_w (wpList_writes · d true tss hT) (wpList_writes · d true ess hE) h
    · exact real_w (wpList_writes .top d false tss hT) (wpList_writes .top d false ess hE) h
  termination_by structural s => s

/-- The walk of a statement list whose identifiers are among `D` has the write facts. -/
theorem wpList_writes [LawfulHasIdent P] [LawfulHasFvar P] [LawfulHasFvars P] {D : List P.Ident}
    (κ : RE P) (d : Nat) (fEnd : Bool) :
    ∀ (ss : PStmts P) {st st' : WSt P} {r : WRes P}, (∀ x ∈ Block.idents ss, x ∈ D) →
      (wpList κ d fEnd ss).run st = .ok (r, st') → WalkW D κ st st' r
  | [], st, _, _, _, h => by
    simp only [wpList, StateT.run_pure] at h
    cases h
    exact WalkW.empty D κ st
  | s :: rest, st, _, _, hD, h => by
    obtain ⟨r, st1, a, st2, h1, h2, hc⟩ := wpList_run_cons h
    have Wr := wpList_writes κ d fEnd rest (fun x hx => hD x (by simp [Block.idents, hx])) h1
    have Wa := wpStmt_writes κ d _ s (fun x hx => hD x (by simp [Block.idents, hx])) h2
    rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
    iterate 2 exact Wa.widen Wr.toWMono WMono.same
    · have Wa' := Wa.widen Wr.toWMono (WMono.refl D _)
      have Wr' := Wr.widen (WMono.refl D st) Wa.toWMono
      exact ⟨Wa'.toWMono, fun it hit y hy => (Rope.mem_app.1 hit).elim (Wa'.out it · y hy)
        (Wr'.out it · y hy), fun y hy => (unionSet_iff.mp hy).elim (Wa'.A y) (Wr'.A y),
        fun e he => (Rope.mem_app.1 he).elim (Wa'.regs e) (Wr'.regs e)⟩
  termination_by structural ss => ss
end

omit iDE iBE iLB iHF iSF iHI iLI iHa iHFs iWL in
/-- A value-valued store that changes one name to a value stays value-valued. -/
private theorem canon_put {σ σ1 : SemanticStore P} {v : P.Val} (hC : WellFormedStore σ F)
    (h1 : σ1 x = some v) (h2 : ∀ y, x ≠ y → σ1 y = σ y)
    (hv : HasVal.value F v) : WellFormedStore σ1 F := fun y w hy => by
  rcases Classical.em (x = y) with rfl | hxy
  · exact Option.some.inj (h1.symm.trans hy) ▸ hv
  · exact hC y w ((h2 y hxy).symm.trans hy)
include iLV in
omit iDE iBE iLB iHI iLI iHa iWL in
/-- A run of items keeps a store value-valued. -/
theorem MainRun.canon (hF : WellFormedSemanticEvalBase F) :
    ∀ {items : List (Item P)} {σ σ' : SemanticStore P} {tr : List (Event P)},
      MainRun F items σ tr σ' → WellFormedStore σ F → WellFormedStore σ' F := fun hm => by
  induction hm with
  | nil => exact id
  | side _ ih => exact ih
  | plain hc _ ih =>
    refine fun hC => ih ?_
    unfold EvalE at hc
    split at hc
    · rcases hc with ⟨he, ⟨_, h1, h2⟩⟩ | ⟨⟨_, h1, h2⟩, hv⟩ | ⟨he, ⟨_, h1, h2⟩⟩ |
        ⟨⟨_, h1, h2⟩, ⟨_, _, _, _, hv⟩⟩ | _ | _ | _
      all_goals first
        | exact canon_put hC h1 h2 (EvalsTo.value hF.val hC he)
        | exact canon_put hC h1 h2 (LawfulHasVal.valueOfTy_isVal _ _ _ hv)
        | exact hC
    · exact hc.elim

omit iLI in
/-- A run of the resolved output of a walk with the write facts changes only names the walk may
    assign and the reach variable of its context. -/
theorem WalkW.frame {st st' : WSt P} (hW : WalkW D κ st st' r) {ir : List (Item P)}
    {σ σ' : SemanticStore P} {tr : List (Event P)} (hir : resolveItems T Y r.out.toList = .ok ir)
    (hm : MainRun F ir σ tr σ') (hy : ¬ Wr0 D st st' y) (hk : κ.wvar ≠ some y) :
    σ' y = σ y := MainRun.frame hir hm y fun it hit hty => (hW.out it hit y hty).elim hy hk
section
omit iWL

/-- A name drawn from `s1` on has no counter below `s1.next`. -/
private theorem NewIn.not_below {s1 s2 : WSt P} {e : P.Ident} (he : NewIn s1 s2 e)
    (hb : ∃ b j, e = freshName b j ∧ j < s1.next) : False := by
  grind [NewIn, freshName_counter_inj]
/-- A name drawn by a walk from `st1` on (after a walk from a well-formed `st` to `st1` of a
    fragment whose identifiers `D` of the form of a fresh name are avoided) is not a name the walk
    from `st` may assign. -/
theorem not_wr0 {st st1 st2 : WSt P} (hwf : WFSt st) (hm : WMono D st st1)
    (hav : ∀ x ∈ D, ∀ b j, x = freshName b j → st.avoid.contains x = true) {e : P.Ident}
    (he : NewIn st1 st2 e) : ¬ Wr0 D st st1 e := by
  have hf := hwf.nm_fresh
  rintro (h | ⟨z, hz⟩ | h) <;> grind [NewIn, freshName_counter_inj, hm.avoid, hm.next]
omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs in
/-- The reach variable of a context is a variable of it. -/
theorem wvar_mem (h : κ.wvar = some y) : y ∈ RE.vars κ := by
  cases κ <;> simp_all [RE.wvar, RE.vars]
/-- A name drawn by a walk from `st1` on is no variable of a context whose variables are fresh
    names drawn before `st`. -/
theorem drawn_not_vars {st st1 st2 : WSt P} (h1 : st.next ≤ st1.next)
    (hκ : ∀ y ∈ RE.vars κ, ∃ b j, y = freshName b j ∧ j < st.next) {e : P.Ident}
    (he : NewIn st1 st2 e) : κ.wvar ≠ some e := fun hw =>
  let ⟨b, j, hy, hj⟩ := hκ _ (wvar_mem hw)
  he.not_below ⟨b, j, hy, by omega⟩

end
omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iWL in
/-- The identifiers of the rest of a list are identifiers of the list. -/
private theorem idents_rest {S : List P.Ident} {s : PStmt P} {rest : PStmts P}
    (hx : x ∈ Block.idents rest) : x ∈ S ++ Block.idents (s :: rest) := by grind [Block.idents]
/-! ## The walks of a list `s :: rest` -/

include iOp iLF iLFs in
/-- After the walks of `rest` and then of `s` (from a well-formed state avoiding the names of
    the form of a fresh name of `S` and of the list, under a context whose variables are fresh
    names drawn before), a run of the resolved output of `rest` leaves the registrations of `s`
    unchanged. -/
theorem keep_regs {fEnd f : Bool} {s : PStmt P} {rest : PStmts P} {st st1 st2 : WSt P} {a : WRes P}
    {S : List P.Ident} {ir : List (Item P)} {σL1 σL2 : SemanticStore P} {tr : List (Event P)}
    (hwf : WFSt st) (h1 : (wpList κ d fEnd rest).run st = .ok (r, st1))
    (h2 : (wpStmt κ d f s).run st1 = .ok (a, st2))
    (hav : ∀ x ∈ S ++ Block.idents (s :: rest), ∀ b j, x = freshName b j →
      st.avoid.contains x = true)
    (hκ : ∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st.next) ∧
      st.avoid.contains y = false ∧ ∀ x : P.Ident, st.nm[x]? ≠ some y)
    (hir : resolveItems T Y r.out.toList = .ok ir) (hm : MainRun F ir σL1 tr σL2) {e : P.Ident}
    (he : e ∈ a.regs.toList) : σL2 e = σL1 e := by
  have Wr := wpList_writes κ d fEnd rest (fun _ => idents_rest (S := S) (s := s)) h1
  have hd := (wpStmt_writes κ d f s (fun _ => id) h2).regs e he
  exact Wr.frame hir hm (not_wr0 hwf Wr.toWMono hav hd)
    (drawn_not_vars Wr.next (fun y hy => (hκ y hy).1) hd)
include iOp iLF iLFs in
/-- Under a context `andNeg q g` with `q ≠ g` whose variables are fresh names drawn before the
    walk, not avoided and no renamings, a run of the resolved output of a list walk (from a
    state avoiding the names of the form of a fresh name of the list) keeps the value of the
    enclosing reach `q`. -/
theorem keep_andNeg {fEnd : Bool} {rest : PStmts P} {st st1 : WSt P} {ir : List (Item P)}
    {σL1 σL2 : SemanticStore P} {tr : List (Event P)}
    (h1 : (wpList κ d fEnd rest).run st = .ok (r, st1))
    (hav : ∀ x ∈ Block.idents rest, ∀ b j, x = freshName b j → st.avoid.contains x = true)
    (hκ : ∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st.next) ∧
      st.avoid.contains y = false ∧ ∀ x : P.Ident, st.nm[x]? ≠ some y)
    (hir : resolveItems T Y r.out.toList = .ok ir) (hm : MainRun F ir σL1 tr σL2) {q g : P.Ident}
    (hκq : κ = .andNeg q g) (hqg : q ≠ g) : σL2 q = σL1 q := by
  subst hκq
  have hq := hκ q (by simp [RE.vars])
  refine (wpList_writes _ d fEnd rest (fun _ => id) h1).frame hir hm ?_
    (by simpa [RE.wvar] using hqg.symm)
  rintro (h | ⟨z, hz⟩ | h) <;> grind [NewIn, freshName_counter_inj]
include iOp iLF iLFs iLV in
/-- After the walks of `rest` and then of `s` (from a well-formed state avoiding the names of
    the form of a fresh name of `S` and of the list, under a context whose variables are fresh
    names drawn before), a run of the resolved output of `rest` from a value-valued store keeps
    the value of the selector of every carried merge registered by `s`. -/
theorem keep_sel {F : P.Factory} (hF : WellFormedSemanticEvalBase F) {κ : RE P} {d : Nat}
    {fEnd f : Bool} {s : PStmt P}
    {rest : PStmts P} {st st1 st2 : WSt P} {r a : WRes P} {S : List P.Ident}
    {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident} {ir : List (Item P)}
    {σL1 σL2 : SemanticStore P} {tr : List (Event P)} (hwf : WFSt st)
    (h1 : (wpList κ d fEnd rest).run st = .ok (r, st1))
    (h2 : (wpStmt κ d f s).run st1 = .ok (a, st2))
    (hav : ∀ x ∈ S ++ Block.idents (s :: rest), ∀ b j, x = freshName b j →
      st.avoid.contains x = true)
    (hκ : ∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st.next) ∧
      st.avoid.contains y = false ∧ ∀ x : P.Ident, st.nm[x]? ≠ some y)
    (hir : resolveItems T Y r.out.toList = .ok ir) (hm : MainRun F ir σL1 tr σL2)
    (hC : WellFormedStore σL1 F) {k i : Nat} {n xB : P.Ident} {v : WExpr P}
    (hc : CarryReg a st2 k i n v xB) (b : Bool) :
    SelIs F T Y σL2 v b ↔ SelIs F T Y σL1 v b := by
  have Wr := wpList_writes κ d fEnd rest (fun _ => idents_rest (S := S) (s := s)) h1
  have Wa := wpStmt_writes κ d f s (fun _ => id) h2
  have hwf1 := (wpList_walkOK h1).wf hwf fun x hx =>
    hav x (idents_rest (stmtsInits_mem_idents x hx))
  obtain ⟨hget, hreg⟩ := hc
  have hx := Wa.regs _ hreg
  rcases Wa.carries k _ (List.mem_of_getElem? hget) with hq | ⟨-, -, e, hv, hsel⟩
  · obtain ⟨b', j, rfl, hj⟩ := hwf1.carries_fresh k _ _ _ _ (List.getElem?_of_mem hq).choose_spec
    exact (hx.not_below ⟨_, _, rfl, hj⟩).elim
  have hg : ∀ x, NewIn st1 st2 x → σL2 x = σL1 x := fun x hx =>
    Wr.frame hir hm (not_wr0 hwf Wr.toWMono hav hx)
      (drawn_not_vars Wr.next (fun y hy => (hκ y hy).1) hx)
  have hC' := MainRun.canon hF hm hC
  dsimp only at hv
  subst hv
  constructor <;> rintro ⟨e1, xB1, x1, he1, e', hr, hev⟩ <;> cases he1
  · exact ⟨_, _, _, rfl, e', hr, (sel_eval hF hC hC' hg hsel hr).symm.trans hev⟩
  · exact ⟨_, _, _, rfl, e', hr, (sel_eval hF hC hC' hg hsel hr).trans hev⟩
include iLV in
omit iLB iHI iLI in
/-- A run of items keeps a bound name bound to a value of its final declared type (for the final
    type maps `T`, `Y`) when its value has that type. -/
theorem keep_typed {ir : List (Item P)} {σL1 σL2 : SemanticStore P} {tr : List (Event P)}
    (hm : MainRun F ir σL1 tr σL2) {w : P.Val} (hw : σL1 n = some w)
    (ht : ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty) :
    ∃ w', σL2 n = some w' ∧ ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w' ty :=
  MainRun.typed hm hw ht

end -- public section

end WP
end Imperative
