/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverFacts
public import Strata.DL.Imperative.CmdCallFormals
import Strata.Transform.WP.WPOverEmit
import Strata.Util.ExceptProps

/-! # The operators of the guarded program

Every operator the guarded program of the WP phase references (`Block.getOps`: the operators of
its commands and of its `ite` conditions) is an operator of the loop-free program
(`wpEntry_ops`), for an expression language whose conditional, Boolean literals, variables and
substitution add no operator (`OpsLaws`).

The guarded expressions of the walk carry the loop-free expressions of the walked fragment
unchanged (`WExpr.user`); the other expressions the walk builds are variables, literals and
conditionals.  `wOpsIn O` says that the loop-free expressions of a guarded expression have their
operators in `O`; every item the walk of a fragment with operators in `O` emits has this
property, and so do the carried merges of the walk state (`OpsWalk`).  Resolution, merging of
obligation runs and nesting then keep the operators within `O`.

Key definitions: `OpsLaws`, `wOpsIn`, `WItem.OpsIn`, `Item.ops`, `OpsWalk`.

Key theorems: `wpEntry_ops`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr}

/-- The laws on operators of the expressions the WP phase builds: a conditional references the
    operators of its parts, the Boolean literals and the variables reference none, and a
    substitution references the operators of the expression and of the substituted values. -/
structure OpsLaws (P : PureExpr) [HasBool P] [HasFvar P] [WPOps P] [HasOps P] : Prop where
  ite : ∀ c t e o, o ∈ HasOps.getOps (P := P) (WPOps.ite c t e) →
    o ∈ HasOps.getOps c ∨ o ∈ HasOps.getOps t ∨ o ∈ HasOps.getOps e
  tt : HasOps.getOps (HasBool.tt (P := P)) = []
  ff : HasOps.getOps (HasBool.ff (P := P)) = []
  var : ∀ x ty, HasOps.getOps (HasFvar.mkVar (P := P) x ty) = []
  substFn : ∀ e f o, o ∈ HasOps.getOps (P := P) (WPOps.substFn e f) →
    o ∈ HasOps.getOps e ∨ ∃ y v, f y = some v ∧ o ∈ HasOps.getOps v

/-! ## Operators of guarded expressions and items -/

section
variable [HasOps P]

/-- The operators of the loop-free expressions of a guarded expression are in `O`. -/
@[expose] def wOpsIn (O : List P.Ident) : WExpr P → Prop
  | .user e _ => ∀ o ∈ HasOps.getOps e, o ∈ O
  | .var _ | .lit _ => True
  | .ite c t e => wOpsIn O c ∧ wOpsIn O t ∧ wOpsIn O e

mutual
/-- The guarded expressions of an item, at any depth, have `wOpsIn O`. -/
@[expose] def WItem.OpsIn (O : List P.Ident) : WItem P → Prop
  | .init _ _ e | .set _ e => ∀ w ∈ e, wOpsIn O w
  | .assume _ e _ => wOpsIn O e
  | .obls _ cs => ∀ c ∈ cs, wOpsIn O c.2.2.1
  | .branch t e => WItem.ListOpsIn O t ∧ WItem.ListOpsIn O e
/-- The guarded expressions of the items of a list, at any depth, have `wOpsIn O`. -/
@[expose] def WItem.ListOpsIn (O : List P.Ident) : List (WItem P) → Prop
  | [] => True
  | it :: rest => it.OpsIn O ∧ WItem.ListOpsIn O rest
end

/-- `WItem.ListOpsIn O` holds exactly when every item of the list has `OpsIn O`. -/
private theorem WItem.listOpsIn_iff {O : List P.Ident} :
    ∀ {l : List (WItem P)}, WItem.ListOpsIn O l ↔ ∀ it ∈ l, it.OpsIn O
  | [] => by simp [WItem.ListOpsIn]
  | it :: rest => by simp [WItem.ListOpsIn, WItem.listOpsIn_iff (l := rest)]

/-- `ite(κ, t, e)` has `wOpsIn O` when `t` and `e` have it. -/
private theorem wOpsIn_kIte {O : List P.Ident} {κ : RE P} {t e : WExpr P} (ht : wOpsIn O t)
    (he : wOpsIn O e) : wOpsIn O (kIte κ t e) := by
  cases κ <;> simp [kIte, wOpsIn, ht, he]

/-- The context of a reach context has `wOpsIn O`. -/
private theorem wOpsIn_kExpr {O : List P.Ident} (κ : RE P) : wOpsIn O (kExpr κ) := by
  cases κ <;> simp [kExpr, wOpsIn, WExpr.not, WExpr.and]

/-- The negation of an expression with `wOpsIn O` has it. -/
private theorem wOpsIn_not {O : List P.Ident} {X : WExpr P} (h : wOpsIn O X) :
    wOpsIn O X.not := by
  cases X <;> simp_all [WExpr.not, wOpsIn]

/-- A disjunction of expressions with `wOpsIn O` has it. -/
private theorem wOpsIn_disjW {O : List P.Ident} :
    ∀ {l : List (WExpr P)}, (∀ a ∈ l, wOpsIn O a) → wOpsIn O (disjW l)
  | [], _ => trivial
  | [a], h => h a (.head _)
  | a :: _ :: _, h => ⟨h a (.head _), trivial, wOpsIn_disjW fun c hc => h c (.tail _ hc)⟩

/-- The items of `setReach κ X` have `OpsIn O` when `X` has `wOpsIn O`. -/
private theorem setReach_ops {O : List P.Ident} (κ : RE P) {X : WExpr P} (hX : wOpsIn O X) :
    ∀ it ∈ (setReach κ X).toList, it.OpsIn O := by
  cases κ <;> simp [setReach, Rope.toList_nil, Rope.toList_one, WItem.OpsIn, hX, wOpsIn_not hX]

/-- The values of the carried merges `C` have `wOpsIn O`. -/
@[expose] def CarOK (O : List P.Ident) (C : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))) :
    Prop :=
  ∀ k q, q ∈ C.getD k [] → wOpsIn O q.2.1

/-- Emptying the carried merges at one depth keeps `CarOK`. -/
private theorem CarOK.insert_nil {O : List P.Ident}
    {C : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))} (h : CarOK O C) (k : Nat) :
    CarOK O (C.insert k []) := fun j q hq => by
  rw [Std.HashMap.getD_insert] at hq
  split at hq
  · simp at hq
  · exact h j q hq

/-- Removing the carried merges at one depth keeps `CarOK`. -/
private theorem CarOK.erase {O : List P.Ident}
    {C : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))} (h : CarOK O C) (k : Nat) :
    CarOK O (C.erase k) := fun j q hq => by
  rw [Std.HashMap.getD_erase] at hq
  split at hq
  · simp at hq
  · exact h j q hq

/-- Registering carried merges selected by an expression with `wOpsIn O` keeps `CarOK O`. -/
private theorem CarOK.carryIns {O : List P.Ident}
    {C : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))} (hC : CarOK O C) {e : WExpr P}
    (he : wOpsIn O e) (cps : List (P.Ident × P.Ident)) (o : Option Nat) :
    CarOK O (carryIns e cps C o) := fun k q hq => by
  obtain ⟨new, hk, hnew⟩ := carryIns_getD e cps C o k
  rw [hk, List.mem_append] at hq
  refine hq.elim (fun hq => ?_) (hC k q)
  obtain ⟨-, p, -, rfl⟩ := hnew q hq
  exact ⟨he, trivial, trivial⟩

mutual
/-- The operators of a flat item, its reachability assumption included. -/
@[expose] def Item.ops [HasBool P] [HasFvar P] [WPOps P] : Item P → List P.Ident
  | .plain s => Stmt.getOps s
  | .obls r cs => Block.getOps (reachPre r) ++ Block.getOps cs
  | .branch t e => Item.listOps t ++ Item.listOps e
/-- The operators of a list of flat items. -/
@[expose] def Item.listOps [HasBool P] [HasFvar P] [WPOps P] : List (Item P) → List P.Ident
  | [] => []
  | it :: rest => it.ops ++ Item.listOps rest
end

end

/-! ## Items of ropes -/

/-- A property of the items of two ropes holds for the items of their concatenation. -/
private theorem seq_app {Q : WItem P → Prop} {a b : Rope (WItem P)} (ha : ∀ it ∈ a.toList, Q it)
    (hb : ∀ it ∈ b.toList, Q it) : ∀ it ∈ (a.app b).toList, Q it := by
  simpa [Rope.toList_app, or_imp, forall_and] using And.intro ha hb

/-- A property of an item holds for the items of its rope. -/
private theorem seq_one {Q : WItem P → Prop} {x : WItem P} (h : Q x) :
    ∀ it ∈ (Rope.one x).toList, Q it := by
  simpa [Rope.toList_one] using h

/-- Every property holds for the items of the empty rope. -/
private theorem seq_nil {Q : WItem P → Prop} : ∀ it ∈ (Rope.nil : Rope (WItem P)).toList, Q it := by
  simp [Rope.toList_nil]

/-- A property of the items of both ropes of a conditional holds for the items of its value. -/
private theorem seq_ite {Q : WItem P → Prop} {c : Prop} [Decidable c] {a b : Rope (WItem P)}
    (ha : ∀ it ∈ a.toList, Q it) (hb : ∀ it ∈ b.toList, Q it) :
    ∀ it ∈ (if c then a else b).toList, Q it := by
  split
  · exact ha
  · exact hb

/-- A property of the items of ropes holds for the items of a fold whose steps keep it. -/
private theorem seq_foldl_step {α : Type} {Q : WItem P → Prop}
    {g : Rope (WItem P) → α → Rope (WItem P)} : ∀ {L : List α} {s : Rope (WItem P)},
    (∀ acc x, x ∈ L → (∀ it ∈ acc.toList, Q it) → ∀ it ∈ (g acc x).toList, Q it) →
    (∀ it ∈ s.toList, Q it) → ∀ it ∈ (L.foldl g s).toList, Q it
  | [], _, _, hs => hs
  | x :: L, s, hg, hs =>
    seq_foldl_step (L := L) (fun acc y hy => hg acc y (.tail _ hy)) (hg s x (.head _) hs)

/-! ## Emission -/

section
variable [iBo : HasBool P] [iFv : HasFvar P] [iW : WPOps P] [iO : HasOps P]

omit iBo iW in
/-- The operators of a concatenation of statement lists are those of its parts. -/
private theorem getOps_append (a b : PStmts P) :
    Block.getOps (a ++ b) = Block.getOps a ++ Block.getOps b := by
  induction a <;> simp [Block.getOps, *]

/-- Every operator of the nesting of flat items is an operator of the items. -/
private theorem nest_ops :
    ∀ (l : List (Item P)), ∀ o ∈ Block.getOps (nest l), o ∈ Item.listOps l
  | [], o, ho => by simp [nest, Block.getOps] at ho
  | .plain _ :: rest, o, ho | .obls _ _ :: rest, o, ho => by
    simp only [nest, nestCons] at ho
    split at ho <;> grind [Item.listOps, Item.ops, Block.getOps, Stmt.getOps, getOps_append,
      nest_ops rest o, ExprOrNondet.getOps]
  | .branch t e :: rest, o, ho => by
    simp only [nest, nestCons] at ho
    split at ho <;> grind [Item.listOps, Item.ops, Block.getOps, Stmt.getOps, getOps_append,
      nest_ops t o, nest_ops e o, ExprOrNondet.getOps]
  termination_by l => sizeOf l

variable [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident] [iHa : Hashable P.Ident]

/-- Every operator of a resolved guarded expression is an operator of its loop-free
    expressions. -/
private theorem resolveE_ops (hL : OpsLaws P) {O : List P.Ident} {T : Std.HashMap P.Ident P.Ty}
    {Y : Std.HashMap P.Ident P.Ident} : ∀ {w : WExpr P} {e' : P.Expr}, resolveE T Y w = .ok e' →
      wOpsIn O w → ∀ o ∈ HasOps.getOps e', o ∈ O
  | .user e [], e', h, hw, o, ho => by
    cases h
    exact hw o ho
  | .user e (p :: ps), e', h, hw, o, ho => by
    simp only [resolveE, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨hm, hf, rfl⟩ := h
    have hv : ∀ (ren : List (P.Ident × P.Ident)) (h0 h : Std.HashMap P.Ident P.Expr),
        (∀ (x : P.Ident) v, h0[x]? = some v → ∃ y ty, v = HasFvar.mkVar (P := P) y ty) →
        ren.foldlM (init := h0) (fun h (y, y') => do
          pure (h.insert y (HasFvar.mkVar y' (some (← tyOfName T Y y'))))) = Except.ok h →
        ∀ (x : P.Ident) v, h[x]? = some v → ∃ y ty, v = HasFvar.mkVar (P := P) y ty := by
      intro ren
      induction ren with
      | nil => exact fun h0 h h0e hf => Except.ok.inj hf ▸ h0e
      | cons q ps ih =>
        intro h0 h h0e hf
        simp only [List.foldlM_cons, bind, Except.bind, pure, Except.pure] at hf
        rcases hty : tyOfName T Y q.2 with _ | ty <;> simp only [hty, reduceCtorEq] at hf
        refine ih _ h (fun x v hv => ?_) hf
        rw [Std.HashMap.getElem?_insert] at hv
        split at hv <;> grind
    rcases hL.substFn _ _ o ho with ho | ⟨y, v, hy, ho⟩
    · exact hw o ho
    · obtain ⟨z, ty, rfl⟩ := hv _ {} hm (by simp) hf y v hy
      simp [hL.var] at ho
  | .var x, e', h, _, o, ho => by
    simp only [resolveE, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨ty, -, rfl⟩ := h
    simp [hL.var] at ho
  | .lit b, e', h, _, o, ho => by cases b <;> cases h <;> simp [hL.tt, hL.ff] at ho
  | .ite c t f, e', h, hw, o, ho => by
    simp only [resolveE, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨c', hc, t', ht, f', hf, rfl⟩ := h
    rcases hL.ite _ _ _ o ho with ho | ho | ho
    · exact resolveE_ops hL hc hw.1 o ho
    · exact resolveE_ops hL ht hw.2.1 o ho
    · exact resolveE_ops hL hf hw.2.2 o ho

/-- Every operator of resolved items is an operator of the loop-free expressions of the items. -/
private theorem resolveItems_ops (hL : OpsLaws P) {O : List P.Ident}
    {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident} (l : List (WItem P)) :
    ∀ (items : List (Item P)), resolveItems T Y l = .ok items → WItem.ListOpsIn O l →
      ∀ o ∈ Item.listOps items, o ∈ O := by
  induction l using WItem.rec_1 (motive_1 := fun it => ∀ a, resolveItem T Y it = .ok a →
    it.OpsIn O → ∀ o ∈ a.ops, o ∈ O) with
  | nil => exact fun _ h _ o ho => by cases h; simp [Item.listOps] at ho
  | cons it rest ihi ihr =>
    intro items h ⟨hi, hr⟩ o ho
    simp only [resolveItems, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨a, ha, r, hrr, rfl⟩ := h
    simp only [Item.listOps, List.mem_append] at ho
    exact ho.elim (ihi a ha hi o) (ihr r hrr hr o)
  | branch t e iht ihe =>
    rename_i a h hi o ho
    simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨t', ht', e', he', rfl⟩ := h
    simp only [Item.ops, List.mem_append] at ho
    exact ho.elim (iht t' ht' hi.1 o) (ihe e' he' hi.2 o)
  | obls rc cs =>
    rename_i a h hc o ho
    simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨cs', hcs, rfl⟩ := h
    have hI : ∀ {c t e : P.Expr}, HasOps.getOps c = [] → HasOps.getOps t = [] →
        HasOps.getOps e = [] → HasOps.getOps (WPOps.ite c t e) = [] := fun hc ht he =>
      List.eq_nil_iff_forall_not_mem.2 fun o ho => by
        rcases hL.ite _ _ _ o ho with h | h | h <;> simp_all
    have hr : Block.getOps (reachPre rc) = [] := by
      rcases rc with _ | (_ | _ | _ | _) <;>
        simp [reachPre, RE.expr, Block.getOps, Stmt.getOps, HasOpsImp.getOps, CmdExt.getOps,
          Cmd.getOps, HasFvar.mkBoolVar, notE, andE, hL.var, hL.tt, hL.ff, hI]
    simp only [Item.ops, hr, List.nil_append] at ho
    clear hr hI
    induction cs generalizing cs' with
    | nil => cases hcs; simp [Block.getOps] at ho
    | cons c cs ih =>
      obtain ⟨b, l, e, md⟩ := c
      simp only [List.mapM_cons, Except.bind_is_ok, Except.pure_is_ok] at hcs
      obtain ⟨c', ⟨e', he, rfl⟩, cs'', hcs, rfl⟩ := hcs
      simp only [Block.getOps, List.mem_append] at ho
      refine ho.elim (fun ho => ?_) (ih (fun c h => hc c (.tail _ h)) cs'' hcs)
      cases b <;> exact resolveE_ops hL he (hc _ (.head _)) o ho
  | assume l e md =>
    rename_i a h hi o ho
    simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨e', he, rfl⟩ := h
    exact resolveE_ops hL he hi o ho
  | init x ty e | set x e =>
    rename_i a h hi o ho
    (try cases ty) <;> rcases e with _ | e <;> simp only [resolveItem, resolveOE,
      Except.bind_is_ok, Except.pure_is_ok, pure_bind] at h
    all_goals first
      | (obtain ⟨_, ⟨e', he, rfl⟩, rfl⟩ := h; exact resolveE_ops hL he (hi _ rfl) o ho)
      | (obtain ⟨_, -, _, ⟨e', he, rfl⟩, rfl⟩ := h; exact resolveE_ops hL he (hi _ rfl) o ho)
      | (obtain ⟨_, -, rfl⟩ := h; simp [Item.ops, mkInit, Stmt.getOps, HasOpsImp.getOps,
          CmdExt.getOps, Cmd.getOps] at ho)
      | (cases h; simp [Item.ops, mkInit, Stmt.getOps, HasOpsImp.getOps, CmdExt.getOps,
          Cmd.getOps] at ho)
      | (obtain ⟨_, rfl, rfl⟩ := h; simp [Item.ops, Stmt.getOps, HasOpsImp.getOps,
          CmdExt.getOps, Cmd.getOps] at ho)

variable [iDE : DecidableEq P.Ident]

omit iB iLB iHa in
/-- Every operator of the merged obligation runs of flat items is an operator of the items. -/
private theorem mergeObls_ops (l : List (Item P)) :
    ∀ o ∈ Item.listOps (mergeObls l), o ∈ Item.listOps l := by
  fun_induction mergeObls l with
  | case2 cs rest r cs' rest' hm ih =>
    simp only [hm, Item.listOps, Item.ops, getOps_append] at ih ⊢
    grind
  | _ => (try cases ‹Item P›) <;> grind [Item.listOps, Item.ops]

/-- Every operator of the emitted guarded program is an operator of the loop-free expressions
    of the items. -/
private theorem emit_ops (hL : OpsLaws P) {O : List P.Ident} {T : Std.HashMap P.Ident P.Ty}
    {Y : Std.HashMap P.Ident P.Ident} {s : Rope (WItem P)} {lay : PStmts P}
    (h : emit T Y s = .ok lay) (hs : WItem.ListOpsIn O s.toList) :
    ∀ o ∈ Block.getOps lay, o ∈ O := by
  obtain ⟨items, hi, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 h
  exact fun o ho => resolveItems_ops hL _ _ hi hs o (mergeObls_ops _ o (nest_ops _ o ho))

end

/-! ## The walk -/

section
variable [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iHa : Hashable P.Ident] [iFs : HasFvars P]

/-- An optional draw keeps the carried merges. -/
private theorem OptDraw.carries {b : String} {s s' : WSt P} {o : Option P.Ident}
    (h : OptDraw b s s' o) : s'.carries = s.carries := by
  cases o with
  | none => exact congrArg WSt.carries h
  | some x => cases (wFreshBool_run _ _).symm.trans h; rfl

variable [iW : WPOps P] [iO : HasOps P]

/-- Every successful run of the walk `m` from a state whose carried merges have `wOpsIn O`
    ends in such a state, with output items whose guarded expressions have `wOpsIn O`. -/
@[expose] def OpsWalk (O : List P.Ident) (m : WM P (WRes P)) : Prop :=
  ∀ st r st', CarOK O st.carries → m.run st = .ok (r, st') →
    CarOK O st'.carries ∧ ∀ it ∈ r.out.toList, it.OpsIn O

/-- Inverts a successful run of a straight-line step of the WP walk in the hypothesis `h`. -/
local macro "wp_inv " h:ident : tactic => `(tactic| simp only [Bool.not_true, Bool.not_false,
  Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_get,
  StateT.run_set, StateT.run_pure, Except.bind_is_ok, Except.pure_is_ok, Except.ok.injEq,
  Prod.mk.injEq, exists_eq_left', liveDel, liveAdd, wFresh_run, wFreshBool_run] at $h:ident)

/-- Splits a goal about the items of a rope built from concatenations and conditionals. -/
local macro "seq_ok" : tactic => `(tactic| (
  repeat' first
    | with_reducible exact seq_nil
    | with_reducible apply seq_app
    | with_reducible apply seq_ite
  all_goals try with_reducible apply seq_one))

/-- Closes `∀ a ∈ e :: L, wOpsIn O a` for a list `L` of variables and `e` a variable or the
    context of a reach context. -/
local macro "vars_ok" : tactic => `(tactic| (
  simp only [List.mem_cons, List.mem_reverse, List.mem_map]
  intro _ ha
  rcases ha with h | ⟨_, -, h⟩ <;> subst h
  all_goals first | exact wOpsIn_kExpr _ | trivial))

/-- Closes `wOpsIn O e` for an expression `e` built by the walk from variables, literals,
    contexts and expressions with `wOpsIn O` in the context. -/
local macro "w_ok" : tactic => `(tactic| repeat' first
  | assumption
  | exact wOpsIn_kExpr _
  | exact (trivial : True)
  | apply wOpsIn_kIte
  | apply wOpsIn_not
  | unfold kAnd
  | unfold kImp
  | unfold WExpr.and
  | unfold WExpr.or
  | refine ⟨?_, ?_, ?_⟩)

/-- Closes `it.OpsIn O` for an item `it` built by the walk, or the goal that the items of a rope
    have `OpsIn O` from the context. -/
local macro "item_ok" : tactic => `(tactic| first
  | assumption
  | (simp only [WItem.OpsIn, Option.mem_def, Option.some.injEq, forall_eq', reduceCtorEq,
      false_implies, implies_true, List.mem_singleton, forall_eq]
     w_ok
     done))

/-- A run of `saveRestore xs` keeps the carried merges and emits saves, copies and restores
    whose guarded expressions have `wOpsIn O`. -/
private theorem saveRestore_ops {O : List P.Ident} {xs : List P.Ident} {s s' : WSt P}
    {sv cp rs : Rope (WItem P)} {cps : List (P.Ident × P.Ident)}
    (h : (saveRestore xs).run s = .ok ((sv, cp, rs, cps), s')) :
    s'.carries = s.carries ∧ (∀ it ∈ sv.toList, it.OpsIn O) ∧ (∀ it ∈ cp.toList, it.OpsIn O) ∧
      ∀ it ∈ rs.toList, it.OpsIn O := by
  unfold saveRestore at h
  obtain ⟨acc, s1, hl, h⟩ := wm_run_bind_ok h
  obtain ⟨sv1, cp1, rs1, cps1⟩ := acc
  cases h
  have hI := wm_forIn_inv (fun _ (b : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) ×
      List (P.Ident × P.Ident)) st => st.carries = s.carries ∧ (∀ it ∈ b.1.toList, it.OpsIn O) ∧
      (∀ it ∈ b.2.1.toList, it.OpsIn O) ∧ ∀ it ∈ b.2.2.1.toList, it.OpsIn O) _ ?_ xs [] _ s _ s'
    ⟨rfl, seq_nil, seq_nil, seq_nil⟩ hl
  · exact hI
  intro S y b st b' st' ⟨hc, h1, h2, h3⟩ hb
  obtain ⟨n1, st1, hn1, hb⟩ := wm_run_bind_ok hb
  obtain ⟨n2, st2, hn2, hb⟩ := wm_run_bind_ok hb
  cases (wFreshLike_run _ _).symm.trans hn1
  cases (wFreshLike_run _ _).symm.trans hn2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hb)
  exact ⟨_, rfl, hc, seq_app h1 (seq_one fun _ h => by cases h; trivial),
    seq_app h2 (seq_one fun _ h => by cases h; trivial),
    seq_app h3 (seq_one fun _ h => by cases h; trivial)⟩

/-- The walk of a statement that is not a command, an `exit`, a block or a deterministic `ite`
    has `OpsWalk O`. -/
private theorem opsWalk_other {O : List P.Ident} (κ : RE P) (d : Nat) (f : Bool) (s : PStmt P)
    (hs : (∀ c, s ≠ .cmd c) ∧ (∀ l md, s ≠ .exit l md) ∧ (∀ l b md, s ≠ .block l b md) ∧
      ∀ c t e md, s ≠ .ite (.det c) t e md) : OpsWalk O (wpStmt κ d f s) := by
  intro st a st' hC h
  obtain ⟨h1, h2, h3, h4⟩ := hs
  unfold wpStmt at h
  rcases s with _ | _ | ⟨_ | c, t, e, md⟩ | _ | _ | _ <;>
    first | exact absurd rfl (h4 _ _ _ _) | cases h | simp at h1 h2 h3
  exact ⟨hC, by simp [Rope.toList_nil]⟩

/-- The walk of a block whose body walks have `OpsWalk O` has it. -/
private theorem opsWalk_block {O : List P.Ident} {κ : RE P} {d : Nat} {f : Bool} {l : String}
    {body : PStmts P} (md : MetaData P) (hB : ∀ κB, OpsWalk O (wpList κB (d + 1) f body)) :
    OpsWalk O (wpStmt κ d f (.block l body md)) := by
  intro st a st' hC h
  unfold wpStmt at h
  wp_inv h
  split at h
  · wp_inv h
    obtain ⟨⟨B, s5⟩, h5, rfl, rfl⟩ := h
    obtain ⟨hC5, hB5⟩ := hB _ _ _ _ (hC.insert_nil (d + 1)) h5
    refine ⟨hC5.erase (d + 1), ?_⟩
    dsimp only
    seq_ok
    all_goals first
      | exact hB5
      | (refine seq_foldl_step (fun acc q hq hacc => seq_app hacc (seq_one ?_)) seq_nil
         simpa [WItem.OpsIn] using hC5 _ q (List.mem_filter.1 hq).1)
      | (simp only [WItem.OpsIn]; refine wOpsIn_disjW ?_; vars_ok)
      | simp [WItem.OpsIn, wOpsIn]
  wp_inv h
  obtain ⟨⟨B, s5⟩, h5, rfl, rfl⟩ := h
  obtain ⟨hC5, hB5⟩ := hB _ _ _ _ (hC.insert_nil (d + 1)) h5
  refine ⟨hC5.erase (d + 1), ?_⟩
  dsimp only
  seq_ok
  all_goals first
    | exact hB5
    | (refine seq_foldl_step (fun acc q hq hacc => seq_app hacc (seq_one ?_)) seq_nil
       simpa [WItem.OpsIn] using hC5 _ q (List.mem_filter.1 hq).1)
    | (refine setReach_ops _ (wOpsIn_disjW ?_); vars_ok)

variable [iLI : LawfulHasIdent P]

/-- A run of `wRen e` keeps the carried merges and returns `e` with a renaming. -/
private theorem wRen_ops {e : P.Expr} {st st' : WSt P} {we : WExpr P} {rd : List P.Ident}
    (h : (wRen e).run st = .ok ((we, rd), st')) {O : List P.Ident}
    (he : ∀ o ∈ HasOps.getOps e, o ∈ O) : st'.carries = st.carries ∧ wOpsIn O we := by
  obtain ⟨⟨ren, rfl, -⟩, -, hs, -⟩ := wRen_run h
  exact ⟨by rw [hs], he⟩

omit iO in
/-- A run of `wDecl x` keeps the carried merges. -/
private theorem wDecl_carries {x n : P.Ident} {st st' : WSt P}
    (h : (wDecl x).run st = .ok (n, st')) : st'.carries = st.carries := by
  rw [(wDecl_spec h).2.2.2.2]

omit iO in
/-- A run of `wName x` keeps the carried merges. -/
private theorem wName_carries {x n : P.Ident} {st st' : WSt P}
    (h : (wName x).run st = .ok (n, st')) : st'.carries = st.carries := by
  rw [(wName_state h).2]

/-- The walk of a command whose operators are in `O` has `OpsWalk O`. -/
private theorem opsWalk_cmd {O : List P.Ident} (κ : RE P) (d : Nat) (f : Bool) (c : CmdExt P)
    (hc : ∀ o ∈ Stmt.getOps (.cmd c : PStmt P), o ∈ O) : OpsWalk O (wpStmt κ d f (.cmd c)) := by
  intro st a st' hC h
  unfold wpStmt at h
  rcases c with ((⟨x, ty, e | _, md⟩ | ⟨x, e | _, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩) |
    ⟨p, args, md⟩)
  all_goals try first | cases h | (cases f; cases h; exact ⟨hC, by simp [Rope.toList_nil]⟩)
  all_goals wp_inv h
  · split at h <;> wp_inv h <;> obtain ⟨⟨⟨we, rd⟩, s1⟩, h1, ⟨n, s2⟩, h2, rfl, rfl⟩ := h
    all_goals
      obtain ⟨hc1, hw⟩ := wRen_ops h1 hc
      refine ⟨(wDecl_carries h2).trans hc1 ▸ hC, ?_⟩
      seq_ok
      all_goals item_ok
  · obtain ⟨⟨n, s2⟩, h2, rfl, rfl⟩ := h
    exact ⟨wDecl_carries h2 ▸ hC, by simp [Rope.toList_one, WItem.OpsIn]⟩
  · split at h <;> wp_inv h <;> obtain ⟨⟨⟨we, rd⟩, s1⟩, h1, ⟨n, s2⟩, h2, rfl, rfl⟩ := h
    all_goals
      obtain ⟨hc1, hw⟩ := wRen_ops h1 hc
      refine ⟨(wName_carries h2).trans hc1 ▸ hC, ?_⟩
      seq_ok
      item_ok
  · split at h <;> wp_inv h <;> obtain ⟨⟨n, s2⟩, h2, ⟨hv, s3⟩, h3, rfl, rfl⟩ := h
    all_goals
      cases (wFreshLike_run _ _).symm.trans h3
      refine ⟨wName_carries h2 ▸ hC, ?_⟩
      seq_ok
      all_goals item_ok
  all_goals
    obtain ⟨⟨⟨we, rd⟩, s1⟩, h1, rfl, rfl⟩ := h
    obtain ⟨hc1, hw⟩ := wRen_ops h1 hc
    refine ⟨hc1 ▸ hC, ?_⟩
    seq_ok
    item_ok

/-- The walk of a real branch on a condition with operators in `O`, whose arm walks have
    `OpsWalk O`, has it. -/
private theorem opsWalk_iteReal {O : List P.Ident} {κ : RE P} {d : Nat} {c : P.Expr}
    {tss ess : PStmts P} (hc : ∀ o ∈ HasOps.getOps c, o ∈ O)
    (hT : OpsWalk O (wpList .top d false tss)) (hE : OpsWalk O (wpList .top d false ess)) :
    OpsWalk O (wpIteReal κ d c tss ess) := by
  intro st a st' hC h
  unfold wpIteReal at h
  wp_inv h
  obtain ⟨⟨E, s2⟩, h2, ⟨T, s4⟩, h4, h⟩ := h
  obtain ⟨hC2, hE2⟩ := hE _ _ _ (by exact hC) h2
  obtain ⟨hC4, hT4⟩ := hT _ _ _ (by exact hC2) h4
  split at h
  · cases h
    exact ⟨hC4, by simp [Rope.toList_nil]⟩
  wp_inv h
  obtain ⟨⟨⟨wc, rdc⟩, s7⟩, h7, rfl, rfl⟩ := h
  obtain ⟨hc7, hw⟩ := wRen_ops h7 hc
  refine ⟨by rw [hc7]; exact hC4, ?_⟩
  dsimp only
  seq_ok
  all_goals try (simp only [WItem.OpsIn, WItem.listOpsIn_iff]; refine ⟨?_, ?_⟩ <;> seq_ok)
  all_goals item_ok

/-- The walk of a laid-out `ite` on a condition with operators in `O`, whose arm walks have
    `OpsWalk O`, has it. -/
private theorem opsWalk_iteLaid {O : List P.Ident} {κ : RE P} {d : Nat} {c : P.Expr}
    {tss ess : PStmts P} (hc : ∀ o ∈ HasOps.getOps c, o ∈ O)
    (hT : ∀ κ', OpsWalk O (wpList κ' d true tss)) (hE : ∀ κ', OpsWalk O (wpList κ' d true ess)) :
    OpsWalk O (wpIteLaid κ d c tss ess) := by
  intro st a st' hC h
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hctx h5 h6 h7 h8 h9 h10 _ h11 _
    h12 _ hEnd => ?_
  obtain ⟨hc1, hw⟩ := wRen_ops h1 hc
  cases (wFreshBool_run _ _).symm.trans h2
  cases (wFreshBool_run _ _).symm.trans h3
  have hC4 : CarOK O s4.carries := by
    rcases hctx with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, x, -, -, h4⟩
    · exact (hc1 ▸ hC : CarOK O s1.carries)
    · exact (hc1 ▸ hC : CarOK O s1.carries)
    · cases (wFreshBool_run _ _).symm.trans h4
      exact (hc1 ▸ hC : CarOK O s1.carries)
  obtain ⟨hC5, hE5⟩ := hE _ _ _ _ hC4 h5
  obtain ⟨hC6, hT6⟩ := hT _ _ _ _ hC5 h6
  obtain ⟨hc7, hsv3, hcp3, hrs3⟩ := saveRestore_ops (O := O) h7
  obtain ⟨hc8, hsvT, hcpT, hrsT⟩ := saveRestore_ops (O := O) h8
  obtain ⟨hc9, hsvE, hcpE, hrsE⟩ := saveRestore_ops (O := O) h9
  have hC12 : CarOK O s12.carries := by
    rw [h12.carries, h11.carries, h10.carries, hc9, hc8, hc7]
    exact hC6
  have hgm : wOpsIn O (optVar gm) := by cases gm <;> trivial
  have hC14 := (hC12.carryIns hgm (carryOf s6 cpsT T.tgt.max?) T.tgt.max?).carryIns
    (e := elseGuard κ gm qm rEm) (by unfold elseGuard; split <;> w_ok)
    (carryOf s6 cpsE E.tgt.max?) E.tgt.max?
  rcases hEnd with ⟨-, rfl, rfl⟩ | ⟨-, hl, rfl⟩
  · exact ⟨hC14, seq_nil⟩
  obtain ⟨live, clock, rfl, -⟩ := liveAdd_step hl
  refine ⟨hC14, seq_app (seq_one (by item_ok)) (seq_foldl_step ?_ seq_nil)⟩
  intro acc x hx hacc
  refine seq_app hacc ?_
  revert x
  simp only [List.forall_mem_cons]
  and_intros
  all_goals
    seq_ok
    repeat' (split <;> seq_ok)
  all_goals first
    | item_ok
    | exact fun _ h => absurd h List.not_mem_nil
    | (refine setReach_ops _ ?_; w_ok)
    | (refine seq_foldl_step (fun acc q _ hacc => seq_app hacc (seq_one ?_)) seq_nil
       simp only [WItem.OpsIn, Option.mem_def, Option.some.injEq, forall_eq']
       split <;> w_ok)

/-- Every statement-list walk of a list with operators in `O` has `OpsWalk O`. -/
private theorem opsWalk_list (O : List P.Ident) (ss : PStmts P) :
    ∀ (κ : RE P) (d : Nat) (fEnd : Bool), (∀ o ∈ Block.getOps ss, o ∈ O) →
      OpsWalk O (wpList κ d fEnd ss) := by
  induction ss using Stmt.rec_1 (motive_1 := fun s => ∀ (κ : RE P) (d : Nat) (f : Bool),
    (∀ o ∈ Stmt.getOps s, o ∈ O) → OpsWalk O (wpStmt κ d f s)) with
  | cmd c =>
    rename_i κ d f h
    exact opsWalk_cmd κ d f c h
  | exit l md =>
    rename_i κ d f _
    intro st a st' hC h
    unfold wpStmt at h
    cases κ <;> wp_inv h <;> (try split at h) <;> cases f <;> (try wp_inv h) <;>
      obtain ⟨rfl, rfl⟩ := h
    all_goals
      refine ⟨hC, ?_⟩
      simp [setReach, Rope.toList_one, Rope.toList_app, Rope.toList_nil, WItem.OpsIn, wOpsIn,
        kExpr, WExpr.not, WExpr.and]
  | block l body md ih =>
    rename_i κ d f h
    exact opsWalk_block md fun κB => ih κB (d + 1) f h
  | ite c tss ess md iht ihe =>
    rename_i κ d f h
    rcases c with c | _
    · have hc : ∀ o ∈ HasOps.getOps c, o ∈ O := fun o ho => h o (by simp [Stmt.getOps,
        ExprOrNondet.getOps, ho])
      have hT := fun κ' fE => iht κ' d fE fun o ho => h o (by simp [Stmt.getOps, ho])
      have hE := fun κ' fE => ihe κ' d fE fun o ho => h o (by simp [Stmt.getOps, ho])
      cases f <;> simp only [wpStmt, Bool.false_eq_true, ↓reduceIte]
      · exact opsWalk_iteReal hc (hT .top false) (hE .top false)
      · exact opsWalk_iteLaid hc (hT · true) (hE · true)
    · exact opsWalk_other κ d f _ ⟨nofun, nofun, nofun, nofun⟩
  | loop | typeDecl =>
    rename_i κ d f _
    exact opsWalk_other κ d f _ ⟨nofun, nofun, nofun, nofun⟩
  | nil =>
    intro κ d fEnd _ st r st' hC h
    simp only [wpList, StateT.run_pure] at h
    cases h
    exact ⟨hC, by simp [Rope.toList_nil]⟩
  | cons s rest ihs ihr =>
    intro κ d fEnd h st R st' hC hrun
    obtain ⟨r, st1, a, st2, h1, h2, hcase⟩ := wpList_run_cons hrun
    obtain ⟨hC1, hr1⟩ := ihr κ d fEnd (fun o ho => h o (List.mem_append_right _ ho)) _ _ _ hC h1
    obtain ⟨hC2, ha⟩ := ihs κ d _ (fun o ho => h o (List.mem_append_left _ ho)) _ _ _ hC1 h2
    rcases hcase with ⟨-, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
    · exact ⟨hC2, ha⟩
    · exact ⟨hC2, ha⟩
    · refine ⟨hC2, fun it hit => ?_⟩
      simp only [WRes.combine, Rope.toList_app, List.mem_append] at hit
      exact hit.elim (ha it) (hr1 it)

/-- **The WP phase references no new operator**: every operator of the guarded program of the
    loop-free list `ss` (the operators of its commands and of its `ite` conditions,
    `Block.getOps`) is an operator of `ss`, for an expression language whose conditional,
    Boolean literals, variables and substitution add no operator (`OpsLaws`). -/
theorem wpEntry_ops (hL : OpsLaws P) {G : IdSet P} {tys : Tys P} {ss : PStmts P} {w : WOut P}
    (h : wpEntry G tys ss = .ok w) : ∀ o ∈ Block.getOps w.lay, o ∈ Block.getOps ss := by
  simp only [wpEntry, wpBody, StateT.run, Except.bind_is_ok, Except.pure_is_ok] at h
  obtain ⟨⟨r, st1⟩, hrun, lay, hlay, rfl⟩ := h
  obtain ⟨-, hr⟩ := opsWalk_list (Block.getOps ss) ss .top 0 false (fun _ h => h) _ r st1
    (fun _ _ hq => by simp at hq) hrun
  exact emit_ops hL hlay (WItem.listOpsIn_iff.2 hr)

end

end -- public section

end WP
end Imperative
