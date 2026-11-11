/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
public import Strata.Transform.WP.WPOverEmit
public import Strata.Transform.WP.WPOverEval
import Strata.Transform.WP.WPOverFacts
import Strata.DL.Imperative.PureExprProps
import Strata.Util.ExceptProps
import Strata.Util.OrderedSetProps

/-! # The simulation through blocks

The walk of a block has the simulation property (`Spec`) when the walks of its body have it.
The body is walked under the block's context, or under a fresh `rL` (initialised to `true`)
at top level; at the block's end the carried merges of the body's always-exiting arms deliver
the exit values of their variables, the exits to the block rejoin through the join
(`setReach`, or the assumption `[wp$join]` at top level), and the projection of the loop-free
store drops the body's locals.

Key theorems: `stmtSpec_block`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep Classical

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iHS : HasSubstFvar P] [iHI : HasIdent P]
  [iL : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHV : HasFvars P]
  [iW : WPLang P] [iIL : WPIteLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLV : LawfulHasFvars P] [iLVal : LawfulHasVal P]
omit iIL
variable {tE : TypedEval P}

variable {F : P.Factory} {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}
  {Lc S V V' vs tg ms : List P.Ident} {Ex : P.Ident → Prop} {κ : RE P} {d clock i t : Nat}
  {f : Bool} {l : String} {body : PStmts P} {md : MetaData P} {st st1 st' stB sa sb : WSt P}
  {B r : WRes P} {live : Std.HashMap P.Ident Nat} {σ σL σ0 σL' σa σb σ1 : SemanticStore P}
  {sel : P.Ident × WExpr P × P.Ident → Bool} {tyf : P.Ident → P.Ty} {n xB rL : P.Ident}
  {X : WExpr P} {its iJ iM : List (Item P)} {x : P.Expr} {w : P.Val} {K : Outcome P → Prop}


/-! ## The walk of a block -/

/-- The walk state the body of a block labelled `l` at depth `d` is walked from. -/
private def blkIn (st : WSt P) (l : String) (d : Nat) : WSt P :=
  { st with
    labelDepth := st.labelDepth.insert l (d + 1)
    pending := st.pending.insert l []
    stampAt := st.stampAt.insert (d + 1) st.clock
    carries := st.carries.insert (d + 1) [] }

section

omit iL iW iOp iLF iLV iLVal

/-- Entering a block labelled `l` at depth `d + 1` (state `s'`, with the live set of `st`) keeps
    a live name live before the enclosing blocks from depth `t` on, given that it was before
    those of `st` other than `l` at a depth other than `d + 1`: the new block is stamped with the
    clock, above every live stamp. -/
private theorem liveFrom_enter {s' : WSt P} (hwf : WFSt st) (hlive : s'.live = st.live)
    (hld : s'.labelDepth = st.labelDepth.insert l (d + 1))
    (hsa : s'.stampAt = st.stampAt.insert (d + 1) st.clock) (hl : st.live.contains n = true)
    (h : ∀ l' j, st.labelDepth[l']? = some j → l' ≠ l → j ≠ d + 1 → t ≤ j →
      liveBefore st n (st.stampAt.getD j 0) = true) : LiveFrom s' t n := by
  grind [LiveFrom, liveBefore, hwf.live_stamp, Std.HashMap.contains_eq_isSome_getElem?]

/-- The walk state after a block, before the final `liveAdd`. -/
private def blkOut (st st1 : WSt P) (l : String) (d : Nat) : WSt P :=
  { st1 with
    labelDepth := match st.labelDepth[l]? with
      | some v => st1.labelDepth.insert l v
      | none => st1.labelDepth.erase l
    pending := match st.pending[l]? with
      | some v => st1.pending.insert l v
      | none => st1.pending.erase l
    carries := st1.carries.erase (d + 1) }

/-- The live snapshots of the exits to the block. -/
private def blkSnaps (st1 : WSt P) (l : String) : List P.Ident :=
  ((st1.pending.getD l []).filter fun e => !st1.dead.contains e).reverse

/-- The live carried merges at the block's depth. -/
private def blkCarr (st1 : WSt P) (d : Nat) : List (P.Ident × WExpr P × P.Ident) :=
  (st1.carries.getD (d + 1) []).filter fun (_, _, k) => !st1.dead.contains k

/-- The merges of a block, under a variable context. -/
private abbrev mergesOf (st1 : WSt P) (d : Nat) : Rope (WItem P) :=
  (blkCarr st1 d).foldl (fun acc (x, v, _) => acc.app (.one (.set x (some v)))) .nil

include iW in
/-- A run of the walk of a block under a variable context. -/
private theorem walk_var (hκ : κ ≠ .top)
    (h : (wpStmt κ d f (.block l body md)).run st = .ok (r, st')) :
    ∃ B st1, (wpList κ (d + 1) f body).run (blkIn st l d) = .ok (B, st1) ∧
      (liveAdd (RE.vars κ)).run (blkOut st st1 l d) = .ok ((), st') ∧
      r.out = (B.out.app (mergesOf st1 d)).app (if !f then .nil
        else if (blkSnaps st1 l).isEmpty then .nil
        else setReach κ (disjW (kExpr κ :: (blkSnaps st1 l).map .var))) ∧
      r.sk = [.block B.sk] ∧ r.hasObl = B.hasObl ∧ r.ax = (B.ax && (blkSnaps st1 l).isEmpty) ∧
      r.drop = false ∧ r.regs = B.regs := by
  simp only [wpStmt, StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind,
    Except.bind_is_ok] at h
  obtain ⟨⟨B, st1⟩, hB, ⟨u, st2⟩, hL, ⟨⟩⟩ := h
  exact ⟨B, st1, hB, hL, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The walk state the body of a top-level block is walked from, after drawing `rL`. -/
private def stTop (st : WSt P) (l : String) (d : Nat) (rL : P.Ident) (n1 : Nat) : WSt P :=
  { blkIn st l d with next := n1, tys := st.tys.insert rL HasBool.boolTy }

include iW in
/-- A run of the walk of a block at top level, the body under the fresh `rL`. -/
private theorem walk_top {n1 : Nat} (hf : freshIn st.avoid "r" st.next = (rL, n1))
    (h : (wpStmt .top d f (.block l body md)).run st = .ok (r, st')) :
    ∃ B st1, (wpList (.name rL) (d + 1) f body).run (stTop st l d rL n1) = .ok (B, st1) ∧
      (liveAdd (RE.vars (P := P) .top)).run (blkOut st st1 l d) = .ok ((), st') ∧
      ∃ J tail, J = (if !f then .nil else if leOpt B.minT d then
          .one (.assume joinLabel (disjW (.var rL :: (blkSnaps st1 l).map .var)) .empty)
          else .nil) ∧ tail = (B.out.app (mergesOf st1 d)).app J ∧
      r.out = (if tail.isNil then .nil else
          Rope.app (.one (.init rL (.known HasBool.boolTy) (some (.lit true)))) tail) ∧
      r.sk = [.block B.sk] ∧ r.hasObl = B.hasObl ∧ r.ax = (B.ax && (blkSnaps st1 l).isEmpty) ∧
      r.drop = false ∧ r.regs = B.regs := by
  rw [wpStmt] at h
  simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind, wFreshBool_run, hf,
    Except.bind_is_ok] at h
  obtain ⟨⟨rL', s0⟩, ⟨⟩, ⟨B, st1⟩, hB, ⟨u, st2⟩, hL, ⟨⟩⟩ := h
  exact ⟨B, st1, hB, hL, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
/-! ## Walk states -/

/-- Two walk states with the same renamings, recorded declarations, counter and avoided
    names. -/
private def SameNames (sa sb : WSt P) : Prop :=
  sa.nm = sb.nm ∧ sa.taken = sb.taken ∧ sa.next = sb.next ∧ sa.avoid = sb.avoid

/-- `FreshInv` for fewer bound names, at a state with the same renamings, declarations and
    avoided names and a smaller counter, the excepted names being excepted or drawn from the
    smaller counter on. -/
private theorem FreshInv.mono {Ex' : P.Ident → Prop} (h : FreshInv Lc Ex sb σL)
    (hnm : sa.nm = sb.nm) (ht : sa.taken = sb.taken) (hav : sa.avoid = sb.avoid)
    (hn : sa.next ≤ sb.next) (hEx : ∀ y, Ex y → Ex' y ∨ ∀ b j, y = freshName b j → sa.next ≤ j)
    (hd : ∀ y, (σL' y).isSome → (σL y).isSome) : FreshInv Lc Ex' sa σL' := by grind [FreshInv]

/-- `FreshInv` at a state with the same names, for fewer bound names. -/
private theorem FreshInv.congr (h : FreshInv Lc Ex sa σL) (hs : SameNames sa sb)
    (hd : ∀ y, (σL' y).isSome → (σL y).isSome) : FreshInv Lc Ex sb σL' :=
  h.mono hs.1.symm hs.2.1.symm hs.2.2.2.symm (Nat.le_of_eq hs.2.2.1.symm) (fun _ h => .inl h) hd

include iW in
/-- `OnInv` carries over to a state with the same names and fewer live names, for fewer read
    variables. -/
private theorem OnInv.transfer (h : OnInv F T Y Lc Ex sa κ S V σ σL) (hs : SameNames sa sb)
    (hl : ∀ n, sb.live.contains n = true → sa.live.contains n = true) (hV : V' ⊆ V) :
    OnInv F T Y Lc Ex sb κ S V' σ σL := by
  obtain ⟨⟨ha, hd, hal, hu, hc0, hcL, hg, hlt, hf⟩, hr⟩ := h
  have hc := curName_eq_of_nm_taken hs.1 hs.2.1
  refine ⟨⟨?_, ?_, ?_, hu, hc0, hcL, hg, ?_, hf.congr hs fun _ => id⟩, hr⟩ <;> grind

include iW in
/-- `OffInv` carries over to a state with the same names, for fewer read variables. -/
private theorem OffInv.transfer (h : OffInv F T Y Lc Ex sa κ S V σL) (hs : SameNames sa sb)
    (hV : V' ⊆ V) : OffInv F T Y Lc Ex sb κ S V' σL :=
  ⟨h.canonL, h.reach, h.bools, fun x hx hv n hn => h.defd x hx (hV hv) n
    (curName_eq_of_nm_taken hs.1 hs.2.1 x ▸ hn), h.gtyped, h.fresh.congr hs fun _ => id⟩

/-- The label depths seen by the body of a block labelled `l` at depth `d`. -/
private theorem blkIn_labelDepth (st : WSt P) (l l' : String) (d : Nat) :
    (blkIn st l d).labelDepth[l']? = if l = l' then some (d + 1) else st.labelDepth[l']? := by
  simp [blkIn, Std.HashMap.getElem?_insert]

/-- The snapshots pending for a label after a block: those of the body's output for another
    label, those of the block's input for the block's own label. -/
private theorem blkOut_pending (st st1 : WSt P) (l l' : String) (d : Nat) :
    (blkOut st st1 l d).pending.getD l' [] =
      if l = l' then st.pending.getD l [] else st1.pending.getD l' [] := by
  unfold blkOut; split <;> grind [Std.HashMap.getD_eq_getD_getElem?]

/-! ## Syntax -/

omit iDE iHB iHF iHS iHI in
/-- The continuation of a block's body reads what the block's continuation reads. -/
private theorem contFV_body_sub
    {k : List (PStmts P)} : contFV (body :: k) ⊆ contFV ([.block l body md] :: k) := fun x => by
  simp [contFV, Strata.Util.OrderedSet.mem_eraseDups, Block.freeVars, Stmt.freeVars]

/-- The label map of a block's body: the variables of the scope read after the block, for its
    own label. -/
private theorem lab_body {k : List (PStmts P)} {Lab : String → List P.Ident}
    (hLab : ∀ l t, st.labelDepth[l]? = some t → t ≤ d ∧ ∀ x ∈ Lab l, x ∈ contFV k ∧ x ∈ S) :
    ∀ (l' : String) (t : Nat), (blkIn st l d).labelDepth[l']? = some t → t ≤ d + 1 ∧
      ∀ x ∈ (fun l'' => if l'' = l then (contFV k).filter (· ∈ S) else Lab l'') l',
        x ∈ contFV k ∧ x ∈ S := by grind [blkIn_labelDepth]

end

omit iLB iHI iL iOp iLF iLV iLVal in
/-- The resolved output of a block under a variable context: the body's, the merges', the
    join's. -/
private theorem resolve_out3 {a b c : Rope (WItem P)} {items : List (Item P)}
    (h : resolveItems T Y ((a.app b).app c).toList = .ok items) :
    ∃ ia ib ic, resolveItems T Y a.toList = .ok ia ∧ resolveItems T Y b.toList = .ok ib ∧
      resolveItems T Y c.toList = .ok ic ∧ items = ia ++ ib ++ ic := by
  simp only [Rope.toList_app, resolveItems_append] at h
  grind

/-! ## Joins: making the reach context equal an expression -/

omit iLB iHI iL iOp iLF iLV iLVal in
/-- A one-`set` item list resolves to the `set` of the resolved expression. -/
private theorem resolve_set1 {v : P.Ident} (h : resolveItems T Y [.set v (some X)] = .ok its) :
    ∃ e', resolveE T Y X = .ok e' ∧ its = [.plain (.cmd (.cmd (.set v (.det e') .empty)))] := by
  grind [resolveItems, resolveItem, resolveOE, Except.bind_is_ok, Except.pure_is_ok]

omit iBE iLB iHB iHF iHS iHI iL iHa iHV iW iOp iLF iLV iLVal in
/-- Updating a variable to the value it holds leaves the store unchanged. -/
private theorem update_self {v : P.Ident} (h : σ v = some w) : σ.update v w = σ := by
  funext y; by_cases hy : y = v <;> simp_all [SemanticStore.update]

section

omit iLB iHI iL iLV

omit iLVal in
include iIL in
/-- Under a reach context that holds, the join `κ ∨ snapshots` evaluates to `tt`. -/
private theorem ev_join_holds (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F)
    (hκ : κ.Holds F σ)
    (hall : ∀ e ∈ ms, σ e = some (HasBool.ttVal F) ∨ σ e = some (HasBool.ffVal F))
    (h : resolveE T Y (disjW (kExpr κ :: ms.map .var)) = .ok x) :
    P.eval F σ x = some (HasBool.ttVal F) := by
  cases ms with
  | nil => exact ev_kExpr_holds hF hC hκ h
  | cons e ms =>
    refine ev_or_tt hF h (fun _ => ev_kExpr_holds hF hC hκ) (resBool_disjW hF fun a ha => ?_)
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    exact resBool_var hF hC (hall y hy)

omit iLVal in
include iIL in
/-- Under a false reach context, the join `κ ∨ snapshots` evaluates to `tt` when one snapshot
    is `tt` and the others are Booleans. -/
private theorem ev_join_exit (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F)
    (hκ : κ.Fails F σ)
    (hκb : ∀ y ∈ RE.vars κ, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F))
    (hall : ∀ e ∈ ms, σ e = some (HasBool.ttVal F) ∨ σ e = some (HasBool.ffVal F))
    (hex : ∃ e ∈ ms, σ e = some (HasBool.ttVal F))
    (h : resolveE T Y (disjW (kExpr κ :: ms.map .var)) = .ok x) :
    P.eval F σ x = some (HasBool.ttVal F) := by
  refine ev_disjW_tt hF (by grind [ev_kExpr_fails hF hC hκ hκb, ev_res_var hF hC]) ?_ h
  obtain ⟨e, he, het⟩ := hex
  exact ⟨.var e, .tail _ (List.mem_map_of_mem he), fun _ h' => ev_res_var hF hC het h'⟩

omit iOp iLF iLVal in
include iIL in
/-- Making a reach context equal an expression evaluating to `tt`: the context holds after,
    only its variables change, and nothing changes when it held before. -/
private theorem setReach_tt (hF : WellFormedSemanticEvalBase F) (hκ : κ ≠ .top)
    (hres : resolveItems T Y (setReach κ X).toList = .ok its)
    (hX : ∀ x, resolveE T Y X = .ok x → P.eval F σ x = some (HasBool.ttVal F)) (hH0 : κ.Holds F σ0)
    (hb : κ.Holds F σ ∨ κ.Fails F σ) (hq : ∀ q g, κ = .andNeg q g → σ q = some (HasBool.ttVal F)) :
    ∃ σ', MainRun F its σ [] σ' ∧ κ.Holds F σ' ∧ (∀ y, y ∉ RE.vars κ → σ' y = σ y) ∧
      (∀ y, (σ' y).isSome = (σ y).isSome) ∧ (κ.Holds F σ → σ' = σ) ∧
      ∀ y ∈ RE.vars κ, σ' y = σ0 y := by
  cases κ <;> simp only [setReach, Rope.toList_one] at hres
  · exact absurd rfl hκ
  all_goals
    obtain ⟨e', he', rfl⟩ := resolve_set1 hres
    first
    | refine ⟨_, set_run hF (hX e' he') (by grind [RE.Holds, RE.Fails]) (.inl rfl), ?_⟩
    | refine ⟨_, set_run hF (ev_not_tt hF he' hX)
        (by grind [RE.Holds, RE.Fails, HasBool.tt_is_not_ff, HasBool.ttVal_ne_ffVal])
        (.inr rfl), ?_⟩
    grind [RE.Holds, RE.Fails, RE.vars, SemanticStore.update, update_self,
      HasBool.tt_is_not_ff, HasBool.ttVal_ne_ffVal]

omit iOp iLF iLVal in
/-- The join of a block under a variable context resolves to nothing when no exit to the block
    is live, and to the resolved `setReach` otherwise. -/
private theorem join_cases
    (h : resolveItems T Y (if ms.isEmpty then .nil
      else setReach κ (disjW (kExpr κ :: ms.map .var))).toList = .ok iJ) :
    (ms = [] ∧ iJ = []) ∨
      (ms ≠ [] ∧ resolveItems T Y (setReach κ (disjW (kExpr κ :: ms.map .var))).toList =
        .ok iJ) := by cases ms <;> simp_all [Rope.toList_nil, resolveItems, pure, Except.pure]

omit iLVal in
include iIL in
/-- The join of a block under a false reach context whose live exit snapshots `ms` are `ff`: it
    runs, the context stays false, only its variables change (to `tt`, from a Boolean), and
    nothing changes when the enclosing context of `q ∧ ¬g` holds. -/
private theorem join_ff (hF : WellFormedSemanticEvalBase F) (hκ : κ ≠ .top)
    (hres : resolveItems T Y (if ms.isEmpty then .nil
      else setReach κ (disjW (kExpr κ :: ms.map .var))).toList = .ok its) (hC : WellFormedStore σ F)
    (hall : ∀ e ∈ ms, σ e = some (HasBool.ffVal F)) (hf : κ.Fails F σ)
    (hb : ∀ q g, κ = .andNeg q g → σ g = some (HasBool.ttVal F) ∨ σ g = some (HasBool.ffVal F)) :
    ∃ σ', MainRun F its σ [] σ' ∧ κ.Fails F σ' ∧ (∀ y, y ∉ RE.vars κ → σ' y = σ y) ∧
      (∀ y, (σ' y).isSome = (σ y).isSome) ∧
      (∀ y v, σ' y = some v → σ y = some v ∨ (v = HasBool.ttVal F ∧ ∃ v0, σ y = some v0 ∧
          (v0 = HasBool.ttVal F ∨ v0 = HasBool.ffVal F))) ∧
      ((∀ q g, κ = .andNeg q g → σ q = some (HasBool.ttVal F)) → σ' = σ) := by
  rcases join_cases hres with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · exact ⟨σ, .nil, hf, fun _ _ => rfl, fun _ => rfl, fun _ _ h => .inl h, fun _ => rfl⟩
  have hJ : ∀ x, resolveE T Y (disjW (kExpr κ :: ms.map .var)) = .ok x →
      P.eval F σ x = some (HasBool.ffVal F) :=
    fun _ h => ev_disjW_ff hF (by grind [ev_kExpr_fails hF hC hf (hf.bools hb), ev_res_var hF hC]) h
  cases κ <;> simp only [setReach, Rope.toList_one] at h
  · exact absurd rfl hκ
  all_goals
    obtain ⟨e', he', rfl⟩ := resolve_set1 h
    first
    | refine ⟨_, set_run hF (hJ _ he') (by grind [RE.Fails]) (.inr rfl), ?_⟩
    | refine ⟨_, set_run hF (ev_not_ff hF he' fun _ => hJ _) (by grind [RE.Fails]) (.inl rfl), ?_⟩
    grind [RE.Fails, RE.vars, SemanticStore.update, update_self,
      HasBool.tt_is_not_ff, HasBool.ttVal_ne_ffVal]

end

/-! ## Sequences of carried merges -/

/-- The items of the merges `set x v` of carried entries `(x, v, xB)`. -/
private def mergeItems (Ms : List (P.Ident × WExpr P × P.Ident)) : List (WItem P) :=
  Ms.map fun e => .set e.1 (some e.2.1)

/-- The effect of one carried merge on a store, its selection `sel` and copy values taken from
    the store `σ0` before the merges. -/
private def mstep (σ0 : SemanticStore P) (sel : P.Ident × WExpr P × P.Ident → Bool)
    (σ : SemanticStore P) (e : P.Ident × WExpr P × P.Ident) : SemanticStore P :=
  if sel e then (match σ0 e.2.2 with | some w => σ.update e.1 w | none => σ) else σ

section

omit iBE iLB iHB iHF iHS iHI iL iHa iHV iW iOp iLF iLV iLVal

/-- Merges change only their targets. -/
private theorem mstore_off :
    ∀ (Ms : List (P.Ident × WExpr P × P.Ident)) (σ : SemanticStore P) (y : P.Ident),
      y ∉ Ms.map (·.1) → Ms.foldl (mstep σ0 sel) σ y = σ y
  | [], _, _, _ => rfl
  | e :: Ms, σ, y, hy => by
    rw [List.foldl_cons, mstore_off Ms _ y fun h => hy (.tail _ h), mstep]
    cases σ0 e.2.2 <;> split <;> simp_all [SemanticStore.update]

/-- Merges none of which selects change nothing. -/
private theorem mstore_none (Ms : List (P.Ident × WExpr P × P.Ident))
    (h : ∀ e ∈ Ms, sel e = false) : Ms.foldl (mstep σ0 sel) σ = σ := by
  induction Ms generalizing σ <;> grind [mstep]

/-- After merges, a name holds its value before them when no merge of it selects, and the copy
    of the selecting merge of it with the largest index otherwise. -/
private theorem mstore_val (Ms : List (P.Ident × WExpr P × P.Ident))
    (hs : ∀ e ∈ Ms, sel e = true → (σ0 e.2.2).isSome) (y : P.Ident) :
    ((∀ (i : Nat) e, Ms[i]? = some e → e.1 = y → sel e = false) ∧
      Ms.foldl (mstep σ0 sel) σ y = σ y) ∨
    ∃ (i : Nat) (e : _), Ms[i]? = some e ∧ e.1 = y ∧ sel e = true ∧
      Ms.foldl (mstep σ0 sel) σ y = σ0 e.2.2 ∧
      ∀ (i' : Nat) e', Ms[i']? = some e' → e'.1 = y → sel e' = true → i' ≤ i := by
  induction Ms generalizing σ with
  | nil => simp
  | cons e Ms ih =>
    rcases ih (σ := mstep σ0 sel σ e) fun e' he' => hs e' (.tail _ he') with
      ⟨hn, hv⟩ | ⟨i, e', hi, hy, hse, hv, hmax⟩
    · by_cases hey : e.1 = y ∧ sel e = true
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hs e (.head _) hey.2)
        refine .inr ⟨0, e, rfl, hey.1, hey.2, ?_, fun i' e'' h hy' hs' => by cases i' <;> grind⟩
        rw [List.foldl_cons, hv]; simp [mstep, hey, hw, SemanticStore.update]
      · refine .inl ⟨fun i' e'' h hy' => by cases i' <;> grind, ?_⟩
        rw [List.foldl_cons, hv, mstep]
        split <;> (try cases σ0 e.2.2) <;> grind [SemanticStore.update]
    · exact .inr ⟨i + 1, e', hi, hy, hse, hv, fun i' e'' h hy' hs' => by cases i' <;> grind⟩

/-- Merges over a filtered list are merges over the list selecting only the kept entries. -/
private theorem mstore_filter (p : P.Ident × WExpr P × P.Ident → Bool) :
    ∀ (Ms : List (P.Ident × WExpr P × P.Ident)) (σ : SemanticStore P),
      (Ms.filter p).foldl (mstep σ0 sel) σ = Ms.foldl (mstep σ0 fun e => p e && sel e) σ := by
  intro Ms; induction Ms <;> grind [mstep]

end

omit iLB iHI iL iOp iLF iLVal in
/-- The free variables of a resolved selector condition are its variables. -/
private theorem fv_resolve_simple :
    ∀ (c : WExpr P) {c' : P.Expr}, wsimple c → resolveE T Y c = .ok c' →
      ∀ y ∈ HasFvars.getFvars c', y ∈ wvars c := fun c => by
  induction c <;> intro c' hs h y hy
  · exact hs.elim
  · exact (resolveE_var h).elim fun ty h =>
      List.mem_singleton.2 (HasFvar.eq_of_mem_getFvars_mkVar (h ▸ hy))
  · cases ‹Bool› <;> cases h <;> simp_all [WPLang.getFvars_tt, WPLang.getFvars_ff]
  · grind [wvars, wsimple, WPLang.getFvars_ite, resolveE_ite]

/-- The invariant of a store during carried merges with targets `tg`: it agrees with the store
    `σ0` before the merges off the targets, binds every target to a value of its type `tyf`,
    and holds values. -/
private def MInv (F : P.Factory) (tg : List P.Ident) (tyf : P.Ident → P.Ty)
    (σ0 σ : SemanticStore P) : Prop :=
  (∀ y, y ∉ tg → σ y = σ0 y) ∧ (∀ y ∈ tg, ∃ w, σ y = some w ∧ HasVal.valueOfTy F w (tyf y)) ∧
    WellFormedStore σ F

omit iLB iHI iL iLV iLVal in
include iIL in
/-- The resolved merges of carried entries run, each selecting merge giving its target the
    value of its copy before the merges: every merge `set x (ite(c, xB, x))` has a selector
    condition evaluating to its selection in every store agreeing with `σ0` off the targets,
    and a copy that is no target holding a value of the target's type. -/
private theorem merges_run (hF : WellFormedSemanticEvalBase F)
    (hC0 : WellFormedStore σ0 F) : ∀ (Ms : List (P.Ident × WExpr P × P.Ident)) {iM : List (Item P)},
      resolveItems T Y (mergeItems Ms) = .ok iM → (∀ e ∈ Ms, e.1 ∈ tg) →
      (∀ e ∈ Ms, ∃ c, e.2.1 = .ite c (.var e.2.2) (.var e.1) ∧ ∀ σ, (∀ y, y ∉ tg → σ y = σ0 y) →
        WellFormedStore σ F → ∀ c', resolveE T Y c = .ok c' → P.eval F σ c' = some
            (if sel e then HasBool.ttVal F else HasBool.ffVal F)) →
      (∀ e ∈ Ms, e.2.2 ∉ tg) →
      (∀ e ∈ Ms, ∃ w, σ0 e.2.2 = some w ∧ HasVal.valueOfTy F w (tyf e.1)) →
      ∀ σ, MInv F tg tyf σ0 σ →
        MainRun F iM σ [] (Ms.foldl (mstep σ0 sel) σ) ∧ MInv F tg tyf σ0 (Ms.foldl (mstep σ0 sel) σ)
  | [], _, h, _, _, _, _, σ, hI => ⟨Except.ok.inj h ▸ .nil, hI⟩
  | e :: Ms, _, h, htg, hc, hxB, hcp, σ, ⟨hoff, hon, hCs⟩ => by
    simp only [List.mem_cons, forall_eq_or_imp] at htg hc hxB hcp
    obtain ⟨i0, iR, hi0, hiR, rfl⟩ := resolveItems_cons_ok h
    obtain ⟨e', he', rfl⟩ := resolveItem_set hi0
    obtain ⟨c, hv, hcev⟩ := hc.1
    obtain ⟨c', t', f', h1, h2, h3, rfl⟩ := resolveE_ite.1 (hv ▸ he')
    obtain ⟨p, hp, hpty⟩ := hon e.1 htg.1
    have hcv := hcev σ hoff hCs c' h1
    obtain ⟨wB, hwB, hwBty⟩ := hcp.1
    have hB := ev_res_var hF hCs ((hoff _ hxB.1).trans hwB) h2
    obtain ⟨w, hw, hwty, hstep, hwC⟩ : ∃ w, P.eval F σ (WPOps.ite c' t' f') = some w ∧
        HasVal.valueOfTy F w (tyf e.1) ∧ mstep σ0 sel σ e = σ.update e.1 w ∧ HasVal.value F w := by
      cases hs : sel e
      · exact ⟨p, WPIteLang.ev_ite_false (by simpa [hs] using hcv) hB (ev_res_var hF hCs hp h3) hpty
          hwBty, hpty, by simp [mstep, hs, update_self hp], hCs _ _ hp⟩
      · exact ⟨wB, WPIteLang.ev_ite_true (by simpa [hs] using hcv) hB (ev_res_var hF hCs hp h3)
          hwBty hpty, hwBty, by simp [mstep, hs, hwB], hC0 _ _ hwB⟩
    have hu := update_facts σ e.1 w
    have hI' : MInv F tg tyf σ0 (σ.update e.1 w) := by
      refine ⟨fun y hy => ?_, fun y hy => ?_, fun y v hv => ?_⟩ <;>
        by_cases hyx : e.1 = y <;> grind [SemanticStore.update, WellFormedStore]
    obtain ⟨hrun, hI''⟩ := merges_run hF hC0 Ms hiR htg.2 hc.2 hxB.2 hcp.2 _ hI'
    rw [List.foldl_cons, hstep]
    exact ⟨.plain (c := .cmd (.set e.1 (.det _) .empty)) (evs1 := []) (evs2 := [])
      (.eval_set hw (.update hp hu.1 hu.2) ⟨p, tyf e.1, hp, hpty, hwty⟩ (hF.var)) hrun, hI''⟩

/-! ## The relations after a block -/

omit iL iOp iLF iLV iLVal in
/-- Leaving a block: the relation `OnCore` for the projected loop-free store at scope `S` and
    reads `V` (variables of `S` read later defined before the block, locals out of `S`
    undefined before it), from the facts at the body's end on the read variables of `S`. -/
private theorem onCore_mk
    (hag : ∀ x ∈ S, x ∈ V → ∀ n, curName sa x = some n → sa.live.contains n = true → σL n = σ1 x)
    (hdd : ∀ x ∈ S, x ∈ V → (σ1 x).isSome ∧ ∀ n, curName sa x = some n → (σL n).isSome)
    (hal : ∀ x ∈ S, x ∈ V → ∀ n, curName sa x = some n → (∀ ty, tyOfName T Y n ≠ .ok ty) →
      ∀ w w', σ1 x = some w → σL n = some w' → ∀ ty, HasVal.valueOfTy F w ty →
      HasVal.valueOfTy F w' ty) (hdef : ∀ x ∈ S, x ∈ V → (σ x).isSome)
    (hun : ∀ x ∈ Lc, x ∉ S → σ x = none) (hC1 : WellFormedStore σ1 F) (hCL : WellFormedStore σL F)
    (hgt : ∀ n w, σL n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty)
    (hlt : ∀ x ∈ S, x ∈ V → ∀ n, curName sa x = some n → ∀ w, σ1 x = some w →
      ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty)
    (hfr : FreshInv Lc Ex sa σL) : OnCore F T Y Lc Ex sa S V (projectStore σ σ1) σL := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hCL, hgt, ?_, hfr⟩ <;> grind [projectStore, WellFormedStore]

omit iL iOp iLF iLV iLVal in
/-- Leaving a block: `OnCore` at the body's end (scope `S'`, reads `V0`) gives `OnCore` for the
    projected loop-free store at scope `S` and reads `V`, at a state with the same current
    names and fewer live names, for a guarded store that differs only on names `D` that are
    not current names of the read variables. -/
private theorem OnCore.proj {Ex0 : P.Ident → Prop} {S' V0 : List P.Ident} {D : List P.Ident}
    (h : OnCore F T Y Lc Ex0 sb S' V0 σ1 σL) (hS : S ⊆ S') (hV : ∀ x ∈ S, x ∈ V → x ∈ V0)
    (hdef : ∀ x ∈ S, x ∈ V → (σ x).isSome) (hun : ∀ x ∈ Lc, x ∉ S → σ x = none)
    (hcn : ∀ x, curName sa x = curName sb x)
    (hl : ∀ n, sa.live.contains n = true → sb.live.contains n = true)
    (hD : ∀ y, y ∉ D → σL' y = σL y) (hCL : WellFormedStore σL' F)
    (hgt : ∀ n w, σL' n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) (hcur : ∀ x ∈ S, x ∈ V → ∀ n, curName sb x = some n → n ∉ D)
    (hfr : FreshInv Lc Ex sa σL') : OnCore F T Y Lc Ex sa S V (projectStore σ σ1) σL' := by
  obtain ⟨ha, hd, hal, -, hC1, -, -, hlt, -⟩ := h
  refine onCore_mk ?_ ?_ ?_ hdef hun hC1 hCL hgt ?_ hfr <;> grind

/-- The state after a block under a variable context, from the body's walk output. -/
private abbrev blkFin (st st1 : WSt P) (l : String) (d : Nat) (live : Std.HashMap P.Ident Nat)
    (clock : Nat) : WSt P :=
  { blkOut st st1 l d with live := live, clock := clock }

section

omit iL iW iOp iLF iLV iLVal

/-- The live snapshots of the exits to the block are pending for its label. -/
private theorem mem_blkSnaps {e : P.Ident} :
    e ∈ blkSnaps st1 l ↔ e ∈ st1.pending.getD l [] ∧ st1.dead.contains e = false := by
  simp [blkSnaps]

/-- The snapshots a block registered (those of its body) and that are pending after it are
    false when the body's snapshots pending for other labels than the block's are. -/
private theorem snapFF_blk (hregs : r.regs = B.regs)
    (hold : ∀ e ∈ B.regs.toList, e ∉ st.pending.getD l []) {ex : Option P.Ident}
    (h : ∀ l0 e, e ∈ B.regs.toList → l ≠ l0 → e ∈ st1.pending.getD l0 [] → some e ≠ ex →
      σL e = some (HasBool.ffVal F)) : SnapFF F r (blkFin st st1 l d live clock) ex σL := by
  grind [SnapFF, blkOut_pending]

/-- The exits of a block to labels other than `ex` satisfy `K` when those of its body to labels
    other than the block's and `ex'` satisfy `K` after leaving the block. -/
private theorem exitEnds_blk (hregs : r.regs = B.regs)
    (hold : ∀ e ∈ B.regs.toList, e ∉ st.pending.getD l []) {ex ex' : Option String}
    (hex : ∀ l1, l ≠ l1 → some l1 ≠ ex → some l1 ≠ ex')
    (hE : ExitEnds B st1 ex' (fun o => K (o.block l σ))) :
    ExitEnds r (blkFin st st1 l d live clock) ex K := by
  grind [ExitEnds, blkOut_pending, Outcome.block]

/-- The shadow ends of a block (other than an exit to `ex`) satisfy `K` when those of its body
    satisfy `K` after leaving the block. -/
private theorem shEnds_blk (hregs : r.regs = B.regs)
    (hax : r.ax = (B.ax && (blkSnaps st1 l).isEmpty))
    (hold : ∀ e ∈ B.regs.toList, e ∉ st.pending.getD l [])
    (hsnap : ∀ e ∈ blkSnaps st1 l, e ∈ B.regs.toList) {ex : Option String} (hex : ex ≠ some l)
    (hEnds : ShEnds B st1 ex (fun o => K (o.block l σ))) :
    ShEnds r (blkFin st st1 l d live clock) ex K := by
  refine ⟨fun h => ?_, exitEnds_blk hregs hold (by grind) hEnds.2⟩
  rcases Bool.and_eq_false_iff.1 (hax ▸ h) with hb | hb
  · grind [Outcome.block, hEnds.1 hb]
  obtain ⟨e, he⟩ := List.isEmpty_eq_false_iff_exists_mem.1 hb
  grind [hEnds.2 l e (hsnap e he) (mem_blkSnaps.1 he).1 hex.symm, Outcome.block]

/-! ## Gaps

Facts the simulation through a block needs that the premises of `Spec` do not provide. -/

include iL iW in
/-- The registrations of the walk of a block's body under a variable context, walked with no
    snapshot pending for the block's label: they are not dead at the body's walk output, the
    live snapshots pending for the block's label there are registrations of the body, a
    registration is pending under at most one label, and they are no snapshot pending for the
    block's label at the block's walk input and no variable of the body's reach context (both
    drawn before the body's walk). -/
private theorem body_regs (htop : κ ≠ .top) (hwf : WFSt st) (hwfB : WFSt stB) (hDB : DeadBelow stB)
    (hst : stB.pending = st.pending.insert l []) (hnext : st.next ≤ stB.next)
    (hκ : ∀ v ∈ RE.vars κ, ∃ b j, v = freshName b j ∧ j < stB.next)
    (hB : (wpList κ (d + 1) f body).run stB = .ok (B, st1)) :
    (∀ e ∈ B.regs.toList, st1.dead.contains e = false) ∧ (∀ e ∈ blkSnaps st1 l, e ∈ B.regs.toList) ∧
    (∀ e ∈ B.regs.toList, ∀ l1 l2, e ∈ st1.pending.getD l1 [] → e ∈ st1.pending.getD l2 [] →
      l1 = l2) ∧
    (∀ e ∈ B.regs.toList, e ∉ st.pending.getD l []) ∧ (∀ v ∈ RE.vars κ, v ∉ B.regs.toList) := by
  refine ⟨wpList_regs_live hB hDB, body_snaps_regs htop (by simp [hst]) hB, wpList_regs_one_label hB
    fun l e he b j hj => by grind [hwfB.pending_fresh l e he, freshName_counter_inj],
    fun e he hp => ?_, fun v hv hr => ?_⟩
  · grind [wpList_regs hB e he, hwf.pending_fresh l e hp, freshName_counter_inj]
  · grind [wpList_regs hB v hr, hκ v hv, freshName_counter_inj]

/-! ## The carried merges of a block -/

/-- The carried merges a block registered after its end are those its body registered at other
    depths than the block's. -/
private theorem carryReg_fin (hregs : r.regs = B.regs) {k : Nat} {v : WExpr P} :
    CarryReg r (blkFin st st1 l d live clock) k i n v xB ↔
      k ≠ d + 1 ∧ CarryReg B st1 k i n v xB := by
  grind [CarryReg, blkOut]

/-- A live carried merge of a block is registered by its body at the block's depth. -/
private theorem carr_reg (hreg : ∀ e ∈ blkCarr st1 d, e.2.2 ∈ B.regs.toList)
    {e : P.Ident × WExpr P × P.Ident}
    (he : e ∈ blkCarr st1 d) : ∃ i, CarryReg B st1 (d + 1) i e.1 e.2.1 e.2.2 :=
  (List.getElem?_of_mem (List.mem_filter.1 he).1).imp fun _ hi => ⟨hi, hreg e he⟩

end

/-- Facts on the carried merges the walk of a block's body (result `B`, output `st1`) registers,
    for the names `vs` of the reach context: the live entries at the block's depth are
    registrations, and registrations are not dead; no registered entry is deeper than the block;
    every registered entry is a selector `ite(c, var xB, var n)` with a simple condition whose
    variables and copy are no target of the block's live merges and not in `vs`; the targets of
    the block's live merges are not in `vs` and no registrations; no registered entry targets a
    name in `vs`. -/
private structure CarrFacts (st1 : WSt P) (d : Nat) (B : WRes P) (vs : List P.Ident) : Prop where
  reg : ∀ e ∈ blkCarr st1 d, e.2.2 ∈ B.regs.toList
  dead : ∀ e ∈ B.regs.toList, st1.dead.contains e = false
  deep : ∀ k i n v xB, CarryReg B st1 k i n v xB → k ≤ d + 1
  shp : ∀ k i n v xB, CarryReg B st1 k i n v xB → ∃ c, v = .ite c (.var xB) (.var n) ∧
    wsimple c ∧ ∀ y ∈ xB :: wvars c, y ∉ (blkCarr st1 d).map (·.1) ∧ y ∉ vs
  tgv : ∀ y, y ∈ vs ∨ y ∈ B.regs.toList → y ∉ (blkCarr st1 d).map (·.1)
  nv : ∀ k i n v xB, CarryReg B st1 k i n v xB → n ∉ vs

/-- The live carried merges of a block have Boolean selectors in `σ0`, targets bound in `σ0` to
    values of their types `tyf`, and copies bound to values of the targets' types `tyf` and of
    the targets' final declared types. -/
private abbrev MgBound (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (st1 : WSt P) (d : Nat) (σ0 : SemanticStore P)
    (tyf : P.Ident → P.Ty) : Prop :=
  ∀ e ∈ blkCarr st1 d, (SelIs F T Y σ0 e.2.1 true ∨ SelIs F T Y σ0 e.2.1 false) ∧
    (∃ w, σ0 e.1 = some w ∧ HasVal.valueOfTy F w (tyf e.1)) ∧
    ∃ w, σ0 e.2.2 = some w ∧ HasVal.valueOfTy F w (tyf e.1) ∧
      ∀ ty, tyOfName T Y e.1 = .ok ty → HasVal.valueOfTy F w ty

/-- The store after the live carried merges of a block from the store `σ0`, each merge selecting
    when its selector evaluates to `true` in `σ0`. -/
private noncomputable def mgStore (F : P.Factory) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (st1 : WSt P) (d : Nat) (σ0 : SemanticStore P) :=
  (blkCarr st1 d).foldl (mstep σ0 fun e => decide (SelIs F T Y σ0 e.2.1 true)) σ0

omit iL iLVal in
include iIL in
/-- The live carried merges of a block run, given its body's walk facts and bound merges: the
    store after them agrees with the store `σ0` before them off their targets, binds the
    targets to values of their types, holds values, and binds exactly the names `σ0` binds. -/
private theorem mg_block (hF : WellFormedSemanticEvalBase F) (hC0 : WellFormedStore σ0 F)
    (hres : resolveItems T Y (mergesOf st1 d).toList = .ok iM) (hcf : CarrFacts st1 d B vs)
    (hbd : MgBound F T Y st1 d σ0 tyf) :
    MainRun F iM σ0 [] (mgStore F T Y st1 d σ0) ∧
    MInv F ((blkCarr st1 d).map (·.1)) tyf σ0 (mgStore F T Y st1 d σ0) ∧
    ∀ y, (mgStore F T Y st1 d σ0 y).isSome = (σ0 y).isSome := by
  simp only [mergesOf, ← List.foldl_map, Rope.toList_foldl_app, Rope.toList_nil, List.nil_append,
    List.flatMap_map, Rope.toList_one, ← List.map_eq_flatMap] at hres
  have h0 : MInv F ((blkCarr st1 d).map (·.1)) tyf σ0 σ0 :=
    ⟨fun _ _ => rfl, fun y hy => (List.mem_map.1 hy).elim fun e ⟨he, h⟩ => h ▸ (hbd e he).2.1, hC0⟩
  have hS : ∀ σ, MInv F ((blkCarr st1 d).map (·.1)) tyf σ0 σ → ∀ y, (σ y).isSome = (σ0 y).isSome :=
    fun σ h y => by by_cases hy : y ∈ (blkCarr st1 d).map (·.1) <;> grind [MInv]
  refine (fun h => ⟨h.1, h.2, hS _ h.2⟩) (merges_run hF hC0 _ hres
    (fun e he => List.mem_map_of_mem he) (fun e he => ?_)
    (fun e he => (carr_reg hcf.reg he).elim fun _ hr => (hcf.shp _ _ _ _ _ hr).elim fun _ h =>
      (h.2.2 _ (.head _)).1)
    (fun e he => (hbd e he).2.2.imp fun _ h => ⟨h.1, h.2.1⟩) σ0 h0)
  obtain ⟨i, hr⟩ := carr_reg hcf.reg he
  obtain ⟨c, hv, hsc, hy⟩ := hcf.shp _ _ _ _ _ hr
  refine ⟨c, hv, fun σ hag hC c' hc => ?_⟩
  rw [ev_congr hF hC hC0 c' fun y h => hag y (hy y (.tail _ (fv_resolve_simple c hsc hc y h))).1]
  rcases (hbd e he).1 with hs | hs <;> grind [SelIs, SelIs.ne]

section

omit iL iOp iLF iLV iLVal

/-- After the live carried merges of a block, a target holds its value before them when no
    registered merge of it at the block's depth selects, and otherwise the copy of the selecting
    one with the largest index. -/
private theorem mg_val (hcf : CarrFacts st1 d B vs) (hok : CarryOK F T Y B st1 σ0) (n : P.Ident) :
    ((∀ i n' v xB, CarryReg B st1 (d + 1) i n' v xB → n' = n → ¬ SelIs F T Y σ0 v true) ∧
      mgStore F T Y st1 d σ0 n = σ0 n) ∨
    ∃ i v xB, CarryReg B st1 (d + 1) i n v xB ∧ SelIs F T Y σ0 v true ∧
      mgStore F T Y st1 d σ0 n = σ0 xB ∧
      ∀ i' v' xB', CarryReg B st1 (d + 1) i' n v' xB' → SelIs F T Y σ0 v' true → i' ≤ i := by
  rw [mgStore, blkCarr, mstore_filter]
  have hc : ∀ e ∈ st1.carries.getD (d + 1) [], (!st1.dead.contains e.2.2 &&
      decide (SelIs F T Y σ0 e.2.1 true)) = true → (σ0 e.2.2).isSome := fun e he hs =>
    (carr_reg hcf.reg (List.mem_filter.2 ⟨he, by grind⟩)).elim fun _ hr => by
      grind [hok _ _ _ _ _ hr]
  rcases mstore_val (σ := σ0) _ hc n with ⟨hno, he⟩ | ⟨i, ⟨n', v, xB⟩, hi, rfl, hs, he, hmax⟩
  · exact .inl ⟨fun i n' v xB hr hn => by grind [CarryReg, hno i _ hr.1 hn, hcf.dead _ hr.2], he⟩
  · refine .inr ⟨i, v, xB, ⟨hi, hcf.reg _ (List.mem_filter.2 ⟨List.mem_of_getElem? hi, by grind⟩)⟩,
      by grind, he, fun i' v' xB' hr hs' => hmax i' _ hr.1 rfl (by grind [hcf.dead _ hr.2])⟩

include iLV in
/-- A registered carried merge selects alike, and its copy holds the same value, in a store
    agreeing off the block's merge targets and the reach context's variables. -/
private theorem sel_tr (hF : WellFormedSemanticEvalBase F) (hcf : CarrFacts st1 d B vs)
    (hCa : WellFormedStore σa F) (hCb : WellFormedStore σb F)
    (hag : ∀ y, y ∉ (blkCarr st1 d).map (·.1) → y ∉ vs → σb y = σa y) {k : Nat} {v : WExpr P}
    (hr : CarryReg B st1 k i n v xB) :
    (∀ b, SelIs F T Y σa v b → SelIs F T Y σb v b) ∧ σb xB = σa xB := by
  grind [hcf.shp _ _ _ _ _ hr, SelIs, ev_congr, fv_resolve_simple]

/-- After the live carried merges of a block, a name with a value reaching the block's end
    through the body's merges (`CarryAgree` at the block's depth) holds it. -/
private theorem mg_here (hcf : CarrFacts st1 d B vs) (hok : CarryOK F T Y B st1 σ0)
    (h : CarryAgree F T Y B st1 (d + 1) σ0 n w) : mgStore F T Y st1 d σ0 n = some w := by
  have hdeep := hcf.deep
  grind [CarryAgree, CarryReg, SelIs.ne, mg_val hcf hok n]

include iLV in
/-- The selectors of the carried merges a block registered are false after it when those of
    its body at the depths other than the block's are false before the block's merges and
    join, which change only the merge targets and the context's variables. -/
private theorem carryFF_fin (hF : WellFormedSemanticEvalBase F) (hregs : r.regs = B.regs)
    (hcf : CarrFacts st1 d B vs) (hCa : WellFormedStore σa F) (hCb : WellFormedStore σb F)
    (hag : ∀ y, y ∉ (blkCarr st1 d).map (·.1) → y ∉ vs → σb y = σa y)
    (hff : ∀ k, k < d + 1 → ∀ i n v xB, CarryReg B st1 k i n v xB → SelIs F T Y σa v false) :
    CarryFF F T Y r (blkFin st st1 l d live clock) σb := fun k i n v xB hr =>
  ((carryReg_fin hregs).1 hr).elim fun hk hr => (sel_tr hF hcf hCa hCb hag hr).1 false
    (hff k (Nat.lt_of_le_of_ne (hcf.deep k i n v xB hr) hk) i n v xB hr)

include iLV in
/-- At a shallower block end than the block's, a value reaching a name through the body's
    carried merges reaches it through the block's after the block's merges. -/
private theorem mg_outer (hF : WellFormedSemanticEvalBase F) (hregs : r.regs = B.regs)
    (hC0 : WellFormedStore σ0 F) (hcf : CarrFacts st1 d B vs) (hok : CarryOK F T Y B st1 σ0)
    (hCM : WellFormedStore (mgStore F T Y st1 d σ0) F) (ht : t ≤ d)
    (h : CarryAgree F T Y B st1 t σ0 n w) :
    CarryAgree F T Y r (blkFin st st1 l d live clock) t (mgStore F T Y st1 d σ0) n w := by
  have hT := fun {k i v xB} (hr : CarryReg B st1 k i n v xB) =>
    sel_tr (T := T) (Y := Y) hF hcf hC0 hCM (fun y hy _ => mstore_off _ _ y hy) hr
  have hfin : ∀ k i v xB, CarryReg r (blkFin st st1 l d live clock) k i n v xB →
      k ≠ d + 1 ∧ CarryReg B st1 k i n v xB := fun _ _ _ _ => (carryReg_fin hregs).1
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun k i v xB hr => (hfin _ _ _ _ hr).elim fun _ hr =>
    (h1 _ _ _ _ hr).imp ((hT hr).1 _) ((hT hr).1 _), ?_⟩
  rcases h2 with ⟨hff, hw⟩ | ⟨k, i, v, xB, hk, hr, hs, hw, hmax⟩
  · refine .inl ⟨fun k i v xB hk hr => (hfin _ _ _ _ hr).elim fun _ hr =>
      (hT hr).1 _ (hff k i v xB hk hr), (mg_val hcf hok n).elim (fun h => h.2.trans hw)
      fun ⟨_, _, _, hr, hs, _⟩ => (SelIs.ne hs (hff _ _ _ _ (by omega) hr)).elim⟩
  rcases Classical.em (k = d + 1) with rfl | hkd
  · refine .inl ⟨fun k' i' v' xB' hk' hr' => (hfin _ _ _ _ hr').elim fun hk'' hr' =>
      (hT hr').1 _ ((h1 _ _ _ _ hr').resolve_left fun hs' => ?_), mg_here hcf hok
      ⟨h1, .inr ⟨_, i, v, xB, Nat.le_refl _, hr, hs, hw, fun k' i' v' xB' hk' =>
        hmax k' i' v' xB' (Nat.le_trans ht (Nat.le_of_succ_le hk'))⟩⟩⟩
    exact (hmax k' i' v' xB' hk' hr' hs').elim (fun h => absurd (hcf.deep _ _ _ _ _ hr') (by omega))
      fun h => hk'' h.1.symm
  · exact .inr ⟨k, i, v, xB, hk, (carryReg_fin hregs).2 ⟨hkd, hr⟩, (hT hr).1 _ hs,
      (hT hr).2.trans hw, fun k' i' v' xB' hk' hr' hs' => (hfin _ _ _ _ hr').elim fun _ hr' =>
        hmax k' i' v' xB' hk' hr' ((h1 _ _ _ _ hr').resolve_right (SelIs.ne hs' <| (hT hr').1 _ ·))⟩

include iL in
/-- Facts on the carried merges the walk of a block's body registers: the live entries at the
    block's depth are registrations; no registered entry is deeper than the block; every
    registered entry is a selector `ite(c, var xB, var n)` with a simple condition whose
    variables and copy are no target of the block's live merges and no variable of the reach
    context; the targets of the block's live merges are no variables of the reach context and
    no registrations; no registered entry targets a variable of the reach context. -/
private theorem carr_walk (hκ : κ ≠ .top) (hst : stB.carries = st.carries.insert (d + 1) [])
    (hL : ∀ (l : String) (t : Nat), stB.labelDepth[l]? = some t → t ≤ d + 1) (hwfB : WFSt stB)
    (hB : (wpList κ (d + 1) f body).run stB = .ok (B, st1))
    (hnd : ∀ e ∈ B.regs.toList, st1.dead.contains e = false)
    (hkr : ∀ v ∈ RE.vars κ, v ∉ B.regs.toList) (hav : ∀ x ∈ Block.idents body, AvoidedIfFresh stB x)
    (hκb : ∀ z ∈ RE.vars κ, (∃ b j, z = freshName b j ∧ j < stB.next) ∧
      stB.avoid.contains z = false ∧ stB.back[z]? = none) : CarrFacts st1 d B (RE.vars κ) := by
  obtain ⟨h1, h2⟩ := body_carries hκ hL (by simp [hst]) hB
  obtain ⟨n1, n2, n3⟩ := body_carries_names hwfB hav (fun _ h => h) hκb (by simp [hst]) hB
  have ht : ∀ y, y ∈ RE.vars κ ∨ y ∈ B.regs.toList → y ∉ (blkCarr st1 d).map (·.1) :=
    fun y hy hm => (List.mem_map.1 hm).elim fun e ⟨he, h⟩ => (carr_reg h1 he).elim fun _ hr =>
      hy.elim (h ▸ n3 _ _ _ _ _ hr.1 hr.2) (h ▸ n1 e he)
  refine ⟨h1, hnd, fun k i n v xB hr => h2 (fun k e he => (hwfB.carries_get he).1) k i n v xB
    hr.1 hr.2, fun k i n v xB hr => ?_, ht, fun k i n v xB hr => n3 k i n v xB hr.1 hr.2⟩
  have hwf1 := (wpList_walkOK hB).wf hwfB fun x hx => hav x (stmtsInits_mem_idents x hx)
  exact (hwf1.carries_sel k i n v xB hr.1).elim fun c hc => (n2 k i n v xB c hr.1 hr.2 hc).elim
    fun hs hy => ⟨c, hc, hs, fun y hy' => (List.mem_cons.1 hy').elim
      (fun h => h ▸ ⟨ht _ (.inr hr.2), fun hm => hkr _ hm hr.2⟩) (hy y)⟩

/-- The live carried merges of a block, all registered by its body, are well formed when the
    body's carried merges are (`CarryOK`): Boolean selectors, targets with final declared types
    bound to values of them, and copies bound to values of them. -/
private theorem carr_bound (hcf : CarrFacts st1 d B vs) (hok : CarryOK F T Y B st1 σL') :
    ∃ tyf, MgBound F T Y st1 d σL' tyf ∧
      ∀ n, (∀ ty, tyOfName T Y n ≠ .ok ty) → n ∉ (blkCarr st1 d).map (·.1) := by
  refine ⟨fun n => if h : ∃ ty, tyOfName T Y n = .ok ty then h.choose else HasBool.boolTy,
    fun e he => ?_, fun n hty hm => (List.mem_map.1 hm).elim fun e ⟨he, h⟩ =>
      (hok _ _ _ _ _ (carr_reg hcf.reg he).choose_spec).2.1.elim (h ▸ hty)⟩
  obtain ⟨hb, hty, ⟨w, hw, hwty⟩, w', hw', hw'ty⟩ := hok _ _ _ _ _ (carr_reg hcf.reg he).choose_spec
  exact ⟨hb, ⟨w, hw, by simpa only [dite_eq_left hty] using hwty _ hty.choose_spec⟩,
    w', hw', by simpa only [dite_eq_left hty] using hw'ty _ hty.choose_spec, hw'ty⟩

include iLV in
/-- The carried merges a block registered are well formed after it when its body's are before
    the block's merges and join, which change only the merge targets (bound after the merges to
    values of their final declared types) and the context's variables. -/
private theorem carryOK_fin (hF : WellFormedSemanticEvalBase F) (hregs : r.regs = B.regs)
    (hcf : CarrFacts st1 d B vs) (hCa : WellFormedStore σa F) (hCb : WellFormedStore σb F)
    (hag : ∀ y, y ∉ (blkCarr st1 d).map (·.1) → y ∉ vs → σb y = σa y)
    (htg : ∀ n ∈ (blkCarr st1 d).map (·.1), ∃ w, σb n = some w ∧
      ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty)
    (hok : CarryOK F T Y B st1 σa) : CarryOK F T Y r (blkFin st st1 l d live clock) σb :=
  fun k i n v xB hr => ((carryReg_fin hregs).1 hr).elim fun _ hr => by
  obtain ⟨hb, hty, hn, w', hw', hw'ty⟩ := hok k i n v xB hr
  have htr := sel_tr (T := T) (Y := Y) hF hcf hCa hCb hag hr
  refine ⟨hb.imp (htr.1 _) (htr.1 _), hty, ?_, w', htr.2.trans hw', hw'ty⟩
  exact (Classical.em (n ∈ (blkCarr st1 d).map (·.1))).elim (htg n) fun hn' =>
    hag n hn' (hcf.nv k i n v xB hr) ▸ hn

/-- The targets of the live carried merges of a block are bound to values of their final
    declared types when the body's carried merges are well formed. -/
private theorem tg_ok (hcf : CarrFacts st1 d B vs) (hok : CarryOK F T Y B st1 σL') :
    ∀ n ∈ (blkCarr st1 d).map (·.1), ∃ w, σL' n = some w ∧ ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty := fun _ hn => (List.mem_map.1 hn).elim fun _ ⟨he, h⟩ =>
  h ▸ (hok _ _ _ _ _ (carr_reg hcf.reg he).choose_spec).2.2.1

/-- After the live carried merges of a block, their targets are bound to values of their final
    declared types when the body's carried merges are well formed. -/
private theorem mg_tg (hcf : CarrFacts st1 d B vs) (hok : CarryOK F T Y B st1 σL') :
    ∀ n ∈ (blkCarr st1 d).map (·.1), ∃ w, mgStore F T Y st1 d σL' n = some w ∧
      ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty := fun n hn => by
  grind [mg_val hcf hok n, tg_ok hcf hok n hn, CarryOK]

end

omit iL iLVal in
include iIL in
/-- The live carried merges of a block change nothing when none selects. -/
private theorem mg_ff (hF : WellFormedSemanticEvalBase F) (hcf : CarrFacts st1 d B vs)
    (hC0 : WellFormedStore σ0 F) (hres : resolveItems T Y (mergesOf st1 d).toList = .ok iM)
    (hbd : MgBound F T Y st1 d σ0 tyf) (hff : CarryFF F T Y B st1 σ0) : MainRun F iM σ0 [] σ0 := by
  have h := (mg_block hF hC0 hres hcf hbd).1
  rwa [mgStore, mstore_none _ fun e he => decide_eq_false fun ht =>
    SelIs.ne ht (hff _ _ _ _ _ (carr_reg hcf.reg he).choose_spec)] at h

/-! ## Blocks under a variable context -/

include iIL in
/-- The walk of a block under a variable context has the simulation property when the walk of
    its body (at the next depth, under the same context) has it. -/
private theorem stmtSpec_block_var (hF : WellFormedSemanticEvalBase F) (md : MetaData P)
    (hκ : κ ≠ .top)
    (hb : ListSpec F tE Lc κ (d + 1) f body) : StmtSpec F tE Lc κ d f (.block l body md) := by
  intro st r st' hwf hrun T Y hfin items hres S hwfS Γ hΓ hwt havoid
    Ex hEx k Lab hLab hκv hD hLK hhigh
  simp only [Block.idents, Stmt.idents, List.append_nil] at havoid
  obtain ⟨B, st1, hB, hL, hout, hsk, hobl, hax, hdrop, hregs⟩ := walk_var hκ hrun
  obtain ⟨live, clock, rfl, hl⟩ := liveAdd_step hL
  have hlive := fun y hy => (hl y).2 (.inl hy)
  obtain ⟨hdead, hsnap, hdisj, hold, hkr⟩ := body_regs (l := l) (stB := blkIn st l d) hκ hwf
    (wfSt_blk hwf l d _) hD rfl (Nat.le_refl _) (fun v hv => (hκv v hv).1) hB
  have hcf := carr_walk (st := st) hκ rfl
    (fun l' t h => (lab_body hLab l' t h).1) (wfSt_blk hwf l d _) hB hdead hkr
    (fun x hx => havoid x (List.mem_append_right _ hx))
    (fun z hz => ⟨(hκv z hz).1, (hκv z hz).2.1, (hκv z hz).2.2.2⟩)
  have hcurB : ∀ x ∈ S, ∀ n, curName (blkIn st l d) x = some n → n ∉ RE.vars κ :=
    fun x hx n hn hk => (curName_cases hn).elim ((hκv n hk).2.2.1 x) fun ⟨_, _, h⟩ => by
      grind [havoid x (List.mem_append_left _ hx), hκv n hk]
  obtain ⟨iB, iM, iJ, hiB, hiM, hiJ, rfl⟩ := resolve_out3 (hout ▸ hres)
  have hspec := hb (fun h => absurd h hκ) (blkIn st l d) B st1 (wfSt_blk hwf l d _) hB T Y hfin
    iB hiB S hwfS Γ (fun h => hΓ (h.imp_right hobl.trans)) hwt.block havoid Ex hEx k _
    (lab_body hLab) hκv hD hLK (by grind [blkIn])
  refine ⟨fun σ σL t cnd b tr hOn hreach hclaim => ?_, fun hf' => ?_, fun hf' => ?_⟩
  · cases hreach with | block hreach => ?_
    obtain ⟨h1, h2, wsub, hw, tr', hhit, hcl⟩ := hspec.1 σ σL t cnd b tr
      (hOn.transfer ⟨rfl, rfl, rfl, rfl⟩ hlive contFV_body_sub) hreach hclaim
    exact ⟨hobl ▸ h1, hsk ▸ SkObl.block [] h2, wsub, hw, tr', hhit.append_left.append_left, hcl⟩
  all_goals
    subst hf'
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hiJ
  rotate_left
  · intro σs σL K hOff hSh
    simp only [OffPost, scopeAfter, Stmt.topInits, List.nil_append, ite_self]
    obtain ⟨tr, σL', hmain, hfe, hOff1, hFr, hSnap, hCFF, hok, hEnds⟩ := hspec.2.2 rfl σs σL _
      (hOff.transfer ⟨rfl, rfl, rfl, rfl⟩ contFV_body_sub) hSh
    obtain ⟨tyf, hbd, -⟩ := carr_bound hcf hok
    have hM : MainRun F iM σL' [] σL' := mg_ff hF hcf hOff1.canonL hiM hbd hCFF
    obtain ⟨σL'', hJ, hFails, hfr, hsome, hswap, -⟩ := join_ff hF hκ hiJ hOff1.canonL
      (fun e' he' => hSnap l e' (hsnap e' he') (mem_blkSnaps.1 he').1 (by simp)) hOff1.reach
      fun q g hqg => hOff1.bools g (hqg ▸ .tail _ (.head _))
    have hCL'' : WellFormedStore σL'' F := fun y v hv =>
      (hswap y v hv).elim (hOff1.canonL y v) fun h => h.1 ▸ (HasBool.boolIsVal F).1
    refine ⟨tr ++ [] ++ [], σL'', (hmain.append hM).append hJ, by simpa using hfe,
      ⟨hCL'', hFails, fun y hy => ?_, fun x hx hv n hn => (hfr n (hcurB x hx n hn)).symm ▸
        hOff1.defd x (by cases B.ax <;> first | exact hx | exact scopeAfter_sub S body hx) hv n hn,
        fun n w hw hY ty hty => ?_,
        hOff1.fresh.congr ⟨rfl, rfl, rfl, rfl⟩ fun y hy => hsome y ▸ hy⟩,
      fun y hy hv => (hfr y hv).trans (hFr y hy hv),
      snapFF_blk hregs hold fun l0 e he _ hp hne => ?_,
      carryFF_fin hF hregs hcf hOff1.canonL hCL'' (fun y _ hy => hfr y hy) fun k _ => hCFF k,
      carryOK_fin hF hregs hcf hOff1.canonL hCL'' (fun y _ hy => hfr y hy)
        (fun n hn => (hfr n fun hv => hcf.tgv n (.inl hv) hn).symm ▸ tg_ok hcf hok n hn) hok,
      shEnds_blk hregs hax hold hsnap (by simp) hEnds⟩
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((hsome y).trans
        (by rcases hOff1.bools y hy with h | h <;> simp [h]))
      exact (hswap y v hv).elim (fun h => hv ▸ h ▸ hOff1.bools y hy) fun h => .inl (h.1 ▸ hv)
    · exact (hswap n w hw).elim (hOff1.gtyped n w · hY ty hty) fun ⟨h, v0, h0, hb0⟩ => h ▸
        LawfulHasVal.valueOfTy_congr F v0 (HasBool.ttVal F) ty HasBool.boolTy
          (hOff1.gtyped n v0 h0 hY ty hty)
          (bool_valueOfTy hb0) (bool_valueOfTy (.inl rfl))
    · exact (hfr e (fun hv => hkr e hv he)).trans (hSnap l0 e he hp hne)
  intro σ σL X evs o hOn hrun hfeas
  refine .inr ?_
  cases hrun with | block hrunB => ?_
  rename_i o
  rcases hspec.2.1 rfl σ σL _ evs _ (hOn.transfer ⟨rfl, rfl, rfl, rfl⟩ hlive contFV_body_sub)
    hrunB hfeas with ⟨h, -⟩ | ⟨tr, σL', hmain, hfe, hpost⟩
  · exact absurd h hκ
  have hok : CarryOK F T Y B st1 σL' := by cases o <;> exact hpost.2.2.2.1
  obtain ⟨tyf, hbd, htgty⟩ := carr_bound hcf hok
  have hent : ∀ x ∈ S, x ∈ contFV k → (σ x).isSome := fun x hx hv =>
    (hOn.defd x hx (contFV_tail_sub hv)).1
  have hfr : ∀ {σa σb : SemanticStore P}, FreshInv Lc Ex (blkIn st l d) σa →
      (∀ y, (σb y).isSome = (σa y).isSome) → FreshInv Lc Ex st σb := fun h hs =>
    h.congr ⟨rfl, rfl, rfl, rfl⟩ fun y hy => hs y ▸ hy
  cases o with
  | normal σ1 =>
    obtain ⟨hOn1, hSnap, hCFF, -, hBax, -, hEE⟩ := hpost
    have hM := mg_ff hF hcf hOn1.canonL hiM hbd hCFF
    have hJ : MainRun F iJ σL' [] σL' :=
      (join_cases hiJ).elim (fun ⟨_, h⟩ => h ▸ .nil) fun ⟨_, h⟩ => (setReach_tt hF hκ h
        (fun _ => ev_join_holds hF hOn1.canonL hOn1.reach fun e he =>
          .inr (hSnap l e (hsnap e he) (mem_blkSnaps.1 he).1 (by simp)))
        hOn1.reach (.inl hOn1.reach)
        fun q g hqg => (hqg ▸ hOn1.reach : RE.Holds F σL' (.andNeg q g)).1).elim
        fun σ' ⟨hr', _, _, _, he, _⟩ => he hOn1.reach ▸ hr'
    exact ⟨tr ++ [] ++ [], σL', (hmain.append hM).append hJ, by simpa using hfe,
      ⟨hOn1.toOnCore.proj (D := []) (scopeAfter_sub S body) (fun _ _ h => h) hent
        hOn.undef (fun _ => rfl) (fun _ h => h) (fun _ _ => rfl) hOn1.canonL hOn1.gtyped
        (fun _ _ _ _ _ h => nomatch h) (hfr hOn1.fresh fun _ => rfl), hOn1.reach⟩,
      snapFF_blk hregs hold fun l0 e he _ hp hne => hSnap l0 e he hp hne,
      carryFF_fin hF hregs hcf hOn1.canonL hOn1.canonL (fun _ _ _ => rfl) fun k _ => hCFF k,
      carryOK_fin hF hregs hcf hOn1.canonL hOn1.canonL (fun _ _ _ => rfl) (tg_ok hcf hok) hok,
      by rw [hax, hBax, Bool.false_and], hdrop, exitEnds_blk hregs hold (fun _ _ h => h) hEE⟩
  | exit l0 σ1 =>
    obtain ⟨hoff, hEnds, hq, -, hm⟩ := hpost
    obtain ⟨hMr, ⟨hMoff, -, hMC⟩, hMs⟩ := mg_block hF hoff.canonL hiM hcf hbd
    have hMgt : ∀ n w, mgStore F T Y st1 d σL' n = some w →
        σL' n = some w ∨ ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty := fun n w hw =>
      (mg_val hcf hok n).imp (fun ⟨_, h⟩ => h ▸ hw) fun ⟨_, _, _, hr, _, hv, _⟩ =>
        (hok _ _ _ _ _ hr).elim fun _ ⟨_, _, w', hw', h⟩ =>
          Option.some.inj (hw'.symm.trans (hv.symm.trans hw)) ▸ h
    have hMsnap : ∀ e ∈ B.regs.toList,
        mgStore F T Y st1 d σL' e = σL' e := fun e he => hMoff e (hcf.tgv e (.inr he))
    have hMκ : ∀ y ∈ RE.vars κ, mgStore F T Y st1 d σL' y = σL' y :=
      fun y hy => hMoff y (hcf.tgv y (.inl hy))
    have hFailsM : κ.Fails F (mgStore F T Y st1 d σL') := by
      cases κ <;> simp only [RE.vars] at hMκ <;> simpa [RE.Fails, hMκ] using hoff.reach
    rcases Classical.em (l0 = l) with rfl | hl
    · simp only [blkIn_labelDepth, ↓reduceIte] at hm
      obtain ⟨e, heR, heP, het, hSnap, hCore, hbelow⟩ := hm
      have hem : e ∈ blkSnaps st1 l0 := mem_blkSnaps.2 ⟨heP, hdead e heR⟩
      obtain ⟨-, hiJ⟩ := (join_cases hiJ).resolve_left fun h => List.ne_nil_of_mem hem h.1
      have hall : ∀ e' ∈ blkSnaps st1 l0, mgStore F T Y st1 d σL' e' = some (HasBool.ttVal F) ∨
          mgStore F T Y st1 d σL' e' = some (HasBool.ffVal F) :=
        fun e' he' => (hMsnap e' (hsnap e' he')) ▸
        (Classical.em (e' = e)).elim (fun h => .inl (h ▸ het)) fun h =>
          .inr (hSnap l0 e' (hsnap e' he') (mem_blkSnaps.1 he').1 fun h' => h (Option.some.inj h'))
      obtain ⟨σL'', hJ, hH, hfr', hsome, -, hvκ⟩ := setReach_tt hF hκ hiJ
        (fun _ => ev_join_exit hF hMC hFailsM (fun y hy => (hMκ y hy).symm ▸ hoff.bools y hy) hall
          ⟨e, hem, (hMsnap e heR).trans het⟩) hOn.reach
        (.inr hFailsM) (fun q g hqg => (hMκ q (hqg ▸ .head _)).trans (hq q g hqg))
      have hval : ∀ y v, σL'' y = some v → σL y = some v ∨
          mgStore F T Y st1 d σL' y = some v := fun y v hv => (Classical.em (y ∈ RE.vars κ)).imp
        (fun hy => (hvκ y hy).symm.trans hv) fun hy => (hfr' y hy).symm.trans hv
      have hCL'' : WellFormedStore σL'' F := fun y v hv =>
        (hval y v hv).elim (hOn.canonL y v) (hMC y v)
      refine ⟨tr ++ [] ++ [], σL'', (hmain.append hMr).append hJ, by simpa using hfe, ?_⟩
      simp only [Outcome.block, ite_true, RunPost]
      have hV : ∀ x ∈ S, x ∈ contFV k → x ∈ (contFV k).filter (· ∈ S) := fun x hx hv =>
        List.mem_filter.2 ⟨hv, by simpa using hx⟩
      refine ⟨⟨onCore_mk (fun x hx hv n hn hln => ?_) (fun x hx hv => ?_)
        (fun x hx hv n hn hty => ?_) hent hOn.undef hCore.canon hCL'' (fun n w hw hY ty hty => ?_)
        (fun x hx hv n hn => hCore.ltyped x (scopeAfter_sub S body hx) (hV x hx hv) n hn)
        (hfr hCore.fresh fun y => (hsome y).trans (hMs y)), hH⟩,
        snapFF_blk hregs hold fun l1 e' he' hl1 hp _ => ?_,
        carryFF_fin hF hregs hcf hoff.canonL hCL''
          (fun y hy1 hy2 => (hfr' y hy2).trans (hMoff y hy1))
          fun k hk _ _ _ _ => hbelow k _ _ _ _ hk,
        carryOK_fin hF hregs hcf hoff.canonL hCL''
          (fun y hy1 hy2 => (hfr' y hy2).trans (hMoff y hy1))
          (fun n hn => (hfr' n fun hv => hcf.tgv n (.inl hv) hn).symm ▸ mg_tg hcf hok n hn)
          hok, ?_, hdrop,
        exitEnds_blk hregs hold (fun l1 hl1 _ h => hl1 (Option.some.inj h).symm) hEnds.2⟩
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
          (hCore.defd x (scopeAfter_sub S body hx) (hV x hx hv)).1
        rw [hw, hfr' n (hcurB x hx n hn)]
        exact mg_here hcf hok (hCore.xagree x (scopeAfter_sub S body hx)
          (hV x hx hv) n hn hln (liveFrom_enter hwf rfl rfl rfl hln
            fun l' j hj _ _ htj => absurd (hLab l' j hj).1 (by omega)) w hw)
      · have hd := hCore.defd x (scopeAfter_sub S body hx) (hV x hx hv)
        exact ⟨hd.1, fun n hn => (hsome n).trans (hMs n) ▸ hd.2 n hn⟩
      · rw [hfr' n (hcurB x hx n hn), hMoff n (htgty n hty)]
        exact hCore.alike x (scopeAfter_sub S body hx) (hV x hx hv) n hn hty
      · exact (hval n w hw).elim (hOn.gtyped n w · hY ty hty) fun h =>
          (hMgt n w h).elim (hCore.gtyped n w · hY ty hty) (· ty hty)
      · exact (hfr' e' (fun hv => hkr e' hv he')).trans ((hMsnap e' he').trans (hSnap l1 e' he' hp
          (by simpa using fun h : e' = e => hl1 (hdisj e heR l0 l1 heP (h ▸ hp)))))
      · simp [hax, List.ne_nil_of_mem hem]
    · simp only [Outcome.block, ite_eq_right hl]
      rw [blkIn_labelDepth, ite_eq_right (Ne.symm hl)] at hm
      have hall : ∀ e' ∈ blkSnaps st1 l,
          mgStore F T Y st1 d σL' e' = some (HasBool.ffVal F) := fun e' he' => by
        have hp := (mem_blkSnaps.1 he').1
        rw [hMsnap e' (hsnap e' he')]
        split at hm
        · exact hm.elim fun e ⟨heR, heP, _, hSnap, _⟩ => hSnap l e' (hsnap e' he') hp
            (by simpa using fun h : e' = e => hl (hdisj e heR l0 l heP (h ▸ hp)))
        · exact hm l e' (hsnap e' he') hp (by simp)
      have hqM : ∀ q g, κ = .andNeg q g → mgStore F T Y st1 d σL' q = some (HasBool.ttVal F) :=
        fun q g hqg => (hMκ q (hqg ▸ .head _)).trans (hq q g hqg)
      obtain ⟨σL'', hJ, -, -, -, -, he⟩ := join_ff hF hκ hiJ hMC hall hFailsM fun q g hqg =>
        (hMκ g (hqg ▸ .tail _ (.head _))).symm ▸ hoff.bools g (hqg ▸ .tail _ (.head _))
      rw [he hqM] at hJ
      have hgtM : ∀ n w, mgStore F T Y st1 d σL' n = some w → Y[n]? = none →
          ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty := fun n w hw hY ty hty =>
        (hMgt n w hw).elim (fun h => hoff.gtyped n w h hY ty hty) (fun h => h ty hty)
      have hfrM := hfr hoff.fresh hMs
      refine ⟨tr ++ [] ++ [], _, (hmain.append hMr).append hJ, by simpa using hfe,
        ⟨hMC, hFailsM, fun y hy => (hMκ y hy).symm ▸ hoff.bools y hy,
          fun x hx hv n hn => ?_, hgtM, hfrM⟩,
        shEnds_blk hregs hax hold hsnap (by simpa using hl) hEnds, hqM,
        carryOK_fin hF hregs hcf hoff.canonL hMC (fun y hy1 _ => hMoff y hy1)
          (mg_tg hcf hok) hok, ?_⟩
      · obtain ⟨w, hw, hwty⟩ := hoff.defd x hx hv n hn
        obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 ((hMs n).trans (by simp [hw]))
        exact ⟨w', hw', (hMgt n w' hw').elim (fun h => Option.some.inj (hw.symm.trans h) ▸ hwty) id⟩
      rcases hlt : st.labelDepth[l0]? with _ | t <;> simp only [hlt] at hm ⊢
      · exact snapFF_blk hregs hold fun l1 e' he' _ hp hne => hMsnap e' he' ▸ hm l1 e' he' hp hne
      · obtain ⟨e, heR, heP, het, hSnap, hCore, hbelow⟩ := hm
        simp only [hl, ite_false] at hCore
        have hp1 : ∀ x ∈ S, x ∈ Lab l0 → projectStore σ σ1 x = σ1 x := fun x hx hv => by
          simp [projectStore, hent x hx ((hLab l0 t hlt).2 x hv).1]
        refine ⟨e, hregs ▸ heR, ?_, (hMsnap e heR).trans het,
          snapFF_blk hregs hold fun l1 e' he' _ hp hne => hMsnap e' he' ▸ hSnap l1 e' he' hp hne,
          ⟨fun x hx hv n hn hln hlf w hw => ?_, fun x hx hv => ?_, fun x hx hv n hn hty => ?_,
            fun x hx hxS => by simp [projectStore, hOn.undef x hx hxS], fun x v hv => ?_, hMC,
            hgtM, fun x hx hv n hn => ?_, hfrM⟩, fun k' i n v xB hk hr => ?_⟩
        · exact (blkOut_pending st st1 l l0 d).trans (ite_eq_right (Ne.symm hl)) ▸ heP
        · rw [hp1 x hx hv] at hw
          exact mg_outer hF hregs hoff.canonL hcf hok hMC (hLab l0 t hlt).1
            (hCore.xagree x (scopeAfter_sub S body hx) hv n hn hln
              (liveFrom_enter hwf rfl rfl rfl hln fun l' j hj _ _ htj => hlf l' j hj htj) w hw)
        · exact hp1 x hx hv ▸ (hCore.defd x (scopeAfter_sub S body hx) hv).imp id
            fun h n hn => hMs n ▸ h n hn
        · rw [hp1 x hx hv, hMoff n (htgty n hty)]
          exact hCore.alike x (scopeAfter_sub S body hx) hv n hn hty
        · exact hCore.canon x v (Option.ite_none_right_eq_some.1 hv).2
        · exact hp1 x hx hv ▸ hCore.ltyped x (scopeAfter_sub S body hx) hv n hn
        · obtain ⟨hk', hr⟩ := (carryReg_fin hregs).1 hr
          exact (sel_tr (T := T) (Y := Y) hF hcf hoff.canonL hMC (fun y hy _ => hMoff y hy) hr).1
            false (hbelow k' i n v xB hk hr)

/-! ## Blocks at top level -/

omit iBE iLB iHI iL iHa iW iOp iLF iLV iLVal in
/-- The `init` of `tt` to an unbound name runs, binding it. -/
private theorem init_run (hF : WellFormedSemanticEvalBase F) {v : P.Ident} (h : σ v = none) :
    EvalE F σ (.cmd (.init v HasBool.boolTy (.det tt) .empty)) (σ.update v (HasBool.ttVal F)) [] :=
  .eval_init (hF.val.eval_tt σ)
    (.init h (update_facts σ v (HasBool.ttVal F)).1 (update_facts σ v (HasBool.ttVal F)).2)
    (bool_valueOfTy (.inl rfl)) hF.var

omit iL iOp iLF iLV in
/-- Entering the body of a top-level block: after `init rL := true`, the relation holds at the
    body's walk output under the context `rL`, with `rL` excepted; `rL` was unbound before. -/
private theorem top_entry {kk : Nat} (hOn : OnInv F T Y Lc Ex sa .top S V σ σL)
    (hs : SameNames sa sb) (hl : ∀ n, sb.live.contains n = true → sa.live.contains n = true)
    (hV : V' ⊆ V) (hrL : rL = freshName "r" kk) (hav : sb.avoid.contains rL = false)
    (hnext : kk < sb.next) (hnm : ∀ x : P.Ident, sb.nm[x]? ≠ some rL)
    (hcur : ∀ x ∈ S, curName sb x ≠ some rL) (hnEx : ¬ Ex rL)
    (hT : ∀ ty, tyOfName T Y rL = .ok ty → HasVal.valueOfTy F (HasBool.ttVal F) ty) :
    σL rL = none ∧
      OnInv F T Y Lc (fun y => Ex y ∨ y = rL) sb (.name rL) S V' σ
        (σL.update rL (HasBool.ttVal F)) := by
  obtain ⟨⟨ha, hd, hal, hu, hc, hcL, hg, hlt, hf⟩, -⟩ := hOn.transfer hs hl hV
  have hnone : σL rL = none := Option.eq_none_iff_forall_ne_some.2 fun w hw => by
    grind [(hf rL (by simp [hw])).2 "r" kk hrL hav]
  have hu' := update_facts σL rL (HasBool.ttVal F)
  have hb := HasBool.boolIsVal (P := P) F
  have hne : ∀ x ∈ S, ∀ n, curName sb x = some n → σL.update rL (HasBool.ttVal F) n = σL n :=
    fun x hx n hn => hu'.2 n fun e => hcur x hx (e ▸ hn)
  refine ⟨hnone, ⟨⟨fun x hx hv n hn hl => (hne x hx n hn).trans (ha x hx hv n hn hl),
    fun x hx hv => (hd x hx hv).imp_right fun h n hn => hne x hx n hn ▸ h n hn,
    fun x hx hv n hn hty w w' h1 h2 => hal x hx hv n hn hty w w' h1 (hne x hx n hn ▸ h2), hu, hc,
    ?_, ?_, hlt, ?_⟩, hu'.1⟩⟩ <;> grind [WellFormedStore, SemanticStore.update, FreshInv]

omit iLB iHI iL iOp iLF iLV iLVal in
/-- The join of a top-level block runs feasibly and changes nothing when it evaluates to
    `tt`. -/
private theorem join_top_run {c : Bool}
    (hiJ : resolveItems T Y (if c then Rope.one (WItem.assume joinLabel X .empty)
      else Rope.nil).toList = .ok iJ)
    (hev : ∀ x, resolveE T Y X = .ok x → P.eval F σ x = some (HasBool.ttVal F)) :
    ∃ tr, MainRun F iJ σ tr σ ∧ Trace.AssumptionsHold P evalInterp () tr := by
  split at hiJ
  · obtain ⟨i, _, hi, ⟨⟩, rfl⟩ := resolveItems_cons_ok (Rope.toList_one _ ▸ hiJ :)
    obtain ⟨x, hx, rfl⟩ := resolveItem_assume hi
    exact ⟨_, .plain .eval_assume .nil, fun _ hc => by grind [evalInterp]⟩
  · simp only [Rope.toList_nil, resolveItems, pure, Except.pure, Except.ok.injEq] at hiJ
    exact ⟨[], hiJ ▸ .nil, nofun⟩

include iIL in
/-- The walk of a block at top level has the simulation property when the walks of its body (at
    the next depth, under every context) have it. -/
private theorem stmtSpec_block_top (hF : WellFormedSemanticEvalBase F) (md : MetaData P)
    (hb : ∀ κB, ListSpec F tE Lc κB (d + 1) f body) :
    StmtSpec F tE Lc .top d f (.block l body md) := by
  intro st r st' hwf hrun T Y hfin items hres S hwfS Γ hΓ hwt havoid
    Ex hEx k Lab hLab _ hD hLK hhigh
  simp only [Block.idents, Stmt.idents, List.append_nil] at havoid
  obtain ⟨kk, hf, hkk, hav⟩ := freshIn_spec st.avoid "r" st.next
  generalize hrL : freshName (P := P) "r" kk = rL at hf hav
  replace hrL := hrL.symm
  have hwfT : WFSt (stTop st l d rL (kk + 1)) := (wFreshBool_walk (x := rL) (b := "r")
    (st := blkIn st l d) (by simp only [wFreshBool_run, blkIn, stTop, hf])).wf
    (wfSt_blk hwf l d _) nofun
  obtain ⟨B, st1, hB, hL, JJ, tail, hJJ, htail, hout, hsk, hobl, hax, hdrop, hregs⟩ :=
    walk_top hf hrun
  obtain ⟨live, clock, rfl, hl⟩ := liveAdd_step hL
  have hlive := fun y hy => (hl y).2 (.inl hy)
  have W := wpList_walkOK hB
  have hne : ∀ n, FreshAt (stTop st l d rL (kk + 1)) n → n ≠ rL := fun n h =>
    h.ne ⟨"r", kk, hrL, Nat.lt_succ_self kk⟩
  have hlow : ∀ b j, rL = freshName b j → j < st.next → False := fun b j h hj =>
    absurd (freshName_counter_inj (hrL.symm.trans h)) (by omega)
  have hn0 : ∀ x : P.Ident, st.nm[x]? ≠ some rL := fun x hx =>
    (hwf.nm_fresh x rL hx).2.elim fun b ⟨j, hn, hj, _⟩ => hlow b j hn hj
  have hn1 : ∀ x : P.Ident, st1.nm[x]? ≠ some rL := fun x hx =>
    (W.nm x rL hx).elim (hn0 x) fun h => hne rL h rfl
  have hcur : ∀ s : WSt P, (∀ x : P.Ident, s.nm[x]? ≠ some rL) → ∀ x ∈ S, curName s x ≠ some rL :=
    fun s hs x hx hc => (curName_cases hc).elim (hs x) fun ⟨_, _, h⟩ => Bool.false_ne_true
      ((h ▸ hav).symm.trans (havoid x (List.mem_append_left _ hx) "r" kk (h ▸ hrL)))
  have hback0 : st.back[rL]? = none := Option.eq_none_iff_forall_ne_some.2 fun x hx =>
    (hwf.back_fresh rL x hx).elim fun b ⟨j, h, hj⟩ => hlow b j h hj
  have htys : st1.tys[rL]? = some HasBool.boolTy := Classical.byContradiction fun h =>
    (W.tys rL (by simpa [stTop] using h)).elim (fun ⟨hm, _⟩ => Bool.false_ne_true (hav.symm.trans
      (havoid rL (List.mem_append_right _ (stmtsInits_mem_idents rL hm)) "r" kk hrL)))
      fun h => h.elim (fun ⟨x, hx⟩ => hn0 x hx) (hne rL · rfl)
  have hnext : kk < st1.next := Nat.lt_of_lt_of_le (Nat.lt_succ_self kk) W.next
  have hav1 : st1.avoid.contains rL = false := W.avoid ▸ hav
  have hrT : ∀ ty, tyOfName T Y rL = .ok ty →
      HasVal.valueOfTy F (HasBool.ttVal F) ty := fun ty h => by
    rcases hfin.1 rL _ htys with hT | ⟨-, hfa, -⟩ | ⟨b, j, hj, hle, -⟩
    · simp only [tyOfName, hT] at h
      exact Except.ok.inj h ▸ bool_valueOfTy (.inl rfl)
    · exact absurd (hav1.symm.trans (hfa "r" kk hrL)) Bool.false_ne_true
    · exact absurd hle (freshName_counter_inj (hrL.symm.trans hj) ▸ Nat.not_le.2 hnext)
  have hnEx : ¬ Ex rL := fun h => Nat.not_lt.2 hkk ((hEx rL h).1 "r" kk hrL)
  have hDT : DeadBelow (stTop st l d rL (kk + 1)) := fun b j h =>
    Nat.lt_of_lt_of_le (hD b j h) (Nat.le_succ_of_le hkk)
  obtain ⟨iT, hiT, hit⟩ : ∃ iT, resolveItems T Y tail.toList = .ok iT ∧ ((items = [] ∧ iT = []) ∨
      items = .plain (.cmd (.cmd (.init rL HasBool.boolTy (.det tt) .empty))) :: iT) := by
    by_cases htn : tail.isNil = true
    · rw [hout, ite_eq_left htn, Rope.toList_nil] at hres
      exact ⟨[], by rw [Rope.isNil_toList htn]; rfl, .inl ⟨(Except.ok.inj hres).symm, rfl⟩⟩
    · rw [hout, ite_eq_right htn, Rope.toList_app, Rope.toList_one] at hres
      obtain ⟨i0, iT, hi0, hiT, rfl⟩ := (resolveItems_append _ _ _ _).1 hres
      obtain ⟨i, _, hi, h0, rfl⟩ := resolveItems_cons_ok hi0
      obtain ⟨_, h1, rfl⟩ := resolveItem_init_det hi
      cases (resolveE_lit true).symm.trans h1
      exact ⟨iT, hiT, .inr (Except.ok.inj h0.symm ▸ rfl)⟩
  obtain ⟨iB, iM, iJ, hiB, hiM, hiJ, rfl⟩ := resolve_out3 (htail ▸ hiT)
  simp only [List.append_eq_nil_iff] at hit
  have hspec := hb (.name rL) nofun (stTop st l d rL (kk + 1)) B st1 hwfT hB T Y hfin iB hiB S
    hwfS Γ (fun h => hΓ (h.imp_right hobl.trans)) hwt.block havoid (fun y => Ex y ∨ y = rL)
    (fun y hy => hy.elim (fun hy => ⟨fun b j hj =>
      Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le ((hEx y hy).1 b j hj) hkk), (hEx y hy).2⟩) fun h =>
      ⟨fun b j hj => freshName_counter_inj (hrL.symm.trans (h.symm.trans hj)) ▸ Nat.lt_succ_self kk,
        h ▸ Classical.byContradiction fun h => hne rL (W.back rL fun h' => h (h'.trans hback0))
          rfl⟩)
    k _ (lab_body hLab) (fun y hy => (List.mem_singleton.1 hy).symm ▸
      ⟨⟨"r", kk, hrL, Nat.lt_succ_self kk⟩, hav, hn0, hback0⟩) hDT
    (fun n s h => KeyOK.of_le (st := st) rfl (Nat.le_succ_of_le hkk) (hLK n s h)) fun k hk => by
      simp [stTop, blkIn, Std.HashMap.getD_insert, Nat.ne_of_lt hk, hhigh k (by omega)]
  refine ⟨fun σ σL t cnd b tr hOn hreach hclaim => ?_, fun hf' => ?_,
    fun _ _ _ _ hOff => hOff.reach.elim⟩
  · obtain ⟨hnone, hOn0⟩ := top_entry (sb := st1) hOn ⟨rfl, rfl, rfl, rfl⟩ hlive contFV_body_sub
      hrL hav1 hnext hn1 (hcur st1 hn1) hnEx hrT
    cases hreach with | block hreach => ?_
    obtain ⟨h1, h2, wsub, hw, tr', hhit, hcl⟩ := hspec.1 σ _ t cnd b tr hOn0 hreach hclaim
    rcases hit with ⟨-, ⟨rfl, -⟩, -⟩ | rfl
    · nomatch hhit
    exact ⟨hobl ▸ h1, hsk ▸ SkObl.block [] h2, wsub, hw, [] ++ tr',
      .plain (init_run hF hnone) hhit.append_left.append_left, by simpa using hcl⟩
  subst hf'
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hJJ
  intro σ σL X evs o hOn hrun hfeas
  obtain ⟨hnone, hOn0⟩ := top_entry (sb := st1) hOn ⟨rfl, rfl, rfl, rfl⟩ hlive contFV_body_sub
    hrL hav1 hnext hn1 (hcur st1 hn1) hnEx hrT
  cases hrun with | block hrunB => ?_
  rename_i o
  rcases hspec.2.1 rfl σ _ _ evs _ hOn0 hrunB hfeas with
    ⟨h, -⟩ | ⟨tr, σL', hmain, hfe, hpost⟩
  · nomatch h
  obtain ⟨hdead, hsnap, hdisj, hold, hkr⟩ := body_regs (l := l) (stB := stTop st l d rL (kk + 1))
    (by simp) hwf hwfT hDT rfl (Nat.le_succ_of_le hkk)
    (fun v hv => ⟨"r", kk, by simpa [RE.vars, hrL] using hv, by simp [stTop]⟩) hB
  have hok : CarryOK F T Y B st1 σL' := by cases o <;> exact hpost.2.2.2.1
  have hcf := carr_walk (st := st) (stB := stTop st l d rL (kk + 1))
    (by simp) rfl (fun l' t h => (lab_body hLab l' t h).1) hwfT hB hdead hkr
    (fun x hx => havoid x (List.mem_append_right _ hx))
    (fun z hz => (List.mem_singleton.1 hz).symm ▸ ⟨⟨"r", kk, hrL, by simp [stTop]⟩, hav, hback0⟩)
  obtain ⟨tyf, hbd, htgty⟩ := carr_bound hcf hok
  have hrLM : rL ∉ (blkCarr st1 d).map (·.1) := hcf.tgv rL (.inl (.head _))
  have hent : ∀ x ∈ S, x ∈ contFV k → (σ x).isSome := fun x hx hv =>
    (hOn.defd x hx (contFV_tail_sub hv)).1
  have hfrS : ∀ {σa σb : SemanticStore P}, FreshInv Lc (fun y => Ex y ∨ y = rL)
      (stTop st l d rL (kk + 1)) σa → (∀ y, (σb y).isSome → (σa y).isSome) →
      FreshInv Lc Ex st σb := fun h hd =>
    h.mono rfl rfl rfl (Nat.le_succ_of_le hkk) (fun y hy => hy.elim .inl fun h => .inr
      fun b j hj => freshName_counter_inj (hrL.symm.trans (h.symm.trans hj)) ▸ hkk) hd
  have hu := update_facts σL rL (HasBool.ttVal F)
  cases o with
  | normal σ1 =>
    obtain ⟨hOn1, hSnap, hCFF, -, hBax, -, hEE⟩ := hpost
    have hax0 : r.ax = false := by rw [hax, hBax, Bool.false_and]
    rcases hit with ⟨rfl, ⟨rfl, rfl⟩, -⟩ | rfl
    · cases hmain
      refine .inr ⟨[], σL, .nil, nofun, ⟨hOn1.toOnCore.proj (D := [rL])
        (scopeAfter_sub S body) (fun _ _ h => h) hent hOn.undef (fun _ => rfl) (fun _ h => h)
        (fun y hy => (hu.2 y (fun h => hy (h ▸ .head _))).symm) hOn.canonL hOn.gtyped
        (fun x hx _ n hn h => hcur st hn0 x hx (hn.trans (congrArg _ (List.mem_singleton.1 h))))
        (hfrS hOn1.fresh fun y h => ?_), trivial⟩, snapFF_blk hregs hold fun l0 e he _ hp hne => ?_,
        carryFF_fin hF hregs hcf hOn1.canonL hOn.canonL
          (fun y _ hy => (hu.2 y (fun h => hy (h ▸ .head _))).symm) fun k _ => hCFF k,
        carryOK_fin hF hregs hcf hOn1.canonL hOn.canonL
          (fun y _ hy => (hu.2 y (fun h => hy (h ▸ .head _))).symm)
          (fun n hn => (hu.2 n fun h => hrLM (h ▸ hn)).symm ▸ tg_ok hcf hok n hn) hok, hax0, hdrop,
        exitEnds_blk hregs hold (fun _ _ h => h) hEE⟩
      · exact (Classical.em (rL = y)).elim (fun e => e ▸ hu.1 ▸ rfl) fun hy => (hu.2 y hy).symm ▸ h
      · exact (hu.2 e fun h => hkr _ (.head _) (h ▸ he)).symm.trans (hSnap l0 e he hp hne)
    · have hM := mg_ff hF hcf hOn1.canonL hiM hbd hCFF
      obtain ⟨trJ, hJ, hfJ⟩ := join_top_run (hJJ ▸ hiJ) fun x hx =>
        ev_join_holds (κ := .name rL) hF hOn1.canonL hOn1.reach (fun e he =>
          .inr (hSnap l e (hsnap e he) (mem_blkSnaps.1 he).1 (by simp))) hx
      refine .inr ⟨[] ++ (tr ++ [] ++ trJ), σL', .plain (init_run hF hnone)
        ((hmain.append hM).append hJ), by simpa using Trace.AssumptionsHold.append hfe hfJ,
        ⟨hOn1.toOnCore.proj (D := []) (scopeAfter_sub S body) (fun _ _ h => h) hent hOn.undef
          (fun _ => rfl) (fun _ h => h) (fun _ _ => rfl) hOn1.canonL hOn1.gtyped
          (fun _ _ _ _ _ h => nomatch h) (hfrS hOn1.fresh fun _ h => h), trivial⟩,
        snapFF_blk hregs hold fun l0 e he _ hp hne => hSnap l0 e he hp hne,
        carryFF_fin hF hregs hcf hOn1.canonL hOn1.canonL (fun _ _ _ => rfl) fun k _ => hCFF k,
        carryOK_fin hF hregs hcf hOn1.canonL hOn1.canonL (fun _ _ _ => rfl)
          (tg_ok hcf hok) hok, hax0, hdrop, exitEnds_blk hregs hold (fun _ _ h => h) hEE⟩
  | exit l0 σ1 =>
    rcases Classical.em (l0 = l) with rfl | hl
    · obtain ⟨hoff, hEnds, -, -, hm⟩ := hpost
      simp only [stTop, blkIn_labelDepth, ↓reduceIte] at hm
      obtain ⟨e, heR, heP, het, hSnap, hCore, hbelow⟩ := hm
      rcases hit with ⟨-, ⟨rfl, -⟩, -⟩ | rfl
      · cases hmain
        exact absurd (Option.some.inj (hu.1.symm.trans hoff.reach)) (HasBool.ttVal_ne_ffVal F)
      have hem : e ∈ blkSnaps st1 l0 := mem_blkSnaps.2 ⟨heP, hdead e heR⟩
      obtain ⟨hMr, ⟨hMoff, -, hMC⟩, hMs⟩ := mg_block hF hoff.canonL hiM hcf hbd
      have hMsnap : ∀ e ∈ B.regs.toList,
          mgStore F T Y st1 d σL' e = σL' e := fun e he => hMoff e (hcf.tgv e (.inr he))
      obtain ⟨trJ, hJ, hfJ⟩ := join_top_run (hJJ ▸ hiJ) fun x hx =>
        ev_join_exit (κ := .name rL) hF hMC ((hMoff rL hrLM).trans hoff.reach)
          (fun y hy => by
            simp only [RE.vars, List.mem_singleton] at hy
            exact hy ▸ .inr ((hMoff rL hrLM).trans hoff.reach)) (fun e' he' =>
          hMsnap e' (hsnap e' he') ▸ (Classical.em (e' = e)).elim (fun h => .inl (h ▸ het)) fun h =>
          .inr (hSnap l0 e' (hsnap e' he') (mem_blkSnaps.1 he').1 fun h' => h (Option.some.inj h')))
          ⟨e, hem, (hMsnap e heR).trans het⟩ hx
      refine .inr ⟨[] ++ (tr ++ [] ++ trJ), _, .plain (init_run hF hnone)
        ((hmain.append hMr).append hJ), by simpa using Trace.AssumptionsHold.append hfe hfJ, ?_⟩
      simp only [Outcome.block, ite_true, RunPost]
      have hV : ∀ x ∈ S, x ∈ contFV k → x ∈ (contFV k).filter (· ∈ S) := fun x hx hv =>
        List.mem_filter.2 ⟨hv, by simpa using hx⟩
      refine ⟨⟨onCore_mk (fun x hx hv n hn hln => ?_) (fun x hx hv => ?_)
        (fun x hx hv n hn hty => ?_) hent hOn.undef hCore.canon hMC (fun n w hw hY ty hty => ?_)
        (fun x hx hv n hn => hCore.ltyped x (scopeAfter_sub S body hx) (hV x hx hv) n hn)
        (hfrS hCore.fresh fun y h => by rwa [← hMs]), trivial⟩,
        snapFF_blk hregs hold fun l1 e' he' hl1 hp _ => ?_,
        carryFF_fin hF hregs hcf hoff.canonL hMC (fun y hy1 _ => hMoff y hy1)
          fun k hk _ _ _ _ => hbelow k _ _ _ _ hk,
        carryOK_fin hF hregs hcf hoff.canonL hMC (fun y hy1 _ => hMoff y hy1)
          (mg_tg hcf hok) hok, ?_, hdrop,
        exitEnds_blk hregs hold (fun l1 hl1 _ h => hl1 (Option.some.inj h).symm) hEnds.2⟩
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
          (hCore.defd x (scopeAfter_sub S body hx) (hV x hx hv)).1
        rw [hw]
        exact mg_here hcf hok (hCore.xagree x (scopeAfter_sub S body hx)
          (hV x hx hv) n hn hln (liveFrom_enter hwf rfl rfl rfl hln
            fun l' j hj _ _ htj => absurd (hLab l' j hj).1 (by omega)) w hw)
      · have hd := hCore.defd x (scopeAfter_sub S body hx) (hV x hx hv)
        exact ⟨hd.1, fun n hn => hMs n ▸ hd.2 n hn⟩
      · rw [hMoff n (htgty n hty)]
        exact hCore.alike x (scopeAfter_sub S body hx) (hV x hx hv) n hn hty
      · exact (mg_val hcf hok n).elim (fun h => hCore.gtyped n w (h.2 ▸ hw) hY ty hty)
          fun ⟨_, _, _, hr, _, hv, _⟩ => (hok _ _ _ _ _ hr).elim fun _ ⟨_, _, w', hw', h⟩ =>
            Option.some.inj (hw'.symm.trans (hv.symm.trans hw)) ▸ h ty hty
      · exact (hMsnap e' he').trans (hSnap l1 e' he' hp
          (by simpa using fun h : e' = e => hl1 (hdisj e heR l0 l1 heP (h ▸ hp))))
      · simp [hax, List.ne_nil_of_mem hem]
    · exact .inl ⟨rfl, l0, projectStore σ σ1, by simp [Outcome.block, hl]⟩

/-! ## The block case -/

include iIL in
/-- The walk of a block has the simulation property when the walks of its body (at the next
    depth, under every context) have it. -/
theorem stmtSpec_block {F : P.Factory} (hF : WellFormedSemanticEvalBase F) {Lc : List P.Ident}
    {κ : RE P} {d : Nat} {f : Bool} {l : String} {body : PStmts P} (md : MetaData P)
    (hb : ∀ κB, ListSpec F tE Lc κB (d + 1) f body) : StmtSpec F tE Lc κ d f (.block l body md) :=
  if hκ : κ = .top then hκ ▸ stmtSpec_block_top hF md hb else stmtSpec_block_var hF md hκ (hb κ)

end -- public section

end WP
end Imperative
