/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WP
public import Strata.Transform.Passive.ProgramProps

/-! # The state of the WP phase

The effect of each state primitive of the WP phase (`WM`) on the walk state: the result and the
final state of a run of `wFresh`, `wFreshBool`, `wFreshLike`, `wName`, `wDecl`, `liveAdd`,
`liveDel` and `wRen`.  The *current name* of a loop-free variable (`curName`) is the WP name a
read of it gets at a point: `wName` fixes it and keeps every defined one, `wDecl` undefines it
for its variable only, and `wRen` renames an expression's free variables to their current
names.

Key theorems: `wName_cases`, `wName_curName`, `wName_curName_keep`,
`wName_fresh`, `wDecl_spec`, `liveAdd_run`, `wRen_run`.

Key definitions: `curName`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P] [iW : WPOps P]
omit iLI iW

/-! ## Runs of the state primitives -/

/-- A successful run of `x >>= f` in the WP state monad is a successful run of `x` followed by
    a successful run of `f` on its result. -/
theorem wm_run_bind_ok {α β : Type} {x : WM P α} {f : α → WM P β} {s s' : WSt P} {b : β}
    (h : (x >>= f).run s = .ok (b, s')) :
    ∃ a s1, x.run s = .ok (a, s1) ∧ (f a).run s1 = .ok (b, s') := by
  rw [StateT.run_bind] at h
  cases hx : x.run s <;> rw [hx] at h <;> first | exact ⟨_, _, rfl, h⟩ | cases h

/-- A successful run of `pure a` in the WP state monad returns `a` and keeps the state. -/
theorem wm_run_pure_ok {α : Type} {a b : α} {s s' : WSt P}
    (h : (pure a : WM P α).run s = .ok (b, s')) : a = b ∧ s = s' := Prod.mk.inj (Except.ok.inj h)

/-- A run of a conditional in the WP state monad is a run of the branch the condition selects. -/
theorem wm_run_ite {α : Type} {c : Prop} [Decidable c] {x y : WM P α} {s : WSt P}
    {r : Except String (α × WSt P)} (h : (if c then x else y).run s = r) :
    (c ∧ x.run s = r) ∨ (¬ c ∧ y.run s = r) := by by_cases hc : c <;> simp_all

/-- A property of the walked prefix, the accumulator and the state that every step of a `forIn`
    loop body in the WP state monad keeps (the body continuing) holds after the loop. -/
theorem wm_forIn_inv {β : Type} (I : List P.Ident → β → WSt P → Prop)
    (f : P.Ident → β → WM P (ForInStep β))
    (hf : ∀ S y b s b' s', I S b s → (f y b).run s = .ok (b', s') →
      ∃ c, b' = .yield c ∧ I (S ++ [y]) c s') :
    ∀ (l S : List P.Ident) (b : β) (s : WSt P) (r : β) (s' : WSt P), I S b s →
      (forIn l b f).run s = .ok (r, s') → I (S ++ l) r s'
  | [], S, b, s, r, s', hI, h => by simpa [← (wm_run_pure_ok h).1, ← (wm_run_pure_ok h).2] using hI
  | y :: l, S, b, s, r, s', hI, h => by
    obtain ⟨b', s1, hy, h⟩ := wm_run_bind_ok (List.forIn_cons f y l b ▸ h)
    obtain ⟨c, rfl, hI'⟩ := hf S y b s b' s1 hI hy
    simpa using wm_forIn_inv I f hf l (S ++ [y]) c s1 r s' hI' h

/-- A run of `wFresh b` returns the name `freshIn` picks and advances the counter. -/
theorem wFresh_run (b : String) (st : WSt P) :
    (wFresh b).run st =
      .ok ((freshIn st.avoid b st.next).1, { st with next := (freshIn st.avoid b st.next).2 }) :=
  rfl

/-- A run of `wFreshBool b` returns the name `freshIn` picks, advances the counter and gives
    the name the Boolean type. -/
theorem wFreshBool_run (b : String) (st : WSt P) :
    (wFreshBool b).run st = .ok ((freshIn st.avoid b st.next).1,
      { st with
        next := (freshIn st.avoid b st.next).2
        tys := st.tys.insert (freshIn st.avoid b st.next).1 HasBool.boolTy }) := rfl

/-- A run of `liveDel x` removes `x` from the live set. -/
theorem liveDel_run (x : P.Ident) (st : WSt P) :
    (liveDel x).run st = .ok ((), { st with live := st.live.erase x }) := rfl

/-- A run of `liveAdd xs` changes only the live set and the clock: the live set gains the names
    of `xs`, present names keep their stamps, new names are stamped at least the old clock, and
    the clock does not decrease. -/
theorem liveAdd_run (xs : List P.Ident) (st : WSt P) :
    ∃ live clock, (liveAdd xs).run st = .ok ((), { st with live := live, clock := clock }) ∧
      (∀ y : P.Ident, live.contains y ↔ st.live.contains y ∨ y ∈ xs) ∧
      (∀ (y : P.Ident) (s : Nat), st.live[y]? = some s → live[y]? = some s) ∧
      (∀ (y : P.Ident) (s : Nat), st.live[y]? = none → live[y]? = some s →
        st.clock ≤ s ∧ s < clock) ∧
      st.clock ≤ clock := by
  refine ⟨_, _, rfl, ?_⟩
  generalize st.live = m, st.clock = c
  induction xs generalizing m c with
  | nil => simp +contextual
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · obtain ⟨h1, h2, h3, h4⟩ := ih m c
      exact ⟨fun y => (h1 y).trans (by grind), h2, h3, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := ih (m.insert x c) (c + 1)
      refine ⟨fun y => (h1 y).trans (by grind), fun y s h => h2 y s (by grind), fun y s h h' => ?_,
        Nat.le_of_succ_le h4⟩
      rcases Classical.em (y = x) with rfl | hy
      · have he := Option.some.inj ((h2 y c (by simp)).symm.trans h')
        exact ⟨Nat.le_of_eq he, he ▸ h4⟩
      · exact (h3 y s (by simp [Std.HashMap.getElem?_insert, Ne.symm hy, h]) h').imp_left
          Nat.le_of_succ_le

/-- A successful run of `liveAdd xs` changes only the live set and the clock, adding `xs`. -/
theorem liveAdd_step {xs : List P.Ident} {s s' : WSt P} {u : Unit}
    (h : (liveAdd xs).run s = .ok (u, s')) : ∃ live clock,
      s' = { s with live := live, clock := clock } ∧
      ∀ y : P.Ident, live.contains y = true ↔ s.live.contains y = true ∨ y ∈ xs := by
  obtain ⟨live, clock, h', hlv, -⟩ := liveAdd_run xs s
  exact ⟨live, clock, (Prod.mk.inj (Except.ok.inj (h.symm.trans h'))).2, hlv⟩

/-! ## Current names -/

/-- The current WP name of the loop-free variable `x` at a point whose walk state is `st`:
    its recorded renaming, or `x` itself when no later declaration of `x` was met, or `none`
    when a later declaration was met and no read after the point fixed the name. -/
@[expose] def curName (st : WSt P) (x : P.Ident) : Option P.Ident :=
  match st.nm[x]? with
  | some n => some n
  | none => if st.taken.contains x then none else some x

/-- A current name is the recorded renaming, or the variable itself when it has none and no
    later declaration of it was met. -/
theorem curName_cases {st : WSt P} {z m : P.Ident} (h : curName st z = some m) :
    st.nm[z]? = some m ∨ (st.nm[z]? = none ∧ st.taken.contains z = false ∧ m = z) := by
  grind [curName]

/-- Two walk states with the same renamings and the same declared names give every variable
    the same current name. -/
theorem curName_eq_of_nm_taken {sa sb : WSt P} (hnm : sa.nm = sb.nm) (ht : sa.taken = sb.taken)
    (x : P.Ident) : curName sa x = curName sb x := by simp [curName, hnm, ht]

/-! ## Runs of the naming primitives -/

include iW
/-- A run of `wFreshLike x` returns the name `freshIn` picks for the base of `x`, advances the
    counter and gives the name the type of `x`. -/
theorem wFreshLike_run (x : P.Ident) (st : WSt P) :
    (wFreshLike x).run st = .ok ((freshIn st.avoid (baseOf x) st.next).1,
      { st with
        next := (freshIn st.avoid (baseOf x) st.next).2
        tyOf := st.tyOf.insert (freshIn st.avoid (baseOf x) st.next).1 x }) := rfl

/-- A run of `wName x` is one of its three cases: the recorded renaming of `x` (state kept),
    `x` itself when no later declaration of `x` was met (state kept), or a fresh name recorded
    as the renaming of `x`. -/
theorem wName_cases {x n : P.Ident} {st st' : WSt P} (h : (wName x).run st = .ok (n, st')) :
    (st.nm[x]? = some n ∧ st' = st) ∨
    (st.nm[x]? = none ∧ st.taken.contains x = false ∧ n = x ∧ st' = st) ∨
    (st.nm[x]? = none ∧ st.taken.contains x = true ∧
      n = (freshIn st.avoid (baseOf x) st.next).1 ∧
      st' = { st with
        next := (freshIn st.avoid (baseOf x) st.next).2
        nm := st.nm.insert x n
        back := st.back.insert n x }) := by
  simp only [wName, StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h <;> (try split at h) <;> cases h <;> simp_all

/-- A run of `wName x` always succeeds. -/
theorem wName_ok (x : P.Ident) (st : WSt P) : ∃ n st', (wName x).run st = .ok (n, st') := by
  simp only [wName, StateT.run_bind, StateT.run_get, pure_bind]
  split <;> (try split) <;> exact ⟨_, _, rfl⟩

/-- A run of `wDecl x` is the run of `wName x` followed by erasing the renaming of `x` and
    recording a later declaration of `x`. -/
theorem wDecl_run {x n : P.Ident} {st s1 : WSt P} (h : (wName x).run st = .ok (n, s1)) :
    (wDecl x).run st = .ok (n, { s1 with nm := s1.nm.erase x, taken := s1.taken.insert x }) := by
  simp only [wDecl, StateT.run_bind, h]
  rfl

/-- After a run of `wName x` returning `n`, the current name of `x` is `n`. -/
theorem wName_curName {x n : P.Ident} {st st' : WSt P} (h : (wName x).run st = .ok (n, st')) :
    curName st' x = some n := by
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ <;> grind [curName]

/-- A run of `wName x` keeps every defined current name. -/
theorem wName_curName_keep {x n : P.Ident} {st st' : WSt P} (h : (wName x).run st = .ok (n, st'))
    (z m : P.Ident) (hz : curName st z = some m) : curName st' z = some m := by
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ <;> grind [curName]

include iLI
/-- A run of `wName x` changes only the counter (which does not decrease), the renamings and
    the back map. -/
theorem wName_state {x n : P.Ident} {st st' : WSt P} (h : (wName x).run st = .ok (n, st')) :
    st.next ≤ st'.next ∧ st' = { st with next := st'.next, nm := st'.nm, back := st'.back } := by
  obtain ⟨k, hk, hn, -⟩ := freshIn_spec st.avoid (baseOf x) st.next
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ <;> grind

/-- A name `wName x` creates (no recorded renaming of `x`, a later declaration of `x` met) is
    `freshName (baseOf x) k` for a counter `k` at least the old counter and past the new one,
    not avoided, and recorded as the renaming of `x` and in the back map. -/
theorem wName_fresh {x n : P.Ident} {st st' : WSt P} (h : (wName x).run st = .ok (n, st'))
    (hx : st.nm[x]? = none) (ht : st.taken.contains x = true) :
    ∃ k, n = freshName (baseOf x) k ∧ st.next ≤ k ∧ st'.next = k + 1 ∧
      st.avoid.contains n = false ∧ st'.nm[x]? = some n ∧ st'.back[n]? = some x := by
  obtain ⟨k, hk, hn, hav⟩ := freshIn_spec st.avoid (baseOf x) st.next
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩ <;> grind

/-- A run of `wDecl x` returns what `wName x` returns, after which `x` has no current name and
    every other variable keeps its current name; it changes only the counter (which does not
    decrease), the renamings, the back map, and records a later declaration of `x`. -/
theorem wDecl_spec {x n : P.Ident} {st st' : WSt P} (h : (wDecl x).run st = .ok (n, st')) :
    (∃ s1, (wName x).run st = .ok (n, s1)) ∧ curName st' x = none ∧
      (∀ z, z ≠ x → curName st' z = curName st z) ∧ st.next ≤ st'.next ∧
      st' = { st with
        next := st'.next
        nm := st'.nm
        taken := st.taken.insert x
        back := st'.back } := by
  obtain ⟨n1, s1, h1⟩ := wName_ok x st
  cases (wDecl_run h1).symm.trans h
  obtain ⟨hle, hs⟩ := wName_state h1
  refine ⟨⟨_, h1⟩, by simp [curName], fun z hz => ?_, hle, by rw [hs]⟩
  rcases wName_cases h1 with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
    grind [curName]

/-! ## Renamed expressions -/

/-- A run of `wRen e` returns `e` with a renaming `ren` and the list `rd` of the names it reads:
    `ren` maps free variables of `e` to their current names (when distinct), every free variable
    of `e` has a current name in `rd` (itself or its image under `ren`), and every name of `rd`
    is the current name of a free variable of `e`. The run changes only the counter (which does
    not decrease), the renamings and the back map, and keeps every defined current name. -/
theorem wRen_run {e : P.Expr} {st st' : WSt P} {we : WExpr P} {rd : List P.Ident}
    (h : (wRen e).run st = .ok ((we, rd), st')) :
    (∃ ren, we = .user e ren ∧
      (∀ p ∈ ren, p.1 ∈ exprFV e ∧ curName st' p.1 = some p.2 ∧ p.2 ≠ p.1) ∧
      (∀ y ∈ exprFV e, ∃ n, curName st' y = some n ∧ n ∈ rd ∧ (n = y ∨ (y, n) ∈ ren)) ∧
      (∀ n ∈ rd, ∃ y ∈ exprFV e, curName st' y = some n)) ∧
    st.next ≤ st'.next ∧ st' = { st with next := st'.next, nm := st'.nm, back := st'.back } ∧
    (∀ z m, curName st z = some m → curName st' z = some m) := by
  simp only [wRen] at h
  obtain ⟨r, s1, hfor, hp⟩ := wm_run_bind_ok h
  obtain ⟨⟨⟩, ⟨⟩⟩ := wm_run_pure_ok hp
  refine (wm_forIn_inv (fun S r s => ((∀ p ∈ r.1, p.1 ∈ S ∧ curName s p.1 = some p.2 ∧ p.2 ≠ p.1) ∧
      (∀ y ∈ S, ∃ n, curName s y = some n ∧ n ∈ r.2 ∧ (n = y ∨ (y, n) ∈ r.1)) ∧
      (∀ n ∈ r.2, ∃ y ∈ S, curName s y = some n)) ∧
    st.next ≤ s.next ∧ s = { st with next := s.next, nm := s.nm, back := s.back } ∧
    (∀ z m, curName st z = some m → curName s z = some m)) _ ?_ _ [] _ _ _ _ ?_ hfor).imp_left
    fun h => ⟨_, rfl, h⟩
  · intro S y b s b' s' ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ hb
    obtain ⟨n, s2, hn, hb⟩ := wm_run_bind_ok hb
    have hc := wName_curName hn
    have hk := wName_curName_keep hn
    obtain ⟨hle, hs⟩ := wName_state hn
    split at hb <;> cases hb <;> exact ⟨_, rfl, by grind⟩
  · exact ⟨⟨nofun, nofun, nofun⟩, Nat.le_refl _, rfl, fun _ _ => id⟩

end
end WP
end Imperative


