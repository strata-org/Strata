/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOutTyping
public import Strata.Transform.WP.WPOverCmd
public import Strata.Transform.WP.WPOverFacts
import Strata.Transform.WP.WPOverEmit
import Strata.Transform.WP.WPOverEffectsWalk
import Strata.Transform.WP.WPProps
import Strata.Transform.WP.WPOverEval
import Strata.Util.ExceptProps

/-! # The items of the WP walk are typed

Every walk of a fragment typed under a typing `Γ` of its scope emits items typed against the
final type maps `T`, `Y` (`LOK`) when `Γ` agrees with them at the state before the fragment
(`TyCtx`), the variables of the reach context are Boolean, and the names with a type reference
have no final declared type; the walk adds Boolean exit snapshots (`PendStep`) and, when an
obligation follows, typed carried merges (`CarStep`) and assigned names with ground final types
(`AOK`), and keeps the names with a type reference without a declared type (`DisjInv`)
(`TypSpec`, `wpList_typSpec`).  Hence the output of `wpEntry` is well typed for every typing
predicate with the laws `TypingLaws` (`wpEntry_wellTyped_of`).

Key definitions: `DisjInv`, `CarStep`, `PendStep`, `AOK`, `TypSpec`, `SRFacts`.

Key theorems: `wpList_typSpec`, `wpEntry_wellTyped_of`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iHS : HasSubstFvar P] [iHI : HasIdent P]
  [iL : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHV : HasFvars P] [iW : WPLang P]
  [iLF : LawfulHasFvars P]

variable {Lc : List P.Ident} {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}

/-! ## Final types along the walk -/

omit iW iLF in
/-- The final type maps keep the declared types of the input state of a walk step (`WalkCore`)
    when they keep those of its output state, the declared names being loop-free locals avoided
    if they have the form of a fresh name. -/
theorem FinalOK.back_walk {D : List P.Ident} {s s' : WSt P} (hw : WalkCore D s s') (hwf : WFSt s)
    (hd : ∀ x ∈ D, x ∈ Lc ∧ AvoidedIfFresh s x) (h : FinalOK Lc s' T Y) : FinalOK Lc s T Y := by
  refine ⟨fun n ty hn => hw.tys_final hwf hd h.1 hn, fun n x hn => h.2.1 n x (hw.tyOf_keep hwf hn),
    fun n hn => ?_⟩
  rcases h.2.2 n hn with hT | ⟨b, j, hj, hn', ha⟩
  · exact (Classical.em (s'.tyOf[n]? = s.tyOf[n]?)).elim (.inl <| · ▸ hT) fun he =>
      .inr ((hw.tyOf n he).imp fun b ⟨j, hj, ha, hn'⟩ => ⟨j, hj, hn', ha⟩)
  · exact .inr ⟨b, j, hj, Nat.le_trans hw.next hn', hw.avoid ▸ ha⟩

omit iL iW iLF in
/-- The final type maps keep the declared types of a state when they keep those of a later state
    with the same declared types, type references and avoided names, at least the same names
    recorded as declared, and a counter at least as large. -/
theorem FinalOK.back_le {s s' : WSt P} (ht : s'.tys = s.tys) (ho : s'.tyOf = s.tyOf)
    (ha : s'.avoid = s.avoid) (hk : ∀ y, s.taken.contains y = true → s'.taken.contains y = true)
    (hn : s.next ≤ s'.next) (h : FinalOK Lc s' T Y) : FinalOK Lc s T Y := by
  refine ⟨fun n ty hn' => ?_, fun n x hx => h.2.1 n x (ho ▸ hx), fun n hn' => ?_⟩
  · rcases h.1 n ty (ht ▸ hn') with h1 | ⟨h1, h2, h3⟩ | ⟨b, j, h1, h2, h3⟩
    · exact .inl h1
    · exact .inr (.inl ⟨h1, fun b j e => ha ▸ h2 b j e,
        Bool.eq_false_iff.2 fun hc => by simp [hk n hc] at h3⟩)
    · exact .inr (.inr ⟨b, j, h1, Nat.le_trans hn h2, ha ▸ h3⟩)
  · rcases h.2.2 n hn' with h1 | ⟨b, j, h1, h2, h3⟩
    · exact .inl (ho ▸ h1)
    · exact .inr ⟨b, j, h1, Nat.le_trans hn h2, ha ▸ h3⟩

omit iL iW iLF in
/-- The final type maps keep the declared types of a state when they keep those of the state after
    drawing a fresh name (with a counter from the state's counter on, not avoided) and giving it a
    type. -/
theorem FinalOK.back_draw {s : WSt P} {b : String} {k : Nat} {ty : P.Ty}
    (hk : s.next ≤ k) (hav : s.avoid.contains (freshName b k) = false)
    (h : FinalOK Lc { s with next := k + 1, tys := s.tys.insert (freshName b k) ty } T Y) :
    FinalOK Lc s T Y := by
  refine ⟨fun n ty' hn => ?_, h.2.1, fun n hn => ?_⟩
  · by_cases hn' : n = freshName b k
    · exact .inr (.inr ⟨b, k, hn', hk, hn' ▸ hav⟩)
    · rcases h.1 n ty' (by simpa [Std.HashMap.getElem?_insert, Ne.symm hn'] using hn) with
        h1 | h1 | ⟨b', j, h1, h2, h3⟩
      · exact .inl h1
      · exact .inr (.inl h1)
      · exact .inr (.inr ⟨b', j, h1, by simp at h2; omega, h3⟩)
  · rcases h.2.2 n hn with h1 | ⟨b', j, h1, h2, h3⟩
    · exact .inl h1
    · exact .inr ⟨b', j, h1, by simp at h2; omega, h3⟩

omit iW iLF in
/-- A name drawn before the state `s` (a fresh name with a counter below `s.next`, not avoided)
    keeps, in the final type maps, its declared type at `s`. -/
theorem FinalOK.drawn {s : WSt P} (h : FinalOK Lc s T Y) {n : P.Ident} {ty : P.Ty}
    (hn : s.tys[n]? = some ty) (hav : s.avoid.contains n = false)
    (hj : ∃ b j, n = freshName b j ∧ j < s.next) : T[n]? = some ty := by
  obtain ⟨b, j, rfl, hj⟩ := hj
  rcases h.1 _ ty hn with h1 | ⟨-, h2, -⟩ | ⟨b', j', h1, h2, -⟩
  · exact h1
  · simp [h2 b j rfl] at hav
  · exact absurd (freshName_counter_inj h1) (by omega)

omit iW iLF in
/-- A walk step keeps the declared type of a name drawn before it. -/
theorem WalkCore.tys_keep {D : List P.Ident} {s s' : WSt P} (hw : WalkCore D s s')
    (hwf : WFSt s) (hd : ∀ x ∈ D, AvoidedIfFresh s x) {n : P.Ident} {ty : P.Ty}
    (hn : s.tys[n]? = some ty) (hav : s.avoid.contains n = false)
    (hj : ∃ b j, n = freshName b j ∧ j < s.next) : s'.tys[n]? = some ty := by
  refine Classical.byContradiction fun hne => ?_
  rcases hw.tys n (fun he => hne (he ▸ hn)) with ⟨h1, -⟩ | ⟨x, hx⟩ | hf
  · obtain ⟨b, j, rfl, -⟩ := hj
    simp [hd _ h1 b j rfl] at hav
  · simp [hwf.nm_untyped hx] at hn
  · exact hf.ne hj rfl

omit iLB iHI iL iLF in
/-- A name with a final declared type has it as its final type. -/
theorem tyOfName_T {n : P.Ident} {ty : P.Ty} (h : T[n]? = some ty) : tyOfName T Y n = .ok ty := by
  simp [tyOfName, h, pure, Except.pure]

omit iLB iHI iL iLF in
/-- A copy name (one with a type reference to `x` and no declared type in the final maps) has
    the final types of `x`. -/
theorem tyOfName_copy {c x : P.Ident} {τ : P.Ty} (hT : T[c]? = none) (hY : Y[c]? = some x)
    (h : tyOfName T Y c = .ok τ) : tyOfName T Y x = .ok τ := by
  simp only [tyOfName, hT, hY, Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · rename_i ty hx
    cases h
    simp [tyOfName, hx, pure, Except.pure]
  · cases h

/-! ## Names with a type reference have no declared type -/

/-- No name with a type reference has a declared type. -/
@[expose] def DisjInv (st : WSt P) : Prop :=
  ∀ (n x : P.Ident), st.tyOf[n]? = some x → st.tys[n]? = none

omit iL iW iLF in
/-- A state step keeps `DisjInv` when the declared types change only at names without a type
    reference after it, and every new type reference is of a name without a declared type. -/
theorem DisjInv.step {s s' : WSt P} (h : DisjInv s)
    (ht : ∀ m : P.Ident, s'.tys[m]? ≠ s.tys[m]? → s'.tyOf[m]? = none)
    (ho : ∀ m x : P.Ident, s'.tyOf[m]? = some x → s.tyOf[m]? = some x ∨ s'.tys[m]? = none) :
    DisjInv s' := fun m x hm => by
  rcases ho m x hm with h1 | h1
  · exact Classical.byContradiction fun hne =>
      (by simp [ht m fun he => hne (he.trans (h m x h1))] at hm)
  · exact h1

omit iW iLF in
/-- A fresh name of a well-formed state (a counter from its counter on) has no type reference. -/
theorem WFSt.tyOf_none {s : WSt P} (hw : WFSt s) {b : String} {k : Nat} (hk : s.next ≤ k) :
    s.tyOf[freshName (P := P) b k]? = none :=
  Option.eq_none_iff_forall_ne_some.2 fun x hx => by
    obtain ⟨b', j, he, hj⟩ := hw.tyOf_fresh _ x hx
    exact absurd (freshName_counter_inj he) (by omega)

omit iW iLF in
/-- A fresh name of a well-formed state, not avoided, has no declared type. -/
theorem WFSt.tys_none {s : WSt P} (hw : WFSt s) {b : String} {k : Nat} (hk : s.next ≤ k)
    (hav : s.avoid.contains (freshName (P := P) b k) = false) :
    s.tys[freshName (P := P) b k]? = none :=
  Option.eq_none_iff_forall_ne_some.2 fun ty hty => by
    rcases hw.tys_keys (freshName b k) (by simp [hty]) with h | ⟨-, h⟩ | ⟨⟨b', j, he, hj⟩, -⟩
    · simp [h] at hav
    · simp [h b k rfl] at hav
    · exact absurd (freshName_counter_inj he) (by omega)

omit iL iW iLF in
/-- Giving a name without a type reference a declared type keeps `DisjInv`. -/
theorem DisjInv.ins {s s' : WSt P} (h : DisjInv s) {n : P.Ident} {ty : P.Ty}
    (hn : s.tyOf[n]? = none) (ht : s'.tys = s.tys.insert n ty) (ho : s'.tyOf = s.tyOf) :
    DisjInv s' := by
  refine DisjInv.step h (fun m hm => ?_) fun m x hm => .inl (ho ▸ hm)
  rw [ho]
  by_cases he : n = m
  · exact he ▸ hn
  · simp [ht, Std.HashMap.getElem?_insert, he] at hm

omit iW iLF in
/-- Giving a fresh name of a well-formed state a declared type keeps `DisjInv`. -/
theorem DisjInv.draw {s s' : WSt P} (h : DisjInv s) (hw : WFSt s) {b : String} {k : Nat}
    {ty : P.Ty} (hk : s.next ≤ k) (ht : s'.tys = s.tys.insert (freshName b k) ty)
    (ho : s'.tyOf = s.tyOf) : DisjInv s' := h.ins (hw.tyOf_none hk) ht ho

omit iL iW iLF in
/-- A state with the declared types and type references of a state with `DisjInv` has it. -/
theorem DisjInv.of_eq {s s' : WSt P} (h : DisjInv s) (ht : s'.tys = s.tys)
    (ho : s'.tyOf = s.tyOf) : DisjInv s' := fun n x hn => ht ▸ h n x (ho ▸ hn)

omit iW iLF in
/-- Drawing a fresh name of a well-formed state, not avoided, with a type reference keeps
    `DisjInv`. -/
theorem DisjInv.copy {s s' : WSt P} (h : DisjInv s) (hw : WFSt s) {b : String} {k : Nat}
    {y : P.Ident} (hk : s.next ≤ k) (hav : s.avoid.contains (freshName (P := P) b k) = false)
    (ht : s'.tys = s.tys) (ho : s'.tyOf = s.tyOf.insert (freshName b k) y) : DisjInv s' := by
  refine DisjInv.step h (fun m hm => absurd (ht ▸ rfl) hm) fun m x hm => ?_
  rw [ho, Std.HashMap.getElem?_insert] at hm
  split at hm
  · rename_i he
    exact .inr (by rw [ht, ← beq_iff_eq.1 he]; exact hw.tys_none hk hav)
  · exact .inl hm

/-! ## The typing property of a walk -/

section
variable (Typ : P.Expr → P.Ty → Prop) (Ground : P.Ty → Prop)

/-- The carried merges of the walk output state `st'` are those of the input state `st` and,
    when an obligation follows the fragment (`fol`), typed `set` items. -/
@[expose] def CarStep (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident)
    (fol : Bool) (st st' : WSt P) : Prop :=
  ∀ k (q : P.Ident × WExpr P × P.Ident), q ∈ st'.carries.getD k [] →
    q ∈ st.carries.getD k [] ∨ (fol = true → PlainOK Typ Ground T Y (.set q.1 (some q.2.1)))

/-- The exit snapshots of the walk output state `st'` are those of the input state `st` and
    names with the Boolean final type. -/
@[expose] def PendStep (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident)
    (st st' : WSt P) : Prop :=
  ∀ l e, e ∈ st'.pending.getD l [] → e ∈ st.pending.getD l [] ∨
    tyOfName T Y e = .ok HasBool.boolTy

/-- The names a walk result assigns have ground final types. -/
@[expose] def AOK (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident)
    (r : WRes P) : Prop :=
  ∀ n, r.A.contains n = true → ∃ τ, tyOfName T Y n = .ok τ ∧ Ground τ

/-- **The typing property of the walk `m` of a fragment `ss`** under the reach context `κ`, for
    the loop-free locals `Lc`, the name set `N` of the nondeterministic values, the scopes
    satisfying `wf`, and the obligation bit `fol`: for every walk from a well-formed state `st`
    in which no name with a type reference has a declared type (`DisjInv`) to `st'` with result
    `r`, final type maps `T`, `Y` extending `st'`, every scope `S` and every typing `Γ` of it
    under which `ss` is typed, the names of `S` and `ss` being avoided if they have the form of a
    fresh name, and a Boolean reach context:
    * `st'` satisfies `DisjInv`, the new exit snapshots are Boolean, and the output has a
      branching item only when it has an obligation;
    * when `T` gives no declared type to the names with a type reference at `st'`, and `Γ` agrees
      with the final types at `st'` if an obligation follows or the output has one: the new
      carried merges are typed when an obligation follows, the output is typed (`LOK`), and the
      assigned names have ground final types when an obligation follows. -/
@[expose] def TypSpec (Lc : List P.Ident) (N : P.Ident → Prop) (κ : RE P) (m : WM P (WRes P))
    (ss : PStmts P) (wf : List P.Ident → Prop) (fol : Bool) : Prop :=
  ∀ st r st', WFSt st → m.run st = .ok (r, st') →
  ∀ (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident), FinalOK Lc st' T Y →
  ∀ S, wf S → ∀ Γ, Block.ExprsTyped Typ Γ ss → Block.nondetGround Ground N Γ ss →
  (∀ x ∈ S ++ Block.idents ss, AvoidedIfFresh st x) → REOK T Y κ → DisjInv st →
  DisjInv st' ∧ PendStep T Y st st' ∧
  (r.out.toList.any WItem.isBranching = true → r.hasObl = true) ∧
  ((∀ (n x : P.Ident), st'.tyOf[n]? = some x → T[n]? = none) →
    (fol = true ∨ r.hasObl = true → TyCtx T Y st' S Γ) →
    CarStep Typ Ground T Y fol st st' ∧ LOK Typ Ground T Y fol r.out.toList ∧
      (fol = true → AOK Ground T Y r))

/-- `TypSpec` of a statement-list walk, for the walks that occur: under `top`, no obligation
    follows the list. -/
abbrev ListTypSpec (Lc : List P.Ident) (N : P.Ident → Prop) (κ : RE P) (d : Nat) (fEnd : Bool)
    (ss : PStmts P) : Prop :=
  (κ = .top → fEnd = false) →
  TypSpec Typ Ground Lc N κ (wpList κ d fEnd ss) ss (fun S => Block.WellScoped Lc S ss) fEnd

/-- `TypSpec` of a statement walk. -/
abbrev StmtTypSpec (Lc : List P.Ident) (N : P.Ident → Prop) (κ : RE P) (d : Nat) (f : Bool)
    (s : PStmt P) : Prop :=
  TypSpec Typ Ground Lc N κ (wpStmt κ d f s) [s] (fun S => Stmt.WellScoped Lc S s) f
end

section
variable {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop} {N : P.Ident → Prop}

omit iL iLF in
/-- The walk of the empty list has the typing property. -/
theorem listTypSpec_nil (κ : RE P) (d : Nat) (fEnd : Bool) :
    ListTypSpec Typ Ground Lc N κ d fEnd [] := fun _ _ _ _ _ h => by
  simp only [wpList, StateT.run_pure] at h
  cases h
  refine fun _ _ _ _ _ _ _ _ _ _ hD => ⟨hD, fun _ _ h => .inl h, by simp [Rope.toList_nil],
    fun _ _ => ⟨fun _ _ h => .inl h, by simp [Rope.toList_nil, LOK], fun _ n hn => ?_⟩⟩
  simp at hn
end

omit iDE iBE iLB iHS iHI iL iHa iW iLF in
/-- The expressions of a statement followed by a list are typed: those of the statement under
    `Γ`, and those of the list under `Γ` extended with the statement's definitions. -/
theorem Block.ExprsTyped.cons' {Typ : P.Expr → P.Ty → Prop} {Γ : VarTyping P} {s : PStmt P}
    {rest : PStmts P} (h : Block.ExprsTyped Typ Γ (s :: rest)) :
    Block.ExprsTyped Typ Γ [s] ∧
      Block.ExprsTyped Typ (Γ.extend (Stmt.typedDefinedVars s)) rest :=
  ⟨⟨⟨h.1.1, trivial⟩, ⟨h.2.1.1, trivial⟩, ⟨h.2.2.1, trivial⟩⟩, h.1.2, h.2.1.2, h.2.2.2⟩

omit iDE iBE iLB iHB iHS iHI iL iHa iW iLF in
/-- The nondeterministic values of a statement followed by a list are ground: those of the
    statement under `Γ`, and those of the list under `Γ` extended with the statement's
    definitions. -/
theorem Block.nondetGround.cons' {Ground : P.Ty → Prop} {N : P.Ident → Prop} {Γ : VarTyping P}
    {s : PStmt P} {rest : PStmts P} (h : Block.nondetGround Ground N Γ (s :: rest)) :
    Block.nondetGround Ground N Γ [s] ∧
      Block.nondetGround Ground N (Γ.extend (Stmt.typedDefinedVars s)) rest :=
  ⟨⟨h.1, trivial⟩, h.2⟩

section
variable {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop} {N : P.Ident → Prop}

omit iLF in
/-- The walk of `s :: rest` has the typing property when the walks of `s` (for every obligation
    bit) and of `rest` have it. -/
theorem listTypSpec_cons {κ : RE P} {d : Nat} {fEnd : Bool} {s : PStmt P} {rest : PStmts P}
    (hs : ∀ f, StmtTypSpec Typ Ground Lc N κ d f s)
    (hr : ListTypSpec Typ Ground Lc N κ d fEnd rest) :
    ListTypSpec Typ Ground Lc N κ d fEnd (s :: rest) := by
  intro htop st R st' hwf hrun T Y hfin S ⟨hwfs, hwfr⟩ Γ hty hng hav hκ hD
  obtain ⟨hts, htr⟩ := Block.ExprsTyped.cons' hty
  obtain ⟨hns, hnr⟩ := Block.nondetGround.cons' hng
  obtain ⟨r, st1, a, st2, h1, h2, hcase⟩ := wpList_run_cons hrun
  have hw1 := wpList_walkOK h1
  have hw2 := wpStmt_walkOK h2
  have hdI : ∀ x ∈ stmtsInits rest, AvoidedIfFresh st x := fun x hx =>
    hav x (by simp [Block.idents, (wfl_inits_scope rest hwfr hx).2.1])
  have hwf1 : WFSt st1 := hw1.wf hwf hdI
  have hav1 : ∀ x ∈ S ++ Block.idents [s], AvoidedIfFresh st1 x := fun x hx b j e =>
    hw1.avoid ▸ hav x (by grind [Block.idents]) b j e
  obtain ⟨hn2, ht2, hc2, hp2, hfin2, hty2, hto2⟩ : st2.nm = st'.nm ∧ st2.taken = st'.taken ∧
      (∀ k, st2.carries.getD k [] = st'.carries.getD k []) ∧
      (∀ l, st2.pending.getD l [] = st'.pending.getD l []) ∧ FinalOK Lc st2 T Y ∧
      st'.tys = st2.tys ∧ st'.tyOf = st2.tyOf := by
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
      exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, hfin, rfl, rfl⟩
  have hcur2 : ∀ z, curName st2 z = curName st' z := curName_eq_of_nm_taken hn2 ht2
  have hfin1 : FinalOK Lc st1 T Y := FinalOK.back_walk hw2.1 hwf1 (fun x hx =>
    (wfl_inits_scope [s] ⟨hwfs, trivial⟩ hx).imp_right fun h => hav1 x (by simp [h.1])) hfin2
  have havR : ∀ x ∈ (Stmt.topInits s ++ S) ++ Block.idents rest, AvoidedIfFresh st x :=
    fun x hx => hav x (by grind [Block.idents, mem_idents_of_topInit])
  obtain ⟨D1, P1, B1, K1⟩ := hr htop st r st1 hwf h1 T Y hfin1 _ hwfr _ htr hnr havR hκ hD
  obtain ⟨D2, P2, B2, K2⟩ := hs _ st1 a st2 hwf1 h2 T Y hfin2 S hwfs Γ hts hns hav1 hκ D1
  have hfT : fEnd = true → (r.hasObl || (fEnd && !r.drop)) = true := fun hf => by
    simp [hf, Bool.eq_false_iff.2 fun hd => absurd (htop (wpList_drop h1 hd)) (by simp [hf])]
  have hctx : TyCtx T Y st2 S Γ → (fEnd = true ∨ r.hasObl = true) →
      TyCtx T Y st1 (Stmt.topInits s ++ S) (Γ.extend (Stmt.typedDefinedVars s)) := fun hT ho =>
    stmtTyCtx Lc κ d s st1 a st2 hwf1
      ((ho.elim hfT fun h => by simp [h] : (r.hasObl || (fEnd && !r.drop)) = true) ▸ h2)
      T Y hfin2 S hwfs hav1 Γ hT
  have hT2 : (TyCtx T Y st' S Γ) → TyCtx T Y st2 S Γ := fun hT x hx ty hty n hn =>
    hT x hx ty hty n (hcur2 x ▸ hn)
  refine ⟨fun n x hn => hty2 ▸ D2 n x (hto2 ▸ hn), fun l e he => ?_, ?_, fun hTY hT => ?_⟩
  · rcases P2 l e (hp2 l ▸ he) with he | he
    · exact P1 l e he
    · exact .inr he
  · rcases hcase with ⟨-, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩
    iterate 2 exact B2
    simp only [WRes.combine, Rope.toList_app, List.any_append, Bool.or_eq_true]
    exact fun h => h.elim (fun h => by simp [B2 h]) fun h => by simp [B1 h]
  have hTY2 : ∀ (n x : P.Ident), st2.tyOf[n]? = some x → T[n]? = none := fun n x hn =>
    hTY n x (hto2 ▸ hn)
  have hTY1 : ∀ (n x : P.Ident), st1.tyOf[n]? = some x → T[n]? = none := fun n x hn =>
    hTY2 n x (hw2.tyOf_keep hwf1 hn)
  replace K1 := K1 hTY1
  replace K2 := K2 hTY2
  have hcar : ∀ {b1 b2 : Bool}, (fEnd = true → b1 = true ∧ b2 = true) →
      CarStep Typ Ground T Y b1 st st1 → CarStep Typ Ground T Y b2 st1 st2 →
      CarStep Typ Ground T Y fEnd st st' := fun hb c1 c2 k q hq =>
    (c2 k q (hc2 k ▸ hq)).elim (fun h => (c1 k q h).imp_right fun h hf => h (hb hf).1)
      fun h => .inr fun hf => h (hb hf).2
  have hcar0 : CarStep Typ Ground T Y false st st' := fun _ _ _ => .inr nofun
  have hf1 := fun hf => (hfT hf : (r.hasObl || (fEnd && !r.drop)) = true)
  rcases hcase with ⟨hd, rfl, rfl⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, rfl⟩
  · have hf : fEnd = false := htop (wpStmt_drop h2 hd).1
    subst hf
    refine ⟨hcar0, ?_, nofun⟩
    by_cases ho : a.hasObl = true
    · exact LOK.imp nofun (K2 fun _ => hT2 (hT (.inr ho))).2.1
    · exact LOK_noBr _ (Bool.eq_false_iff.2 fun h => ho (B2 h))
  · cases hf : fEnd
    · refine ⟨hcar0, ?_, nofun⟩
      by_cases ho : a.hasObl = true
      · exact LOK.imp nofun (K2 fun _ => hT2 (hT (.inr ho))).2.1
      · exact LOK_noBr _ (Bool.eq_false_iff.2 fun h => ho (B2 h))
    · have hT' := hT2 (hT (.inl hf))
      obtain ⟨c2, l2, a2⟩ := K2 fun _ => hT'
      obtain ⟨c1, -, -⟩ := K1 fun _ => hctx hT' (.inl hf)
      exact ⟨hf ▸ hcar (fun _ => ⟨hf, hf1 hf⟩) c1 c2, LOK.imp (fun _ => hf1 hf) l2,
        fun _ => a2 (hf1 hf)⟩
  · have hTs : (r.hasObl || (fEnd && !r.drop)) = true ∨ a.hasObl = true → TyCtx T Y st2 S Γ :=
      fun ho => hT2 (hT (ho.elim (fun h => by
        rcases Bool.or_eq_true _ _ ▸ h with h | h
        · simp [WRes.combine, h]
        · simp_all) fun h => .inr (by simp [WRes.combine, h])))
    obtain ⟨c2, l2, a2⟩ := K2 hTs
    obtain ⟨c1, l1, a1⟩ := K1 fun ho => hctx (hTs (.inl (ho.elim hf1 fun h => by simp [h]))) ho
    refine ⟨hcar (fun hf => ⟨hf, hf1 hf⟩) c1 c2, ?_, fun hf n hn => ?_⟩
    · rw [WRes.combine, Rope.toList_app]
      refine LOK_append _ _ _ (LOK.imp (fun h => ?_) l2) l1
      rcases Bool.or_eq_true _ _ ▸ h with h | h
      · exact hf1 h
      · simp [B1 h]
    · simp only [WRes.combine, unionSet_contains, Bool.or_eq_true] at hn
      exact hn.elim (a2 (hf1 hf) n) (a1 hf n)
end

/-! ## Commands -/

section
variable {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop} {N : P.Ident → Prop}

/-- Inverts a successful run of a straight-line step of the WP walk in the hypothesis `h`. -/
local macro "ty_inv " h:ident : tactic => `(tactic| simp only [Bool.not_true, Bool.not_false,
  Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_get,
  StateT.run_set, StateT.run_pure, Except.bind_is_ok, Except.pure_is_ok, Except.ok.injEq,
  Prod.mk.injEq, exists_eq_left', liveDel, wFresh_run, wFreshBool_run] at $h:ident)

/-- The renamed expression of a loop-free expression `e` typed at `ty`, whose free variables are
    in the scope `S` with annotations agreeing with a typing `Γ` of `S` that agrees with the final
    types at a later state `st'` keeping the current names, is typed at `ty`. -/
theorem wRen_wok (hL : TypingLaws Typ Ground) {e : P.Expr} {we : WExpr P} {rd : List P.Ident}
    {s s0 st' : WSt P} (h : (wRen e).run s = .ok ((we, rd), s0)) {S : List P.Ident}
    {Γ : VarTyping P} (hS : ∀ y ∈ exprFV e, y ∈ S)
    (hcur : ∀ y ∈ S, ∀ n, curName s0 y = some n → curName st' y = some n)
    (hΓ : TyCtx T Y st' S Γ) (hann : Γ.annotates (HasFvars.getTypedFvars e)) {ty : P.Ty}
    (he : Typ e ty) : WOK Typ T Y we ty := by
  obtain ⟨⟨ren, rfl, hr1, hr2, -⟩, -⟩ := wRen_run h
  refine WOK.user hL he (fun p hp hno => ?_) fun p hp q hq hq1 => ?_
  · have hy : p.1 ∈ exprFV e := mem_exprFV.2 (LawfulHasFvars.mem_getFvars_of_typed e _ _ hp)
    obtain ⟨n, hc, -, hn | hm⟩ := hr2 p.1 hy
    · subst hn
      exact hΓ _ (hS _ hy) p.2 (hann _ _ hp) _ (hcur _ (hS _ hy) _ hc)
    · exact absurd rfl (hno _ hm)
  · obtain ⟨hq0, hc, -⟩ := hr1 q hq
    exact hΓ _ (hS _ hq0) p.2 (hq1 ▸ hann _ _ hp) _ (hcur _ (hS _ hq0) _ hc)

omit iLF in
/-- The final type of the WP name `n` that `wName x` returns for a declaration of `x` (from the
    well-formed state `s1`) is its declared type at a later state `st'` recording the
    declaration, with the same avoided names, when `x` is avoided if it has the form of a fresh
    name. -/
theorem decl_final {x n : P.Ident} {s1 s1' st' : WSt P} {ty : P.Ty}
    (hk : (wName x).run s1 = .ok (n, s1')) (hw1 : WFSt s1) (hfin : FinalOK Lc st' T Y)
    (hty : st'.tys[n]? = some ty) (htk : st'.taken.contains x = true)
    (hav : st'.avoid = s1.avoid) (hnext : s1'.next ≤ st'.next) (hxav : AvoidedIfFresh s1 x) :
    T[n]? = some ty := by
  obtain ⟨k, hk', hn, hav'⟩ := freshIn_spec s1.avoid (baseOf x) s1.next
  rcases wName_cases hk with ⟨h1, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
  · obtain ⟨-, b, j, hn, hj, ha⟩ := hw1.nm_fresh x n h1
    exact hfin.drawn hty (hav ▸ ha) ⟨b, j, hn, by omega⟩
  · rcases hfin.1 n ty hty with h | ⟨-, -, h3⟩ | ⟨b, j, h1, -, h3⟩
    · exact h
    · simp [htk] at h3
    · simp [hav, hxav b j h1] at h3
  · simp only [hk'] at hnext hty ⊢
    exact hfin.drawn hty (hav ▸ hav') ⟨_, k, rfl, by omega⟩

omit iL iLF in
/-- A walk step keeping the carried merges adds none. -/
theorem car_of_eq {fol : Bool} {st st' : WSt P} (h : st'.carries = st.carries) :
    CarStep Typ Ground T Y fol st st' := fun _ _ hq => .inl (h ▸ hq)

omit iL iLF in
/-- A walk step keeping the exit snapshots adds none. -/
theorem pend_of_eq {st st' : WSt P} (h : st'.pending = st.pending) : PendStep T Y st st' :=
  fun _ _ he => .inl (h ▸ he)

omit iLF in
/-- The WP name that `wName x` returns for a variable `x` avoided if it has the form of a fresh
    name has no type reference in the well-formed state it runs from. -/
theorem decl_tyOf_none {x n : P.Ident} {s0 s1 : WSt P} (hk : (wName x).run s0 = .ok (n, s1))
    (hw : WFSt s0) (hx : AvoidedIfFresh s0 x) : s0.tyOf[n]? = none := by
  obtain ⟨k, hk', hn, -⟩ := freshIn_spec s0.avoid (baseOf x) s0.next
  refine Option.eq_none_iff_forall_ne_some.2 fun y hy => ?_
  obtain ⟨ha, hnm⟩ := hw.tyOf_keys n y hy
  rcases wName_cases hk with ⟨h1, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩
  · exact hnm x h1
  · obtain ⟨b, j, he, -⟩ := hw.tyOf_fresh n y hy
    simp [hx b j he] at ha
  · rw [hk'] at hy
    exact absurd hy (by rw [hw.tyOf_none hn]; simp)

omit iL in
omit iLF in
/-- The typing property of a walk step that keeps the carried merges, adds Boolean exit snapshots
    and outputs typed straight-line items. -/
theorem plain_close {st st' : WSt P} {a : WRes P} {fol : Bool} {S : List P.Ident}
    {Γ : VarTyping P} (hD : DisjInv st') (hc : CarStep Typ Ground T Y fol st st')
    (hp : PendStep T Y st st') (hb : ∀ it ∈ a.out.toList, it.isBranching = false)
    (hok : (∀ (n x : P.Ident), st'.tyOf[n]? = some x → T[n]? = none) →
      (fol = true ∨ a.hasObl = true → TyCtx T Y st' S Γ) →
      (∀ it ∈ a.out.toList, PlainOK Typ Ground T Y it) ∧ (fol = true → AOK Ground T Y a)) :
    DisjInv st' ∧ PendStep T Y st st' ∧
      (a.out.toList.any WItem.isBranching = true → a.hasObl = true) ∧
      ((∀ (n x : P.Ident), st'.tyOf[n]? = some x → T[n]? = none) →
        (fol = true ∨ a.hasObl = true → TyCtx T Y st' S Γ) →
        CarStep Typ Ground T Y fol st st' ∧ LOK Typ Ground T Y fol a.out.toList ∧
          (fol = true → AOK Ground T Y a)) :=
  ⟨hD, hp, fun h => by
    obtain ⟨it, hm, hi⟩ := List.any_eq_true.1 h
    simp [hb it hm] at hi, fun hTY hT => ⟨hc,
      LOK_plain fun it hm => ⟨hb it hm, (hok hTY hT).1 it hm⟩, (hok hTY hT).2⟩⟩

/-- The walk of a command has the typing property. -/
theorem stmtTypSpec_cmd (hL : TypingLaws Typ Ground) (κ : RE P) (d : Nat) (f : Bool)
    (c : CmdExt P) : StmtTypSpec Typ Ground Lc N κ d f (.cmd c) := by
  intro st a st' hwf h T Y hfin S hwfs Γ hty hng hav hκ hD
  unfold wpStmt at h
  rcases c with ((⟨x, ty, e | _, md⟩ | ⟨x, e | _, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩) |
    ⟨p, args, md⟩)
  all_goals try cases h
  all_goals cases f <;> ty_inv h
  all_goals try (obtain ⟨rfl, rfl⟩ := h
                 exact ⟨hD, fun _ _ h => .inl h, by simp [Rope.toList_nil], fun _ _ =>
                   ⟨fun _ _ h => .inl h, by simp [Rope.toList_nil, LOK], nofun⟩⟩)
  case cmd.init.det.true =>
    obtain ⟨⟨hwt, -⟩, -, hann, -⟩ := hty
    obtain ⟨hxS, -, hrS⟩ := hwfs
    obtain ⟨⟨⟨we, rd⟩, s0⟩, h0, ⟨n, s1⟩, h1, h⟩ := h
    simp only at h1
    obtain ⟨-, -, hc1, -, -⟩ := wDecl_spec h1
    obtain ⟨n', s1', hk⟩ := wName_ok x s0
    obtain ⟨hnn, rfl⟩ := Prod.mk.inj (Except.ok.inj ((wDecl_run hk).symm.trans h1))
    replace hnn : n = n' := hnn.symm
    subst hnn
    obtain ⟨hn1, hs1⟩ := wName_state hk
    obtain ⟨-, hn0', hs0, -⟩ := wRen_run h0
    have hw0 : WFSt s0 := (wRen_walk h0).wf hwf nofun
    have hxav : AvoidedIfFresh s0 x := fun b j e => by
      rw [hs0]
      exact hav x (by simp [Block.idents, Stmt.idents]) b j e
    have hcur : ∀ y ∈ S, ∀ m, curName s0 y = some m →
        curName { s1' with nm := s1'.nm.erase x, taken := s1'.taken.insert x } y = some m :=
      fun y hy m hm => (hc1 y fun he => hxS (he ▸ hy)).trans hm
    have hg : Ground ty := hL.ground hwt
    split at h <;> ty_inv h
    · obtain ⟨⟨u, s3⟩, h3, rfl, rfl⟩ := h
      obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h3
      have hTn : T[n]? = some ty := decl_final hk hw0 hfin (by simp) (by simp)
        (by rw [hs1, hs0]) (Nat.le_refl _) hxav
      have hn0 : st.tyOf[n]? = none := by rw [← decl_tyOf_none hk hw0 hxav, hs0]
      refine plain_close (hD.ins hn0 (by rw [hs1, hs0]) (by rw [hs1, hs0]))
        (car_of_eq (by rw [hs1, hs0])) (pend_of_eq (by rw [hs1, hs0]))
        (by simp [Rope.toList_one, WItem.isBranching])
        fun _ hT => ⟨fun it hm => ?_, fun _ m hm => by simp at hm⟩
      simp only [Rope.toList_one, List.mem_singleton] at hm
      subst hm
      intro ty' hty'
      cases hty'
      refine ⟨fun τ hτ => Except.ok.inj ((tyOfName_T hTn).symm.trans hτ).symm, hg,
        fun w hw => ?_⟩
      cases hw
      exact wRen_wok hL h0 hrS (fun y hy m hm => by simpa [curName] using hcur y hy m hm)
        (hT (.inl rfl)) hann hwt
    · obtain ⟨k, hk', hkn, hkav⟩ := freshIn_spec s1'.avoid (baseOf x) s1'.next
      rw [hk'] at h
      obtain ⟨⟨u, s3⟩, h3, rfl, rfl⟩ := h
      obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h3
      have hTn : T[n]? = some ty := decl_final hk hw0 hfin
        (by rw [Std.HashMap.getElem?_insert]; split <;> simp) (by simp) (by rw [hs1, hs0])
        (by simp; omega) hxav
      have hTd : T[freshName (baseOf x) k]? = some ty := hfin.drawn (by simp)
        (by simpa using hkav) ⟨_, k, rfl, by simp⟩
      have hd : ∀ τ, tyOfName T Y (freshName (baseOf x) k) = .ok τ → τ = ty := fun τ hτ =>
        Except.ok.inj ((tyOfName_T hTd).symm.trans hτ).symm
      have hn0 : st.tyOf[n]? = none := by rw [← decl_tyOf_none hk hw0 hxav, hs0]
      have hk0 : st.next ≤ k := Nat.le_trans hn0' (Nat.le_trans hn1 hkn)
      refine plain_close (DisjInv.ins (s := { st with tys := st.tys.insert n ty })
          (hD.ins hn0 rfl rfl) (hwf.tyOf_none hk0) (by rw [hs1, hs0]) (by rw [hs1, hs0]))
        (car_of_eq (by rw [hs1, hs0])) (pend_of_eq (by rw [hs1, hs0]))
        (by simp [Rope.toList_one, Rope.toList_app, WItem.isBranching])
        fun _ hT => ⟨fun it hm => ?_, fun _ m hm => by simp at hm⟩
      simp only [Rope.toList_app, Rope.toList_one, List.singleton_append, List.mem_cons,
        List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      all_goals intro ty' hty'
      all_goals cases hty'
      · exact ⟨hd, hg, nofun⟩
      refine ⟨fun τ hτ => Except.ok.inj ((tyOfName_T hTn).symm.trans hτ).symm, hg,
        fun w hw => ?_⟩
      cases hw
      refine WOK.kIte hL hκ (wRen_wok hL h0 hrS (fun y hy m hm => ?_) (hT (.inl rfl)) hann hwt)
        (WOK.var hL hg hd)
      simpa [curName] using hcur y hy m hm
  case cmd.init.nondet.true =>
    obtain ⟨⟨n, s1⟩, h1, rfl, rfl⟩ := h
    have hg : Ground ty := hng.1.2 (hng.1.1 trivial)
    obtain ⟨n', s1', hk⟩ := wName_ok x st
    obtain ⟨hnn, rfl⟩ := Prod.mk.inj (Except.ok.inj ((wDecl_run hk).symm.trans h1))
    replace hnn : n = n' := hnn.symm
    subst hnn
    obtain ⟨-, hs1⟩ := wName_state hk
    have hxav : AvoidedIfFresh st x := hav x (by simp [Block.idents, Stmt.idents])
    have hTn : T[n]? = some ty := decl_final hk hwf hfin (by simp) (by simp) (by rw [hs1])
      (Nat.le_refl _) hxav
    refine plain_close (hD.ins (decl_tyOf_none hk hwf hxav) (by rw [hs1]) (by rw [hs1]))
      (car_of_eq (by rw [hs1])) (pend_of_eq (by rw [hs1]))
      (by simp [Rope.toList_one, WItem.isBranching])
      fun _ _ => ⟨fun it hm => ?_, fun _ m hm => by simp at hm⟩
    simp only [Rope.toList_one, List.mem_singleton] at hm
    subst hm
    intro ty' hty'
    cases hty'
    exact ⟨fun τ hτ => Except.ok.inj ((tyOfName_T hTn).symm.trans hτ).symm, hg, nofun⟩
  case cmd.set.det.true =>
    obtain ⟨⟨τ, hΓx, hwt⟩, -⟩ := hty.1
    obtain ⟨-, -, hann, -⟩ := hty
    obtain ⟨hxS, hrS⟩ := hwfs
    obtain ⟨⟨⟨we, rd⟩, s0⟩, h0, ⟨n, s1⟩, h1, h⟩ := h
    simp only at h1
    obtain ⟨-, hs1⟩ := wName_state h1
    have hc1 := wName_curName h1
    have hk1 := wName_curName_keep h1
    obtain ⟨-, -, hs0, -⟩ := wRen_run h0
    have hg : Ground τ := hL.ground hwt
    have hwok : ∀ {s' : WSt P}, s'.nm = s1.nm → s'.taken = s1.taken → TyCtx T Y s' S Γ →
        tyOfName T Y n = .ok τ ∧ WOK Typ T Y we τ := fun hn ht hT =>
      ⟨hT x hxS τ hΓx n (curName_eq_of_nm_taken hn ht x ▸ hc1),
        wRen_wok hL h0 hrS (fun y _ m hm => curName_eq_of_nm_taken hn ht y ▸ hk1 y m hm) hT hann
          hwt⟩
    have hA : ∀ m, (Std.HashSet.ofList [n]).contains m = true → m = n := fun m hm => by
      simp only [Std.HashSet.contains_ofList, List.contains_cons, List.contains_nil, Bool.or_false,
        beq_iff_eq] at hm
      exact hm
    split at h <;> ty_inv h
    · obtain ⟨⟨u, s3⟩, h3, rfl, rfl⟩ := h
      obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h3
      refine plain_close (hD.of_eq (by rw [hs1, hs0]) (by rw [hs1, hs0]))
        (car_of_eq (by rw [hs1, hs0])) (pend_of_eq (by rw [hs1, hs0]))
        (by simp [Rope.toList_one, WItem.isBranching]) fun _ hT => ?_
      obtain ⟨hn, hw⟩ := hwok rfl rfl (hT (.inl rfl))
      refine ⟨fun it hm => ?_, fun _ m hm => hA m hm ▸ ⟨τ, hn, hg⟩⟩
      simp only [Rope.toList_one, List.mem_singleton] at hm
      subst hm
      exact ⟨τ, hn, hg, fun w hw' => by cases hw'; exact hw⟩
    · obtain ⟨⟨u, s3⟩, h3, ⟨u', s4⟩, h4, rfl, rfl⟩ := h
      obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h3
      obtain ⟨live', clock', rfl, -⟩ := liveAdd_step h4
      refine plain_close (hD.of_eq (by rw [hs1, hs0]) (by rw [hs1, hs0]))
        (car_of_eq (by rw [hs1, hs0])) (pend_of_eq (by rw [hs1, hs0]))
        (by simp [Rope.toList_one, WItem.isBranching]) fun _ hT => ?_
      obtain ⟨hn, hw⟩ := hwok rfl rfl (hT (.inl rfl))
      refine ⟨fun it hm => ?_, fun _ m hm => hA m hm ▸ ⟨τ, hn, hg⟩⟩
      simp only [Rope.toList_one, List.mem_singleton] at hm
      subst hm
      exact ⟨τ, hn, hg, fun w hw' => by
        cases hw'
        exact WOK.kIte hL hκ hw (WOK.var hL hg fun τ' h => Except.ok.inj (h.symm.trans hn))⟩
  case cmd.set.nondet.true =>
    obtain ⟨τ, hΓx, hg⟩ := hng.1.2 (hng.1.1 trivial)
    obtain ⟨⟨n, s1⟩, h1, ⟨c, s2⟩, h2, h⟩ := h
    simp only at h2
    obtain ⟨-, hs1⟩ := wName_state h1
    have hc1 := wName_curName h1
    obtain ⟨k, hk', hkn, hkav⟩ := freshIn_spec s1.avoid (baseOf n) s1.next
    obtain ⟨hn1, -⟩ := wName_state h1
    have hD2 : ∀ {s' : WSt P}, s'.tys = s1.tys →
        s'.tyOf = s1.tyOf.insert (freshName (baseOf n) k) n → DisjInv s' := fun ht ho =>
      DisjInv.copy (s := st) hD hwf (Nat.le_trans hn1 hkn) (by rw [hs1] at hkav; exact hkav)
        (by rw [ht, hs1]) (by rw [ho, hs1])
    rw [wFreshLike_run, hk'] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h2)
    have hcl : ∀ {s' : WSt P}, FinalOK Lc s' T Y →
        (∀ (m x : P.Ident), s'.tyOf[m]? = some x → T[m]? = none) → s'.nm = s1.nm →
        s'.taken = s1.taken → s'.tyOf[freshName (P := P) (baseOf n) k]? = some n →
        TyCtx T Y s' S Γ →
        tyOfName T Y n = .ok τ ∧
          ∀ τ', tyOfName T Y (freshName (baseOf n) k) = .ok τ' → τ' = τ :=
      fun hf hY hn ht hc hT =>
        have hn' := hT x hwfs τ hΓx n (curName_eq_of_nm_taken hn ht x ▸ hc1)
        ⟨hn', fun τ' h => Except.ok.inj ((tyOfName_copy (hY _ _ hc) (hf.2.1 _ _ hc) h).symm.trans
          hn')⟩
    have hA : ∀ m, (Std.HashSet.ofList [n]).contains m = true → m = n := fun m hm => by
      simp only [Std.HashSet.contains_ofList, List.contains_cons, List.contains_nil, Bool.or_false,
        beq_iff_eq] at hm
      exact hm
    split at h <;> ty_inv h
    · obtain ⟨rfl, rfl⟩ := h
      refine plain_close (hD2 rfl rfl) (car_of_eq (by rw [hs1])) (pend_of_eq (by rw [hs1]))
        (by simp [Rope.toList_one, Rope.toList_app, WItem.isBranching]) fun hTY hT => ?_
      obtain ⟨hn, hc⟩ := hcl hfin hTY rfl rfl (by simp) (hT (.inl rfl))
      refine ⟨fun it hm => ?_, fun _ m hm => hA m hm ▸ ⟨τ, hn, hg⟩⟩
      simp only [Rope.toList_app, Rope.toList_one, List.singleton_append, List.mem_cons,
        List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · intro ty' hty'
        obtain rfl := Except.ok.inj ((hty' : tyOfName T Y n = .ok ty').symm.trans hn)
        exact ⟨hc, hg, nofun⟩
      · exact ⟨τ, hn, hg, fun w hw => by cases hw; exact WOK.var hL hg hc⟩
    · obtain ⟨⟨u, s3⟩, h3, rfl, rfl⟩ := h
      obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h3
      refine plain_close (hD2 rfl rfl) (car_of_eq (by rw [hs1])) (pend_of_eq (by rw [hs1]))
        (by simp [Rope.toList_one, Rope.toList_app, WItem.isBranching]) fun hTY hT => ?_
      obtain ⟨hn, hc⟩ := hcl hfin hTY rfl rfl (by simp) (hT (.inl rfl))
      refine ⟨fun it hm => ?_, fun _ m hm => hA m hm ▸ ⟨τ, hn, hg⟩⟩
      simp only [Rope.toList_app, Rope.toList_one, List.singleton_append, List.mem_cons,
        List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · intro ty' hty'
        obtain rfl := Except.ok.inj ((hty' : tyOfName T Y n = .ok ty').symm.trans hn)
        exact ⟨hc, hg, nofun⟩
      · exact ⟨τ, hn, hg, fun w hw => by
          cases hw
          exact WOK.kIte hL hκ (WOK.var hL hg hc)
            (WOK.var hL hg fun τ' h => Except.ok.inj (h.symm.trans hn))⟩
  case cmd.assume.true =>
    obtain ⟨-, ⟨hwt, -⟩, hann, -⟩ := hty
    obtain ⟨⟨⟨wa, rd⟩, s0⟩, h0, ⟨u, s1⟩, h1, rfl, rfl⟩ := h
    obtain ⟨-, -, hs0, -⟩ := wRen_run h0
    obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h1
    refine plain_close (hD.of_eq (by rw [hs0]) (by rw [hs0])) (car_of_eq (by rw [hs0]))
      (pend_of_eq (by rw [hs0])) (by simp [Rope.toList_one, WItem.isBranching])
      fun _ hT => ⟨fun it hm => ?_, fun _ m hm => by simp at hm⟩
    simp only [Rope.toList_one, List.mem_singleton] at hm
    subst hm
    exact WOK.kIte hL hκ (wRen_wok hL h0 hwfs (fun _ _ _ h => h) (hT (.inl rfl)) hann hwt)
      (WOK.lit hL true)
  all_goals
    obtain ⟨-, ⟨hwt, -⟩, hann, -⟩ := hty
    obtain ⟨⟨⟨we, rd⟩, s0⟩, h0, ⟨u, s1⟩, h1, rfl, rfl⟩ := h
    obtain ⟨-, -, hs0, -⟩ := wRen_run h0
    obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h1
    refine ⟨hD.of_eq (by rw [hs0]) (by rw [hs0]), fun _ _ h => .inl (by rw [hs0] at h; exact h),
      fun _ => rfl, fun _ hT =>
      ⟨fun _ _ h => .inl (by rw [hs0] at h; exact h), ?_, fun _ m hm => by simp at hm⟩⟩
    simp only [Rope.toList_one, LOK]
    refine ⟨fun κ' hκ' => ?_, fun c hc => ?_, trivial⟩
    · cases κ <;> cases hκ' <;> exact hκ
    · simp only [List.mem_singleton] at hc
      subst hc
      exact wRen_wok hL h0 hwfs (fun _ _ _ h => h) (hT (.inr rfl)) hann hwt

omit iL in
omit iLB iHI in
/-- The items of `setReach κ X` for a Boolean reach context and a Boolean `X` are typed
    straight-line items. -/
theorem setReach_plain (hL : TypingLaws Typ Ground) {κ : RE P} {X : WExpr P} (hκ : REOK T Y κ)
    (hX : WOK Typ T Y X HasBool.boolTy) :
    ∀ it ∈ (setReach κ X).toList, it.isBranching = false ∧ PlainOK Typ Ground T Y it := by
  have hg : Ground HasBool.boolTy := hL.ground hL.tt
  cases κ <;> simp only [setReach, Rope.toList_nil, Rope.toList_one, List.mem_singleton,
    List.not_mem_nil, forall_eq] <;>
    first
      | exact ⟨rfl, _, hκ _ (.head _), hg, fun w hw => by cases hw; exact hX⟩
      | exact ⟨rfl, _, hκ _ (.head _), hg, fun w hw => by cases hw; exact WOK.not hL hX⟩
      | exact ⟨rfl, _, hκ _ (.tail _ (.head _)), hg, fun w hw => by cases hw; exact WOK.not hL hX⟩
      | exact nofun


omit iL in
omit iLF in
/-- The walk of a statement that is not a command, an `exit`, a block or a deterministic `ite`
    has the typing property. -/
theorem stmtTypSpec_other (κ : RE P) (d : Nat) (f : Bool) (s : PStmt P)
    (hs : (∀ c, s ≠ .cmd c) ∧ (∀ l md, s ≠ .exit l md) ∧ (∀ l b md, s ≠ .block l b md) ∧
      ∀ c t e md, s ≠ .ite (.det c) t e md) : StmtTypSpec Typ Ground Lc N κ d f s := by
  intro st a st' _ h _ _ _ _ _ _ _ _ _ _ hD
  obtain ⟨h1, h2, h3, h4⟩ := hs
  unfold wpStmt at h
  rcases s with _ | _ | ⟨_ | c, t, e, md⟩ | _ | _ | _ <;>
    first | exact absurd rfl (h4 _ _ _ _) | cases h | simp at h1 h2 h3
  exact plain_close hD (car_of_eq rfl) (pend_of_eq rfl) (by simp [Rope.toList_nil]) fun _ _ =>
    ⟨by simp [Rope.toList_nil], fun _ m hm => by simp at hm⟩

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW iLF in
/-- The items of a fold of `set` items are those of its start and the `set`s of the elements. -/
theorem mem_foldl_set {α : Type} (g : α → P.Ident) (v : α → Option (WExpr P)) :
    ∀ (L : List α) (s : Rope (WItem P)) (it : WItem P),
      it ∈ (L.foldl (fun acc x => acc.app (.one (.set (g x) (v x)))) s).toList →
        it ∈ s.toList ∨ ∃ x ∈ L, it = .set (g x) (v x)
  | [], _, _, h => .inl h
  | x :: L, s, it, h => by
    rcases mem_foldl_set g v L _ it h with h | ⟨y, hy, rfl⟩
    · simp only [Rope.toList_app, Rope.toList_one, List.mem_append, List.mem_singleton] at h
      exact h.elim .inl fun h => .inr ⟨x, .head _, h⟩
    · exact .inr ⟨y, .tail _ hy, rfl⟩



omit iL iLF in
/-- The exit snapshots after a block: those of its body for the other labels, those before the
    block for its label. -/
theorem block_pend {l : String} {st s0 s1 st' : WSt P} (hP : PendStep T Y s0 s1)
    (h0 : ∀ l', s0.pending.getD l' [] = if l = l' then [] else st.pending.getD l' [])
    (h1 : st'.pending = match st.pending[l]? with
      | some v => s1.pending.insert l v
      | none => s1.pending.erase l) : PendStep T Y st st' := by
  intro l' e he
  rw [h1] at he
  by_cases hl : l = l'
  · subst hl
    split at he <;> rename_i heq
    · simp only [Std.HashMap.getD_insert, beq_self_eq_true, ↓reduceIte] at he
      exact .inl (by simp [Std.HashMap.getD_eq_getD_getElem?, heq, he])
    · simp at he
  · have he' : e ∈ s1.pending.getD l' [] := by
      split at he <;> simpa [Std.HashMap.getD_insert, Std.HashMap.getD_erase, hl] using he
    exact (hP l' e he').imp_left fun h => by simpa [h0 l', hl] using h

omit iL iLF in
/-- The carried merges after a block: those of its body except at the block's depth. -/
theorem block_car {fol : Bool} {k0 : Nat} {st s0 s1 st' : WSt P}
    (hC : CarStep Typ Ground T Y fol s0 s1)
    (h0 : ∀ k, k ≠ k0 → s0.carries.getD k [] = st.carries.getD k [])
    (h1 : st'.carries = s1.carries.erase k0) : CarStep Typ Ground T Y fol st st' := by
  intro k q hq
  rw [h1, Std.HashMap.getD_erase] at hq
  split at hq
  · simp at hq
  · rename_i hk
    exact (hC k q hq).imp_left fun h => h0 k (fun he => hk (by simp [he])) ▸ h


omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW iLF in
/-- The items of `setReach κ X` are straight-line items. -/
theorem setReach_noBr {κ : RE P} {X : WExpr P} :
    ∀ it ∈ (setReach κ X).toList, it.isBranching = false := by
  cases κ <;> simp [setReach, Rope.toList_nil, Rope.toList_one, WItem.isBranching]

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW iLF in
/-- The elements of an optional rope `x` followed by `t`. -/
theorem ite_nil_or {α : Type} (c : Bool) (x : α) (t : Rope α) :
    (if c = true then Rope.nil else (Rope.one x).app t).toList = [] ∨
      (if c = true then Rope.nil else (Rope.one x).app t).toList = [x] ++ t.toList := by
  cases c <;> simp [Rope.toList_app, Rope.toList_one, Rope.toList_nil]

omit iL in
omit iLF in
/-- The typing property of a block walk, from that of its body walk (from `s0` to `s1`, result
    `B`): the output is the body's output, the carried merges `C` of the block (at its depth
    `k0`, added by the body) and the join items `J`, optionally preceded by typed items `pre`. -/
theorem block_close {fol : Bool} {k0 : Nat} {l : String} {st s0 s1 st' : WSt P} {a B : WRes P}
    {S : List P.Ident} {Γ : VarTyping P} {J : Rope (WItem P)} {pre : List (WItem P)}
    {C : List (P.Ident × WExpr P × P.Ident)}
    (hD' : DisjInv st') (hto' : st'.tyOf = s1.tyOf)
    (PB : PendStep T Y s0 s1) (BB : B.out.toList.any WItem.isBranching = true → B.hasObl = true)
    (KB : (∀ (n x : P.Ident), s1.tyOf[n]? = some x → T[n]? = none) →
      (fol = true ∨ B.hasObl = true → TyCtx T Y s1 S Γ) →
      CarStep Typ Ground T Y fol s0 s1 ∧ LOK Typ Ground T Y fol B.out.toList ∧
        (fol = true → AOK Ground T Y B))
    (hp0 : ∀ l', s0.pending.getD l' [] = if l = l' then [] else st.pending.getD l' [])
    (hc0 : ∀ k, k ≠ k0 → s0.carries.getD k [] = st.carries.getD k [])
    (hc0' : s0.carries.getD k0 [] = [])
    (hp' : st'.pending = match st.pending[l]? with
      | some v => s1.pending.insert l v
      | none => s1.pending.erase l)
    (hc' : st'.carries = s1.carries.erase k0) (hcur : ∀ z, curName st' z = curName s1 z)
    (hC : ∀ q ∈ C, q ∈ s1.carries.getD k0 [])
    (hJ1 : ∀ it ∈ J.toList, it.isBranching = false)
    (hJ2 : (∀ e ∈ s1.pending.getD l [], tyOfName T Y e = .ok HasBool.boolTy) →
      fol = true → ∀ it ∈ J.toList, PlainOK Typ Ground T Y it)
    (hpre : ∀ it ∈ pre, it.isBranching = false ∧ PlainOK Typ Ground T Y it)
    (hout : a.out.toList = pre ++ (B.out.toList ++
        ((C.foldl (fun (acc : Rope (WItem P)) x => acc.app (.one (.set x.1 (some x.2.1))))
          .nil).toList ++ J.toList)) ∨ a.out.toList = [])
    (hO : a.hasObl = B.hasObl) (hA : a.A = C.foldl (fun s x => s.insert x.1) B.A) :
    DisjInv st' ∧ PendStep T Y st st' ∧
      (a.out.toList.any WItem.isBranching = true → a.hasObl = true) ∧
      ((∀ (n x : P.Ident), st'.tyOf[n]? = some x → T[n]? = none) →
        (fol = true ∨ a.hasObl = true → TyCtx T Y st' S Γ) →
        CarStep Typ Ground T Y fol st st' ∧ LOK Typ Ground T Y fol a.out.toList ∧
          (fol = true → AOK Ground T Y a)) := by
  have hMg : ∀ it ∈ (C.foldl (fun (acc : Rope (WItem P)) x =>
      acc.app (.one (.set x.1 (some x.2.1)))) .nil).toList, ∃ q ∈ C, it = .set q.1 (some q.2.1) :=
    fun it hm =>
    (mem_foldl_set (fun q => q.1) (fun q => some q.2.1) C .nil it hm).resolve_left
      (by simp [Rope.toList_nil])
  have hnb : ∀ it ∈ (C.foldl (fun (acc : Rope (WItem P)) x =>
      acc.app (.one (.set x.1 (some x.2.1)))) .nil).toList ++ J.toList, it.isBranching = false :=
    fun it hm => (List.mem_append.1 hm).elim
    (fun h => (hMg it h).elim fun _ ⟨_, he⟩ => he ▸ rfl) (hJ1 it)
  have hnb' : ((C.foldl (fun (acc : Rope (WItem P)) x =>
      acc.app (.one (.set x.1 (some x.2.1)))) .nil).toList ++ J.toList).any WItem.isBranching =
      false :=
    Bool.eq_false_iff.2 fun h => by
      obtain ⟨it, hm, hi⟩ := List.any_eq_true.1 h
      simp [hnb it hm] at hi
  have hnp : pre.any WItem.isBranching = false := Bool.eq_false_iff.2 fun h => by
    obtain ⟨it, hm, hi⟩ := List.any_eq_true.1 h
    simp [(hpre it hm).1] at hi
  refine ⟨hD', block_pend PB hp0 hp', fun h => ?_, fun hTY hT => ?_⟩
  · rcases hout with hout | hout <;> rw [hout] at h
    · simp only [List.any_append, hnp, hnb', Bool.false_or, Bool.or_false] at h
      exact hO ▸ BB h
    · simp at h
  obtain ⟨cB, lB, aB⟩ := KB (fun n x h => hTY n x (hto' ▸ h)) fun ho => fun x hx ty hty n hn =>
    hT (ho.imp_right (hO ▸ ·)) x hx ty hty n ((hcur x).trans hn)
  have hCok : fol = true → ∀ q ∈ C, PlainOK Typ Ground T Y (.set q.1 (some q.2.1)) :=
    fun hf q hq => ((cB k0 q (hC q hq)).resolve_left (by simp [hc0'])) hf
  refine ⟨block_car cB hc0 hc', ?_, fun hf n hn => ?_⟩
  · rcases hout with hout | hout <;> rw [hout]
    · refine LOK_append _ _ _ (LOK_plain hpre) (LOK_append _ _ _ (LOK.imp ?_ lB) ?_)
      · simp [hnb']
      · cases hfol : fol
        · exact LOK_noBr _ hnb'
        · refine LOK_plain fun it hm => ⟨hnb it hm, ?_⟩
          rcases List.mem_append.1 hm with hm | hm
          · obtain ⟨q, hq, rfl⟩ := hMg it hm
            exact hCok hfol q hq
          · refine hJ2 (fun e he => ?_) hfol it hm
            exact (PB l e he).resolve_left (by simp [hp0 l])
    · simp [LOK]
  · rw [hA] at hn
    rcases foldl_insert_fst (fun _ _ => rfl) hn with hn | ⟨q, hq, rfl⟩
    · exact aB hf n hn
    · obtain ⟨τ, h1, h2, -⟩ := hCok hf q hq
      exact ⟨τ, h1, h2⟩

omit iDE iBE iLB iHS iHI iL iHa iW iLF in
/-- The expressions of a block's body are typed when those of the block are. -/
theorem Block.ExprsTyped.block' {Typ : P.Expr → P.Ty → Prop} {Γ : VarTyping P} {l : String}
    {body : PStmts P} {md : MetaData P} (h : Block.ExprsTyped Typ Γ [.block l body md]) :
    Block.ExprsTyped Typ Γ body := ⟨h.1.1, h.2.1.1, h.2.2.1⟩

/-- The walk of a block has the typing property when the walks of its body (at the next depth,
    under every context) have it. -/
theorem stmtTypSpec_block (hL : TypingLaws Typ Ground) {κ : RE P} {d : Nat} {f : Bool}
    {l : String} {body : PStmts P} (md : MetaData P)
    (hB : ∀ κB, ListTypSpec Typ Ground Lc N κB (d + 1) f body) :
    StmtTypSpec Typ Ground Lc N κ d f (.block l body md) := by
  intro st a st' hwf h T Y hfin S hwfs Γ hty hng hav hκ hD
  have hg : Ground HasBool.boolTy := hL.ground hL.tt
  have htyB := Block.ExprsTyped.block' hty
  have hngB : Block.nondetGround Ground N Γ body := hng.1
  have hwf0 := wfSt_blk hwf l d st.clock
  unfold wpStmt at h
  ty_inv h
  split at h
  all_goals ty_inv h
  all_goals obtain ⟨⟨B, s1⟩, h1, ⟨u, s2⟩, h2, rfl, rfl⟩ := h
  all_goals obtain ⟨live, clock, hst', -⟩ := liveAdd_step h2
  all_goals simp only at hst' h1
  all_goals subst hst'
  all_goals
    have hfin1 : FinalOK Lc s1 T Y :=
      FinalOK.back_le rfl rfl rfl (fun _ h => h) (Nat.le_refl _) hfin
    have hT1 : TyCtx T Y _ S Γ → TyCtx T Y s1 S Γ := fun h => h
    have hdB : ∀ x ∈ stmtsInits body, AvoidedIfFresh st x := fun x hx =>
      hav x (by simp [Block.idents, Stmt.idents, (wfl_inits_scope body hwfs hx).2.1])
    have havB : ∀ x ∈ S ++ Block.idents body, AvoidedIfFresh st x := fun x hx =>
      hav x ((List.mem_append.1 hx).elim (List.mem_append_left _) fun h =>
        List.mem_append_right _ (by simp [Block.idents, Stmt.idents, h]))
  case' h_1 =>
    obtain ⟨k, hk', hkn, hkav⟩ := freshIn_spec st.avoid "r" st.next
    rw [hk'] at h1 ⊢
    dsimp only at h1
    have hw0 := (wFreshBool_walk (b := "r") (st := { st with
      labelDepth := st.labelDepth.insert l (d + 1), pending := st.pending.insert l [],
      stampAt := st.stampAt.insert (d + 1) st.clock, carries := st.carries.insert (d + 1) [] })
      (by rw [wFreshBool_run, hk'])).wf hwf0 nofun
    have hrL : s1.tys[freshName (P := P) "r" k]? = some HasBool.boolTy :=
      (wpList_walkOK h1).1.tys_keep hw0 hdB (by simp) (by simpa using hkav) ⟨_, k, rfl, by simp⟩
    have hTr : tyOfName T Y (freshName (P := P) "r" k) = .ok HasBool.boolTy :=
      tyOfName_T (hfin1.drawn hrL (by rw [(wpList_walkOK h1).1.avoid]; simpa using hkav)
        ⟨_, k, rfl, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (wpList_walkOK h1).1.next⟩)
    obtain ⟨DB, PB, BB, KB⟩ := hB (.name (freshName "r" k)) nofun _ B s1 hw0 h1 T Y hfin1 S hwfs
      Γ htyB hngB havB
      (fun y hy => by simp only [RE.vars, List.mem_singleton] at hy; exact hy ▸ hTr)
      (DisjInv.draw (s := st) hD hwf hkn rfl rfl)
  case' h_2 =>
    obtain ⟨DB, PB, BB, KB⟩ := hB _ (fun h => absurd h ‹_›) _ B s1 hwf0 h1 T Y hfin1 S hwfs Γ htyB
      hngB havB hκ hD
  all_goals
    have hm : ∀ e, e ∈ ((s1.pending.getD l []).filter fun e => !s1.dead.contains e).reverse →
        e ∈ s1.pending.getD l [] := fun e he => (List.mem_filter.1 (List.mem_reverse.1 he)).1
  case h_1 =>
    refine block_close (st := st) (s1 := s1) (l := l) (k0 := d + 1)
      (C := (s1.carries.getD (d + 1) []).filter fun x => !s1.dead.contains x.2.2)
      (J := if !f then .nil else if leOpt B.minT d then .one (.assume joinLabel (disjW
        (.var (freshName "r" k) :: (((s1.pending.getD l []).filter fun e =>
          !s1.dead.contains e).reverse.map .var))) .empty) else .nil)
      (pre := [.init (freshName "r" k) (.known HasBool.boolTy) (some (.lit true))])
      (DB.of_eq rfl rfl) rfl PB BB KB
      (fun l' => by by_cases h : l = l' <;> simp [Std.HashMap.getD_insert, h])
      (fun k' hk => by simp [Std.HashMap.getD_insert, Ne.symm hk]) (by simp) ?_ ?_ ?_
      (fun q hq => (List.mem_filter.1 hq).1) (fun it hit => ?_) (fun hP hf it hit => ?_)
      (fun it hit => ?_) ?_ ?_ ?_
    all_goals first | rfl | (intro; rfl) | skip
    · split at hit
      · simp [Rope.toList_nil] at hit
      · split at hit <;> simp_all [Rope.toList_nil, Rope.toList_one, WItem.isBranching]
    · rw [hf] at hit
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hit
      split at hit
      · simp only [Rope.toList_one, List.mem_singleton] at hit
        subst hit
        refine WOK.disjW hL _ fun w hw => ?_
        rcases List.mem_cons.1 hw with rfl | hw
        · exact WOK.bvar hL hTr
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
          exact WOK.bvar hL (hP e (hm e he))
      · simp [Rope.toList_nil] at hit
    · simp only [List.mem_singleton] at hit
      subst hit
      exact ⟨rfl, fun ty hty => by
        cases hty
        exact ⟨fun τ hτ => Except.ok.inj (hτ.symm.trans hTr), hg, fun w hw => by
          cases hw; exact WOK.lit hL true⟩⟩
    · exact (ite_nil_or _ _ _).elim .inr fun h => .inl (h.trans (by simp [Rope.toList_app]))
  case h_2 =>
    refine block_close (st := st) (s1 := s1) (l := l) (k0 := d + 1)
      (C := (s1.carries.getD (d + 1) []).filter fun x => !s1.dead.contains x.2.2)
      (J := if !f then .nil else if ((s1.pending.getD l []).filter fun e =>
          !s1.dead.contains e).reverse.isEmpty then .nil
        else setReach κ (disjW (kExpr κ :: (((s1.pending.getD l []).filter fun e =>
          !s1.dead.contains e).reverse.map .var))))
      (pre := []) (DB.of_eq rfl rfl) rfl PB BB KB
      (fun l' => by by_cases h : l = l' <;> simp [Std.HashMap.getD_insert, h])
      (fun k' hk => by simp [Std.HashMap.getD_insert, Ne.symm hk]) (by simp) ?_ ?_ ?_
      (fun q hq => (List.mem_filter.1 hq).1) (fun it hit => ?_) (fun hP hf it hit => ?_) nofun
      (.inl ?_) ?_ ?_
    all_goals first | rfl | (intro; rfl) | skip
    · split at hit
      · simp [Rope.toList_nil] at hit
      · split at hit
        · simp [Rope.toList_nil] at hit
        · exact setReach_noBr it hit
    · rw [hf] at hit
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hit
      split at hit
      · simp [Rope.toList_nil] at hit
      · refine (setReach_plain hL hκ (WOK.disjW hL _ fun w hw => ?_) it hit).2
        rcases List.mem_cons.1 hw with rfl | hw
        · exact WOK.kExpr hL hκ
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
          exact WOK.bvar hL (hP e (hm e he))
    · simp [Rope.toList_app]


omit iDE iBE iLB iHS iHI iL iHa iW iLF in
/-- The expressions of a deterministic `ite` are typed: its condition is Boolean, its annotations
    agree with `Γ`, and the expressions of its arms are typed. -/
theorem Block.ExprsTyped.ite' {Typ : P.Expr → P.Ty → Prop} {Γ : VarTyping P} {c : P.Expr}
    {tss ess : PStmts P} {md : MetaData P} (h : Block.ExprsTyped Typ Γ [.ite (.det c) tss ess md]) :
    Typ c HasBool.boolTy ∧ Γ.annotates (HasFvars.getTypedFvars c) ∧ Block.ExprsTyped Typ Γ tss ∧
      Block.ExprsTyped Typ Γ ess :=
  ⟨h.1.1.1, h.2.2.1.1, ⟨h.1.1.2.1, h.2.1.1.1, h.2.2.1.2.1⟩, h.1.1.2.2, h.2.1.1.2, h.2.2.1.2.2⟩

omit iL iW iLF in
/-- A well-formed state with an empty live set and no exit snapshots, and other label depths, is
    well formed. -/
theorem WFSt.reset {st : WSt P} (hw : WFSt st) (ld : Std.HashMap String Nat) :
    WFSt { st with live := {}, labelDepth := ld, pending := {} } :=
  { hw with
    pending_fresh := fun _ _ h => by simp at h
    live_stamp := fun _ _ h => by simp at h }

omit iL iW iLF in
/-- A well-formed state with an empty live set is well formed. -/
theorem WFSt.resetLive {st : WSt P} (hw : WFSt st) : WFSt { st with live := {} } :=
  { hw with live_stamp := fun _ _ h => by simp at h }

/-- The walk of a real branch has the typing property when the walks of its arms (under `top`,
    no obligation following them) have it. -/
theorem stmtTypSpec_iteReal (hL : TypingLaws Typ Ground) {κ : RE P} {d : Nat} {c : P.Expr}
    {tss ess : PStmts P} (md : MetaData P)
    (hT : ListTypSpec Typ Ground Lc N .top d false tss)
    (hE : ListTypSpec Typ Ground Lc N .top d false ess) :
    TypSpec Typ Ground Lc N κ (wpIteReal κ d c tss ess) [.ite (.det c) tss ess md]
      (fun S => Stmt.WellScoped Lc S (.ite (.det c) tss ess md)) false := by
  intro st a st' hwf h T Y hfin S hwfs Γ hty hng hav hκ hD
  obtain ⟨hwc, hann, htyT, htyE⟩ := Block.ExprsTyped.ite' hty
  obtain ⟨hngT, hngE⟩ : Block.nondetGround Ground N Γ tss ∧ Block.nondetGround Ground N Γ ess :=
    hng.1
  obtain ⟨hrS, hwfT, hwfE⟩ := hwfs
  have hg : Ground HasBool.boolTy := hL.ground hL.tt
  unfold wpIteReal at h
  ty_inv h
  obtain ⟨⟨E, s2⟩, h2, ⟨T', s4⟩, h4, h⟩ := h
  simp only at h4 h
  have hw1 := hwf.reset {}
  have hW2 := wpList_walkOK h2
  have hdE : ∀ x ∈ stmtsInits ess, AvoidedIfFresh st x := fun x hx =>
    hav x (by simp [Block.idents, Stmt.idents, (wfl_inits_scope ess hwfE hx).2.1])
  have hdT : ∀ x ∈ stmtsInits tss, AvoidedIfFresh st x := fun x hx =>
    hav x (by simp [Block.idents, Stmt.idents, (wfl_inits_scope tss hwfT hx).2.1])
  have hw2 : WFSt s2 := hW2.wf hw1 hdE
  have hw3 := hw2.resetLive
  have hW4 := wpList_walkOK h4
  have ha2 : s2.avoid = st.avoid := hW2.avoid
  have hw4 : WFSt s4 := hW4.wf hw3 fun x hx b j e => by simpa [ha2] using hdT x hx b j e
  have havT : ∀ x ∈ S ++ Block.idents tss, AvoidedIfFresh { s2 with live := {} } x :=
    fun x hx b j e => by
      simpa [ha2] using hav x (by grind [Block.idents, Stmt.idents]) b j e
  have havE : ∀ x ∈ S ++ Block.idents ess,
      AvoidedIfFresh ({ st with live := {}, labelDepth := {}, pending := {} } : WSt P) x :=
    fun x hx b j e => hav x (by grind [Block.idents, Stmt.idents]) b j e
  have harms : FinalOK Lc s4 T Y → DisjInv s4 ∧
      (T'.out.toList.any WItem.isBranching = true → T'.hasObl = true) ∧
      (E.out.toList.any WItem.isBranching = true → E.hasObl = true) ∧
      ((∀ (n x : P.Ident), s4.tyOf[n]? = some x → T[n]? = none) → TyCtx T Y s4 S Γ →
        LOK Typ Ground T Y false T'.out.toList ∧ LOK Typ Ground T Y false E.out.toList) :=
    fun hfin4 => by
      have hfin2 : FinalOK Lc s2 T Y := FinalOK.back_le (s' := { s2 with live := {} }) rfl rfl rfl
        (fun _ h => h) (Nat.le_refl _) (FinalOK.back_walk hW4.1 hw3 (fun x hx =>
          ⟨(wfl_inits_scope tss hwfT hx).1, fun b j e => by simpa [ha2] using hdT x hx b j e⟩)
          hfin4)
      obtain ⟨D2, -, BE, KE⟩ := hE (fun _ => rfl) _ E s2 hw1 h2 T Y hfin2 S hwfE Γ htyE hngE havE
        (fun _ h => nomatch h) (hD.of_eq rfl rfl)
      obtain ⟨D4, -, BT, KT⟩ := hT (fun _ => rfl) _ T' s4 hw3 h4 T Y hfin4 S hwfT Γ htyT hngT havT
        (fun _ h => nomatch h) (D2.of_eq rfl rfl)
      refine ⟨D4, BT, BE, fun hTY4 hT4 => ⟨(KT hTY4 fun _ => hT4).2.1, ?_⟩⟩
      have hT2 : TyCtx T Y s2 S Γ := TyCtx.back hT4 fun x hx n hn =>
        hW4.1.names x n (wfl_inits_disjoint S tss hwfT x hx) hn
      exact (KE (fun n x h => hTY4 n x (hW4.1.tyOf_keep hw3 h)) fun _ => hT2).2.1
  split at h
  · ty_inv h
    obtain ⟨rfl, rfl⟩ := h
    have hfin4 : FinalOK Lc s4 T Y :=
      FinalOK.back_le rfl rfl rfl (fun _ h => h) (Nat.le_refl _) hfin
    exact plain_close ((harms hfin4).1.of_eq rfl rfl) (fun _ _ _ => .inr nofun) (pend_of_eq rfl)
      (by simp [Rope.toList_nil]) fun _ _ => ⟨by simp [Rope.toList_nil], nofun⟩
  rename_i hob
  ty_inv h
  obtain ⟨⟨⟨wc, rdc⟩, s6⟩, h6, ⟨u, s7⟩, h7, rfl, rfl⟩ := h
  simp only at h7
  obtain ⟨k, hk', hkn, hkav⟩ := freshIn_spec s6.avoid "g" s6.next
  rw [hk'] at h7 ⊢
  obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h7
  obtain ⟨-, hn6, hs6, hc6⟩ := wRen_run h6
  have hfin6 : FinalOK Lc s6 T Y :=
    FinalOK.back_draw hkn hkav (FinalOK.back_le rfl rfl rfl (fun _ h => h) (Nat.le_refl _) hfin)
  have hfin4 : FinalOK Lc s4 T Y := FinalOK.back_le rfl rfl rfl (fun _ h => h) (Nat.le_refl _)
    (FinalOK.back_le (by rw [hs6]) (by rw [hs6]) (by rw [hs6]) (fun _ h => by rw [hs6]; exact h)
      hn6 hfin6)
  obtain ⟨D4, BT, BE, KA⟩ := harms hfin4
  have hTg : tyOfName T Y (freshName (P := P) "g" k) = .ok HasBool.boolTy :=
    tyOfName_T (hfin.drawn (by simp) (by simpa using hkav) ⟨_, k, rfl, by simp⟩)
  have h6t : s6.tys = s4.tys ∧ s6.tyOf = s4.tyOf := by rw [hs6]; exact ⟨rfl, rfl⟩
  refine ⟨DisjInv.ins (s := s4) D4 (hw4.tyOf_none (Nat.le_trans hn6 hkn))
      (by simp only; rw [h6t.1]) (by simp only; rw [h6t.2]),
    pend_of_eq (by simp only; rw [hs6]), fun _ => rfl,
    fun hTY hT' => ⟨fun _ _ _ => .inr nofun, ?_, nofun⟩⟩
  have hT0 := hT' (.inr rfl)
  have hT4 : TyCtx T Y s4 S Γ := TyCtx.back hT0 fun x _ n hn => hc6 x n hn
  obtain ⟨lT, lE⟩ := KA (fun n x h => hTY n x (by simp only; rw [h6t.2]; exact h)) hT4
  have hwc' : WOK Typ T Y wc HasBool.boolTy :=
    wRen_wok hL h6 hrS (fun _ _ _ h => h) hT0 hann hwc
  have hgi : PlainOK Typ Ground T Y (.init (freshName "g" k) (.known HasBool.boolTy)
      (some (kAnd κ wc))) := fun ty hty => by
    cases hty
    exact ⟨fun τ hτ => Except.ok.inj (hτ.symm.trans hTg), hg, fun w hw => by
      cases hw; exact WOK.kIte hL hκ hwc' (WOK.lit hL false)⟩
  have haT : PlainOK Typ Ground T Y (.assume reachLabel (.var (freshName "g" k)) .empty) :=
    WOK.bvar hL hTg
  have haE : PlainOK Typ Ground T Y
      (.assume reachLabel (kAnd κ (WExpr.var (freshName "g" k)).not) .empty) :=
    WOK.kIte hL hκ (WOK.not hL (WOK.bvar hL hTg)) (WOK.lit hL false)
  split
  · simp only [Rope.toList_app, Rope.toList_one, List.singleton_append, LOK, List.any_cons,
      WItem.isBranching, List.any_nil, Bool.or_false, Bool.or_true, forall_const]
    exact ⟨hgi, ⟨fun _ => haT, lT⟩, fun _ => haE, lE⟩
  · split
    all_goals
      simp only [Rope.toList_app, Rope.toList_one, List.cons_append, List.nil_append, LOK]
      first
        | exact ⟨fun _ => hgi, fun _ => haT, lT⟩
        | exact ⟨fun _ => hgi, fun _ => haE, lE⟩


/-! ## Laid-out `ite`s -/

/-- `n` is a fresh name drawn between the states `s` and `s'`: not avoided, with a counter from
    `s.next` on and below `s'.next`. -/
@[expose] def DrawnIn (s s' : WSt P) (n : P.Ident) : Prop :=
  ∃ b j, n = freshName b j ∧ s.avoid.contains n = false ∧ s.next ≤ j ∧ j < s'.next

/-- The facts of a run of `saveRestore xs` from `s` to `s'` with saves `sv`, copies `cp`,
    restores `rs` and copy pairs `cps`: for triples `ns` of a variable of `xs`, its save name and
    its copy name, the items are the saves, copies and restores of the triples, the copy pairs
    pair each variable with its copy name, the save and copy names are drawn by the run and have
    type references to their variable, the type references change only at names the run draws,
    and the state changes only in its counter (which does not decrease) and type references. -/
structure SRFacts (s : WSt P) (xs : List P.Ident) (sv cp rs : Rope (WItem P))
    (cps : List (P.Ident × P.Ident)) (s' : WSt P) (ns : List (P.Ident × P.Ident × P.Ident)) :
    Prop where
  vars : ∀ q ∈ ns, q.1 ∈ xs
  saves : sv.toList = ns.map (fun q => .init q.2.1 (.of q.1) (some (.var q.1)))
  copies : cp.toList = ns.map (fun q => .init q.2.2 (.of q.1) (some (.var q.1)))
  restores : rs.toList = ns.map (fun q => .set q.1 (some (.var q.2.1)))
  pairs : ∀ p ∈ cps, ∃ q ∈ ns, p = (q.1, q.2.2)
  drawn : ∀ q ∈ ns, DrawnIn s s' q.2.1 ∧ DrawnIn s s' q.2.2
  tyOf : ∀ q ∈ ns, s'.tyOf[q.2.1]? = some q.1 ∧ s'.tyOf[q.2.2]? = some q.1
  fresh : ∀ n, s'.tyOf[n]? ≠ s.tyOf[n]? → DrawnIn s s' n
  next : s.next ≤ s'.next
  eq : s' = { s with next := s'.next, tyOf := s'.tyOf }

omit iLF in
/-- A run of `saveRestore xs` has the facts `SRFacts` for some triples. -/
theorem saveRestore_facts {xs : List P.Ident} {s s' : WSt P} {sv cp rs : Rope (WItem P)}
    {cps : List (P.Ident × P.Ident)} (h : (saveRestore xs).run s = .ok ((sv, cp, rs, cps), s')) :
    ∃ ns, SRFacts s xs sv cp rs cps s' ns := by
  unfold saveRestore at h
  obtain ⟨acc, s1, hl, h⟩ := wm_run_bind_ok h
  obtain ⟨sv1, cp1, rs1, cps1⟩ := acc
  cases h
  have hI := wm_forIn_inv (fun S (b : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) ×
      List (P.Ident × P.Ident)) st => ∃ ns, SRFacts s S b.1 b.2.1 b.2.2.1 b.2.2.2 st ns) _ ?_ xs []
    _ s _ s' ⟨[], fun _ h => by simp at h, Rope.toList_nil, Rope.toList_nil, Rope.toList_nil,
      fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => absurd rfl h, Nat.le_refl _, rfl⟩ hl
  · simpa using hI
  intro S y b st b' st' ⟨ns, hS, hsv, hcp, hrs, hcps, hdr, hty, hfr, hle, hst⟩ hb
  obtain ⟨n1, st1, h1, hb⟩ := wm_run_bind_ok hb
  obtain ⟨n2, st2, h2, hb⟩ := wm_run_bind_ok hb
  obtain ⟨k1, hk1, hn1, hav1⟩ := freshIn_spec st.avoid (baseOf y) st.next
  rw [wFreshLike_run, hk1] at h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h1)
  obtain ⟨k2, hk2, hn2, hav2⟩ := freshIn_spec st.avoid (baseOf y) (k1 + 1)
  rw [wFreshLike_run] at h2
  simp only [hk2] at h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h2)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hb)
  have hsa : st.avoid = s.avoid := by rw [hst]
  have hd1 : DrawnIn s ({ st with next := k2 + 1 } : WSt P) (freshName (baseOf y) k1) :=
    ⟨_, k1, rfl, hsa ▸ hav1, by omega, by simp only; omega⟩
  have hd2 : DrawnIn s ({ st with next := k2 + 1 } : WSt P) (freshName (baseOf y) k2) :=
    ⟨_, k2, rfl, hsa ▸ hav2, by omega, by simp only; omega⟩
  have hold : ∀ n, DrawnIn s st n → n ≠ freshName (baseOf y) k1 ∧ n ≠ freshName (baseOf y) k2 :=
    fun n ⟨b, j, he, _, _, hj⟩ => ⟨fun h => absurd (freshName_counter_inj (he.symm.trans h))
      (by omega), fun h => absurd (freshName_counter_inj (he.symm.trans h)) (by omega)⟩
  have hmono : ∀ n, DrawnIn s st n → DrawnIn s ({ st with next := k2 + 1 } : WSt P) n :=
    fun n ⟨b, j, he, ha, h1, h2⟩ => ⟨b, j, he, ha, h1, by simp only; omega⟩
  have h12 : freshName (P := P) (baseOf y) k1 ≠ freshName (baseOf y) k2 := fun he =>
    absurd (freshName_counter_inj he) (by omega)
  refine ⟨_, rfl, ns ++ [(y, freshName (baseOf y) k1, freshName (baseOf y) k2)],
    fun q hq => ?_, by simp [Rope.toList_app, Rope.toList_one, hsv],
    by simp [Rope.toList_app, Rope.toList_one, hcp],
    by simp [Rope.toList_app, Rope.toList_one, hrs],
    fun p hp => ?_, fun q hq => ?_, fun q hq => ?_, fun n hn => ?_, by simp only; omega,
    by rw [hst]⟩
  · simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact List.mem_append_left _ (hS q hq)
    · exact List.mem_append_right _ (.head _)
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨_, List.mem_append_right _ (.head _), rfl⟩
    · exact (hcps p hp).imp fun q ⟨hq, he⟩ => ⟨List.mem_append_left _ hq, he⟩
  · simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact ⟨hmono _ (hdr q hq).1, hmono _ (hdr q hq).2⟩
    · exact ⟨hd1, hd2⟩
  · simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · obtain ⟨a1, a2⟩ := hold _ (hdr q hq).1
      obtain ⟨b1, b2⟩ := hold _ (hdr q hq).2
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm a1, Ne.symm a2, Ne.symm b1,
        Ne.symm b2, ↓reduceIte]
      exact hty q hq
    · simp only [Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm h12, ↓reduceIte]
      exact ⟨trivial, trivial⟩
  · by_cases h1 : n = freshName (baseOf y) k1
    · exact h1 ▸ hd1
    by_cases h2 : n = freshName (baseOf y) k2
    · exact h2 ▸ hd2
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm h1, Ne.symm h2, ↓reduceIte] at hn
    exact hmono _ (hfr n hn)

omit iW iLF in
/-- The final type maps keep the declared types of a well-formed state when they keep those of a
    later state with the same declared types, avoided names and recorded declarations, a counter
    at least as large, and type references changed only at names drawn in between. -/
theorem FinalOK.back_drawnIn {s s' : WSt P} (hwf : WFSt s) (ht : s'.tys = s.tys)
    (ha : s'.avoid = s.avoid) (hk : s'.taken = s.taken) (hn : s.next ≤ s'.next)
    (ho : ∀ n, s'.tyOf[n]? ≠ s.tyOf[n]? → DrawnIn s s' n) (h : FinalOK Lc s' T Y) :
    FinalOK Lc s T Y := by
  have hkeep : ∀ n x, s.tyOf[n]? = some x → s'.tyOf[n]? = some x := fun n x hx =>
    Classical.byContradiction fun hne => by
      obtain ⟨b, j, he, -, hj, -⟩ := ho n (fun e => hne (e ▸ hx))
      obtain ⟨b', j', he', hj'⟩ := hwf.tyOf_fresh n x hx
      exact absurd (freshName_counter_inj (he.symm.trans he')) (by omega)
  refine ⟨fun n ty hn' => ?_, fun n x hx => h.2.1 n x (hkeep n x hx), fun n hn' => ?_⟩
  · rcases h.1 n ty (ht ▸ hn') with h1 | ⟨h1, h2, h3⟩ | ⟨b, j, h1, h2, h3⟩
    · exact .inl h1
    · exact .inr (.inl ⟨h1, fun b j e => ha ▸ h2 b j e, hk ▸ h3⟩)
    · exact .inr (.inr ⟨b, j, h1, Nat.le_trans hn h2, ha ▸ h3⟩)
  · rcases h.2.2 n hn' with h1 | ⟨b, j, h1, h2, h3⟩
    · exact (Classical.em (s'.tyOf[n]? = s.tyOf[n]?)).elim (fun e => .inl (e ▸ h1)) fun e =>
        let ⟨b, j, he, hav, hj, _⟩ := ho n e
        .inr ⟨b, j, he, hj, hav⟩
    · exact .inr ⟨b, j, h1, Nat.le_trans hn h2, ha ▸ h3⟩

omit iW iLF in
/-- An optional draw of a Boolean name leaves the state unchanged or draws a fresh name and gives
    it the Boolean type. -/
theorem OptDraw.cases {b : String} {s s' : WSt P} {o : Option P.Ident} (h : OptDraw b s s' o) :
    (o = none ∧ s' = s) ∨ ∃ k, o = some (freshName b k) ∧ s.next ≤ k ∧
      s.avoid.contains (freshName b k) = false ∧
      s' = { s with next := k + 1, tys := s.tys.insert (freshName b k) HasBool.boolTy } := by
  cases o with
  | none => exact .inl ⟨rfl, h⟩
  | some x =>
    obtain ⟨k, hk, hn, hav⟩ := freshIn_spec s.avoid b s.next
    have h' := (wFreshBool_run b s).symm.trans (show (wFreshBool b).run s = .ok (x, s') from h)
    rw [hk] at h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h'.symm)
    exact .inr ⟨k, rfl, hn, hav, rfl⟩

omit iW iLF in
/-- The final type maps keep the declared types of a state when they keep those after an optional
    draw. -/
theorem FinalOK.back_opt {b : String} {s s' : WSt P} {o : Option P.Ident} (h : OptDraw b s s' o)
    (hf : FinalOK Lc s' T Y) : FinalOK Lc s T Y := by
  rcases h.cases with ⟨-, rfl⟩ | ⟨k, -, hk, hav, rfl⟩
  · exact hf
  · exact FinalOK.back_draw hk hav hf

omit iL in
omit iLB iHI iLF in
/-- A concatenation of item ropes after which a branching item follows is typed when every part
    is. -/
theorem LOK_foldl_app : ∀ (parts : List (Rope (WItem P))) (s : Rope (WItem P)),
    LOK Typ Ground T Y true s.toList → (∀ p ∈ parts, LOK Typ Ground T Y true p.toList) →
    LOK Typ Ground T Y true (parts.foldl Rope.app s).toList
  | [], _, hs, _ => hs
  | p :: parts, s, hs, hp => LOK_foldl_app parts _ (by
      rw [Rope.toList_app]
      exact LOK_append _ _ _ (LOK.imp (fun _ => rfl) hs) (hp p (.head _)))
    fun q hq => hp q (.tail _ hq)

omit iDE iHB iHF iHS iHI iL iHV iW iLF in
/-- An element of an interset of hash sets is in the first one. -/
theorem mem_interSet_left {a b : Std.HashSet P.Ident} {y : P.Ident}
    (h : y ∈ interSet a b) : a.contains y = true := by
  simp only [interSet, Std.HashSet.fold_eq_foldl_toList, ← List.foldl_filter] at h
  split at h <;> simp_all

omit iL iW iLF in
/-- A name drawn between `s` and `s'` is drawn between any state before `s` with the same avoided
    names and any state after `s'`. -/
theorem DrawnIn.widen {s0 s s' s1 : WSt P} {n : P.Ident} (h : DrawnIn s s' n)
    (ha : s.avoid = s0.avoid) (h0 : s0.next ≤ s.next) (h1 : s'.next ≤ s1.next) : DrawnIn s0 s1 n :=
  let ⟨b, j, he, hav, hj1, hj2⟩ := h
  ⟨b, j, he, ha ▸ hav, Nat.le_trans h0 hj1, Nat.lt_of_lt_of_le hj2 h1⟩

omit iW iLF in
/-- A state step that changes the type references only at names drawn by it keeps the type
    references of a well-formed state. -/
theorem tyOf_keep_drawnIn {s s' : WSt P} (hwf : WFSt s)
    (ho : ∀ n, s'.tyOf[n]? ≠ s.tyOf[n]? → DrawnIn s s' n) {n x : P.Ident}
    (hx : s.tyOf[n]? = some x) : s'.tyOf[n]? = some x :=
  Classical.byContradiction fun hne => by
    obtain ⟨b, j, he, -, hj, -⟩ := ho n (fun e => hne (e ▸ hx))
    obtain ⟨b', j', he', hj'⟩ := hwf.tyOf_fresh n x hx
    exact absurd (freshName_counter_inj (he.symm.trans he')) (by omega)

omit iW iLF in
/-- An optional draw keeps the declared type of a name drawn before it. -/
theorem OptDraw.tys_keep {b : String} {s s' : WSt P} {o : Option P.Ident} (h : OptDraw b s s' o)
    {n : P.Ident} {ty : P.Ty} (hn : s.tys[n]? = some ty)
    (hj : ∃ b j, n = freshName b j ∧ j < s.next) : s'.tys[n]? = some ty := by
  rcases h.cases with ⟨-, rfl⟩ | ⟨k, -, hk, -, rfl⟩
  · exact hn
  · obtain ⟨b', j, rfl, hj⟩ := hj
    have hne : freshName (P := P) b k ≠ freshName b' j := fun he =>
      absurd (freshName_counter_inj he) (by omega)
    simpa [Std.HashMap.getElem?_insert, hne] using hn

omit iL iW iLF in
/-- A run of `saveRestore` keeps the avoided names, the declared types, the recorded
    declarations, the renamings, the carried merges and the exit snapshots. -/
theorem SRFacts.same {s s' : WSt P} {xs : List P.Ident} {sv cp rs : Rope (WItem P)}
    {cps : List (P.Ident × P.Ident)} {ns : List (P.Ident × P.Ident × P.Ident)}
    (h : SRFacts s xs sv cp rs cps s' ns) :
    s'.avoid = s.avoid ∧ s'.tys = s.tys ∧ s'.taken = s.taken ∧ s'.nm = s.nm ∧
      s'.carries = s.carries ∧ s'.pending = s.pending := by
  rw [h.eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

omit iW iLF in
/-- An optional draw keeps the avoided names, the type references, the recorded declarations,
    the renamings, the carried merges and the exit snapshots. -/
theorem OptDraw.same {b : String} {s s' : WSt P} {o : Option P.Ident} (h : OptDraw b s s' o) :
    s'.avoid = s.avoid ∧ s'.tyOf = s.tyOf ∧ s'.taken = s.taken ∧ s'.nm = s.nm ∧
      s'.carries = s.carries ∧ s'.pending = s.pending := by
  rcases h.cases with ⟨-, rfl⟩ | ⟨k, -, -, -, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

omit iW iLF in
/-- An optional draw from a state whose type references are of names with a counter below its
    counter keeps `DisjInv`. -/
theorem DisjInv.opt' {b : String} {s s' : WSt P} {o : Option P.Ident} (h : OptDraw b s s' o)
    (hD : DisjInv s)
    (hK : ∀ n x : P.Ident, s.tyOf[n]? = some x → ∃ b j, n = freshName b j ∧ j < s.next) :
    DisjInv s' := by
  rcases h.cases with ⟨-, rfl⟩ | ⟨k, -, hk, -, rfl⟩
  · exact hD
  · refine hD.ins (Option.eq_none_iff_forall_ne_some.2 fun x hx => ?_) rfl rfl
    obtain ⟨b', j, he, hj⟩ := hK _ x hx
    exact absurd (freshName_counter_inj he) (by omega)

omit iW iLF in
/-- A run of `saveRestore` keeps the type reference of a name drawn before it. -/
theorem SRFacts.tyOf_keep {s s' : WSt P} {xs : List P.Ident} {sv cp rs : Rope (WItem P)}
    {cps : List (P.Ident × P.Ident)} {ns : List (P.Ident × P.Ident × P.Ident)}
    (h : SRFacts s xs sv cp rs cps s' ns) {n : P.Ident}
    (hn : ∃ b j, n = freshName b j ∧ j < s.next) :
    s'.tyOf[n]? = s.tyOf[n]? := Classical.byContradiction fun hne => by
  obtain ⟨b, j, he, -, hj, -⟩ := h.fresh n hne
  obtain ⟨b', j', he', hj'⟩ := hn
  exact absurd (freshName_counter_inj (he.symm.trans he')) (by omega)

omit iW iLF in
/-- An optional draw keeps every component of the state but the counter and the declared
    types. -/
theorem OptDraw.eq {b : String} {s s' : WSt P} {o : Option P.Ident} (h : OptDraw b s s' o) :
    s' = { s with next := s'.next, tys := s'.tys } ∧ s.next ≤ s'.next := by
  rcases h.cases with ⟨-, rfl⟩ | ⟨k, -, hk, -, rfl⟩
  · exact ⟨rfl, Nat.le_refl _⟩
  · exact ⟨rfl, by simp only; omega⟩

omit iL in
omit iLB iHI in
/-- The items of a variable `x` with a ground final type and its copy `c` (whose final types are
    those of `x`) are typed: the copy's `init` from `x`, the restore of `x` from `c`, and the merge
    of `x` and `c` under a Boolean selector. -/
theorem copy_plain (hL : TypingLaws Typ Ground) {x c : P.Ident}
    (hx : ∃ τ, tyOfName T Y x = .ok τ ∧ Ground τ)
    (hc : ∀ τ, tyOfName T Y c = .ok τ → tyOfName T Y x = .ok τ) :
    PlainOK Typ Ground T Y (.init c (.of x) (some (.var x))) ∧
      PlainOK Typ Ground T Y (.set x (some (.var c))) ∧
      ∀ e, WOK Typ T Y e HasBool.boolTy →
        PlainOK Typ Ground T Y (.set x (some (.ite e (.var c) (.var x)))) := by
  obtain ⟨τ, hτ, hg⟩ := hx
  have hvx : WOK Typ T Y (.var x) τ := WOK.var hL hg fun τ' h => Except.ok.inj (h.symm.trans hτ)
  have hvc : WOK Typ T Y (.var c) τ := WOK.var hL hg fun τ' h =>
    Except.ok.inj ((hc τ' h).symm.trans hτ)
  refine ⟨fun ty hty => ?_, ⟨τ, hτ, hg, fun w hw => by cases hw; exact hvc⟩,
    fun e he => ⟨τ, hτ, hg, fun w hw => by cases hw; exact WOK.ite hL he hvc hvx⟩⟩
  obtain rfl := Except.ok.inj ((hty : tyOfName T Y x = .ok ty).symm.trans hτ)
  exact ⟨fun τ' h => Except.ok.inj ((hc τ' h).symm.trans hτ), hg, fun w hw => by
    cases hw; exact hvx⟩

omit iLB iHI iL iLF in
/-- An `init` of a Boolean name with a Boolean value is typed. -/
theorem binit_plain (hL : TypingLaws Typ Ground) {x : P.Ident} {w : WExpr P}
    (hx : tyOfName T Y x = .ok HasBool.boolTy) (hw : WOK Typ T Y w HasBool.boolTy) :
    PlainOK Typ Ground T Y (.init x (.known HasBool.boolTy) (some w)) := fun ty hty => by
  cases hty
  exact ⟨fun τ hτ => Except.ok.inj (hτ.symm.trans hx), hL.ground hL.tt, fun w' hw' => by
    cases hw'; exact hw⟩

omit iL in
omit iLB iHI iLF in
/-- An optional item, typed when present, is typed. -/
theorem LOK_ite_one {c : Prop} [Decidable c] {x : WItem P}
    (h : x.isBranching = false ∧ PlainOK Typ Ground T Y x) :
    LOK Typ Ground T Y true (if c then Rope.nil else Rope.one x).toList := by
  split
  · simp [LOK, Rope.toList_nil]
  · exact LOK_plain fun it hit => by
      simp only [Rope.toList_one, List.mem_singleton] at hit
      exact hit ▸ h

omit iLB iHI iL iLF in
/-- An optional rope, typed when present, is typed. -/
theorem LOK_ite_nil {c : Prop} [Decidable c] {p : Rope (WItem P)}
    (h : LOK Typ Ground T Y true p.toList) :
    LOK Typ Ground T Y true (if c then p else Rope.nil).toList := by
  split
  · exact h
  · simp [LOK, Rope.toList_nil]

/-- The walk of a laid-out `ite` has the typing property when the walks of its arms (at the same
    depth, under every context, an obligation following them) have it. -/
theorem typSpec_iteLaid (hL : TypingLaws Typ Ground) {κ : RE P} {d : Nat} {c : P.Expr}
    {tss ess : PStmts P} (md : MetaData P)
    (hT : ∀ κ', ListTypSpec Typ Ground Lc N κ' d true tss)
    (hE : ∀ κ', ListTypSpec Typ Ground Lc N κ' d true ess) :
    TypSpec Typ Ground Lc N κ (wpIteLaid κ d c tss ess) [.ite (.det c) tss ess md]
      (fun S => Stmt.WellScoped Lc S (.ite (.det c) tss ess md)) true := by
  intro st a st' hwf h T Y hfin S hwfs Γ hty hng hav hκ hD
  obtain ⟨hwc, hann, htyT, htyE⟩ := Block.ExprsTyped.ite' hty
  obtain ⟨hngT, hngE⟩ : Block.nondetGround Ground N Γ tss ∧ Block.nondetGround Ground N Γ ess :=
    hng.1
  obtain ⟨hrS, hwfT, hwfE⟩ := hwfs
  have hg : Ground HasBool.boolTy := hL.ground hL.tt
  have hdE : ∀ x ∈ stmtsInits ess, AvoidedIfFresh st x := fun x hx =>
    hav x (by simp [Block.idents, Stmt.idents, (wfl_inits_scope ess hwfE hx).2.1])
  have hdT : ∀ x ∈ stmtsInits tss, AvoidedIfFresh st x := fun x hx =>
    hav x (by simp [Block.idents, Stmt.idents, (wfl_inits_scope tss hwfT hx).2.1])
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T' s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hctx h5 h6 h7 h8 h9 h10 hgm h11
    hqm h12 hrm hEnd => ?_
  obtain ⟨-, hn1, hs1, hc1⟩ := wRen_run h1
  have hw1 : WFSt s1 := (wRen_walk h1).wf hwf nofun
  have hw2 : WFSt s2 := (wFreshBool_walk h2).wf hw1 nofun
  have hw3 : WFSt s3 := (wFreshBool_walk h3).wf hw2 nofun
  obtain ⟨k2, hk2, hkn2, hkav2⟩ := freshIn_spec s1.avoid "g" s1.next
  rw [wFreshBool_run, hk2] at h2
  obtain ⟨hg2, hs2⟩ := Prod.mk.inj (Except.ok.inj h2)
  subst hg2
  obtain ⟨k3, hk3, hkn3, hkav3⟩ := freshIn_spec s2.avoid "r" s2.next
  rw [wFreshBool_run, hk3] at h3
  obtain ⟨hr3, hs3⟩ := Prod.mk.inj (Except.ok.inj h3)
  subst hr3
  obtain ⟨hd4, hκEv, hκE0⟩ : OptDraw "r" s3 s4 rE ∧
      (∀ y ∈ RE.vars κE, y = freshName "g" k2 ∨ rE = some y ∨ y ∈ RE.vars κ) ∧ κE ≠ .top := by
    rcases hctx with ⟨-, hκE, hrE, hs⟩ | ⟨⟨q, hq, hκE⟩, hrE, hs⟩ | ⟨-, x, hκE, hrE, h4⟩
    · exact ⟨by rw [hrE]; exact hs, by rw [hκE]; simp [RE.vars], by rw [hκE]; nofun⟩
    · exact ⟨by rw [hrE]; exact hs, by rw [hκE, hq]; simp [RE.vars], by rw [hκE]; nofun⟩
    · exact ⟨by rw [hrE]; exact h4, by rw [hκE, hrE]; simp [RE.vars], by rw [hκE]; nofun⟩
  obtain ⟨hs4, hn4⟩ := hd4.eq
  have hw4 : WFSt s4 := by
    cases rE with
    | none => exact (show s4 = _ from hd4) ▸ hw3
    | some x => exact (wFreshBool_walk hd4).wf hw3 nofun
  have ha3 : s3.avoid = st.avoid := by rw [← hs3, ← hs2, hs1]
  have ha4 : s4.avoid = st.avoid := by rw [hs4]; exact ha3
  have hW5 := wpList_walkOK h5
  have hW6 := wpList_walkOK h6
  have hw5 : WFSt s5 := hW5.wf hw4 fun x hx b j e => ha4 ▸ hdE x hx b j e
  have hw6 : WFSt s6 := hW6.wf hw5 fun x hx b j e => (hW5.avoid.trans ha4) ▸ hdT x hx b j e
  obtain ⟨ns3, r3⟩ := saveRestore_facts h7
  obtain ⟨nsT, r8⟩ := saveRestore_facts h8
  obtain ⟨nsE, r9⟩ := saveRestore_facts h9
  obtain ⟨hs10, hn10⟩ := h10.eq
  obtain ⟨hs11, hn11⟩ := h11.eq
  obtain ⟨hs12, hn12⟩ := h12.eq
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ : st'.tys = s12.tys ∧ st'.tyOf = s12.tyOf ∧
      st'.avoid = s12.avoid ∧ st'.taken = s12.taken ∧ st'.next = s12.next ∧ st'.nm = s12.nm ∧
      st'.pending = s12.pending ∧ st'.carries = (carryIns (elseGuard κ gm qm rEm)
        (carryOf s6 cpsE E.tgt.max?) (carryIns (optVar gm) (carryOf s6 cpsT T'.tgt.max?)
          s12.carries T'.tgt.max?) E.tgt.max?) := by
    rcases hEnd with ⟨-, rfl, -⟩ | ⟨-, hl, -⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · obtain ⟨live, clock, rfl, -⟩ := liveAdd_step hl
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have fin12 : FinalOK Lc s12 T Y :=
    FinalOK.back_le e1 e2 e3 (fun y h => e4 ▸ h) (e5 ▸ Nat.le_refl _) hfin
  have fin11 := FinalOK.back_opt h12 fin12
  have fin10 := FinalOK.back_opt h11 fin11
  have fin9 := FinalOK.back_opt h10 fin10
  obtain ⟨a7, t7, k7, n7, c7, p7⟩ := r3.same
  obtain ⟨a8, t8, k8, n8, c8, p8⟩ := r8.same
  obtain ⟨a9, t9, k9, n9, c9, p9⟩ := r9.same
  obtain ⟨a10, o10, k10, n10, c10, p10⟩ := h10.same
  obtain ⟨a11, o11, k11, n11, c11, p11⟩ := h11.same
  obtain ⟨a12, o12, k12, n12, c12, p12⟩ := h12.same
  have ho9 : ∀ n, s9.tyOf[n]? ≠ s6.tyOf[n]? → DrawnIn s6 s9 n := fun n hn => by
    by_cases h98 : s9.tyOf[n]? = s8.tyOf[n]?
    · by_cases h87 : s8.tyOf[n]? = s7.tyOf[n]?
      · exact (r3.fresh n fun e => hn (h98.trans (h87.trans e))).widen rfl (Nat.le_refl _)
          (Nat.le_trans r8.next r9.next)
      · exact (r8.fresh n h87).widen a7 r3.next r9.next
    · exact (r9.fresh n h98).widen (a8.trans a7) (Nat.le_trans r3.next r8.next) (Nat.le_refl _)
  have fin6 : FinalOK Lc s6 T Y := FinalOK.back_drawnIn hw6 (t9.trans (t8.trans t7))
    (a9.trans (a8.trans a7)) (k9.trans (k8.trans k7))
    (Nat.le_trans r3.next (Nat.le_trans r8.next r9.next)) ho9 fin9
  have ha5 : s5.avoid = st.avoid := hW5.avoid.trans ha4
  have fin5 : FinalOK Lc s5 T Y := FinalOK.back_walk hW6.1 hw5 (fun x hx =>
    ⟨(wfl_inits_scope tss hwfT hx).1, fun b j e => ha5 ▸ hdT x hx b j e⟩) fin6
  have fin4 : FinalOK Lc s4 T Y := FinalOK.back_walk hW5.1 hw4 (fun x hx =>
    ⟨(wfl_inits_scope ess hwfE hx).1, fun b j e => ha4 ▸ hdE x hx b j e⟩) fin5
  have ty12 : s12.tyOf = s9.tyOf := o12.trans (o11.trans o10)
  have hn2 : s2.next = k2 + 1 := by rw [← hs2]
  have hn3 : s3.next = k3 + 1 := by rw [← hs3]
  have hav21 : s2.avoid = s1.avoid := by rw [← hs2]
  have tg3 : s3.tys[freshName (P := P) "g" k2]? = some HasBool.boolTy := by
    have hne : freshName (P := P) "r" k3 ≠ freshName "g" k2 := fun he =>
      absurd (freshName_counter_inj he) (by omega)
    rw [← hs3, ← hs2]
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq, hne, ↓reduceIte]
  have tr3 : s3.tys[freshName (P := P) "r" k3]? = some HasBool.boolTy := by
    rw [← hs3]
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq, ↓reduceIte]
  have ha1 : s1.avoid = st.avoid := by rw [hs1]
  have hTg : tyOfName T Y (freshName (P := P) "g" k2) = .ok HasBool.boolTy :=
    tyOfName_T (fin4.drawn (hd4.tys_keep tg3 ⟨_, k2, rfl, by omega⟩)
      (by rw [ha4, ← ha1]; exact hkav2)
      ⟨_, k2, rfl, Nat.lt_of_lt_of_le (by omega) hn4⟩)
  have hTr : tyOfName T Y (freshName (P := P) "r" k3) = .ok HasBool.boolTy :=
    tyOfName_T (fin4.drawn (hd4.tys_keep tr3 ⟨_, k3, rfl, by omega⟩)
      (by rw [ha4, ← ha1, ← hav21]; exact hkav3)
      ⟨_, k3, rfl, Nat.lt_of_lt_of_le (by omega) hn4⟩)
  have hTrE : ∀ x, rE = some x → tyOfName T Y x = .ok HasBool.boolTy := fun x hx => by
    rcases hd4.cases with ⟨h0, -⟩ | ⟨k, h0, hk, hk', rfl⟩
    · simp [hx] at h0
    · obtain rfl := Option.some.inj (hx.symm.trans h0)
      exact tyOfName_T (fin4.drawn (by simp) (by simpa [ha3] using hk') ⟨_, k, rfl, by simp⟩)
  have hκE : REOK T Y κE := fun y hy => by
    rcases hκEv y hy with rfl | hy | hy
    · exact hTg
    · exact hTrE y hy
    · exact hκ y hy
  have hTo : ∀ {b : String} {s s' : WSt P} {o : Option P.Ident}, OptDraw b s s' o →
      FinalOK Lc s' T Y → ∀ x, o = some x → tyOfName T Y x = .ok HasBool.boolTy :=
    fun hd hf x hx => by
      rcases hd.cases with ⟨h0, -⟩ | ⟨k, h0, hk, hk', rfl⟩
      · simp [hx] at h0
      · obtain rfl := Option.some.inj (hx.symm.trans h0)
        exact tyOfName_T (hf.drawn (by simp) (by simpa using hk') ⟨_, k, rfl, by simp⟩)
  have hTgm := hTo h10 fin10
  have hTqm := hTo h11 fin11
  have hTrm := hTo h12 fin12
  have hcur6 : ∀ z, curName st' z = curName s6 z := curName_eq_of_nm_taken
    (e6.trans (n12.trans (n11.trans (n10.trans (n9.trans (n8.trans n7))))))
    (e4.trans (k12.trans (k11.trans (k10.trans (k9.trans (k8.trans k7))))))
  have hcur41 : ∀ z, curName s4 z = curName s1 z := curName_eq_of_nm_taken
    (by rw [hs4, ← hs3, ← hs2]) (by rw [hs4, ← hs3, ← hs2])
  have hcurS : ∀ z ∈ S, ∀ m, curName s1 z = some m → curName st' z = some m := fun z hz m hm =>
    (hcur6 z).trans (hW6.names z m (wfl_inits_disjoint S tss hwfT z hz)
      (hW5.names z m (wfl_inits_disjoint S ess hwfE z hz) ((hcur41 z).trans hm)))
  have havE : ∀ x ∈ S ++ Block.idents ess, AvoidedIfFresh s4 x := fun x hx b j e =>
    ha4 ▸ hav x (by grind [Block.idents, Stmt.idents]) b j e
  have havT : ∀ x ∈ S ++ Block.idents tss, AvoidedIfFresh s5 x := fun x hx b j e =>
    ha5 ▸ hav x (by grind [Block.idents, Stmt.idents]) b j e
  have D1 : DisjInv s1 := hD.of_eq (by rw [hs1]) (by rw [hs1])
  have D2 : DisjInv s2 := DisjInv.draw D1 hw1 hkn2 (by rw [← hs2]) (by rw [← hs2])
  have D3 : DisjInv s3 := DisjInv.draw D2 hw2 hkn3 (by rw [← hs3]) (by rw [← hs3])
  have D4 : DisjInv s4 := D3.opt' hd4 fun n x h => hw3.tyOf_fresh n x h
  obtain ⟨D5, PE, BE, KE⟩ := hE κE (fun h => absurd h hκE0) s4 E s5 hw4 h5 T Y fin5 S hwfE Γ
    htyE hngE havE hκE D4
  obtain ⟨D6, PT, BT, KT⟩ := hT (.name (freshName "r" k3)) nofun s5 T' s6 hw5 h6 T Y fin6 S hwfT
    Γ htyT hngT havT (fun y hy => by simp only [RE.vars, List.mem_singleton] at hy; exact hy ▸ hTr)
    D5
  have hK9 : ∀ n x : P.Ident, s9.tyOf[n]? = some x → ∃ b j, n = freshName b j ∧ j < s9.next :=
    fun n x h => by
      by_cases he : s9.tyOf[n]? = s6.tyOf[n]?
      · obtain ⟨b, j, e, hj⟩ := hw6.tyOf_fresh n x (he ▸ h)
        exact ⟨b, j, e, Nat.lt_of_lt_of_le hj (Nat.le_trans r3.next (Nat.le_trans r8.next r9.next))⟩
      · obtain ⟨b, j, e, -, -, hj⟩ := ho9 n he
        exact ⟨b, j, e, hj⟩
  have D9 : DisjInv s9 := DisjInv.step D6 (fun m hm => absurd (by rw [t9, t8, t7]) hm)
    fun m x hm => by
      by_cases he : s9.tyOf[m]? = s6.tyOf[m]?
      · exact .inl (he ▸ hm)
      · obtain ⟨b, j, rfl, hav', hj, -⟩ := ho9 m he
        exact .inr (by rw [t9, t8, t7]; exact hw6.tys_none hj hav')
  have D10 : DisjInv s10 := D9.opt' h10 hK9
  have D11 : DisjInv s11 := D10.opt' h11 fun n x h =>
    (hK9 n x (o10 ▸ h)).imp fun _ => .imp fun _ ⟨e, hj⟩ => ⟨e, Nat.lt_of_lt_of_le hj hn10⟩
  have D12 : DisjInv s12 := D11.opt' h12 fun n x h =>
    (hK9 n x (o10 ▸ o11 ▸ h)).imp fun _ => .imp fun _ ⟨e, hj⟩ =>
      ⟨e, Nat.lt_of_lt_of_le hj (Nat.le_trans hn10 hn11)⟩
  refine ⟨D12.of_eq e1 e2, ?_, ?_, fun hTY hT' => ?_⟩
  rotate_right
  have hTY9 : ∀ (n x : P.Ident), s9.tyOf[n]? = some x → T[n]? = none := fun n x h =>
    hTY n x (by rw [e2, ty12]; exact h)
  have hTY6 : ∀ (n x : P.Ident), s6.tyOf[n]? = some x → T[n]? = none := fun n x h =>
    hTY9 n x (tyOf_keep_drawnIn hw6 ho9 h)
  have hTY5 : ∀ (n x : P.Ident), s5.tyOf[n]? = some x → T[n]? = none := fun n x h =>
    hTY6 n x (hW6.1.tyOf_keep hw5 h)
  have hT0 : TyCtx T Y st' S Γ := hT' (.inl rfl)
  have hT6 : TyCtx T Y s6 S Γ := TyCtx.back hT0 fun z _ m hm => (hcur6 z).trans hm
  have hT5 : TyCtx T Y s5 S Γ := TyCtx.back hT6 fun z hz m hm =>
    hW6.names z m (wfl_inits_disjoint S tss hwfT z hz) hm
  have hwc' : WOK Typ T Y wc HasBool.boolTy := wRen_wok hL h1 hrS hcurS hT0 hann hwc
  obtain ⟨cE, lE, aE⟩ := KE hTY5 fun _ => hT5
  obtain ⟨cT, lT, aT⟩ := KT hTY6 fun _ => hT6
  · have hcopy : ∀ c x, s9.tyOf[c]? = some x → ∀ τ, tyOfName T Y c = .ok τ →
        tyOfName T Y x = .ok τ := fun c x h τ => tyOfName_copy (hTY9 c x h) (fin9.2.1 c x h)
    have hlt : ∀ {s s' : WSt P} {n : P.Ident}, DrawnIn s s' n →
        ∃ b j, n = freshName b j ∧ j < s'.next := fun ⟨b, j, he, _, _, hj⟩ => ⟨b, j, he, hj⟩
    have hp3 : ∀ q ∈ ns3, (∃ τ, tyOfName T Y q.1 = .ok τ ∧ Ground τ) ∧
        (∀ τ, tyOfName T Y q.2.1 = .ok τ → tyOfName T Y q.1 = .ok τ) ∧
        ∀ τ, tyOfName T Y q.2.2 = .ok τ → tyOfName T Y q.1 = .ok τ := fun q hq => by
      have hx := r3.vars q hq
      split at hx
      · simp at hx
      refine ⟨aT rfl _ (mem_interSet_left hx), hcopy _ _ ?_, hcopy _ _ ?_⟩
      · rw [r9.tyOf_keep (hlt (r3.drawn q hq).1 |>.imp fun _ => .imp fun _ ⟨e, h⟩ =>
          ⟨e, Nat.lt_of_lt_of_le h r8.next⟩), r8.tyOf_keep (hlt (r3.drawn q hq).1)]
        exact (r3.tyOf q hq).1
      · rw [r9.tyOf_keep (hlt (r3.drawn q hq).2 |>.imp fun _ => .imp fun _ ⟨e, h⟩ =>
          ⟨e, Nat.lt_of_lt_of_le h r8.next⟩), r8.tyOf_keep (hlt (r3.drawn q hq).2)]
        exact (r3.tyOf q hq).2
    have hpT : ∀ q ∈ nsT, (∃ τ, tyOfName T Y q.1 = .ok τ ∧ Ground τ) ∧
        (∀ τ, tyOfName T Y q.2.1 = .ok τ → tyOfName T Y q.1 = .ok τ) ∧
        ∀ τ, tyOfName T Y q.2.2 = .ok τ → tyOfName T Y q.1 = .ok τ := fun q hq =>
      ⟨aT rfl _ (fold_filter_mem (r8.vars q hq)),
        hcopy _ _ (by rw [r9.tyOf_keep (hlt (r8.drawn q hq).1)]; exact (r8.tyOf q hq).1),
        hcopy _ _ (by rw [r9.tyOf_keep (hlt (r8.drawn q hq).2)]; exact (r8.tyOf q hq).2)⟩
    have hpE : ∀ q ∈ nsE, (∃ τ, tyOfName T Y q.1 = .ok τ ∧ Ground τ) ∧
        (∀ τ, tyOfName T Y q.2.1 = .ok τ → tyOfName T Y q.1 = .ok τ) ∧
        ∀ τ, tyOfName T Y q.2.2 = .ok τ → tyOfName T Y q.1 = .ok τ := fun q hq =>
      ⟨aE rfl _ (fold_filter_mem (r9.vars q hq)), hcopy _ _ (r9.tyOf q hq).1,
        hcopy _ _ (r9.tyOf q hq).2⟩
    have hgm' : WOK Typ T Y (optVar gm) HasBool.boolTy := by
      cases gm with
      | none => exact WOK.lit hL false
      | some x => exact WOK.bvar hL (hTgm x rfl)
    have hEg : WOK Typ T Y (elseGuard κ gm qm rEm) HasBool.boolTy := by
      unfold elseGuard
      split
      · exact WOK.not hL hgm'
      · exact WOK.and hL (WOK.bvar hL (hTqm _ rfl)) (WOK.not hL hgm')
      · exact WOK.bvar hL (hTrm _ rfl)
      · exact WOK.lit hL false
    refine ⟨fun k q hq => ?_, ?_, fun _ n hn => ?_⟩
    · rw [e8] at hq
      obtain ⟨nE, eE, hnE⟩ := carryIns_getD (elseGuard κ gm qm rEm) (carryOf s6 cpsE E.tgt.max?)
        (carryIns (optVar gm) (carryOf s6 cpsT T'.tgt.max?) s12.carries T'.tgt.max?) E.tgt.max? k
      obtain ⟨nT, eT, hnT⟩ := carryIns_getD (optVar gm) (carryOf s6 cpsT T'.tgt.max?) s12.carries
        T'.tgt.max? k
      rw [eE, eT, List.mem_append, List.mem_append] at hq
      rcases hq with hq | hq | hq
      · obtain ⟨-, p, hp, rfl⟩ := hnE q hq
        obtain ⟨q', hq', rfl⟩ := r9.pairs p (carryOf_sub hp)
        obtain ⟨h1, -, h3⟩ := hpE q' hq'
        exact .inr fun _ => (copy_plain hL h1 h3).2.2 _ hEg
      · obtain ⟨-, p, hp, rfl⟩ := hnT q hq
        obtain ⟨q', hq', rfl⟩ := r8.pairs p (carryOf_sub hp)
        obtain ⟨h1, -, h3⟩ := hpT q' hq'
        exact .inr fun _ => (copy_plain hL h1 h3).2.2 _ hgm'
      · rw [c12, c11, c10, c9, c8, c7] at hq
        rcases cT k q hq with hq | hq
        · rcases cE k q hq with hq | hq
          · exact .inl (by rw [hs4, ← hs3, ← hs2, hs1] at hq; exact hq)
          · exact .inr hq
        · exact .inr hq
    · rcases hEnd with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · simp [LOK, Rope.toList_nil]
      rw [Rope.toList_app, Rope.toList_one]
      refine LOK_append true _ _ (LOK_plain fun it hm => ?_)
        (LOK_foldl_app _ _ (by simp [LOK, Rope.toList_nil]) fun p hp => ?_)
      · simp only [List.mem_singleton] at hm
        subst hm
        exact ⟨rfl, binit_plain hL hTg (WOK.kIte hL hκ hwc' (WOK.lit hL false))⟩
      have hsr : ∀ {s s' : WSt P} {xs : List P.Ident} {sv cp rs : Rope (WItem P)}
          {cps : List (P.Ident × P.Ident)} {ns : List (P.Ident × P.Ident × P.Ident)},
          SRFacts s xs sv cp rs cps s' ns → (∀ q ∈ ns, (∃ τ, tyOfName T Y q.1 = .ok τ ∧ Ground τ) ∧
            (∀ τ, tyOfName T Y q.2.1 = .ok τ → tyOfName T Y q.1 = .ok τ) ∧
            ∀ τ, tyOfName T Y q.2.2 = .ok τ → tyOfName T Y q.1 = .ok τ) →
          LOK Typ Ground T Y true sv.toList ∧ LOK Typ Ground T Y true cp.toList ∧
            LOK Typ Ground T Y true rs.toList := fun h hp => by
        refine ⟨LOK_plain fun it hit => ?_, LOK_plain fun it hit => ?_, LOK_plain fun it hit => ?_⟩
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (h.saves ▸ hit)
          exact ⟨rfl, (copy_plain hL (hp q hq).1 (hp q hq).2.1).1⟩
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (h.copies ▸ hit)
          exact ⟨rfl, (copy_plain hL (hp q hq).1 (hp q hq).2.2).1⟩
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (h.restores ▸ hit)
          exact ⟨rfl, (copy_plain hL (hp q hq).1 (hp q hq).2.1).2.1⟩
      have hU : WOK Typ T Y ((WExpr.var (freshName "r" k3)).or (kExpr κE)) HasBool.boolTy :=
        WOK.or hL (WOK.bvar hL hTr) (WOK.kExpr hL hκE)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
      · exact LOK_ite_one ⟨rfl, binit_plain hL hTr (WOK.bvar hL hTg)⟩
      · split
        · exact LOK_plain fun it hit => by
            simp only [Rope.toList_one, List.mem_singleton] at hit
            subst hit
            exact ⟨rfl, binit_plain hL (hTgm _ rfl) (WOK.bvar hL hTg)⟩
        · simp [LOK, Rope.toList_nil]
      · split
        · exact LOK_plain fun it hit => by
            simp only [Rope.toList_one, List.mem_singleton] at hit
            subst hit
            exact ⟨rfl, binit_plain hL (hTqm _ rfl) (WOK.bvar hL (hκ _ (.head _)))⟩
        · simp [LOK, Rope.toList_nil]
      · exact (hsr r3 hp3).1
      · exact (hsr r8 hpT).1
      · exact lT
      · exact (hsr r3 hp3).2.1
      · exact (hsr r8 hpT).2.1
      · exact (hsr r3 hp3).2.2
      · exact (hsr r8 hpT).2.2
      · split
        · exact LOK_ite_one ⟨rfl, binit_plain hL (hTrE _ rfl)
            (WOK.kIte hL hκ (WOK.not hL (WOK.bvar hL hTg)) (WOK.lit hL false))⟩
        · simp [LOK, Rope.toList_nil]
      · split
        · exact LOK_plain fun it hit => by
            simp only [Rope.toList_one, List.mem_singleton] at hit
            subst hit
            exact ⟨rfl, binit_plain hL (hTrm _ rfl) (WOK.bvar hL (hTrE _ rfl))⟩
        · simp [LOK, Rope.toList_nil]
      · exact (hsr r9 hpE).1
      · exact lE
      · exact (hsr r9 hpE).2.1
      · exact (hsr r9 hpE).2.2
      · refine LOK_plain fun it hit => ?_
        obtain h | ⟨p, hp, rfl⟩ := mem_foldl_set _ _ _ _ _ hit
        · simp [Rope.toList_nil] at h
        obtain ⟨q, hq, rfl⟩ := r3.pairs p (List.mem_filter.1 hp).1
        obtain ⟨h1, -, h3⟩ := hp3 q hq
        refine ⟨rfl, ?_⟩
        split
        · exact (copy_plain hL h1 h3).2.2 _ hgm'
        · exact (copy_plain hL h1 h3).2.1
      · refine LOK_ite_nil ?_
        split
        · exact LOK_plain fun it hit => by
            simp only [Rope.toList_one, List.mem_singleton] at hit
            subst hit
            exact ⟨rfl, hU⟩
        · exact LOK_plain fun it hit => setReach_plain hL hκ hU it hit
    · rcases hEnd with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · simp at hn
      · simp only [unionSet_contains, Bool.or_eq_true] at hn
        rcases hn with hn | hn <;> split at hn
        all_goals first
          | exact aT rfl n hn
          | exact aE rfl n hn
          | simp at hn
  · have hp4 : s4.pending = st.pending := by rw [hs4, ← hs3, ← hs2, hs1]
    intro l e he
    rw [e7, p12, p11, p10, p9, p8, p7] at he
    rcases PT l e he with he | he
    · rcases PE l e he with he | he
      · exact .inl (hp4 ▸ he)
      · exact .inr he
    · exact .inr he
  · rcases hEnd with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · simp [Rope.toList_nil]
    intro hb
    obtain ⟨it, hit, hbr⟩ := List.any_eq_true.1 hb
    clear hb
    rw [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
      List.nil_append, List.singleton_append, List.mem_cons, List.mem_flatMap] at hit
    rcases hit with rfl | ⟨p, hp, hit⟩
    · cases hbr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    show (T'.hasObl || E.hasObl) = true
    have hnb : ∀ {it : WItem P}, it.isBranching = true → ∀ {L : List (WItem P)},
        (∀ x ∈ L, x.isBranching = false) → it ∈ L → False := fun hb _ hL h => by
      simp [hL _ h] at hb
    have hsr : ∀ {s s' : WSt P} {xs : List P.Ident} {sv cp rs : Rope (WItem P)}
        {cps : List (P.Ident × P.Ident)} {ns : List (P.Ident × P.Ident × P.Ident)},
        SRFacts s xs sv cp rs cps s' ns →
        (∀ x ∈ sv.toList, x.isBranching = false) ∧ (∀ x ∈ cp.toList, x.isBranching = false) ∧
          ∀ x ∈ rs.toList, x.isBranching = false := fun h => by
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨q, -, rfl⟩ := List.mem_map.1 (h.saves ▸ hx)
        rfl
      · obtain ⟨q, -, rfl⟩ := List.mem_map.1 (h.copies ▸ hx)
        rfl
      · obtain ⟨q, -, rfl⟩ := List.mem_map.1 (h.restores ▸ hx)
        rfl
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Bool.or_eq_true_iff.2 (.inl (BT (List.any_eq_true.2 ⟨it, hit, hbr⟩)))
      | exact Bool.or_eq_true_iff.2 (.inr (BE (List.any_eq_true.2 ⟨it, hit, hbr⟩)))
      | exact (hnb hbr (hsr r3).1 hit).elim
      | exact (hnb hbr (hsr r3).2.1 hit).elim
      | exact (hnb hbr (hsr r3).2.2 hit).elim
      | exact (hnb hbr (hsr r8).1 hit).elim
      | exact (hnb hbr (hsr r8).2.1 hit).elim
      | exact (hnb hbr (hsr r8).2.2 hit).elim
      | exact (hnb hbr (hsr r9).1 hit).elim
      | exact (hnb hbr (hsr r9).2.1 hit).elim
      | exact (hnb hbr (hsr r9).2.2 hit).elim
      | skip
    all_goals first
      | (obtain h | ⟨q, -, rfl⟩ := mem_foldl_set _ _ _ _ _ hit
         · simp [Rope.toList_nil] at h
         · cases hbr)
      | ((try dsimp only at hit)
         (repeat' split at hit) <;> first
          | (simp only [Rope.toList_nil, List.not_mem_nil] at hit)
          | (simp only [Rope.toList_one, List.mem_singleton] at hit; subst hit; cases hbr)
          | exact absurd hbr (by simp [setReach_noBr it hit]))

/-- The walk of an `exit` has the typing property. -/
theorem stmtTypSpec_exit (hL : TypingLaws Typ Ground) (κ : RE P) (d : Nat) (f : Bool) (l : String)
    (md : MetaData P) : StmtTypSpec Typ Ground Lc N κ d f (.exit l md) := by
  intro st a st' hwf h T Y hfin S hwfs Γ hty hng hav hκ hD
  have hg : Ground HasBool.boolTy := hL.ground hL.tt
  unfold wpStmt at h
  cases κ <;> ty_inv h <;> (try split at h) <;> cases f <;> (try ty_inv h)
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := h
       exact plain_close (hD.of_eq rfl rfl) (car_of_eq rfl) (pend_of_eq rfl)
         (fun it hm => (setReach_plain hL hκ (WOK.lit hL false) it hm).1)
         fun _ _ => ⟨fun it hm => (setReach_plain hL hκ (WOK.lit hL false) it hm).2,
           fun _ m hm => by simp at hm⟩)
    | (obtain ⟨rfl, rfl⟩ := h
       exact plain_close (hD.of_eq rfl rfl) (car_of_eq rfl) (pend_of_eq rfl)
         (by simp [Rope.toList_nil]) fun _ _ =>
         ⟨by simp [Rope.toList_nil], fun _ m hm => by simp at hm⟩)
    | skip
  all_goals
    obtain ⟨k, hk', hkn, hkav⟩ := freshIn_spec st.avoid "r" st.next
    rw [hk'] at h
    obtain ⟨⟨u, s1⟩, h1, rfl, rfl⟩ := h
    obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h1
    have hTe : tyOfName T Y (freshName (P := P) "r" k) = .ok HasBool.boolTy :=
      tyOfName_T (hfin.drawn (by simp) (by simpa using hkav) ⟨_, k, rfl, by simp⟩)
    refine plain_close (DisjInv.draw (s := st) hD hwf hkn rfl rfl) (car_of_eq rfl)
      (fun l' e he => ?_) (fun it hm => ?_)
      fun _ _ => ⟨fun it hm => ?_, fun _ m hm => by simp at hm⟩
    · simp only [Std.HashMap.getD_insert] at he
      split at he
      · rcases List.mem_cons.1 he with rfl | he
        · exact .inr hTe
        · exact .inl (by simpa [beq_iff_eq.1 ‹_›] using he)
      · exact .inl he
    all_goals simp only [Rope.toList_app, Rope.toList_one, List.singleton_append,
      List.mem_cons] at hm
    all_goals rcases hm with rfl | hm
    · rfl
    · exact (setReach_plain hL hκ (WOK.lit hL false) it hm).1
    · intro ty hty
      cases hty
      exact ⟨fun τ hτ => Except.ok.inj (hτ.symm.trans hTe), hg, fun w hw => by
        cases hw; exact WOK.kExpr hL hκ⟩
    · exact (setReach_plain hL hκ (WOK.lit hL false) it hm).2
end

section
variable {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop} {N : P.Ident → Prop}

omit iLF in
mutual
/-- **Every statement-list walk has the typing property.** -/
theorem wpList_typSpec [LawfulHasFvars P] (hL : TypingLaws Typ Ground) :
    ∀ (ss : PStmts P) (κ : RE P) (d : Nat) (fEnd : Bool), ListTypSpec Typ Ground Lc N κ d fEnd ss
  | [], κ, d, fEnd => listTypSpec_nil κ d fEnd
  | s :: rest, κ, d, fEnd =>
    listTypSpec_cons (fun f => wpStmt_typSpec hL s κ d f) (wpList_typSpec hL rest κ d fEnd)
/-- Every statement walk has the typing property. -/
theorem wpStmt_typSpec [LawfulHasFvars P] (hL : TypingLaws Typ Ground) :
    ∀ (s : PStmt P) (κ : RE P) (d : Nat) (f : Bool), StmtTypSpec Typ Ground Lc N κ d f s
  | .cmd c, κ, d, f => stmtTypSpec_cmd hL κ d f c
  | .exit l md, κ, d, f => stmtTypSpec_exit hL κ d f l md
  | .block l body md, κ, d, f =>
    stmtTypSpec_block hL md fun κB => wpList_typSpec hL body κB (d + 1) f
  | .ite (.det c) tss ess md, κ, d, f => by
    cases f <;> simp only [StmtTypSpec, wpStmt, Bool.false_eq_true, ↓reduceIte]
    · exact stmtTypSpec_iteReal hL md (wpList_typSpec hL tss .top d false)
        (wpList_typSpec hL ess .top d false)
    · exact typSpec_iteLaid hL md (fun κ' => wpList_typSpec hL tss κ' d true)
        (fun κ' => wpList_typSpec hL ess κ' d true)
  | .ite .nondet _ _ _, κ, d, f | .loop _ _ _ _ _, κ, d, f | .typeDecl _ _, κ, d, f =>
    stmtTypSpec_other κ d f _ ⟨nofun, nofun, nofun, nofun⟩
end
end

/-! ## The output of the WP phase -/

/-- **The output of the WP phase is well typed** for typing laws `TypingLaws Typ Ground`: the
    guarded program of a loop-free list `ss` well scoped from the variables of `tys`, reading only
    variables of `tys`, and well typed under `tys`, is well typed under the typing of the free
    variables of `ss` by `tys`. -/
theorem wpEntry_wellTyped_of [LawfulHasVal P] [HasOps P] [LawfulHasFvar P]
    {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop} (hL : TypingLaws Typ Ground)
    {G : IdSet P} {tys : Tys P} {ss : PStmts P} {w : WOut P} (h : wpEntry G tys ss = .ok w)
    (hwf : Block.WellScoped Lc (tys.map (·.1)) ss)
    (hfv : ∀ x ∈ Block.freeVars ss, x ∈ tys.map (·.1))
    (htyp : Block.WellTyped Typ Ground (fun x => tys.get? x) ss) :
    Block.WellTyped Typ Ground (fun x => if x ∈ Block.freeVars ss then tys.get? x else none)
      w.lay := by
  have hfvw := wpEntry_fv h hwf
  simp only [wpEntry, wpBody, StateT.run, Except.bind_is_ok, Except.pure_is_ok] at h
  obtain ⟨⟨r, st1⟩, hrun, lay, hlay, rfl⟩ := h
  obtain ⟨hty, N, hng⟩ := htyp
  have hav : ∀ y ∈ tys.map (·.1) ++ Block.idents ss, ∀ b j, y = freshName b j →
      (inputAvoid G tys ss).contains y = true := fun y hy _ _ _ => by
    grind [inputAvoid, AvoidSet.contains, IdSet.ofList]
  obtain ⟨hcur, -, hget⟩ := wpList_top_facts hwf ⟨rfl, rfl, rfl, rfl⟩
    (fun y hy b j hj => hav y (List.mem_append_left _ hy) b j hj) hrun
  obtain ⟨D1, -, -, K⟩ := wpList_typSpec (Lc := Lc) (N := N) hL ss .top 0 false (fun _ => rfl) _ r
    st1 (by constructor <;> grind [TyKey, inputAvoid, AvoidSet.contains, IdSet.ofList,
      → foldr_insert_key]) hrun st1.tys st1.tyOf
    ⟨fun _ _ h => .inl h, fun _ _ h => h, fun _ h => .inl h⟩ _ hwf
    _ hty hng hav (fun _ h => nomatch h) (fun _ _ h => by simp at h)
  obtain ⟨-, hlok, -⟩ := K (fun n x h => D1 n x h) fun _ x hx ty hty' n hn => by
    obtain rfl := Option.some.inj ((hcur x hx).1.symm.trans hn)
    exact wpList_top_tyOfName hwf ⟨rfl, rfl, rfl, rfl⟩
      (fun y hy b j hj => hav y (List.mem_append_left _ hy) b j hj) hrun x hx ty hty'
  obtain ⟨items, hitems, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 hlay
  have htok := nest_TyOK hL false _ (mergeObls_IOK false _ (resolveItems_IOK false _ _ hitems hlok))
  obtain ⟨hE, hN⟩ := Block.wellTyped_of_tyOK hL _
    (fun x => if x ∈ Block.freeVars ss then tys.get? x else none) htok fun x hx τ hτ => by
      have hxs := hfvw x hx
      simp only [hxs, ↓reduceIte]
      exact hget x (hfv x hxs) τ (tyOpt_eq.1 hτ)
  exact ⟨hE, _, hN⟩

end -- public section

end WP
end Imperative
