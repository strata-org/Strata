/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify
import all Strata.Transform.Simplify

/-! # The live-set bookkeeping of the dead-definition sweep

`dropDeadDefsAux` threads one `Std.HashSet` of live names through the whole sweep and
updates it in place: the arms of a branch are swept one after the other, the names the
first arm inserted being erased before the second and inserted again after it. This file
shows that the bookkeeping is exact:
- `dropDeadDefsAux_congr`: the swept statements, and the members of the returned live
  set, depend only on the members of the live set the sweep starts from, and not on
  `added`;
- `dropDeadDefsAux_inserted`: `added` records exactly the names the sweep inserted, none of
  them live before;
- `dropDeadDefsArms_spec`: the in-place sweep of a branch's arms gives the same arms as
  sweeping each one on its own from the live set after the branch, and returns the
  union of what those two sweeps return.
- `dropDeadDefsStmt_agree`, `dropDeadDefsArms_agree`, `dropDeadDefsAux_agree`: the mutual
  induction behind all three, which says that two sweeps from sets with the same members
  agree (`LiveAgree`); a proof about a single statement or a branch can use them directly.
-/

public section

namespace Core.Simplify

open Std

/-- Two live sets with the same members. -/
@[expose] def SameLive (a b : HashSet String) : Prop := ∀ x, x ∈ a ↔ x ∈ b

/-- `SameLive` is reflexive. -/
theorem SameLive.refl (a : HashSet String) : SameLive a a := fun _ => Iff.rfl

/-- `SameLive` is symmetric. -/
theorem SameLive.symm {a b : HashSet String} (h : SameLive a b) : SameLive b a :=
  fun x => (h x).symm

/-- `SameLive` is transitive. -/
theorem SameLive.trans {a b c : HashSet String} (h₁ : SameLive a b) (h₂ : SameLive b c) :
    SameLive a c := fun x => (h₁ x).trans (h₂ x)

/-- Sets with the same members answer `contains` alike. -/
theorem SameLive.contains_eq {a b : HashSet String} (h : SameLive a b) (x : String) :
    a.contains x = b.contains x := by
  have hx := h x
  simp only [HashSet.mem_iff_contains] at hx
  cases ha : a.contains x <;> cases hb : b.contains x <;> simp_all

/-- Inserting the same name into sets with the same members keeps them so. -/
theorem SameLive.insert {a b : HashSet String} (h : SameLive a b) (y : String) :
    SameLive (a.insert y) (b.insert y) := fun x => by
  simp only [HashSet.mem_insert, h x]

/-- Erasing the same name from sets with the same members keeps them so. -/
theorem SameLive.erase {a b : HashSet String} (h : SameLive a b) (y : String) :
    SameLive (a.erase y) (b.erase y) := fun x => by
  simp only [HashSet.mem_erase, h x]

/-! ## `insertTracked` -/

/-- What a sweep step did to the live set: it inserted exactly the names `new`, distinct
    and none of them live before. -/
structure Inserted (live : HashSet String) (new : List String) (live' : HashSet String) :
    Prop where
  nodup : new.Nodup
  fresh : ∀ x ∈ new, x ∉ live
  mem : ∀ x, x ∈ live' ↔ x ∈ live ∨ x ∈ new

/-- Inserting nothing leaves the set as it was. -/
theorem Inserted.nil (live : HashSet String) : Inserted live [] live :=
  ⟨.nil, by simp, by simp⟩

/-- Two insertion steps in a row insert what each inserts, the later names first. -/
theorem Inserted.trans {l₀ l₁ l₂ : HashSet String} {n₁ n₂ : List String}
    (h₁ : Inserted l₀ n₁ l₁) (h₂ : Inserted l₁ n₂ l₂) : Inserted l₀ (n₂ ++ n₁) l₂ where
  nodup := by
    refine List.nodup_append.mpr ⟨h₂.nodup, h₁.nodup, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact h₂.fresh x hx ((h₁.mem x).mpr (.inr hy))
  fresh := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact fun h => h₂.fresh x hx ((h₁.mem x).mpr (.inl h))
    · exact h₁.fresh x hx
  mem := by
    intro x
    rw [h₂.mem x, h₁.mem x, List.mem_append]
    constructor
    · rintro ((h | h) | h) <;> simp [h]
    · rintro (h | h | h) <;> simp [h]

/-- `insertTracked` of no names returns the set and `added` unchanged. -/
theorem insertTracked_nil (live : HashSet String) (added : List String) :
    insertTracked live added [] = (live, added) := by
  unfold insertTracked; rfl

/-- `insertTracked` of a non-empty list inserts the head, consing it onto `added` when it
    was not already present, and goes on with the tail. -/
theorem insertTracked_cons (live : HashSet String) (added : List String) (y : String)
    (ys : List String) :
    insertTracked live added (y :: ys) =
      insertTracked (live.insert y) (if live.contains y then added else y :: added) ys := by
  have h : live.containsThenInsert y = (live.contains y, live.insert y) :=
    Prod.ext HashSet.containsThenInsert_fst HashSet.containsThenInsert_snd
  simp only [insertTracked, List.foldl_cons, h]

/-- Inserting a name already present changes no membership. -/
theorem SameLive.insert_of_mem {live : HashSet String} {y : String} (hy : y ∈ live) :
    SameLive (live.insert y) live := fun x => by
  rw [HashSet.mem_insert]
  constructor
  · rintro (h | h)
    · exact (HashSet.mem_congr h).mp hy
    · exact h
  · exact .inr

/-- A name is in the set `insertTracked` returns exactly when it was in the set before or
    is one of the names inserted. -/
theorem insertTracked_mem (live : HashSet String) (added ys : List String) (x : String) :
    x ∈ (insertTracked live added ys).1 ↔ x ∈ live ∨ x ∈ ys := by
  induction ys generalizing live added with
  | nil => simp [insertTracked_nil]
  | cons y ys ih =>
    rw [insertTracked_cons, ih, HashSet.mem_insert, List.mem_cons, beq_iff_eq]
    constructor
    · rintro ((rfl | h) | h) <;> simp_all
    · rintro (h | rfl | h) <;> simp_all

/-- Inserting a name not yet present. -/
theorem Inserted.singleton {live : HashSet String} {y : String} (hy : y ∉ live) :
    Inserted live [y] (live.insert y) :=
  ⟨List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    fun x hx => by rw [List.mem_singleton.mp hx]; exact hy,
    fun x => by rw [HashSet.mem_insert, List.mem_singleton, beq_iff_eq, eq_comm, or_comm]⟩

/-- Erasing the names a step inserted gives back the set it started from. -/
theorem Inserted.erase_all {live live' : HashSet String} {new : List String}
    (h : Inserted live new live') : SameLive (new.foldl (·.erase ·) live') live := by
  suffices ∀ (l : HashSet String) (ns : List String), ns.Nodup →
      (∀ x, x ∈ l ↔ x ∈ live ∨ x ∈ ns) → (∀ x ∈ ns, x ∉ live) →
      SameLive (ns.foldl (·.erase ·) l) live from
    this live' new h.nodup h.mem h.fresh
  intro l ns
  induction ns generalizing l with
  | nil => intro _ hl _ x; simpa using hl x
  | cons n ns ih =>
    intro hnd hl hfresh
    have hn : n ∉ ns := (List.nodup_cons.mp hnd).1
    refine ih _ (List.nodup_cons.mp hnd).2 (fun x => ?_) (fun x hx => hfresh x (.tail _ hx))
    simp only [HashSet.mem_erase, hl x, List.mem_cons, beq_eq_false_iff_ne, ne_eq]
    constructor
    · rintro ⟨hne, h | h | h⟩
      · exact .inl h
      · exact absurd h.symm hne
      · exact .inr h
    · rintro (h | h)
      · exact ⟨fun he => hfresh x (by simp [← he]) h, .inl h⟩
      · exact ⟨fun he => hn (he ▸ h), .inr (.inr h)⟩

/-- Erasing the same names from sets with the same members keeps them so. -/
theorem SameLive.foldl_erase {a b : HashSet String} (h : SameLive a b) (ns : List String) :
    SameLive (ns.foldl (·.erase ·) a) (ns.foldl (·.erase ·) b) := by
  induction ns generalizing a b with
  | nil => exact h
  | cons n ns ih => exact ih (h.erase n)

/-- `Inserted` only looks at the members of the set it starts from. -/
theorem Inserted.congr_left {a b c : HashSet String} {new : List String}
    (h : Inserted a new c) (hab : SameLive a b) : Inserted b new c :=
  ⟨h.nodup, fun x hx hb => h.fresh x hx ((hab x).mpr hb),
    fun x => (h.mem x).trans (by rw [hab x])⟩

/-! ## Two runs of a sweep -/

/-- Two runs of a sweep step, one from `a` consing onto `added₁` and returning `l₁` and
    `r₁`, the other from a set with the same members as `a` consing onto `added₂` and
    returning `l₂` and `r₂`: they return live sets with the same members, and both cons
    the same names `new`, which are exactly the names the step inserted. -/
@[expose] def LiveAgree (a : HashSet String) (added₁ added₂ : List String)
    (l₁ : HashSet String) (r₁ : List String) (l₂ : HashSet String) (r₂ : List String) : Prop :=
  SameLive l₁ l₂ ∧ ∃ new, r₁ = new ++ added₁ ∧ r₂ = new ++ added₂ ∧ Inserted a new l₁

/-- Two sweep steps in a row agree when each does: the names they cons compose. -/
theorem LiveAgree.seq {a l₁ l₂ m₁ m₂ : HashSet String} {ad₁ ad₂ r₁ r₂ s₁ s₂ : List String}
    (h₁ : LiveAgree a ad₁ ad₂ l₁ r₁ l₂ r₂) (h₂ : LiveAgree l₁ r₁ r₂ m₁ s₁ m₂ s₂) :
    LiveAgree a ad₁ ad₂ m₁ s₁ m₂ s₂ := by
  obtain ⟨-, n₁, hr₁, hr₂, hi₁⟩ := h₁
  obtain ⟨hm, n₂, hs₁, hs₂, hi₂⟩ := h₂
  exact ⟨hm, n₂ ++ n₁, by simp [hs₁, hr₁], by simp [hs₂, hr₂], hi₁.trans hi₂⟩

/-- Agreement depends only on the members of the set the steps start from. -/
theorem LiveAgree.congr_left {a b l₁ l₂ : HashSet String} {ad₁ ad₂ r₁ r₂ : List String}
    (h : LiveAgree a ad₁ ad₂ l₁ r₁ l₂ r₂) (hab : SameLive a b) :
    LiveAgree b ad₁ ad₂ l₁ r₁ l₂ r₂ := by
  obtain ⟨hl, n, h₁, h₂, hi⟩ := h
  exact ⟨hl, n, h₁, h₂, hi.congr_left hab⟩

/-- `insertTracked` from sets with the same members, onto any two lists. -/
theorem insertTracked_agree {a b : HashSet String} (h : SameLive a b)
    (added₁ added₂ ys : List String) :
    LiveAgree a added₁ added₂ (insertTracked a added₁ ys).1 (insertTracked a added₁ ys).2
      (insertTracked b added₂ ys).1 (insertTracked b added₂ ys).2 := by
  induction ys generalizing a b added₁ added₂ with
  | nil =>
    simp only [insertTracked_nil]
    exact ⟨h, [], rfl, rfl, Inserted.nil a⟩
  | cons y ys ih =>
    rw [insertTracked_cons, insertTracked_cons, ← h.contains_eq y]
    by_cases hy : a.contains y
    · simp only [hy, ite_true]
      have hsame := SameLive.insert_of_mem (HashSet.mem_iff_contains.mpr hy)
      exact (ih (h.insert y) added₁ added₂).congr_left hsame
    · simp only [hy, Bool.false_eq_true, ite_false]
      have hy' : y ∉ a := fun h => hy (HashSet.mem_iff_contains.mp h)
      have h₀ : LiveAgree a added₁ added₂ (a.insert y) (y :: added₁) (b.insert y)
          (y :: added₂) :=
        ⟨h.insert y, [y], rfl, rfl, Inserted.singleton hy'⟩
      exact h₀.seq (ih (h.insert y) _ _)

/-! ## The sweep -/

variable (F : Lambda.Factory CoreLParams)

mutual
/-- `dropDeadDefsStmt` depends only on the members of the live set, and `added` records
    exactly the names it inserts. -/
theorem dropDeadDefsStmt_agree (D : Defined) {a b : HashSet String} (h : SameLive a b)
    (added₁ added₂ : List String) (stmt : Statement) :
    (dropDeadDefsStmt F D a added₁ stmt).1 = (dropDeadDefsStmt F D b added₂ stmt).1 ∧
      LiveAgree a added₁ added₂
        (dropDeadDefsStmt F D a added₁ stmt).2.1 (dropDeadDefsStmt F D a added₁ stmt).2.2
        (dropDeadDefsStmt F D b added₂ stmt).2.1 (dropDeadDefsStmt F D b added₂ stmt).2.2 := by
  match stmt with
  | .ite cond thenSs elseSs md =>
    simp only [dropDeadDefsStmt]
    split
    · have hA := dropDeadDefsArms_agree D h added₁ added₂ elseSs thenSs
      rcases hA₁ : dropDeadDefsArms F D a added₁ elseSs thenSs with ⟨e₁, t₁, l₁, r₁⟩
      rcases hA₂ : dropDeadDefsArms F D b added₂ elseSs thenSs with ⟨e₂, t₂, l₂, r₂⟩
      rw [hA₁, hA₂] at hA
      obtain ⟨he, ht, hl⟩ := hA
      simp only at he ht hl ⊢
      subst he ht
      exact ⟨rfl, hl.seq (insertTracked_agree hl.1 r₁ r₂ _)⟩
    · have hA := dropDeadDefsArms_agree D h added₁ added₂ thenSs elseSs
      rcases hA₁ : dropDeadDefsArms F D a added₁ thenSs elseSs with ⟨t₁, e₁, l₁, r₁⟩
      rcases hA₂ : dropDeadDefsArms F D b added₂ thenSs elseSs with ⟨t₂, e₂, l₂, r₂⟩
      rw [hA₁, hA₂] at hA
      obtain ⟨ht, he, hl⟩ := hA
      simp only at he ht hl ⊢
      subst he ht
      exact ⟨rfl, hl.seq (insertTracked_agree hl.1 r₁ r₂ _)⟩
  | .block label inner md =>
    have hB := dropDeadDefsAux_agree D h added₁ added₂ inner
    simp only [dropDeadDefsStmt]
    rcases hB₁ : dropDeadDefsAux F D a added₁ inner with ⟨i₁, l₁, r₁⟩
    rcases hB₂ : dropDeadDefsAux F D b added₂ inner with ⟨i₂, l₂, r₂⟩
    rw [hB₁, hB₂] at hB
    obtain ⟨hi, hl⟩ := hB
    simp only at hi hl ⊢
    subst hi
    exact ⟨rfl, hl⟩
  | .loop guard measure invs body md =>
    have hB := dropDeadDefsAux_agree D h added₁ added₂ body
    simp only [dropDeadDefsStmt]
    rcases hB₁ : dropDeadDefsAux F D a added₁ body with ⟨i₁, l₁, r₁⟩
    rcases hB₂ : dropDeadDefsAux F D b added₂ body with ⟨i₂, l₂, r₂⟩
    rw [hB₁, hB₂] at hB
    obtain ⟨hi, hl⟩ := hB
    simp only at hi hl ⊢
    subst hi
    exact ⟨rfl, hl.seq (insertTracked_agree hl.1 r₁ r₂ _)⟩
  | .cmd _ | .exit _ _ | .typeDecl _ _ =>
    simp only [dropDeadDefsStmt, true_and]
    exact insertTracked_agree h added₁ added₂ _
  termination_by sizeOf stmt

/-- `dropDeadDefsArms` depends only on the members of the live set, and `added` records
    exactly the names it inserts. -/
theorem dropDeadDefsArms_agree (D : Defined) {a b : HashSet String} (h : SameLive a b)
    (added₁ added₂ : List String) (first second : List Statement) :
    let o₁ := dropDeadDefsArms F D a added₁ first second
    let o₂ := dropDeadDefsArms F D b added₂ first second
    o₁.1 = o₂.1 ∧ o₁.2.1 = o₂.2.1 ∧
      LiveAgree a added₁ added₂ o₁.2.2.1 o₁.2.2.2 o₂.2.2.1 o₂.2.2.2 := by
  intro o₁ o₂
  simp only [o₁, o₂, dropDeadDefsArms]
  split
  · have hS := dropDeadDefsAux_agree D h added₁ added₂ second
    rcases hS₁ : dropDeadDefsAux F D a added₁ second with ⟨s₁, l₁, r₁⟩
    rcases hS₂ : dropDeadDefsAux F D b added₂ second with ⟨s₂, l₂, r₂⟩
    rw [hS₁, hS₂] at hS
    obtain ⟨hs, hl⟩ := hS
    simp only at hs hl ⊢
    exact ⟨by trivial, hs, hl⟩
  · have hF := dropDeadDefsAux_agree D h [] [] first
    rcases hF₁ : dropDeadDefsAux F D a [] first with ⟨f₁, lF₁, nF₁⟩
    rcases hF₂ : dropDeadDefsAux F D b [] first with ⟨f₂, lF₂, nF₂⟩
    rw [hF₁, hF₂] at hF
    unfold LiveAgree at hF
    obtain ⟨hf, hlF, nF, hn₁, hn₂, hins⟩ := hF
    simp only [List.append_nil] at hf hlF hn₁ hn₂ hins ⊢
    subst hf nF₁ nF₂
    have hE := hlF.foldl_erase nF
    have hS := dropDeadDefsAux_agree D hE added₁ added₂ second
    rcases hS₁ : dropDeadDefsAux F D (nF.foldl (·.erase ·) lF₁) added₁ second
      with ⟨s₁, l₁, r₁⟩
    rcases hS₂ : dropDeadDefsAux F D (nF.foldl (·.erase ·) lF₂) added₂ second
      with ⟨s₂, l₂, r₂⟩
    rw [hS₁, hS₂] at hS
    obtain ⟨hs, hl⟩ := hS
    simp only at hs hl ⊢
    exact ⟨by trivial, hs, (hl.seq (insertTracked_agree hl.1 r₁ r₂ nF)).congr_left hins.erase_all⟩
  termination_by sizeOf first + sizeOf second
  decreasing_by all_goals cases first <;> cases second <;> simp <;> omega

/-- `dropDeadDefsAux` depends only on the members of the live set, and `added` records
    exactly the names it inserts. -/
theorem dropDeadDefsAux_agree (D : Defined) {a b : HashSet String} (h : SameLive a b)
    (added₁ added₂ : List String) (ss : List Statement) :
    (dropDeadDefsAux F D a added₁ ss).1 = (dropDeadDefsAux F D b added₂ ss).1 ∧
      LiveAgree a added₁ added₂
        (dropDeadDefsAux F D a added₁ ss).2.1 (dropDeadDefsAux F D a added₁ ss).2.2
        (dropDeadDefsAux F D b added₂ ss).2.1 (dropDeadDefsAux F D b added₂ ss).2.2 := by
  match ss with
  | [] =>
    simp only [dropDeadDefsAux, true_and]
    exact ⟨h, [], rfl, rfl, Inserted.nil a⟩
  | stmt :: rest =>
    have ihR := dropDeadDefsAux_agree (D.after stmt) h added₁ added₂ rest
    simp only [dropDeadDefsAux]
    rcases hR₁ : dropDeadDefsAux F (D.after stmt) a added₁ rest with ⟨rest₁, l₁, r₁⟩
    rcases hR₂ : dropDeadDefsAux F (D.after stmt) b added₂ rest with ⟨rest₂, l₂, r₂⟩
    rw [hR₁, hR₂] at ihR
    obtain ⟨hrest, hl⟩ := ihR
    simp only at hrest hl ⊢
    subst hrest
    have hkeep := dropDeadDefsStmt_agree D hl.1 r₁ r₂ stmt
    cases definedBy F D stmt with
    | none =>
      simp only [Bool.false_eq_true, ite_false]
      obtain ⟨hs, hsl⟩ := hkeep
      exact ⟨by rw [hs], hl.seq hsl⟩
    | some x =>
      simp only [hl.1.contains_eq x.name]
      split
      · exact ⟨rfl, hl⟩
      · obtain ⟨hs, hsl⟩ := hkeep
        exact ⟨by rw [hs], hl.seq hsl⟩
  termination_by sizeOf ss
end

/-- `dropDeadDefsAux` gives the same swept list from live sets with the same members, onto
    any `added`. -/
theorem dropDeadDefsAux_congr (D : Defined) {a b : HashSet String} (h : SameLive a b)
    (added₁ added₂ : List String) (ss : List Statement) :
    (dropDeadDefsAux F D a added₁ ss).1 = (dropDeadDefsAux F D b added₂ ss).1 ∧
      SameLive (dropDeadDefsAux F D a added₁ ss).2.1 (dropDeadDefsAux F D b added₂ ss).2.1 :=
  let ⟨h₁, h₂, _⟩ := dropDeadDefsAux_agree F D h added₁ added₂ ss
  ⟨h₁, h₂⟩

/-- `added` records exactly the names `dropDeadDefsAux` inserts into the live set. -/
theorem dropDeadDefsAux_inserted (D : Defined) (live : HashSet String) (added : List String)
    (ss : List Statement) :
    ∃ new, (dropDeadDefsAux F D live added ss).2.2 = new ++ added ∧
      Inserted live new (dropDeadDefsAux F D live added ss).2.1 :=
  let ⟨_, _, new, h₁, _, h₂⟩ :=
    dropDeadDefsAux_agree F D (SameLive.refl live) added added ss
  ⟨new, h₁, h₂⟩

/-- The in-place sweep of a branch's arms is the same as sweeping each arm on its own from
    the live set after the branch: the swept arms are those sweeps, and the live set it
    returns holds what either sweep returns. -/
theorem dropDeadDefsArms_spec (D : Defined) (live : HashSet String) (added : List String)
    (first second : List Statement) :
    let o := dropDeadDefsArms F D live added first second
    o.1 = (dropDeadDefsAux F D live [] first).1 ∧
      o.2.1 = (dropDeadDefsAux F D live [] second).1 ∧
      (∀ x, x ∈ o.2.2.1 ↔ x ∈ (dropDeadDefsAux F D live [] first).2.1 ∨
        x ∈ (dropDeadDefsAux F D live [] second).2.1) ∧
      ∃ new, o.2.2.2 = new ++ added ∧ Inserted live new o.2.2.1 := by
  intro o
  have hins : ∃ new, o.2.2.2 = new ++ added ∧ Inserted live new o.2.2.1 := by
    obtain ⟨-, -, -, new, h₁, -, h₂⟩ :=
      dropDeadDefsArms_agree F D (SameLive.refl live) added added first second
    exact ⟨new, h₁, h₂⟩
  suffices o.1 = (dropDeadDefsAux F D live [] first).1 ∧
      o.2.1 = (dropDeadDefsAux F D live [] second).1 ∧
      (∀ x, x ∈ o.2.2.1 ↔ x ∈ (dropDeadDefsAux F D live [] first).2.1 ∨
        x ∈ (dropDeadDefsAux F D live [] second).2.1) from
    ⟨this.1, this.2.1, this.2.2, hins⟩
  clear hins
  simp only [o, dropDeadDefsArms]
  split
  · rename_i hfirst
    obtain rfl : first = [] := List.isEmpty_iff.mp hfirst
    have hS := dropDeadDefsAux_congr F D (SameLive.refl live) added [] second
    obtain ⟨_, _, hi⟩ := dropDeadDefsAux_inserted F D live added second
    simp only [dropDeadDefsAux]
    refine ⟨by trivial, hS.1, fun x => ?_⟩
    rw [← hS.2 x]
    exact ⟨.inr, fun h => h.elim (fun h => (hi.mem x).mpr (.inl h)) id⟩
  · obtain ⟨nF, hnF, hiF⟩ := dropDeadDefsAux_inserted F D live [] first
    rcases hF : dropDeadDefsAux F D live [] first with ⟨f, lF, aF⟩
    rw [hF] at hnF hiF
    simp only [List.append_nil] at hnF hiF ⊢
    subst aF
    have hE := hiF.erase_all
    have hS := dropDeadDefsAux_congr F D hE added [] second
    obtain ⟨_, _, hiS⟩ := dropDeadDefsAux_inserted F D (nF.foldl (·.erase ·) lF) added second
    rcases hS' : dropDeadDefsAux F D (nF.foldl (·.erase ·) lF) added second with ⟨s, lS, rS⟩
    rw [hS'] at hS hiS
    simp only at hS hiS ⊢
    refine ⟨by trivial, hS.1, fun x => ?_⟩
    rw [insertTracked_mem, ← hS.2 x, hiF.mem x]
    have hsub : x ∈ live → x ∈ lS := fun h => (hiS.mem x).mpr (.inl ((hE x).mpr h))
    constructor
    · rintro (h | h)
      · exact .inr h
      · exact .inl (.inr h)
    · rintro ((h | h) | h)
      · exact .inl (hsub h)
      · exact .inr h
      · exact .inl h

end Core.Simplify

end
